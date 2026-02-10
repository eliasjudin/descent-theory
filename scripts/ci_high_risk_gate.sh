#!/usr/bin/env bash
set -euo pipefail

# Exit code:
#   0 => high-risk Lean edits detected
#   1 => no high-risk Lean edits detected

resolve_range() {
  local resolved=""

  if [[ -n "${GITHUB_BASE_REF:-}" ]]; then
    git fetch --no-tags --depth=1 origin "${GITHUB_BASE_REF}" >/dev/null 2>&1 || true
    if git rev-parse --verify "origin/${GITHUB_BASE_REF}" >/dev/null 2>&1; then
      local base_sha
      base_sha="$(git merge-base HEAD "origin/${GITHUB_BASE_REF}" || true)"
      if [[ -n "$base_sha" ]]; then
        resolved="${base_sha}...HEAD"
      fi
    fi
  fi

  if [[ -z "$resolved" && -n "${GITHUB_EVENT_BEFORE:-}" ]] \
    && [[ "${GITHUB_EVENT_BEFORE}" != "0000000000000000000000000000000000000000" ]]; then
    if git rev-parse --verify "${GITHUB_EVENT_BEFORE}" >/dev/null 2>&1; then
      resolved="${GITHUB_EVENT_BEFORE}...HEAD"
    fi
  fi

  if [[ -z "$resolved" ]] && git rev-parse --verify HEAD~1 >/dev/null 2>&1; then
    resolved="HEAD~1...HEAD"
  fi

  printf '%s\n' "$resolved"
}

range="${1:-}"
if [[ -z "$range" ]]; then
  range="$(resolve_range)"
fi

if [[ -z "$range" ]]; then
  echo "warning: could not determine commit range; treating as high risk."
  exit 0
fi

mapfile -t lean_files < <(git diff --name-only "$range" -- '*.lean' | sed '/^[[:space:]]*$/d')
if [[ "${#lean_files[@]}" -eq 0 ]]; then
  echo "No changed Lean files in range ${range}."
  exit 1
fi

tmp_matches="$(mktemp)"
high_risk_files=()
trap 'rm -f "$tmp_matches"' EXIT

for file in "${lean_files[@]}"; do
  [[ -f "$file" ]] || continue
  if git diff -U0 "$range" -- "$file" \
    | grep -E '^[+-]' \
    | grep -Ev '^(\+\+\+|---)' \
    | grep -En \
      -e 'set_option' \
      -e '@\[[^]]*simp[^]]*\]' \
      -e 'attribute[[:space:]]+\[[^]]*simp[^]]*\]' \
      -e '^[-+][[:space:]]*instance([[:space:]]|$)' \
      -e '^[-+][[:space:]]*(syntax|macro|macro_rules|elab|declare_syntax_cat)([[:space:]]|$)' \
      -e 'priority[[:space:]]*[:=]' \
      > "$tmp_matches"; then
    high_risk_files+=("$file")
    echo "---- ${file} ----"
    cat "$tmp_matches"
  fi
done

if [[ "${#high_risk_files[@]}" -eq 0 ]]; then
  echo "No high-risk Lean edits detected in range ${range}."
  exit 1
fi

echo "High-risk Lean edits detected in range ${range}:"
printf ' - %s\n' "${high_risk_files[@]}"
exit 0
