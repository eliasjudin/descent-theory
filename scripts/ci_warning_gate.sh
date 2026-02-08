#!/usr/bin/env bash
set -euo pipefail

LOG_FILE="${1:-ci-build.log}"
TRACKER_FILE="${2:-SORRY_TRACKER.md}"

if [[ ! -f "$LOG_FILE" ]]; then
  echo "error: missing build log: $LOG_FILE" >&2
  exit 1
fi

if [[ ! -f "$TRACKER_FILE" ]]; then
  echo "error: missing tracker: $TRACKER_FILE" >&2
  exit 1
fi

ansi_free_log="$(mktemp)"
non_sorry_warnings="$(mktemp)"
sorry_locations="$(mktemp)"
expected_decls_raw="$(mktemp)"
expected_decls="$(mktemp)"
actual_decls="$(mktemp)"
trap 'rm -f "$ansi_free_log" "$non_sorry_warnings" "$sorry_locations" "$expected_decls_raw" "$expected_decls" "$actual_decls"' EXIT

# Strip ANSI escapes from CI logs before parsing warnings.
sed -E 's/\x1B\[[0-9;]*[[:alpha:]]//g' "$LOG_FILE" > "$ansi_free_log"

grep -n "warning:" "$ansi_free_log" | grep -v "declaration uses 'sorry'" > "$non_sorry_warnings" || true
if [[ -s "$non_sorry_warnings" ]]; then
  echo "Found non-sorry warnings in build output:"
  cat "$non_sorry_warnings"
  exit 1
fi
echo "No non-sorry warnings found."

sed -nE 's/^[[:space:]]*- Declaration:[[:space:]]*`([^`]+)`.*/\1/p' "$TRACKER_FILE" > "$expected_decls_raw"
sort -u "$expected_decls_raw" > "$expected_decls"

if [[ "$(wc -l < "$expected_decls_raw")" -ne "$(wc -l < "$expected_decls")" ]]; then
  echo "error: duplicate declaration names found in $TRACKER_FILE" >&2
  exit 1
fi

sed -nE "s#^[[:space:]]*warning:[[:space:]]*([^:]+\\.lean):([0-9]+):[0-9]+:[[:space:]]*declaration uses 'sorry'.*#\\1:\\2#p" "$ansi_free_log" \
  | sort -u > "$sorry_locations"

if [[ ! -s "$sorry_locations" ]]; then
  if [[ -s "$expected_decls" ]]; then
    echo "error: tracker lists declarations, but no declaration uses 'sorry' warnings were found in $LOG_FILE" >&2
    echo "clear completed entries from $TRACKER_FILE or ensure build logs include all warnings." >&2
    exit 1
  fi
  echo "No declaration uses 'sorry' warnings found and tracker is empty."
  exit 0
fi

if [[ ! -s "$expected_decls" ]]; then
  echo "error: found declaration uses 'sorry' warnings but tracker has no entries: $TRACKER_FILE" >&2
  exit 1
fi

resolve_decl_name() {
  local file="$1"
  local line="$2"
  local decl_line
  local name

  decl_line="$(sed -n "${line}p" "$file")"
  name="$(
    printf '%s\n' "$decl_line" | awk '
      {
        for (i = 1; i <= NF; i++) {
          if ($i == "theorem" || $i == "lemma" || $i == "def" || $i == "abbrev" || $i == "opaque" || $i == "instance" || $i == "example") {
            print $(i + 1)
            exit
          }
        }
      }
    '
  )"

  name="$(printf '%s' "$name" | sed -E 's/^`//; s/`$//; s/\(.*$//; s/:.*$//; s/[[:space:]]+$//')"
  if [[ -z "$name" ]]; then
    echo "error: could not resolve declaration name at $file:$line" >&2
    exit 1
  fi
  printf '%s\n' "$name"
}

while IFS=: read -r file line; do
  if [[ ! -f "$file" ]]; then
    echo "error: warning references missing file: $file" >&2
    exit 1
  fi
  resolve_decl_name "$file" "$line"
done < "$sorry_locations" | sort -u > "$actual_decls"

if ! diff -u "$expected_decls" "$actual_decls"; then
  echo
  echo "SORRY allowlist mismatch."
  echo "Update $TRACKER_FILE or discharge/introduce sorries so the sets match exactly."
  exit 1
fi

echo "SORRY allowlist matches warning-declared declarations."
