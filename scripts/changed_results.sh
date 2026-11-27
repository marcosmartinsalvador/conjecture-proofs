#!/usr/bin/env bash
# Prints the result folders the checker should run on, one per line.
#   scripts/changed_results.sh all            every folder
#   scripts/changed_results.sh <git-range>    folders whose .lean files changed in the
#                                             range; every folder if the checker, the
#                                             pinned versions or the setup changed, or
#                                             if the range cannot be read
set -uo pipefail
cd "$(dirname "$0")/.."
all () { for d in conjectures/*/; do [ -f "$d/Statement.lean" ] && basename "$d"; done; }
range="${1:-all}"
if [ "$range" = "all" ]; then all; exit 0; fi
if ! changed="$(git diff --name-only "$range" 2>/dev/null)"; then all; exit 0; fi
if printf '%s\n' "$changed" | grep -qE '^(tools/|tests/|lean-toolchain$|lakefile\.toml$|lake-manifest\.json$|setup\.sh$)'; then
  all; exit 0
fi
printf '%s\n' "$changed" | sed -nE 's#^conjectures/([^/]+)/[^/]+\.lean$#\1#p' | sort -u \
  | while read -r s; do [ -f "conjectures/$s/Statement.lean" ] && echo "$s"; done
exit 0
