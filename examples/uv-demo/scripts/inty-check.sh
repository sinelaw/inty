#!/usr/bin/env bash
#
# Run the `inty` type checker over the project's sources, in the same
# spirit as `ty check`: discover every module under src/ and check it.
#
# Unlike `ty`, inty has no project/venv discovery, so we reconstruct the
# import search path by hand:
#   - src/                        (first-party `authkit` package)
#   - the venv's site-packages    (third-party: pydantic, jwt, ...)
#
# inty checks a single file per invocation, so we loop. Exit non-zero if
# any file fails.

set -u

here="$(cd "$(dirname "$0")/.." && pwd)"
repo_root="$(cd "$here/../.." && pwd)"

inty_bin="${INTY_BIN:-$repo_root/target/release/inty}"
if [[ ! -x "$inty_bin" ]]; then
  echo "inty binary not found at $inty_bin (build with: cargo build --release -p inty-cli)" >&2
  exit 2
fi

# Reconstruct the search path ty/pyright would derive from the venv.
site_packages="$(find "$here/.venv" -type d -name site-packages 2>/dev/null | head -n1)"
export INTY_PYTHONPATH="$here/src${site_packages:+:$site_packages}"

echo "inty:           $inty_bin"
echo "INTY_PYTHONPATH=$INTY_PYTHONPATH"
echo

fail=0
total=0
while IFS= read -r -d '' file; do
  total=$((total + 1))
  echo "=== $file ==="
  if ! "$inty_bin" "$file"; then
    fail=$((fail + 1))
  fi
  echo
done < <(find "$here/src" -name '*.py' -print0 | sort -z)

echo "checked $total file(s), $fail failed"
exit $((fail > 0 ? 1 : 0))
