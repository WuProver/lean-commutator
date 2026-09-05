#!/bin/bash
set -euo pipefail
export PATH="${HOME}/.elan/bin:/run/current-system/sw/bin:/opt/homebrew/bin:${PATH:-/usr/bin:/bin}"
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if command -v elan >/dev/null 2>&1; then
  proof_lake="$(elan which lake)"
else
  proof_lake="$(command -v lake)"
fi
printf '%s\n' 'Building both libraries...'
"$proof_lake" build
python3 scripts/verify_no_epsilon.py --lake "$proof_lake"
printf '%s\n' 'Build and full theorem audit passed.'
