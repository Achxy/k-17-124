#!/usr/bin/env bash
# The same verification entry point is used locally and by CI.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-layout.py
scripts/with-lean.sh lake --wfail build
scripts/with-lean.sh lake env lean Audit.lean
