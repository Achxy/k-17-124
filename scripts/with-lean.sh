#!/usr/bin/env bash
# Use the Lean toolchain pinned by lean-toolchain through Elan on PATH.
set -euo pipefail
cd "$(dirname "$0")/.."
exec "$@"
