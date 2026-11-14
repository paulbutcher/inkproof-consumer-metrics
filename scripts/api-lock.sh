#!/usr/bin/env bash
# Prints the public API of Metrics, one line per declaration; CI compares it with API.lock.
# Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/.."
lake build >&2
lake exe api-lock Metrics Metrics.Proofs
