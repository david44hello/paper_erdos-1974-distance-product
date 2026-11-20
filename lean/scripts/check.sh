#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
git ls-files --error-unmatch -- AUDIT.md CLAIMS.json Audit.lean >/dev/null
lake exe cache get
lake env lean -j1 scripts/RealLimsupControl.lean
python3 scripts/audit.py
git diff --exit-code HEAD -- AUDIT.md CLAIMS.json Audit.lean
