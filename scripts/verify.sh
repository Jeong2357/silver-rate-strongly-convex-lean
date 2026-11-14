#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-only
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$project_dir"
mkdir -p verification
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
python3 scripts/audit_release.py --check-inputs-only
lake build +StrongSilver.Main > verification/build-main.log 2>&1
lake build +StrongSilver > verification/build-all.log 2>&1
python3 scripts/audit_release.py
