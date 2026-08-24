#!/usr/bin/env bash
# Idempotent Cloud Agent setup for this Lean 4 / Lake project.
# Safe to run repeatedly: it installs elan only when missing and then builds,
# which downloads the exact toolchain pinned in `lean-toolchain`.
set -euo pipefail

# Install elan (the Lean toolchain manager) if it is not already present.
# `--default-toolchain none` avoids fetching an extra toolchain; `lake build`
# below installs the one pinned by `lean-toolchain`.
if [ ! -x "$HOME/.elan/bin/elan" ] && ! command -v elan >/dev/null 2>&1; then
  curl -fsSL https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

# Make elan/lake/lean available for the remainder of this script.
export PATH="$HOME/.elan/bin:$PATH"

elan --version
lake --version

# Build the project. This resolves the pinned toolchain and compiles the
# library and executable, leaving the workspace ready for development.
lake build
