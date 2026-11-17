#!/usr/bin/env bash
# Build with Lake and fail if Lean reports a runtime panic.
#
# A panic during elaboration (for example `panic!` inside a `#guard` in
# `Mtg.Engine.Tests.Events`) is captured as an information diagnostic:
# `info: <file>:<line>:<col>: PANIC at ...`. Information diagnostics do not
# fail `lake build`, and Lake reprints them when it replays a cached module.
# `LEAN_ABORT_ON_PANIC` makes a fresh panic abort the compiler. The log scan
# also rejects a panic that was only replayed from cache.
set -euo pipefail

export LEAN_ABORT_ON_PANIC=1
# The panic line already names the declaration, file, and message.
export LEAN_BACKTRACE="${LEAN_BACKTRACE:-0}"

log=$(mktemp)
trap 'rm -f "$log" "$log.hits"' EXIT

set +e
lake build "$@" 2>&1 | tee "$log"
status=${PIPESTATUS[0]}
set -e

if grep -n 'PANIC at ' "$log" >"$log.hits"; then
  echo "::error::Lean reported a runtime panic. These are information diagnostics, so lake build would otherwise succeed."
  echo "Runtime panic:"
  cat "$log.hits"
  exit 1
fi

exit "$status"
