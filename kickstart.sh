#!/usr/bin/env bash
# Sanity check for the TTpaola SEFM artifact.
# Prefer Docker if available, otherwise use a local GHC/cabal toolchain.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

expect_pass() {
  echo "==> $1"
}

if command -v docker >/dev/null 2>&1; then
  expect_pass "Docker path: build image and run test suite"
  docker build -t ttpaola-artifact .
  docker run --rm ttpaola-artifact
  echo
  expect_pass "Optional: print initial food-delivery config"
  docker run --rm ttpaola-artifact cabal run timed-ttpaola
else
  expect_pass "Local path: cabal update / build / test"
  if ! command -v cabal >/dev/null 2>&1; then
    echo "error: neither docker nor cabal found." >&2
    echo "Install Docker, or GHC+cabal via https://www.haskell.org/ghcup/" >&2
    exit 1
  fi
  cabal update
  cabal build all
  cabal test --test-show-details=direct
  echo
  expect_pass "Optional: print initial food-delivery Config"
  cabal run timed-ttpaola
fi

echo
echo "OK: kick-start succeeded."
echo "Expected test tail: 64 examples, 0 failures"
echo "Next: follow AE appendix Sec. A.3 (or README claims F1-F7)."
