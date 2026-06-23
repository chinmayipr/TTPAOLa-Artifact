# TyPAOL: Time-Bounded Consent for Active Objects (Haskell Artifact)

This artifact accompanies the paper *"Time-Bounded Consent for Active Objects"*.
It is a reference implementation of the timed extension of TyPAOL: the type
checker, the untyped operational semantics (runtime consent checks at every
reduction), the typed operational semantics (a single check at method
activation), and a scheduler that drives either semantics over the same
configuration. The test suite (56 cases) turns the paper's claims into
executable checks.

## What this artifact demonstrates

| # | Claim | Where checked |
|---|---|---|
| 1 | The type checker computes constraint sets (Cn), modified-user sets (Um), accessed-user sets (Uc), and output offsets (delta_out) for the running food-delivery example as reported in the paper (setAddrCons, renewCons, getAddr, deliver). | test/MigrationTest.hs, #2-#5 |
| 2 | Non-interference: deliver and getAddr may run concurrently; renewCons and deliver conflict on a shared user. | test/MigrationTest.hs, #6/#7 |
| 3 | Activation (InstCnstr) accepts/rejects at the time boundaries reported in the paper, including after partial consent renewal and after expiry pruning (RemExpired). | test/MigrationTest.hs, #8-#12 |
| 4 | The timeout-guarded fetch reaches the Ok branch when the callee answers in time and the Err branch on timeout, including the zero-timeout edge case. | test/InterpreterTest.hs, test/MigrationTest.hs #13/#14 |
| 5 | Safety: under the typed semantics a thread whose constraints cannot be satisfied is never activated; under the untyped semantics the same configuration activates the thread and gets stuck mid-execution with a consent violation. | test/SafetyTest.hs |
| 6 | Consent-algebra laws: tag combination is a greatest lower bound, allowed actions are anti-monotone in time, expired entries are pruned, same-(class, purpose) consent is overwritten. | test/ConsentTest.hs |

## Requirements

* GHC 9.12.2 and cabal-install >= 3.14 (the versions the artifact was
  developed and tested with). Any GHC supporting GHC2021 (>= 9.2) is
  expected to work.
* Dependencies (fetched automatically by cabal from Hackage): containers,
  mtl, and for the tests hspec.
* Tested on macOS (Apple Silicon); the code is pure Haskell with no
  OS-specific parts.

The easiest way to install the toolchain is [GHCup](https://www.haskell.org/ghcup/):

```sh
ghcup install ghc 9.12.2
ghcup install cabal latest
```

Alternatively, a Dockerfile is provided (see below).

## Quick start (~2 minutes)

```sh
cabal update
cabal build all          # builds library + executable (first run fetches deps)
cabal test               # runs the full suite; expect "56 examples, 0 failures"
cabal run timed-typaol   # type-checks the food-delivery example and prints
                         # the bootstrapped initial configuration at time 0
```

Expected tail of `cabal test`:

```
Finished in ... seconds
56 examples, 0 failures
Test suite tests: PASS
```

Expected output of `cabal run timed-typaol`: a Config value showing two
objects (Plat, Courier), the user alice, and her four Plat consent entries
with expiry 80, matching the initial configuration in the paper's example.

## Step-by-step evaluation

Each test group is independently runnable with hspec's `--match` filter:

```sh
# The safety demonstration (claim 5): same configuration, both semantics
cabal test --test-options='--match "Type safety"'

# Type-checker results for the running example (claim 1)
cabal test --test-options='--match "TyPAOL migration"'

# Operational rules for delay/fetch (claim 4)
cabal test --test-options='--match "TyPAOL.Interpreter"'
```

The safety test (test/SafetyTest.hs) is the heart of the artifact. It builds
one configuration containing a method

```
riskyOp(U u, D x) { delay 10; let _z = x in unit }
```

with consent that expires at time 5, i.e. before the worst-case constraint
(at offset 10) fires. Driving the typed scheduler yields
[StepBind, StepStuck]: the activation gate rejects the thread, nothing runs,
no error. Driving the untyped scheduler on the same input yields
StepBind -> StepActivate -> StepTimeAdv 10 -> ConsentViolation Collect at
time 10: the thread starts and gets stuck. This is the operational
restatement of the paper's soundness theorem.

## Repository layout

| Module | Formal artefact |
|---|---|
| src/TyPAOL/Syntax.hs | Surface syntax: expressions, tags, policies, programs. delay is a leaf; sequencing e1;e2 is sugar for let _ = e1 in e2. |
| src/TyPAOL/Consent.hs | Consent environment, runtime tags, tag combine, tag order, allowed actions, comply checks, addConsent, RemExpired. |
| src/TyPAOL/Runtime.hs | Configurations, objects, messages, typed/untyped queues, class table, bootstrap (initConfig). |
| src/TyPAOL/Eval.hs | Value-expression evaluation with tag propagation. |
| src/TyPAOL/Interpreter.hs | Untyped semantics: instantaneous reduction with per-action comply checks, timed reduction, global time advance, bind/activate. |
| src/TyPAOL/Types.hs | Extended types, policy expressions, constraints (Cn), type comparison, initial environments. |
| src/TyPAOL/TypeChecker.hs | Typing rules; per-method inference of (Cn, Um) and delta_out. |
| src/TyPAOL/TypedInterpreter.hs | Typed semantics: reductions without runtime checks, InstAnn, InstCnstr, plcy, non-interference, typed bind/activate. |
| src/TyPAOL/Scheduler.hs | Driver with rule priority instant > bind > activate > time; parametric in typed/untyped. |
| src/TyPAOL/Examples/FoodDelivery.hs | The paper's running example as an AST value, including the bootstrap. |
| app/Main.hs | Type-checks the example and prints the initial configuration. |
| test/ | ConsentTest, EvalTest, InterpreterTest, TypeCheckerTest, MigrationTest, SafetyTest. |

There is intentionally no concrete-syntax parser: programs are written as
Haskell values of type Program (see FoodDelivery.hs for the pattern). This
keeps the artifact small and the AST in one-to-one correspondence with the
paper's grammar.

## Writing your own scenario

1. Define classes/methods as ClassDecl / MethodDecl values
   (src/TyPAOL/Examples/FoodDelivery.hs is the template).
2. Build the class table and run the checker:
   `inferMethodMeta (buildClassTable prog)`. A Left is a type error; a Right
   carries per-method (Cn, Um) metadata.
3. Bootstrap with `initConfig prog ct` (or construct a Config by hand, as the
   tests do) and drive it:
   `runExcept (runStateT (run ct typed) cfg)` with typed = True/False.
4. Inspect the returned [StepResult] trace and the final Config (futures,
   fields, consent environment).

## Docker (optional, for a fully pinned environment)

```sh
docker build -t typaol-artifact .
docker run --rm typaol-artifact            # runs the test suite
docker run --rm typaol-artifact cabal run timed-typaol
```

## License

BSD-3-Clause; see LICENSE.
