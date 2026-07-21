# TT-Paola: Time Bounded Consent for Active Objects

This artifact accompanies the paper *"Time-Bounded Consent for Active Objects"*.
It is a reference implementation of the timed extension of TTpaola: the type
checker, the untyped operational semantics (runtime consent checks at every
reduction), the typed operational semantics (a single check at method
activation), and a scheduler that drives either semantics over the same
configuration. The test suite (64 cases) turns the paper's claims into
executable checks.

## What this artifact demonstrates

The test suite encodes the paper's executable claims as follows.

1. **Food-delivery typing.** For the running example, the checker recovers the
   reported metadata: `setAddrCons` / `renewCons` produce an empty constraint
   set and a non-empty modified-user set; `getAddr` requires Use, Collect, and
   Transfer at offset 1 with `delta_out = 1`; `deliver` requires Use and Collect
   with maximum constraint offset 4 and `delta_out = 14`.
   (`test/MigrationTest.hs`, groups #2-#5.)

2. **Non-interference.** `deliver` and `getAddr` may run concurrently;
   `renewCons` conflicts with `deliver` when both touch the same user.
   (MigrationTest #6/#7.)

3. **Activation timing.** With Courier consent duration `delta1 = 11`, InstCnstr
   accepts `deliver` at `tau = 0` and rejects it at `tau = 8`. After
   `renewCons` (`delta2 = 6`), use/transfer are overwritten while collect is
   not. RemExpired then drops expired Courier entries and blocks activation.
   (MigrationTest #8-#12.)

4. **Timeout-guarded fetch.** A resolved future yields Ok before the timeout,
   an unresolved future yields Err on timeout, including the zero-timeout case.
   (`test/InterpreterTest.hs`, MigrationTest #13/#14.)

5. **Typed vs untyped safety.** On one configuration where consent expires
   before the worst-case offset, the typed scheduler binds the message but
   never activates the thread, the untyped scheduler activates it and later
   fails with a Collect consent violation at time 10.
   (`test/SafetyTest.hs`.)

6. **Consent algebra.** Tag combination is a greatest lower bound allowed
   actions shrink as time advances. RemExpired and same-(class, purpose)
   overwrite behave as specified. (`test/ConsentTest.hs`; MigrationTest.)

7. **Negative litmus.** Ill-typed programs are rejected (aliased user
   actuals and personal fetch-else), untyped bind and fetch-adv fail when
   compliance does not hold and typed activation enforces NI and applies
   `plcy` for in-method consent grants.
   (`test/LitmusTest.hs`.)


## Requirements

* GHC 9.12.2 and cabal-install >= 3.14 (the versions the artifact was
  developed and tested with). Any GHC supporting GHC2021 (>= 9.2) is
  expected to work.
* Dependencies (fetched automatically by cabal from Hackage): containers,
  mtl, and for the tests hspec.
* Tested on macOS (Apple Silicon) and the code is pure Haskell with no
  OS-specific parts.

The easiest way to install the toolchain is [GHCup](https://www.haskell.org/ghcup/):

```sh
ghcup install ghc 9.12.2
ghcup install cabal latest
```

Alternatively, a Dockerfile is provided (see below). For AE kick-the-tires,
run `./kickstart.sh` (Docker if available, else local cabal).

## Quick start (~2 minutes)

```sh
./kickstart.sh            # preferred one-shot sanity check
# or:
cabal update
cabal build all
cabal test               # expect "64 examples, 0 failures"
cabal run timed-ttpaola
```

Expected tail of `cabal test`:

```
Finished in ... seconds
64 examples, 0 failures
Test suite tests: PASS
```

Expected output of `cabal run timed-ttpaola`: a Config value showing two
objects (Plat, Courier), the user alice, and her three Plat consent entries
(use, collect, transfer) with expiry 80, matching Example 2's initial Sigma0.

## Step-by-step evaluation

Each test group is independently runnable with hspec's `--match` filter:

```sh
# The safety demonstration (claim 5): same configuration, both semantics
cabal test --test-options='--match "Type safety"'

# Type-checker results for the running example (claim 1)
cabal test --test-options='--match "TTpaola migration"'

# Operational rules for delay/fetch (claim 4)
cabal test --test-options='--match "TTpaola.Interpreter"'

# Negative litmus (claim 7)
cabal test --test-options='--match "negative litmus"'
```

The safety test (test/SafetyTest.hs) is the novelty of the artifact. It builds
one configuration containing a method

```
riskyOp(U u, D x) { delay 10; let _z = x in unit }
```

with consent that expires at time 5, i.e. before the worst-case constraint
(at offset 10) fires. Driving the typed scheduler yields
[StepBind, StepStuck]:activation gate rejects the thread, nothing runs,
no error. Driving the untyped scheduler on the same input yields
StepBind -> StepActivate -> StepTimeAdv 10 -> ConsentViolation Collect at
time 10: the thread starts and gets stuck. This is the part of the paper's soundness theorem.

## Repository layout

- `src/TTpaola/Syntax.hs` — surface syntax (expressions, tags, policies, programs). `delay` is a leaf. Sequencing `e1;e2` is sugar for `let _ = e1 in e2`.
- `src/TTpaola/Consent.hs` — consent environment, tags, Fig. 3 `comply{U,C,T,S}`, `addConsent`, RemExpired, `consentLeq`.
- `src/TTpaola/Runtime.hs` — configurations, objects, messages, typed and untyped queues, class table, bootstrap (`initConfig`).
- `src/TTpaola/Eval.hs` — value-expression evaluation with tag propagation.
- `src/TTpaola/Interpreter.hs` — untyped semantics: instantaneous reduction with per-action comply checks, timed reduction, global time advance, bind and activate.
- `src/TTpaola/Types.hs` — extended types, policy expressions, constraints (Cn), type comparison, initial environments.
- `src/TTpaola/TypeChecker.hs` — typing rules and per-method inference of (Cn, Um) and `delta_out`.
- `src/TTpaola/TypedInterpreter.hs` — typed semantics: reductions without runtime checks, InstAnn, InstCnstr, `plcy`, non-interference, typed bind and activate.
- `src/TTpaola/Scheduler.hs` — driver with priority instant > bind > activate > time, parametric in typed or untyped.
- `src/TTpaola/Examples/FoodDelivery.hs` — Fig. 2 example (`delta1=11`, `delta2=6`), including address store and Example 2 Sigma0.
- `app/Main.hs` — type-checks the example and prints the initial configuration.
- `test/` — ConsentTest, EvalTest, InterpreterTest, TypeCheckerTest, MigrationTest, SafetyTest, LitmusTest.
- `kickstart.sh` — one-shot kick-the-tires script (Docker or local cabal).


There is intentionally no concrete-syntax parser: programs are written as
Haskell values of type Program (see FoodDelivery.hs for the pattern). This
keeps the artifact small and the AST in one-to-one correspondence with the
paper's grammar.

## Writing your own scenario

1. Define classes/methods as ClassDecl / MethodDecl values
   (src/TTpaola/Examples/FoodDelivery.hs is the template).
2. Build the class table and run the checker:
   `inferMethodMeta (buildClassTable prog)`. A Left is a type error and a Right
   carries per-method (Cn, Um) metadata.
3. Bootstrap with `initConfig prog ct` (or construct a Config by hand, as the
   tests do) and drive it:
   `runExcept (runStateT (run ct typed) cfg)` with typed = True/False.
4. Inspect the returned [StepResult] trace and the final Config (futures,
   fields, consent environment).

## Docker (optional, for a fully pinned environment)

```sh
docker build -t ttpaola-artifact .
docker run --rm ttpaola-artifact            # runs the test suite
docker run --rm ttpaola-artifact cabal run timed-ttpaola
```

## License

BSD-3-Clause; see LICENSE.
