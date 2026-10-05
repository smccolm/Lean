# Author computations — reproduction and proof boundary

Research date: 5 October 2026. Original scripts are unchanged under `Sources/DhimanKadiriQuesadaHerrera-v1-source/anc/`. Archive hashes cover both. No code from these files is imported into a Lean proof.

## AFE1.sage

Header specifies SageMath 9.5. The code sets exact rational `g1=1413472/100000` and `H=3*10^12`, defines m(c) as C(x), differentiates symbolically, and uses `RIF` to check two interval inequalities used in the real-cutoff transfer. It then prints c₀ using ordinary `n(...)` evaluation. The existence of interval comparisons does not imply that every printed decimal is outward-certified.

Read-only inspection completed; replay **NOT RUN**, because Sage is unavailable. This is not a scaffold failure or permission to start Lean conversion. A future reproduction environment should pin Sage 9.5 (or record and compare a migration), capture the boolean interval results and enclosing intervals, and check all advertised decimal rounding. Do not substitute plain Python for Sage syntax and call that the same run.

## AFE2.py

Unmodified replay succeeded, exit 0, with Python 3.13.5, NumPy 1.26.4 and SciPy 1.17.1. The source fixes Decimal precision to 50 but also uses double-precision NumPy values and converts those floats to Decimal strings. It prints four Table 1 rows and k=1..150. The paper's finite-corollary scope is k≤50.

Observed Table 1 output agrees with all displayed cells, including `(2.264445,2.265204,2.265204,5.961915e−2)` at the program's `t₀=6.2832`. This numeric input is slightly larger than the theorem's exact `2π`. It does not cover the omitted tiny interval by itself.

At k=2, the unmodified script prints `2.13226549` for x<y whereas Table 2 prints `2.132265`. Several displayed six-decimal entries are rounded to nearest. These observations must not be labeled exact upper-bound certificates. `find_max` uses `(0,1)` rather than the advertised `[1/2,1]`; later code uses finite differences, endpoint signs and one Brent root. A no-sign-change test does not exclude multiple interior extrema. The code also replaces `(C₂−1)/log(C₂)` by 1 when close to 1, a numerical stabilization that needs a rigorous error enclosure if used for an upper bound.

The [SciPy documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.minimize_scalar.html) describes `minimize_scalar` as local minimization; it does not certify global extrema. [Sage's interval documentation](https://doc.sagemath.org/html/en/reference/rings_numerical/sage/rings/real_mpfi.html) explains the interval representation relevant to AFE1. Neither external numerical library is proof evidence for Lean without a kernel-checked bridge.

## Reproduce separately from scaffold verification

```powershell
python Tools/reproduce_author_code.py
```

This optional research command verifies the archived AFE2 script hash, runs the unchanged code with the current interpreter, captures versions/stdout/stderr/exit in a timestamped `logs/author-code-...` folder and reports **REPLAY ONLY — NOT A PROOF**. It does not install dependencies, execute Sage, edit source, contact the network or update proof status. The recorded setup run is summarized in `Tools/author_code_observation.json` with output hash; logs are generated evidence, not required source files. Table values should be compared under any environment change.

## Later certification requirements

Freeze the accepted analytic branch formulas first. Then prove global monotonicity/convexity or cover compact parameter intervals with exact rational/interval certificates checked in Lean. Include endpoints, all σ in the source range, exact π/gamma/digamma enclosures, every k case and outward rounding. Retain raw author results even where a repaired rigorous decimal differs. DKKH-13/16/17 remain OPEN until actual mathematical consumers use these certificates. No `native_decide`, external assertion, trusted float or assumed optimizer maximum may close them.
