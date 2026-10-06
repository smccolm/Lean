# Author computations — reproduction and proof boundary

## Owner-approved corrected contracts — 5 October 2026

The owner has explicitly adopted all five proposals in the attached instruction accompanying “Proceed”: the Part-II E₁ envelope A−(B−C)/y; the four positive-frequency quotient monotonicity conditions for h=g′ and h=g(f′−N); the full-positive-gap Corollary 0.1 repair with halfSecondEndpointDelta and the complete finite-head coefficient; the proof-consistent Theorem-10 branch assignments; and every certified Table 1–2 proposal in Computation Review at commit a9ddec65b578914f19199443a3e8ffa3a406e8e8. The present values are identical to that commit. The literal Corollary 0.2 remains unchanged. These are owner-approved local corrected contracts, not author-issued corrections.

All original displays, counterexamples and proof diagnostics remain preserved. Historical sections saying “pending” describe their original checkpoint and are superseded by this decision. All explicit public consumers, the final semantic comparison and sequential release verification have passed: 20/20 gates are accepted. No scope decision listed here remains blocked on owner approval.

The owner also authorizes mathematically justified repairs of this class without repeated approval. First attempt an independent proof of the original conclusion under the original hypotheses. When a repair is necessary, preserve the original, identify the precise failure, prove the replacement, expose every changed hypothesis/constant, verify its applications, and distinguish failed proof steps from false theorems. Escalation is reserved for abandoning a required result, changing the central objective, or unresolved competing contracts that materially change the program. Proof integrity, source preservation and acceptance checks remain mandatory.

Research date: 5 October 2026. Original scripts are unchanged under `Sources/DhimanKadiriQuesadaHerrera-v1-source/anc/`. Archive hashes cover both. No code from these files is imported into a Lean proof.

## AFE1.sage

Header specifies SageMath 9.5. The code sets exact rational `g1=1413472/100000` and `H=3*10^12`, defines m(c) as C(x), differentiates symbolically, and uses `RIF` to check two interval inequalities used in the real-cutoff transfer. It then prints c₀ using ordinary `n(...)` evaluation. The existence of interval comparisons does not imply that every printed decimal is outward-certified.

Read-only inspection completed; replay **NOT RUN**, because Sage is unavailable. This replay limitation is independent of the subsequently activated Lean goal. A future reproduction environment should pin Sage 9.5 (or record and compare a migration), capture the boolean interval results and enclosing intervals, and check all advertised decimal rounding. Do not substitute plain Python for Sage syntax and call that the same run.

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

Freeze the accepted analytic branch formulas first. Then prove global monotonicity/convexity or cover compact parameter intervals with exact rational/interval certificates checked in Lean. Include endpoints, all σ in the source range, exact π/gamma/digamma enclosures, every k case and outward rounding. Retain raw author results even where a repaired rigorous decimal differs. DKQH-13/16/17 remain OPEN until actual mathematical consumers use these certificates. No `native_decide`, external assertion, trusted float or assumed optimizer maximum may close them.

## AFE1 decimal certification and DKQH-13 acceptance review

AFEDigammaNumerics proves ψ(x)≥log(x)−1/(2x)−1/(12x²) for every x>0 by a positive logarithm series, an explicit rational remainder and a finite telescoping limit. The actual digamma recurrence and ψ(1)=−γ then bound both special-function values by 31 finite reciprocal terms and elementary logarithms. The logarithms use proved finite Taylor lower/upper bounds after argument reduction. AFEFirstConstants checks four finite rational certificates with ordinary kernel-checked norm_num; pi is rounded downward from Mathlib's proved enclosure, and each reciprocal argument is rounded upward using proved factor monotonicity.

All six branches in the exact c₀ maxima are bounded. afeFirstRealConstant_small_le proves c₀(14.13472)≤1.2552; afeFirstRealConstant_large_le proves c₀(3·10^12)≤1.2127. The public afe_first_kind_small_decimal and afe_first_kind_large_decimal consume those certificates and the actual real-cutoff AFE. Two unfolded source consumers preserve σ∈(0,1], the exact thresholds, inclusion of n=1, actual ζ and the displayed decimals. No assumption about zero verification or RH occurs. The current inventory is 87 files, twenty-one production modules and two verification modules. All new public declarations and consumers are registered. DKQH-13 is DONE after the exact-source review and sequential foundation/paper checks passed; the accepted count is 6/20.

The author programs remain frozen and their outputs remain computational observations. The new AFE1 certification is an independent analytic/rational proof; it does not use Sage, Python, floating-point values or an optimizer as proof evidence. The Python Fraction exploration only selected convenient outward rational endpoints; Lean independently proves their complete finite inequalities. AFE2/Table 1–3 certification remains open.

## Table 1 failures and proposed Table 2 certificates

TableLowerBounds proves a fourth-order upper estimate for the actual digamma function and a finite lower enclosure 0.577215664≤γ. Combined with rational logarithm/pi bounds, it proves that Table 1's direct entries 2.265204 at exact 2π, 1.792736 at 1000, and 1.750701 at 10¹⁰ are strictly below the actual direct maxima: sigma=1 supplies each witness. These are failures of the claimed numerical maximum bounds, not counterexamples to the zeta remainder inequality itself. The printed entries remain preserved.

AFETableTwo proves outward candidate bounds for all twenty cells at k=1,...,10, over the complete closed sigma strip. Finite exponential sums certify the floor-defined lower cutoffs. Distinct sigma ranges for the two A₀ inputs give separate direct/reflected rational certificates, propagated through the actual global maxima and then the actual two-polynomial AFE. The proposed decimals are listed in Computation Review and explicitly named proposedTableTwoDirect/proposedTableTwoReflected; they are not yet an adopted source repair.

The unchanged Table 3, large-k bound and constant-six consequence remain proved. DKQH-16/17 stay OPEN for the remaining Table 1 certificates and explicit adoption of numerical repairs. General Part-II and E03 decisions remain pending. Current scope: 137 retained files, 71 production and two verification modules, 113 semantic consumers; accepted count 8/20.

| k | Printed direct | Adopted direct | Printed reflected | Adopted reflected |
|---|---:|---:|---:|---:|
| 1 | 2.069011 | 2.069011 | 2.069008 | 2.069008 |
| 2 | 2.132269 | 2.132269 | 2.132265 | 2.132266 |
| 3 | 2.222299 | 2.222300 | 2.222296 | 2.222296 |
| 4 | 2.472238 | 2.472239 | 2.472235 | 2.472236 |
| 5 | 2.766225 | 2.766226 | 2.766222 | 2.766222 |
| 6 | 3.075279 | 3.075280 | 3.075276 | 3.075277 |
| 7 | 3.390201 | 3.390202 | 3.390198 | 3.390198 |
| 8 | 3.707264 | 3.707265 | 3.707261 | 3.707262 |
| 9 | 4.025115 | 4.025116 | 4.025112 | 4.025113 |
| 10 | 4.343256 | 4.343257 | 4.343253 | 4.343254 |

The proposed upper certificates do not by themselves assert that every changed original Table 2 entry is false. The three Table 1 failures above have separate lower-bound proofs. Adoption remains pending.

## Global chi-factor table certificates

ChiTableBounds bounds the actual C₁ on the entire closed sigma strip by a concave cubic and an explicit sum-of-squares identity. A finite Taylor remainder certifies C₂; finite positive exponential sums bound the remaining tails. The complete C₀ product and its actual attained maximum therefore give δ₀≤0.05961930 at exact 2π, δ₀≤0.0003692901 at 1000, δ₀≤3.692588·10⁻¹¹ at 10¹⁰, and δ₀≤1.230863·10⁻¹³ at 3·10¹². The last two are unchanged printed values; the first two are proposed outward replacements, not yet adopted. No optimizer output or sampled interval enters these proofs.

The remaining Table 1 epsilon assembly and numerical-repair adoption stay OPEN under DKQH-16. Table 2 candidates, unchanged Table 3, large-k and constant-six bounds are proved as described above. Pending Part-II and E03 decisions are unchanged. Current scope: 137 retained files, 71 production and two verification modules, 113 semantic consumers; accepted count 8/20.

## Complete proposed Table 1 AFE certificates

AFETableOne proves all sixteen proposed Table 1 cells over the entire closed sigma strip. The four thresholds retain exact 2π in the first row. The symmetric lower cutoffs are proved equal to floor(sqrt(t₀/(2π)))+1/2 and are derived from the physical height, half-integer condition and x=y; no extra symmetric-cutoff hypothesis remains. Separate actual direct, reflected and symmetric zeta-remainder theorems consume all coefficient certificates, preserve logarithmic factors and cover both signs of t.

The complete proposed Table 1 and Table 2 replacements are listed beside the preserved printed values in Computation Review. All unchanged Table 3 entries, k/π+1.1601 and the constant-six consequence are also proved. Numerical source-repair adoption and E03 remain pending before DKQH-16/17 can be accepted. The general Part-II decisions and DKQH-09–11 obligations remain separate. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.

| Exact threshold | Column | Printed | Adopted certified bound |
|---|---|---:|---:|
| 2π | Reflected x<y | 2.264445 | 2.264445 |
| 2π | Symmetric x=y | 2.265204 | 2.265207 |
| 2π | Direct x>y | 2.265204 | 2.265207 |
| 2π | δ₀ | 0.05961915 | 0.05961930 |
| 1000 | Reflected x<y | 1.792711 | 1.792711 |
| 1000 | Symmetric x=y | 1.265977 | 1.265978 |
| 1000 | Direct x>y | 1.792736 | 1.792737 |
| 1000 | δ₀ | 0.0003692900 | 0.0003692901 |
| 10¹⁰ | Reflected x<y | 1.750701 | 1.750701 |
| 10¹⁰ | Symmetric x=y | 1.160079 | 1.160080 |
| 10¹⁰ | Direct x>y | 1.750701 | 1.750702 |
| 10¹⁰ | δ₀ | 3.692588·10⁻¹¹ | 3.692588·10⁻¹¹ |
| 3·10¹² | Reflected x<y | 1.750689 | 1.750689 |
| 3·10¹² | Symmetric x=y | 1.160048 | 1.160049 |
| 3·10¹² | Direct x>y | 1.750689 | 1.750689 |
| 3·10¹² | δ₀ | 1.230863·10⁻¹³ | 1.230863·10⁻¹³ |

The proposal changes nine of the sixteen Table 1 cells and fourteen of the twenty Table 2 cells. All eight Table 3 entries remain unchanged. Three direct Table 1 entries have proved strict lower-bound counterexamples; the other changed entries are justified here by independent outward upper certificates, without asserting that each original entry has separately been refuted. The owner explicitly adopted this exact set of certificates on 5 October 2026. Public Lean identifiers beginning `proposed_table_` retain their original names for compatibility; their proved bounds are now the adopted contract.
