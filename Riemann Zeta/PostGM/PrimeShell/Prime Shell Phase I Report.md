# Prime Shell Phase I Report

Date: 2026-08-29

## Verdict

Prime Shell Phase I (PSH-01 through PSH-06) is complete in the isolated subtree. The exact result is an **F1 FAIL for the collapsed Guth–Maynard shift-prefix interface**.

The source prime-prime term and its dyadic difference-frequency off-diagonal have been exposed exactly. The literal dyadic kernel is `K(N,T,n,h)`, not a scalar `K(N,T,h)`. Anchoring it produces a scalar prefix-consumable term plus an exact two-variable variation remainder. Lean proves:

1. the scalar term is controlled by cumulative prefixes through an exact finite Abel identity;
2. a universal consumer using only collapsed shift prefixes forces the kernel rows to be identical; and
3. whenever two literal rows differ at one positive shift, all collapsed prefixes can vanish while the corresponding kernel functional is nonzero.

Therefore GM Corollary 1.4, converted only into cumulative shift information, is not by itself a faithful input to this trace calculation. A direct bound for the exact variation remainder, or `n`-localized/rectangle-prefix correlation information, is required.

This report does not claim that GM is useless, that the concrete AF kernel has been numerically proved nonconstant at a named tuple, that MRT already suffices, that the disconnected shell is admissible, or that any new zero theorem has been proved.

## Isolation boundary

- Frozen GM boundary: commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`.
- No file under `RiemannZeta/` or `RiemannZeta.lean` was edited.
- The extension is rooted at `PostGM/PrimeShell/Extension/`; its Lake manifest pins the Zeta23 Git dependency to the exact release commit.
- Nothing from this experiment is imported into the frozen project root.

## Pinned Zeta23 reproduction

The reproduction was performed in `PostGM/PrimeShell/upstream/formal-math-v1.0`, which remained clean at the exact release state throughout the checks. Afterward, the extension was changed to a Git dependency at the same SHA and Lake checked out that dependency under `Extension/.lake/packages/Zeta23`. The old ignored upstream working copy was removed so the frozen GM verifier would not mistake external Comparator challenge stubs for project-owned source.

The reproduced state was:

- Anthropic `formal-math` tag `v1.0`;
- tag object `82ee6340d6fb15d51fc73ba1ba7b8cac672a7bba`;
- commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`;
- Lean `v4.33.0-rc2`;
- Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

Results:

| Check | Result | Qualification |
|---|---|---|
| `lake build` | exit 0; 9010 jobs | Unchanged upstream emitted 247 warning lines. This is not represented as a zero-warning upstream build. |
| Released solution builds | exit 0 | Base, multiplicity, and XiPrime solutions built. |
| Axiom probes | pass | Reported only `propext`, `Classical.choice`, and `Quot.sound`; one specialized law needed fewer. |
| Comparator base topic | accepted | Windows development replay; default Lean kernel accepted and Comparator reported “Your solution is okay!”. |
| Comparator multiplicity topic | accepted | Same qualification. |
| Comparator XiPrime topic | accepted | Same qualification. |
| Official `landrun` | unavailable | The official runner is Linux-only; no WSL distribution was installed. |
| `nanoda` alternative | failed to build | Missing Visual C runtime import library `msvcrt.lib`. |

Comparator was pinned at `71b52ec29e06d4b7d882726553b1ceb99a2499e0`, `lean4export` at `15f6055e299ad5b89345e533cc2192f4cc00f659`, and the attempted `nanoda` alternative at `68d5ca9db226849b41a6fff59d796ff19d0a8840`. No successful local `landrun` checkout or execution is claimed. The Comparator runs are explicitly a development replay, not a successful trusted-sandbox reproduction.

SHA-256 hashes of the retained logs:

| Log | SHA-256 |
|---|---|
| `00-lake-version.log` | `FA8AC01C3DD2EC91BEF7F22A89FC4AC5FCED74A5B70D90C675CB74E3DD9EC181` |
| `01-cache-get.log` | `F40462E136106DBEE07ABC6293723186BB9C71AEDC0637809FB0949D35418BBC` |
| `02-lake-build.log` | `2F64EA46C40FDC1083B51B40D0B96E3CE05A0285F4F9393D954DABFAF86875DF` |
| `03-solution-builds.log` | `0E229FD8D3027713EDDCF1CF4B6D8D9129F79D26CF42D4A9B63905A4D99BF415` |
| `04-axioms-base.log` | `87135DE3C5855D8559FE2B477B56144FD39A95C83B8BB55F47FAE83C433EF723` |
| `05-axioms-multiplicity.log` | `1B79BF7E576B4D4A4F07AC33F83F097C13318D6563B1312001D6CF886DE718B7` |
| `06-axioms-xiprime.log` | `733099A851BB9537853A46829B60EAA49D5043D6AC2A9F3F9D484D732DD6FAEB` |
| `07-axioms-pairceiling.log` | `73F6BDE6B5BD7DBA9C3B05FD33D6C8BAE639B9B55457D578382245B0C09E8276` |
| `08-comparator-base-windows-trial.log` | `FC4E377A63A694EB0C3DAB2C31FEB853957CC224450ACB671AF92BA6A0036B95` |
| `09-comparator-base-windows-trial.log` | `0F06CEB4F60076EE06B310723BE23AA306D7822517683AD1D45901A4DB75A44F` |
| `10-comparator-base-windows-trial.log` | `2D2E9CEEFE83687B5E45A920510F0280541919CD0584AAA8EFE3EDD6EF8EFB42` |
| `11-comparator-base-windows-trial.log` | `E8355DDEC5ADA06F7D961F971EE76E5518BE5707E0860F2DB8CF5E9989CA435D` |
| `12-comparator-multiplicity-windows-trial.log` | `4B4499944F6DE4684560E76CD5FE970FEA9D45D260BDB1F832625A6AD51375E4` |
| `13-comparator-xiprime-windows-trial.log` | `D1730619D339F323942058867812805D25A132BD38796E68E8D26C2510676912` |

## Exact paper-to-Lean crosswalk

Authoritative paper: Alpoge–Furman, arXiv:2608.13637v2.

| Paper item | Exact source content | Zeta23 declarations | Match status and conventions |
|---|---|---|---|
| Equation (2.7) | `φ(u)=χ(L/2+u)χ(L/2-u) ψ(u/L)^(1/2)`, with `L=log(T/2π)`, `X=e^L=T/(2π)`, even compact support `[-L/2,L/2]`. | `Zeta23.Params.phi` in `Zeta23/Defs.lean`; `Zeta23.Taper.phi` in `Zeta23/Taper/Basic.lean`; Montgomery–Taylor specialization `Zeta23.ThmD.vStar` and `Zeta23.ThmD.phiD` in `ThmD/Functional.lean` and `ThmD/Window.lean`. | **Not a single verbatim declaration.** Base `Params.phi u = ρ((L/2-|u|)/w)` is the flat taper. `phiD = sqrt(vStar lam (u/L))*Taper.phi` is the MT-window specialization. Documentation must not identify either alone with the fully generic paper formula. |
| Equation (5.10) | Six-term bilinear expansion of `M[μ+P_X+Π_X, μ+P_X+Π_X]`. | `Zeta23.PrimeSide.eq_Msplit` in `Zeta23/PrimeSideA.lean`. | Exact six-term equality. `Mform` integrates over `Set.Icc T (2*T) × Set.Icc T (2*T)`; endpoints are included, immaterial to Lebesgue measure but explicit in Lean. |
| Equation (5.11) | `∫ Φ(x)^2 exp(i x y) dx = 2π g(y)`. | `Zeta23.PrimeSide.LocalHypsCore.Phi_sq_fourier` in `Zeta23/PrimeSideA/Basic.lean`, instantiated by `Params.integral_PhiR_sq_mul_cos` through `PrimeSideA/Bridge.lean`. | Lean uses the real cosine form `∫ x, Φ x ^ 2 * cos(x*y) = 2π*g y`, justified by real evenness. Paper Fourier transform is `∫f(u)e^{iτu}du`; Mathlib uses the `e^{-2πivw}` convention, bridged in the explicit-formula code by `paperFT_ofReal_eq_fourier`. |
| Proposition 5.4 | `M[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)^2/n g(log n) + Oχ(L²X)` for the source regime. | Exact equality `Zeta23.PrimeSide.Mform_PX_PX` in `PrimeSideB/PP.lean`; bound `Zeta23.PrimeSide.prop_PP` in the same file; `primeRange X = Finset.Ioc 0 ⌊X⌋₊` and `acoef n=Λ(n)/sqrt(n)` from `PrimeSideA/Defs.lean`. | `Mform_PX_PX` splits diagonal difference frequency, off-diagonal difference frequency, and sum frequency with factor `1/(2π²)`. `prop_PP` gives an eventual constant bound `≤ C*(L²X)`. The `X≤T` regime is supplied by `PrimeSideB.eventually_X_le_T` and, in final assembly, `Zeta23.X_le_T`. |
| Theorem 5.7 | `||G̃||_HS² = (R(ψ)+Oχ(L^-1)) N(T,2T)` for the paper's admissible window. | Base-window trace package: `PrimeSide.tr2_first`, `PrimeSide.tr2`, `PrimeSide.ratio`, `PrimeSide.tracesBounds_of_facts`, and `PrimeSide.thm_traces_of_localHyps` in `PrimeSideB.lean` / `PrimeSideB/Traces.lean`. MT-window package: `ThmD.TracesBoundsD`, `ThmD.tr2D_pointwise`, `ThmD.ratioD_pointwise`, `ThmD.tracesBoundsD_of_factsD`, and `ThmD.tracesBoundsD_concrete`. | **Packaged specialization, not one theorem with the paper's generic `ψ` statement verbatim.** The base package records the Hilbert–Schmidt second trace and ratio for the flat taper; `ThmD` retains the MT window parameters `a`, `b`, and `J`. Downstream `ThmTracesHyp` is the consumed trace interface. |
| Section 7.2 obstruction | For `X≫T`, the prime off-diagonal is no longer absorbed by the diagonal error; extended support requires prime-pair information. | The restriction is visible in `PrimeSideB.eventually_X_le_T`, `PrimeSideB.regime`, and final `Assembly.X_le_T`; the unestimated exact term is exposed upstream by `Mform_PX_PX` and in this extension by `primeResonantDifference`. | Zeta23 proves the `X≤T` specialization. It does not prove the beyond-support-one prime-pair estimate. Phase I exposes rather than assumes that missing term. |

Further exact conventions:

- `primeRange X` is `(0, floor(X)]`, hence includes all prime powers through the von Mangoldt weight, not only primes.
- `PX X τ = -(1/π) Σ a_n cos(τ log n)`.
- The dyadic extension uses `Finset.Ioc N (2*N)` and positive shifts `Finset.Icc 1 H`; the condition `n+h ∈ Ioc N (2*N)` retains the right-edge truncation literally.
- `IsPrimeResonant T n m` is the literal condition `|T*(log n-log m)|≤1`; it is not replaced by `h≲N/T` until a proved consequence is invoked.

## Extension theorem ledger

### Exact prime-prime source decomposition

- `primeDifferenceOffDiagonal_eq_resonant_add_nonresonant`
- `primePrime_exact_decomposition`
- `primePrime_exact_source_ledger`
- `primePrime_sub_main_exact`
- `primePrime_bound_regression_from_exact_decomposition`

The regression theorem has the same eventual `C L²X` conclusion as upstream `prop_PP` and rewrites both its proof and target through the exact decomposition. It is not a detached restatement.

### Literal dyadic kernel

- `dyadicDifferenceOffDiagonal_eq_shiftSum`: exact upper-triangle and `m=n+h` bijection.
- `dyadicShiftSum_eq_kernel_mul_correlation_add_remainder`: exact anchor-plus-variation identity.
- `abs_dyadicKernelVariationRemainder_le_literal_sum`: retains `|K(n,h)|+|K(N+1,h)|`, the source coefficient normalization, and endpoint indicator.
- `dyadicLambdaCorrelation_eq_zero_of_N_le_h` and `dyadicShiftSum_eq_of_N_le_H`: exact shift support/tail.
- `dyadicLambdaWeight_nonneg`: arithmetic sign ledger.
- `abs_dyadicShiftKernel_le`: explicit difference-frequency size bound.
- `resonant_log_shift_implies_range`: literal logarithmic resonance implies `(2T-1)h≤2n`.

There is no asserted fixed sign for the oscillatory kernel. The proved sign statement concerns the von Mangoldt coefficient product; the two kernel orientations remain explicit.

### Narrow GM interface

`GMCorollary14PiFinite` is the fixed-length finite proposition matching the published `π` statement. `GMCorollary14LambdaFinite` is the narrow post-partial-summation proposition needed by the cumulative route. Neither is an axiom, theorem, instance, or hypothesis of a public unconditional result.

The file separately proves or exposes:

- the exact prime-log plus proper-prime-power decomposition;
- `(x,x+H]` versus `[x,x+H]` endpoint correction;
- exceptional sets for prime and Lambda errors;
- Lambda-weighted and exact Zeta23-`acoef` exceptional-mass losses;
- finite simultaneous-length union cost;
- the exact cumulative-correlation-to-short-interval identity; and
- `GMSection132Dependencies`, listing partial summation, proper prime powers, explicit-formula truncation, the near-one logarithmic density estimate, the Vinogradov–Korobov zero-free region, and the short-interval mean-square step.

This is an interface derivation and bookkeeping result, not a formalization of GM Corollary 1.4.

## F1 theorem-level verdict

The exact source identity is

`dyadicShiftSum = Σ_h K_anchor(h) * dyadicLambdaCorrelation(N,h) + dyadicKernelVariationRemainder`.

`finite_abel_identity` and `abs_weighted_sum_le_of_prefix_bound` prove that a uniform prefix estimate controls the first term by the endpoint size plus total scalar variation. `abs_dyadicShiftSum_le_of_prefix_and_variation` proves the complete consumer once a direct `DyadicKernelVariationBound` is supplied.

The obstruction is exact information loss. `PrefixOnlyTwoPointTransfer K0 K1` says that every array with zero collapsed prefixes must have zero kernel functional. `prefix_only_two_point_transfer_forces_row_constancy` proves this implies `K0(h)=K1(h)` for every positive `h`. The counterexample places `+1` and `-1` in two rows at one shift, so every collapsed prefix is zero while the functional is `K0(h)-K1(h)`.

Consequently:

- **PASS:** scalar Abel transfer for the anchored term;
- **FAIL:** a consumer whose only arithmetic input is the collapsed shift prefix, unless literal row constancy is additionally proved;
- **missing faithful input:** direct control of the exact variation remainder or `n`-localized/rectangle-prefix correlation control;
- **not claimed:** a concrete evaluated nonconstancy witness for the AF taper.

MRT's almost-all fixed-shift theorem is the next justified source to inspect because it retains more shift-local information than GM's collapsed cumulative route. It is not yet known to control the literal two-variable weight, so PSH-07 and later items remain open.

## Strict scale consequences

The extension proves:

- `resonant_scale_of_power`: if `N=T^α`, then `N/T=T^(α-1)`;
- `gm_overlap_iff_alpha_gt_fifteen_thirteenths`: for positive `α`, `2/15 < 1-1/α` iff `15/13 < α`;
- `exists_strict_gm_margin_iff_alpha_gt_fifteen_thirteenths`: a positive epsilon margin exists exactly when `α>15/13`;
- `resonant_log_shift_implies_range`: an exact, non-asymptotic resonance-to-shift bound.

These are scale consequences, not a support theorem or a trace estimate.

## Verification

The isolated extension was checked with:

```text
lake build PrimeShell
lake env lean PrimeShell/Audit.lean
```

The build completed 8710 jobs with exit code 0 and no Lean warning output. The audit lists every new public theorem and reports only the permitted standard dependencies `propext`, `Classical.choice`, and `Quot.sound` (some theorems use a subset).

Repository scans of the extension found no `sorry`, `admit`, `sorryAx`, project `axiom`/postulated `constant`, `native_decide`, `implemented_by`, or `unsafe` bypass.

The frozen repository's principal verifier was then rerun after the external Zeta23 checkout had been moved behind the ignored, exact Git dependency. It returned exit code 0 with:

```text
FINAL RESULT: PASS
Root/default production build: PASS
Exact publication contract: PASS
Retained regressions: PASS
Transitive axiom and exact-output audit: PASS
Declaration linter gate: PASS
Found 0 errors in 9402 declarations (plus 7925 automatically generated ones)
```

The audit covered 14,290 discovered nonprivate project theorems and reported only the permitted dependencies `propext`, `Classical.choice`, and `Quot.sound`. The timestamped verifier evidence is `logs/foundation_freeze_20260829_194359.log` with manifest `logs/foundation_freeze_20260829_194359.json`. This verifies that the Prime Shell subtree did not disturb the frozen GM build; it is not semantic evidence beyond the theorem-level claims itemized above.

## Scope and next decision

Phase I closes the proposed GM-prefix route. It does not authorize disconnected-shell optimization, a full formalization of GM short intervals, or a zero-side theorem. The next rational research action is to test whether MRT-style fixed-shift information, or a direct source-specific variation estimate, controls the exact `K(N,T,n,h)` remainder. That is a new bounded goal, not part of this completion claim.
