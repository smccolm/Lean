# Gafni-Tao research agenda

**Status:** the stated release-scope theorem chain is kernel-checked; external
semantic review and optional source extensions remain separate work.

**Suggested commit message:** `PostGM Gafni-Tao: finalize native release with zero-warning pinned PNT closure`

The owner supplies this message to `push_to_github.bat`. The push script is not
part of the build and must not be run by an agent without explicit instruction.

## 1. Research objective

The program formalizes Gafni-Tao arXiv `2505.24017v1` for exceptional short
intervals, using a read-only frozen Guth-Maynard foundation. Its release scope
is:

1. the source definitions of the exceptional-set exponent `mu`, ordinary
   zero-density exponent `A`, and four-zero energy exponent `A*`;
2. the Section 2 analytic transfer, including equations (2.3)-(2.7) and
   Lemmas 2.1-2.4;
3. native Gafni-Tao Theorems 1.1, 1.2, and 1.3;
4. actual use of the frozen Guth-Maynard density theorem at `A0=30/13`;
5. the two displayed Section 3 inequalities
   `mu(17/30)<=7/12` and
   `mu(2/15+Delta)<=1-9*Delta/13` for `0<Delta<=1/100`.

This is a formalization of published mathematics, not a claim of a new theorem
or a path to the Riemann Hypothesis.

## 2. Exact public outputs

The central release endpoints are:

```lean
GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem12_max_native
GafniTao.gafniTaoTheorem11_guthMaynard_native
GafniTao.gafniTaoTheorem11_guthMaynard_allIntervals_regression
GafniTao.gafniTaoTheorem11_guthMaynard_almostAll_regression
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native
GafniTao.exceptionalExponent_two_fifteenths_add_le_native
```

Theorem 1.3 has the exact outer shape:

```lean
exceptionalExponent theta <= refinedExceptionalUpperExponent theta
```

and `refinedExceptionalUpperExponent` retains the source
`inf_{epsilon>0}`. Its fixed-epsilon inner term is the supremum over the actual
ordinary-density constraint of

```text
min(
  (1-theta)*(1-sigma)*A(sigma) + 2*sigma - 1,
  (1-theta)*(1-sigma)*A*(sigma) + 4*sigma - 3
).
```

No continuity or attainment of `A` is assumed. The alternate maximum theorem
restricts the nontrivial optimization to the strict upper half strip and adds
the source `max(1-theta,...)` term.

## 3. Source objects

The release uses the literal measurable set

```text
{x in [X,2X] :
  |sum_(x<n<=x+x^theta) Lambda(n) - x^theta| >= delta*x^theta}.
```

`mu_delta` is defined by a fixed-power eventual bound, without adding an
epsilon to its defining exponent. `mu` is the positive-threshold supremum,
with a proved countable diagonal form and the extended-real empty-supremum
convention.

`A` is the least exponent for the multiplicity-weighted zero rectangle count
in the source epsilon-power sense. `N*` counts ordered zero quadruples with
product analytic multiplicity and tolerance
`|gamma1+gamma2-gamma3-gamma4|<=1`; `A*` is its epsilon exponent.

## 4. Section 2 proof route

The formal route is:

```text
real Chebyshev/Mangoldt identity
  -> local multiplicative cover and x^theta-to-x/tau replacement
  -> sharp truncated explicit formula at physical height
  -> equations (2.3)-(2.4)
  -> native VK vanishing plus native logarithmic near-one density
  -> Lemma 2.1
  -> strip L-infinity estimate (Lemma 2.2)
  -> compact bump, Fourier decay, exact c_rho
  -> second moment (Lemma 2.3)
  -> pair count / Schur / N* bridge
  -> fourth moment (Lemma 2.4)
  -> half-open J-strip alternatives and equation (2.7)
  -> epsilon/J limit assembly
  -> Theorems 1.3 and 1.2.
```

The sharp explicit formula keeps the zero multiplicities, sign, pole,
trivial-zero and endpoint contributions, prime powers, chosen height, and the
`x log^2(x)/T` error scale visible in the theorem chain.

The exponent ledger preserves the local-cover multiplicity, logarithmic
losses, `2/J`, `4/J`, epsilon margins, and the paper's order of limits.

## 5. Theorem 1.1 and frozen Guth-Maynard

`ZeroEnergy.lean` converts the real frozen theorem
`RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native` into the
ordinary density envelope. `Theorem11.lean` then applies the Gafni-Tao
transfer; it does not accept the desired result as a hypothesis.

At `A0=30/13`, exact arithmetic gives:

- all intervals for `theta>1-1/A0=17/30`;
- almost all intervals for `theta>1-2/A0=2/15`;
- one measurable exceptional set outside which the asymptotic holds, with
  ordinary natural density zero.

## 6. Published Section 3 inputs and samples

The second sample consumes the native Pintz cutoff
`pintzTwentyThreeTwentyFourCutoff_native`. The first sample consumes the two
native Heath-Brown four-zero energy cells reached when the optimizer is
confined around `sigma=7/10`. The proof never assumes the stronger complete
three-cell predicate.

The public sample statements are:

```text
mu(17/30) <= 7/12

0 < Delta <= 1/100
  -> mu(2/15+Delta) <= 1-9*Delta/13.
```

The rational range `Delta<=1/100` is an explicit sufficient-smallness range,
not an informal neighborhood.

## 7. Verification and dependency integrity

The isolated package is pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The command of record is:

```powershell
cmd /c run_gafni_tao_build.bat --no-pause
```

The runner checks source hashes, verifies and builds the minimal local PNT+
closure, builds the release root, rejects every warning and linter diagnostic,
executes the central axiom audit, scans Lean source for forbidden proof
shortcuts, and saves an unsuppressed timestamped log. Module-local axiom-print commands were removed after their results were
consolidated in `GafniTao/Audit.lean`; this eliminates repeated informational
noise without weakening the audit.

The accepted dependency output for public endpoints is limited to Lean/Mathlib
logical axioms normally reported as `propext`, `Classical.choice`, and
`Quot.sound`. It must not include `sorryAx` or a project postulate.

The isolated dependency is the exact 83-file transitive PNT+ closure required
by the frozen foundation and Gafni-Tao. Eighty-two files are byte-identical to
revision `4ecb950126c4290293c5662dfe0e884123171df5`; the sole edit deletes four
unreachable declarations from `Wiener.lean`, including the two admitted
Fourier-decay declarations. Their absence changes no retained theorem. The
runner validates that provenance and rejects every diagnostic. See
`Reproduction Manifest.md` for the full ledger.

The recorded release run passed on 2026-09-07 at 03:32:47 -07:00. It built
3,592 local PNT+ jobs and 10,344 Gafni-Tao jobs with zero diagnostics and saved
the complete output as `logs/gafni_tao_release_20260907_033222.log`.

## 8. Source and theorem audit discipline

The following tests remain distinct:

1. **Kernel test:** Lean accepts the proof term and its axiom output is clean.
2. **Semantic test:** the public theorem unfolds to the source object with the
   same ranges, multiplicities, endpoints, limits, and dependency edges.
3. **Release test:** the theorem is reachable from the root, centrally audited,
   reproducible from pinned inputs, and documented without overclaim.

All three are required for a checked Shitlist theorem item.

## 9. Explicitly optional continuation

The current release deliberately does not claim:

- Ford's optimized numerical constants in the older zeta-growth and density
  estimates;
- the third/high Heath-Brown energy cell;
- the complete best-known Section 3 piecewise curve or its plotted optimizer;
- external expert validation, peer review, publication, or canonicality.

These are separately scoped research extensions. Their absence does not enter
the proof terms of Theorems 1.1-1.3 or the two released sample inequalities.

## 10. Maintenance rule

Any later change to a public statement or dependency edge must update, in the
same revision:

- `Gafni-Tao Architecture.md`;
- `Gafni-Tao Crosswalk.md`;
- `Gafni-Tao Shitlist.md`;
- this agenda;
- `README.md`;
- `Extension/GafniTao/Audit.lean`; and
- the suggested commit message above.

Do not run `push_to_github.bat` as part of proof verification.
