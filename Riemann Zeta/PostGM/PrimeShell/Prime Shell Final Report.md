# Prime Shell Final Report

Date: 2026-08-30

## Verdict

Prime Shell reached terminal state **ROUTE DISPROVED**. It did not produce a new zero theorem.

The public endpoint is:

```lean
theorem primeShell_universal_no_gain_native :
    ∀ S : FaithfulAmplitudeShell, ∀ delta : ℝ, 0 < delta →
      ¬ ((2 / 3 : ℝ) + delta <
        2 - kappaXi S.A.toPrimeShellAdmissible.P.lam (amplitudeSq S.q))
```

The class is separately proved inhabited:

```lean
theorem faithfulAmplitudeShell_nonempty : Nonempty FaithfulAmplitudeShell
```

Thus the terminal theorem is not an implication over an empty class.

## Correction of the provisional F2 argument

The former terminal claim put a literal zero gap into a total `WindowProfile v` and then contradicted Zeta23’s strict positivity field. That only showed that this particular interface was unsuitable for a disconnected total profile. It did not rule out the source construction itself.

The corrected construction starts with a smooth nonnegative amplitude `q`, permits zeros of `q`, and passes `q²` to `Params.atV`. The theorem `atAmplitude_phi` proves that the physical test function is exactly

```text
q(u / L(T)) * phi(u),
```

so no nonsmooth square-root substitution is hidden. `extendedFamilyHyps_atAmplitude` proves the complete extended explicit-formula family hypotheses in the source range `3 * lambda < 4`.

`twoBandAmplitude` is an explicit sum of smooth compactly supported bumps centered at `±999/2000`, with outer radius `1/2000`. Lean proves its evenness, nonnegativity, `C³` regularity, derivative bound, nonzero mass, support split, exact difference-set localization, and source-entry identities. These results build `concreteFaithfulAmplitudeShell` at `lambda = 199/150`, proving non-vacuity.

## Exact universal obstruction

For a faithful shell let:

- `g = rightEdge - leftEdge` be the open gap length;
- `m = 1 - g` be the total permitted support length inside `[-1/2,1/2]`;
- `v = q²`;
- `I = ∫ v` and `J = ∫ v²` over the normalized interval; and
- `W = jWin D1 lambda v`.

The proof has four exact components.

1. `amplitudeSq_integral_cauchy_of_separated_support` proves Cauchy–Schwarz on the literal support:

   ```text
   I² ≤ m * J.
   ```

2. Strict cross-band separation is the field `1 < lambda * g`. The full explicit-formula range supplies `lambda < 4/3`. Together they imply

   ```text
   3 * lambda * m < 1.
   ```

3. Positive mass gives `I > 0`; the support inequality then gives `J > 0`. `jWin_D1_nonneg_extended` proves `W ≥ 0` from the actual nonnegative D1 kernel, without imposing a support-one upper bound on `lambda`.

4. The exact Zeta23 definition unfolds to

   ```text
   kappaXi lambda v = (J + lambda * W) / (lambda * I²).
   ```

   Therefore `3 * lambda * I² < J + lambda * W`, and hence `3 < kappaXi lambda v`.

`FaithfulAmplitudeShell.kappaXi_gt_three` is the assembled theorem. Since the exact spectral output is `2 - kappaXi`, `FaithfulAmplitudeShell.no_positive_gain` and `primeShell_universal_no_gain_native` follow. The direct proposition `FaithfulSeparatedAmplitudeGain` is proved equivalent to `False` by `faithfulSeparatedAmplitudeGain_iff_false`.

The obstruction does not depend on the size of an arithmetic error. Perfect control of every prime term would still leave the spectral quotient above three.

## Concrete F1 result

The Phase-I F1 result remains valid and independent. `KernelSymmetry.lean` and `ConcreteF1.lean` construct two explicit rows of the actual pinned `Params.PhiR` kernel in one dyadic block. One row is zero and another is positive at an explicit family of heights. Consequently `concrete_literal_prefix_only_transfer_fails` proves that collapsed Guth–Maynard shift-prefix data cannot control the exact two-variable kernel by the proposed prefix-only transfer.

This is not the terminal no-go: the universal spectral theorem above is stronger and does not depend on choosing GM, MRT, or any other arithmetic input.

## Arithmetic and success-branch status

The exact source decomposition, dyadic shift kernel, finite GM interfaces, Abel identities, and two-variable oracle consumers are preserved. They are not represented as unconditional prime-correlation theorems.

The success-branch obligations to formalize GM or MRT and propagate a positive shell certificate are closed as unnecessary under terminal state B. This is not a claim that their scale ranges are inconsistent. In fact the concrete `lambda = 199/150` proves a nonempty strict overlap between `33/25` and `4/3`; the failure is the exact spectral support-loss inequality.

`primeShellDelta` and `primeShell_simple_critical_line_native` do not exist, and no positive improvement or zero-count conclusion is claimed.

## Verification standard

The isolated root, changed modules, and `PrimeShell/Audit.lean` must elaborate at the exact pins. Audit output for the terminal chain is restricted to `propext`, `Classical.choice`, and `Quot.sound`. Repository scans forbid `sorry`, `admit`, `sorryAx`, project `axiom`/`constant` declarations, `unsafe`, `native_decide`, and `implemented_by`.

The immutable pinned Zeta23 source emits pre-existing warning and linter diagnostics when Lake replays it. Prime Shell does not suppress these or call the upstream build warning-free. Direct elaboration of Prime Shell source emits no project warning.

The frozen GM verifier is a separate check under Lean `v4.30.0`; it returned `FINAL RESULT: PASS`. Its evidence is `logs/foundation_freeze_20260830_040456.log` and `.json`. Prime Shell remains absent from `RiemannZeta.lean`. The owner-operated `push_to_github.bat` is not part of verification and was not run.

## External status

PSH-21 remains open. Kernel checking, local source reproduction, and a two-sided statement comparator are not independent expert review, peer review, publication, or community acceptance.
