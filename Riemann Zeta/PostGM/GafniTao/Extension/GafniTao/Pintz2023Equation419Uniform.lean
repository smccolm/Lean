import GafniTao.Pintz2023Equation419Halasz

/-!
# Pintz (2023), equation (4.19): uniformity in the selected power

Equation (4.16) chooses the natural power only after the physical height is
fixed.  This file takes the finite intersection over all possible powers
`h < ceil (20 / epsilon)`.  Thus the constants and height thresholds used by
the Halasz estimate cannot depend on a power chosen later.
-/

open Complex Finset Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The exact fixed-height conclusion of the equation-(4.19) consumer. -/
def Pintz2023Equation419HalaszAt
    {eta target : ℝ} {k ell : ℕ}
    (data : Pintz2023PowerMarginData eta target k ell)
    (h : ℕ) (T : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∃ Ce Cd Cg : ℝ,
    0 < Ce ∧ 0 < Cd ∧ 0 < Cg ∧
    (N₀ : ℝ) ≤ T ^ pintz2023EllThreshold eta data.epsilon ell ∧
    ∀ (X U N : ℕ) (R : ℝ) (baseI : Finset ℕ)
      (Z : Finset ℝ) (etaAt : ℝ → ℝ),
      let epsilonCoeff := data.epsilon / (100 * (k : ℝ))
      let A :=
        ((1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) /
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
      let E := Ce ^ 2 * pintz2023HalaszKernelConstant⁻¹ *
        (N : ℝ) ^ (-4 * eta - 2 / pintz2023SourceLambda T k +
          2 * epsilonCoeff)
      let D := pintz2023NearOneDiagonalMajorant Cd N eta eta
      baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N → N₀ ≤ N →
      1 ≤ T →
      T ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      (N : ℝ) ≤ T ^ (3 : ℝ) →
      IsSeparated (3 * pintz2023SourceLambda T k) Z →
      (∀ u ∈ Z, etaAt u ∈ Set.Icc 0 eta) →
      (∀ u ∈ Z, ∀ v ∈ Z, |v - u| ≤ T) →
      (∀ u ∈ Z,
        A ≤ ‖dirichletPoly N
          (pintz2023SmallMPoweredLineCoeff X R baseI h
            (1 - etaAt u + 1 / pintz2023SourceLambda T k)) u‖) →
      (Z.card : ℝ) * A ^ 2 ≤ 2 * E * D

/-- Fixed-power equation (4.19), repackaged with all its constants visible at
the chosen height. -/
theorem eventually_pintz2023_equation419_halasz_at
    {eta target : ℝ} {k ell h : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell)
    (hh : 0 < h) :
    ∀ᶠ T : ℝ in atTop, Pintz2023Equation419HalaszAt data h T := by
  obtain ⟨N₀, Ce, Cd, Cg, hCe, hCd, hCg, hEventually⟩ :=
    exists_eventually_pintz2023_equation419_halasz_native hcell data hh
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have ha : 0 < pintz2023EllThreshold eta data.epsilon ell := by
    unfold pintz2023EllThreshold
    exact one_div_pos.mpr (pintzEllDenominator_pos hell data.ell_margin)
  have hScale := (tendsto_rpow_atTop ha).eventually
    (eventually_ge_atTop (N₀ : ℝ))
  filter_upwards [hEventually, hScale] with T hT hN₀
  exact ⟨N₀, Ce, Cd, Cg, hCe, hCd, hCg, hN₀, hT⟩

/-- One height threshold works for every power that equation (4.16) can
select.  This is the finite-uniformity bridge needed to consume that
equation without reversing quantifiers. -/
theorem eventually_forall_pintz2023_equation419_halasz_at
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∀ᶠ T : ℝ in atTop, ∀ h ∈ Finset.range (⌈20 / data.epsilon⌉₊ + 1),
      0 < h → Pintz2023Equation419HalaszAt data h T := by
  have hEach : ∀ h ∈ Finset.range (⌈20 / data.epsilon⌉₊ + 1),
      ∀ᶠ T : ℝ in atTop,
        0 < h → Pintz2023Equation419HalaszAt data h T := by
    intro h hhRange
    by_cases hh : 0 < h
    · filter_upwards [eventually_pintz2023_equation419_halasz_at
        hcell data hh] with T hT
      intro _hh
      exact hT
    · filter_upwards [] with T
      intro hhPositive
      exact False.elim (hh (by omega))
  exact (Finset.eventually_all
    (Finset.range (⌈20 / data.epsilon⌉₊ + 1))).2 hEach

#print axioms eventually_pintz2023_equation419_halasz_at
#print axioms eventually_forall_pintz2023_equation419_halasz_at

end


end GafniTao
