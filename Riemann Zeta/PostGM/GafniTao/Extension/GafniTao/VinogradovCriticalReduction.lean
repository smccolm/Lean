import GafniTao.HeathBrownKthDerivativeSetup
import GafniTao.FordMomentInterpolation

/-!
# Reduction of VMVT to the critical endpoint

The modern Vinogradov mean-value theorem is genuinely deep only at the
critical index.  This file proves the exact reduction used by Heath--Brown:
the critical bound in every degree implies every supercritical instance of
`HeathBrownVMVTMainConjecture`.  Thus no stronger all-moment statement remains
as an unexamined interface.
-/

open Complex Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

/-- The critical-endpoint form of the Vinogradov mean-value theorem. -/
def VinogradovCriticalEndpointTheorem : Prop :=
  ∀ (l : ℕ) (epsilon : ℝ), 1 ≤ l → 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧
      FordVinogradovMomentBound (fordVinogradovKappa l) l C epsilon

/-- The complete Weyl sum has its literal trivial pointwise bound `Q`. -/
theorem norm_fordVinogradovWeylSum_le
    (k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    ‖fordVinogradovWeylSum k Q α‖ ≤ Q := by
  unfold fordVinogradovWeylSum
  calc
    ‖∑ n : Fin Q, fordVinogradovMonomial n α‖ ≤
        ∑ n : Fin Q, ‖fordVinogradovMonomial n α‖ := norm_sum_le _ _
    _ = ∑ _n : Fin Q, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [fordVinogradovMonomial, UnitAddTorus.mFourier]
    _ = Q := by simp

/-- Raising the moment above a smaller index costs only the trivial
`Q^(2(s-s₀))` factor.  This is the exact normalized-Haar argument. -/
theorem fordVinogradovMomentNat_le_trivial_power_mul
    {s₀ s k Q : ℕ} (hs : s₀ ≤ s) :
    (fordVinogradovMomentNat s k Q : ℝ) ≤
      (Q : ℝ) ^ (2 * (s - s₀)) *
        fordVinogradovMomentNat s₀ k Q := by
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  let W : UnitAddTorus (Fin k) → ℝ :=
    fun α => ‖fordVinogradovWeylSum k Q α‖
  have hW : Continuous W :=
    (continuous_fordVinogradovWeylSum k Q).norm
  have hIntLeft : Integrable (fun α => W α ^ (2 * s)) μ := by
    rw [← integrableOn_univ]
    exact (hW.pow _).continuousOn.integrableOn_compact isCompact_univ
  have hIntBase : Integrable (fun α => W α ^ (2 * s₀)) μ := by
    rw [← integrableOn_univ]
    exact (hW.pow _).continuousOn.integrableOn_compact isCompact_univ
  have hIntRight : Integrable
      (fun α => (Q : ℝ) ^ (2 * (s - s₀)) * W α ^ (2 * s₀)) μ :=
    hIntBase.const_mul _
  have hPoint : ∀ α : UnitAddTorus (Fin k),
      W α ^ (2 * s) ≤
        (Q : ℝ) ^ (2 * (s - s₀)) * W α ^ (2 * s₀) := by
    intro α
    have hnorm : W α ≤ (Q : ℝ) := by
      exact norm_fordVinogradovWeylSum_le k Q α
    have hpow : W α ^ (2 * (s - s₀)) ≤
        (Q : ℝ) ^ (2 * (s - s₀)) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm _
    have hindex : 2 * s₀ + 2 * (s - s₀) = 2 * s := by omega
    rw [← hindex, pow_add]
    nlinarith [pow_nonneg (norm_nonneg (fordVinogradovWeylSum k Q α))
      (2 * s₀)]
  have hIntegral :
      (∫ α, W α ^ (2 * s) ∂μ) ≤
        ∫ α, (Q : ℝ) ^ (2 * (s - s₀)) *
          W α ^ (2 * s₀) ∂μ :=
    integral_mono hIntLeft hIntRight hPoint
  rw [integral_const_mul] at hIntegral
  simpa only [W, μ, ford_vinogradov_torus_real_mean_eq] using hIntegral

theorem fordVinogradovKappa_cast (l : ℕ) :
    (fordVinogradovKappa l : ℝ) =
      (l : ℝ) * ((l : ℝ) + 1) / 2 := by
  unfold fordVinogradovKappa
  rw [Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self l))
    (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  rfl

/-- A critical endpoint estimate gives every larger moment with the exact
main-conjecture exponent. -/
theorem FordVinogradovMomentBound.of_critical
    {l s : ℕ} {C epsilon : ℝ}
    (hs : fordVinogradovKappa l ≤ s)
    (hcritical : FordVinogradovMomentBound
      (fordVinogradovKappa l) l C epsilon) :
    FordVinogradovMomentBound s l C epsilon := by
  intro Q hQ
  have hraise := fordVinogradovMomentNat_le_trivial_power_mul
    (k := l) (Q := Q) hs
  have hcriticalQ := hcritical Q hQ
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hExp :
      ((2 * (s - fordVinogradovKappa l) : ℕ) : ℝ) +
          fordLambda34 (fordVinogradovKappa l) l epsilon =
        fordLambda34 s l epsilon := by
    unfold fordLambda34
    push_cast
    rw [Nat.cast_sub hs]
    ring
  calc
    (fordVinogradovMomentNat s l Q : ℝ) ≤
        (Q : ℝ) ^ (2 * (s - fordVinogradovKappa l)) *
          fordVinogradovMomentNat (fordVinogradovKappa l) l Q := hraise
    _ ≤ (Q : ℝ) ^ (2 * (s - fordVinogradovKappa l)) *
          (C * (Q : ℝ) ^
            fordLambda34 (fordVinogradovKappa l) l epsilon) := by
      gcongr
    _ = C * ((Q : ℝ) ^ (2 * (s - fordVinogradovKappa l)) *
          (Q : ℝ) ^ fordLambda34
            (fordVinogradovKappa l) l epsilon) := by ring
    _ = C * (Q : ℝ) ^ fordLambda34 s l epsilon := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_add hQpos, hExp]

/-- The endpoint family is logically sufficient for the all-supercritical
form used in Heath--Brown's paper. -/
theorem heathBrownVMVTMainConjecture_of_critical
    (hcritical : VinogradovCriticalEndpointTheorem) :
    HeathBrownVMVTMainConjecture := by
  intro l s epsilon hl hs hepsilon
  obtain ⟨C, hC, hmoment⟩ := hcritical l epsilon hl hepsilon
  exact ⟨C, hC, hmoment.of_critical hs⟩

#print axioms norm_fordVinogradovWeylSum_le
#print axioms fordVinogradovMomentNat_le_trivial_power_mul
#print axioms FordVinogradovMomentBound.of_critical
#print axioms heathBrownVMVTMainConjecture_of_critical

end

end GafniTao
