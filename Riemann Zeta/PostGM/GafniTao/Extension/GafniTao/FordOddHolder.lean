import GafniTao.FordBoundaryCover

/-!
# Ford Lemma 3.2: powered Hölder form

The odd moment is converted to the integer-powered form used in Ford's
contradiction argument.  All three factors are the literal torus integrals:
the even factor is `S₄`, and the zeroth residue factor is the polynomial
collision count.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

theorem fordS4OddIntegral_nonneg
    {k d T P p : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (s Q q : ℕ) (c : ZMod p) :
    0 ≤ fordS4OddIntegral (P := P) Ψ hdk s Q q c := by
  unfold fordS4OddIntegral
  exact integral_nonneg fun _ ↦ mul_nonneg (sq_nonneg _) (by positivity)

theorem ford_odd_integral_pow_le
    {k d T P p s Q q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (c : ZMod p) (hs : 1 ≤ s) :
    fordS4OddIntegral (P := P) Ψ hdk s Q q c ^ (2 * s) ≤
      (fordS4Count (P := P) Ψ hdk s Q q c : ℝ) ^ (2 * s - 1) *
        (fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk : ℝ) := by
  let A : UnitAddTorus (Fin k) → ENNReal := fun α ↦
    ENNReal.ofReal
      (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2)
  let B : UnitAddTorus (Fin k) → ENNReal := fun α ↦
    ENNReal.ofReal ‖fordResidueWeylSum k Q q p c α‖
  have hA : AEMeasurable A (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_fordPolynomialWeylSum Ψ hdk).norm.pow 2)).aemeasurable
  have hB : AEMeasurable B (fordTorusMeasure k) := by
    exact (ENNReal.continuous_ofReal.comp
      (continuous_fordResidueWeylSum k Q q p c).norm).aemeasurable
  have hpow := ford_lintegral_weighted_interpolation_pow hA hB
    (n := 2 * s) (by omega)
  have hodd : (∫⁻ α, A α * B α ^ (2 * s - 1) ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordS4OddIntegral (P := P) Ψ hdk s Q q c) := by
    calc
      (∫⁻ α, A α * B α ^ (2 * s - 1) ∂fordTorusMeasure k) =
          ∫⁻ α, ENNReal.ofReal
            (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1))
            ∂fordTorusMeasure k := by
        apply lintegral_congr
        intro α
        simp [A, B, ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (∫ α,
            ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s - 1)
            ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordS4Odd_integrand Ψ hdk s Q q c)
          (Filter.Eventually.of_forall fun _ ↦
            mul_nonneg (sq_nonneg _) (by positivity))).symm
      _ = _ := rfl
  have heven : (∫⁻ α, A α * B α ^ (2 * s) ∂fordTorusMeasure k) =
      ENNReal.ofReal (fordS4Count (P := P) Ψ hdk s Q q c : ℝ) := by
    calc
      (∫⁻ α, A α * B α ^ (2 * s) ∂fordTorusMeasure k) =
          ∫⁻ α, ENNReal.ofReal
            (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s))
            ∂fordTorusMeasure k := by
        apply lintegral_congr
        intro α
        simp [A, B, ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (fordS4Fourier (P := P) Ψ hdk s Q q c) :=
        (ofReal_integral_eq_lintegral_ofReal
          (integrable_fordS4_integrand Ψ hdk s Q q c)
          (Filter.Eventually.of_forall fun _ ↦
            mul_nonneg (sq_nonneg _) (by positivity))).symm
      _ = _ := by rw [fordS4Fourier_eq_count]
  have hzero : (∫⁻ α, A α ∂fordTorusMeasure k) =
      ENNReal.ofReal
        (fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk : ℝ) := by
    have hzeroInt : Integrable (fun α : UnitAddTorus (Fin k) ↦
        ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2)
        (fordTorusMeasure k) := by
      rw [← integrableOn_univ]
      apply ContinuousOn.integrableOn_compact isCompact_univ
      exact ((continuous_fordPolynomialWeylSum Ψ hdk).norm.pow 2).continuousOn
    calc
      (∫⁻ α, A α ∂fordTorusMeasure k) =
          ∫⁻ α, ENNReal.ofReal
            (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2)
            ∂fordTorusMeasure k := by rfl
      _ = ENNReal.ofReal (∫ α,
            ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2
            ∂fordTorusMeasure k) :=
        (ofReal_integral_eq_lintegral_ofReal hzeroInt
          (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).symm
      _ = _ := by rw [fordPolynomialFourier_eq_collisionCount]
  rw [hodd, heven, hzero] at hpow
  have hoddnonneg := fordS4OddIntegral_nonneg (P := P) (p := p)
    Ψ hdk s Q q c
  have hconverted : ENNReal.ofReal
      (fordS4OddIntegral (P := P) Ψ hdk s Q q c ^ (2 * s)) ≤
      ENNReal.ofReal
        ((fordS4Count (P := P) Ψ hdk s Q q c : ℝ) ^ (2 * s - 1) *
          (fordPolynomialCollisionCount (P := P) (p := p) Ψ hdk : ℝ)) := by
    rw [ENNReal.ofReal_pow hoddnonneg]
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity)]
    simpa using hpow
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (by positivity))).mp hconverted

#print axioms ford_odd_integral_pow_le

end

end GafniTao
