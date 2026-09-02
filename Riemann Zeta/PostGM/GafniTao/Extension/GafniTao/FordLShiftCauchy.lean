import GafniTao.FordLShiftRaisedWeyl
import GafniTao.FordKPowerMoment
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Ford Lemma 3.3: Cauchy--Schwarz for the selected shift

The selected shifted integral is written as the product of the square roots
of the raised-system `K_s` integral and the ordinary Vinogradov moment.  The
proof uses the exact norm bridge, not a pointwise replacement of a truncated
sum by a complete sum.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

theorem integral_mul_le_sqrt_mul_sqrt_of_continuous_nonneg
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [T2Space X] [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x, f x * g x ∂μ) ≤
      √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    rw [← integrableOn_univ]
    exact (hf.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have hg2 : Integrable (fun x => g x ^ 2) μ := by
    rw [← integrableOn_univ]
    exact (hg.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have hfmem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2
  have hgmem : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2
  have hfmem' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hfmem
  have hgmem' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hgmem
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    hfmem' hgmem'
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

theorem fordLPositiveShiftIntegral_le_fourier_sqrt
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (p q s Q : ℕ) (h : FordPositiveShift P m) :
    fordLPositiveShiftIntegral Ψ m p q s Q h ≤
      √(fordKFourier
        (fordIntegerDifferenceSystem Ψ hT (h.1 * m)
          (Nat.mul_pos (by
            have hh := h.property
            rw [Finset.mem_Icc] at hh
            omega) hm)) s P Q (p * q)) *
      √(fordPowerMomentIntegral k s Q (p * q)) := by
  let Υ := fordIntegerDifferenceSystem Ψ hT (h.1 * m)
    (Nat.mul_pos (by
      have hh := h.property
      rw [Finset.mem_Icc] at hh
      omega) hm)
  let A : UnitAddTorus (Fin k) → ℝ := fun α =>
    ‖fordPolynomialFullWeylSum (P := P) Υ α‖
  let B : UnitAddTorus (Fin k) → ℝ := fun α =>
    ‖fordPowerFullWeylSum k Q (p * q) α‖
  let f : UnitAddTorus (Fin k) → ℝ := fun α => A α ^ k * B α ^ s
  let g : UnitAddTorus (Fin k) → ℝ := fun α => B α ^ s
  have hcs := integral_mul_le_sqrt_mul_sqrt_of_continuous_nonneg
    (fordTorusMeasure k) f g
    (((continuous_fordPolynomialFullWeylSum Υ).norm.pow k).mul
      ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow s))
    ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow s)
    (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
    (fun _ => pow_nonneg (norm_nonneg _) _)
  have hleft : fordLPositiveShiftIntegral Ψ m p q s Q h =
      ∫ α : UnitAddTorus (Fin k), f α * g α ∂fordTorusMeasure k := by
    unfold fordLPositiveShiftIntegral
    apply integral_congr_ae
    filter_upwards [] with α
    rw [norm_fordLShiftedWeylSum_true_eq_raised Ψ hT m hm h]
    dsimp [f, g, A, B, Υ]
    rw [two_mul, pow_add]
    ring
  have hf2 : (∫ α : UnitAddTorus (Fin k), f α ^ 2 ∂fordTorusMeasure k) =
      fordKFourier Υ s P Q (p * q) := by
    unfold fordKFourier
    apply integral_congr_ae
    filter_upwards [] with α
    dsimp [f, A, B]
    ring_nf
  have hg2 : (∫ α : UnitAddTorus (Fin k), g α ^ 2 ∂fordTorusMeasure k) =
      fordPowerMomentIntegral k s Q (p * q) := by
    unfold fordPowerMomentIntegral
    apply integral_congr_ae
    filter_upwards [] with α
    dsimp [g, B]
    rw [← pow_mul]
    congr 1
    omega
  rw [hleft]
  calc
    (∫ α : UnitAddTorus (Fin k), f α * g α ∂fordTorusMeasure k) ≤
        √(∫ α : UnitAddTorus (Fin k), f α ^ 2 ∂fordTorusMeasure k) *
          √(∫ α : UnitAddTorus (Fin k), g α ^ 2 ∂fordTorusMeasure k) := hcs
    _ = _ := by rw [hf2, hg2]

theorem fordLPositiveShiftIntegral_le_count_sqrt
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    (p q s Q : ℕ) (hpq : 0 < p * q) (h : FordPositiveShift P m) :
    fordLPositiveShiftIntegral Ψ m p q s Q h ≤
      √(fordKCount
        (fordIntegerDifferenceSystem Ψ hT (h.1 * m)
          (Nat.mul_pos (by
            have hh := h.property
            rw [Finset.mem_Icc] at hh
            omega) hm)) s P Q (p * q) : ℝ) *
      √(fordVinogradovMomentNat s k Q : ℝ) := by
  simpa [fordKFourier_eq_count,
    fordPowerMomentIntegral_eq_vinogradov hpq] using
      fordLPositiveShiftIntegral_le_fourier_sqrt Ψ hT m hm p q s Q h

#print axioms integral_mul_le_sqrt_mul_sqrt_of_continuous_nonneg
#print axioms fordLPositiveShiftIntegral_le_count_sqrt

end

end GafniTao
