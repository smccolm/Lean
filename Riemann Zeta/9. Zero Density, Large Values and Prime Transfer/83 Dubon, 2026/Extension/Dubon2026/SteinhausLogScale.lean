import Dubon2026.SteinhausLogNormalized

/-! # Exact return from normalized Haar sums to the source quadratic scale -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem steinhausSum_scale_normalized {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (z : ι → UnitAddCircle) :
    steinhausSum b z = (steinhausScale b : ℂ) * steinhausSum (normalizedSteinhausCoefficients b) z := by
  have hS : (steinhausScale b : ℂ) ≠ 0 := by exact_mod_cast (steinhausScale_pos b hb).ne'
  unfold steinhausSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold normalizedSteinhausCoefficients
  push_cast
  field_simp

theorem translated_steinhaus_scale {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (a : ℂ) (z : ι → UnitAddCircle) :
    a + steinhausSum b z = (steinhausScale b : ℂ) *
      (a / (steinhausScale b : ℂ) + steinhausSum (normalizedSteinhausCoefficients b) z) := by
  have hS : (steinhausScale b : ℂ) ≠ 0 := by exact_mod_cast (steinhausScale_pos b hb).ne'
  rw [steinhausSum_scale_normalized b hb z]
  field_simp

/-- The full source logarithmic estimate for actual independent Haar coordinates. -/
theorem exists_uniform_steinhaus_log {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K → ∀ a : ℂ,
      Integrable (fun z => Real.log ‖a + steinhausSum b z‖) (steinhausHaar κ) ∧
      Real.log (steinhausScale b) - C ≤ ∫ z, Real.log ‖a + steinhausSum b z‖ ∂steinhausHaar κ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalized_steinhaus_log hK
  refine ⟨C, hC, ?_⟩
  intro κ _ _ b hb hm hcomp a
  obtain ⟨hi, hlow, hne⟩ := hbound κ b hb hm hcomp (a / (steinhausScale b : ℂ))
  have hS := steinhausScale_pos b hb
  have he : (fun z => Real.log ‖a + steinhausSum b z‖) =ᵐ[steinhausHaar κ]
      fun z => Real.log (steinhausScale b) +
        Real.log ‖a / (steinhausScale b : ℂ) + steinhausSum (normalizedSteinhausCoefficients b) z‖ := by
    filter_upwards [hne] with z hz
    rw [translated_steinhaus_scale b hb a z, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS,
      Real.log_mul hS.ne' (norm_ne_zero_iff.mpr hz)]
  refine ⟨((integrable_const _).add hi).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_add (integrable_const _) hi, integral_const,
    probReal_univ, one_smul]
  linarith

end

end Dubon2026
