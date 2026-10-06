import Dubon2026.SteinhausRadialIntegral
import Dubon2026.PolarRadialIntegral

/-! # One planar characteristic-function L1 constant for every admissible dimension -/

namespace Dubon2026

open MeasureTheory Set
open scoped BigOperators

theorem continuous_charFun_steinhausLaw {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) : Continuous (charFun (steinhausLaw c)) := by
  have he : charFun (steinhausLaw c) = fun ξ : ℂ => ∏ i, (besselJ0 (c i * ‖ξ‖) : ℂ) :=
    funext (charFun_steinhausLaw c hc)
  rw [he]
  apply continuous_finsetProd
  intro i _
  exact Complex.continuous_ofReal.comp
    (continuous_besselJ0.comp (continuous_const.mul continuous_norm))

theorem steinhaus_planar_L1_of_radial {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hi : IntegrableOn (fun r : ℝ => r * steinhausRadialProfile c r) (Ioi 0)) :
    Integrable (charFun (steinhausLaw c)) ∧
    (∫ ξ : ℂ, ‖charFun (steinhausLaw c) ξ‖) =
      (2 * Real.pi) * ∫ r : ℝ in Ioi 0, r * steinhausRadialProfile c r := by
  have hrad := integrable_complex_radial (continuous_steinhausRadialProfile c)
    (fun r _ => steinhausRadialProfile_nonneg c r) hi
  have hnorm : Integrable (fun ξ : ℂ => ‖charFun (steinhausLaw c) ξ‖) := by
    simpa only [norm_charFun_eq_radialProfile c hc] using hrad
  refine ⟨(integrable_norm_iff (continuous_charFun_steinhausLaw c hc).aestronglyMeasurable).1 hnorm, ?_⟩
  simp_rw [norm_charFun_eq_radialProfile c hc]
  exact integral_complex_radial (continuous_steinhausRadialProfile c)
    (fun r _ => steinhausRadialProfile_nonneg c r)

theorem exists_uniform_steinhaus_charFun_L1 {K : ℝ} (hK : 1 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K →
      Integrable (charFun (steinhausLaw (normalizedSteinhausCoefficients b))) ∧
      (∫ ξ : ℂ, ‖charFun (steinhausLaw (normalizedSteinhausCoefficients b)) ξ‖) ≤ L := by
  obtain ⟨L, hL, hbnd⟩ := exists_uniform_steinhaus_radial_bound hK
  refine ⟨(2 * Real.pi) * L, by positivity, ?_⟩
  intro κ _ _ b hb hm hcomp
  obtain ⟨hi, hbound⟩ := hbnd κ b hb hm hcomp
  obtain ⟨hchar, he⟩ := steinhaus_planar_L1_of_radial (normalizedSteinhausCoefficients b)
    (fun i => (normalizedSteinhausCoefficients_pos b hb i).le) hi
  refine ⟨hchar, ?_⟩
  rw [he]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Dubon2026
