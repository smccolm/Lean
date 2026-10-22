import Dubon2026.SourceOriginalIntegralPeriodsPrincipal
import Dubon2026.SourceOriginalRegularDifferentialSubtraction

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> all-loop
period correction. The source loop-generation formula modulo residues extends
integer periods on the chosen loops to every loop avoiding the divisor.
The residue coefficients and the correction coefficients remain integers.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_integral_periods_of_generators {ι : Type*} [Fintype ι]
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ])
    (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) = (D v : ℂ))
    (Pz : ι → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (m : ι → ℤ) (hm : ∀ k, pathIntegral N θ (Z k) = 2 * Real.pi * Complex.I * (m k : ℂ))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ (κ : ι → ℤ) (w : Place ℂ F → ℤ), ∀ η : Ω[F⁄ℂ],
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) →
        (∀ v : Place ℂ F, D v = 0 → 0 ≤ v.ordDifferential η) →
        pathIntegral N η γ = ∑ k, (κ k : ℂ) * pathIntegral N η (Z k) +
          2 * Real.pi * Complex.I * ∑ v ∈ D.support,
            (w v : ℂ) * originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η)) :
    ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ a : ℤ, pathIntegral N θ γ = 2 * Real.pi * Complex.I * a := by
  classical
  intro P γ hγ
  obtain ⟨κ, w, h⟩ := hgen P γ hγ
  have hreg : ∀ v : Place ℂ F, D v = 0 → 0 ≤ v.ordDifferential θ := by
    intro v hv
    exact v.ord_nonneg_of_mem (original_coeff_regular_off_divisor N D θ hθ hres v hv)
  rw [h θ hθ hreg]
  refine ⟨(∑ k, κ k * m k) + ∑ v ∈ D.support, w v * D v, ?_⟩
  simp only [hm, hres, Int.cast_add, Int.cast_sum, Int.cast_mul, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

end
end Dubon2026.SourceFunctionField.OriginalChart
