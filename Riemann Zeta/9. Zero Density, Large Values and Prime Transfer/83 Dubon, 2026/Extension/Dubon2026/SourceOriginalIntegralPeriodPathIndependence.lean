import Dubon2026.SourceOriginalRegularPathIntegralLaws
import Dubon2026.SourceOriginalSimplePoleRegularPart

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Integral loop periods make the exponential
of the actual differential integral independent of the path away from the
divisor support. Simple-pole residue data prove regularity along these paths;
only the still-unproved period correction is an upstream period hypothesis.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_coeff_regular_off_divisor (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (v : Place ℂ F) (hv : D v = 0) : v.differentialCoeff η ∈ v.toValuationSubring := by
  have hz : originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = 0 := by
    rw [hres, hv, Int.cast_zero]
  simpa only [map_zero, zero_mul, sub_zero] using
    original_simple_pole_regular_part N v η (hη v) 0 hz

theorem exp_pathIntegral_eq_of_integral_periods (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m)
    {P Q : Place ℂ F} (γ δ : Path P Q)
    (hγ : ∀ t, D (γ t) = 0) (hδ : ∀ t, D (δ t) = 0) :
    Complex.exp (pathIntegral N η γ) = Complex.exp (pathIntegral N η δ) := by
  have hγreg := fun t => original_coeff_regular_off_divisor N D η hη hres (γ t) (hγ t)
  have hδreg := fun t => original_coeff_regular_off_divisor N D η hη hres (δ t) (hδ t)
  have hδsymm : ∀ t, (δ.symm t).differentialCoeff η ∈ (δ.symm t).toValuationSubring :=
    fun t => hδreg (unitInterval.symm t)
  have hloop : ∀ t, D ((γ.trans δ.symm) t) = 0 := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hδ _
  obtain ⟨m, hm⟩ := hper P (γ.trans δ.symm) hloop
  rw [pathIntegral_trans_of_coeff_mem N γ δ.symm hγreg hδsymm,
    pathIntegral_symm_of_coeff_mem N δ hδreg] at hm
  have he : pathIntegral N η γ = pathIntegral N η δ + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    linear_combination hm
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end
end Dubon2026.SourceFunctionField.OriginalChart
