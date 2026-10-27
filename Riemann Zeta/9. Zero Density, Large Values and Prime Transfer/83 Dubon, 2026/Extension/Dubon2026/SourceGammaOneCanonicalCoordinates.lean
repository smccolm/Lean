import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceGammaOneCurveGeometry
import Dubon2026.SourceCurveExactDerivativeOrder
import Dubon2026.SourceCurveCoordinateValues
import Dubon2026.SourceCurveFiniteCoordinateRegularGenus

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> matching genus
lower bound. Reuse the finite-coordinate canonical-degree theorem and exact
local derivative orders for the actual j field. Finite points contribute
nonnegative differential orders, so an exact genus formula is unnecessary. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve KaehlerDifferential
open scoped MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

/-- The divisor of the actual nonzero j differential in the original subgroup field. -/
def jCanonicalDivisor : Divisor ℂ (functionFieldOver Γ ℂ) :=
  letI := functionFieldOver_hasCanonicalDivisor Γ ℂ hT
  canonicalDivisorOf (D_jCoordinateOver_ne_zero Γ ℂ)

theorem jCanonicalDivisor_apply (v : Place ℂ (functionFieldOver Γ ℂ)) :
    jCanonicalDivisor hT v =
      v.ordDifferential (D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ)) := by
  letI := functionFieldOver_hasCanonicalDivisor Γ ℂ hT
  exact canonicalDivisorOf_apply (D_jCoordinateOver_ne_zero Γ ℂ) v

theorem jCanonicalDivisor_degree :
    Divisor.degree (jCanonicalDivisor hT) =
      2 * (Module.finrank ℂ (regularDifferentials ℂ (functionFieldOver Γ ℂ)) : ℤ) - 2 := by
  letI := finiteDimensional_jCoordinateOver hT ℂ
  exact finite_coordinate_canonical_degree_eq_regular_dimension (jCoordinateOver Γ ℂ)
    (transcendental_jCoordinateOver Γ ℂ) (D_jCoordinateOver_ne_zero Γ ℂ)
    (D_jCoordinateOver_ne_zero Γ ℂ)

include hT in
theorem ordDifferential_D_eq_order_sub_one (v : Place ℂ (functionFieldOver Γ ℂ))
    {f : functionFieldOver Γ ℂ} (hf : v.ord f ≠ 0) :
    v.ordDifferential (D ℂ (functionFieldOver Γ ℂ) f) = v.ord f - 1 := by
  letI := functionFieldOver_dCoordGenerates Γ ℂ hT v
  letI := functionFieldOver_localDifferentials Γ ℂ hT v
  letI := finiteDimensional_jCoordinateOver hT ℂ
  letI := finite_coordinate_place_residue (jCoordinateOver Γ ℂ) v
  letI : Algebra.IsSeparable ℂ v.ResidueField := inferInstance
  letI : Nontrivial Ω[functionFieldOver Γ ℂ⁄ℂ] :=
    nontrivial_of_ne _ _ (D_jCoordinateOver_ne_zero Γ ℂ)
  exact v.ordDifferential_D_eq_ord_sub_one hf

theorem jCanonicalDivisor_at_pole (v : Place ℂ (functionFieldOver Γ ℂ))
    (hv : v.ord (jCoordinateOver Γ ℂ) < 0) :
    jCanonicalDivisor hT v = v.ord (jCoordinateOver Γ ℂ) - 1 := by
  rw [jCanonicalDivisor_apply]
  exact ordDifferential_D_eq_order_sub_one hT v hv.ne

theorem jCanonicalDivisor_at_value (v : Place ℂ (functionFieldOver Γ ℂ)) (c : ℂ)
    (hv : 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)) :
    jCanonicalDivisor hT v =
      v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) - 1 := by
  rw [jCanonicalDivisor_apply]
  have h := ordDifferential_D_eq_order_sub_one hT v hv.ne'
  rw [map_sub, Derivation.map_algebraMap, sub_zero] at h
  exact h

theorem jCanonicalDivisor_nonneg_of_j_nonneg (v : Place ℂ (functionFieldOver Γ ℂ))
    (hv : 0 ≤ v.ord (jCoordinateOver Γ ℂ)) : 0 ≤ jCanonicalDivisor hT v := by
  obtain ⟨c, hc, _⟩ := v.exists_unique_coordinate_value
    (place_residue_bijective hT v).surjective
    (transcendental_jCoordinateOver Γ ℂ) (v.mem_of_ord_nonneg hv)
  rw [jCanonicalDivisor_at_value hT v c hc]
  omega

end
end Dubon2026.SourceFunctionField.GammaOne
