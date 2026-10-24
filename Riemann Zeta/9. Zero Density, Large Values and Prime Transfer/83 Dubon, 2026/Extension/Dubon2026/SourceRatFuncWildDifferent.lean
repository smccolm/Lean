import Dubon2026.SourceRatFuncPositiveLocalDifferentials
import Dubon2026.SourceCurveGaloisWildDifferent
import Dubon2026.SourceRatFuncSpecializationOrder
import Dubon2026.SourceCurveRegularComparison

/-! The full wild different bound on the actual finite Galois rational
extension, at every positive rational-coordinate place. All local
differential, fixed-field, inertia and character inputs are derived.
This is the exact auxiliary-field form needed for the DUB-17/18 strong
wild modular differential orders; transfer to the modular field remains. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField
variable {K M : Type*} [Field K] [IsAlgClosed K] [Field M]
variable [Algebra K M] [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
variable [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]

theorem rational_wild_different_bound (v : Place K M)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hv : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X))
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X)) :
    v.ord (algebraMap (RatFunc K) M RatFunc.X) - 1 + ((p : ℤ) ^ a - 1) ≤
      v.ordDifferential (D K M (algebraMap (RatFunc K) M RatFunc.X)) := by
  haveI := (finite_galois_coordinateField K (M := M)).1
  haveI := finite_positive_rational_place_differentials v hv
  haveI := positive_rational_place_dCoordGenerates v hv
  haveI : Nontrivial Ω[M⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_rationalExtension_differentials K M)
  have hres := place_residue_bijective_of_finite_coordinate
    (algebraMap (RatFunc K) M RatFunc.X) v
  haveI : Module.Finite K v.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap K v.ResidueField) hres.surjective
  haveI : Algebra.IsSeparable K v.ResidueField := inferInstance
  have ho := v.ord_algebraMap_restrict (F := RatFunc K) RatFunc.X
  have hpos : 0 < (v.restrict (RatFunc K)).ord RatFunc.X := by
    rw [ho] at hv
    exact (mul_pos_iff_of_pos_right (v.ord_restricted_uniformizer_pos (F := RatFunc K))).mp hv
  have hx : (v.restrict (RatFunc K)).ord RatFunc.X = 1 := by
    simpa only [map_zero, sub_zero] using
      rational_finite_value_order_eq_one (v.restrict (RatFunc K)) (0 : K)
        (by simpa only [map_zero, sub_zero] using hpos)
  exact v.wild_different_bound_of_galois_parameter p RatFunc.X hx
    (RegularDifferentialsComparison.differentialCoeff_ne_zero
      (D_rationalCoordinate_ne_zero K M) v) a ha

end
end Dubon2026.SourceCurve.Place
