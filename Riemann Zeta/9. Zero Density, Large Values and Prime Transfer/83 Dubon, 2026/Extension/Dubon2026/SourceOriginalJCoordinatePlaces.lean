import Dubon2026.SourceCurveCoordinateValues
import Dubon2026.SourceOriginalExactDerivativeOrder
import Dubon2026.SourceOriginalCanonicalDivisors

/-! DUB-17/18 -> numerical modular genus and analytic cusp-form realization.
Every actual original place is either a pole of j or lies over a unique
finite j value. On both branches the actual canonical j-divisor coefficient
is the exact coordinate order minus one. The remaining modular input is the
ramification and fiber count at 0, 1728 and infinity, not local differential
or residue-field hypotheses.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem original_j_place_dichotomy [IsAlgClosed L]
    (v : Place L (modularFunctionFieldOver N L)) :
    v.ord (jOver N L) < 0 ∨
      ∃! c : L, 0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c) := by
  rcases lt_or_ge (v.ord (jOver N L)) 0 with hp | hreg
  · exact Or.inl hp
  · exact Or.inr (v.exists_unique_coordinate_value
      (original_place_residue_algebraMap_bijective N L v).surjective
      (transcendental_jOver N L) (v.mem_of_ord_nonneg hreg))

theorem original_jCanonical_at_pole
    (v : Place L (modularFunctionFieldOver N L)) (hp : v.ord (jOver N L) < 0) :
    originalCanonicalDivisor N L (D_jOver_ne_zero N L) v = v.ord (jOver N L) - 1 := by
  rw [originalCanonicalDivisor_apply]
  exact original_ordDifferential_D_eq_ord_sub_one N L v hp.ne

theorem original_jCanonical_at_value
    (v : Place L (modularFunctionFieldOver N L)) (c : L)
    (hc : 0 < v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c)) :
    originalCanonicalDivisor N L (D_jOver_ne_zero N L) v =
      v.ord (jOver N L - algebraMap L (modularFunctionFieldOver N L) c) - 1 := by
  rw [originalCanonicalDivisor_apply]
  have h := original_ordDifferential_D_eq_ord_sub_one N L v hc.ne'
  rw [map_sub, Derivation.map_algebraMap, sub_zero] at h
  exact h

end
end Dubon2026.SourceFunctionField
