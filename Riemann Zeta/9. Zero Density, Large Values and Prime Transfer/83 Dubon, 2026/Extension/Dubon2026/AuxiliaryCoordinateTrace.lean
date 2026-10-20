import Dubon2026.SmallLevelAuxiliaryAction
import Mathlib.RepresentationTheory.Coinvariants

/-! # The unnormalized trace in auxiliary coordinates

CHT uses the sum of level-quotient translates, with no division by the level
index. This map identifies coinvariants even when the index is not a unit.
-/

namespace Dubon2026

noncomputable section

variable {R D J W : Type*} [CommRing R] [Group D] [Fintype D]
variable [AddCommGroup W] [Module R W]

open scoped BigOperators

/-- The source trace is the sum over all quotient coordinates. -/
def auxiliaryCoordinateTrace : (J → D → W) →ₗ[R] (J → W) where
  toFun f j := ∑ d : D, f j d
  map_add' f g := by ext j; exact Finset.sum_add_distrib
  map_smul' a f := by
    ext j
    change (∑ d : D, a • f j d) = a • ∑ d : D, f j d
    rw [Finset.smul_sum]

/-- A single quotient coordinate carries the full weight value. -/
def auxiliaryCoordinateSingle (d : D) : (J → W) →ₗ[R] (J → D → W) := by
  classical
  exact
    { toFun := fun w j x => if x = d then w j else 0
      map_add' := by intro f g; ext j x; split_ifs <;> simp_all
      map_smul' := by intro a f; ext j x; split_ifs <;> simp_all }

/-- The trace is invariant under the actual quotient-coordinate action. -/
theorem auxiliaryCoordinateTrace_invariant (d : D) (f : J → D → W) :
    auxiliaryCoordinateTrace (R := R) (quotientRightTranslation (R := R) d f) =
      auxiliaryCoordinateTrace (R := R) f := by
  funext j
  exact Equiv.sum_comp (Equiv.mulRight d) (f j)

omit [Group D] in
/-- The trace of one coordinate is its coefficient, without division by the group order. -/
theorem auxiliaryCoordinateTrace_single (d : D) (w : J → W) :
    auxiliaryCoordinateTrace (R := R) (auxiliaryCoordinateSingle (R := R) d w) = w := by
  classical
  funext j
  simp [auxiliaryCoordinateTrace, auxiliaryCoordinateSingle]

omit [Group D] in
/-- Every function is the finite sum of its quotient coordinates. -/
theorem auxiliaryCoordinateSingle_sum (f : J → D → W) :
    ∑ d : D, auxiliaryCoordinateSingle (R := R) d (fun j => f j d) = f := by
  classical
  ext j x
  simp [auxiliaryCoordinateSingle]

omit [Fintype D] in
/-- All quotient coordinates have the same class in the actual coinvariant quotient. -/
theorem auxiliaryCoordinateSingle_coinvariant (d : D) (w : J → W) :
    Representation.Coinvariants.mk (quotientRightTranslation (R := R) (D := D))
      (auxiliaryCoordinateSingle (R := R) d w) =
    Representation.Coinvariants.mk (quotientRightTranslation (R := R) (D := D))
      (auxiliaryCoordinateSingle (R := R) 1 w) := by
  classical
  have he : quotientRightTranslation (R := R) d⁻¹
      (auxiliaryCoordinateSingle (R := R) 1 w) = auxiliaryCoordinateSingle (R := R) d w := by
    ext j x
    simp [quotientRightTranslation, auxiliaryCoordinateSingle, mul_inv_eq_one]
  rw [← he]
  exact Representation.Coinvariants.mk_self_apply _ _ _

end
end Dubon2026
