import Dubon2026.DualMatrixStrictAlgebra
import Dubon2026.PolarizedCoefficientMap

/-! The actual fixed-similitude reduction kernel over dual numbers is the
full matrix algebra. This identifies the tangent coefficients of the source
polarized deformation problem required by DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Actual reduction of the polarized target from dual numbers. -/
def polarizedDualReduction : PolarizedGaloisGroup ι (DualNumber R) →* PolarizedGaloisGroup ι R :=
  polarizedCoefficientMap (TrivSqZeroExt.fstHom R R R).toRingHom

/-- The original coefficient inclusion gives a constant polarized lift. -/
def polarizedDualConstant : PolarizedGaloisGroup ι R →* PolarizedGaloisGroup ι (DualNumber R) :=
  polarizedCoefficientMap (TrivSqZeroExt.inlHom R R)

/-- Actual reduction recovers the entire original constant point. -/
theorem polarizedDualReduction_constant (g : PolarizedGaloisGroup ι R) :
    polarizedDualReduction (polarizedDualConstant g) = g := by
  change polarizedCoefficientMap
    ((TrivSqZeroExt.fstHom R R R).toRingHom.comp (TrivSqZeroExt.inlHom R R)) g = g
  have h : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (TrivSqZeroExt.inlHom R R) =
      RingHom.id R := by ext x; rfl
  rw [h, polarizedCoefficientMap_id]
  rfl

/-- The original matrix infinitesimal inside the source fixed-similitude kernel. -/
def polarizedStrictPoint (X : Matrix ι ι R) : PolarizedGaloisGroup ι (DualNumber R) :=
  polarizedLinearInclusion (dualMatrixStrictUnit X)

/-- Addition of actual infinitesimal matrices is multiplication in the source kernel. -/
theorem polarizedStrictPoint_add (X Y : Matrix ι ι R) :
    polarizedStrictPoint (X + Y) = polarizedStrictPoint X * polarizedStrictPoint Y := by
  simp only [polarizedStrictPoint, dualMatrixStrictUnit_add, map_mul]

/-- The zero infinitesimal is the identity source point. -/
theorem polarizedStrictPoint_zero : polarizedStrictPoint (0 : Matrix ι ι R) = 1 := by
  simp only [polarizedStrictPoint, dualMatrixStrictUnit_zero, map_one]

/-- Original full matrix coordinates are injective in the polarized kernel. -/
theorem polarizedStrictPoint_injective :
    Function.Injective (polarizedStrictPoint (ι := ι) (R := R)) :=
  polarizedLinearInclusion_injective.comp dualMatrixStrictUnit_injective

/-- The original strict point reduces to the identity source point. -/
theorem polarizedStrictPoint_reduction (X : Matrix ι ι R) :
    polarizedDualReduction (polarizedStrictPoint X) = 1 := by
  change polarizedLinearInclusion (dualMatrixReduction (dualMatrixStrictUnit X)) = 1
  rw [dualMatrixStrictUnit_reduction, map_one]

/-- The original strict point has exactly fixed similitude. -/
theorem polarizedStrictPoint_similitude (X : Matrix ι ι R) :
    polarizedSimilitude (polarizedStrictPoint X) = 1 :=
  polarizedSimilitude_identityComponent _

/-- Every actual point reducing to one with fixed similitude is an original full matrix infinitesimal. -/
theorem polarizedStrictPoint_of_kernel (g : PolarizedGaloisGroup ι (DualNumber R))
    (hr : polarizedDualReduction g = 1) (hν : polarizedSimilitude g = 1) :
    polarizedStrictPoint (dualMatrixInfinitesimal g.left.1) = g := by
  have hc : polarizedComponent g = 1 := by
    have h := congrArg polarizedComponent hr
    change polarizedComponent g = 1 at h
    exact h
  have hred : dualMatrixReduction g.left.1 = 1 :=
    congrArg (fun x : PolarizedGaloisGroup ι R => x.left.1) hr
  have hm : g.left.2 = 1 := by
    change g.left.2 * polarizedComponentSign (polarizedComponent g) = 1 at hν
    simpa only [hc, map_one, mul_one] using hν
  apply SemidirectProduct.ext
  · apply Prod.ext
    · exact dualMatrixStrictUnit_of_reduction g.left.1 hred
    · exact hm.symm
  · exact hc.symm

end
end Dubon2026
