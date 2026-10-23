import Dubon2026.SourceEllipticOddAffineSpecialization
import Mathlib.RingTheory.Localization.Ideal

/-! The ideal of an actual affine point extends to exactly the kernel of
localized evaluation. Its pullback from the actual odd quotient is the ideal
of the literal quotient coordinates. This uses native localization ideal
correspondence, avoiding an additional point-place classification. It supplies
the prime ideals required for the relative norm comparison on DUB-17/18. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F]

/-- The kernel of actual coordinate evaluation is the actual affine point ideal. -/
theorem ker_evalAlgHom_eq_XYIdeal {W : WeierstrassCurve.Affine F} {x y : F}
    (h : W.Equation x y) :
    RingHom.ker (evalAlgHom (W := W) (A := F) h).toRingHom = CoordinateRing.XYIdeal W x (C y) := by
  ext z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change evalAlgHom (W := W) (A := F) h (CoordinateRing.mk W p) = 0 ↔ _
  rw [evalAlgHom_mk, Dubon2026.SourceEllipticClassGroup.mk_mem_XYIdeal_iff h]
  simp only [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

variable (W : WeierstrassCurve F) (S : Finset (F × F))
variable {x y : F} (h : W.toAffine.Equation x y) (hd : (hP S Prod.fst).eval x ≠ 0)

/-- The evaluation kernel contracts to the original point ideal. -/
theorem kernelLocalEval_ker_under :
    (RingHom.ker (kernelLocalEval W S h hd)).under W.toAffine.CoordinateRing =
      CoordinateRing.XYIdeal W.toAffine x (C y) := by
  ext z
  change kernelLocalEval W S h hd (algebraMap W.toAffine.CoordinateRing (kernelLocalRing W S) z) = 0 ↔ _
  rw [kernelLocalEval_algebraMap]
  change z ∈ RingHom.ker (evalAlgHom (W := W.toAffine) (A := F) h).toRingHom ↔ _
  rw [ker_evalAlgHom_eq_XYIdeal]

/-- The original point ideal extends to exactly the localized evaluation kernel. -/
theorem map_XYIdeal_eq_kernelLocalEval_ker :
    (CoordinateRing.XYIdeal W.toAffine x (C y)).map
      (algebraMap W.toAffine.CoordinateRing (kernelLocalRing W S)) =
      RingHom.ker (kernelLocalEval W S h hd) := by
  letI := isLocalization_kernelLocalRing W S
  rw [← kernelLocalEval_ker_under W S h hd]
  exact IsLocalization.map_under (Submonoid.powers (kernelCoordinate W S)) _ _

/-- The actual localized evaluation ideal is maximal, with residue field the coefficient field. -/
theorem isMaximal_kernelLocalEval_ker : (RingHom.ker (kernelLocalEval W S h hd)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (kernelLocalEval_surjective W S h hd)

variable [DecidableEq F] [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual quotient pullback contracts the source point ideal to the ideal of the literal quotient coordinates. -/
theorem comap_kernelLocalEval_ker_oddKernelPullback (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    (RingHom.ker (kernelLocalEval W (oddOrderSummingSet W Q n) h hd)).comap
      (oddKernelPullback W hQ).toRingHom =
      CoordinateRing.XYIdeal (veluQuotient W (oddOrderSummingSet W Q n)).toAffine
        (veluAffineX W (oddOrderSummingSet W Q n) x)
        (C (veluAffineY W (oddOrderSummingSet W Q n) x y)) := by
  change RingHom.ker (oddAffineEval W h hQ hd).toRingHom = _
  rw [oddAffineEval_eq_evalAlgHom, ker_evalAlgHom_eq_XYIdeal]

end Dubon2026.SourceEllipticFunctionField
