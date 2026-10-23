import Dubon2026.SourceEllipticKernelPointIdeal

/-! Actual affine evaluation on the common integral closure used by the odd
point norm. The proved concrete localization identifies this ring and fixes
both its original-source and quotient-target actions. These identities let
the relative ideal norm consume the actual point ideals (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual common ring and concrete kernel localization have identical elements in the source field. -/
noncomputable def oddIntermediateLocalizationEquiv (hQ : addOrderOf Q = 2 * n + 1) :
    oddIntermediateRing W hQ ≃+* kernelLocalRing W (oddOrderSummingSet W Q n) where
  toFun z := ⟨z.val, by
    change z.val ∈ (kernelLocalRing W (oddOrderSummingSet W Q n)).toSubring
    rw [← oddIntermediateRing_eq_kernelLocalRing W hQ]
    exact z.property⟩
  invFun z := ⟨z.val, by
    rw [oddIntermediateRing_eq_kernelLocalRing W hQ]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The concrete identification preserves the actual source coordinate embedding. -/
theorem oddIntermediateLocalizationEquiv_source (hQ : addOrderOf Q = 2 * n + 1)
    (z : W.toAffine.CoordinateRing) :
    oddIntermediateLocalizationEquiv W hQ (oddSourceToIntermediate W hQ z) =
      algebraMap W.toAffine.CoordinateRing (kernelLocalRing W (oddOrderSummingSet W Q n)) z := rfl

/-- The concrete identification preserves the actual quotient coordinate pullback. -/
theorem oddIntermediateLocalizationEquiv_target (hQ : addOrderOf Q = 2 * n + 1)
    (z : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing) :
    oddIntermediateLocalizationEquiv W hQ (oddTargetToIntermediate W hQ z) =
      oddKernelPullback W hQ z := rfl

/-- The source action on the actual common ring is its proved original coordinate embedding. -/
noncomputable abbrev oddIntermediateSourceAlgebra (hQ : addOrderOf Q = 2 * n + 1) :
    Algebra W.toAffine.CoordinateRing (oddIntermediateRing W hQ) :=
  (oddSourceToIntermediate W hQ).toAlgebra

/-- The common ring is a localization for its actual source action. -/
theorem isLocalization_oddIntermediateRing (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddIntermediateSourceAlgebra W hQ
    IsLocalization (Submonoid.powers (kernelCoordinate W (oddOrderSummingSet W Q n)))
      (oddIntermediateRing W hQ) := by
  letI := oddIntermediateSourceAlgebra W hQ
  let e : oddIntermediateRing W hQ ≃ₐ[W.toAffine.CoordinateRing]
      kernelLocalRing W (oddOrderSummingSet W Q n) :=
    { oddIntermediateLocalizationEquiv W hQ with
      commutes' := oddIntermediateLocalizationEquiv_source W hQ }
  exact (IsLocalization.isLocalization_iff_of_algEquiv _ e).mpr (isLocalization_kernelLocalRing W _)

variable {x y : F} (h : W.toAffine.Equation x y)

/-- Actual evaluation on the integral closure used in the point norm. -/
noncomputable def oddIntermediateEval (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) : oddIntermediateRing W hQ →+* F :=
  (kernelLocalEval W _ h hd).comp (oddIntermediateLocalizationEquiv W hQ).toRingHom

/-- Evaluation on the common ring agrees with original coordinate evaluation. -/
theorem oddIntermediateEval_source (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) (z : W.toAffine.CoordinateRing) :
    oddIntermediateEval W h hQ hd (oddSourceToIntermediate W hQ z) =
      evalAlgHom (W := W.toAffine) (A := F) h z := by
  change kernelLocalEval W _ h hd (oddIntermediateLocalizationEquiv W hQ _) = _
  rw [oddIntermediateLocalizationEquiv_source, kernelLocalEval_algebraMap]

/-- Evaluation on the common ring agrees with the literal quotient-coordinate evaluation. -/
theorem oddIntermediateEval_target (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0)
    (z : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.CoordinateRing) :
    oddIntermediateEval W h hQ hd (oddTargetToIntermediate W hQ z) = oddAffineEval W h hQ hd z := by
  change kernelLocalEval W _ h hd (oddIntermediateLocalizationEquiv W hQ _) = _
  rw [oddIntermediateLocalizationEquiv_target]
  rfl

/-- Actual evaluation on the common ring is onto the coefficient field. -/
theorem oddIntermediateEval_surjective (hQ : addOrderOf Q = 2 * n + 1)
    (hd : (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0) :
    Function.Surjective (oddIntermediateEval W h hQ hd) :=
  (kernelLocalEval_surjective W _ h hd).comp (oddIntermediateLocalizationEquiv W hQ).surjective

end Dubon2026.SourceEllipticFunctionField
