import Dubon2026.SourceEllipticOddQuotientField

/-! The finite Galois extension through the actual odd quotient pullback.
The proved image and fixed-field results are transported to the quotient's
own function field, so later norm constructions can use the actual curve
field rather than assuming a field-extension certificate (DUB-17/18). -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual function-field action through the proved odd quotient pullback. -/
noncomputable abbrev oddQuotientAlgebra (hQ : addOrderOf Q = 2 * n + 1) :
    Algebra (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField :=
  (oddQuotientPullback W hQ).toRingHom.toAlgebra

/-- The actual quotient pullback respects the original coefficient field. -/
theorem oddQuotient_scalarTower (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddQuotientAlgebra W hQ
    IsScalarTower F (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField := by
  letI := oddQuotientAlgebra W hQ
  exact IsScalarTower.of_algebraMap_eq fun a => ((oddQuotientPullback W hQ).commutes a).symm

/-- The actual curve-field extension has degree equal to the prescribed odd order. -/
theorem finrank_oddQuotient (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddQuotientAlgebra W hQ
    Module.finrank (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField = 2 * n + 1 := by
  letI := oddQuotientAlgebra W hQ
  have he := Algebra.finrank_eq_of_equiv_equiv
    (AlgEquiv.ofInjective (oddQuotientPullback W hQ) (oddQuotientPullback W hQ).injective).toRingEquiv
    (RingEquiv.refl W.toAffine.FunctionField) (by ext z; rfl)
  exact he.trans (finrank_oddQuotient_range W hQ)

/-- The actual quotient curve-field extension is finite dimensional. -/
theorem finiteDimensional_oddQuotient (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddQuotientAlgebra W hQ
    FiniteDimensional (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField := by
  letI := oddQuotientAlgebra W hQ
  exact .of_finrank_pos (by rw [finrank_oddQuotient W hQ]; omega)

/-- The actual quotient curve-field extension is Galois without excluding characteristics two or three. -/
theorem isGalois_oddQuotient (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddQuotientAlgebra W hQ
    IsGalois (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField := by
  letI := oddQuotientAlgebra W hQ
  letI := finiteDimensional_oddQuotient_range W hQ
  letI := isGalois_oddQuotient_range W hQ
  let e : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField ≃ₐ[F]
      (oddQuotientPullback W hQ).fieldRange :=
    AlgEquiv.ofInjective (oddQuotientPullback W hQ) (oddQuotientPullback W hQ).injective
  exact IsGalois.of_equiv_equiv
    (f := e.symm.toRingEquiv) (g := RingEquiv.refl W.toAffine.FunctionField) (by
      ext z
      change (oddQuotientPullback W hQ) (e.symm z) = z.val
      exact congrArg Subtype.val (e.apply_symm_apply z))

/-- The actual quotient curve-field extension is separable. -/
theorem isSeparable_oddQuotient (hQ : addOrderOf Q = 2 * n + 1) :
    letI := oddQuotientAlgebra W hQ
    Algebra.IsSeparable (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.FunctionField W.toAffine.FunctionField := by
  letI := oddQuotientAlgebra W hQ
  letI := isGalois_oddQuotient W hQ
  infer_instance

end Dubon2026.SourceEllipticFunctionField
