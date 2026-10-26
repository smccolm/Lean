import Dubon2026.SourceAbsoluteArithmeticRestriction

/-! DUB-17/18 -> arithmetic residual association -> fixed local maps.
Extend the already chosen arithmetic local embedding to the actual
global algebraic closure. This links the uniform absolute local theorem
to the prescribed arithmetic restriction, without replacing either map. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

theorem sourceArithmeticLocalEmbedding_exists_extension
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    ∃ e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure p hp,
      ∀ x : U, e (x : Qbar) =
        rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a x := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  let j : U →ₐ[ℚ] rationalPrimeLocalClosure p hp := rationalArithmeticLocalEmbedding a
  letI : Algebra U (rationalPrimeLocalClosure p hp) := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ U (rationalPrimeLocalClosure p hp) := IsScalarTower.of_algHom j
  let e : Qbar →ₐ[U] rationalPrimeLocalClosure p hp := IsAlgClosed.lift
  exact ⟨e.restrictScalars ℚ, fun x => e.commutes x⟩

private theorem arithmeticLocalEmbedding_algebra_independent
    {L : Type} [Field L] [IsAlgClosed L] (a : 𝓞 ℚ)
    (α β : Algebra ℚ L) (x : rationalUnramifiedExtension a) :
    (@rationalArithmeticLocalEmbedding L _ α _ a) x =
      (@rationalArithmeticLocalEmbedding L _ β _ a) x := by
  cases Subsingleton.elim α β
  rfl

theorem sourceAbsoluteArithmeticRestriction_local
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure p hp)
    (he : let U := rationalUnramifiedExtension a
      letI : Algebra ℚ U := U.algebra'
      ∀ x : U, e (x : Qbar) =
        rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a x)
    (g : Gal(rationalPrimeLocalClosure p hp/rationalPrimeLocalField p hp)) :
    sourceAbsoluteArithmeticRestriction a (embeddedNormalGaloisRestriction e g) =
      rationalPrimeArithmeticRestriction a p hp g := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  change (show Gal(U/ℚ) from sourceAbsoluteArithmeticRestriction a
    (embeddedNormalGaloisRestriction e g)) =
      (show Gal(U/ℚ) from rationalPrimeArithmeticRestriction a p hp g)
  apply AlgEquiv.ext
  intro x
  have hj (y : U) :
      rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a y =
        (@rationalArithmeticLocalEmbedding (rationalPrimeLocalClosure p hp) _
          (@AlgebraicClosure.instAlgebra (rationalPrimeLocalField p hp) _ ℚ _
            (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ
              (rationalPrimePlace p hp))) _ a) y :=
    arithmeticLocalEmbedding_algebra_independent a _ _ y
  apply (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).injective
  exact (he _).symm.trans
    ((congrArg e (sourceAbsoluteArithmeticRestriction_commutes a
      (embeddedNormalGaloisRestriction e g) x)).trans
      ((embeddedNormalGaloisRestriction_commutes e g (x : Qbar)).trans
        ((congrArg g (he x)).trans
          ((congrArg g (hj x)).trans
            ((rationalPrimeArithmeticRestriction_commutes a p hp g x).symm.trans (hj _).symm)))))

end
end Dubon2026
