import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Algebra.Tower

/-! # Restriction through an actual embedding of an original normal field

The target is the original field's automorphism group. The embedding supplies
the genuine scalar tower, and pinned normal restriction constructs the map.
-/

namespace Dubon2026
noncomputable section

variable {k E F K : Type*} [Field k] [Field E] [Field F] [Field K]
  [Algebra k E] [Normal k E] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K]

/-- Restrict the original automorphisms fixing the larger base field to the
specified embedded original normal field. No target restriction homomorphism
is assumed; normality proves its existence. -/
def embeddedNormalGaloisRestriction (e : E →ₐ[k] K) :
    (K ≃ₐ[F] K) →* (E ≃ₐ[k] E) := by
  letI : Algebra E K := e.toRingHom.toAlgebra
  letI : IsScalarTower k E K := IsScalarTower.of_algHom e
  exact (AlgEquiv.restrictNormalHom E).comp {
    toFun := fun g => g.restrictScalars k
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

/-- The actual restricted automorphism is characterized on every original
field element by the same embedding and original automorphism. -/
theorem embeddedNormalGaloisRestriction_commutes (e : E →ₐ[k] K)
    (g : K ≃ₐ[F] K) (x : E) :
    e (embeddedNormalGaloisRestriction e g x) = g (e x) := by
  letI : Algebra E K := e.toRingHom.toAlgebra
  letI : IsScalarTower k E K := IsScalarTower.of_algHom e
  exact (g.restrictScalars k).restrictNormal_commutes E x

/-- The original embedding commutation law uniquely determines the constructed
restriction on the actual target automorphism group. -/
theorem embeddedNormalGaloisRestriction_unique (e : E →ₐ[k] K)
    (f : (K ≃ₐ[F] K) →* (E ≃ₐ[k] E))
    (hf : ∀ (g : K ≃ₐ[F] K) (x : E), e (f g x) = g (e x)) :
    f = embeddedNormalGaloisRestriction e := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply e.injective
  exact (hf g x).trans (embeddedNormalGaloisRestriction_commutes e g x).symm

end
end Dubon2026
