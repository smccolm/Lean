import Dubon2026.SourceIntertwinedRangeEquiv
import Dubon2026.SourceCharacterIdempotentRankTwo

/-! DUB-17/18 -> primitive determinant -> prescribed primitive Tate image.
Combine the actual operator-coordinate identity with its normalized
character to identify the literal image with the two coefficient coordinates. -/
namespace Dubon2026
noncomputable section
variable {E A V : Type*} [Field E] [CommRing A] [Algebra E A]
variable [AddCommGroup V] [Module E V]

/-- The prescribed character coordinates on the actual projector image. -/
def rankTwoCharacterRangeEquiv (e : V ≃ₗ[E] (Fin 2 → A))
    (Q : Module.End E V) (a : A) (κ : A →ₐ[E] E)
    (hc : κ a = 1) (hs : ∀ z : A, z * a = κ z • a)
    (he : ∀ (v : V) (i : Fin 2), e (Q v) i = a * e v i) :
    Q.range ≃ₗ[E] (Fin 2 → E) :=
  (intertwinedRangeEquiv e Q ((LinearMap.mulRight E a).compLeft (Fin 2))
    (fun v => funext fun i => (he v i).trans (mul_comm a (e v i)))).trans
      (characterIdempotentRankTwoEquiv κ a hc hs)

theorem rankTwoCharacterRangeEquiv_apply (e : V ≃ₗ[E] (Fin 2 → A))
    (Q : Module.End E V) (a : A) (κ : A →ₐ[E] E)
    (hc : κ a = 1) (hs : ∀ z : A, z * a = κ z • a)
    (he : ∀ (v : V) (i : Fin 2), e (Q v) i = a * e v i)
    (x : Q.range) (i : Fin 2) :
    rankTwoCharacterRangeEquiv e Q a κ hc hs he x i = κ (e x.val i) := by
  simp only [rankTwoCharacterRangeEquiv, LinearEquiv.trans_apply,
    characterIdempotentRankTwoEquiv_apply, intertwinedRangeEquiv_apply]

end
end Dubon2026
