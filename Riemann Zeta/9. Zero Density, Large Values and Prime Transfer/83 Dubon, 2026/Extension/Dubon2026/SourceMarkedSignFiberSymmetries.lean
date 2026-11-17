import Dubon2026.SourceMarkedSignFiberFactor

/-! DUB-17/18 -> reverse original genus -> wild finite fibers.
Retain every actual point automorphism after factoring a marked-point
fiber chart through sign classes. The characteristic-three conjugation
identity also descends by taking images of those same sign classes. -/
namespace Dubon2026.SourceFunctionField.MarkedTorsion
noncomputable section
variable {A Y : Type*} [AddCommGroup A] (N : ℕ)

theorem signClass_fiber_factor_invariant
    (f : {P : A // addOrderOf P = N} → Y) (F : SignClasses A N → Y)
    (hF : ∀ P, F ⟨{P.val, -P.val}, P.val, P.property, rfl⟩ = f P)
    (e : A ≃+ A) (he : ∀ P Q, Q.val = e P.val → f Q = f P)
    (s : SignClasses A N) : F (signClassesEquiv N e s) = F s := by
  obtain ⟨P, hP, hs⟩ := s.property
  let p : {P : A // addOrderOf P = N} := ⟨P, hP⟩
  let q : {P : A // addOrderOf P = N} :=
    ⟨e P, (addOrderOf_injective e.toAddMonoidHom e.injective P).trans hP⟩
  have hp : s = ⟨{p.val, -p.val}, p.val, p.property, rfl⟩ := Subtype.ext hs
  have hq : signClassesEquiv N e s = ⟨{q.val, -q.val}, q.val, q.property, rfl⟩ := by
    apply Subtype.ext
    change e '' s.val = _
    rw [hs, Set.image_pair, map_neg]
  rw [hq, hp, hF, hF]
  exact he p q rfl

theorem signClassesEquiv_conjugation (a b : A ≃+ A)
    (hab : ∀ P, a (b P) = b (b (a P))) (s : SignClasses A N) :
    signClassesEquiv N a (signClassesEquiv N b s) =
      signClassesEquiv N b (signClassesEquiv N b (signClassesEquiv N a s)) := by
  apply Subtype.ext
  change a '' (b '' s.val) = b '' (b '' (a '' s.val))
  simp only [Set.image_image]
  congr 1
  funext P
  exact hab P

end
end Dubon2026.SourceFunctionField.MarkedTorsion
