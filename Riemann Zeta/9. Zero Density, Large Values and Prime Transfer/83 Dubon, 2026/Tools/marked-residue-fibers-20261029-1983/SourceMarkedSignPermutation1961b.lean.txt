import Dubon2026.SourceMarkedTorsionSignClasses
import Dubon2026.SourceManinOrbitCount

/-! DUB-17/18 -> reverse original genus -> finite elliptic fibers.
The actual exceptional point automorphisms act on primitive points modulo
sign. Their quadratic identities imply periods two and three on this
specific quotient, so the existing finite orbit counts apply directly.
No adapted torsion basis is needed for this step. -/
namespace Dubon2026.SourceFunctionField.MarkedTorsion
noncomputable section
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Transport the actual exact-order sign classes by a point-group equivalence. -/
def signClassesEquiv (N : ℕ) (e : A ≃+ B) : SignClasses A N ≃ SignClasses B N where
  toFun := mapSignClasses e.toAddMonoidHom e.injective
  invFun := mapSignClasses e.symm.toAddMonoidHom e.symm.injective
  left_inv s := by
    apply Subtype.ext
    change e.symm '' (e '' s.val) = s.val
    rw [Set.image_image]
    simp only [e.symm_apply_apply, Set.image_id']
  right_inv s := by
    apply Subtype.ext
    change e '' (e.symm '' s.val) = s.val
    rw [Set.image_image]
    simp only [e.apply_symm_apply, Set.image_id']

theorem signClassesEquiv_pair (N : ℕ) (e : A ≃+ B) (P : A) (hP : addOrderOf P = N) :
    (signClassesEquiv N e ⟨{P, -P}, P, hP, rfl⟩).val = {e P, -(e P)} := by
  change e '' ({P, -P} : Set A) = _
  rw [Set.image_pair, map_neg]

theorem signClassesEquiv_square (N : ℕ) (e : A ≃+ A)
    (he : ∀ P, e (e P) = -P) : signClassesEquiv N e ^ 2 = 1 := by
  ext s : 1
  apply Subtype.ext
  obtain ⟨P, hP, hs⟩ := s.property
  change e '' (e '' s.val) = s.val
  rw [hs, Set.image_pair, Set.image_pair, map_neg, map_neg, he, neg_neg, Set.pair_comm]

theorem signClassesEquiv_cube (N : ℕ) (e : A ≃+ A)
    (he : ∀ P, e (e P) + e P + P = 0) : signClassesEquiv N e ^ 3 = 1 := by
  have hp (P : A) : e (e (e P)) = P := by
    have h := he (e P)
    rw [add_assoc, eq_neg_of_add_eq_zero_left (he P)] at h
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
  ext s : 1
  apply Subtype.ext
  obtain ⟨P, hP, hs⟩ := s.property
  change e '' (e '' (e '' s.val)) = s.val
  rw [hs, Set.image_pair, Set.image_pair, Set.image_pair, map_neg, map_neg, map_neg, hp]

end
end Dubon2026.SourceFunctionField.MarkedTorsion
