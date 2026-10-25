import Dubon2026.SourceCharacterIdempotentLine

/-! DUB-17/18 -> primitive determinant -> the rank-two projector image.
Native range and product equivalences turn the actual character left ideal
into the two prescribed coefficient coordinates. -/
namespace Dubon2026
noncomputable section
variable {E A : Type*} [Field E] [Ring A] [Algebra E A]

/-- The image of coordinatewise multiplication by the character idempotent is rank two. -/
def characterIdempotentRankTwoEquiv (κ : A →ₐ[E] E) (e : A)
    (he : κ e = 1) (hκ : ∀ a : A, a * e = κ a • e) :
    ((LinearMap.mulRight E e).compLeft (Fin 2)).range ≃ₗ[E] (Fin 2 → E) := by
  let L := algebraIdempotentLeftIdeal (S := E) e
  let j := L.subtype.compLeft (Fin 2)
  have hj : Function.Injective j := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  have hr : j.range = ((LinearMap.mulRight E e).compLeft (Fin 2)).range := by
    rw [LinearMap.range_compLeft, LinearMap.range_compLeft, Submodule.range_subtype]
    rfl
  exact (LinearEquiv.ofEq _ _ hr.symm).trans
    ((LinearEquiv.ofInjective j hj).symm.trans
      (LinearEquiv.piCongrRight fun _ => characterIdempotentLeftIdealEquiv κ e he hκ))

theorem characterIdempotentRankTwoEquiv_symm_val (κ : A →ₐ[E] E) (e : A)
    (he : κ e = 1) (hκ : ∀ a : A, a * e = κ a • e) (v : Fin 2 → E) :
    ((characterIdempotentRankTwoEquiv κ e he hκ).symm v).val = fun i => v i • e := rfl

theorem characterIdempotentRankTwoEquiv_apply (κ : A →ₐ[E] E) (e : A)
    (he : κ e = 1) (hκ : ∀ a : A, a * e = κ a • e)
    (x : ((LinearMap.mulRight E e).compLeft (Fin 2)).range) (i : Fin 2) :
    characterIdempotentRankTwoEquiv κ e he hκ x i = κ (x.val i) := by
  have h := congrArg (fun z : ((LinearMap.mulRight E e).compLeft (Fin 2)).range => κ (z.val i))
    ((characterIdempotentRankTwoEquiv κ e he hκ).symm_apply_apply x)
  simpa only [characterIdempotentRankTwoEquiv_symm_val, map_smul, he, smul_eq_mul, mul_one] using h

end
end Dubon2026
