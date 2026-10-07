import Dubon2026.FiniteRepresentationInnerProduct
import Dubon2026.FiniteSymmetricKernels
import Mathlib.RepresentationTheory.Invariants

/-! # Orthogonal finite-group averages for the genuine congruence representation -/

namespace Dubon2026

noncomputable section

section Algebra
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- Mathlib's finite-group invariant projection, with invertibility supplied over the complex field. -/
def finiteGroupProjection (ρ : Representation ℂ G V) : V →ₗ[ℂ] V :=
  letI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  ρ.averageMap

/-- The invariant projection is the literal normalized finite operator average. -/
theorem finiteGroupProjection_eq (ρ : Representation ℂ G V) :
    finiteGroupProjection ρ = (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g := by
  simp [finiteGroupProjection, Representation.averageMap, GroupAlgebra.average]

/-- Averaging produces vectors fixed by every group element. -/
theorem finiteGroupProjection_invariant (ρ : Representation ℂ G V) (x : V) (g : G) :
    ρ g (finiteGroupProjection ρ x) = finiteGroupProjection ρ x := by
  letI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact ρ.averageMap_invariant x g

/-- The finite-group average fixes exactly the invariant vectors. -/
theorem finiteGroupProjection_eq_self_iff (ρ : Representation ℂ G V) (x : V) :
    finiteGroupProjection ρ x = x ↔ ∀ g, ρ g x = x := by
  constructor
  · intro hx g
    rw [← hx]
    exact finiteGroupProjection_invariant ρ x g
  · intro hx
    letI : Invertible (Fintype.card G : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    exact ρ.averageMap_id x hx

/-- The actual normalized group average is idempotent. -/
theorem finiteGroupProjection_idempotent (ρ : Representation ℂ G V) :
    IsIdempotentElem (finiteGroupProjection ρ) := by
  apply LinearMap.ext
  intro x
  exact (finiteGroupProjection_eq_self_iff ρ _).mpr (finiteGroupProjection_invariant ρ x)

end Algebra

section InnerProduct
variable {G V : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Group invariance moves a representation operator to its inverse in the other slot. -/
theorem representation_inner_inverse (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (g : G) (x y : V) : inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  have h := hρ g x (ρ g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

/-- In a proved invariant inner product, the actual group average is an orthogonal projection. -/
theorem finiteGroupProjection_symmetric [Fintype G] (ρ : Representation ℂ G V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    (finiteGroupProjection ρ).IsSymmetricProjection := by
  refine ⟨finiteGroupProjection_idempotent ρ, ?_⟩
  intro x y
  rw [finiteGroupProjection_eq]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_left, inner_smul_right,
    sum_inner, inner_sum, map_inv₀, map_natCast]
  congr 1
  simp only [representation_inner_inverse ρ hρ]
  exact Equiv.sum_comp (Equiv.inv G) (fun g => inner ℂ x (ρ g y))

end InnerProduct
end
end Dubon2026
