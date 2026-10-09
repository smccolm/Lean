import Dubon2026.UnitaryInvariantProjection
import Dubon2026.FiniteGroupProjection
import Mathlib.Tactic.Ring

/-! # Actual cyclic projection gives a genuine mixed matrix-coefficient factorization -/

namespace Dubon2026

noncomputable section

/-- A genuine group homomorphism and original representation compose with their exact multiplication action. -/
theorem representation_hom_mul_apply {G H V : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (j : G →* H)
    (a b : G) (x : V) : ρ (j (a * b)) x = ρ (j a) (ρ (j b) x) := by
  rw [map_mul, map_mul, Module.End.mul_apply]

/-- If the genuine orthogonal projection of a vector is on the original generator line, the actual unitary coefficient factors after multiplication by the original generator norm squared. -/
theorem unitary_projection_coefficient_factor {G V : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (S : Submodule ℂ V) [S.HasOrthogonalProjection] (hS : ∀ g x, x ∈ S → ρ g x ∈ S)
    (y z : V) (hy : y ∈ S) (c : ℂ) (hz : S.starProjection z = c • y) (g : G) :
    inner ℂ y (ρ g z) * inner ℂ y y = inner ℂ y (ρ g y) * inner ℂ y z := by
  have hi (x : V) : inner ℂ y (S.starProjection x) = inner ℂ y x := by
    have he := S.inner_starProjection_left_eq_right y x
    rw [S.starProjection_eq_self_iff.mpr hy] at he
    exact he.symm
  have hg : inner ℂ y (ρ g z) = c * inner ℂ y (ρ g y) := by
    calc
      _ = inner ℂ y (S.starProjection (ρ g z)) := (hi _).symm
      _ = inner ℂ y (ρ g (S.starProjection z)) := by
        rw [unitary_invariant_starProjection ρ hρ S hS]
      _ = _ := by rw [hz, map_smul, inner_smul_right]
  have he : inner ℂ y z = c * inner ℂ y y := by
    rw [← hi z, hz, inner_smul_right]
  rw [hg, he]
  ring

/-- For two genuine commuting unitary actions, factorization of their original generator coefficients implies the full mixed Gram identity on actual orbit vectors. -/
theorem commuting_unitary_mixed_gram {G H V : Type*} [Group G] [Group H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hσ : ∀ h x y, inner ℂ (σ h x) (σ h y) = inner ℂ x y)
    (hcomm : ∀ g h x, ρ g (σ h x) = σ h (ρ g x)) (y : V)
    (hfactor : ∀ g h, inner ℂ y (ρ g (σ h y)) * inner ℂ y y =
      inner ℂ y (ρ g y) * inner ℂ y (σ h y)) (g₁ g₂ : G) (a₁ a₂ : H) :
    inner ℂ (ρ g₁ (σ a₁ y)) (ρ g₂ (σ a₂ y)) * inner ℂ y y =
      inner ℂ (ρ g₁ y) (ρ g₂ y) * inner ℂ (σ a₁ y) (σ a₂ y) := by
  rw [representation_inner_inverse ρ hρ g₁, ← Module.End.mul_apply, ← map_mul]
  rw [hcomm, representation_inner_inverse σ hσ a₁, ← Module.End.mul_apply, ← map_mul, ← hcomm]
  rw [hfactor, representation_inner_inverse ρ hρ g₁, representation_inner_inverse σ hσ a₁]
  simp only [← Module.End.mul_apply, ← map_mul]

end
end Dubon2026
