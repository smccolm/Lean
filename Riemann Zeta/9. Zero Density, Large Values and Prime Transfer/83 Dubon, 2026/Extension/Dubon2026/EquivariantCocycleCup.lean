import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # The genuine degree-one cup product from an equivariant coefficient pairing -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

include hβ in
/-- The original inhomogeneous cup formula is a genuine two-cocycle. The proof
uses the two original one-cocycle identities and actual coefficient equivariance. -/
theorem equivariantOneCocycleCup_mem
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) :
    (fun z : G × G => β (f z.1) (B.ρ z.1 (u z.2))) ∈ groupCohomology.cocycles₂ C := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h j
  have hf : f (g * h) = A.ρ g (f h) + f g :=
    (groupCohomology.mem_cocycles₁_iff _).mp f.property g h
  have hu : u (h * j) = B.ρ h (u j) + u h :=
    (groupCohomology.mem_cocycles₁_iff _).mp u.property h j
  change β (f (g * h)) (B.ρ (g * h) (u j)) + β (f g) (B.ρ g (u h)) =
    C.ρ g (β (f h) (B.ρ h (u j))) + β (f g) (B.ρ g (u (h * j)))
  rw [hf, hu, ← hβ g (f h) (B.ρ h (u j))]
  simp only [map_add, LinearMap.add_apply, map_mul, Module.End.mul_apply]
  abel

/-- The actual two-cocycle with value `β(f(g), g • u(h))`. -/
def equivariantOneCocycleCup
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) :
    groupCohomology.cocycles₂ C :=
  ⟨fun z => β (f z.1) (B.ρ z.1 (u z.2)), equivariantOneCocycleCup_mem A B C β hβ f u⟩

/-- The constructed cup product retains the exact original inhomogeneous formula. -/
theorem equivariantOneCocycleCup_apply
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) (g h : G) :
    equivariantOneCocycleCup A B C β hβ f u (g, h) = β (f g) (B.ρ g (u h)) := by
  rfl

end
end Dubon2026
