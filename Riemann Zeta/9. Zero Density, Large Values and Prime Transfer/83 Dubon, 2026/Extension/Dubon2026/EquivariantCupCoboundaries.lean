import Dubon2026.EquivariantCocycleCup

/-! # Exact original coboundary witnesses for the degree-one cup product -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
    (β : A →ₗ[R] B →ₗ[R] C)
    (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

/-- Cupping an original degree-zero coboundary on the left is the original
degree-one differential of the explicit cochain `g ↦ β(a, u(g))`. -/
theorem equivariantOneCocycleCup_coboundary_left
    (a : A) (u : groupCohomology.cocycles₁ B) :
    (equivariantOneCocycleCup A B C β hβ
      ⟨groupCohomology.d₀₁ A a, groupCohomology.d₀₁_apply_mem_cocycles₁ (A := A) a⟩ u :
        G × G → C) =
      groupCohomology.d₁₂ C (fun g => β a (u g)) := by
  funext z
  rcases z with ⟨g, h⟩
  have hu : u (g * h) = B.ρ g (u h) + u g :=
    (groupCohomology.mem_cocycles₁_iff _).mp u.property g h
  change β (A.ρ g a - a) (B.ρ g (u h)) =
    C.ρ g (β a (u h)) - β a (u (g * h)) + β a (u g)
  rw [hu, ← hβ g a (u h)]
  simp only [map_sub, LinearMap.sub_apply, map_add]
  abel

/-- Cupping an original coboundary on the right uses the negative explicit
cochain `g ↦ -β(f(g), g • b)`, retaining the actual inhomogeneous sign. -/
theorem equivariantOneCocycleCup_coboundary_right
    (f : groupCohomology.cocycles₁ A) (b : B) :
    (equivariantOneCocycleCup A B C β hβ f
      ⟨groupCohomology.d₀₁ B b, groupCohomology.d₀₁_apply_mem_cocycles₁ (A := B) b⟩ :
        G × G → C) =
      groupCohomology.d₁₂ C (fun g => -β (f g) (B.ρ g b)) := by
  funext z
  rcases z with ⟨g, h⟩
  have hf : f (g * h) = A.ρ g (f h) + f g :=
    (groupCohomology.mem_cocycles₁_iff _).mp f.property g h
  change β (f g) (B.ρ g (B.ρ h b - b)) =
    C.ρ g (-β (f h) (B.ρ h b)) - (-β (f (g * h)) (B.ρ (g * h) b)) +
      (-β (f g) (B.ρ g b))
  rw [map_neg, ← hβ g (f h) (B.ρ h b), hf]
  simp only [map_sub, map_add, LinearMap.add_apply, map_mul, Module.End.mul_apply]
  abel

end
end Dubon2026
