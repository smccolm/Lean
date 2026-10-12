import Dubon2026.ContinuousInvariantConnectingMap
import Dubon2026.ContinuousCoefficientConnectingMap
import Dubon2026.ContinuousCohomologyCup

/-! # The original cochain identity behind cup/connecting-map adjunction

For dual coefficient sequences, a degree-one lift and a degree-zero lift
produce an explicit boundary. This is the sign-sensitive identity needed to
make the local duality exact-sequence argument for DUB-17 use the actual cup.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  (A B C U V W D : Rep.{0} R G)
  (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C)
  (ι : U →ₗ[R] V) (π : V →ₗ[R] W)
  (hι : ∀ g u, ι (U.ρ g u) = V.ρ g (ι u))
  (hπ : ∀ g v, π (V.ρ g v) = W.ρ g (π v))
  (α : A →ₗ[R] W →ₗ[R] D) (β : B →ₗ[R] V →ₗ[R] D)
  (γ : C →ₗ[R] U →ₗ[R] D)
  (hβ : ∀ g b v, β (B.ρ g b) (V.ρ g v) = D.ρ g (β b v))
  (hαβ : ∀ a v, β (φ a) v = α a (π v))
  (hγβ : ∀ b u, β b (ι u) = γ (ψ b) u)

include hι hπ hβ hαβ hγβ in
/-- The differential of the literal mixed lift is evaluation of the lifted
degree-one boundary minus the actual cup with the invariant's boundary. -/
theorem connectingCupAdjunction_boundary
    (b : G → B) (a : G × G → A) (c : G → C) (u : G → U)
    (v : V) (w : W.ρ.invariants)
    (hb : ∀ g, ψ (b g) = c g)
    (ha : ∀ g h, φ (a (g, h)) = B.ρ g (b h) - b (g * h) + b g)
    (hu : ∀ g, ι (u g) = V.ρ g v - v) (hv : π v = w.val)
    (g h : G) :
    groupCohomology.d₁₂ D (fun t => β (b t) (V.ρ t v)) (g, h) =
      α (a (g, h)) w.val - γ (c g) (U.ρ g (u h)) := by
  have hm : V.ρ (g * h) v = V.ρ g (V.ρ h v) :=
    congrArg (fun f : V →ₗ[R] V => f v) (V.ρ.map_mul g h)
  have hw : π (V.ρ (g * h) v) = w.val := by
    rw [hπ, hv]
    exact w.property (g * h)
  have hx : β (φ (a (g, h))) (V.ρ (g * h) v) = α (a (g, h)) w.val := by
    rw [hαβ, hw]
  have hy : β (b g) (V.ρ g (V.ρ h v - v)) = γ (c g) (U.ρ g (u h)) := by
    rw [← hu, ← hι, hγβ, hb]
  change D.ρ g (β (b h) (V.ρ h v)) - β (b (g * h)) (V.ρ (g * h) v) +
    β (b g) (V.ρ g v) = _
  rw [← hβ, ← hm]
  calc
    β (B.ρ g (b h)) (V.ρ (g * h) v) - β (b (g * h)) (V.ρ (g * h) v) +
        β (b g) (V.ρ g v) =
        β (B.ρ g (b h) - b (g * h) + b g) (V.ρ (g * h) v) -
          β (b g) (V.ρ g (V.ρ h v - v)) := by
      rw [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
        map_sub, map_sub, ← hm]
      abel
    _ = α (a (g, h)) w.val - γ (c g) (U.ρ g (u h)) := by
      rw [← ha, hx, hy]

end
end Dubon2026
