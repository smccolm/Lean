import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Preserve a fixed coefficient algebra while transporting the proved
rank-two matrix realization to original Tate coordinates and its prime
generators. These elementary transport lemmas isolate the exact coordinate
identities already proved for the DUB-17/18 specialization chain. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {K T V A I J : Type*} [CommRing K] [Ring T] [Algebra K T]
variable [AddCommMonoid V] [Module K V] {m : ℕ}

theorem explicitRankTwo_transfer_coordinates
    (M : A → Matrix (Fin m) (Fin m) K) (w : I → A)
    (u : I → Module.End K V) (φ : A → T)
    (c : V ≃ₗ[K] (Fin m → K))
    (hc : ∀ i x, c (u i x) = M (w i) *ᵥ c x)
    (he : ∃ e : (Fin m → K) ≃ₗ[K] (Fin 2 → T),
      ∀ a v, e (M a *ᵥ v) = fun j => φ a * e v j) :
    ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ i x, e (u i x) = fun j => φ (w i) * e x j := by
  obtain ⟨e, he⟩ := he
  exact ⟨c.trans e, fun i x => (congrArg e (hc i x)).trans (he (w i) (c x))⟩

theorem explicitRankTwo_reindex
    (u : I → Module.End K V) (v : J → Module.End K V) (w : J → I)
    (hv : ∀ j, v j = u (w j)) (χ : I → T)
    (he : ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ i x, e (u i x) = fun a => χ i * e x a) :
    ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ j x, e (v j x) = fun a => χ (w j) * e x a := by
  obtain ⟨e, he⟩ := he
  exact ⟨e, fun j x => (congrArg (fun U : Module.End K V => e (U x)) (hv j)).trans
    (he (w j) x)⟩

end
end Dubon2026
