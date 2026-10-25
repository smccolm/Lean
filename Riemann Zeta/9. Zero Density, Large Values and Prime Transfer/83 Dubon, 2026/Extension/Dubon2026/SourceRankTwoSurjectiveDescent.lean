import Dubon2026.SourceExplicitRankTwoCoordinates

/-! DUB-17/18 -> original primitive Tate image. Descend already proved
rank-two word coordinates through the actual surjective Hecke presentation.
This extends the native coordinate reindexing to the quotient presentation. -/
namespace Dubon2026
variable {K T V I J : Type*} [CommRing K] [Ring T] [Algebra K T]
variable [AddCommMonoid V] [Module K V]

theorem rankTwo_surjective_descent (w : I → J) (hw : Function.Surjective w)
    (u : I → Module.End K V) (v : J → Module.End K V)
    (χ : I → T) (δ : J → T)
    (hv : ∀ i, v (w i) = u i) (hδ : ∀ i, δ (w i) = χ i)
    (he : ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ i x, e (u i x) = fun j => χ i * e x j) :
    ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ t x, e (v t x) = fun j => δ t * e x j := by
  obtain ⟨e, he⟩ := he
  refine ⟨e, fun t x => ?_⟩
  obtain ⟨i, rfl⟩ := hw t
  rw [hv, hδ]
  exact he i x

end Dubon2026
