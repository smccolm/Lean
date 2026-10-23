import Dubon2026.SourceHeckeLinearGaloisTransport
import Dubon2026.SourceRankTwoCoordinateTopology

/-! Assemble the existing Hecke-linearity and topology results while
retaining a fixed coefficient algebra. DUB-17/18 uses this with the actual
original matrix algebra so the prescribed eigencharacter can be applied. -/
namespace Dubon2026
noncomputable section
open Matrix

theorem exists_continuous_hecke_coordinate_rep
    {K T V G I : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [CommRing T] [Algebra K T] [TopologicalSpace T] [IsModuleTopology K T]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [TopologicalSpace V] [IsModuleTopology K V]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : I → T) (hgen : Algebra.adjoin K (Set.range χ) = ⊤)
    (u : I → Module.End K V)
    (he : ∃ e : V ≃ₗ[K] (Fin 2 → T), ∀ i x, e (u i x) = fun a => χ i * e x a)
    (ρ : G →* Module.End K V) (hcomm : ∀ g i, Commute (ρ g) (u i))
    (hρ : ∀ x, Continuous (fun g => ρ g x)) :
    ∃ (e : V ≃ₗ[K] (Fin 2 → T)) (σ : G →* GeneralLinearGroup (Fin 2) T),
      (∀ i x, e (u i x) = fun a => χ i * e x a) ∧ Continuous σ ∧
      ∀ g x, (σ g).val *ᵥ e x = e (ρ g x) := by
  obtain ⟨e, he⟩ := he
  letI : Module.Finite K T := finite_coefficients_of_rankTwo e
  letI : IsTopologicalRing T := IsModuleTopology.isTopologicalRing K T
  let τ := heckeLinearGaloisRep χ hgen u e he ρ hcomm
  have ht := heckeLinearGaloisRep_equivariant χ hgen u e he ρ hcomm
  refine ⟨e, rankTwoGeneralLinearRep τ, he, ?_, ?_⟩
  · exact rankTwoGeneralLinearRep_continuous τ
      (rankTwo_coordinate_action_continuous e ρ τ ht hρ)
  · intro g x
    exact (rankTwoGeneralLinearRep_action τ g (e x)).trans (ht g x)

end
end Dubon2026
