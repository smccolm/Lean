import Dubon2026.OriginalInducedRelationAcyclicity
import Dubon2026.OriginalClassH2TraceInjection
import Dubon2026.OriginalRelationExtensionObstruction

/-! # Detect the actual subgroup obstruction from induced H2 vanishing

DUB-17's induced middle-extension step needs no new Shapiro/connecting
comparison. The actual induced connecting isomorphism detects the whole
H2 coefficient map. Existing trace injectivity detects its restriction,
and the actual induction unit gives the adjoint subgroup map.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Zero of the induced relation obstruction forces zero of the original
subgroup relation obstruction, using the actual class trace. -/
theorem originalInducedRelation_zero_obstruction_restricts
    {G : Type} [Group G] [Fintype G]
    (C : Rep.{0} ℤ G) (u : groupCohomology C 2) (hu : addOrderOf u = Nat.card G)
    (N : Subgroup G) [Fintype N]
    (hc : Nat.card (groupCohomology (Rep.res N.subtype C) 2) = Nat.card N)
    (hg : Submodule.span ℤ
      {(groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u} = ⊤)
    (B : Rep.{0} ℤ G) [Finite B]
    (ψ : Rep.ind N.subtype (originalRelationModule (Rep.res N.subtype B)) ⟶ C)
    (hz : groupCohomology.δ (originalInducedRelationSequence_shortExact N B) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map ψ = 0) :
    originalRelationExtensionObstruction (Rep.res N.subtype B) (Rep.res N.subtype C)
      ((Rep.indResAdjunction ℤ N.subtype).homEquiv _ C ψ) = 0 := by
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  letI := originalInducedRelationConnecting_isIso N B
  have hψ : (groupCohomology.functor ℤ G 2).map ψ = 0 := by
    apply (cancel_epi (groupCohomology.δ
      (originalInducedRelationSequence_shortExact N B) 1 2 rfl)).mp
    simpa only [Limits.comp_zero] using hz
  have hr := originalClassH2_zero_map_restricts _ C u hu N hc hg ψ hψ
  unfold originalRelationExtensionObstruction
  rw [Adjunction.homEquiv_unit]
  erw [Functor.map_comp, hr, Limits.comp_zero]

end
end Dubon2026
