import Dubon2026.SourceOriginalWeightedEdgeCancellation
import Dubon2026.SourceOriginalDissectionPrimitiveJumps

/-! DUB-17/18 -> raw reciprocity -> the actual global residue-jump identity.
For every genuine source dissection and original regular differential family,
the constructed primitives and jumps satisfy the required weighted cancellation
on every paired edge, for every original differential regular on the skeleton.
Dissection existence and the finite global sum are still separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.bdry_mem_skeleton (𝒟 : CellDissection N) (C : 𝒟.ιC)
    (k : Fin (𝒟.cell C).R.N) {s : ℝ} (hs : s ∈ (𝒟.cell C).R.arcIcc k) :
    (𝒟.cell C).bdry s ∈ 𝒟.skeleton :=
  mem_iUnion.mpr ⟨⟨C, k⟩, ⟨(𝒟.cell C).R.loop s, ⟨s, hs, rfl⟩, rfl⟩⟩

theorem CellDissection.exists_regular_primitives_edge_cancellation (𝒟 : CellDissection N)
    {κ : Type*} (η : κ → Ω[F⁄ℂ]) (hη : ∀ i, η i ∈ regularDifferentials ℂ F) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      (∀ C, IsOpen (V C) ∧ (𝒟.cell C).R.q ∈ V C ∧
        StarConvex ℝ (𝒟.cell C).R.q (V C) ∧ (𝒟.cell C).R.K ⊆ V C ∧ V C ⊆ (𝒟.cell C).ζ.target) ∧
      (∀ i C, Ψ i C (𝒟.cell C).R.q = 0 ∧
        ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w) ∧
      (∀ e i,
        let p := 𝒟.arcOf (e, true)
        let n := 𝒟.arcOf (e, false)
        ∀ s ∈ (𝒟.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((𝒟.cell p.1).R.loop s) -
            Ψ i n.1 ((𝒟.cell n.1).ζ ((𝒟.cell p.1).bdry s)) = J e i) ∧
      ∀ (θ : Ω[F⁄ℂ]), (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) → ∀ e i,
        let p := 𝒟.arcOf (e, true)
        let n := 𝒟.arcOf (e, false)
        (∫ s in ((𝒟.cell p.1).R.φs p.2.castSucc)..((𝒟.cell p.1).R.φs p.2.succ),
          Ψ i p.1 ((𝒟.cell p.1).R.loop s) * (𝒟.cell p.1).bdryIntegrand θ s) +
          (∫ t in ((𝒟.cell n.1).R.φs n.2.castSucc)..((𝒟.cell n.1).R.φs n.2.succ),
            Ψ i n.1 ((𝒟.cell n.1).R.loop t) * (𝒟.cell n.1).bdryIntegrand θ t) =
              J e i * 𝒟.edgeInt θ e := by
  obtain ⟨V, Ψ, J, hV, hΨ, hJ⟩ := 𝒟.exists_regular_primitives_and_jumps η hη
  refine ⟨V, Ψ, J, hV, hΨ, hJ, ?_⟩
  intro θ hθ e i
  let p := 𝒟.arcOf (e, true)
  let n := 𝒟.arcOf (e, false)
  have hp : 𝒟.side p.1 p.2 = (e, true) := 𝒟.side_arcOf _
  have hn : 𝒟.side n.1 n.2 = (e, false) := 𝒟.side_arcOf _
  obtain ⟨ψ, hanti, hc, ha, hb, hbd⟩ := 𝒟.arc_rev p.1 p.2 n.1 n.2
    (by rw [hp, hn]) (by rw [hp]) (by rw [hn])
  exact (𝒟.cell p.1).weighted_edge_cancellation (𝒟.cell n.1) p.2 n.2 ψ hanti hc ha hb hbd
    θ (fun s hs => hθ _ (𝒟.bdry_mem_skeleton p.1 p.2 hs))
    (Ψ i p.1) (Ψ i n.1)
    (fun w hw => ((hΨ i p.1).2 w ((hV p.1).2.2.2.1 hw)).continuousAt)
    (fun w hw => ((hΨ i n.1).2 w ((hV n.1).2.2.2.1 hw)).continuousAt)
    (J e i) (hJ e i)

end
end Dubon2026.SourceFunctionField.CellGeometry
