import Dubon2026.SourceOriginalWeightedResidueJumpSum
import Dubon2026.SourceOriginalPoleCarrierSum

/-! DUB-17/18 -> raw geometric reciprocity -> the source residue-jump identity.
For the exact one-pole-per-cell and centered dissection outputs, every family of
original regular differentials has constructed normalized cell primitives and
jumps satisfying the full assigned-pole weighted residue identity. Primitive
existence, boundary regularity, reversal, edge cancellation and global summation
are all discharged. Actual dissection construction and loop/matrix reciprocity
remain upstream; this theorem does not assert their existence.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Real Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.exists_regular_primitives_residue_jumps (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hsep : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧
      (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (c : Place ℂ F → 𝒟.ιC) (hc : ∀ v ∈ S, v ∈ (𝒟.cell (c v)).interior')
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
      ∀ (θ : Ω[F⁄ℂ]), (∀ v ∈ S, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) → ∀ i,
          2 * π * Complex.I * ∑ v ∈ S,
            originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) *
              Ψ i (c v) ((𝒟.cell (c v)).ζ v) = ∑ e : 𝒟.ιE, J e i * 𝒟.edgeInt θ e := by
  classical
  obtain ⟨V, Ψ, J, hV, hΨ, hJ, hedge⟩ := 𝒟.exists_regular_primitives_edge_cancellation η hη
  refine ⟨V, Ψ, J, hV, hΨ, hJ, ?_⟩
  intro θ hpol hreg i
  have ha : ∀ C z, z ∈ (𝒟.cell C).R.K → AnalyticAt ℂ (Ψ i C) z := by
    intro C z hz
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [(hV C).1.mem_nhds ((hV C).2.2.2.1 hz)] with w hw
    exact ((hΨ i C).2 w hw).differentiableAt
  have hskel := 𝒟.regular_on_skeleton S (fun v hv => ⟨c v, hc v hv⟩) θ hreg
  have hsum := 𝒟.weighted_residue_jump_sum S hsep hcent θ hpol hreg (Ψ i) ha
    (fun e => J e i) (fun e => hedge θ hskel e i)
  rw [𝒟.sum_pole_carriers S c hc] at hsum
  exact hsum

end
end Dubon2026.SourceFunctionField.CellGeometry
