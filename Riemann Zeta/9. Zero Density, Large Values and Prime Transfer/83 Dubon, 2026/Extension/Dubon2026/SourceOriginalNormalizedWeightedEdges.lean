import Dubon2026.SourceOriginalPolygonPrimitiveData
import Dubon2026.SourceOriginalDissectionResidueJumps

/-! DUB-17/18 -> original Abel-Jacobi -> bilinear period reciprocity.
Apply the existing weighted edge and residue identities to the same normalized
primitives used by the actual polygon matrix. Their derivatives and jumps,
rather than a second independently chosen primitive family, supply cancellation.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential OriginalChart
open scoped Topology Real
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem normalized_primitive_analytic (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (hP : PrimData D η V Ψ)
    (i : κ) (C : D.ιC) {z : ℂ} (hz : z ∈ (D.cell C).R.K) :
    AnalyticAt ℂ (Ψ i C) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(hP.hVo C).mem_nhds (hP.hKV C hz)] with w hw
  exact (hP.hΨ i C w hw).differentiableAt

theorem normalized_weighted_edge_cancellation (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J) (θ : Ω[F⁄ℂ])
    (hθ : ∀ x ∈ D.skeleton, 0 ≤ x.ordDifferential θ) (e : D.ιE) (i : κ) :
    D.arcInt (fun C s => Ψ i C ((D.cell C).R.loop s) * (D.cell C).bdryIntegrand θ s)
      (D.arcOf (e, true)) +
    D.arcInt (fun C s => Ψ i C ((D.cell C).R.loop s) * (D.cell C).bdryIntegrand θ s)
      (D.arcOf (e, false)) = J e i * D.edgeInt θ e := by
  let p := D.arcOf (e, true)
  let n := D.arcOf (e, false)
  have hp : D.side p.1 p.2 = (e, true) := D.side_arcOf _
  have hn : D.side n.1 n.2 = (e, false) := D.side_arcOf _
  obtain ⟨ψ, hanti, hc, ha, hb, hbd⟩ := D.arc_rev p.1 p.2 n.1 n.2
    (by rw [hp, hn]) (by rw [hp]) (by rw [hn])
  exact (D.cell p.1).weighted_edge_cancellation (D.cell n.1) p.2 n.2 ψ hanti hc ha hb hbd
    θ (fun s hs => hθ _ (D.bdry_mem_skeleton p.1 p.2 hs)) (Ψ i p.1) (Ψ i n.1)
    (fun w hw => (hP.hΨ i p.1 w (hP.hKV p.1 hw)).continuousAt)
    (fun w hw => (hP.hΨ i n.1 w (hP.hKV n.1 hw)).continuousAt) (J e i) (hJ i e)

theorem normalized_weighted_residue_sum (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J) (S : Finset (Place ℂ F))
    (hsep : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (c : Place ℂ F → D.ιC) (hc : ∀ v ∈ S, v ∈ (D.cell (c v)).interior')
    (θ : Ω[F⁄ℂ]) (hpol : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (hreg : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) (i : κ) :
    2 * π * Complex.I * ∑ v ∈ S,
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) *
        Ψ i (c v) ((D.cell (c v)).ζ v) = ∑ e, J e i * D.edgeInt θ e := by
  have hskel := D.regular_on_skeleton S (fun v hv => ⟨c v, hc v hv⟩) θ hreg
  have hsum := D.weighted_residue_jump_sum S hsep hcent θ hpol hreg (Ψ i)
    (fun C z hz => normalized_primitive_analytic D η V Ψ hP i C hz)
    (fun e => J e i) (fun e => normalized_weighted_edge_cancellation D η V Ψ J hP hJ θ hskel e i)
  rw [D.sum_pole_carriers S c hc] at hsum
  exact hsum

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
