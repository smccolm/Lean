import Dubon2026.SourceOriginalPairedArcOverlap
import Dubon2026.SourceOriginalCellPrimitiveJumps

/-! DUB-17/18 -> raw reciprocity -> actual cell primitives and edge jumps.
For any genuine source dissection, every family of original regular
differentials has constructed normalized cell primitives and constant jumps on
all paired edges. The domains, primitives, overlap and jump constants are
derived. Dissection existence, edge-integral cancellation and the global
residue and loop-generation conclusions remain to be proved.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.exists_regular_primitives_and_jumps (𝒟 : CellDissection N)
    {κ : Type*} (η : κ → Ω[F⁄ℂ]) (hη : ∀ i, η i ∈ regularDifferentials ℂ F) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      (∀ C, IsOpen (V C) ∧ (𝒟.cell C).R.q ∈ V C ∧
        StarConvex ℝ (𝒟.cell C).R.q (V C) ∧ (𝒟.cell C).R.K ⊆ V C ∧ V C ⊆ (𝒟.cell C).ζ.target) ∧
      (∀ i C, Ψ i C (𝒟.cell C).R.q = 0 ∧
        ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w) ∧
      ∀ e i,
        let p := 𝒟.arcOf (e, true)
        let n := 𝒟.arcOf (e, false)
        ∀ s ∈ (𝒟.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((𝒟.cell p.1).R.loop s) -
            Ψ i n.1 ((𝒟.cell n.1).ζ ((𝒟.cell p.1).bdry s)) = J e i := by
  have hex := fun C : 𝒟.ιC => (𝒟.cell C).exists_regular_primitives η hη
  choose V Ψ hVo hVq hVs hKV hVt hΨ using hex
  have hj : ∀ e : 𝒟.ιE, ∀ i : κ, ∃ J : ℂ,
      let p := 𝒟.arcOf (e, true)
      let n := 𝒟.arcOf (e, false)
      ∀ s ∈ (𝒟.cell p.1).R.arcIcc p.2,
        Ψ p.1 i ((𝒟.cell p.1).R.loop s) -
          Ψ n.1 i ((𝒟.cell n.1).ζ ((𝒟.cell p.1).bdry s)) = J := by
    intro e i
    let p := 𝒟.arcOf (e, true)
    let n := 𝒟.arcOf (e, false)
    exact (𝒟.cell p.1).primitive_jump_on_arc (𝒟.cell n.1) p.2 (𝒟.paired_arc_overlap e)
      (η i) (Ψ p.1 i) (Ψ n.1 i)
      (fun w hw => (hΨ p.1 i).2 w (hKV p.1 hw))
      (fun w hw => (hΨ n.1 i).2 w (hKV n.1 hw))
  choose J hJ using hj
  exact ⟨V, fun i C => Ψ C i, J, fun C => ⟨hVo C, hVq C, hVs C, hKV C, hVt C⟩,
    fun i C => hΨ C i, hJ⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
