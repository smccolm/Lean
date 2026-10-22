import Dubon2026.SourceOriginalDualTreeNormalization
import Dubon2026.SourceOriginalDissectionPrimitiveJumps

/-! DUB-17/18 -> original Abel-Jacobi -> raw reciprocity.
Reuse the constructed regular cell primitives and constant edge jumps. The
proved dual-tree normalization changes only additive constants, preserves
every derivative and domain, kills the dual-tree jumps and fixes the root.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential IntegerEdgeChains DissectionTrees
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.exists_normalized_primitives_and_jumps (D : CellDissection N)
    (η : κ → Ω[F⁄ℂ]) (hη : ∀ i, η i ∈ regularDifferentials ℂ F)
    (Ts : Finset D.ιE)
    (hTs : IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts)
    (C₀ : D.ιC) (w₀ : ℂ) :
    ∃ (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      (∀ C, IsOpen (V C) ∧ (D.cell C).R.q ∈ V C ∧
        StarConvex ℝ (D.cell C).R.q (V C) ∧ (D.cell C).R.K ⊆ V C ∧ V C ⊆ (D.cell C).ζ.target) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (D.cell C).ζ (η i) w) w) ∧
      (∀ e i,
        let p := D.arcOf (e, true)
        let n := D.arcOf (e, false)
        ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((D.cell p.1).R.loop s) -
            Ψ i n.1 ((D.cell n.1).ζ ((D.cell p.1).bdry s)) = J e i) ∧
      (∀ e ∈ Ts, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  obtain ⟨V, Ψ, J, hV, hΨ, hJ⟩ := D.exists_regular_primitives_and_jumps η hη
  obtain ⟨c, hc, hce⟩ := D.exists_normalising_constants Ts hTs J C₀ (fun i => Ψ i C₀ w₀)
  refine ⟨V, (fun i C w => Ψ i C w + c C i),
    (fun e => J e + c (Cside D e true) - c (Cside D e false)), hV, ?_, ?_, hce, ?_⟩
  · intro i C w hw
    exact ((hΨ i C).2 w hw).add_const _
  · intro e i
    dsimp only
    intro s hs
    have hj := hJ e i s hs
    change Ψ i (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) +
        c (D.arcOf (e, true)).1 i -
        (Ψ i (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).ζ
          ((D.cell (D.arcOf (e, true)).1).bdry s)) + c (D.arcOf (e, false)).1 i) =
      J e i + c (D.arcOf (e, true)).1 i - c (D.arcOf (e, false)).1 i
    linear_combination hj
  · intro i
    simp only [hc, Pi.neg_apply]
    exact add_neg_cancel _

end
end Dubon2026.SourceFunctionField.CellGeometry
