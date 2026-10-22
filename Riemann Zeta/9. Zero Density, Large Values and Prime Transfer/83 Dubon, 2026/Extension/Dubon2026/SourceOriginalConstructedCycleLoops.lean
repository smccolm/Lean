import Dubon2026.SourceOriginalFundamentalCycleLoops

/-! DUB-17/18 -> original Abel-Jacobi -> actual cycle periods.
The constructed original dissection, trees, polygon and integer cycles now
have actual loops with the exact integral formula for every differential
regular on the skeleton. All geometry and cycle assumptions are discharged
by the same constructed witnesses; period generation and raw reciprocity
remain separate necessary obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees DissectionPolygon OriginalEdgePaths
open KaehlerDifferential OriginalChart
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_centered_cycle_loops (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked)
      (T Ts : Finset A.dissection.ιE) (Z : A.dissection.ιE → A.dissection.ιE → ℤ),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
      Disjoint T Ts ∧
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
      IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      PolygonWordConclusion A.dissection Ts ∧
      (∀ j w, (∑ e with (A.dissection.ends e).2 = w, Z j e) =
        (∑ e with (A.dissection.ends e).1 = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      (∀ {B : Type*} [AddCommGroup B] (f : A.dissection.ιE → B),
        (∀ w, (∑ e with (A.dissection.ends e).2 = w, f e) =
          (∑ e with (A.dissection.ends e).1 = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j) ∧
      ∃ γ : (j : A.dissection.ιE) →
          Path (A.dissection.vert (A.dissection.ends j).1) (A.dissection.vert (A.dissection.ends j).1),
        (∀ j t, γ j t ∈ A.dissection.skeleton) ∧
        ∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton A.dissection θ →
          (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
          pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * A.dissection.edgeInt θ e := by
  classical
  obtain ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec⟩ := exists_original_centered_cycle_system P₀ S
  have hex := fun j => exists_fundamental_cycle_loop A.dissection hz hdelta hzero ht hw j
  choose γ hγ using hex
  refine ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, ?_, ?_⟩
  · exact fun j => (hγ j).1
  · exact fun j => (hγ j).2

end
end Dubon2026.SourceFunctionField.CellGeometry
