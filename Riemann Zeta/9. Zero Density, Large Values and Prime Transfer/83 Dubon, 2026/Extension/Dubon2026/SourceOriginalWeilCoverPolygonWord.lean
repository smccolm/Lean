import Dubon2026.SourceRadialDissectionPolygonWord
import Dubon2026.SourceOriginalWeilCoverNontrivialTreeCotree

/-! DUB-17/18 -> actual cover reciprocity -> actual polygon word.
Apply the existing integer graph spanning-tree and cotree proof to the
constructed marked analytic cover dissection. The same actual dissection retains all geometry, Euler identity and the polygon
word with actual vertex matching and closed integer subwords. Analytic loop
realization and period generation remain separate. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders




open IntegerEdgeChains RadialDissectionTrees RadialDissectionPolygon

theorem exists_cover_polygon_word (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ)) ∧
      (2 ≤ Fintype.card D.ιV) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) ∧
      (∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) ∧
      ∃ T Ts : Finset D.ιE,
        IsTree (hdΓ D) (tlΓ D) T ∧
        IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts ∧
        Disjoint T Ts ∧
        (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) ∧
        IsWalkConn (hdΓ D) (tlΓ D) T ∧
        PolygonWordConclusion D Ts := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, ht, hts, hd, hc, hw⟩ :=
    exists_cover_nontrivial_tree_cotree N n radicand baseDivisor hRadicand hOrders P₀ S
  haveI : Nonempty D.ιV := Fintype.card_pos_iff.mp (by omega)
  have hcard := spanningTree_card (hdΓ D) (tlΓ D) T ht
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hTne
  refine ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, ht, hts, hd, hc, hw, ?_⟩
  exact exists_polygon_word D hinj Ts hts
    ⟨e, fun h => Finset.disjoint_left.mp hd he h⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
