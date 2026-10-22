import Dubon2026.SourceOriginalOrdinaryArcMatching
import Dubon2026.SourceOriginalBranchArcMatching
import Dubon2026.SourceOriginalExteriorArcMatching
import Dubon2026.SourceOriginalPlanarGridGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> actual geometric pairing.
All three matching results apply to the previously constructed centered
global cover. Its rectangle centers discharge the branch-center identity;
its refined window discharges the exterior center identity. No additional
sheet selection, carrier separation or powered-arc coverage is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem ordinary_arc_matching (p : ℤ × ℤ) (hp : A.G.D.capAt p = none)
    (k : Fin (A.G.region p).N) {L : Set (Place ℂ F)} (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ (A.G.region p).arcSet k)
    (honto : (A.G.region p).arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ i, Fin ((A.G.ordinary p hp).C i).R.N,
      L = ((A.G.ordinary p hp).C a.1).arc a.2 :=
  (A.G.ordinary p hp).exists_unique_arc_over k hL hne hover honto

theorem branch_arc_matching (p : ℤ × ℤ) (b : ℂ) (hp : A.G.D.capAt p = some b)
    (k : Fin (A.G.region p).N) {L : Set (Place ℂ F)} (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ (A.G.region p).arcSet k)
    (honto : (A.G.region p).arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ v, Fin ((A.G.branch p b hp).C v).R.N,
      L = ((A.G.branch p b hp).C a.1).arc a.2 := by
  have hBad : ({0, 1728} : Finset ℂ) ⊆ insert 0 (insert 1728 Marked) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    tauto
  have hq : (A.G.region p).q = b :=
    (A.G.rectangle p).1.trans (A.G.D.cap_center hBad hp)
  exact (A.G.branch p b hp).exists_unique_arc_over hq k hL hne hover honto

theorem exterior_arc_matching (k : Fin A.W.R.N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ A.W.R.arcSet k)
    (honto : A.W.R.arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ v, Fin (A.poles.C v).R.N, L = (A.poles.C a.1).arc a.2 :=
  A.poles.exists_unique_arc_over A.W.q_eq k hL hne hover honto

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
