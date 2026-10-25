import Dubon2026.SourceOriginalWeilCoverGlobalArcPairing
import Dubon2026.SourceOriginalCoverLiftedIntersectionChains

/-! DUB-17/18 -> cover reciprocity -> actual lifted dissection.
The already constructed global coordinates and arc pairing now carry the
pointwise intersection chains inherited from the proved base dissection.
Every new chain premise is discharged by exact projection, arc reversal
and disjoint sheets. Vertex assembly and reciprocity remain separate. -/
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

/-- The exact constructed lifted pairing together with its pointwise intersection chains. -/
def CoverGlobalIntersectionCoordinates (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) : Prop :=
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  ∃ (V : A.Index → Set ℂ) (ζ : (i : A.Index) → J i → OpenPartialHomeomorph (Place ℂ EE) ℂ),
    (∀ i, IsOpen (V i) ∧ (A.cell i).R.q ∈ V i ∧ StarConvex ℝ (A.cell i).R.q (V i) ∧
      (A.cell i).R.K ⊆ V i ∧ V i ⊆ (A.cell i).ζ.target) ∧
    (∀ i j, (ζ i j).target = V i ∧ j.1 ∈ (ζ i j).source ∧ ζ i j j.1 = (A.cell i).R.q) ∧
    (∀ i j z, z ∈ V i → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z) ∧
    (∀ i, Pairwise fun j k => Disjoint (ζ i j).source (ζ i k).source) ∧
    (∀ i w, w.restrict FF ∈ (A.cell i).carrier → ∃ j, w ∈ (ζ i j).symm '' (A.cell i).R.K) ∧
    (∀ i j P, P ∈ (ζ i j).source →
      AnalyticAt ℂ (ζ i j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
        deriv (ζ i j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) ∧
    ∃ T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1,
      Function.Involutive (A.pairing.liftedPair J T) ∧
      (∀ a, (A.pairing.liftedPair J T a).1 = A.pairing.pair a.1) ∧
      (∀ a, A.pairing.orient (A.pairing.liftedPair J T a).1 = !A.pairing.orient a.1) ∧
      (∀ e j, A.pairing.liftedPair J T ⟨e.1, j⟩ = ⟨A.pairing.pair e.1, T e j⟩) ∧
      (∀ e : A.pairing.Edge, ∃ ψ : ℝ → ℝ,
        StrictAntiOn ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
        ContDiffOn ℝ 1 ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
        ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.castSucc) = (A.cell e.1.1).R.φs e.1.2.succ ∧
        ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.succ) = (A.cell e.1.1).R.φs e.1.2.castSucc ∧
        ∀ j t, t ∈ (A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2 →
          (ζ (A.pairing.pair e.1).1 (T e j)).symm ((A.cell (A.pairing.pair e.1).1).R.loop t) =
            (ζ e.1.1 j).symm ((A.cell e.1.1).R.loop (ψ t))) ∧
      ∀ (i j : Σ c : A.Index, J c) (w : Place ℂ EE),
        w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K →
        w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K →
        Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j

theorem cover_global_intersection_coordinates (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    CoverGlobalIntersectionCoordinates N n radicand baseDivisor hRadicand hOrders Marked A := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  have h := cover_global_paired_coordinates N n radicand baseDivisor hRadicand hOrders Marked A
  obtain ⟨V, ζ, hV, ht, hp, hd, hx, ha, T, hinv, hb, ho, hpos, hrev⟩ := h
  have hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target :=
    fun i j z hz => by rw [(ht i j).1]; exact (hV i).2.2.2.1 hz
  have hpK : ∀ i j z, z ∈ (A.cell i).R.K → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z :=
    fun i j z hz => hp i j z ((hV i).2.2.2.1 hz)
  have harcs := A.pairing.liftedPair_arc_images_of_reversal J (fun c s => (ζ c s).symm) T hrev
  refine ⟨V, ζ, hV, ht, hp, hd, hx, ha, T, hinv, hb, ho, hpos, hrev, ?_⟩
  intro i j w hi hj
  exact A.lifted_intersection_chain (fun w : Place ℂ EE => w.restrict FF) J ζ hK hpK hd T harcs i j w hi hj

theorem exists_cover_global_intersection_coordinates (Marked : Finset ℂ) :
    ∃ A : OriginalGlobalCellCover N Marked,
      CoverGlobalIntersectionCoordinates N n radicand baseDivisor hRadicand hOrders Marked A := by
  obtain ⟨A, _⟩ := exists_original_global_cell_cover N Marked
  exact ⟨A, cover_global_intersection_coordinates N n radicand baseDivisor hRadicand hOrders Marked A⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
