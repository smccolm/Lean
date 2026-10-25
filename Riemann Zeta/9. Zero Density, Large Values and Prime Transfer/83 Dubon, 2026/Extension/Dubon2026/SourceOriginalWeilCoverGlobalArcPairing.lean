import Dubon2026.SourceOriginalWeilCoverLiftedArcPairing
import Dubon2026.SourceOriginalWeilCoverCellLiftFamily
import Dubon2026.SourceOriginalGlobalCellPairing

/-! DUB-17/18 -> cover reciprocity -> actual finite paired lifted coordinates.
This names the exact geometric construction statement and then proves it
from the constructed original global cover, its proved pairing, and the
actual complete analytic cover-sheet families. The proposition definition
alone is not an existence proof. Vertices and intersection chains are separate. -/
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

/-- Exact paired-coordinate construction statement; existence is proved below. -/
def CoverGlobalPairedCoordinates (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) : Prop :=
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
      ∀ e : A.pairing.Edge, ∃ ψ : ℝ → ℝ,
        StrictAntiOn ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
        ContDiffOn ℝ 1 ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
        ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.castSucc) = (A.cell e.1.1).R.φs e.1.2.succ ∧
        ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.succ) = (A.cell e.1.1).R.φs e.1.2.castSucc ∧
        ∀ j t, t ∈ (A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2 →
          (ζ (A.pairing.pair e.1).1 (T e j)).symm ((A.cell (A.pairing.pair e.1).1).R.loop t) =
            (ζ e.1.1 j).symm ((A.cell e.1.1).R.loop (ψ t))

theorem cover_global_paired_coordinates (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    CoverGlobalPairedCoordinates N n radicand baseDivisor hRadicand hOrders Marked A := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  have hcell (i : A.Index) := exists_cover_cell_lift_family N n radicand baseDivisor hRadicand hOrders (A.cell i)
  choose V ζ hV hq hc hK hVe hcard ht hp hmap hd hx ha using hcell
  have hζK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target :=
    fun i j z hz => by rw [(ht i j).1]; exact hK i hz
  have hpζ : ∀ i j z, z ∈ (ζ i j).target → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z :=
    fun i j z hz => hp i j z (by rwa [← (ht i j).1])
  have hpair := exists_lifted_pairing_transports N n radicand baseDivisor hRadicand hOrders
    A.cell A.pairing J ζ hζK hpζ hd hx
  exact ⟨V, ζ, fun i => ⟨hV i, hq i, hc i, hK i, hVe i⟩, ht, hp, hd, hx, ha, hpair⟩

theorem exists_cover_global_paired_coordinates (Marked : Finset ℂ) :
    ∃ A : OriginalGlobalCellCover N Marked,
      CoverGlobalPairedCoordinates N n radicand baseDivisor hRadicand hOrders Marked A := by
  obtain ⟨A, _⟩ := exists_original_global_cell_cover N Marked
  exact ⟨A, cover_global_paired_coordinates N n radicand baseDivisor hRadicand hOrders Marked A⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
