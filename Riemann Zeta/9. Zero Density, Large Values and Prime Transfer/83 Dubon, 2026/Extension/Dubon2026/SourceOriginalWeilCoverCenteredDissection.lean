import Dubon2026.SourceOriginalWeilCoverDissectionConstructed
import Dubon2026.SourceOriginalLiftedDissectionIncidence
import Dubon2026.SourceCoverLiftedMarkedCells

/-! DUB-17/18 -> actual third-kind reciprocity -> marked cover dissection.
Apply the proved base centered-cover theorem to the projected marked set.
Projection is injective on each lifted carrier, so exact centers and point
separation lift even when distinct cover points project to the same base point.
Every literal vertex is incident to an actual lifted edge. -/
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



theorem exists_cover_centered_cell_dissection (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) ∧
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0 := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let p : Place ℂ EE → Place ℂ FF := fun w => w.restrict FF
  let S₀ := S.image p
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N (p P₀) S₀
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (J i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  letI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite (J i)
  have h := cover_global_intersection_coordinates N n radicand baseDivisor hRadicand hOrders Marked A
  obtain ⟨V, ζ, hV, ht, hp, hd, hx, ha, T, hinv, hb, ho, hpos, hrev, hinter⟩ := h
  have hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target :=
    fun i j z hz => by rw [(ht i j).1]; exact (hV i).2.2.2.1 hz
  have hpK : ∀ i j z, z ∈ (A.cell i).R.K → p ((ζ i j).symm z) = (A.cell i).ζ.symm z :=
    fun i j z hz => hp i j z ((hV i).2.2.2.1 hz)
  have hcover : ∀ w : Place ℂ EE, ∃ i : Σ c : A.Index, J c,
      w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K := by
    intro w
    obtain ⟨i, hi⟩ := A.covers (w.restrict FF)
    obtain ⟨j, hj⟩ := hx i w hi
    exact ⟨⟨i, j⟩, hj⟩
  have hconn := cover_global_adjacency N n radicand baseDivisor hRadicand hOrders
    Marked A ζ T hK hcover hinter
  let D := A.toLiftedDissection J ζ hK T hrev hcover hinter hconn
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hpw : p w ∈ insert (p P₀) (S₀ : Set (Place ℂ FF)) := by
      rcases hw with hw | hw
      · exact Or.inl (congrArg p hw)
      · exact Or.inr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    obtain ⟨i, hi, hci⟩ := hcent (p w) hpw
    obtain ⟨j, hj⟩ := hx i w ((A.cell i).interior_subset_carrier hi)
    refine ⟨⟨i, j⟩, ?_⟩
    exact SheetCover.lifted_cell_center p (A.cell i).ζ (ζ i j) (A.cell i).R
      (A.cell i).hKt (hK i j) (hpK i j) hj hci
  · intro i
    have hs : ((A.cell i.1).carrier ∩ p '' (S : Set (Place ℂ EE))).Subsingleton := by
      simpa only [S₀, Finset.coe_image] using hsep i.1
    exact SheetCover.lifted_marked_separation p (A.cell i.1).ζ (ζ i.1 i.2) (A.cell i.1).R
      (A.cell i.1).hKt (hpK i.1 i.2) (S : Set (Place ℂ EE)) hs
  · exact CellPairing.lifted_vertex_injective J (fun i j => (ζ i j).symm)
  · exact A.lifted_dissection_vertex_incidence J ζ hK T hrev hcover hinter hconn
  · intro i P hP
    exact ha i.1 i.2 P hP

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
