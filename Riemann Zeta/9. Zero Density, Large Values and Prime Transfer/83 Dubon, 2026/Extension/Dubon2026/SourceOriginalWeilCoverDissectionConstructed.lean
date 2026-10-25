import Dubon2026.SourceOriginalLiftedDissectionAssembly
import Dubon2026.SourceOriginalWeilCoverGlobalAdjacency

/-! DUB-17/18 -> cover reciprocity -> constructed actual analytic dissection.
Assemble every source geometric dissection field on the literal Kummer-cover
place space, using the proved global sheet families, pairing, pointwise chains
and global adjacency. The vertex inclusion is injective and every actual
coordinate is analytic with nonzero derivative. Reciprocity is not assumed
or concluded by this geometric construction. -/
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


theorem exists_cover_cell_dissection (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE), Function.Injective D.vert ∧
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0 := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (J i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  letI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite (J i)
  have h := cover_global_intersection_coordinates N n radicand baseDivisor hRadicand hOrders Marked A
  obtain ⟨V, ζ, hV, ht, hp, hd, hx, ha, T, hinv, hb, ho, hpos, hrev, hinter⟩ := h
  have hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target :=
    fun i j z hz => by rw [(ht i j).1]; exact (hV i).2.2.2.1 hz
  have hcover : ∀ w : Place ℂ EE, ∃ i : Σ c : A.Index, J c,
      w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K := by
    intro w
    obtain ⟨i, hi⟩ := A.covers (w.restrict FF)
    obtain ⟨j, hj⟩ := hx i w hi
    exact ⟨⟨i, j⟩, hj⟩
  have hconn := cover_global_adjacency N n radicand baseDivisor hRadicand hOrders
    Marked A ζ T hK hcover hinter
  let D := A.toLiftedDissection J ζ hK T hrev hcover hinter hconn
  refine ⟨D, ?_, ?_⟩
  · exact CellPairing.lifted_vertex_injective J (fun i j => (ζ i j).symm)
  · intro i P hP
    exact ha i.1 i.2 P hP

theorem exists_actual_cover_cell_dissection :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE), Function.Injective D.vert ∧
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0 := by
  obtain ⟨A, _⟩ := exists_original_global_cell_cover N ∅
  exact exists_cover_cell_dissection N n radicand baseDivisor hRadicand hOrders ∅ A

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
