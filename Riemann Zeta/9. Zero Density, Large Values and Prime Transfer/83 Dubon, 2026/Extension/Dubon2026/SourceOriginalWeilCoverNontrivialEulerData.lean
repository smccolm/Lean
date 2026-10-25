import Dubon2026.SourceOriginalWeilCoverLiftedEuler
import Dubon2026.SourceOriginalLiftedMarkedEulerNontrivialAssembly
import Dubon2026.SourceOriginalWeilCoverVertexNontrivial
import Dubon2026.SourceCoverLiftedMarkedCells

/-! DUB-17/18 -> actual cover reciprocity -> complete geometric Euler input.
For every actual basepoint and finite marked set, construct the analytic
cover dissection with exact centers, separation, actual vertex incidence
and the Euler identity for the actual regular-differential genus. The count
uses proved restriction fibers, the native base dissection identity and
unramified genus multiplicity. No geometric or Euler hypothesis remains. -/
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



theorem cover_nontrivial_euler_dissection_of_centered_base (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked)
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE))
    (hcent : ∀ w ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : A.Index,
      w.restrict FF ∈ (A.cell i).interior' ∧ (A.cell i).ζ (w.restrict FF) = (A.cell i).R.q)
    (hsep : ∀ i : A.Index, ((A.cell i).carrier ∩
      (fun w : Place ℂ EE => w.restrict FF) '' (S : Set (Place ℂ EE))).Subsingleton) :
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
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0 := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_connectedSpace N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let p : Place ℂ EE → Place ℂ FF := fun w => w.restrict FF
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (J i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  letI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite (J i)
  have h := cover_global_intersection_coordinates N n radicand baseDivisor hRadicand hOrders Marked A
  obtain ⟨V, ζ, hV, ht, hp, hd, hx, ha, T, hinv, hb, ho, hpos, hrev, hinter⟩ := h
  have hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target :=
    fun i j z hz => by rw [(ht i j).1]; exact (hV i).2.2.2.1 hz
  have hpK : ∀ i j z, z ∈ (A.cell i).R.K → p ((ζ i j).symm z) = (A.cell i).ζ.symm z :=
    fun i j z hz => hp i j z ((hV i).2.2.2.1 hz)
  have he := cover_lifted_euler_identity N n radicand baseDivisor hRadicand hOrders Marked A ζ hpK hx
  have hV2 := cover_lifted_vertex_count_ge_two N n radicand baseDivisor hRadicand hOrders Marked A ζ hpK hx
  exact A.exists_lifted_marked_euler_dissection_nontrivial J ζ hK T hrev p hpK hx hinter P₀ S hcent hsep
    (Module.finrank ℂ (regularDifferentials ℂ EE)) he hV2
    (placeFamily N n radicand baseDivisor hRadicand hOrders) ha

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
