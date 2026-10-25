import Dubon2026.SourceRadialDissectionTreeCotree
import Dubon2026.SourceOriginalWeilCoverEulerDissection

/-! DUB-17/18 -> actual cover reciprocity -> exact 2g geometric edges.
Apply the existing integer graph spanning-tree and cotree proof to the
constructed marked analytic cover dissection. All geometric and Euler inputs
are discharged; actual loop realization and period generation remain separate. -/
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




open IntegerEdgeChains RadialDissectionTrees

theorem exists_cover_tree_cotree (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ)) ∧
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
        IsWalkConn (hdΓ D) (tlΓ D) T := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h := exists_cover_euler_cell_dissection N n radicand baseDivisor hRadicand hOrders P₀ S
  obtain ⟨D, hcent, hsep, hEuler, hinj, hinc, ha⟩ := h
  letI : Nonempty D.ιC := ⟨(hcent P₀ (Or.inl rfl)).choose⟩
  have htrees := RadialDissectionTrees.exists_tree_cotree D
    (Module.finrank ℂ (regularDifferentials ℂ EE)) hinj hinc hEuler
  obtain ⟨T, Ts, ht, hts, hd, hc, hw⟩ := htrees
  refine ⟨D, hcent, hsep, hEuler, hinj, hinc, ha, T, Ts, ht, hts, hd, hc, ?_⟩
  intro u v
  refine Relation.ReflTransGen.mono (fun {a b} ⟨e, he, hab⟩ => ⟨e, he, ?_⟩) (hw u v)
  rcases hab with hab | hab
  · exact Or.inr ⟨congrArg Prod.snd hab, congrArg Prod.fst hab⟩
  · exact Or.inl ⟨congrArg Prod.snd hab, congrArg Prod.fst hab⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
