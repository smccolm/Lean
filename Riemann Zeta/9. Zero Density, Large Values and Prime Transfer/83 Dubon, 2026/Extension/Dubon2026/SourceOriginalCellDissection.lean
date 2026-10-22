import Dubon2026.SourceOriginalAnalyticCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! DUB-17/18 -> raw geometric reciprocity -> finite actual cell dissection.
This retains the full source paired-arc, vertex, cover and connectivity data
on the already constructed original curve. Construction of this data remains
an obligation. No Euler count, loop generation or reciprocity is postulated.
Adapted from Def_AlgebraicCurve_CellDissection, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

/-- A genuine finite paired cell dissection of the original complex place curve.
This is geometric data to be constructed; its type alone proves no existence. -/
structure CellDissection (N : ℕ) [NeZero N] where

  /-- The finite cell indices. -/
  ιC : Type
  /-- The finite geometric edge indices. -/
  ιE : Type
  /-- The finite vertex indices. -/
  ιV : Type
  /-- The finite indexing instance used by the source dissection. -/
  [fintypeC : Fintype ιC]
  /-- The finite indexing instance used by the source dissection. -/
  [fintypeE : Fintype ιE]
  /-- The finite indexing instance used by the source dissection. -/
  [fintypeV : Fintype ιV]
  /-- The finite indexing instance used by the source dissection. -/
  [decEqC : DecidableEq ιC]
  /-- The finite indexing instance used by the source dissection. -/
  [decEqE : DecidableEq ιE]
  /-- The finite indexing instance used by the source dissection. -/
  [decEqV : DecidableEq ιV]
  /-- The genuine analytic cell assigned to each index. -/
  cell : ιC → Cell N

  /-- The paired edge and orientation of each source arc. -/
  side : (C : ιC) → Fin (cell C).R.N → ιE × Bool

  side_bij : Function.Bijective fun p : (Σ C : ιC, Fin (cell C).R.N) => side p.1 p.2

  /-- The endpoints of each oriented geometric edge. -/
  ends : ιE → ιV × ιV
  /-- The actual original place of each vertex. -/
  vert : ιV → Place ℂ (modularFunctionFieldOver N ℂ)

  arc_ends : ∀ (C : ιC) (k : Fin (cell C).R.N),
    (cell C).bdry ((cell C).R.φs k.castSucc) =
        vert (if (side C k).2 then (ends (side C k).1).1 else (ends (side C k).1).2) ∧
      (cell C).bdry ((cell C).R.φs k.succ) =
        vert (if (side C k).2 then (ends (side C k).1).2 else (ends (side C k).1).1)

  arc_rev : ∀ (C : ιC) (k : Fin (cell C).R.N) (C' : ιC) (k' : Fin (cell C').R.N),
    (side C k).1 = (side C' k').1 → (side C k).2 = true → (side C' k').2 = false →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell C').R.arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
      ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
      ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
      ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)

  cover : ⋃ C, (cell C).carrier = univ

  inter : ∀ (C C' : ιC) (x : Place ℂ (modularFunctionFieldOver N ℂ)), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
    Relation.ReflTransGen
      (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (side A k).1 = (side B k').1 ∧ x ∈ (cell A).arc k)
      C C'

  conn : ∀ C C' : ιC, Relation.ReflTransGen
    (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N), (side A k).1 = (side B k').1)
    C C'

attribute [instance] CellDissection.fintypeC CellDissection.fintypeE CellDissection.fintypeV
  CellDissection.decEqC CellDissection.decEqE CellDissection.decEqV

variable {N : ℕ} [NeZero N]

/-- The unique cell arc corresponding to an oriented geometric edge. -/
noncomputable def CellDissection.arcOf (𝒟 : CellDissection N) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  Function.surjInv 𝒟.side_bij.surjective q

/-- The actual original differential integral along the positive edge arc. -/
noncomputable def CellDissection.edgeInt (𝒟 : CellDissection N) (θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  ∫ s in ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)..
      ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
    (𝒟.cell (𝒟.arcOf (e, true)).1).bdryIntegrand θ s

/-- The union of all actual original-place edge arcs. -/
def CellDissection.skeleton (𝒟 : CellDissection N) : Set (Place ℂ (modularFunctionFieldOver N ℂ)) :=
  ⋃ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), (𝒟.cell p.1).arc p.2

end
end Dubon2026.SourceFunctionField.CellGeometry
