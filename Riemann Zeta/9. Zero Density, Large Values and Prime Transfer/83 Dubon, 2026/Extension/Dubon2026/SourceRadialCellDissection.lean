import Dubon2026.SourceOriginalAnalyticCells

/-! DUB-17/18 -> actual cover reciprocity -> the full source dissection data.
The original CellDissection hardcodes the base function field. This minimal
geometric form retains every paired-arc, endpoint, finite-cover and connectivity
field for the literal Kummer-cover place space. Its existence is proved in the
consumer; analytic and nonsingular coordinates are proved there separately.
The fields are construction obligations, not postulated mathematical results.
Adapted from SourceOriginalCellDissection and its documented FLT source. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set

/-- A genuine radial region inside a coordinate on the actual space. -/
structure RadialCell (X : Type*) [TopologicalSpace X] where
  /-- The actual local coordinate. -/
  ζ : OpenPartialHomeomorph X ℂ
  /-- The original radial region. -/
  R : RadialRegion
  hKt : R.K ⊆ ζ.target

/-- The actual compact radial carrier. -/
def RadialCell.carrier {X : Type*} [TopologicalSpace X] (C : RadialCell X) : Set X := C.ζ.symm '' C.R.K
/-- The actual lifted radial boundary. -/
def RadialCell.bdry {X : Type*} [TopologicalSpace X] (C : RadialCell X) (t : ℝ) : X := C.ζ.symm (C.R.loop t)
/-- The actual image of a radial boundary arc. -/
def RadialCell.arc {X : Type*} [TopologicalSpace X] (C : RadialCell X) (k : Fin C.R.N) : Set X := C.ζ.symm '' C.R.arcSet k

/-- Full source geometric dissection data on the actual space. -/
structure RadialCellDissection (X : Type*) [TopologicalSpace X] where

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
  /-- The genuine radial coordinate cell assigned to each index. -/
  cell : ιC → RadialCell X

  /-- The paired edge and orientation of each source arc. -/
  side : (C : ιC) → Fin (cell C).R.N → ιE × Bool

  side_bij : Function.Bijective fun p : (Σ C : ιC, Fin (cell C).R.N) => side p.1 p.2

  /-- The endpoints of each oriented geometric edge. -/
  ends : ιE → ιV × ιV
  /-- The actual point of each vertex. -/
  vert : ιV → X

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

  inter : ∀ (C C' : ιC) (x : X), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
    Relation.ReflTransGen
      (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (side A k).1 = (side B k').1 ∧ x ∈ (cell A).arc k)
      C C'

  conn : ∀ C C' : ιC, Relation.ReflTransGen
    (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N), (side A k).1 = (side B k').1)
    C C'

attribute [instance] RadialCellDissection.fintypeC RadialCellDissection.fintypeE RadialCellDissection.fintypeV
  RadialCellDissection.decEqC RadialCellDissection.decEqE RadialCellDissection.decEqV

end
end Dubon2026.SourceFunctionField.CellGeometry
