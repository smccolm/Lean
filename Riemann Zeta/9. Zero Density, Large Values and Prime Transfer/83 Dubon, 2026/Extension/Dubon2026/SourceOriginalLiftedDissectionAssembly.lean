import Dubon2026.SourceRadialCellDissection
import Dubon2026.SourceOriginalCellPairingLiftVertices
import Dubon2026.SourceOriginalCellPairingLiftDissectionSides
import Dubon2026.SourceOriginalLiftedCoverAdjacency

/-! DUB-17/18 -> actual cover reciprocity -> full dissection assembly.
Construct the complete source-format dissection from the actual sheet families.
All edges and vertices are explicit finite types, side indexing is bijective,
and every endpoint, reversed arc, cover and connectivity field is proved. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open Set CellPairing
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The complete geometric dissection of the actual lifted coordinate family. -/
def toLiftedDissection {X : Type} [TopologicalSpace X]
    (J : A.Index → Type) [∀ i, Fintype (J i)]
    (ζ : (i : A.Index) → J i → OpenPartialHomeomorph X ℂ)
    (hK : ∀ i j, (A.cell i).R.K ⊆ (ζ i j).target)
    (T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1)
    (hrev : ∀ e : A.pairing.Edge, ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
      ContDiffOn ℝ 1 ψ ((A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2) ∧
      ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.castSucc) = (A.cell e.1.1).R.φs e.1.2.succ ∧
      ψ ((A.cell (A.pairing.pair e.1).1).R.φs (A.pairing.pair e.1).2.succ) = (A.cell e.1.1).R.φs e.1.2.castSucc ∧
      ∀ j t, t ∈ (A.cell (A.pairing.pair e.1).1).R.arcIcc (A.pairing.pair e.1).2 →
        (ζ (A.pairing.pair e.1).1 (T e j)).symm ((A.cell (A.pairing.pair e.1).1).R.loop t) =
          (ζ e.1.1 j).symm ((A.cell e.1.1).R.loop (ψ t)))
    (hcover : ∀ w : X, ∃ i : Σ c : A.Index, J c, w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K)
    (hinter : ∀ (i j : Σ c : A.Index, J c) (w : X),
      w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K →
      w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K →
      Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j)
    (hconn : ∀ i j : Σ c : A.Index, J c,
      Relation.ReflTransGen
        (fun a b : Σ c : A.Index, J c =>
          ∃ (k : Fin (A.cell a.1).R.N) (l : Fin (A.cell b.1).R.N),
            A.pairing.liftedPair J T ⟨⟨a.1, k⟩, a.2⟩ = ⟨⟨b.1, l⟩, b.2⟩) i j) :
    RadialCellDissection X := by
  classical
  let f : (i : A.Index) → J i → ℂ → X := fun i j => (ζ i j).symm
  have hends (e : A.pairing.Edge) (j : J e.1.1) :
      liftedEndpoint J f ⟨A.pairing.pair e.1, T e j⟩ false = liftedEndpoint J f ⟨e.1, j⟩ true ∧
        liftedEndpoint J f ⟨A.pairing.pair e.1, T e j⟩ true = liftedEndpoint J f ⟨e.1, j⟩ false := by
    obtain ⟨ψ, _, _, hl, hr, he⟩ := hrev e
    exact A.pairing.lifted_endpoint_reversal J f T e j ψ hl hr (he j)
  have hs (a b : Σ a : (Σ c : A.Index, Fin (A.cell c).R.N), J a.1)
      (h : A.pairing.liftedPair J T a = b) :
      (A.pairing.liftedSideEquiv J T a).1 = (A.pairing.liftedSideEquiv J T b).1 := by
    have hside := congrArg Prod.fst (A.pairing.liftedSideEquiv_pair J T a)
    rw [h] at hside
    exact hside.symm
  exact {
    ιC := Σ c : A.Index, J c
    ιE := Σ e : A.pairing.Edge, J e.1.1
    ιV := LiftedVertex (cell := A.cell) J f
    cell := fun i => ⟨ζ i.1 i.2, (A.cell i.1).R, hK i.1 i.2⟩
    side := fun i k => A.pairing.liftedCellSideEquiv J T ⟨i, k⟩
    side_bij := (A.pairing.liftedCellSideEquiv J T).bijective
    ends := A.pairing.liftedEnds J f
    vert := Subtype.val
    arc_ends := fun i k => A.pairing.lifted_arc_endpoints J f T hends ⟨⟨i.1, k⟩, i.2⟩
    arc_rev := fun i k j l => A.pairing.lifted_reversed_side_arcs J f T hrev ⟨⟨i.1, k⟩, i.2⟩ ⟨⟨j.1, l⟩, j.2⟩
    cover := eq_univ_of_forall fun w => mem_iUnion.mpr (hcover w)
    inter := fun i j w hi hj => Relation.ReflTransGen.mono
      (fun a b ⟨k, l, hp, hw⟩ => ⟨k, l, hs _ _ hp, hw⟩) (hinter i j w hi hj)
    conn := fun i j => Relation.ReflTransGen.mono
      (fun a b ⟨k, l, hp⟩ => ⟨k, l, hs _ _ hp⟩) (hconn i j) }

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
