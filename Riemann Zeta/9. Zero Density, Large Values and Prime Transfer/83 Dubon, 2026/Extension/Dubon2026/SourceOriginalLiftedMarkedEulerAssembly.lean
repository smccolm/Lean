import Dubon2026.SourceOriginalLiftedDissectionIncidence
import Dubon2026.SourceCoverLiftedMarkedCells
import Dubon2026.SourceOriginalLiftedCoverAdjacency
import Mathlib.SetTheory.Cardinal.Finite

/-! DUB-17/18 -> actual cover reciprocity -> assembled marked Euler geometry.
Assemble the proved source dissection fields before specializing to the large
literal cover field. The actual consumer supplies the proved Euler count,
connected Hausdorff cover, projected marked data and analytic coordinates. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set CellPairing
attribute [local instance] OriginalChart.placeTopology
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_lifted_marked_euler_dissection {X : Type} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
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
    (p : X → Place ℂ (modularFunctionFieldOver N ℂ))
    (hp : ∀ i j z, z ∈ (A.cell i).R.K → p ((ζ i j).symm z) = (A.cell i).ζ.symm z)
    (hx : ∀ i w, p w ∈ (A.cell i).carrier → ∃ j, w ∈ (ζ i j).symm '' (A.cell i).R.K)
    (hinter : ∀ (i j : Σ c : A.Index, J c) (w : X),
      w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K →
      w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K →
      Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j)
    (P₀ : X) (S : Finset X)
    (hcent : ∀ w ∈ insert P₀ (S : Set X), ∃ i : A.Index,
      p w ∈ (A.cell i).interior' ∧ (A.cell i).ζ (p w) = (A.cell i).R.q)
    (hsep : ∀ i : A.Index, ((A.cell i).carrier ∩ p '' (S : Set X)).Subsingleton)
    (g : ℕ)
    (hEuler : (Nat.card (LiftedVertex (cell := A.cell) J (fun i j => (ζ i j).symm)) : ℤ) -
      (Nat.card (Σ e : A.pairing.Edge, J e.1.1) : ℤ) + (Nat.card (Σ i : A.Index, J i) : ℤ) = 2 - 2 * (g : ℤ))
    (family : X → ℂ → X)
    (ha : ∀ i j P, P ∈ (ζ i j).source →
      AnalyticAt ℂ (ζ i j ∘ family P) 0 ∧ deriv (ζ i j ∘ family P) 0 ≠ 0) :
    ∃ D : RadialCellDissection X,
      (∀ P ∈ insert P₀ (S : Set X), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set X)).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) = 2 - 2 * (g : ℤ)) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) ∧
      ∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ family P) 0 ∧ deriv ((D.cell i).ζ ∘ family P) 0 ≠ 0 := by
  classical
  have hcover : ∀ w : X, ∃ i : Σ c : A.Index, J c, w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K := by
    intro w
    obtain ⟨i, hi⟩ := A.covers (p w)
    obtain ⟨j, hj⟩ := hx i w hi
    exact ⟨⟨i, j⟩, hj⟩
  have hconn := A.lifted_cover_adjacency J ζ T hK hcover hinter
  let D := A.toLiftedDissection J ζ hK T hrev hcover hinter hconn
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi, hci⟩ := hcent w hw
    obtain ⟨j, hj⟩ := hx i w ((A.cell i).interior_subset_carrier hi)
    exact ⟨⟨i, j⟩, SheetCover.lifted_cell_center p (A.cell i).ζ (ζ i j) (A.cell i).R
      (A.cell i).hKt (hK i j) (hp i j) hj hci⟩
  · intro i
    exact SheetCover.lifted_marked_separation p (A.cell i.1).ζ (ζ i.1 i.2) (A.cell i.1).R
      (A.cell i.1).hKt (hp i.1 i.2) (S : Set X) (hsep i.1)
  · simpa only [Nat.card_eq_fintype_card] using hEuler
  · exact lifted_vertex_injective J (fun i j => (ζ i j).symm)
  · exact A.lifted_dissection_vertex_incidence J ζ hK T hrev hcover hinter hconn
  · intro i P hP
    exact ha i.1 i.2 P hP

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
