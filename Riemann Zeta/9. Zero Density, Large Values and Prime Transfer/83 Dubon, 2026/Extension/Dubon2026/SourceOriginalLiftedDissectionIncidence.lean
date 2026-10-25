import Dubon2026.SourceOriginalLiftedDissectionAssembly
import Dubon2026.SourceOriginalLiftedVertexIncidence

/-! DUB-17/18 -> marked cover dissection -> actual vertex incidence.
Use the original endpoint proof before specializing to the large cover field.
Every vertex of the assembled dissection is incident to an actual edge. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open Set CellPairing
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem lifted_dissection_vertex_incidence {X : Type} [TopologicalSpace X]
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
    let D := A.toLiftedDissection J ζ hK T hrev hcover hinter hconn
    ∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v := by
  dsimp only
  intro v
  apply A.pairing.lifted_vertex_incident J (fun i j => (ζ i j).symm) T _ v
  intro e j
  obtain ⟨ψ, _, _, hl, hr, he⟩ := hrev e
  exact A.pairing.lifted_endpoint_reversal J (fun i j => (ζ i j).symm) T e j ψ hl hr (he j)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
