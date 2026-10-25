import Dubon2026.SourceFiniteClosedCoverAdjacency
import Dubon2026.SourceOriginalCoverLiftedIntersectionChains

/-! DUB-17/18 -> actual cover dissection -> global adjacency.
Apply the existing finite closed-cover argument to lifted radial carriers.
The actual cover consumer supplies connectedness, Hausdorffness and finite
sheet indices, avoiding expansion of its splitting field in this topology proof. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open Set
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem lifted_cover_adjacency {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    (J : A.Index → Type) [Finite (Σ c : A.Index, J c)]
    (ζ : (i : A.Index) → J i → OpenPartialHomeomorph X ℂ)
      (T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1) :
      (∀ i j, (A.cell i).R.K ⊆ (ζ i j).target) →
      (∀ w : X, ∃ i : Σ c : A.Index, J c, w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K) →
      (∀ (i j : Σ c : A.Index, J c) (w : X),
        w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K →
        w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K →
        Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j) →
      ∀ i j : Σ c : A.Index, J c,
        Relation.ReflTransGen
          (fun a b : Σ c : A.Index, J c =>
            ∃ (k : Fin (A.cell a.1).R.N) (l : Fin (A.cell b.1).R.N),
              A.pairing.liftedPair J T ⟨⟨a.1, k⟩, a.2⟩ = ⟨⟨b.1, l⟩, b.2⟩) i j := by
  intro hK hcover hinter i j
  apply SheetCover.finite_closed_cover_reachable
    (fun i : Σ c : A.Index, J c => (ζ i.1 i.2).symm '' (A.cell i.1).R.K) _ _ _ hcover _ i j
  · intro a
    exact ((A.cell a.1).R.isCompact_K.image_of_continuousOn
      ((ζ a.1 a.2).continuousOn_symm.mono (hK a.1 a.2))).isClosed
  · intro a
    refine ⟨(ζ a.1 a.2).symm (A.cell a.1).R.q, (A.cell a.1).R.q, ?_, rfl⟩
    change ‖(A.cell a.1).R.q - (A.cell a.1).R.q‖ ≤ _
    rw [sub_self, norm_zero]
    exact ((A.cell a.1).R.hpos _).le
  · intro a b w ha hb
    exact Relation.ReflTransGen.mono
      (fun _ _ ⟨k, l, hp, _⟩ => ⟨k, l, hp⟩) (hinter a b w ha hb)


end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
