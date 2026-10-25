import Dubon2026.SourceOriginalCellPairingLiftVertices
import Dubon2026.SourceCoverLiftedMarkedCells
import Dubon2026.SourceOriginalCellPairingVertices

/-! DUB-17/18 -> cover Euler/cycle count -> actual vertex fibers.
The literal lifted vertex set is exactly the full inverse image of the
literal base vertex set. This uses exact projection of every endpoint and
exhaustion of every cell carrier, not an assumed vertex multiplicity. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable {X : Type*} [TopologicalSpace X]

theorem lifted_endpoint_projects (p : X → Place ℂ (modularFunctionFieldOver N ℂ))
    (J : ι → Type) (ζ : (i : ι) → J i → OpenPartialHomeomorph X ℂ)
    (hp : ∀ i j z, z ∈ (cell i).R.K → p ((ζ i j).symm z) = (cell i).ζ.symm z)
    (a : Σ i : ι, Fin (cell i).R.N) (j : J a.1) (b : Bool) :
    p (liftedEndpoint J (fun i j => (ζ i j).symm) ⟨a, j⟩ b) = endpoint a b := by
  cases b <;> exact hp a.1 j _ ((cell a.1).R.loop_mem_K _)

theorem lifted_vertices_eq_preimage (p : X → Place ℂ (modularFunctionFieldOver N ℂ))
    (J : ι → Type) (ζ : (i : ι) → J i → OpenPartialHomeomorph X ℂ)
    (hp : ∀ i j z, z ∈ (cell i).R.K → p ((ζ i j).symm z) = (cell i).ζ.symm z)
    (hx : ∀ i w, p w ∈ (cell i).carrier → ∃ j, w ∈ (ζ i j).symm '' (cell i).R.K) :
    LiftedVertex (cell := cell) J (fun i j => (ζ i j).symm) = p ⁻¹' Vertex (cell := cell) := by
  ext w
  constructor
  · rintro ⟨⟨⟨a, j⟩, b⟩, rfl⟩
    exact ⟨(a, b), (lifted_endpoint_projects p J ζ hp a j b).symm⟩
  · rintro ⟨⟨a, b⟩, he⟩
    have hbase : p w ∈ (cell a.1).carrier := by
      rw [← he]
      cases b <;> exact ⟨_, (cell a.1).R.loop_mem_K _, rfl⟩
    obtain ⟨j, hj⟩ := hx a.1 w hbase
    have hpoint : liftedEndpoint J (fun i j => (ζ i j).symm) ⟨a, j⟩ b ∈
        (ζ a.1 j).symm '' (cell a.1).R.K := by
      cases b <;> exact ⟨_, (cell a.1).R.loop_mem_K _, rfl⟩
    refine ⟨(⟨a, j⟩, b), ?_⟩
    exact SheetCover.lifted_carrier_injOn p (cell a.1).ζ (ζ a.1 j) (cell a.1).R
      (cell a.1).hKt (hp a.1 j) hpoint hj ((lifted_endpoint_projects p J ζ hp a j b).trans he)

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
