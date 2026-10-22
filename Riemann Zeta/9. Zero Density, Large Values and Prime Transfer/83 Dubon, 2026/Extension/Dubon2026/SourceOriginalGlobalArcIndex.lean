import Dubon2026.SourceOriginalExteriorArcImages

/-! DUB-17/18 -> original Abel-Jacobi -> the actual paired cell family.
Assign each constructed original cell its planar square or exterior region.
Use the proved planar Shares relation directly, retaining its exact side
incidence and intersection-chain semantics.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

/-- A lifted original-place set has regular j values and maps onto the whole planar set. -/
def LiesOver (L : Set (Place ℂ (modularFunctionFieldOver N ℂ))) (Z : Set ℂ) : Prop :=
  (∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ Z) ∧
    Z ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L

theorem LiesOver.of_image_eq {L : Set (Place ℂ (modularFunctionFieldOver N ℂ))} {Z : Set ℂ}
    (hr : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring)
    (he : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L = Z) : LiesOver L Z := by
  refine ⟨fun P hP => ⟨hr P hP, he ▸ mem_image_of_mem _ hP⟩, ?_⟩
  rw [he]

theorem LiesOver.eq {L : Set (Place ℂ (modularFunctionFieldOver N ℂ))} {Z Z' : Set ℂ}
    (h : LiesOver L Z) (h' : LiesOver L Z') : Z = Z' := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨P, hP, rfl⟩ := h.2 hz
    exact (h'.1 P hP).2
  · intro z hz
    obtain ⟨P, hP, rfl⟩ := h'.2 hz
    exact (h.1 P hP).2

namespace OriginalGlobalCellCover
variable {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The planar region below one actual cell; none denotes the exterior. -/
def regionOf : A.Index → Option (ℤ × ℤ)
  | .inl (.inl p) => some p.1.1.1
  | .inl (.inr p) => some (A.G.branchSquare p.1)
  | .inr _ => none

/-- A boundary arc of a specified actual cell of the global cover. -/
abbrev Arc := Σ i : A.Index, Fin (A.cell i).R.N

/-- The actual set of original places on a globally indexed boundary arc. -/
def arcPlaces (a : A.Arc) : Set (Place ℂ (modularFunctionFieldOver N ℂ)) := (A.cell a.1).arc a.2

/-- The exact proved planar side-incidence relation on the constructed grid. -/
abbrev Shares := StarProperty.Shares A.planarData

theorem branch_region_center (p : ℤ × ℤ) (b : ℂ) (hp : A.G.D.capAt p = some b) :
    (A.G.region p).q = b := by
  apply (A.G.rectangle p).1.trans
  apply A.G.D.cap_center _ hp
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  tauto

theorem regionOf_mem_window (i : A.Index) {p : ℤ × ℤ} (h : A.regionOf i = some p) :
    p ∈ Icc A.G.D.lo A.G.D.hi ×ˢ Icc A.G.D.lo A.G.D.hi := by
  have hp : p ∈ A.G.squares := by
    cases i with
    | inl i =>
      cases i with
      | inl q =>
        have he : q.1.1.1 = p := Option.some.inj h
        exact he ▸ q.1.1.2
      | inr q =>
        have he : A.G.branchSquare q.1 = p := Option.some.inj h
        exact he ▸ A.G.branchSquare_mem q.1
    | inr v => cases h
  obtain ⟨hj, hk⟩ := Finset.mem_product.mp hp
  exact ⟨Finset.mem_Icc.mp hj, Finset.mem_Icc.mp hk⟩

end OriginalGlobalCellCover
end
end Dubon2026.SourceFunctionField.CellGeometry
