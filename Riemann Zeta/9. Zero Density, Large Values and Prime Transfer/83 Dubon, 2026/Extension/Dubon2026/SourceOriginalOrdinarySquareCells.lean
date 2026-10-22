import Dubon2026.SourceOriginalOrdinarySquareSheets
import Dubon2026.SourceCellSixArcBoundary
import Dubon2026.SourceOriginalAnalyticCells

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Actual analytic j sheets and the constructed six-arc radial rectangle produce
all ordinary original-place cells. Their carriers cover exactly the original
j preimage of the closed square and are pairwise disjoint within that square.
The full source side, endpoint, branch and segment geometry is retained.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The full geometric output of the source six-arc rectangle construction. -/
def RectSixArcs.RectangleGeometry (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (R : RadialRegion) : Prop :=
      R.q = p ∧ R.N = 6 ∧
      R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
      (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
      (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ R.K, z ∉ R.Kint →
        R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
          = z) ∧
      (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
        R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂))

theorem Cell.mem_carrier_iff_coordinate (C : Cell N) (P : Place ℂ F) :
    P ∈ C.carrier ↔ P ∈ C.ζ.source ∧ C.ζ P ∈ C.R.K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨C.ζ.map_target (C.hKt hz), (C.ζ.right_inv (C.hKt hz)).symm ▸ hz⟩
  · rintro ⟨hP, hz⟩
    exact ⟨C.ζ P, hz, C.ζ.left_inv hP⟩

theorem exists_original_ordinary_square_cells (N : ℕ) [NeZero N] {o h : ℝ}
    (hh : 0 < h) (j k : ℤ) (p : ℂ) (yL : ℝ)
    (hx₀ : o + j * h < p.re) (hx₁ : p.re < o + (j + 1) * h)
    (hy₀ : o + k * h < p.im) (hy₁ : p.im < o + (k + 1) * h)
    (hL₀ : o + k * h < yL) (hL₁ : yL < o + (k + 1) * h)
    (h0 : (0 : ℂ) ∉ SquareGrid.gridSquare o h j k)
    (h1728 : (1728 : ℂ) ∉ SquareGrid.gridSquare o h j k) :
    ∃ (V : Set ℂ) (R : RadialRegion)
      (C : Fin (SourceLevelProjective.dedekindPsi N) → Cell N),
      IsOpen V ∧ SquareGrid.gridSquare o h j k ⊆ V ∧
      (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
      RectSixArcs.RectangleGeometry (o + j * h) (o + (j + 1) * h)
        (o + k * h) (o + (k + 1) * h) p yL R ∧
      (∀ i, (C i).R = R) ∧
      IsOriginalSheetFamily (jOver N ℂ) V (fun i => (C i).ζ) ∧
      (∀ P : Place ℂ (modularFunctionFieldOver N ℂ),
        (jOver N ℂ ∈ P.toValuationSubring ∧
          originalPlaceEval N ℂ P (jOver N ℂ) ∈ SquareGrid.gridSquare o h j k) ↔
          ∃ i, P ∈ (C i).carrier) ∧
      Pairwise (fun i i' => Disjoint (C i).carrier (C i').carrier) := by
  obtain ⟨V, A, hV, hQV, hV0, hV1728, hA⟩ := exists_original_j_ordinary_square_sheets N hh j k h0 h1728
  obtain ⟨R, hR⟩ := RectSixArcs.exists_rect_sixArcs (o + j * h) (o + (j + 1) * h)
    (o + k * h) (o + (k + 1) * h) p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁
  have hRK : R.K = SquareGrid.gridSquare o h j k := hR.2.2.1
  let C : Fin (SourceLevelProjective.dedekindPsi N) → Cell N := fun i =>
    { toAnalyticCoord := A i
      R := R
      hKt := by rw [hA.1 i, hRK]; exact hQV }
  have hcoord (i) (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
      P ∈ (C i).carrier ↔ P ∈ (A i).ζ.source ∧ (A i).ζ P ∈ R.K :=
    (C i).mem_carrier_iff_coordinate P
  refine ⟨V, R, C, hV, hQV, hV0, hV1728, hR, fun _ => rfl, hA, ?_, ?_⟩
  · intro P
    constructor
    · rintro ⟨hreg, hP⟩
      obtain ⟨i, hi⟩ := hA.2.2.2 P hreg (hQV hP)
      refine ⟨i, (hcoord i P).mpr ⟨hi, ?_⟩⟩
      rw [hRK, (hA.2.1 i P hi).2]
      exact hP
    · rintro ⟨i, hi⟩
      obtain ⟨hsrc, hval⟩ := (hcoord i P).mp hi
      obtain ⟨hreg, he⟩ := hA.2.1 i P hsrc
      rw [hRK, he] at hval
      exact ⟨hreg, hval⟩
  · intro i i' hii'
    exact (hA.2.2.1 hii').mono (fun P hP => ((hcoord i P).mp hP).1)
      (fun P hP => ((hcoord i' P).mp hP).1)

end
end Dubon2026.SourceFunctionField.CellGeometry
