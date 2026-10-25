import Dubon2026.SourceAnalyticCoordinateInverse
import Dubon2026.SourceOriginalWeilCoverManifold

/-! DUB-17/18 -> cover reciprocity -> cell coefficient calculus.
The lifted cell coordinates are already proved analytic with nonzero
derivative in the actual cover parameter. The local inverse theorem supplies
the inverse analyticity and exact derivative needed for edge integrals and
cell primitives. No inverse-calculus premise is introduced. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_coordinate_inverse :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders Q) 0 →
      deriv (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders Q) 0 ≠ 0 →
      AnalyticAt ℂ (placeChart N n radicand baseDivisor hRadicand hOrders Q ∘ ζ.symm) (ζ Q) ∧
      HasDerivAt (placeChart N n radicand baseDivisor hRadicand hOrders Q ∘ ζ.symm)
        (deriv (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders Q) 0)⁻¹ (ζ Q) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd
  let φ : OpenPartialHomeomorph (Place ℂ EE) ℂ :=
    (placeCore N n radicand baseDivisor hRadicand hOrders).openPartialHomeomorph
      (placeChart N n radicand baseDivisor hRadicand hOrders Q) ⟨Q, rfl⟩
  have hφQ : Q ∈ φ.source := mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q
  have hφ0 : φ Q = 0 := placeChart_self N n radicand baseDivisor hRadicand hOrders Q
  have ha' : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q) := by rw [hφ0]; exact ha
  have hd' : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0 := by rw [hφ0]; exact hd
  have hlocal := SheetCover.coordinate_local_inverse φ ζ hφQ hQ ha' hd'
  have hinv := (hlocal.2.1.self_of_nhds).2.2
  rw [ζ.left_inv hQ, hφ0] at hinv
  exact ⟨SheetCover.analyticAt_coordinate_inverse φ ζ hφQ hQ ha' hd', hinv⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
