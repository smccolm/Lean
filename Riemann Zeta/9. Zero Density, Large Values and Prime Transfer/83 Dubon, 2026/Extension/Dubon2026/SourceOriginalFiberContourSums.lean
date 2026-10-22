import Dubon2026.SourceOriginalFiberIndexing

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> constancy of the exact weighted fiber contour. These
functions are the literal contour sums on the actual original chart disks.
Their comparison, derivative and vanishing are proved separately under
the existing limits, retaining the exact coefficients and multiplicities.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential ComplexFiberContour
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

/-- The weighted contour expression for the actual Abel-Jacobi fiber sum. -/
def originalFiberContourSum {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) (j : OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z) (t : ℂ) : Fin n → ℂ :=
  let k : ℂ := (2 * Real.pi * Complex.I)⁻¹
  ∑ v ∈ Z₀,
    ((k * ∮ z in C((0 : ℂ), j.r v),
      (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) •
        (abelJacobiVec N bb P₀ v - fun i => j.Φ v i 0) +
      k • fun i => ∮ z in C((0 : ℂ), j.r v),
        j.Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t))

/-- The differentiated contour expression, prior to proving its vanishing. -/
def originalFiberContourDerivative {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) (j : OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z) (t : ℂ) : Fin n → ℂ :=
  let k : ℂ := (2 * Real.pi * Complex.I)⁻¹
  ∑ v ∈ Z₀,
    ((k * ∮ z in C((0 : ℂ), j.r v),
      deriv (fun _ => (1 : ℂ)) z / (chartRead N v f z - t)) •
        (abelJacobiVec N bb P₀ v - fun i => j.Φ v i 0) +
      k • fun i => ∮ z in C((0 : ℂ), j.r v),
        deriv (j.Φ v i) z / (chartRead N v f z - t))

end
end Dubon2026.SourceFunctionField.OriginalChart
