import Dubon2026.SourceOriginalWeilCoverJacobiInversion

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
Construct the finite basis of the actual cover's regular differentials,
then apply the proved inversion theorem to that same basis. No finite
dimensionality, basis, frame or local-surjectivity hypothesis is supplied.
The principal-divisor converse remains required before dividing classes. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

/-- A basis of the actual finite-dimensional space of regular cover differentials. -/
def coverRegularBasis : Module.Basis (Fin (Module.finrank ℂ (regularDifferentials ℂ EE)))
    ℂ (regularDifferentials ℂ EE) := by
  letI := finite_cover_regularDifferentials N n r
  exact Module.finBasis ℂ (regularDifferentials ℂ EE)

variable [NeZero n]
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)

theorem exists_cover_jacobi_divisor (P₀ : Place ℂ EE)
    (u : Fin (Module.finrank ℂ (regularDifferentials ℂ EE)) → ℂ) :
    ∃ D : Divisor ℂ EE, Divisor.degree D = 0 ∧
      abelJacobiDiv N n r A hr hrA (fun i => (coverRegularBasis N n r i : Ω[EE⁄ℂ])) P₀ D - u ∈
        pathPeriodLattice N n r A hr hrA (fun i => (coverRegularBasis N n r i : Ω[EE⁄ℂ])) :=
  cover_jacobi_inversion N n r A hr hrA (coverRegularBasis N n r) P₀ u

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
