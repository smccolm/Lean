import Dubon2026.SourceOriginalWeilCoverTwoPoleDimensions
import Dubon2026.SourceCurveTwoPoleDifferential

/-! DUB-17/18 -> cover Abel converse -> prescribed third-kind residues.
The native dimension and local-order deductions consume the actual cover
Riemann-Roch identity and canonical differential orders. Both poles are
exactly simple and the differential is regular at every other place. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

theorem exists_cover_two_pole_function {ω₀ : Ω[EE⁄ℂ]} (hω₀ : ω₀ ≠ 0)
    (P Q : Place ℂ EE) :
    let K₀ := coverCanonicalDivisor N n r hω₀
    ∃ h ∈ LSpace (K₀ + Finsupp.single P 1 + Finsupp.single Q 1),
      h ∉ LSpace (K₀ + Finsupp.single P 1) ∧ h ∉ LSpace (K₀ + Finsupp.single Q 1) := by
  have hdim := cover_two_pole_dimensions N n r (ω₀ := ω₀) hω₀ P Q
  exact exists_two_pole_function_of_dimensions (F := EE)
    (coverCanonicalDivisor N n r hω₀) P Q hdim

theorem exists_cover_two_pole_differential {P Q : Place ℂ EE} (hPQ : P ≠ Q) :
    ∃ ω : Ω[EE⁄ℂ], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place ℂ EE, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by
  letI : ∀ v : Place ℂ EE, v.DCoordGenerates := cover_place_dCoordGenerates N n r
  letI := cover_differentials_nontrivial N n r
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[EE⁄ℂ])
  have hfun := exists_cover_two_pole_function N n r (ω₀ := ω₀) hω₀ P Q
  exact exists_two_pole_differential_of_function (F := EE) hω₀
    (coverCanonicalDivisor N n r hω₀) (coverCanonicalDivisor_apply N n r hω₀) hPQ hfun

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
