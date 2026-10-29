import Dubon2026.SourceRationalLocalValuation
import Dubon2026.RationalPrimeFiniteTameGenerator

/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
realization -> actual good-prime Hecke stability. Compose the already
proved original local Frobenius existence with its valuation transport.
This removes a supplied decomposition/Frobenius witness from the original
Gamma1 quotient consumer; it introduces no local arithmetic hypothesis. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

theorem sourceRationalLocalValuation_exists_frobenius (q : ℕ) (hq : q.Prime)
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq) :
    ∃ d : (sourceRationalLocalValuation q hq e).decompositionSubgroup ℚ,
      ∀ z : IsLocalRing.ResidueField (sourceRationalLocalValuation q hq e),
        d • z = z ^ q := by
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius q hq
  obtain ⟨hd, hres⟩ := sourceRationalLocalValuation_frobenius q hq e φ hφ
  exact ⟨⟨embeddedNormalGaloisRestriction e φ, hd⟩, hres⟩

end
end Dubon2026
