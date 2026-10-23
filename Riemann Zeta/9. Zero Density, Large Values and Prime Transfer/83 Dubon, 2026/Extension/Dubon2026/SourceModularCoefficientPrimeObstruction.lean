import Dubon2026.SourceModularCoefficientPolynomialDescent
import Dubon2026.SourceJPrimeNonpolynomial

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime nonmembership. The existing root-of-unity
orbit theorem already works in arbitrary characteristic once a nonzero
coefficient at a positive prime-multiple exponent is supplied. Polynomial
descent now makes it an obstruction to actual rational j membership.
The coefficient premise remains explicit and must be discharged in the
positive-characteristic arithmetic argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem prime_coefficient_obstructs_rational_j
    (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] (hpK : (p : K) ≠ 0)
    {m : ℕ} (hm : 0 < m) (hw : (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0) :
    qExpand K p (jqModC K) ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  intro hmem
  obtain ⟨Q, hQ⟩ := coefficient_j_polynomial_of_mem_rational p K hmem
  exact PrimeDegreeAux.aeval_jqModC_ne_jqNModC hpK hm hw Q hQ

end
end Dubon2026.SourceFunctionField
