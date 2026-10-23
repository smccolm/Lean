import Dubon2026.SourcePrimeJPositiveCharacteristic
import Dubon2026.SourceModularCoefficientPolynomialDescent
import Dubon2026.SourceJPrimeNonpolynomial
import Mathlib.Algebra.CharP.Algebra

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
exact modular field degree. The prime nonmembership input is proved for
every coefficient field and every prime nonzero in that field. Positive
characteristic ascends to the algebraic closure and uses the proved Hasse,
norm and eta contradiction; characteristic zero reuses the existing proof.
There is no nonzero Fourier coefficient, Hasse, norm, root-count, or prime
nonmembership assumption in the final theorem. Exact extension degree and
good reduction remain subsequent mathematical obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem prime_j_not_mem_rational_j_of_ne_char
    (K : Type*) [Field K] {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    [CharP K ℓ] (hpℓ : p ≠ ℓ) :
    qExpand K p (jqModC K) ∉
      IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  intro hmem
  obtain ⟨R, hR⟩ := coefficient_j_polynomial_of_mem_rational p K hmem
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hmap : Polynomial.aeval (jqModC (AlgebraicClosure K))
      (R.map (algebraMap K (AlgebraicClosure K))) = jqNModC (AlgebraicClosure K) p := by
    rw [← PrimeDegreeAux.coeffMap_aeval_jqModC, hR, coeffMap_qExpand]
    change qExpand (AlgebraicClosure K) p
      ((jqModC K).map (algebraMap K (AlgebraicClosure K))) = _
    rw [map_jqModC]
    rfl
  exact prime_j_polynomial_impossible_closed hpℓ hmap

theorem prime_j_not_mem_rational_j_away_characteristic
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] (hpK : (p : K) ≠ 0) :
    qExpand K p (jqModC K) ∉
      IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K ℓ with hprime | rfl
  · haveI : Fact ℓ.Prime := ⟨hprime⟩
    apply prime_j_not_mem_rational_j_of_ne_char K (ℓ := ℓ)
    intro h
    exact hpK (h ▸ CharP.cast_eq_zero K ℓ)
  · haveI : CharZero K := CharP.charP_to_charZero K
    intro hmem
    obtain ⟨R, hR⟩ := coefficient_j_polynomial_of_mem_rational p K hmem
    exact PrimeDegreeAux.aeval_jqModC_ne_jqNModC_charZero p R hR

end
end Dubon2026.SourceFunctionField
