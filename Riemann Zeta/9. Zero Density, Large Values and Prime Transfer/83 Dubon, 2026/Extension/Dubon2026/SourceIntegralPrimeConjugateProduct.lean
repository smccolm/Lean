import Dubon2026.SourceExactIntegralModularPolynomial
import Dubon2026.SourcePrimeBidirectionalRelation

/-! The previously constructed prime conjugate product is the actual integral
minimal polynomial. Native integrally closed divisibility and the proved exact
degree identify the two without a new polynomial-data structure or a symmetry
assumption. This removes the identification input in the degree-two explicit
polynomial comparison, required for the cyclic-quotient root interpretation,
finite inertia census and good reduction on the DUB-17 / DUB-18 chain. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial

theorem eq_modularPolynomial_of_monic_root_degree (N : ℕ) [NeZero N]
    (P : Polynomial (Polynomial ℤ)) (hPm : P.Monic)
    (hP : P.eval₂ evalAtJ (qExpand ℚ N jq) = 0)
    (hdeg : P.natDegree ≤ SourceLevelProjective.dedekindPsi N) :
    P = modularPolynomial N := by
  haveI : Module.IsTorsionFree ℤ[X] (LaurentSeries ℚ) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro A B hAB
      apply evaluate_injective
      apply (algebraMap J (LaurentSeries ℚ)).injective
      simpa only [algebraMap_evaluate] using hAB)
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (modularPolynomial_monic N) hPm
  · exact minpoly.isIntegrallyClosed_dvd (level_integral_over_int_polynomial N) hP
  · rwa [modularPolynomial_natDegree]

theorem modularPolynomial_prime_natDegree (p : ℕ) [hp : Fact p.Prime] :
    (modularPolynomial p).natDegree = p + 1 := by
  rw [modularPolynomial_natDegree]
  simpa using SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out (by decide)

theorem modularPolynomial_prime_conjugate_product (p : ℕ) [Fact p.Prime]
    (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p) :
    (modularPolynomial p).map
      (((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ) := by
  obtain ⟨P, hPm, hdeg, hprod⟩ := exists_prime_monic_degree_product p ζ hζ
  have hroot := prime_product_forward_root p _ ζ P hprod
  have heq := eq_modularPolynomial_of_monic_root_degree p P hPm hroot (by
    rw [← modularPolynomial_natDegree, modularPolynomial_prime_natDegree, hdeg])
  rwa [heq] at hprod

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
