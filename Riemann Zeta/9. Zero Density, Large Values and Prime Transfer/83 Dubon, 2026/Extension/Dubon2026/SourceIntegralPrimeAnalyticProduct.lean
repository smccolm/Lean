import Dubon2026.SourceIntegralPrimeConjugateProduct
import Dubon2026.SourcePrimeConjugateRealization
import Dubon2026.SourceAnalyticJTransformation

/-! Evaluate the existing exact integral modular polynomial as the full
analytic prime-Hecke product. The already proved Laurent conjugate product
and analytic coefficient realizations give the identity by uniqueness of
convergent sums. No new modular-polynomial construction or coefficient
descent is needed. This connects the actual odd quotient j-values to the
integral polynomial on the DUB-17/18 cyclic-root dependency chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial UpperHalfPlane

theorem realL_evalAtJ (P : Polynomial ℤ) :
    RealL 1 (coeffMap castC (evalAtJ P))
      (fun τ => P.eval₂ (Int.castRingHom ℂ) (JMultiplicity.jf τ)) := by
  have h := realL_aeval_jq (P.map (Int.castRingHom ℚ))
  have he : aeval jq (P.map (Int.castRingHom ℚ)) = evalAtJ P := by
    rw [aeval_def, eval₂_map]
    change eval₂ _ jq P = eval₂ _ jq P
    congr 1
    exact Subsingleton.elim _ _
  rw [he] at h
  refine h.congr rfl fun τ => ?_
  rw [Polynomial.map_map, Polynomial.eval_map]
  congr 1

theorem modularPolynomial_prime_analytic_product_of_root
    (p : ℕ) [Fact p.Prime] (ζ : (CyclotomicField p ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p) (τ : ℍ) :
    relationAtSeed (modularPolynomial p) (JMultiplicity.jf τ) =
      ∏ i : Fin (p + 1), (X - C (JMultiplicity.jf (rep p i • τ))) := by
  ext k
  have hprod := realL_phiProd_coeff p ζ hζ k
  rw [← modularPolynomial_prime_conjugate_product p ζ hζ,
    Polynomial.coeff_map, Polynomial.coeff_map] at hprod
  change RealL p (coeffMap (sigma p ζ hζ)
    (coeffEmb (CyclotomicField p ℚ) (qExpand ℚ p (evalAtJ ((modularPolynomial p).coeff k))))) _ at hprod
  rw [coeffMap_sigma_coeffEmb, coeffMap_qExpand] at hprod
  have hsum := realL_one_of_realL_qExpand p _ _ hprod
  have heq := (realL_evalAtJ ((modularPolynomial p).coeff k) τ).unique (hsum τ)
  simpa only [relationAtSeed, Polynomial.coeff_map,
    jt, JMultiplicity.jf] using heq

theorem modularPolynomial_prime_analytic_product (p : ℕ) [hp : Fact p.Prime] (τ : ℍ) :
    relationAtSeed (modularPolynomial p) (JMultiplicity.jf τ) =
      ∏ i : Fin (p + 1), (X - C (JMultiplicity.jf (rep p i • τ))) := by
  letI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField p ℚ)
    (Set.mem_singleton p) hp.out.ne_zero
  have hu := hz.isUnit hp.out.ne_zero
  exact modularPolynomial_prime_analytic_product_of_root p hu.unit
    (by simpa only [hu.unit_spec] using hz) τ

end Dubon2026.SourceFunctionField.IntegralJCoordinate
