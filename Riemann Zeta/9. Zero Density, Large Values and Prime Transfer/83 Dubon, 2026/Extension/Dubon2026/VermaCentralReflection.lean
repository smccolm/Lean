import Dubon2026.VermaSingularEmbedding
import Mathlib.Algebra.Polynomial.Roots

/-! # Genuine reflection symmetry of the full original polynomial central character -/

namespace Dubon2026

noncomputable section
open Polynomial

/-- The actual singular polynomial embedding forces equality of every original central scalar at the natural reflected pair n and -n-2. -/
theorem vermaPolynomialCentralValue_nat_reflection (n : ℕ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaPolynomialCentralValue (n : ℂ) z = vermaPolynomialCentralValue (-(n : ℂ) - 2) z := by
  have he := vermaSingular_enveloping (R := ℂ) n z.val 1
  rw [mul_one, vermaPolynomialCentralValue_X_pow, vermaPolynomialCentralValue_generator,
    mul_smul_comm, mul_one] at he
  exact (smul_left_injective ℂ (pow_ne_zero (n + 1) (X_ne_zero : (X : ℂ[X]) ≠ 0))) he

/-- Infinitely many genuine singular embeddings force reflection symmetry of the entire original universal central polynomial. -/
theorem vermaUniversalCentralPolynomial_reflection
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaUniversalCentralPolynomial z = (vermaUniversalCentralPolynomial z).comp (-X - C 2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro _ ⟨n, rfl⟩
  change eval (n : ℂ) (vermaUniversalCentralPolynomial z) =
    eval (n : ℂ) ((vermaUniversalCentralPolynomial z).comp (-X - C 2))
  rw [eval_comp, eval_sub, eval_neg, eval_X, eval_C]
  have hpos := vermaUniversalCentralPolynomial_aeval (n : ℂ) z
  have hneg := vermaUniversalCentralPolynomial_aeval (-(n : ℂ) - 2) z
  rw [coe_aeval_eq_eval] at hpos hneg
  exact hpos.trans ((vermaPolynomialCentralValue_nat_reflection n z).trans hneg.symm)

/-- The genuine full central scalar is invariant under μ ↦ -μ-2 at every complex highest weight. -/
theorem vermaPolynomialCentralValue_reflection (μ : ℂ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaPolynomialCentralValue μ z = vermaPolynomialCentralValue (-μ - 2) z := by
  have he := congrArg (eval μ) (vermaUniversalCentralPolynomial_reflection z)
  rw [eval_comp, eval_sub, eval_neg, eval_X, eval_C] at he
  have hpos := vermaUniversalCentralPolynomial_aeval μ z
  have hneg := vermaUniversalCentralPolynomial_aeval (-μ - 2) z
  rw [coe_aeval_eq_eval] at hpos hneg
  exact hpos.symm.trans (he.trans hneg)

/-- The genuine entire central character at the cusp highest-weight parameter -k equals its algebraic reflected parameter k-2. -/
theorem vermaPolynomialCentralValue_cusp_reflection (k : ℤ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaPolynomialCentralValue (-(k : ℂ)) z = vermaPolynomialCentralValue ((k : ℂ) - 2) z := by
  simpa only [neg_neg] using vermaPolynomialCentralValue_reflection (-(k : ℂ)) z

end
end Dubon2026
