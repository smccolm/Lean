import Dubon2026.BohrLift

/-! # Absence of integer resonances among the prime logarithms -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

theorem primeCoordinate_prime {N : ℕ} (p : PrimeCoordinate N) : p.val.Prime :=
  (mem_primesUpTo.mp p.property).1

theorem prime_coordinate_product_ne_zero {N : ℕ} (e : PrimeCoordinate N → ℕ) :
    (∏ p : PrimeCoordinate N, p.val ^ e p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact pow_ne_zero _ (primeCoordinate_prime p).ne_zero

theorem factorization_prime_coordinate_product {N : ℕ}
    (e : PrimeCoordinate N → ℕ) (q : PrimeCoordinate N) :
    (∏ p : PrimeCoordinate N, p.val ^ e p).factorization q.val = e q := by
  classical
  rw [Nat.factorization_prod (fun p _ => pow_ne_zero (e p) (primeCoordinate_prime p).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  have hterm (p : PrimeCoordinate N) :
      (p.val ^ e p).factorization q.val = if p = q then e p else 0 := by
    rw [(primeCoordinate_prime p).factorization_pow, Finsupp.single_apply]
    simp only [Subtype.val_inj]
  simp only [hterm]
  simp

theorem log_prime_coordinate_product {N : ℕ} (e : PrimeCoordinate N → ℕ) :
    Real.log (∏ p : PrimeCoordinate N, (p.val : ℝ) ^ e p) =
      ∑ p : PrimeCoordinate N, (e p : ℝ) * Real.log p.val := by
  rw [Real.log_prod]
  · simp only [Real.log_pow]
  · intro p _
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (primeCoordinate_prime p).ne_zero)

theorem prime_log_integer_independent {N : ℕ} (k : PrimeCoordinate N → ℤ)
    (h : (∑ p : PrimeCoordinate N, (k p : ℝ) * Real.log p.val) = 0) :
    ∀ p, k p = 0 := by
  classical
  let A : ℕ := ∏ p : PrimeCoordinate N, p.val ^ (k p).toNat
  let B : ℕ := ∏ p : PrimeCoordinate N, p.val ^ (-k p).toNat
  have hA : A ≠ 0 := prime_coordinate_product_ne_zero _
  have hB : B ≠ 0 := prime_coordinate_product_ne_zero _
  have hsplit (p : PrimeCoordinate N) :
      ((k p).toNat : ℝ) - ((-k p).toNat : ℝ) = (k p : ℝ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (k p)
  have hlogs : Real.log (A : ℝ) - Real.log (B : ℝ) = 0 := by
    dsimp only [A, B]
    simp only [Nat.cast_prod, Nat.cast_pow]
    rw [log_prime_coordinate_product, log_prime_coordinate_product, ← Finset.sum_sub_distrib]
    simpa only [← sub_mul, hsplit] using h
  have hAB : A = B := by
    have hposA : (A : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < A
      exact_mod_cast Nat.pos_of_ne_zero hA
    have hposB : (B : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < B
      exact_mod_cast Nat.pos_of_ne_zero hB
    exact_mod_cast Real.log_injOn_pos hposA hposB (sub_eq_zero.mp hlogs)
  intro p
  have hval := congrArg (fun n : ℕ => n.factorization p.val) hAB
  dsimp only [A, B] at hval
  rw [factorization_prime_coordinate_product, factorization_prime_coordinate_product] at hval
  omega

end

end Dubon2026
