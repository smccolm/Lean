import Dubon2026.GeneralLinearIntegralDeterminantTwist

/-! Multiplication of literal source induced regular functions adds their
original Borel weights. Natural powers and finite products serve the
explicit dominant-weight vector, using the already proved determinant
twist for the possibly negative constant weight.
-/

namespace Dubon2026
noncomputable section

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- Pointwise addition of the original integral tuples multiplies their exact reversed-Borel characters. -/
theorem generalLinearBorelWeight_add (lam mu : Fin n → ℤ) (b : generalLinearBorel R n) :
    generalLinearBorelWeight (fun i => lam i + mu i) b =
      generalLinearBorelWeight lam b * generalLinearBorelWeight mu b := by
  simp only [generalLinearBorelWeight_apply, zpow_add, Finset.prod_mul_distrib]

/-- A natural multiple of the original integral tuple gives the corresponding natural power of its exact character. -/
theorem generalLinearBorelWeight_nat_mul (lam : Fin n → ℤ) (a : ℕ)
    (b : generalLinearBorel R n) :
    generalLinearBorelWeight (fun i => (a : ℤ) * lam i) b =
      generalLinearBorelWeight lam b ^ a := by
  simp only [generalLinearBorelWeight_apply]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm (a : ℤ), zpow_mul, zpow_natCast]

/-- Finite sums of the original weight tuples give the actual finite product of source characters. -/
theorem generalLinearBorelWeight_sum {J : Type*} (s : Finset J)
    (lam : J → Fin n → ℤ) (b : generalLinearBorel R n) :
    generalLinearBorelWeight (fun i => ∑ j ∈ s, lam j i) b =
      ∏ j ∈ s, generalLinearBorelWeight (lam j) b := by
  classical
  induction s using Finset.induction with
  | empty => simp [generalLinearBorelWeight_apply]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [generalLinearBorelWeight_add, ih]

/-- Taking a natural power of an actual induced regular function multiplies the original weight by that natural number. -/
theorem generalLinearIntegralInduced_pow (lam : Fin n → ℤ) (a : ℕ)
    {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam) :
    p ^ a ∈ generalLinearIntegralInducedSubmodule R n (fun i => (a : ℤ) * lam i) := by
  intro A _ _ g b
  simp only [map_pow, hp A g b, generalLinearBorelWeight_nat_mul,
    Units.val_pow_eq_pow_val, mul_pow]

/-- Finite products of actual induced regular functions lie in the exact source module for the sum of their original weights. -/
theorem generalLinearIntegralInduced_prod {J : Type*} (s : Finset J)
    (lam : J → Fin n → ℤ) (p : J → GeneralLinearRegularFunctions R n)
    (hp : ∀ j ∈ s, p j ∈ generalLinearIntegralInducedSubmodule R n (lam j)) :
    (∏ j ∈ s, p j) ∈ generalLinearIntegralInducedSubmodule R n (fun i => ∑ j ∈ s, lam j i) := by
  intro A _ _ g b
  simp only [map_prod, generalLinearBorelWeight_sum, Units.coe_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact hp j hj A g b

end
end Dubon2026
