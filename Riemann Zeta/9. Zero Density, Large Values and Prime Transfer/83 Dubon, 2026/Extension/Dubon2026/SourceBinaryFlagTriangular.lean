import Dubon2026.SourceBinaryCoefficientFlag

/-! Actual upper triangular action on the residual coefficient flag.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> the original coefficient flag -> its group and Hecke invariant steps and
their explicit one-dimensional quotient characters.

The coefficient calculation adapts the flag proof in
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd.lean
(Apache-2.0; retained LICENSE and NOTICE), reusing the actual local matrix
polynomial action.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial

variable {R : Type} [CommRing R]

private theorem upper_monomial (M : Matrix (Fin 2) (Fin 2) R) (h10 : M 1 0 = 0)
    (m : Fin 2 →₀ ℕ) (r : R) :
    matrixPolynomialAction M (monomial m r) =
      monomial (Finsupp.single 0 (m 0)) (r * M 0 0 ^ (m 0)) *
        (C (M 0 1) * X 0 + C (M 1 1) * X 1) ^ (m 1) := by
  rw [matrixPolynomialAction, aeval_monomial,
    Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, h10, zero_smul, add_zero]
  simp only [smul_eq_C_mul]
  rw [MvPolynomial.algebraMap_eq, mul_pow, ← C_pow, monomial_eq]
  have hx : ((Finsupp.single (0 : Fin 2) (m 0)).prod
      fun i e => (X i : MvPolynomial (Fin 2) R) ^ e) = X 0 ^ (m 0) := by
    rw [Finsupp.prod_single_index]
    exact pow_zero _
  rw [hx, C_mul]
  ring

private theorem coefficient_below_monomial {j : ℕ} (r : R)
    (P : MvPolynomial (Fin 2) R) {m : Fin 2 →₀ ℕ} (hm : m 0 < j) :
    coeff m (monomial (Finsupp.single 0 j) r * P) = 0 := by
  rw [coeff_monomial_mul', if_neg]
  intro h
  have he := h 0
  rw [Finsupp.single_eq_same] at he
  omega

/-- The original upper triangular polynomial action preserves every actual
coefficient-flag step. -/
theorem sourceBinaryCoefficientFlag_upper_stable (n j : ℕ)
    (M : Matrix (Fin 2) (Fin 2) R) (h10 : M 1 0 = 0)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    homogeneousMatrixAction n M P ∈ sourceBinaryCoefficientFlag R n j := by
  intro m hm
  change coeff m (matrixPolynomialAction M P.val) = 0
  conv_lhs => rw [P.val.as_sum, map_sum]
  rw [coeff_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hd0 : j ≤ d 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hP d (by omega))
  rw [upper_monomial M h10]
  exact coefficient_below_monomial _ _ (lt_of_lt_of_le hm hd0)

private theorem coefficient_last_linear_pow (a b : R) (k : ℕ) :
    coeff (Finsupp.single 1 k) ((C a * X 0 + C b * X 1) ^ k : MvPolynomial (Fin 2) R) =
      b ^ k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', add_mul, coeff_add, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul,
      coeff_X_mul', coeff_X_mul']
    have h0 : (0 : Fin 2) ∉ (Finsupp.single (1 : Fin 2) (k + 1)).support := by
      rw [Finsupp.support_single _ (Nat.succ_ne_zero k)]
      simp
    have h1 : (1 : Fin 2) ∈ (Finsupp.single (1 : Fin 2) (k + 1)).support := by
      rw [Finsupp.support_single _ (Nat.succ_ne_zero k)]
      simp
    rw [if_neg h0, if_pos h1, mul_zero, zero_add,
      show Finsupp.single (1 : Fin 2) (k + 1) - Finsupp.single 1 1 = Finsupp.single 1 k by
        rw [← Finsupp.single_tsub]; rfl,
      ih, pow_succ']

/-- The actual upper triangular action on the j-th coefficient quotient is
the explicit diagonal character a^j d^(n-j). -/
theorem sourceBinaryFlagGraded_upper (n j : ℕ)
    (M : Matrix (Fin 2) (Fin 2) R) (h10 : M 1 0 = 0)
    (P : homogeneousSubmodule (Fin 2) R n) (hP : P ∈ sourceBinaryCoefficientFlag R n j) :
    coeff (sourceBinaryFlagExponent n j) (homogeneousMatrixAction n M P).val =
      M 0 0 ^ j * M 1 1 ^ (n - j) * coeff (sourceBinaryFlagExponent n j) P.val := by
  classical
  change coeff _ (matrixPolynomialAction M P.val) = _
  conv_lhs => rw [P.val.as_sum, map_sum]
  rw [coeff_sum]
  have hterm : ∀ d ∈ P.val.support, d ≠ sourceBinaryFlagExponent n j →
      coeff (sourceBinaryFlagExponent n j)
        (matrixPolynomialAction M (monomial d (coeff d P.val))) = 0 := by
    intro d hd hne
    have hd0 : j ≤ d 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hd) (hP d (by omega))
    have hdeg : d 0 + d 1 = n := by
      have he : d.degree = n := by
        by_contra h
        exact (MvPolynomial.mem_support_iff.mp hd) (P.property.coeff_eq_zero h)
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using he
    have hlt : j < d 0 := by
      refine lt_of_le_of_ne hd0 fun h => hne ?_
      ext i
      fin_cases i
      · simp [sourceBinaryFlagExponent, h]
      · simpa [sourceBinaryFlagExponent] using (show d 1 = n - j by omega)
    rw [upper_monomial M h10]
    exact coefficient_below_monomial _ _ (by rwa [sourceBinaryFlagExponent_zero])
  rw [Finset.sum_eq_single (sourceBinaryFlagExponent n j) (fun d hd hne => hterm d hd hne)
    (fun h => by rw [MvPolynomial.notMem_support_iff.mp h, map_zero, map_zero, coeff_zero])]
  rw [upper_monomial M h10, coeff_monomial_mul', if_pos (by
      intro i; fin_cases i <;> simp [sourceBinaryFlagExponent]),
    show sourceBinaryFlagExponent n j - Finsupp.single 0 (sourceBinaryFlagExponent n j 0) =
      Finsupp.single 1 (n - j) by
        ext i; fin_cases i <;> simp [sourceBinaryFlagExponent],
    sourceBinaryFlagExponent_zero, sourceBinaryFlagExponent_one, coefficient_last_linear_pow]
  ring

end
end Dubon2026
