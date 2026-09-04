import GafniTao.WooleyBinomialMatrix
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor coefficients in Wooley equation (7.10)

This is the exact algebra behind the integers `Ω_il` in Section 7.  For a
normal-form polynomial `X^j + p^c X^(k+1) ψ`, its coefficient of `X^i`
after translation by `h` factors as `h^(j-i) Ω`, and `Ω` is congruent to
`choose j i` modulo `p^c`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The translated polynomial with its constant term removed. -/
def wooleyTaylorDifference (h : ℤ) (f : Polynomial ℤ) : Polynomial ℤ :=
  taylor h f - C (f.eval h)

theorem wooleyTaylorDifference_coeff_zero (h : ℤ) (f : Polynomial ℤ) :
    (wooleyTaylorDifference h f).coeff 0 = 0 := by
  simp [wooleyTaylorDifference]

/-- Exact Taylor truncation at degree `r`: no asymptotic remainder and no
unspecified polynomial. -/
theorem wooleyTaylorDifference_eq_low_sum_add_tail
    (r : ℕ) (h : ℤ) (f : Polynomial ℤ) :
    wooleyTaylorDifference h f =
      ∑ i : Fin r,
        C ((wooleyTaylorDifference h f).coeff ((i : ℕ) + 1)) *
          X ^ ((i : ℕ) + 1) +
      X ^ (r + 1) *
        wooleyPolynomialTail (r + 1) (wooleyTaylorDifference h f) := by
  let g := wooleyTaylorDifference h f
  have hdeg :
      (wooleyPolynomialLowPart (r + 1) g).natDegree < r + 1 :=
    wooleyPolynomialLowPart_natDegree_lt (Nat.zero_lt_succ r)
      g
  have hlow : wooleyPolynomialLowPart (r + 1) g =
      ∑ i : Fin r, C (g.coeff ((i : ℕ) + 1)) * X ^ ((i : ℕ) + 1) := by
    rw [(wooleyPolynomialLowPart (r + 1) g).as_sum_range_C_mul_X_pow' hdeg]
    rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [wooleyPolynomialLowPart_coeff (by omega)]
    change C ((wooleyTaylorDifference h f).coeff 0) + _ = _
    rw [wooleyTaylorDifference_coeff_zero, C_0, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wooleyPolynomialLowPart_coeff (by omega)]
  change g = _
  calc
    g = wooleyPolynomialLowPart (r + 1) g +
        X ^ (r + 1) * wooleyPolynomialTail (r + 1) g :=
      (wooleyPolynomial_low_add_tail (r + 1) g).symm
    _ = _ := by rw [hlow]

/-- Hasse differentiation cannot lower the initial degree `k+1` far enough
to cross degree `j-i` when `i≤j≤k`. -/
theorem wooley_X_pow_sub_dvd_hasseDeriv_X_pow_mul
    {i j k : ℕ} (hi : i ≤ j) (hj : j ≤ k) (psi : Polynomial ℤ) :
    X ^ (j - i) ∣ hasseDeriv i (X ^ (k + 1) * psi) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rw [hasseDeriv_coeff]
  have hlt : d + i < k + 1 := by omega
  rw [coeff_X_pow_mul']
  simp only [if_neg (not_le.mpr hlt), mul_zero]

/-- Literal coefficient factorization defining the source integer `Ω`. -/
theorem wooley_taylorCoefficient_exists_omega
    {p c i j k : ℕ} (h : ℤ) (hi : i ≤ j) (hj : j ≤ k)
    (psi : Polynomial ℤ) :
    ∃ Omega : ℤ,
      (taylor h
        (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi)).coeff i =
          h ^ (j - i) * Omega ∧
      Int.ModEq ((p : ℤ) ^ c) Omega (Nat.choose j i : ℤ) := by
  obtain ⟨q, hq⟩ :=
    wooley_X_pow_sub_dvd_hasseDeriv_X_pow_mul hi hj psi
  refine ⟨(Nat.choose j i : ℤ) + (p : ℤ) ^ c * q.eval h, ?_, ?_⟩
  · rw [taylor_coeff]
    have hmono :
        hasseDeriv i (X ^ j : Polynomial ℤ) =
          monomial (j - i) (Nat.choose j i : ℤ) := by
      rw [X_pow_eq_monomial, hasseDeriv_monomial]
      simp only [mul_one]
    have hscalar :
        C ((p : ℤ) ^ c) * X ^ (k + 1) * psi =
          ((p : ℤ) ^ c) • (X ^ (k + 1) * psi) := by
      rw [mul_assoc, Polynomial.C_mul']
      rfl
    have hderivScalar :
        hasseDeriv i (((p : ℤ) ^ c) • (X ^ (k + 1) * psi)) =
          ((p : ℤ) ^ c) • hasseDeriv i (X ^ (k + 1) * psi) :=
      (hasseDeriv i).map_smul ((p : ℤ) ^ c) (X ^ (k + 1) * psi)
    rw [map_add, hmono, hscalar, hderivScalar, hq]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
    ring
  · rw [Int.modEq_iff_dvd]
    use -(q.eval h)
    ring

/-- Without assuming `i≤j`, the translated coefficient is still its
monomial Taylor coefficient plus a literal multiple of `p^c`.  This is the
raw congruence used before the source redistributes powers of the translation
parameter. -/
theorem wooley_taylorCoefficient_eq_monomial_add_spacing
    {p c i j k : ℕ} (h : ℤ) (psi : Polynomial ℤ) :
    ∃ z : ℤ,
      (taylor h
        (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi)).coeff i =
        (Nat.choose j i : ℤ) * h ^ (j - i) + (p : ℤ) ^ c * z := by
  refine ⟨(hasseDeriv i (X ^ (k + 1) * psi)).eval h, ?_⟩
  rw [taylor_coeff]
  have hmono :
      hasseDeriv i (X ^ j : Polynomial ℤ) =
        monomial (j - i) (Nat.choose j i : ℤ) := by
    rw [X_pow_eq_monomial, hasseDeriv_monomial]
    simp only [mul_one]
  have hscalar :
      C ((p : ℤ) ^ c) * X ^ (k + 1) * psi =
        ((p : ℤ) ^ c) • (X ^ (k + 1) * psi) := by
    rw [mul_assoc, Polynomial.C_mul']
    rfl
  have hderivScalar :
      hasseDeriv i (((p : ℤ) ^ c) • (X ^ (k + 1) * psi)) =
        ((p : ℤ) ^ c) • hasseDeriv i (X ^ (k + 1) * psi) :=
    (hasseDeriv i).map_smul ((p : ℤ) ^ c) (X ^ (k + 1) * psi)
  rw [map_add, hmono, hscalar, hderivScalar]
  simp [Polynomial.eval_mul, Polynomial.eval_pow]

/-- Source-faithful Laurent factorization of every translated coefficient.
When `i > j`, the displayed power `h^(j-i)` has negative exponent; the
integral coefficient `Omega` then contains the compensating positive power of
`h`.  Stating the equality in `ℚ` records that convention without pretending
that a negative exponent is a natural power. -/
theorem wooley_taylorCoefficient_exists_laurent_omega
    {p c i j k : ℕ} (h : ℤ) (hh : h ≠ 0) (hj : j ≤ k)
    (psi : Polynomial ℤ) :
    ∃ Omega : ℤ,
      ((taylor h
        (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi)).coeff i : ℚ) =
          (h : ℚ) ^ ((j : ℤ) - (i : ℤ)) * (Omega : ℚ) ∧
      Int.ModEq ((p : ℤ) ^ c) Omega (Nat.choose j i : ℤ) := by
  by_cases hij : i ≤ j
  · obtain ⟨Omega, hcoeff, hmod⟩ :=
      wooley_taylorCoefficient_exists_omega h hij hj psi
    refine ⟨Omega, ?_, hmod⟩
    rw [hcoeff, Int.cast_mul, Int.cast_pow]
    have hexp : ((j - i : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by omega
    rw [← zpow_natCast, hexp]
  · have hji : j < i := Nat.lt_of_not_ge hij
    obtain ⟨z, hcoeff⟩ :=
      wooley_taylorCoefficient_eq_monomial_add_spacing
        (p := p) (c := c) (i := i) (j := j) (k := k) h psi
    let a : ℤ :=
      (taylor h
        (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi)).coeff i
    refine ⟨a * h ^ (i - j), ?_, ?_⟩
    · have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
      have hexp : ((i - j : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by omega
      change (a : ℚ) =
        (h : ℚ) ^ ((j : ℤ) - (i : ℤ)) *
          ((a * h ^ (i - j) : ℤ) : ℚ)
      rw [Int.cast_mul, Int.cast_pow, ← zpow_natCast, hexp]
      symm
      calc
        (h : ℚ) ^ ((j : ℤ) - (i : ℤ)) *
              ((a : ℚ) * (h : ℚ) ^ ((i : ℤ) - (j : ℤ))) =
            (a : ℚ) *
              ((h : ℚ) ^ ((j : ℤ) - (i : ℤ)) *
                (h : ℚ) ^ ((i : ℤ) - (j : ℤ))) := by ring
        _ = (a : ℚ) := by
          rw [← zpow_add₀ hhq]
          norm_num
    · have hchoose : Nat.choose j i = 0 := Nat.choose_eq_zero_of_lt hji
      rw [hchoose, Int.natCast_zero, Int.modEq_iff_dvd]
      have ha : a = (p : ℤ) ^ c * z := by
        dsimp [a]
        rw [hcoeff, hchoose]
        ring
      rw [ha]
      exact ⟨-(z * h ^ (i - j)), by ring⟩

/-- The `Ω` coefficient is nonzero modulo `p` exactly when the corresponding
binomial coefficient is, provided the spacing exponent is positive. -/
theorem wooley_taylorOmega_mod_prime
    {p c i j : ℕ} (hc : 1 ≤ c) {Omega : ℤ}
    (hOmega : Int.ModEq ((p : ℤ) ^ c) Omega (Nat.choose j i : ℤ)) :
    (Omega : ZMod p) = (Nat.choose j i : ZMod p) := by
  have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ c := by
    exact dvd_pow_self (p : ℤ) (by omega)
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff]
  exact hOmega.of_dvd hpdiv

#print axioms wooley_X_pow_sub_dvd_hasseDeriv_X_pow_mul
#print axioms wooleyTaylorDifference_coeff_zero
#print axioms wooleyTaylorDifference_eq_low_sum_add_tail
#print axioms wooley_taylorCoefficient_exists_omega
#print axioms wooley_taylorCoefficient_eq_monomial_add_spacing
#print axioms wooley_taylorCoefficient_exists_laurent_omega
#print axioms wooley_taylorOmega_mod_prime

end

end GafniTao
