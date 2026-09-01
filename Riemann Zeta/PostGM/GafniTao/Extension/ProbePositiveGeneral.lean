import GafniTao.FordPositiveIntegralFormula

namespace GafniTao

noncomputable section

def fordPositivePrimitiveCandidate (a y : ℚ) (k : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.C
      (a * (k.choose m : ℚ) * (3 * y) ^ m /
        (3 * k - m + 1 : ℚ)) *
      Polynomial.X ^ (3 * k - m + 1)

theorem map_fordPositivePhasePolynomial (y : ℚ) :
    fordPositivePhasePolynomial.map (Polynomial.evalRingHom y) =
      Polynomial.C (3 * y) * Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
  unfold fordPositivePhasePolynomial fordBiY fordBiV fordBiRat
  simp
  ring

theorem fordPositiveMonomial_identity
    {k m : ℕ} (hm : m ∈ Finset.range (k + 1)) (y : ℚ) :
    (Polynomial.C (3 * y) * Polynomial.X ^ 2) ^ m *
          (Polynomial.X ^ 3) ^ (k - m) * (k.choose m : Polynomial ℚ) =
      Polynomial.C ((k.choose m : ℚ) * (3 * y) ^ m) *
        Polynomial.X ^ (3 * k - m) := by
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [show (k.choose m : Polynomial ℚ) =
    Polynomial.C (k.choose m : ℚ) by norm_num]
  calc
    Polynomial.C (3 * y) ^ m * Polynomial.X ^ (2 * m) *
          Polynomial.X ^ (3 * (k - m)) * Polynomial.C (k.choose m : ℚ) =
        (Polynomial.C (3 * y) ^ m * Polynomial.C (k.choose m : ℚ)) *
          (Polynomial.X ^ (2 * m) * Polynomial.X ^ (3 * (k - m))) := by ring
    _ = Polynomial.C ((3 * y) ^ m * (k.choose m : ℚ)) *
          Polynomial.X ^ (2 * m + 3 * (k - m)) := by
      rw [← map_pow, ← Polynomial.C_mul, ← pow_add]
    _ = Polynomial.C ((k.choose m : ℚ) * (3 * y) ^ m) *
          Polynomial.X ^ (3 * k - m) := by
      congr 2
      · ring
      · omega

theorem derivative_fordPositivePrimitiveCandidate (a y : ℚ) (k : ℕ) :
    Polynomial.derivative (fordPositivePrimitiveCandidate a y k) =
      Polynomial.C a *
        (Polynomial.C (3 * y) * Polynomial.X ^ 2 + Polynomial.X ^ 3) ^ k := by
  unfold fordPositivePrimitiveCandidate
  rw [Polynomial.derivative_sum]
  rw [add_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
  simp only [Nat.add_sub_cancel]
  rw [fordPositiveMonomial_identity hm]
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hcast : ((3 * k - m + 1 : ℕ) : ℚ) =
      3 * (k : ℚ) - (m : ℚ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : m ≤ 3 * k)]
    push_cast
    ring
  have hdenpos : 0 < 3 * (k : ℚ) - (m : ℚ) + 1 := by
    have hmkq : (m : ℚ) ≤ (k : ℚ) := by exact_mod_cast hmk
    linarith
  have hden : 3 * (k : ℚ) - (m : ℚ) + 1 ≠ 0 := hdenpos.ne'
  have hscalar :
      (a * (k.choose m : ℚ) * (3 * y) ^ m /
          (3 * (k : ℚ) - (m : ℚ) + 1)) *
          ((3 * k - m + 1 : ℕ) : ℚ) =
        a * ((k.choose m : ℚ) * (3 * y) ^ m) := by
    rw [hcast]
    field_simp [hden]
  calc
    Polynomial.C
          (a * (k.choose m : ℚ) * (3 * y) ^ m /
            (3 * (k : ℚ) - (m : ℚ) + 1)) *
          (Polynomial.C ((3 * k - m + 1 : ℕ) : ℚ) *
            Polynomial.X ^ (3 * k - m)) =
        Polynomial.C
          ((a * (k.choose m : ℚ) * (3 * y) ^ m /
            (3 * (k : ℚ) - (m : ℚ) + 1)) *
            ((3 * k - m + 1 : ℕ) : ℚ)) *
          Polynomial.X ^ (3 * k - m) := by
            simp only [map_mul]
            ring
    _ = Polynomial.C (a * ((k.choose m : ℚ) * (3 * y) ^ m)) *
          Polynomial.X ^ (3 * k - m) := by rw [hscalar]
    _ = Polynomial.C a *
          (Polynomial.C ((k.choose m : ℚ) * (3 * y) ^ m) *
            Polynomial.X ^ (3 * k - m)) := by
      simp only [map_mul]
      ring

@[simp] theorem fordPositivePrimitiveCandidate_coeff_zero
    (a y : ℚ) (k : ℕ) :
    (fordPositivePrimitiveCandidate a y k).coeff 0 = 0 := by
  unfold fordPositivePrimitiveCandidate
  simp

theorem map_fordPositiveLiftTerm (p : Polynomial ℚ) (k : ℕ) (y : ℚ) :
    (fordPositiveLiftTerm p k).map (Polynomial.evalRingHom y) =
      Polynomial.C (p.coeff k) *
        (Polynomial.C (3 * y) * Polynomial.X ^ 2 + Polynomial.X ^ 3) ^ k := by
  unfold fordPositiveLiftTerm
  rw [Polynomial.map_mul, Polynomial.map_pow,
    map_fordPositivePhasePolynomial]
  simp [fordBiRat]

theorem map_fordBiIntegralPositiveLiftTerm
    (p : Polynomial ℚ) (k : ℕ) (y : ℚ) :
    (fordBiIntegralPolynomial (fordPositiveLiftTerm p k)).map
        (Polynomial.evalRingHom y) =
      fordPositivePrimitiveCandidate (p.coeff k) y k := by
  rw [map_fordBiIntegralPolynomial]
  apply ratPolynomial_eq_of_derivative_eq_of_coeff_zero_eq
  · rw [derivative_fordRatIntegralPolynomial,
      derivative_fordPositivePrimitiveCandidate,
      map_fordPositiveLiftTerm]
  · simp

def fordPositivePrimitiveCandidateValue (a y : ℚ) (k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (k + 1),
    a * (k.choose m : ℚ) * (3 * y) ^ m *
      (3 / 2 : ℚ) ^ (3 * k - m + 1) /
        (3 * k - m + 1 : ℚ)

theorem eval_fordPositivePrimitiveCandidate (a y : ℚ) (k : ℕ) :
    Polynomial.eval (3 / 2) (fordPositivePrimitiveCandidate a y k) =
      fordPositivePrimitiveCandidateValue a y k := by
  unfold fordPositivePrimitiveCandidate fordPositivePrimitiveCandidateValue
  simp only [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  simp
  ring

theorem fordPositiveIntegralFormula_eval (p : Polynomial ℚ) (y : ℚ) :
    Polynomial.eval y (fordPositiveIntegralFormula p) =
      ∑ k ∈ Finset.range 67,
        fordPositivePrimitiveCandidateValue (p.coeff k) y k := by
  unfold fordPositiveIntegralFormula
  rw [fordBiEvalV_eval_rat]
  change Polynomial.eval (3 / 2)
      ((Polynomial.mapRingHom (Polynomial.evalRingHom y))
        (∑ k ∈ Finset.range 67,
          fordBiIntegralPolynomial (fordPositiveLiftTerm p k))) = _
  rw [map_sum]
  simp only [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval (3 / 2)
      ((fordBiIntegralPolynomial (fordPositiveLiftTerm p k)).map
        (Polynomial.evalRingHom y)) = _
  rw [map_fordBiIntegralPositiveLiftTerm,
    eval_fordPositivePrimitiveCandidate]

def fordPositiveIntegralPolynomialFormula (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range 67,
    ∑ m ∈ Finset.range (k + 1),
      Polynomial.C
        (p.coeff k * (k.choose m : ℚ) * 3 ^ m *
          (3 / 2 : ℚ) ^ (3 * k - m + 1) /
            (3 * k - m + 1 : ℚ)) * Polynomial.X ^ m

theorem eval_fordPositiveIntegralPolynomialFormula
    (p : Polynomial ℚ) (y : ℚ) :
    Polynomial.eval y (fordPositiveIntegralPolynomialFormula p) =
      ∑ k ∈ Finset.range 67,
        fordPositivePrimitiveCandidateValue (p.coeff k) y k := by
  unfold fordPositiveIntegralPolynomialFormula
  simp only [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold fordPositivePrimitiveCandidateValue
  apply Finset.sum_congr rfl
  intro m hm
  simp
  ring

theorem fordPositiveIntegralFormula_eq_polynomialFormula (p : Polynomial ℚ) :
    fordPositiveIntegralFormula p =
      fordPositiveIntegralPolynomialFormula p := by
  apply Polynomial.funext
  intro y
  rw [fordPositiveIntegralFormula_eval,
    eval_fordPositiveIntegralPolynomialFormula]

theorem fordPositiveIntegralPolynomialFormula_coeff
    (p : Polynomial ℚ) (n : ℕ) :
    (fordPositiveIntegralPolynomialFormula p).coeff n =
      ∑ k ∈ Finset.range 67,
        if n < k + 1 then
          p.coeff k * (k.choose n : ℚ) * 3 ^ n *
            (3 / 2 : ℚ) ^ (3 * k - n + 1) /
              (3 * k - n + 1 : ℚ)
        else 0 := by
  unfold fordPositiveIntegralPolynomialFormula
  simp only [Polynomial.coeff_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hn : n < k + 1
  · rw [if_pos hn]
    rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [Polynomial.coeff_C_mul, hmn.symm]
    · exact fun h => (h (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by
      intro h
      subst m
      exact hn (Finset.mem_range.mp hm)
    simp [Polynomial.coeff_C_mul, hmn]

end

end GafniTao
