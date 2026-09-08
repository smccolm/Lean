import Tao2026.Counting

/-!
# Type-F₃ intervals and factorial squares

This file proves the exact equivalence asserted in Tao's Definition 1.2(iii):
a type-`F₃` interval is the same data as a solution of the three-factorial
square equation with its two largest indices equal to the interval endpoints.
The proof keeps the square denominator in the factorial quotient honest by
proving the required natural-number cancellation lemma.
-/

namespace Tao2026

/-- If a square times `d` is a square in the naturals, then `d` is a square.
The proof first derives divisibility of the square root prime-by-prime, so it
does not use rational division. -/
theorem exists_eq_sq_of_sq_mul_eq_sq {c d m : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : c ^ 2 * d = m ^ 2) : ∃ r : ℕ, d = r ^ 2 := by
  have hm : m ≠ 0 := by
    intro hmzero
    apply mul_ne_zero (pow_ne_zero 2 hc) hd
    simpa [hmzero] using h
  have hcDvdM : c ∣ m := by
    rw [← Nat.factorization_prime_le_iff_dvd hc hm]
    intro p hp
    have hfac := congrArg (fun n : ℕ => n.factorization p) h
    change (c ^ 2 * d).factorization p = (m ^ 2).factorization p at hfac
    rw [Nat.factorization_mul (pow_ne_zero 2 hc) hd,
      Nat.factorization_pow, Nat.factorization_pow] at hfac
    change 2 * c.factorization p + d.factorization p =
      2 * m.factorization p at hfac
    omega
  obtain ⟨r, hr⟩ := hcDvdM
  refine ⟨r, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hc.bot_lt 2)
  calc
    c ^ 2 * d = m ^ 2 := h
    _ = c ^ 2 * r ^ 2 := by rw [hr]; ring

/-- Exact source equivalence from Definition 1.2(iii), including `H ≥ 1`
and the strict inequality on the smaller factorial index. -/
theorem isFactorialThreeInterval_iff_factorialSquare {N H : ℕ} :
    IsFactorialThreeInterval N H ↔
      1 ≤ H ∧ ∃ a m : ℕ, 1 ≤ a ∧ a < N ∧
        a.factorial * N.factorial * (N + H).factorial = m ^ 2 := by
  constructor
  · rintro ⟨hH, a, ha, haN, hcomponents⟩
    have hproduct0 := consecutiveProduct_ne_zero N H
    have hfactorial0 : a.factorial ≠ 0 := Nat.factorial_ne_zero a
    obtain ⟨r, hr⟩ :=
      (squarefreeComponent_eq_iff_mul_eq_sq hproduct0 hfactorial0).mp
        hcomponents
    refine ⟨hH, a, N.factorial * r, ha, haN, ?_⟩
    rw [← factorial_mul_consecutiveProduct]
    calc
      a.factorial * N.factorial *
          (N.factorial * consecutiveProduct N H) =
          N.factorial ^ 2 *
            (consecutiveProduct N H * a.factorial) := by ring
      _ = N.factorial ^ 2 * r ^ 2 := by rw [hr]
      _ = (N.factorial * r) ^ 2 := by ring
  · rintro ⟨hH, a, m, ha, haN, hfactorial⟩
    have htotal : N.factorial ^ 2 *
        (a.factorial * consecutiveProduct N H) = m ^ 2 := by
      calc
        N.factorial ^ 2 * (a.factorial * consecutiveProduct N H) =
            a.factorial * N.factorial *
              (N.factorial * consecutiveProduct N H) := by ring
        _ = a.factorial * N.factorial * (N + H).factorial := by
          rw [factorial_mul_consecutiveProduct]
        _ = m ^ 2 := hfactorial
    obtain ⟨r, hr⟩ := exists_eq_sq_of_sq_mul_eq_sq
      (Nat.factorial_ne_zero N)
      (mul_ne_zero (Nat.factorial_ne_zero a) (consecutiveProduct_ne_zero N H))
      htotal
    have hcomponents : squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial := by
      symm
      exact (squarefreeComponent_eq_iff_mul_eq_sq
        (Nat.factorial_ne_zero a) (consecutiveProduct_ne_zero N H)).mpr
          ⟨r, hr⟩
    exact ⟨hH, a, ha, haN, hcomponents⟩

/-- Source equivalence from Definition 1.3(iii): `n` is a right endpoint of
a type-`F₃` interval exactly when it is the largest index in a strictly
ordered three-factorial square solution. -/
theorem mem_factorialThreeSet_iff_exists_factorialSquare {n : ℕ} :
    n ∈ factorialThreeSet ↔
      ∃ a₁ a₂ m : ℕ, 1 ≤ a₁ ∧ a₁ < a₂ ∧ a₂ < n ∧
        a₁.factorial * a₂.factorial * n.factorial = m ^ 2 := by
  constructor
  · rintro ⟨N, H, rfl, hinterval⟩
    rcases isFactorialThreeInterval_iff_factorialSquare.mp hinterval with
      ⟨hH, a, m, ha, haN, hsquare⟩
    exact ⟨a, N, m, ha, haN, by omega, hsquare⟩
  · rintro ⟨a₁, a₂, m, ha₁, ha₁a₂, ha₂n, hsquare⟩
    have ha₂nLe : a₂ ≤ n := ha₂n.le
    have hsum : a₂ + (n - a₂) = n := Nat.add_sub_of_le ha₂nLe
    refine ⟨a₂, n - a₂, hsum.symm, ?_⟩
    rw [isFactorialThreeInterval_iff_factorialSquare]
    refine ⟨by omega, a₁, m, ha₁, ha₁a₂, ?_⟩
    simpa only [hsum] using hsquare

/-- The endpoint characterization phrased using the public factorial-triple
predicate. -/
theorem mem_factorialThreeSet_iff_exists_triple {n : ℕ} :
    n ∈ factorialThreeSet ↔
      ∃ a₁ a₂ : ℕ, IsFactorialSquareTriple a₁ a₂ n := by
  rw [mem_factorialThreeSet_iff_exists_factorialSquare]
  constructor
  · rintro ⟨a₁, a₂, m, ha₁, ha₁a₂, ha₂n, hm⟩
    exact ⟨a₁, a₂, ha₁, ha₁a₂, ha₂n, m, hm⟩
  · rintro ⟨a₁, a₂, ha₁, ha₁a₂, ha₂n, m, hm⟩
    exact ⟨a₁, a₂, m, ha₁, ha₁a₂, ha₂n, hm⟩

/-- The finite set of type-`F₃` endpoints in `[1,x]`.  Naming this finset
lets later counting arguments refer to the actual values, rather than only
their cardinality. -/
noncomputable def factorialThreeNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n => n ∈ factorialThreeSet

@[simp]
theorem mem_factorialThreeNumbersUpTo {x n : ℕ} :
    n ∈ factorialThreeNumbersUpTo x ↔
      n ∈ Finset.Icc 1 x ∧ n ∈ factorialThreeSet := by
  classical
  simp [factorialThreeNumbersUpTo]

/-- Projecting a factorial-square triple to its largest index gives exactly
the finite set of type-`F₃` endpoints. -/
theorem image_factorialSquareTriplesUpTo_endpoint (x : ℕ) :
    (factorialSquareTriplesUpTo x).image (fun t => t.2.2) =
      factorialThreeNumbersUpTo x := by
  classical
  ext n
  rw [Finset.mem_image, mem_factorialThreeNumbersUpTo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_factorialSquareTriplesUpTo] at ht
    exact ⟨ht.2.2.1, mem_factorialThreeSet_iff_exists_triple.mpr
      ⟨t.1, t.2.1, ht.2.2.2⟩⟩
  · rintro ⟨hnRange, hn⟩
    have hnBounds : 1 ≤ n ∧ n ≤ x := Finset.mem_Icc.mp hnRange
    obtain ⟨a₁, a₂, htriple⟩ :=
      mem_factorialThreeSet_iff_exists_triple.mp hn
    refine ⟨(a₁, a₂, n), ?_, rfl⟩
    apply mem_factorialSquareTriplesUpTo.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨htriple.1, le_trans htriple.2.1.le
        (le_trans htriple.2.2.1.le hnBounds.2)⟩,
      Finset.mem_Icc.mpr ⟨le_trans htriple.1 htriple.2.1.le,
        le_trans htriple.2.2.1.le hnBounds.2⟩,
      hnRange, htriple⟩

/-- Every `F₃` endpoint contributes at least one factorial-square triple.
This is the exact finite-cardinality direction used in the lower-bound half
of Tao's Theorem 1.10. -/
theorem factorialThreeCount_le_factorialSquareTripleCount (x : ℕ) :
    factorialThreeCount x ≤ factorialSquareTripleCount x := by
  classical
  change (factorialThreeNumbersUpTo x).card ≤
    (factorialSquareTriplesUpTo x).card
  rw [← image_factorialSquareTriplesUpTo_endpoint]
  exact Finset.card_image_le

end Tao2026
