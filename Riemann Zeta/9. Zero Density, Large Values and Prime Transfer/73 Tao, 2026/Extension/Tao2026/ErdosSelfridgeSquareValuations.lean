import Tao2026.ErdosSelfridgeSquareDensity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Factorization

/-!
# The valuation ledger behind Erdős--Selfridge equation (23)

This file isolates the exact integer arithmetic between equations (21), (22),
and the displayed real-power estimate (23) in Section 3.1 of the pinned 1975
paper.  The two exceptional primes are kept explicit; no logarithmic rounding
or numerical primorial estimate is used here.
-/

namespace Tao2026

open scoped BigOperators

/-- The product of the canonical squarefree coefficients in the source
interval. -/
noncomputable def erdosSelfridgeSquareCoefficientProduct (N H : ℕ) : ℕ :=
  ∏ i ∈ Finset.range H, powerFreePart 2 (N + (i + 1))

theorem erdosSelfridgeSquareCoefficientProduct_pos (N H : ℕ) :
    0 < erdosSelfridgeSquareCoefficientProduct N H := by
  apply Finset.prod_pos
  intro i hi
  exact Nat.pos_iff_ne_zero.mpr (powerFreePart_ne_zero 2 (N + (i + 1)))

/-- The binary digit sum of `n` is at most `log₂(n+1)`.  The successor is
essential: at `n=2^r-1` equality holds. -/
theorem binary_digits_sum_cast_le_logb_succ (n : ℕ) :
    ((Nat.digits 2 n).sum : ℝ) ≤ Real.logb 2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn]
      have hdivLt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      have hih := ih (n / 2) hdivLt
      rw [Nat.digits_eq_cons_digits_div (by omega) hn, List.sum_cons, Nat.cast_add]
      have hmodLt : n % 2 < 2 := Nat.mod_lt n (by omega)
      interval_cases hmod : n % 2
      · norm_num only [Nat.cast_zero, zero_add]
        have hsucc : n / 2 + 1 ≤ n + 1 :=
          Nat.add_le_add_right (Nat.div_le_self n 2) 1
        exact hih.trans (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (by positivity) (by exact_mod_cast hsucc))
      · have hnForm : n + 1 = 2 * (n / 2 + 1) := by
          omega
        have hnFormReal : (n : ℝ) + 1 =
            2 * (((n / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast hnForm
        calc
          ((1 : ℕ) : ℝ) + ((Nat.digits 2 (n / 2)).sum : ℝ) ≤
              1 + Real.logb 2 (((n / 2 : ℕ) : ℝ) + 1) := by
                simpa [add_comm] using add_le_add_left hih 1
          _ = Real.logb 2 2 +
              Real.logb 2 (((n / 2 : ℕ) : ℝ) + 1) := by
            rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          _ = Real.logb 2 (2 * (((n / 2 : ℕ) : ℝ) + 1)) := by
            rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)]
            positivity
          _ = Real.logb 2 (n + 1) := by rw [hnFormReal]

/-- The corresponding sharp ternary digit estimate.  The middle residue uses
`√3≤2`; residues zero and two are respectively monotone and exact. -/
theorem ternary_digits_sum_cast_div_two_le_logb_succ (n : ℕ) :
    ((Nat.digits 3 n).sum : ℝ) / 2 ≤ Real.logb 3 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [hn]
      have hdivLt : n / 3 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      have hih := ih (n / 3) hdivLt
      rw [Nat.digits_eq_cons_digits_div (by omega) hn, List.sum_cons, Nat.cast_add]
      have hmodLt : n % 3 < 3 := Nat.mod_lt n (by omega)
      interval_cases hmod : n % 3
      · norm_num only [Nat.cast_zero, zero_add]
        have hsucc : n / 3 + 1 ≤ n + 1 :=
          Nat.add_le_add_right (Nat.div_le_self n 3) 1
        exact hih.trans (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
          (by positivity) (by exact_mod_cast hsucc))
      · have hhalfLog : (1 / 2 : ℝ) ≤ Real.logb 3 2 := by
          rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) (by norm_num)]
          rw [← Real.sqrt_eq_rpow]
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
        have hsmall : 2 * (n / 3 + 1) ≤ n + 1 := by omega
        have hsmallReal : (2 : ℝ) * (((n / 3 : ℕ) : ℝ) + 1) ≤
            (n : ℝ) + 1 := by exact_mod_cast hsmall
        calc
          (((1 : ℕ) : ℝ) + ((Nat.digits 3 (n / 3)).sum : ℝ)) / 2 =
              1 / 2 + ((Nat.digits 3 (n / 3)).sum : ℝ) / 2 := by ring
          _ ≤ Real.logb 3 2 +
              Real.logb 3 (((n / 3 : ℕ) : ℝ) + 1) :=
            add_le_add hhalfLog hih
          _ = Real.logb 3 (2 * (((n / 3 : ℕ) : ℝ) + 1)) := by
            rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)]
            positivity
          _ ≤ Real.logb 3 (n + 1) :=
            Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
              (by positivity) hsmallReal
      · have hnForm : n + 1 = 3 * (n / 3 + 1) := by omega
        have hnFormReal : (n : ℝ) + 1 =
            3 * (((n / 3 : ℕ) : ℝ) + 1) := by exact_mod_cast hnForm
        calc
          (((2 : ℕ) : ℝ) + ((Nat.digits 3 (n / 3)).sum : ℝ)) / 2 =
              1 + ((Nat.digits 3 (n / 3)).sum : ℝ) / 2 := by ring
          _ ≤ 1 + Real.logb 3 (((n / 3 : ℕ) : ℝ) + 1) := by
            simpa [add_comm] using add_le_add_left hih 1
          _ = Real.logb 3 3 +
              Real.logb 3 (((n / 3 : ℕ) : ℝ) + 1) := by
            rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
          _ = Real.logb 3 (3 * (((n / 3 : ℕ) : ℝ) + 1)) := by
            rw [Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0)]
            positivity
          _ = Real.logb 3 (n + 1) := by rw [hnFormReal]

private theorem one_half_le_logb_three_two :
    (1 / 2 : ℝ) ≤ Real.logb 3 2 := by
  rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) (by norm_num)]
  rw [← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- The paper's lower bound `α ≥ H-1-log₂ H` for the power `α` of `2` in
`(H-1)!`. -/
theorem factorization_factorial_two_source_lower {H : ℕ} (hH : 1 ≤ H) :
    (((H - 1 : ℕ) : ℝ) - Real.logb 2 H) ≤
      (((H - 1).factorial.factorization 2 : ℕ) : ℝ) := by
  let n := H - 1
  have hnSucc : n + 1 = H := by omega
  have hfac := Nat.sub_one_mul_factorization_factorial
    (n := n) (p := 2) (by norm_num : (2 : ℕ).Prime)
  have hsumNat : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hsumReal := binary_digits_sum_cast_le_logb_succ n
  have hnSuccReal : (n : ℝ) + 1 = (H : ℝ) := by exact_mod_cast hnSucc
  rw [hnSuccReal] at hsumReal
  norm_num at hfac
  have hfacCast : (((n.factorial.factorization 2 : ℕ) : ℝ)) =
      (n : ℝ) - ((Nat.digits 2 n).sum : ℝ) := by
    rw [hfac, Nat.cast_sub hsumNat]
  change (n : ℝ) - Real.logb 2 H ≤
    ((n.factorial.factorization 2 : ℕ) : ℝ)
  rw [hfacCast]
  linarith

/-- The paper's lower bound `β ≥ (H-1)/2-log₃ H` for the power `β` of `3`
in `(H-1)!`. -/
theorem factorization_factorial_three_source_lower {H : ℕ} (hH : 1 ≤ H) :
    ((H - 1 : ℕ) : ℝ) / 2 - Real.logb 3 H ≤
      (((H - 1).factorial.factorization 3 : ℕ) : ℝ) := by
  let n := H - 1
  have hnSucc : n + 1 = H := by omega
  have hfac := Nat.sub_one_mul_factorization_factorial
    (n := n) (p := 3) (by norm_num : (3 : ℕ).Prime)
  have hsumNat : (Nat.digits 3 n).sum ≤ n := Nat.digit_sum_le 3 n
  have hsumReal := ternary_digits_sum_cast_div_two_le_logb_succ n
  have hnSuccReal : (n : ℝ) + 1 = (H : ℝ) := by exact_mod_cast hnSucc
  rw [hnSuccReal] at hsumReal
  norm_num at hfac
  have hfacCast : (2 : ℝ) * (((n.factorial.factorization 3 : ℕ) : ℝ)) =
      (n : ℝ) - ((Nat.digits 3 n).sum : ℝ) := by
    calc
      (2 : ℝ) * (((n.factorial.factorization 3 : ℕ) : ℝ)) =
          (((2 * n.factorial.factorization 3 : ℕ) : ℝ)) := by norm_num
      _ = (((n - (Nat.digits 3 n).sum : ℕ) : ℝ)) := by rw [hfac]
      _ = (n : ℝ) - ((Nat.digits 3 n).sum : ℝ) := Nat.cast_sub hsumNat
  change (n : ℝ) / 2 - Real.logb 3 H ≤
    ((n.factorial.factorization 3 : ℕ) : ℝ)
  linarith

/-- Positive integers in `(N,N+H]` whose 2-adic valuation is odd. -/
noncomputable def oddTwoValuationInterval (N H : ℕ) : Finset ℕ :=
  (Finset.Ioc N (N + H)).filter fun m => Odd (m.factorization 2)

/-- Positive integers in `(N,N+H]` whose 3-adic valuation is odd. -/
noncomputable def oddThreeValuationInterval (N H : ℕ) : Finset ℕ :=
  (Finset.Ioc N (N + H)).filter fun m => Odd (m.factorization 3)

private theorem odd_factorization_two_mul_iff_even {m : ℕ} (hm : 0 < m) :
    Odd ((2 * m).factorization 2) ↔ Even (m.factorization 2) := by
  rw [Nat.factorization_mul (by norm_num) hm.ne', Finsupp.coe_add, Pi.add_apply,
    (show (2 : ℕ).factorization 2 = 1 by norm_num), Nat.add_comm, Nat.odd_add_one]
  exact Nat.not_odd_iff_even

private theorem odd_factorization_three_mul_iff_even {m : ℕ} (hm : 0 < m) :
    Odd ((3 * m).factorization 3) ↔ Even (m.factorization 3) := by
  rw [Nat.factorization_mul (by norm_num) hm.ne', Finsupp.coe_add, Pi.add_apply,
    (show (3 : ℕ).factorization 3 = 1 by norm_num), Nat.add_comm, Nat.odd_add_one]
  exact Nat.not_odd_iff_even

/-- Exact halving recurrence for the odd 2-adic valuation count. -/
theorem card_oddTwoValuationInterval_rec (N H : ℕ) :
    (oddTwoValuationInterval N H).card =
      ((N + H) / 2 - N / 2) -
        (oddTwoValuationInterval (N / 2) ((N + H) / 2 - N / 2)).card := by
  let D := (N + H) / 2 - N / 2
  let Q := Finset.Ioc (N / 2) ((N + H) / 2)
  have hcardEven : (oddTwoValuationInterval N H).card =
      (Q.filter fun q => Even (q.factorization 2)).card := by
    apply Finset.card_bij (fun m _ => m / 2)
    · intro m hm
      have hmData := Finset.mem_filter.mp (show m ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 2)) from hm)
      have hmBounds := Finset.mem_Ioc.mp hmData.1
      have hfacNe : m.factorization 2 ≠ 0 := by
        intro hz
        rw [hz] at hmData
        exact Nat.not_odd_zero hmData.2
      have hdvd : 2 ∣ m := Nat.dvd_of_factorization_pos hfacNe
      have hmEq : 2 * (m / 2) = m := Nat.mul_div_cancel' hdvd
      rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hfloor : 2 * (N / 2) ≤ N := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self N 2
        omega
      · exact Nat.div_le_div_right hmBounds.2
      · have hodd := hmData.2
        rw [← hmEq] at hodd
        exact (odd_factorization_two_mul_iff_even (by omega)).mp hodd
    · intro m₁ hm₁ m₂ hm₂ hdiv
      have hm₁Data := Finset.mem_filter.mp (show m₁ ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 2)) from hm₁)
      have hm₂Data := Finset.mem_filter.mp (show m₂ ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 2)) from hm₂)
      have hdvd₁ : 2 ∣ m₁ := Nat.dvd_of_factorization_pos (by
        intro hz
        rw [hz] at hm₁Data
        exact Nat.not_odd_zero hm₁Data.2)
      have hdvd₂ : 2 ∣ m₂ := Nat.dvd_of_factorization_pos (by
        intro hz
        rw [hz] at hm₂Data
        exact Nat.not_odd_zero hm₂Data.2)
      calc
        m₁ = 2 * (m₁ / 2) := (Nat.mul_div_cancel' hdvd₁).symm
        _ = 2 * (m₂ / 2) := by rw [hdiv]
        _ = m₂ := Nat.mul_div_cancel' hdvd₂
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      refine ⟨2 * q, ?_, by simp⟩
      rw [oddTwoValuationInterval, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · omega
      · exact (odd_factorization_two_mul_iff_even (by omega)).mpr hq.2
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Q) (fun q => Odd (q.factorization 2))
  have hnot : (Q.filter fun q => ¬ Odd (q.factorization 2)) =
      Q.filter fun q => Even (q.factorization 2) := by
    ext q
    simp [Nat.not_odd_iff_even]
  rw [hnot] at hpartition
  have hQcard : Q.card = D := by
    dsimp only [Q, D]
    simp
  have hoddQ : (Q.filter fun q => Odd (q.factorization 2)) =
      oddTwoValuationInterval (N / 2) D := by
    dsimp only [Q, D, oddTwoValuationInterval]
    congr 2
    omega
  rw [hcardEven, ← hoddQ]
  omega

/-- Exact thirding recurrence for the odd 3-adic valuation count. -/
theorem card_oddThreeValuationInterval_rec (N H : ℕ) :
    (oddThreeValuationInterval N H).card =
      ((N + H) / 3 - N / 3) -
        (oddThreeValuationInterval (N / 3) ((N + H) / 3 - N / 3)).card := by
  let D := (N + H) / 3 - N / 3
  let Q := Finset.Ioc (N / 3) ((N + H) / 3)
  have hcardEven : (oddThreeValuationInterval N H).card =
      (Q.filter fun q => Even (q.factorization 3)).card := by
    apply Finset.card_bij (fun m _ => m / 3)
    · intro m hm
      have hmData := Finset.mem_filter.mp (show m ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 3)) from hm)
      have hmBounds := Finset.mem_Ioc.mp hmData.1
      have hfacNe : m.factorization 3 ≠ 0 := by
        intro hz
        rw [hz] at hmData
        exact Nat.not_odd_zero hmData.2
      have hdvd : 3 ∣ m := Nat.dvd_of_factorization_pos hfacNe
      have hmEq : 3 * (m / 3) = m := Nat.mul_div_cancel' hdvd
      rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hfloor : 3 * (N / 3) ≤ N := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self N 3
        omega
      · exact Nat.div_le_div_right hmBounds.2
      · have hodd := hmData.2
        rw [← hmEq] at hodd
        exact (odd_factorization_three_mul_iff_even (by omega)).mp hodd
    · intro m₁ hm₁ m₂ hm₂ hdiv
      have hm₁Data := Finset.mem_filter.mp (show m₁ ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 3)) from hm₁)
      have hm₂Data := Finset.mem_filter.mp (show m₂ ∈
        (Finset.Ioc N (N + H)).filter (fun m => Odd (m.factorization 3)) from hm₂)
      have hdvd₁ : 3 ∣ m₁ := Nat.dvd_of_factorization_pos (by
        intro hz
        rw [hz] at hm₁Data
        exact Nat.not_odd_zero hm₁Data.2)
      have hdvd₂ : 3 ∣ m₂ := Nat.dvd_of_factorization_pos (by
        intro hz
        rw [hz] at hm₂Data
        exact Nat.not_odd_zero hm₂Data.2)
      calc
        m₁ = 3 * (m₁ / 3) := (Nat.mul_div_cancel' hdvd₁).symm
        _ = 3 * (m₂ / 3) := by rw [hdiv]
        _ = m₂ := Nat.mul_div_cancel' hdvd₂
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      refine ⟨3 * q, ?_, by simp⟩
      rw [oddThreeValuationInterval, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · omega
      · exact (odd_factorization_three_mul_iff_even (by omega)).mpr hq.2
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Q) (fun q => Odd (q.factorization 3))
  have hnot : (Q.filter fun q => ¬ Odd (q.factorization 3)) =
      Q.filter fun q => Even (q.factorization 3) := by
    ext q
    simp [Nat.not_odd_iff_even]
  rw [hnot] at hpartition
  have hQcard : Q.card = D := by
    dsimp only [Q, D]
    simp
  have hoddQ : (Q.filter fun q => Odd (q.factorization 3)) =
      oddThreeValuationInterval (N / 3) D := by
    dsimp only [Q, D, oddThreeValuationInterval]
    congr 2
    omega
  rw [hcardEven, ← hoddQ]
  omega

theorem card_oddTwoValuationInterval_le (N H : ℕ) :
    (oddTwoValuationInterval N H).card ≤ H := by
  calc
    (oddTwoValuationInterval N H).card ≤ (Finset.Ioc N (N + H)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = H := by simp

theorem card_oddThreeValuationInterval_le (N H : ℕ) :
    (oddThreeValuationInterval N H).card ≤ H := by
  calc
    (oddThreeValuationInterval N H).card ≤ (Finset.Ioc N (N + H)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = H := by simp

/-- Uniform two-sided discrepancy for odd 2-adic valuations in a translated
interval.  The upper half is exactly the estimate used for `γ` in the paper;
the lower half is the mutually inductive companion needed by the halving
recurrence. -/
theorem oddTwoValuationInterval_discrepancy (H : ℕ) (hH : 1 ≤ H) :
    ∀ N : ℕ,
      (3 : ℝ) * (oddTwoValuationInterval N H).card - H ≤
          Real.logb 2 (3 * H + 1) ∧
      (H : ℝ) - 3 * (oddTwoValuationInterval N H).card ≤
          Real.logb 2 ((3 * H - 1 : ℕ) : ℝ) := by
  induction H using Nat.strong_induction_on with
  | h H ih =>
      intro N
      by_cases hHone : H = 1
      · subst H
        have hcard := card_oddTwoValuationInterval_le N 1
        constructor
        · have hlog : Real.logb 2 (4 : ℝ) = 2 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
              Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
            norm_num
          norm_num only [Nat.cast_one, Nat.cast_ofNat]
          rw [hlog]
          have hcardReal : ((oddTwoValuationInterval N 1).card : ℝ) ≤ 1 := by
            exact_mod_cast hcard
          linarith
        · have hlog : Real.logb 2 (2 : ℝ) = 1 :=
            Real.logb_self_eq_one (by norm_num)
          norm_num only [Nat.cast_one, Nat.cast_ofNat]
          rw [hlog]
          have hcardNonneg : (0 : ℝ) ≤
              (oddTwoValuationInterval N 1).card := by positivity
          linarith
      · have hHtwo : 2 ≤ H := by omega
        let D := (N + H) / 2 - N / 2
        let C := (oddTwoValuationInterval N H).card
        let C' := (oddTwoValuationInterval (N / 2) D).card
        have hDpos : 1 ≤ D := by
          dsimp only [D]
          omega
        have hDlt : D < H := by
          dsimp only [D]
          omega
        have hDupper : 2 * D ≤ H + 1 := by
          dsimp only [D]
          omega
        have hDlower : H ≤ 2 * D + 1 := by
          dsimp only [D]
          omega
        have hrec : C = D - C' := by
          dsimp only [C, C', D]
          exact card_oddTwoValuationInterval_rec N H
        have hC'le : C' ≤ D := card_oddTwoValuationInterval_le _ _
        have hrecCast : (C : ℝ) = (D : ℝ) - (C' : ℝ) := by
          rw [hrec, Nat.cast_sub hC'le]
        obtain ⟨hupper', hlower'⟩ := ih D hDlt hDpos (N / 2)
        change (3 : ℝ) * C' - D ≤ Real.logb 2 (3 * D + 1) at hupper'
        change (D : ℝ) - 3 * C' ≤
          Real.logb 2 ((3 * D - 1 : ℕ) : ℝ) at hlower'
        constructor
        · have harg : 2 * (3 * D - 1) ≤ 3 * H + 1 := by omega
          have hargLeftPos : 0 < 2 * (3 * D - 1) := by omega
          have hDupperReal : (2 : ℝ) * D ≤ H + 1 := by
            exact_mod_cast hDupper
          calc
            (3 : ℝ) * C - H ≤
                1 + Real.logb 2 ((3 * D - 1 : ℕ) : ℝ) := by
              rw [hrecCast]
              linarith
            _ = Real.logb 2 (2 * ((3 * D - 1 : ℕ) : ℝ)) := by
              calc
                1 + Real.logb 2 ((3 * D - 1 : ℕ) : ℝ) =
                    Real.logb 2 2 + Real.logb 2 ((3 * D - 1 : ℕ) : ℝ) := by
                  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
                _ = Real.logb 2 (2 * ((3 * D - 1 : ℕ) : ℝ)) :=
                  (Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
                    (by exact_mod_cast (show 3 * D - 1 ≠ 0 by omega))).symm
            _ ≤ Real.logb 2 (3 * H + 1) :=
              Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
                (by exact_mod_cast hargLeftPos) (by exact_mod_cast harg)
        · by_cases hDsmall : 2 * D < H
          · have hEq : H = 2 * D + 1 := by omega
            have hEqReal : (H : ℝ) = 2 * D + 1 := by exact_mod_cast hEq
            have hargEq : 2 * (3 * D + 1) = 3 * H - 1 := by omega
            calc
              (H : ℝ) - 3 * C ≤
                  1 + Real.logb 2 (3 * D + 1) := by
                rw [hrecCast]
                linarith
              _ = Real.logb 2 (2 * ((3 * D + 1 : ℕ) : ℝ)) := by
                calc
                  1 + Real.logb 2 (3 * (D : ℝ) + 1) =
                      Real.logb 2 2 + Real.logb 2 ((3 * D + 1 : ℕ) : ℝ) := by
                    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
                    norm_num
                  _ = Real.logb 2 (2 * ((3 * D + 1 : ℕ) : ℝ)) :=
                    (Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
                      (by positivity : (((3 * D + 1 : ℕ) : ℝ)) ≠ 0)).symm
              _ = Real.logb 2 ((3 * H - 1 : ℕ) : ℝ) := by
                congr 2
                exact_mod_cast hargEq
          · by_cases hDeq : 2 * D = H
            · have harg : 3 * D + 1 ≤ 3 * H - 1 := by omega
              have hDeqReal : (2 : ℝ) * D = H := by exact_mod_cast hDeq
              calc
                (H : ℝ) - 3 * C ≤ Real.logb 2 (3 * D + 1) := by
                  rw [hrecCast]
                  linarith
                _ ≤ Real.logb 2 ((3 * H - 1 : ℕ) : ℝ) :=
                  Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
                    (by positivity) (by exact_mod_cast harg)
            · have hEq : 2 * D = H + 1 := by omega
              have hEqReal : (2 : ℝ) * D = H + 1 := by exact_mod_cast hEq
              have harg : 3 * D + 1 ≤ 3 * H - 1 := by omega
              calc
                (H : ℝ) - 3 * C ≤ Real.logb 2 (3 * D + 1) := by
                  rw [hrecCast]
                  linarith
                _ ≤ Real.logb 2 ((3 * H - 1 : ℕ) : ℝ) :=
                  Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
                    (by positivity) (by exact_mod_cast harg)

/-- Uniform two-sided discrepancy for odd 3-adic valuations.  Its upper half
is the source estimate for `δ`; the shifted lower half makes the exact
thirding recurrence close. -/
theorem oddThreeValuationInterval_discrepancy (H : ℕ) (hH : 1 ≤ H) :
    ∀ N : ℕ,
      (4 : ℝ) * (oddThreeValuationInterval N H).card - H ≤
          1 + 2 * Real.logb 3 (2 * H + 1) ∧
      (H : ℝ) - 4 * (oddThreeValuationInterval N H).card ≤
          1 + 2 * Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) := by
  induction H using Nat.strong_induction_on with
  | h H ih =>
      intro N
      by_cases hHone : H = 1
      · subst H
        have hcard := card_oddThreeValuationInterval_le N 1
        have hcardReal : ((oddThreeValuationInterval N 1).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        have hcardNonneg : (0 : ℝ) ≤
            (oddThreeValuationInterval N 1).card := by positivity
        have hlogThree : Real.logb 3 (3 : ℝ) = 1 :=
          Real.logb_self_eq_one (by norm_num)
        constructor
        · norm_num only [Nat.cast_one, Nat.cast_ofNat]
          rw [hlogThree]
          linarith
        · norm_num only [Nat.cast_one, Nat.cast_ofNat, Real.logb_one,
            mul_zero, add_zero]
          linarith
      · have hHtwo : 2 ≤ H := by omega
        let D := (N + H) / 3 - N / 3
        let C := (oddThreeValuationInterval N H).card
        let C' := (oddThreeValuationInterval (N / 3) D).card
        have hDupper : 3 * D ≤ H + 2 := by
          dsimp only [D]
          omega
        have hDlower : H ≤ 3 * D + 2 := by
          dsimp only [D]
          omega
        have hrec : C = D - C' := by
          dsimp only [C, C', D]
          exact card_oddThreeValuationInterval_rec N H
        have hC'le : C' ≤ D := card_oddThreeValuationInterval_le _ _
        have hrecCast : (C : ℝ) = (D : ℝ) - (C' : ℝ) := by
          rw [hrec, Nat.cast_sub hC'le]
        by_cases hDzero : D = 0
        · have hHeq : H = 2 := by
            dsimp only [D] at hDzero
            omega
          have hCzero : C = 0 := by omega
          subst H
          have hlogFive : 0 ≤ Real.logb 3 (5 : ℝ) :=
            Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) (by norm_num)
          have hlogThree : Real.logb 3 (3 : ℝ) = 1 :=
            Real.logb_self_eq_one (by norm_num)
          have hActualZero : (oddThreeValuationInterval N 2).card = 0 := by
            simpa [C] using hCzero
          rw [hActualZero]
          constructor
          · norm_num only [Nat.cast_ofNat, Nat.cast_zero, mul_zero,
              zero_sub]
            linarith
          · norm_num only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero]
            rw [hlogThree]
            norm_num
        · have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hDzero
          have hDlt : D < H := by
            dsimp only [D]
            omega
          obtain ⟨hupper', hlower'⟩ := ih D hDlt hDpos (N / 3)
          change (4 : ℝ) * C' - D ≤
            1 + 2 * Real.logb 3 (2 * D + 1) at hupper'
          change (D : ℝ) - 4 * C' ≤
            1 + 2 * Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) at hlower'
          constructor
          · by_cases hnonpos : 3 * D ≤ H
            · have harg : 2 * D - 1 ≤ 2 * H + 1 := by omega
              have hargPos : 0 < ((2 * D - 1 : ℕ) : ℝ) := by
                exact_mod_cast (show 0 < 2 * D - 1 by omega)
              have hlogLe : Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) ≤
                  Real.logb 3 (2 * H + 1) :=
                Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
                  hargPos (by exact_mod_cast harg)
              calc
                (4 : ℝ) * C - H ≤
                    1 + 2 * Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) := by
                  rw [hrecCast]
                  have hnonposReal : (3 : ℝ) * D ≤ H := by exact_mod_cast hnonpos
                  linarith
                _ ≤ 1 + 2 * Real.logb 3 (2 * H + 1) := by
                  linarith
            · by_cases hone : 3 * D = H + 1
              · have honeReal : (3 : ℝ) * D = H + 1 := by exact_mod_cast hone
                have hscale : 2 * (2 * D - 1) ≤ 2 * H + 1 := by omega
                have hlogScale :
                    (1 / 2 : ℝ) + Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) ≤
                      Real.logb 3 (2 * H + 1) := by
                  calc
                    (1 / 2 : ℝ) + Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) ≤
                        Real.logb 3 2 +
                          Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) :=
                      by simpa [add_comm] using
                        add_le_add_right one_half_le_logb_three_two
                          (Real.logb 3 ((2 * D - 1 : ℕ) : ℝ))
                    _ = Real.logb 3 (2 * ((2 * D - 1 : ℕ) : ℝ)) :=
                      (Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
                        (by exact_mod_cast (show 2 * D - 1 ≠ 0 by omega))).symm
                    _ ≤ Real.logb 3 (2 * H + 1) :=
                      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
                        (by exact_mod_cast (show 0 < 2 * (2 * D - 1) by omega))
                        (by exact_mod_cast hscale)
                rw [hrecCast]
                linarith
              · have htwo : 3 * D = H + 2 := by omega
                have htwoReal : (3 : ℝ) * D = H + 2 := by exact_mod_cast htwo
                have hscale : 3 * (2 * D - 1) = 2 * H + 1 := by omega
                have hlogScale :
                    1 + Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) =
                      Real.logb 3 (2 * H + 1) := by
                  calc
                    1 + Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) =
                        Real.logb 3 3 +
                          Real.logb 3 ((2 * D - 1 : ℕ) : ℝ) := by
                      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
                    _ = Real.logb 3 (3 * ((2 * D - 1 : ℕ) : ℝ)) :=
                      (Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0)
                        (by exact_mod_cast (show 2 * D - 1 ≠ 0 by omega))).symm
                    _ = Real.logb 3 (2 * H + 1) := by
                      congr 2
                      exact_mod_cast hscale
                rw [hrecCast]
                linarith
          · by_cases hnonpos : H ≤ 3 * D
            · have harg : 2 * D + 1 ≤ 2 * H - 1 := by omega
              have hlogLe : Real.logb 3 (2 * D + 1) ≤
                  Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) :=
                Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
                  (by positivity) (by exact_mod_cast harg)
              calc
                (H : ℝ) - 4 * C ≤
                    1 + 2 * Real.logb 3 (2 * D + 1) := by
                  rw [hrecCast]
                  have hnonposReal : (H : ℝ) ≤ 3 * D := by exact_mod_cast hnonpos
                  linarith
                _ ≤ 1 + 2 * Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) := by
                  linarith
            · by_cases hone : H = 3 * D + 1
              · have honeReal : (H : ℝ) = 3 * D + 1 := by exact_mod_cast hone
                have hscale : 2 * (2 * D + 1) ≤ 2 * H - 1 := by omega
                have hlogScale :
                    (1 / 2 : ℝ) + Real.logb 3 (2 * D + 1) ≤
                      Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) := by
                  calc
                    (1 / 2 : ℝ) + Real.logb 3 (2 * D + 1) ≤
                        Real.logb 3 2 + Real.logb 3 (2 * D + 1) :=
                      by simpa [add_comm] using
                        add_le_add_right one_half_le_logb_three_two
                          (Real.logb 3 (2 * (D : ℝ) + 1))
                    _ = Real.logb 3 (2 * ((2 * D + 1 : ℕ) : ℝ)) := by
                      calc
                        Real.logb 3 2 + Real.logb 3 (2 * (D : ℝ) + 1) =
                            Real.logb 3 2 +
                              Real.logb 3 ((2 * D + 1 : ℕ) : ℝ) := by norm_num
                        _ = Real.logb 3 (2 * ((2 * D + 1 : ℕ) : ℝ)) :=
                          (Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
                            (by positivity : (((2 * D + 1 : ℕ) : ℝ)) ≠ 0)).symm
                    _ ≤ Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) :=
                      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
                        (by positivity) (by exact_mod_cast hscale)
                rw [hrecCast]
                linarith
              · have htwo : H = 3 * D + 2 := by omega
                have htwoReal : (H : ℝ) = 3 * D + 2 := by exact_mod_cast htwo
                have hscale : 3 * (2 * D + 1) = 2 * H - 1 := by omega
                have hlogScale :
                    1 + Real.logb 3 (2 * D + 1) =
                      Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) := by
                  calc
                    1 + Real.logb 3 (2 * D + 1) =
                        Real.logb 3 3 + Real.logb 3 (2 * D + 1) := by
                      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)]
                    _ = Real.logb 3 (3 * ((2 * D + 1 : ℕ) : ℝ)) := by
                      calc
                        Real.logb 3 3 + Real.logb 3 (2 * (D : ℝ) + 1) =
                            Real.logb 3 3 +
                              Real.logb 3 ((2 * D + 1 : ℕ) : ℝ) := by norm_num
                        _ = Real.logb 3 (3 * ((2 * D + 1 : ℕ) : ℝ)) :=
                          (Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0)
                            (by positivity : (((2 * D + 1 : ℕ) : ℝ)) ≠ 0)).symm
                    _ = Real.logb 3 ((2 * H - 1 : ℕ) : ℝ) := by
                      congr 2
                      exact_mod_cast hscale
                rw [hrecCast]
                linarith
/-- Offset-indexed and interval-indexed odd-valuation counts agree. -/
theorem card_filter_odd_two_factorization_offsets (N H : ℕ) :
    ((Finset.range H).filter fun i =>
      Odd ((N + (i + 1)).factorization 2)).card =
      (oddTwoValuationInterval N H).card := by
  apply Finset.card_bij (fun i _ => N + (i + 1))
  · intro i hi
    rw [Finset.mem_filter] at hi
    change N + (i + 1) ∈
      (Finset.Ioc N (N + H)).filter fun m => Odd (m.factorization 2)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hi.1
      omega⟩, hi.2⟩
  · intro i hi j hj hij
    omega
  · intro m hm
    rw [oddTwoValuationInterval, Finset.mem_filter] at hm
    have hmBounds := Finset.mem_Ioc.mp hm.1
    refine ⟨m - N - 1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hval : N + (m - N - 1 + 1) = m := by omega
      simpa [hval] using hm.2
    · omega

private theorem powerFreePart_two_factorization_eq_indicator_odd
    (m p : ℕ) (hp : p = 2) :
    (powerFreePart 2 m).factorization p =
      if Odd (m.factorization 2) then 1 else 0 := by
  subst p
  rw [factorization_powerFreePart, powerFreeFactorization,
    Finsupp.mapRange_apply]
  by_cases hodd : Odd (m.factorization 2)
  · rw [if_pos hodd]
    exact Nat.odd_iff.mp hodd
  · rw [if_neg hodd]
    have hmod := Nat.mod_lt (m.factorization 2) (by omega : 0 < 2)
    rw [Nat.odd_iff] at hodd
    omega

/-- The 2-adic valuation of the canonical squarefree coefficient product is
exactly the number of interval elements having odd 2-adic valuation. -/
theorem factorization_erdosSelfridgeSquareCoefficientProduct_two (N H : ℕ) :
    (erdosSelfridgeSquareCoefficientProduct N H).factorization 2 =
      (oddTwoValuationInterval N H).card := by
  rw [erdosSelfridgeSquareCoefficientProduct, Nat.factorization_prod_apply]
  · calc
      (∑ i ∈ Finset.range H,
          (powerFreePart 2 (N + (i + 1))).factorization 2) =
          ∑ i ∈ Finset.range H,
            if Odd ((N + (i + 1)).factorization 2) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact powerFreePart_two_factorization_eq_indicator_odd _ 2 rfl
      _ = ((Finset.range H).filter fun i =>
          Odd ((N + (i + 1)).factorization 2)).card := by
            exact Finset.sum_boole _ _
      _ = (oddTwoValuationInterval N H).card :=
        card_filter_odd_two_factorization_offsets N H
  · intro i hi
    exact powerFreePart_ne_zero _ _

/-- The paper's upper estimate
`γ ≤ (H + log₂(3H+1))/3` for the power `γ` of `2` in the product of the
canonical squarefree coefficients. -/
theorem factorization_squareCoefficientProduct_two_source_upper
    {N H : ℕ} (hH : 1 ≤ H) :
    (((erdosSelfridgeSquareCoefficientProduct N H).factorization 2 : ℕ) : ℝ) ≤
      ((H : ℝ) + Real.logb 2 (3 * H + 1)) / 3 := by
  have hupper := (oddTwoValuationInterval_discrepancy H hH N).1
  rw [factorization_erdosSelfridgeSquareCoefficientProduct_two]
  linarith

theorem card_filter_odd_three_factorization_offsets (N H : ℕ) :
    ((Finset.range H).filter fun i =>
      Odd ((N + (i + 1)).factorization 3)).card =
      (oddThreeValuationInterval N H).card := by
  apply Finset.card_bij (fun i _ => N + (i + 1))
  · intro i hi
    rw [Finset.mem_filter] at hi
    change N + (i + 1) ∈
      (Finset.Ioc N (N + H)).filter fun m => Odd (m.factorization 3)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hi.1
      omega⟩, hi.2⟩
  · intro i hi j hj hij
    omega
  · intro m hm
    rw [oddThreeValuationInterval, Finset.mem_filter] at hm
    have hmBounds := Finset.mem_Ioc.mp hm.1
    refine ⟨m - N - 1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      have hval : N + (m - N - 1 + 1) = m := by omega
      simpa [hval] using hm.2
    · omega

private theorem powerFreePart_two_factorization_three_eq_indicator_odd
    (m : ℕ) :
    (powerFreePart 2 m).factorization 3 =
      if Odd (m.factorization 3) then 1 else 0 := by
  rw [factorization_powerFreePart, powerFreeFactorization,
    Finsupp.mapRange_apply]
  by_cases hodd : Odd (m.factorization 3)
  · rw [if_pos hodd]
    exact Nat.odd_iff.mp hodd
  · rw [if_neg hodd]
    have hmod := Nat.mod_lt (m.factorization 3) (by omega : 0 < 2)
    rw [Nat.odd_iff] at hodd
    omega

/-- The analogous exact count for the 3-adic coefficient-product
valuation. -/
theorem factorization_erdosSelfridgeSquareCoefficientProduct_three (N H : ℕ) :
    (erdosSelfridgeSquareCoefficientProduct N H).factorization 3 =
      (oddThreeValuationInterval N H).card := by
  rw [erdosSelfridgeSquareCoefficientProduct, Nat.factorization_prod_apply]
  · calc
      (∑ i ∈ Finset.range H,
          (powerFreePart 2 (N + (i + 1))).factorization 3) =
          ∑ i ∈ Finset.range H,
            if Odd ((N + (i + 1)).factorization 3) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact powerFreePart_two_factorization_three_eq_indicator_odd _
      _ = ((Finset.range H).filter fun i =>
          Odd ((N + (i + 1)).factorization 3)).card := by
            exact Finset.sum_boole _ _
      _ = (oddThreeValuationInterval N H).card :=
        card_filter_odd_three_factorization_offsets N H
  · intro i hi
    exact powerFreePart_ne_zero _ _

/-- The paper's upper estimate
`δ ≤ (H+1+2 log₃(2H+1))/4` for the power `δ` of `3` in the product of the
canonical squarefree coefficients. -/
theorem factorization_squareCoefficientProduct_three_source_upper
    {N H : ℕ} (hH : 1 ≤ H) :
    (((erdosSelfridgeSquareCoefficientProduct N H).factorization 3 : ℕ) : ℝ) ≤
      ((H : ℝ) + 1 + 2 * Real.logb 3 (2 * H + 1)) / 4 := by
  have hupper := (oddThreeValuationInterval_discrepancy H hH N).1
  rw [factorization_erdosSelfridgeSquareCoefficientProduct_three]
  linarith

/-- Each prime below `H` occurs exactly once in the squarefree primorial used
in equation (21). -/
theorem factorization_erdosSelfridgePrimeProduct_eq_one
    {H p : ℕ} (hp : p.Prime) (hpH : p < H) :
    (erdosSelfridgePrimeProduct H).factorization p = 1 := by
  rw [erdosSelfridgePrimeProduct, Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single p]
    · exact hp.factorization_self
    · intro q hq hqp
      have hqPrime : q.Prime := (Nat.mem_primesBelow.mp hq).2
      simp [hqPrime, hqp]
    · intro hpNotMem
      exact (hpNotMem (Nat.mem_primesBelow.mpr ⟨hpH, hp⟩)).elim
  · intro q hq
    exact (Nat.mem_primesBelow.mp hq).2.ne_zero

private theorem factorization_mul_pow_mul_pow
    {n b c e f p : ℕ} (hn : n ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (n * b ^ e * c ^ f).factorization p =
      n.factorization p + e * b.factorization p + f * c.factorization p := by
  rw [Nat.factorization_mul
      (mul_ne_zero hn (pow_ne_zero e hb)) (pow_ne_zero f hc),
    Nat.factorization_mul hn (pow_ne_zero e hb),
    Nat.factorization_pow, Nat.factorization_pow]
  simp [Pi.add_apply]

/-- Equation (21) with the complete 2- and 3-adic content exposed.  This is
the exact integer inequality used before the paper replaces all four
valuations by elementary logarithmic bounds. -/
theorem erdosSelfridge_equation21_two_three_valuation_ledger
    {N H : ℕ} (hH : 4 ≤ H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    erdosSelfridgeSquareCoefficientProduct N H *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1) ∣
      ((H - 1).factorial * erdosSelfridgePrimeProduct H) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) := by
  have hcoeffDvd : erdosSelfridgeSquareCoefficientProduct N H ∣
      (H - 1).factorial * erdosSelfridgePrimeProduct H := by
    exact product_powerFreePart_two_dvd_factorial_mul_primeProduct
      (by omega) hfail
  have hleft0 : erdosSelfridgeSquareCoefficientProduct N H *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (erdosSelfridgeSquareCoefficientProduct_pos N H).ne'
        (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by norm_num))
  have hright0 : ((H - 1).factorial * erdosSelfridgePrimeProduct H) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (Nat.factorial_ne_zero _)
          (erdosSelfridgePrimeProduct_pos H).ne')
        (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (by norm_num))
  rw [← Nat.factorization_le_iff_dvd hleft0 hright0]
  intro p
  by_cases hp : p.Prime
  · have hbase := (Nat.factorization_le_iff_dvd
        (erdosSelfridgeSquareCoefficientProduct_pos N H).ne'
        (mul_ne_zero (Nat.factorial_ne_zero _)
          (erdosSelfridgePrimeProduct_pos H).ne')).mpr hcoeffDvd p
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _)
      (erdosSelfridgePrimeProduct_pos H).ne', Finsupp.coe_add, Pi.add_apply] at hbase
    by_cases hp2 : p = 2
    · subst p
      have hprimeTwo : (2 : ℕ).Prime := by norm_num
      have hprimorialTwo :
          (erdosSelfridgePrimeProduct H).factorization 2 = 1 :=
        factorization_erdosSelfridgePrimeProduct_eq_one hprimeTwo (by omega)
      have hthreeTwo : (3 : ℕ).factorization 2 = 0 := by
        simp [Nat.Prime.factorization (by norm_num : (3 : ℕ).Prime)]
      rw [factorization_mul_pow_mul_pow
          (erdosSelfridgeSquareCoefficientProduct_pos N H).ne'
          (by norm_num) (by norm_num),
        factorization_mul_pow_mul_pow
          (mul_ne_zero (Nat.factorial_ne_zero _)
            (erdosSelfridgePrimeProduct_pos H).ne')
          (by norm_num) (by norm_num),
        Nat.factorization_mul (Nat.factorial_ne_zero _)
          (erdosSelfridgePrimeProduct_pos H).ne',
        Finsupp.coe_add, Pi.add_apply,
        hprimeTwo.factorization_self, hprimorialTwo, hthreeTwo]
      omega
    · by_cases hp3 : p = 3
      · subst p
        have hprimeThree : (3 : ℕ).Prime := by norm_num
        have hprimorialThree :
            (erdosSelfridgePrimeProduct H).factorization 3 = 1 :=
          factorization_erdosSelfridgePrimeProduct_eq_one hprimeThree (by omega)
        have htwoThree : (2 : ℕ).factorization 3 = 0 := by
          simp [Nat.Prime.factorization (by norm_num : (2 : ℕ).Prime)]
        rw [factorization_mul_pow_mul_pow
            (erdosSelfridgeSquareCoefficientProduct_pos N H).ne'
            (by norm_num) (by norm_num),
          factorization_mul_pow_mul_pow
            (mul_ne_zero (Nat.factorial_ne_zero _)
              (erdosSelfridgePrimeProduct_pos H).ne')
            (by norm_num) (by norm_num),
          Nat.factorization_mul (Nat.factorial_ne_zero _)
            (erdosSelfridgePrimeProduct_pos H).ne',
          Finsupp.coe_add, Pi.add_apply,
          hprimeThree.factorization_self, hprimorialThree, htwoThree]
        omega
      · rw [factorization_mul_pow_mul_pow
            (erdosSelfridgeSquareCoefficientProduct_pos N H).ne'
            (by norm_num) (by norm_num),
          factorization_mul_pow_mul_pow
            (mul_ne_zero (Nat.factorial_ne_zero _)
              (erdosSelfridgePrimeProduct_pos H).ne')
            (by norm_num) (by norm_num),
          Nat.factorization_mul (Nat.factorial_ne_zero _)
            (erdosSelfridgePrimeProduct_pos H).ne',
          Finsupp.coe_add, Pi.add_apply]
        have hpFacTwo : (2 : ℕ).factorization p = 0 := by
          simp [Nat.Prime.factorization (by norm_num : (2 : ℕ).Prime), hp2]
        have hpFacThree : (3 : ℕ).factorization p = 0 := by
          simp [Nat.Prime.factorization (by norm_num : (3 : ℕ).Prime), hp3]
        simp only [hpFacTwo, hpFacThree, mul_zero, add_zero]
        exact hbase
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Combining the cleared-denominator equation (22) with the exact valuation
ledger.  This is equation (23) before inserting the paper's four estimates for
the valuations and simplifying their logarithmic remainders. -/
theorem powerFreePart_two_preEquation23_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (3 ^ H * H.factorial) *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1) <
      (2 ^ H * ((H - 1).factorial * erdosSelfridgePrimeProduct H)) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) := by
  have h22 := powerFreePart_two_equation22_of_failure hSS hH hHN hfail
  change 3 ^ H * H.factorial <
    2 ^ H * erdosSelfridgeSquareCoefficientProduct N H at h22
  have hledgerDvd :=
    erdosSelfridge_equation21_two_three_valuation_ledger (by omega) hfail
  have hledgerRightPos :
      0 < ((H - 1).factorial * erdosSelfridgePrimeProduct H) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) := by
    exact mul_pos
      (mul_pos
        (mul_pos (Nat.factorial_pos _) (erdosSelfridgePrimeProduct_pos H))
        (pow_pos (by norm_num) _))
      (pow_pos (by norm_num) _)
  have hledgerLe := Nat.le_of_dvd hledgerRightPos hledgerDvd
  have hscalePos :
      0 < 2 ^ ((H - 1).factorial.factorization 2 + 1) *
        3 ^ ((H - 1).factorial.factorization 3 + 1) := by positivity
  have hscaled := Nat.mul_lt_mul_of_pos_right h22 hscalePos
  calc
    (3 ^ H * H.factorial) *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1) =
        (3 ^ H * H.factorial) *
          (2 ^ ((H - 1).factorial.factorization 2 + 1) *
            3 ^ ((H - 1).factorial.factorization 3 + 1)) := by ring
    _ < (2 ^ H * erdosSelfridgeSquareCoefficientProduct N H) *
          (2 ^ ((H - 1).factorial.factorization 2 + 1) *
            3 ^ ((H - 1).factorial.factorization 3 + 1)) := hscaled
    _ = 2 ^ H *
        (erdosSelfridgeSquareCoefficientProduct N H *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1)) := by ring
    _ ≤ 2 ^ H *
        (((H - 1).factorial * erdosSelfridgePrimeProduct H) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3)) :=
      Nat.mul_le_mul_left _ hledgerLe
    _ = (2 ^ H * ((H - 1).factorial * erdosSelfridgePrimeProduct H)) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) := by ring

/-- The exact real-valued form of the pre-equation-(23) ledger after
cancelling `(H-1)!`.  The exponents are still natural-number valuations; this
is the algebraic bridge on which the four source estimates act. -/
theorem powerFreePart_two_preEquation23_real_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    ((3 : ℝ) ^ H * H) *
          (2 : ℝ) ^ ((H - 1).factorial.factorization 2 + 1) *
          (3 : ℝ) ^ ((H - 1).factorial.factorization 3 + 1) <
      ((2 : ℝ) ^ H * erdosSelfridgePrimeProduct H) *
          (2 : ℝ) ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          (3 : ℝ) ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) := by
  have hpre := powerFreePart_two_preEquation23_of_failure hSS hH hHN hfail
  have hpreReal :
      (((3 ^ H * H.factorial) *
          2 ^ ((H - 1).factorial.factorization 2 + 1) *
          3 ^ ((H - 1).factorial.factorization 3 + 1) : ℕ) : ℝ) <
        (((2 ^ H * ((H - 1).factorial * erdosSelfridgePrimeProduct H)) *
          2 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
          3 ^ ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3) : ℕ) : ℝ) := by
    exact_mod_cast hpre
  have hHpos : 0 < H := by omega
  have hfactorial : H.factorial = H * (H - 1).factorial := by
    calc
      H.factorial = (H - 1 + 1).factorial := by
        congr 1
        omega
      _ = (H - 1 + 1) * (H - 1).factorial := Nat.factorial_succ _
      _ = H * (H - 1).factorial := by
        congr 1
        omega
  rw [hfactorial] at hpreReal
  norm_num only [Nat.cast_mul, Nat.cast_pow] at hpreReal
  have hfacPos : (0 : ℝ) < ((H - 1).factorial : ℕ) := by positivity
  have hscaled :
      (((H - 1).factorial : ℕ) : ℝ) *
          (((3 : ℝ) ^ H * H) *
            (2 : ℝ) ^ ((H - 1).factorial.factorization 2 + 1) *
            (3 : ℝ) ^ ((H - 1).factorial.factorization 3 + 1)) <
        (((H - 1).factorial : ℕ) : ℝ) *
          (((2 : ℝ) ^ H * erdosSelfridgePrimeProduct H) *
            (2 : ℝ) ^
              ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
            (3 : ℝ) ^
              ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3)) := by
    convert hpreReal using 1 <;> ring
  exact lt_of_mul_lt_mul_left hscaled hfacPos.le

/-- The preceding real inequality with the powers on the right divided out.
This is the exact multiplicative shape used when the valuation estimates are
inserted. -/
theorem powerFreePart_two_preEquation23_ratio_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (H : ℝ) * (((3 : ℝ) / 2) ^ H) *
          ((2 : ℝ) ^ ((H - 1).factorial.factorization 2 + 1) /
            (2 : ℝ) ^
              ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2)) *
          ((3 : ℝ) ^ ((H - 1).factorial.factorization 3 + 1) /
            (3 : ℝ) ^
              ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3)) <
      erdosSelfridgePrimeProduct H := by
  have hreal :=
    powerFreePart_two_preEquation23_real_of_failure hSS hH hHN hfail
  let D : ℝ :=
    (2 : ℝ) ^ H *
      (2 : ℝ) ^
        ((erdosSelfridgeSquareCoefficientProduct N H).factorization 2) *
      (3 : ℝ) ^
        ((erdosSelfridgeSquareCoefficientProduct N H).factorization 3)
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hscaled :
      ((3 : ℝ) ^ H * H) *
          (2 : ℝ) ^ ((H - 1).factorial.factorization 2 + 1) *
          (3 : ℝ) ^ ((H - 1).factorial.factorization 3 + 1) <
        (erdosSelfridgePrimeProduct H : ℝ) * D := by
    convert hreal using 1
    all_goals
      dsimp only [D]
      ring
  have hdiv := (div_lt_iff₀ hDpos).mpr hscaled
  convert hdiv using 1
  dsimp only [D]
  rw [div_pow]
  field_simp

/-- The exact source-shaped real-exponent form before estimating the four
valuations. -/
theorem powerFreePart_two_preEquation23_rpow_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (H : ℝ) * (((3 : ℝ) / 2) ^ (H : ℝ)) *
          (2 : ℝ) ^
            (((((H - 1).factorial.factorization 2 + 1 : ℕ) : ℝ)) -
              (((erdosSelfridgeSquareCoefficientProduct N H).factorization 2 : ℕ) : ℝ)) *
          (3 : ℝ) ^
            (((((H - 1).factorial.factorization 3 + 1 : ℕ) : ℝ)) -
              (((erdosSelfridgeSquareCoefficientProduct N H).factorization 3 : ℕ) : ℝ)) <
      erdosSelfridgePrimeProduct H := by
  have hratio :=
    powerFreePart_two_preEquation23_ratio_of_failure hSS hH hHN hfail
  rw [Real.rpow_natCast]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
  norm_num only [Real.rpow_natCast]
  exact hratio

/-- Inserting all four valuation estimates gives the logarithmic form directly
preceding the numerical simplification to the constant `14/3` in equation
(23). -/
theorem powerFreePart_two_preEquation23_logarithmic_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (H : ℝ) * (((3 : ℝ) / 2) ^ (H : ℝ)) *
          (2 : ℝ) ^
            ((2 * (H : ℝ)) / 3 - Real.logb 2 H -
              Real.logb 2 (3 * (H : ℝ) + 1) / 3) *
          (3 : ℝ) ^
            ((H : ℝ) / 4 + 1 / 4 - Real.logb 3 H -
              Real.logb 3 (2 * (H : ℝ) + 1) / 2) <
      erdosSelfridgePrimeProduct H := by
  have hrpow :=
    powerFreePart_two_preEquation23_rpow_of_failure hSS hH hHN hfail
  have hHone : 1 ≤ H := by omega
  have htwoLower := factorization_factorial_two_source_lower hHone
  have hthreeLower := factorization_factorial_three_source_lower hHone
  have htwoUpper :=
    factorization_squareCoefficientProduct_two_source_upper
      (N := N) hHone
  have hthreeUpper :=
    factorization_squareCoefficientProduct_three_source_upper
      (N := N) hHone
  have hcastSub : (((H - 1 : ℕ) : ℝ) + 1) = H := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have htwoExponent :
      (2 * (H : ℝ)) / 3 - Real.logb 2 H -
          Real.logb 2 (3 * (H : ℝ) + 1) / 3 ≤
        ((((H - 1).factorial.factorization 2 + 1 : ℕ) : ℝ)) -
          (((erdosSelfridgeSquareCoefficientProduct N H).factorization 2 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    norm_num only [Nat.cast_ofNat] at htwoLower htwoUpper
    linarith
  have hthreeExponent :
      (H : ℝ) / 4 + 1 / 4 - Real.logb 3 H -
          Real.logb 3 (2 * (H : ℝ) + 1) / 2 ≤
        ((((H - 1).factorial.factorization 3 + 1 : ℕ) : ℝ)) -
          (((erdosSelfridgeSquareCoefficientProduct N H).factorization 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    norm_num only [Nat.cast_ofNat] at hthreeLower hthreeUpper
    linarith
  have hpowTwo := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) htwoExponent
  have hpowThree := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) hthreeExponent
  apply lt_of_le_of_lt _ hrpow
  gcongr

/-- The elementary root estimate which accounts for the numerical constant in
equation (23).  It is deliberately proved with slack: the root factor is at
most `4H²`, while the source records `(14/3)H²`. -/
theorem erdosSelfridge_equation23_root_factor_le {H : ℕ} (hH : 1 ≤ H) :
    (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
          (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) /
          (3 : ℝ) ^ (1 / 4 : ℝ) ≤
      (14 / 3 : ℝ) * (H : ℝ) ^ 2 := by
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hfirstBase : (3 : ℝ) * H + 1 ≤ 4 * H := by linarith
  have hsecondBase : (2 : ℝ) * H + 1 ≤ 3 * H := by linarith
  have hfourRoot : (4 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
    calc
      (4 : ℝ) ^ (1 / 3 : ℝ) ≤ 4 ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
  have hthreeRoot : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hfirst :
      (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) ≤
        2 * (H : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) ≤
          (4 * (H : ℝ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hfirstBase (by norm_num)
      _ = (4 : ℝ) ^ (1 / 3 : ℝ) *
          (H : ℝ) ^ (1 / 3 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (H : ℝ) ^ (1 / 3 : ℝ) := by gcongr
  have hsecond :
      (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) ≤
        2 * (H : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) ≤
          (3 * (H : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hsecondBase (by norm_num)
      _ = (3 : ℝ) ^ (1 / 2 : ℝ) *
          (H : ℝ) ^ (1 / 2 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (H : ℝ) ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hthreeRoot
          (Real.rpow_nonneg (by positivity) _)
  have hHPowers :
      (H : ℝ) ^ (1 / 3 : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) ≤ H := by
    calc
      (H : ℝ) ^ (1 / 3 : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) =
          (H : ℝ) ^ ((1 / 3 : ℝ) + 1 / 2) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ ≤ (H : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hHreal (by norm_num)
      _ = H := Real.rpow_one _
  have hnumerator :
      (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
          (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) ≤
        4 * (H : ℝ) ^ 2 := by
    calc
      (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
          (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) ≤
          (H : ℝ) * (2 * (H : ℝ) ^ (1 / 3 : ℝ)) *
            (2 * (H : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
      _ = 4 * (H : ℝ) *
          ((H : ℝ) ^ (1 / 3 : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ 4 * (H : ℝ) * H := by gcongr
      _ = 4 * (H : ℝ) ^ 2 := by ring
  have hdenomOne : (1 : ℝ) ≤ (3 : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
          (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) /
          (3 : ℝ) ^ (1 / 4 : ℝ) ≤
        (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
          (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) := by
      exact div_le_self (by positivity) hdenomOne
    _ ≤ 4 * (H : ℝ) ^ 2 := hnumerator
    _ ≤ (14 / 3 : ℝ) * (H : ℝ) ^ 2 := by nlinarith [sq_nonneg (H : ℝ)]

private theorem two_logarithmic_power_eq {H : ℕ} (hH : 1 ≤ H) :
    (2 : ℝ) ^
        ((2 * (H : ℝ)) / 3 - Real.logb 2 H -
          Real.logb 2 (3 * (H : ℝ) + 1) / 3) =
      (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) /
        ((H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ)) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  have hXpos : (0 : ℝ) < 3 * H + 1 := by positivity
  have hlogH : (2 : ℝ) ^ Real.logb 2 H = H :=
    Real.rpow_logb (by norm_num) (by norm_num) hHpos
  have hlogX :
      (2 : ℝ) ^ (Real.logb 2 (3 * (H : ℝ) + 1) / 3) =
        (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) := by
    calc
      (2 : ℝ) ^ (Real.logb 2 (3 * (H : ℝ) + 1) / 3) =
          (2 : ℝ) ^ (Real.logb 2 (3 * (H : ℝ) + 1) * (1 / 3 : ℝ)) := by
            congr 1
            ring
      _ = ((2 : ℝ) ^ Real.logb 2 (3 * (H : ℝ) + 1)) ^
          (1 / 3 : ℝ) := Real.rpow_mul (by norm_num) _ _
      _ = (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hXpos]
  calc
    (2 : ℝ) ^
        ((2 * (H : ℝ)) / 3 - Real.logb 2 H -
          Real.logb 2 (3 * (H : ℝ) + 1) / 3) =
        (2 : ℝ) ^ ((2 * (H : ℝ)) / 3 -
          (Real.logb 2 H + Real.logb 2 (3 * (H : ℝ) + 1) / 3)) := by
            congr 1
            ring
    _ = (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) /
        (2 : ℝ) ^
          (Real.logb 2 H + Real.logb 2 (3 * (H : ℝ) + 1) / 3) :=
      Real.rpow_sub (by norm_num) _ _
    _ = (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) /
        ((2 : ℝ) ^ Real.logb 2 H *
          (2 : ℝ) ^ (Real.logb 2 (3 * (H : ℝ) + 1) / 3)) := by
      rw [Real.rpow_add (by norm_num)]
    _ = (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) /
        ((H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ)) := by
      rw [hlogH, hlogX]

private theorem three_logarithmic_power_eq {H : ℕ} (hH : 1 ≤ H) :
    (3 : ℝ) ^
        ((H : ℝ) / 4 + 1 / 4 - Real.logb 3 H -
          Real.logb 3 (2 * (H : ℝ) + 1) / 2) =
      ((3 : ℝ) ^ ((H : ℝ) / 4) * (3 : ℝ) ^ (1 / 4 : ℝ)) /
        ((H : ℝ) * (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  have hXpos : (0 : ℝ) < 2 * H + 1 := by positivity
  have hlogH : (3 : ℝ) ^ Real.logb 3 H = H :=
    Real.rpow_logb (by norm_num) (by norm_num) hHpos
  have hlogX :
      (3 : ℝ) ^ (Real.logb 3 (2 * (H : ℝ) + 1) / 2) =
        (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    calc
      (3 : ℝ) ^ (Real.logb 3 (2 * (H : ℝ) + 1) / 2) =
          (3 : ℝ) ^ (Real.logb 3 (2 * (H : ℝ) + 1) * (1 / 2 : ℝ)) := by
            congr 1
            ring
      _ = ((3 : ℝ) ^ Real.logb 3 (2 * (H : ℝ) + 1)) ^
          (1 / 2 : ℝ) := Real.rpow_mul (by norm_num) _ _
      _ = (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hXpos]
  calc
    (3 : ℝ) ^
        ((H : ℝ) / 4 + 1 / 4 - Real.logb 3 H -
          Real.logb 3 (2 * (H : ℝ) + 1) / 2) =
        (3 : ℝ) ^ (((H : ℝ) / 4 + 1 / 4) -
          (Real.logb 3 H + Real.logb 3 (2 * (H : ℝ) + 1) / 2)) := by
            congr 1
            ring
    _ = (3 : ℝ) ^ ((H : ℝ) / 4 + 1 / 4) /
        (3 : ℝ) ^
          (Real.logb 3 H + Real.logb 3 (2 * (H : ℝ) + 1) / 2) :=
      Real.rpow_sub (by norm_num) _ _
    _ = ((3 : ℝ) ^ ((H : ℝ) / 4) * (3 : ℝ) ^ (1 / 4 : ℝ)) /
        ((3 : ℝ) ^ Real.logb 3 H *
          (3 : ℝ) ^ (Real.logb 3 (2 * (H : ℝ) + 1) / 2)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
    _ = ((3 : ℝ) ^ ((H : ℝ) / 4) * (3 : ℝ) ^ (1 / 4 : ℝ)) /
        ((H : ℝ) * (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
      rw [hlogH, hlogX]

/-- Erdős--Selfridge equation (23), with its source constant `14/3`, for the
canonical coefficient family attached to a putative square-case
counterexample. -/
theorem erdosSelfridge_equation23_of_failure
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hH : 64 ≤ H) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H 2) :
    (((3 : ℝ) / 2) ^ (H : ℝ)) *
          (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) *
          (3 : ℝ) ^ ((H : ℝ) / 4) <
      (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H := by
  have hHone : 1 ≤ H := by omega
  have hlog :=
    powerFreePart_two_preEquation23_logarithmic_of_failure hSS hH hHN hfail
  rw [two_logarithmic_power_eq hHone,
    three_logarithmic_power_eq hHone] at hlog
  let M : ℝ :=
    (((3 : ℝ) / 2) ^ (H : ℝ)) *
      (2 : ℝ) ^ ((2 * (H : ℝ)) / 3) *
      (3 : ℝ) ^ ((H : ℝ) / 4)
  let R : ℝ :=
    (H : ℝ) * (3 * (H : ℝ) + 1) ^ (1 / 3 : ℝ) *
      (2 * (H : ℝ) + 1) ^ (1 / 2 : ℝ) /
      (3 : ℝ) ^ (1 / 4 : ℝ)
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hquotient : M / R < erdosSelfridgePrimeProduct H := by
    convert hlog using 1
    dsimp only [M, R]
    field_simp
  have hmainLt : M < (erdosSelfridgePrimeProduct H : ℝ) * R :=
    (div_lt_iff₀ hRpos).mp hquotient
  have hroot := erdosSelfridge_equation23_root_factor_le hHone
  change M < (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H
  calc
    M < (erdosSelfridgePrimeProduct H : ℝ) * R := hmainLt
    _ ≤ (erdosSelfridgePrimeProduct H : ℝ) *
        ((14 / 3 : ℝ) * (H : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H := by ring

end Tao2026
