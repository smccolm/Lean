import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Chebyshev
import Tao2026.SmoothNumbers

/-!
# Exact Hildebrand identities for smooth numbers

This file supplies the finite arithmetic identities that precede the analytic
de Bruijn--Hildebrand iteration.  In particular, multiplication by a smooth
prime power identifies smooth cofactors with smooth multiples, and the
resulting divisor counts can be inserted into the factorization formula for
`Real.log`.
-/

namespace Tao2026

/-- The `y`-smooth numbers up to `X` which are divisible by `q`. -/
def smoothDivisibleNumbers (X y q : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo X (y + 1)).filter (q ∣ ·)

theorem mem_smoothDivisibleNumbers {X y q n : ℕ} :
    n ∈ smoothDivisibleNumbers X y q ↔ n ≤ X ∧ IsSmooth n y ∧ q ∣ n := by
  simp only [smoothDivisibleNumbers, Finset.mem_filter,
    mem_smoothNumbersUpTo_source]
  tauto

/-- Multiplication by a nonzero smooth number parametrizes the smooth
multiples up to `X` by their smooth cofactors. -/
theorem image_mul_smoothNumbersUpTo {X y q : ℕ}
    (hq0 : q ≠ 0) (hqSmooth : IsSmooth q y) :
    (Nat.smoothNumbersUpTo (X / q) (y + 1)).image (q * ·) =
      smoothDivisibleNumbers X y q := by
  classical
  ext n
  constructor
  · rw [Finset.mem_image]
    rintro ⟨m, hm, rfl⟩
    rw [mem_smoothNumbersUpTo_source] at hm
    rw [mem_smoothDivisibleNumbers]
    refine ⟨?_, ?_, dvd_mul_right q m⟩
    · simpa only [mul_comm] using
        (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq0)).mp hm.1
    · exact Nat.mul_mem_smoothNumbers hqSmooth hm.2
  · rw [mem_smoothDivisibleNumbers]
    rintro ⟨hnX, hnSmooth, hqDvd⟩
    rw [Finset.mem_image]
    refine ⟨n / q, ?_, Nat.mul_div_cancel' hqDvd⟩
    rw [mem_smoothNumbersUpTo_source]
    refine ⟨Nat.div_le_div_right hnX, ?_⟩
    exact Nat.mem_smoothNumbers_of_dvd hnSmooth (Nat.div_dvd_of_dvd hqDvd)

/-- Exact count of smooth multiples of a nonzero smooth number. -/
theorem card_smoothDivisibleNumbers {X y q : ℕ}
    (hq0 : q ≠ 0) (hqSmooth : IsSmooth q y) :
    (smoothDivisibleNumbers X y q).card = psiNat (X / q) y := by
  rw [← image_mul_smoothNumbersUpTo hq0 hqSmooth]
  calc
    ((Nat.smoothNumbersUpTo (X / q) (y + 1)).image (q * ·)).card =
        (Nat.smoothNumbersUpTo (X / q) (y + 1)).card :=
      Finset.card_image_iff.mpr (by
        intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq0) hab)
    _ = psiNat (X / q) y := rfl

/-- Every positive power of a prime at most `y` is `y`-smooth. -/
theorem primePow_isSmooth {p a y : ℕ} (hp : p.Prime) (hpY : p ≤ y) :
    IsSmooth (p ^ a) y := by
  rw [isSmooth_iff]
  refine ⟨pow_ne_zero _ hp.ne_zero, ?_⟩
  intro q hq hqDvd
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqDvd)
  simpa [hqp] using hpY

/-- Prime-power divisibility inside the smooth set has the expected exact
cofactor count. -/
theorem card_smoothDivisibleNumbers_primePow {X y p a : ℕ}
    (hp : p.Prime) (hpY : p ≤ y) :
    (smoothDivisibleNumbers X y (p ^ a)).card = psiNat (X / p ^ a) y :=
  card_smoothDivisibleNumbers (pow_ne_zero _ hp.ne_zero) (primePow_isSmooth hp hpY)

/-- For a `y`-smooth number, the factorization formula for its logarithm may
be summed over the fixed finite set of primes at most `y`. -/
theorem log_nat_eq_sum_primesLE_factorization {n y : ℕ} (hn : IsSmooth n y) :
    Real.log n =
      ∑ p ∈ y.primesLE, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · simpa [Nat.primesLE] using
      (Nat.primeFactors_subset_of_mem_smoothNumbers hn)
  · intro p _ hpNot
    rw [Finsupp.notMem_support_iff.mp hpNot]
    norm_num

/-- On numbers up to `X`, a prime multiplicity is the number of its positive
powers up to `X` which divide the number. -/
theorem factorization_eq_card_Icc_pow_dvd {n X p : ℕ}
    (hp : p.Prime) (hn0 : n ≠ 0) (hnX : n ≤ X) :
    n.factorization p = ((Finset.Icc 1 X).filter (p ^ · ∣ n)).card := by
  rw [Nat.factorization_eq_card_pow_dvd n hp]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨ha1, han⟩, hdiv⟩
    exact ⟨⟨ha1, han.le.trans hnX⟩, hdiv⟩
  · rintro ⟨⟨ha1, _⟩, hdiv⟩
    exact ⟨⟨ha1, Nat.lt_of_pow_dvd_right hn0 hp.two_le hdiv⟩, hdiv⟩

/-- Exact double-counting identity for the total multiplicity of a fixed
prime in the `y`-smooth numbers up to `X`. -/
theorem sum_smooth_factorization_eq_sum_psiNat {X y p : ℕ}
    (hp : p.Prime) (hpY : p ≤ y) :
    ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), n.factorization p =
      ∑ a ∈ Finset.Icc 1 X, psiNat (X / p ^ a) y := by
  classical
  calc
    ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), n.factorization p =
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          ((Finset.Icc 1 X).filter (p ^ · ∣ n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mem_smoothNumbersUpTo_source] at hn
      exact factorization_eq_card_Icc_pow_dvd hp
        (isSmooth_iff.mp hn.2).1 hn.1
    _ = ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          ∑ a ∈ Finset.Icc 1 X, if p ^ a ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      exact (Finset.sum_boole (p ^ · ∣ n) (Finset.Icc 1 X)).symm
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
            if p ^ a ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 X,
          (smoothDivisibleNumbers X y (p ^ a)).card := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_boole (p ^ a ∣ ·)
        (Nat.smoothNumbersUpTo X (y + 1))
    _ = ∑ a ∈ Finset.Icc 1 X, psiNat (X / p ^ a) y := by
      apply Finset.sum_congr rfl
      intro a _
      exact card_smoothDivisibleNumbers_primePow hp hpY

/-- Logarithmic weight of all `y`-smooth numbers up to `X`. -/
noncomputable def smoothLogSum (X y : ℕ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), Real.log n

/-- The prime-power side of the exact Chebyshev--Hildebrand identity. -/
noncomputable def smoothPrimePowerPsiSum (X y : ℕ) : ℝ :=
  ∑ p ∈ y.primesLE, Real.log p *
    ∑ a ∈ Finset.Icc 1 X, (psiNat (X / p ^ a) y : ℝ)

/-- Exact finite Chebyshev--Hildebrand identity.  It is obtained solely from
unique factorization and the smooth-cofactor bijection; no prime number
theorem or asymptotic estimate enters here. -/
theorem smoothLogSum_eq_smoothPrimePowerPsiSum (X y : ℕ) :
    smoothLogSum X y = smoothPrimePowerPsiSum X y := by
  classical
  rw [smoothLogSum, smoothPrimePowerPsiSum]
  calc
    ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), Real.log n =
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          ∑ p ∈ y.primesLE,
            (n.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mem_smoothNumbersUpTo_source] at hn
      exact log_nat_eq_sum_primesLE_factorization hn.2
    _ = ∑ p ∈ y.primesLE,
          ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
            (n.factorization p : ℝ) * Real.log p := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ y.primesLE, Real.log p *
          ∑ a ∈ Finset.Icc 1 X, (psiNat (X / p ^ a) y : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hpMem
      have hp : p.Prime := Nat.prime_of_mem_primesLE hpMem
      have hpY : p ≤ y := Nat.le_of_mem_primesLE hpMem
      have hcast :
          ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
              (n.factorization p : ℝ) =
            ∑ a ∈ Finset.Icc 1 X, (psiNat (X / p ^ a) y : ℝ) := by
        exact_mod_cast sum_smooth_factorization_eq_sum_psiNat hp hpY
      calc
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
            (n.factorization p : ℝ) * Real.log p =
            (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
              (n.factorization p : ℝ)) * Real.log p := by
          rw [Finset.sum_mul]
        _ = (∑ a ∈ Finset.Icc 1 X,
              (psiNat (X / p ^ a) y : ℝ)) * Real.log p := by rw [hcast]
        _ = Real.log p * ∑ a ∈ Finset.Icc 1 X,
              (psiNat (X / p ^ a) y : ℝ) := mul_comm _ _

/-- The exact boundary deficit between `Psi(X,y) log X` and the summed
logarithms of the smooth numbers.  Its integral approximation is the error
term in the refined Hildebrand recurrence. -/
noncomputable def smoothLogDefect (X y : ℕ) : ℝ :=
  ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), (Real.log X - Real.log n)

/-- Exact refined Chebyshev--Hildebrand decomposition, with the boundary
defect kept as a finite sum. -/
theorem psiNat_mul_log_eq_primePowerPsiSum_add_defect (X y : ℕ) :
    (psiNat X y : ℝ) * Real.log X =
      smoothPrimePowerPsiSum X y + smoothLogDefect X y := by
  rw [← smoothLogSum_eq_smoothPrimePowerPsiSum]
  simp only [smoothLogSum, smoothLogDefect, Finset.sum_sub_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [psiNat]
  ring

/-- The boundary defect is nonnegative, since every represented smooth
number is positive and at most `X`. -/
theorem smoothLogDefect_nonneg (X y : ℕ) : 0 ≤ smoothLogDefect X y := by
  rw [smoothLogDefect]
  apply Finset.sum_nonneg
  intro n hn
  rw [mem_smoothNumbersUpTo_source] at hn
  apply sub_nonneg.mpr
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (isSmooth_iff.mp hn.2).1
  have hXPos : 0 < (X : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (isSmooth_iff.mp hn.2).1).trans_le hn.1
  exact Real.strictMonoOn_log.monotoneOn hnPos hXPos (by exact_mod_cast hn.1)

/-- The exact weighted prime-power recurrence is bounded above by its
`Psi(X,y) log X` envelope. -/
theorem smoothPrimePowerPsiSum_le_psiNat_mul_log (X y : ℕ) :
    smoothPrimePowerPsiSum X y ≤ (psiNat X y : ℝ) * Real.log X := by
  rw [psiNat_mul_log_eq_primePowerPsiSum_add_defect]
  exact le_add_of_nonneg_right (smoothLogDefect_nonneg X y)

/-- First-prime-power consequence of the weighted identity.  This is the
finite recursive inequality used at the start of Hildebrand's iteration. -/
theorem sum_log_mul_psiNat_div_le_psiNat_mul_log {X y : ℕ} (hX : 1 ≤ X) :
    ∑ p ∈ y.primesLE, Real.log p * (psiNat (X / p) y : ℝ) ≤
      (psiNat X y : ℝ) * Real.log X := by
  apply le_trans (b := smoothPrimePowerPsiSum X y)
  · rw [smoothPrimePowerPsiSum]
    apply Finset.sum_le_sum
    intro p hpMem
    apply mul_le_mul_of_nonneg_left
    · have hOne : 1 ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
      have hsingle := Finset.single_le_sum
        (s := Finset.Icc 1 X)
        (f := fun a => (psiNat (X / p ^ a) y : ℝ))
        (fun _ _ => Nat.cast_nonneg _) hOne
      simpa using hsingle
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primesLE hpMem).one_le)
  · exact smoothPrimePowerPsiSum_le_psiNat_mul_log X y

/-- The first-power inequality restricted to any smaller prime packet. -/
theorem sum_log_mul_psiNat_div_le_psiNat_mul_log_of_le
    {X b y : ℕ} (hX : 1 ≤ X) (hby : b ≤ y) :
    ∑ p ∈ b.primesLE, Real.log p * (psiNat (X / p) y : ℝ) ≤
      (psiNat X y : ℝ) * Real.log X := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hby)
    (fun p hp _ => mul_nonneg
      (Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
      (Nat.cast_nonneg _))).trans
  exact sum_log_mul_psiNat_div_le_psiNat_mul_log (X := X) (y := y) hX

/-- Iterated finite Hildebrand lower bound.  Every allowed weighted prime
division contributes one factor of `theta(y)`, while all intermediate
logarithmic denominators are bounded by the original `log X`. -/
theorem chebyshevTheta_pow_le_psiNat_mul_log_pow
    {X y d : ℕ} (hy : 2 ≤ y) (hpower : y ^ d ≤ X) :
    Chebyshev.theta y ^ d ≤ (psiNat X y : ℝ) * Real.log X ^ d := by
  induction d generalizing X with
  | zero =>
      simp only [pow_zero, mul_one]
      exact_mod_cast one_le_psiNat (by simpa using hpower)
  | succ d ih =>
      have hX : 1 ≤ X := by
        exact le_trans (one_le_pow₀ (by omega : 1 ≤ y)) hpower
      have hlogX : 0 ≤ Real.log (X : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hX)
      calc
        Chebyshev.theta y ^ (d + 1) =
            (∑ p ∈ y.primesLE, Real.log p) * Chebyshev.theta y ^ d := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
          ring
        _ = ∑ p ∈ y.primesLE,
              Real.log p * Chebyshev.theta y ^ d := by
          rw [Finset.sum_mul]
        _ ≤ ∑ p ∈ y.primesLE,
              (Real.log p * (psiNat (X / p) y : ℝ)) * Real.log X ^ d := by
          apply Finset.sum_le_sum
          intro p hpMem
          have hp : p.Prime := Nat.prime_of_mem_primesLE hpMem
          have hpY : p ≤ y := Nat.le_of_mem_primesLE hpMem
          have hsubPower : y ^ d ≤ X / p := by
            apply (Nat.le_div_iff_mul_le hp.pos).2
            calc
              y ^ d * p ≤ y ^ d * y := Nat.mul_le_mul_left _ hpY
              _ = y ^ (d + 1) := (pow_succ y d).symm
              _ ≤ X := hpower
          have hquotPos : 1 ≤ X / p :=
            le_trans (one_le_pow₀ (by omega : 1 ≤ y)) hsubPower
          have hlogQuot : Real.log (X / p : ℕ) ≤ Real.log X := by
            apply Real.strictMonoOn_log.monotoneOn
            · show 0 < ((X / p : ℕ) : ℝ)
              exact_mod_cast Nat.zero_lt_of_lt hquotPos
            · show 0 < (X : ℝ)
              exact_mod_cast Nat.zero_lt_of_lt hX
            · exact_mod_cast Nat.div_le_self X p
          have hlogQuotNonneg : 0 ≤ Real.log (X / p : ℕ) :=
            Real.log_nonneg (by exact_mod_cast hquotPos)
          have hlogPow : Real.log (X / p : ℕ) ^ d ≤ Real.log X ^ d := by
            exact pow_le_pow_left₀ hlogQuotNonneg hlogQuot d
          have hpsiLog :
              (psiNat (X / p) y : ℝ) * Real.log (X / p : ℕ) ^ d ≤
                (psiNat (X / p) y : ℝ) * Real.log X ^ d :=
            mul_le_mul_of_nonneg_left hlogPow (Nat.cast_nonneg _)
          have hiter := (ih hsubPower).trans hpsiLog
          have hpLog : 0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hp.one_le)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hiter hpLog
        _ = (∑ p ∈ y.primesLE,
              Real.log p * (psiNat (X / p) y : ℝ)) * Real.log X ^ d := by
          rw [Finset.sum_mul]
        _ ≤ ((psiNat X y : ℝ) * Real.log X) * Real.log X ^ d :=
          mul_le_mul_of_nonneg_right
            (sum_log_mul_psiNat_div_le_psiNat_mul_log hX)
            (pow_nonneg hlogX d)
        _ = (psiNat X y : ℝ) * Real.log X ^ (d + 1) := by
          rw [pow_succ]
          ring

/-- Quotient form of the iterated lower bound. -/
theorem chebyshevTheta_div_log_pow_le_psiNat
    {X y d : ℕ} (hy : 2 ≤ y) (hX : 2 ≤ X) (hpower : y ^ d ≤ X) :
    (Chebyshev.theta y / Real.log X) ^ d ≤ (psiNat X y : ℝ) := by
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.log_pos (by exact_mod_cast hX)) d)).2
  simpa only [mul_comm] using
    chebyshevTheta_pow_le_psiNat_mul_log_pow hy hpower

/-- Endpoint-refined iteration: after `d` full packets up to `y`, one final
packet may stop at any `b ≤ y`.  This is the finite device that retains the
fractional part of `log X / log y`. -/
theorem chebyshevTheta_mul_pow_le_psiNat_mul_log_pow
    {X b y d : ℕ} (hb : 2 ≤ b) (hy : 2 ≤ y) (hby : b ≤ y)
    (hpower : y ^ d * b ≤ X) :
    Chebyshev.theta b * Chebyshev.theta y ^ d ≤
      (psiNat X y : ℝ) * Real.log X ^ (d + 1) := by
  have hX : 1 ≤ X := by
    have hprodPos : 0 < y ^ d * b :=
      Nat.mul_pos (pow_pos (by omega : 0 < y) d) (by omega)
    exact (Nat.one_le_iff_ne_zero.mpr hprodPos.ne').trans hpower
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  calc
    Chebyshev.theta b * Chebyshev.theta y ^ d =
        ∑ p ∈ b.primesLE, Real.log p * Chebyshev.theta y ^ d := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_mul]
    _ ≤ ∑ p ∈ b.primesLE,
          (Real.log p * (psiNat (X / p) y : ℝ)) * Real.log X ^ d := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp : p.Prime := Nat.prime_of_mem_primesLE hpMem
      have hpB : p ≤ b := Nat.le_of_mem_primesLE hpMem
      have hsubPower : y ^ d ≤ X / p := by
        apply (Nat.le_div_iff_mul_le hp.pos).2
        exact (Nat.mul_le_mul_left (y ^ d) hpB).trans hpower
      have hquotPos : 1 ≤ X / p :=
        le_trans (one_le_pow₀ (by omega : 1 ≤ y)) hsubPower
      have hlogQuot : Real.log (X / p : ℕ) ≤ Real.log X := by
        apply Real.strictMonoOn_log.monotoneOn
        · show 0 < ((X / p : ℕ) : ℝ)
          exact_mod_cast Nat.zero_lt_of_lt hquotPos
        · show 0 < (X : ℝ)
          exact_mod_cast Nat.zero_lt_of_lt hX
        · exact_mod_cast Nat.div_le_self X p
      have hlogQuotNonneg : 0 ≤ Real.log (X / p : ℕ) :=
        Real.log_nonneg (by exact_mod_cast hquotPos)
      have hlogPow : Real.log (X / p : ℕ) ^ d ≤ Real.log X ^ d :=
        pow_le_pow_left₀ hlogQuotNonneg hlogQuot d
      have hpsiLog :
          (psiNat (X / p) y : ℝ) * Real.log (X / p : ℕ) ^ d ≤
            (psiNat (X / p) y : ℝ) * Real.log X ^ d :=
        mul_le_mul_of_nonneg_left hlogPow (Nat.cast_nonneg _)
      have hiter :=
        (chebyshevTheta_pow_le_psiNat_mul_log_pow hy hsubPower).trans hpsiLog
      have hpLog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hp.one_le)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hiter hpLog
    _ = (∑ p ∈ b.primesLE,
          Real.log p * (psiNat (X / p) y : ℝ)) * Real.log X ^ d := by
      rw [Finset.sum_mul]
    _ ≤ ((psiNat X y : ℝ) * Real.log X) * Real.log X ^ d :=
      mul_le_mul_of_nonneg_right
        (sum_log_mul_psiNat_div_le_psiNat_mul_log_of_le hX hby)
        (pow_nonneg hlogX d)
    _ = (psiNat X y : ℝ) * Real.log X ^ (d + 1) := by
      rw [pow_succ]
      ring

end Tao2026
