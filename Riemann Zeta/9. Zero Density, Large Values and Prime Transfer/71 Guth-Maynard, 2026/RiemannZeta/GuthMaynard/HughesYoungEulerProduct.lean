import Mathlib.NumberTheory.EulerProduct.Basic
import RiemannZeta.GuthMaynard.HughesYoungEulerFactors

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The Euler product behind Hughes--Young Lemma 6.1

The coefficient in equation (106) is installed as a genuine multiplicative
arithmetic function.  This file proves its multiplicativity, absolute
summability in the paper's half-plane, and its Euler-product expansion.  The
next layer evaluates each prime-power factor using equations (107)--(118).
-/

/-- The completely multiplicative complex power `n ↦ n^z`, with the required
arithmetic-function value zero at `n = 0`. -/
noncomputable def hughesYoungNatCPow (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ z, by simp⟩

@[simp]
theorem hughesYoungNatCPow_apply_of_pos {n : ℕ} (hn : 0 < n) (z : ℂ) :
    hughesYoungNatCPow z n = (n : ℂ) ^ z := by
  simp [hughesYoungNatCPow, hn.ne']

theorem hughesYoungNatCPow_isMultiplicative (z : ℂ) :
    (hughesYoungNatCPow z).IsMultiplicative := by
  constructor
  · simp [hughesYoungNatCPow]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := by simpa using hmn
      subst n
      simp [hughesYoungNatCPow]
    · by_cases hn : n = 0
      · subst n
        have hm1 : m = 1 := by simpa using hmn
        subst m
        simp [hughesYoungNatCPow]
      · rw [hughesYoungNatCPow_apply_of_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm)
          (Nat.pos_of_ne_zero hn)),
        hughesYoungNatCPow_apply_of_pos (Nat.pos_of_ne_zero hm),
        hughesYoungNatCPow_apply_of_pos (Nat.pos_of_ne_zero hn)]
        simpa only [Nat.cast_mul] using
          Complex.natCast_mul_natCast_cpow m n z

/-- The fixed-twist gcd power appearing in equation (106). -/
noncomputable def hughesYoungGCDCPow (h : ℕ) (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else ((Nat.gcd h n : ℕ) : ℂ) ^ z, by simp⟩

@[simp]
theorem hughesYoungGCDCPow_apply_of_pos {h n : ℕ} (hn : 0 < n) (z : ℂ) :
    hughesYoungGCDCPow h z n = ((Nat.gcd h n : ℕ) : ℂ) ^ z := by
  simp [hughesYoungGCDCPow, hn.ne']

theorem hughesYoungGCDCPow_isMultiplicative (h : ℕ) (z : ℂ) :
    (hughesYoungGCDCPow h z).IsMultiplicative := by
  constructor
  · simp [hughesYoungGCDCPow]
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := by simpa using hmn
      subst n
      simp [hughesYoungGCDCPow]
    · by_cases hn : n = 0
      · subst n
        have hm1 : m = 1 := by simpa using hmn
        subst m
        simp [hughesYoungGCDCPow]
      · rw [hughesYoungGCDCPow_apply_of_pos
          (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)),
        hughesYoungGCDCPow_apply_of_pos (Nat.pos_of_ne_zero hm),
        hughesYoungGCDCPow_apply_of_pos (Nat.pos_of_ne_zero hn)]
        rw [hmn.gcd_mul h]
        simpa only [Nat.cast_mul] using
          Complex.natCast_mul_natCast_cpow (Nat.gcd h m) (Nat.gcd h n) z

/-- The pointwise factor `d^c μ(d)` in equation (106). -/
noncomputable def hughesYoungMoebiusCPow (c : ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ).pmul
    (hughesYoungNatCPow c)

theorem hughesYoungMoebiusCPow_isMultiplicative (c : ℂ) :
    (hughesYoungMoebiusCPow c).IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.pmul
    ArithmeticFunction.isMultiplicative_moebius.intCast
    (hughesYoungNatCPow_isMultiplicative c)

/-- The divisor sum `∑_{d|n} d^c μ(d)` in equation (106). -/
noncomputable def hughesYoungEquation106DivisorFactor (c : ℂ) :
    ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
    hughesYoungMoebiusCPow c

theorem hughesYoungEquation106DivisorFactor_isMultiplicative (c : ℂ) :
    (hughesYoungEquation106DivisorFactor c).IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_zeta.natCast
    (hughesYoungMoebiusCPow_isMultiplicative c)

theorem hughesYoungEquation106DivisorFactor_apply
    {n : ℕ} (hn : 0 < n) (c : ℂ) :
    hughesYoungEquation106DivisorFactor c n =
      ∑ d ∈ n.divisors,
        (d : ℂ) ^ c * ArithmeticFunction.moebius d := by
  unfold hughesYoungEquation106DivisorFactor
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn
  simp [hughesYoungMoebiusCPow, ArithmeticFunction.pmul_apply,
    hughesYoungNatCPow_apply_of_pos hdPos, mul_comm]

/-- The exact `l`-coefficient remaining after extracting `ζ(1+c)` from
equation (105). -/
noncomputable def hughesYoungEquation106Coefficient
    (h k : ℕ) (a b c : ℂ) : ArithmeticFunction ℂ :=
  ArithmeticFunction.pdiv
    ((hughesYoungGCDCPow h a).pmul
      ((hughesYoungGCDCPow k b).pmul
        (hughesYoungEquation106DivisorFactor c)))
    (hughesYoungNatCPow (a + b + c))

theorem hughesYoungEquation106Coefficient_isMultiplicative
    (h k : ℕ) (a b c : ℂ) :
    (hughesYoungEquation106Coefficient h k a b c).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.pdiv
  · exact (hughesYoungGCDCPow_isMultiplicative h a).pmul
      ((hughesYoungGCDCPow_isMultiplicative k b).pmul
        (hughesYoungEquation106DivisorFactor_isMultiplicative c))
  · exact hughesYoungNatCPow_isMultiplicative (a + b + c)

theorem hughesYoungEquation106Coefficient_apply
    {n : ℕ} (hn : 0 < n) (h k : ℕ) (a b c : ℂ) :
    hughesYoungEquation106Coefficient h k a b c n =
      ((Nat.gcd h n : ℕ) : ℂ) ^ a *
        ((Nat.gcd k n : ℕ) : ℂ) ^ b *
        (∑ d ∈ n.divisors,
          (d : ℂ) ^ c * ArithmeticFunction.moebius d) /
        (n : ℂ) ^ (a + b + c) := by
  unfold hughesYoungEquation106Coefficient
  rw [ArithmeticFunction.pdiv_apply]
  simp only [ArithmeticFunction.pmul_apply]
  rw [hughesYoungGCDCPow_apply_of_pos hn,
    hughesYoungGCDCPow_apply_of_pos hn,
    hughesYoungEquation106DivisorFactor_apply hn,
    hughesYoungNatCPow_apply_of_pos hn]
  ring

/-- The gcd occurring in the prime-power Euler factor is determined exactly
by the minimum of the two `p`-adic exponents.  This is the arithmetic bridge
used implicitly when Hughes--Young passes from equation (106) to (109). -/
theorem gcd_prime_pow_eq_pow_min_factorization
    {h p e : ℕ} (hh : 0 < h) (hp : p.Prime) :
    Nat.gcd h (p ^ e) = p ^ min (h.factorization p) e := by
  apply Nat.eq_of_factorization_eq
  · exact (Nat.gcd_pos_of_pos_left _ hh).ne'
  · exact pow_ne_zero _ hp.ne_zero
  intro q
  rw [Nat.factorization_gcd hh.ne' (pow_ne_zero _ hp.ne_zero),
    hp.factorization_pow, hp.factorization_pow]
  by_cases hqp : q = p
  · subst q
    simp [Finsupp.inf_apply]
  · simp [Finsupp.inf_apply, hqp]

/-- The Möbius divisor factor in equation (106), evaluated on a prime
power.  Only the divisors `1` and `p` survive. -/
theorem hughesYoungEquation106DivisorFactor_prime_pow
    {p e : ℕ} (hp : p.Prime) (c : ℂ) :
    hughesYoungEquation106DivisorFactor c (p ^ e) =
      if e = 0 then 1 else 1 - (p : ℂ) ^ c := by
  rw [hughesYoungEquation106DivisorFactor_apply (Nat.pow_pos hp.pos)]
  rw [Nat.sum_divisors_prime_pow hp]
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ]
      by_cases he : e = 0
      · subst e
        have ih' :
            (∑ x ∈ Finset.range (0 + 1),
              ((p ^ x : ℕ) : ℂ) ^ c * ArithmeticFunction.moebius (p ^ x)) = 1 := ih
        rw [ih']
        simp only [zero_add, pow_one, if_false, Nat.one_ne_zero]
        rw [ArithmeticFunction.moebius_apply_prime hp]
        norm_num
        ring
      · rw [show ∑ x ∈ Finset.range (e + 1),
              ((p ^ x : ℕ) : ℂ) ^ c * ArithmeticFunction.moebius (p ^ x) =
              1 - (p : ℂ) ^ c by simpa [he] using ih]
        simp [ArithmeticFunction.moebius_apply_prime_pow hp, he]

/-- Exact prime-power coefficient extracted from equation (106).  This is
the arithmetic statement whose three valuation cases are summed in equations
(107)--(118). -/
theorem hughesYoungEquation106Coefficient_prime_pow
    {h k p e : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (a b c : ℂ) :
    hughesYoungEquation106Coefficient h k a b c (p ^ e) =
      (p : ℂ) ^ ((min (h.factorization p) e : ℕ) * a) *
        (p : ℂ) ^ ((min (k.factorization p) e : ℕ) * b) *
        (if e = 0 then 1 else 1 - (p : ℂ) ^ c) /
        (p : ℂ) ^ (e * (a + b + c)) := by
  rw [hughesYoungEquation106Coefficient_apply (Nat.pow_pos hp.pos),
    gcd_prime_pow_eq_pow_min_factorization hh hp,
    gcd_prime_pow_eq_pow_min_factorization hk hp]
  rw [← hughesYoungEquation106DivisorFactor_apply (Nat.pow_pos hp.pos),
    hughesYoungEquation106DivisorFactor_prime_pow hp]
  simp only [Nat.cast_pow]
  rw [Complex.natCast_cpow_natCast_mul,
    Complex.natCast_cpow_natCast_mul,
    Complex.natCast_cpow_natCast_mul]

/-- Quotient of two prime-base complex powers, with natural scaling made
explicit in the exponent. -/
theorem primeCPow_nat_ratio {p m n : ℕ} (hp : p.Prime) (u v : ℂ) :
    (p : ℂ) ^ (m * u) / (p : ℂ) ^ (n * v) =
      (p : ℂ) ^ (m * u - n * v) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hp0]
  ring_nf

/-- The equation-(109) coefficient while the exponent is inside the
`p`-adic valuation of `h`. -/
theorem primeCPow_equation109_inside {p e : ℕ} (hp : p.Prime)
    (a b c : ℂ) :
    (p : ℂ) ^ (e * a) / (p : ℂ) ^ (e * (a + b + c)) =
      ((p : ℂ) ^ (-(b + c))) ^ e := by
  rw [primeCPow_nat_ratio hp]
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

/-- The equation-(109) coefficient after the exponent has passed the
`p`-adic valuation of `h`. -/
theorem primeCPow_equation109_outside
    {p hpv e : ℕ} (hp : p.Prime) (hle : hpv ≤ e) (a b c : ℂ) :
    (p : ℂ) ^ (hpv * a) / (p : ℂ) ^ (e * (a + b + c)) =
      ((p : ℂ) ^ (-(b + c))) ^ hpv *
        ((p : ℂ) ^ (-(a + b + c))) ^ (e - hpv) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [primeCPow_nat_ratio hp]
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul,
    ← Complex.cpow_add _ _ hp0]
  congr 1
  rw [Nat.cast_sub hle]
  ring

/-- Equation-(106) is symmetric under exchanging the two twists and their
corresponding shifts. -/
theorem hughesYoungEquation106Coefficient_swap
    (h k n : ℕ) (a b c : ℂ) :
    hughesYoungEquation106Coefficient h k a b c n =
      hughesYoungEquation106Coefficient k h b a c n := by
  by_cases hn : n = 0
  · subst n
    simp [hughesYoungEquation106Coefficient]
  · rw [hughesYoungEquation106Coefficient_apply (Nat.pos_of_ne_zero hn),
      hughesYoungEquation106Coefficient_apply (Nat.pos_of_ne_zero hn)]
    ring_nf

/-- Absolute summability of the multiplicative equation-(106) coefficient,
deduced from the already-proved absolute convergence and Fubini step in
equations (105)--(106). -/
theorem summable_norm_hughesYoungEquation106Coefficient
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    Summable (fun n : ℕ =>
      ‖hughesYoungEquation106Coefficient h k a b c n‖) := by
  let zc : ℂ := riemannZeta (1 + c)
  have hzc : zc ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp only [zc]
    simpa using add_lt_add_left hC 1
  have hpair := summable_hughesYoungEquation96Term hh hk hA hC
  have houter : Summable (fun l : ℕ =>
      ∑' r : ℕ, hughesYoungEquation96Term h k a b (1 + c) r l) :=
    hpair.prod_symm.prod
  have hscaled := houter.mul_left zc⁻¹
  have hshift : Summable (fun l : ℕ =>
      hughesYoungEquation106Coefficient h k a b c (l + 1)) := by
    refine hscaled.congr (fun l => ?_)
    letI : NeZero (l + 1) := ⟨Nat.succ_ne_zero l⟩
    have hinner := hughesYoungEquation105_inner (l + 1) c hC
    let A : ℂ := ((Nat.gcd h (l + 1) : ℕ) : ℂ) ^ a *
      ((Nat.gcd k (l + 1) : ℕ) : ℂ) ^ b *
      ((((l + 1 : ℕ) : ℂ) ^ (a + b))⁻¹)
    have hfactor :
        (∑' r : ℕ, hughesYoungEquation96Term h k a b (1 + c) r l) =
          A * (∑' r : ℕ,
            ramanujanSum (l + 1) (r + 1) /
              ((r + 1 : ℕ) : ℂ) ^ (1 + c)) := by
      calc
        (∑' r : ℕ, hughesYoungEquation96Term h k a b (1 + c) r l) =
            ∑' r : ℕ, A *
              (ramanujanSum (l + 1) (r + 1) /
                ((r + 1 : ℕ) : ℂ) ^ (1 + c)) := by
          apply tsum_congr
          intro r
          unfold hughesYoungEquation96Term A
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = A * (∑' r : ℕ,
            ramanujanSum (l + 1) (r + 1) /
              ((r + 1 : ℕ) : ℂ) ^ (1 + c)) := tsum_mul_left
    rw [hfactor, hinner]
    rw [hughesYoungEquation106Coefficient_apply (Nat.succ_pos l)]
    unfold hughesYoungEquation105FiniteFactor
    have hl0 : (((l + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
    have hpowa : (((l + 1 : ℕ) : ℂ) ^ (a + b)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hl0)
    have hpowc : (((l + 1 : ℕ) : ℂ) ^ c) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hl0)
    change zc⁻¹ *
        (A * (zc * hughesYoungEquation105FiniteFactor (l + 1) c)) = _
    unfold A hughesYoungEquation105FiniteFactor
    rw [show a + b + c = (a + b) + c by ring,
      Complex.cpow_add _ _ hl0,
      Complex.cpow_add _ _ hl0]
    field_simp [hzc, hpowa, hpowc]
    rw [Complex.cpow_add _ _ hl0]
    ring
  have hfull : Summable (hughesYoungEquation106Coefficient h k a b c) :=
    (summable_nat_add_iff 1).mp (by simpa using hshift)
  exact summable_norm_iff.mpr hfull

/-- Equation (107) as the actual Euler factor of equation (106) at a prime
which divides neither coprime twist. -/
theorem hughesYoungEquation107_of_not_dvd
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hph : ¬ p ∣ h) (hpk : ¬ p ∣ k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      1 + (1 - (p : ℂ) ^ c) *
        hughesYoungEquation107Series ((p : ℂ) ^ (-(a + b + c))) := by
  let f : ℕ → ℂ := fun e =>
    hughesYoungEquation106Coefficient h k a b c (p ^ e)
  have hsAll := summable_norm_hughesYoungEquation106Coefficient hh hk hA hC
  have hs : Summable f := by
    exact (summable_norm_iff.mp hsAll).comp_injective
      (Nat.pow_right_injective hp.two_le)
  rw [← hs.sum_add_tsum_nat_add 1]
  have hf0 : f 0 = 1 := by
    unfold f
    rw [hughesYoungEquation106Coefficient_prime_pow hh hk hp]
    norm_num
  rw [show ∑ x ∈ Finset.range 1, f x = 1 by simp [hf0]]
  congr 1
  unfold hughesYoungEquation107Series
  rw [← tsum_mul_left]
  apply tsum_congr
  intro e
  unfold f
  rw [hughesYoungEquation106Coefficient_prime_pow hh hk hp]
  rw [Nat.factorization_eq_zero_of_not_dvd hph,
    Nat.factorization_eq_zero_of_not_dvd hpk]
  simp only [Nat.zero_min, Nat.cast_zero, zero_mul, Complex.cpow_zero,
    one_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  have hpow :
      ((p : ℂ) ^ ((e + 1 : ℕ) * (a + b + c)))⁻¹ =
        ((p : ℂ) ^ (-(a + b + c))) ^ (e + 1) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [div_eq_mul_inv, hpow]

/-- Equation (109) as the actual Euler factor of equation (106) at a prime
dividing `h`.  Coprimality forces the corresponding valuation of `k` to be
zero, and the proof splits the coefficient at the exact valuation of `h`. -/
theorem hughesYoungEquation109_of_dvd_left
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hhk : Nat.Coprime h k) (hph : p ∣ h)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      1 + (1 - (p : ℂ) ^ c) *
        hughesYoungEquation109Series
          (h.factorization p)
          ((p : ℂ) ^ (-(a + b + c)))
          ((p : ℂ) ^ (-(b + c))) := by
  have hpk : ¬ p ∣ k := by
    intro hpk
    have hpg : p ∣ Nat.gcd h k := Nat.dvd_gcd hph hpk
    rw [hhk.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  have hkfac : k.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpk
  let f : ℕ → ℂ := fun e =>
    hughesYoungEquation106Coefficient h k a b c (p ^ e)
  have hsAll := summable_norm_hughesYoungEquation106Coefficient hh hk hA hC
  have hs : Summable f := by
    exact (summable_norm_iff.mp hsAll).comp_injective
      (Nat.pow_right_injective hp.two_le)
  rw [← hs.sum_add_tsum_nat_add 1]
  have hf0 : f 0 = 1 := by
    unfold f
    rw [hughesYoungEquation106Coefficient_prime_pow hh hk hp]
    norm_num
  rw [show ∑ x ∈ Finset.range 1, f x = 1 by simp [hf0]]
  congr 1
  unfold hughesYoungEquation109Series
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold f
  rw [hughesYoungEquation106Coefficient_prime_pow hh hk hp, hkfac]
  simp only [Nat.zero_min, Nat.cast_zero, zero_mul, Complex.cpow_zero,
    mul_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  by_cases hn : n < h.factorization p
  · rw [if_pos hn]
    have hle : n + 1 ≤ h.factorization p := Nat.succ_le_iff.mpr hn
    rw [min_eq_right hle]
    rw [show (p : ℂ) ^ ((n + 1 : ℕ) * a) *
          (1 - (p : ℂ) ^ c) /
          (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c)) =
        (1 - (p : ℂ) ^ c) *
          ((p : ℂ) ^ ((n + 1 : ℕ) * a) /
            (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c))) by ring]
    rw [primeCPow_equation109_inside hp]
  · rw [if_neg hn]
    have hle : h.factorization p ≤ n + 1 := by omega
    rw [min_eq_left hle]
    rw [show (p : ℂ) ^ ((h.factorization p : ℕ) * a) *
          (1 - (p : ℂ) ^ c) /
          (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c)) =
        (1 - (p : ℂ) ^ c) *
          ((p : ℂ) ^ ((h.factorization p : ℕ) * a) /
            (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c))) by ring]
    rw [primeCPow_equation109_outside hp hle]

/-- The symmetric equation-(109) Euler factor at a prime dividing `k`. -/
theorem hughesYoungEquation109_of_dvd_right
    {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hhk : Nat.Coprime h k) (hpk : p ∣ k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      1 + (1 - (p : ℂ) ^ c) *
        hughesYoungEquation109Series
          (k.factorization p)
          ((p : ℂ) ^ (-(a + b + c)))
          ((p : ℂ) ^ (-(a + c))) := by
  have hA' : 1 < (b + a).re := by
    simpa [add_comm] using hA
  calc
    (∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
        ∑' e : ℕ, hughesYoungEquation106Coefficient k h b a c (p ^ e) := by
      apply tsum_congr
      intro e
      exact hughesYoungEquation106Coefficient_swap h k (p ^ e) a b c
    _ = 1 + (1 - (p : ℂ) ^ c) *
        hughesYoungEquation109Series
          (k.factorization p)
          ((p : ℂ) ^ (-(b + a + c)))
          ((p : ℂ) ^ (-(a + c))) :=
      hughesYoungEquation109_of_dvd_left hk hh hp hhk.symm hpk hA' hC
    _ = _ := by ring_nf

/-- Euler-product form of the inner sum in equation (106).  This is the
global multiplicative statement to which equations (107)--(118) apply. -/
theorem hughesYoungEquation106_eulerProduct
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    ∏' p : Nat.Primes,
        ∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c (p ^ e) =
      ∑' n : ℕ, hughesYoungEquation106Coefficient h k a b c n := by
  exact (hughesYoungEquation106Coefficient_isMultiplicative h k a b c).eulerProduct_tprod
    (summable_norm_hughesYoungEquation106Coefficient hh hk hA hC)

/-- Equation (106) with the arithmetic sum replaced by its exact Euler
product. -/
theorem hughesYoungEquation106_eq_zeta_mul_eulerProduct
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    hughesYoungEquation106 h k a b c =
      riemannZeta (1 + c) *
        ∏' p : Nat.Primes,
          ∑' e : ℕ,
            hughesYoungEquation106Coefficient h k a b c (p ^ e) := by
  unfold hughesYoungEquation106
  rw [hughesYoungEquation106_eulerProduct hh hk hA hC]
  congr 1
  have hsNorm := summable_norm_hughesYoungEquation106Coefficient hh hk hA hC
  have hs : Summable (hughesYoungEquation106Coefficient h k a b c) :=
    summable_norm_iff.mp hsNorm
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hshift :
      (∑' l : ℕ, hughesYoungEquation106Coefficient h k a b c (l + 1)) =
        ∑' n : ℕ, hughesYoungEquation106Coefficient h k a b c n := by
    simpa [hughesYoungEquation106Coefficient] using hsplit
  rw [← hshift]
  apply tsum_congr
  intro l
  rw [hughesYoungEquation106Coefficient_apply (Nat.succ_pos l)]

end RiemannZeta.GuthMaynard
