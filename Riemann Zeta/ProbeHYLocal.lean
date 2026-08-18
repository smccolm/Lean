import RiemannZeta.GuthMaynard.HughesYoungEulerProduct

#check Nat.sum_divisors_prime_pow
#check Nat.divisors_prime_pow
#check ArithmeticFunction.moebius_apply_prime_pow
#check Nat.factorization_gcd
#check Nat.Prime.factorization_pow
#check Nat.factorization_pow_self
#check Nat.gcd_eq_right_iff_dvd
#check Nat.gcd_eq_left_iff_dvd
#check Nat.coprime_pow_left_iff
#check Nat.coprime_pow_right_iff
#check Nat.Prime.not_dvd_one
#check Nat.Prime.coprime_iff_not_dvd
#check Nat.Coprime.gcd_left
#check Nat.Coprime.gcd_right
#check Nat.Prime.pow_dvd_iff_le_factorization
#check Nat.factorization_eq_zero_of_not_dvd
#check Nat.Prime.dvd_iff_one_le_factorization
#check Nat.factorization_eq_zero_iff
#check ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd
#check ArithmeticFunction.IsMultiplicative.eulerProduct_tprod
#check HasProd.congr_cofinite₀
#check Multipliable.tsum_congr_cofinite₀
#check Nat.prime_of_mem_primeFactors

example {h p e : ℕ} (hh : 0 < h) (hp : p.Prime) :
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

open Complex Finset
open scoped BigOperators

example {p e : ℕ} (hp : p.Prime) (c : ℂ) :
    RiemannZeta.GuthMaynard.hughesYoungEquation106DivisorFactor c (p ^ e) =
      if e = 0 then 1 else 1 - (p : ℂ) ^ c := by
  rw [RiemannZeta.GuthMaynard.hughesYoungEquation106DivisorFactor_apply
    (Nat.pow_pos hp.pos)]
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

example {h k p e : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (a b c : ℂ) :
    RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c (p ^ e) =
      (p : ℂ) ^ ((min (h.factorization p) e : ℕ) * a) *
        (p : ℂ) ^ ((min (k.factorization p) e : ℕ) * b) *
        (if e = 0 then 1 else 1 - (p : ℂ) ^ c) /
        (p : ℂ) ^ (e * (a + b + c)) := by
  rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_apply
      (Nat.pow_pos hp.pos),
    RiemannZeta.GuthMaynard.gcd_prime_pow_eq_pow_min_factorization hh hp,
    RiemannZeta.GuthMaynard.gcd_prime_pow_eq_pow_min_factorization hk hp]
  rw [← RiemannZeta.GuthMaynard.hughesYoungEquation106DivisorFactor_apply
      (Nat.pow_pos hp.pos),
    RiemannZeta.GuthMaynard.hughesYoungEquation106DivisorFactor_prime_pow hp]
  simp only [Nat.cast_pow]
  rw [Complex.natCast_cpow_natCast_mul,
    Complex.natCast_cpow_natCast_mul,
    Complex.natCast_cpow_natCast_mul]

example {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hph : ¬ p ∣ h) (hpk : ¬ p ∣ k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ,
        RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      1 + (1 - (p : ℂ) ^ c) *
        RiemannZeta.GuthMaynard.hughesYoungEquation107Series
          ((p : ℂ) ^ (-(a + b + c))) := by
  let f : ℕ → ℂ := fun e =>
    RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c (p ^ e)
  have hsAll := RiemannZeta.GuthMaynard.summable_norm_hughesYoungEquation106Coefficient
    hh hk hA hC
  have hs : Summable f := by
    exact (summable_norm_iff.mp hsAll).comp_injective
      (Nat.pow_right_injective hp.two_le)
  rw [← hs.sum_add_tsum_nat_add 1]
  have hf0 : f 0 = 1 := by
    unfold f
    rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_prime_pow
      hh hk hp]
    norm_num
  rw [show ∑ x ∈ Finset.range 1, f x = 1 by simp [hf0]]
  congr 1
  unfold RiemannZeta.GuthMaynard.hughesYoungEquation107Series
  rw [← tsum_mul_left]
  apply tsum_congr
  intro e
  unfold f
  rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_prime_pow
    hh hk hp]
  rw [Nat.factorization_eq_zero_of_not_dvd hph,
    Nat.factorization_eq_zero_of_not_dvd hpk]
  simp only [Nat.zero_min, Nat.cast_zero, zero_mul, Complex.cpow_zero,
    one_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow :
      ((p : ℂ) ^ ((e + 1 : ℕ) * (a + b + c)))⁻¹ =
        ((p : ℂ) ^ (-(a + b + c))) ^ (e + 1) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [div_eq_mul_inv, hpow]

example {p m n : ℕ} (hp : p.Prime) (u v : ℂ) :
    (p : ℂ) ^ (m * u) / (p : ℂ) ^ (n * v) =
      (p : ℂ) ^ (m * u - n * v) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hp0]
  ring_nf

example {p e : ℕ} (hp : p.Prime) (a b c : ℂ) :
    (p : ℂ) ^ (e * a) / (p : ℂ) ^ (e * (a + b + c)) =
      ((p : ℂ) ^ (-(b + c))) ^ e := by
  rw [show (p : ℂ) ^ (e * a) / (p : ℂ) ^ (e * (a + b + c)) =
      (p : ℂ) ^ (e * a - e * (a + b + c)) by
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hp0]
        congr 1]
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

example {p hpv e : ℕ} (hp : p.Prime) (hle : hpv ≤ e) (a b c : ℂ) :
    (p : ℂ) ^ (hpv * a) / (p : ℂ) ^ (e * (a + b + c)) =
      ((p : ℂ) ^ (-(b + c))) ^ hpv *
        ((p : ℂ) ^ (-(a + b + c))) ^ (e - hpv) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [show (p : ℂ) ^ (hpv * a) / (p : ℂ) ^ (e * (a + b + c)) =
      (p : ℂ) ^ (hpv * a - e * (a + b + c)) by
        rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hp0]
        congr 1]
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul,
    ← Complex.cpow_add _ _ hp0]
  congr 1
  rw [Nat.cast_sub hle]
  ring

example {h k p : ℕ} (hh : 0 < h) (hk : 0 < k) (hp : p.Prime)
    (hhk : Nat.Coprime h k) (hph : p ∣ h)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    (∑' e : ℕ,
        RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c (p ^ e)) =
      1 + (1 - (p : ℂ) ^ c) *
        RiemannZeta.GuthMaynard.hughesYoungEquation109Series
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
    RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c (p ^ e)
  have hsAll := RiemannZeta.GuthMaynard.summable_norm_hughesYoungEquation106Coefficient
    hh hk hA hC
  have hs : Summable f := by
    exact (summable_norm_iff.mp hsAll).comp_injective
      (Nat.pow_right_injective hp.two_le)
  rw [← hs.sum_add_tsum_nat_add 1]
  have hf0 : f 0 = 1 := by
    unfold f
    rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_prime_pow
      hh hk hp]
    norm_num
  rw [show ∑ x ∈ Finset.range 1, f x = 1 by simp [hf0]]
  congr 1
  unfold RiemannZeta.GuthMaynard.hughesYoungEquation109Series
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold f
  rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_prime_pow
    hh hk hp, hkfac]
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
    rw [RiemannZeta.GuthMaynard.primeCPow_equation109_inside hp]
  · rw [if_neg hn]
    have hle : h.factorization p ≤ n + 1 := by omega
    rw [min_eq_left hle]
    rw [show (p : ℂ) ^ ((h.factorization p : ℕ) * a) *
          (1 - (p : ℂ) ^ c) /
          (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c)) =
        (1 - (p : ℂ) ^ c) *
          ((p : ℂ) ^ ((h.factorization p : ℕ) * a) /
            (p : ℂ) ^ ((n + 1 : ℕ) * (a + b + c))) by ring]
    rw [RiemannZeta.GuthMaynard.primeCPow_equation109_outside hp hle]

example (h k n : ℕ) (a b c : ℂ) :
    RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient h k a b c n =
      RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient k h b a c n := by
  by_cases hn : n = 0
  · subst n
    simp [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient]
  · rw [RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_apply
      (Nat.pos_of_ne_zero hn),
    RiemannZeta.GuthMaynard.hughesYoungEquation106Coefficient_apply
      (Nat.pos_of_ne_zero hn)]
    ring_nf
