import RiemannZeta.GuthMaynard.DFIEquation26
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The epsilon bound for the divisor function

DFI use the standard estimate `d(n) \ll_\varepsilon n^\varepsilon`
after equation (26).  This file proves that estimate from factorization,
with the dependence on `\varepsilon` represented by an existential constant.
-/

open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-- The elementary inequality `k + 1 \le 2^k`. -/
theorem nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      omega

/-- A threshold beyond which `p^ε ≥ 2`. -/
noncomputable def divisorEpsilonThreshold (ε : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ ε⁻¹⌉₊

theorem two_le_rpow_of_threshold_le
    {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : divisorEpsilonThreshold ε ≤ p) :
    (2 : ℝ) ≤ (p : ℝ) ^ ε := by
  have hroot : (2 : ℝ) ^ ε⁻¹ ≤ p :=
    (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hnonneg : 0 ≤ (2 : ℝ) ^ ε⁻¹ := Real.rpow_nonneg (by norm_num) _
  have hrpow := Real.rpow_le_rpow hnonneg hroot hε.le
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hrpow
  rw [inv_mul_cancel₀ hε.ne', Real.rpow_one] at hrpow
  exact hrpow

/-- The finite loss contributed by primes below the epsilon threshold. -/
noncomputable def divisorEpsilonConstant (ε : ℝ) : ℝ :=
  ∏ p ∈ Finset.range (divisorEpsilonThreshold ε),
    max 1 (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1))

theorem divisorEpsilonConstant_pos (ε : ℝ) :
    0 < divisorEpsilonConstant ε := by
  unfold divisorEpsilonConstant
  exact Finset.prod_pos fun p hp => lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Each prime-power divisor factor is bounded by its epsilon power, with
only a factor from the fixed finite set of small primes. -/
theorem factorization_succ_le_divisorEpsilonFactor
    {ε : ℝ} (hε : 0 < ε) {p k : ℕ} (hp : p.Prime) :
    ((k + 1 : ℕ) : ℝ) ≤
      (if p < divisorEpsilonThreshold ε then
          max 1 (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1))
        else 1) * ((p : ℝ) ^ ε) ^ k := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hbase : 1 < (p : ℝ) ^ ε := Real.one_lt_rpow hpR hε
  split_ifs with hsmall
  · have hk := (k + 1).cast_le_pow_div_sub hbase
    have hden : 0 < (p : ℝ) ^ ε - 1 := sub_pos.mpr hbase
    calc
      ((k + 1 : ℕ) : ℝ) ≤ ((p : ℝ) ^ ε) ^ (k + 1) /
          ((p : ℝ) ^ ε - 1) := hk
      _ = (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1)) *
          ((p : ℝ) ^ ε) ^ k := by rw [pow_succ]; field_simp
      _ ≤ max 1 (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1)) *
          ((p : ℝ) ^ ε) ^ k := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hlarge : divisorEpsilonThreshold ε ≤ p := Nat.le_of_not_gt hsmall
    have htwo := two_le_rpow_of_threshold_le hε hlarge
    calc
      ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast nat_succ_le_two_pow k
      _ = (2 : ℝ) ^ k := by norm_num
      _ ≤ ((p : ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) htwo k
      _ = 1 * ((p : ℝ) ^ ε) ^ k := by ring

/-- The classical pointwise epsilon bound for the divisor-counting
function.  The constant depends only on `ε`. -/
theorem card_divisors_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) :
    ((n.divisors.card : ℕ) : ℝ) ≤
      divisorEpsilonConstant ε * (n : ℝ) ^ ε := by
  rw [Nat.card_divisors hn]
  push_cast
  calc
    ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
        ∏ p ∈ n.primeFactors,
          ((if p < divisorEpsilonThreshold ε then
              max 1 (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1))
            else 1) * ((p : ℝ) ^ ε) ^ (n.factorization p)) := by
      exact Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => by
        simpa using factorization_succ_le_divisorEpsilonFactor
          (p := p) (k := n.factorization p) hε
          (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors,
          (if p < divisorEpsilonThreshold ε then
            max 1 (((p : ℝ) ^ ε) / ((p : ℝ) ^ ε - 1)) else 1)) *
        (∏ p ∈ n.primeFactors,
          ((p : ℝ) ^ ε) ^ (n.factorization p)) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ divisorEpsilonConstant ε *
        (∏ p ∈ n.primeFactors,
          ((p : ℝ) ^ ε) ^ (n.factorization p)) := by
      gcongr
      unfold divisorEpsilonConstant
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, mul_one]
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_range.mpr hp.2
      · intro p hp
        exact zero_le_one.trans (le_max_left (1 : ℝ) _)
      · intro p hpRange hpNot
        exact le_max_left (1 : ℝ) _
    _ = divisorEpsilonConstant ε * (n : ℝ) ^ ε := by
      congr 1
      calc
        ∏ p ∈ n.primeFactors,
            ((p : ℝ) ^ ε) ^ n.factorization p =
            ∏ p ∈ n.primeFactors,
              (((p : ℝ) ^ n.factorization p) ^ ε) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
            ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
          congr 1
          ring
        _ = (∏ p ∈ n.primeFactors,
              ((p : ℝ) ^ n.factorization p)) ^ ε := by
          exact Real.finsetProd_rpow n.primeFactors
            (fun p => (p : ℝ) ^ n.factorization p)
            (fun p hp => by positivity) ε
        _ = (n : ℝ) ^ ε := by
          congr 1
          exact_mod_cast (show
            ∏ p ∈ n.primeFactors, p ^ n.factorization p = n by
              simpa only [← Nat.prod_factorization_eq_prod_primeFactors] using
                Nat.prod_factorization_pow_eq_self hn)

/-- Division by a fixed divisor is injective on its multiples. -/
theorem nat_div_injectiveOn_multiples {d : ℕ} :
    Set.InjOn (fun q : ℕ => q / d) {q | d ∣ q} := by
  intro q hq r hr hdiv
  calc
    q = d * (q / d) := (Nat.mul_div_cancel' hq).symm
    _ = d * (r / d) := congrArg (fun z => d * z) hdiv
    _ = r := Nat.mul_div_cancel' hr

/-- The reciprocal quotients of multiples of `d` in an interval are bounded
by the ordinary harmonic sum. -/
theorem sum_Ioo_filter_dvd_one_div_quotient_le_harmonic
    (K L d : ℕ) (hd : 0 < d) :
    (∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        (1 / ((q / d : ℕ) : ℝ))) ≤ ((harmonic L : ℚ) : ℝ) := by
  let S := (Finset.Ioo K L).filter (d ∣ ·)
  have hinj : Set.InjOn (fun q : ℕ => q / d) (↑S : Set ℕ) := by
    apply nat_div_injectiveOn_multiples.mono
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have heq :
      (∑ q ∈ S, (1 / ((q / d : ℕ) : ℝ))) =
        ∑ r ∈ S.image (fun q => q / d), (1 / (r : ℝ)) := by
    symm
    rw [Finset.sum_image]
    intro q hq r hr hqr
    exact hinj hq hr hqr
  rw [heq]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨q, hqS, rfl⟩ := hr
    have hq := Finset.mem_Ioo.mp (Finset.mem_filter.mp hqS).1
    have hdq := (Finset.mem_filter.mp hqS).2
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hq.1
    have hquotPos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hqPos hdq) hd
    exact Finset.mem_Icc.mpr ⟨hquotPos, (Nat.div_le_self q d).trans hq.2.le⟩
  · intro r hrIcc hrNot
    positivity

/-- Equation (26) with the divisor set enlarged from `gcd(h,q)` to `h`.
This form retains the crucial restriction that each divisor divides `q`. -/
theorem norm_ramanujanSum_le_sum_divisors_filter_dvd
    (q h : ℕ) [NeZero q] (hh : h ≠ 0) :
    ‖ramanujanSum q h‖ ≤
      ∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0 := by
  rw [ramanujanSum_eq_dfi26]
  calc
    ‖∑ d ∈ (Nat.gcd h q).divisors,
        (d : ℂ) * ArithmeticFunction.moebius (q / d)‖ ≤
        ∑ d ∈ (Nat.gcd h q).divisors,
          ‖(d : ℂ) * ArithmeticFunction.moebius (q / d)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (Nat.gcd h q).divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      have hμ : (|ArithmeticFunction.moebius (q / d)| : ℝ) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    _ = ∑ d ∈ (Nat.gcd h q).divisors,
        if d ∣ q then (d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hdg
      have hdGcd := Nat.dvd_of_mem_divisors hdg
      have hdq : d ∣ q := dvd_trans hdGcd (Nat.gcd_dvd_right h q)
      simp [hdq]
    _ ≤ ∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun d => if d ∣ q then (d : ℝ) else 0)
      · intro d hdg
        have hdGcd := Nat.dvd_of_mem_divisors hdg
        have hdh : d ∣ h := dvd_trans hdGcd (Nat.gcd_dvd_left h q)
        exact Nat.mem_divisors.mpr ⟨hdh, hh⟩
      · intro d hdDiv hdNot
        positivity

/-- Sparse-multiple form of the finite equation-(27) tail. -/
theorem sum_Ioo_dvd_weighted_inv_sq_le
    (K L d : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) ≤
      (1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ) := by
  rw [← Finset.sum_filter]
  calc
    ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        (d : ℝ) / (q : ℝ) ^ 2 ≤
        ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
          (1 / (K + 1 : ℝ)) * (1 / ((q / d : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1
      have hdq := (Finset.mem_filter.mp hq).2
      have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
      have hKq : (K + 1 : ℝ) ≤ q := by exact_mod_cast hqIoo.1
      have hdPosR : (0 : ℝ) < d := by exact_mod_cast hd
      have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPos
      have hdRne : (d : ℝ) ≠ 0 := hdPosR.ne'
      have hquot : (q : ℝ) / d = (q / d : ℕ) := by
        rw [Nat.cast_div hdq hdRne]
      calc
        (d : ℝ) / (q : ℝ) ^ 2 = (1 / (q : ℝ)) * ((d : ℝ) / q) := by
          field_simp
        _ ≤ (1 / (K + 1 : ℝ)) * ((d : ℝ) / q) := by
          exact mul_le_mul_of_nonneg_right
            (one_div_le_one_div_of_le (by positivity) hKq)
            (div_nonneg hdPosR.le hqPosR.le)
        _ = (1 / (K + 1 : ℝ)) * (1 / ((q : ℝ) / d)) := by
          field_simp
        _ = (1 / (K + 1 : ℝ)) * (1 / ((q / d : ℕ) : ℝ)) := by
          rw [hquot]
    _ = (1 / (K + 1 : ℝ)) *
        (∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
          (1 / ((q / d : ℕ) : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ (1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_filter_dvd_one_div_quotient_le_harmonic K L d hd)
        (by positivity)

/-- The harmonic loss is bounded by any prescribed positive power, with an
explicit epsilon-dependent constant. -/
theorem harmonic_le_epsilon_rpow
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ((harmonic L : ℚ) : ℝ) ≤
      (1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε) := by
  by_cases hL : L = 0
  · simp [hL, add_nonneg zero_le_one (inv_nonneg.mpr hε.le)]
  have hLPos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  have hpowOne : (1 : ℝ) ≤ (L : ℝ) ^ ε := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hLone hε.le
  have hlogPower := Real.log_le_sub_one_of_pos
    (Real.rpow_pos_of_pos hLPos ε)
  rw [Real.log_rpow hLPos] at hlogPower
  have hlog : Real.log L ≤ ε⁻¹ * ((L : ℝ) ^ ε - 1) := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using hlogPower)
  calc
    ((harmonic L : ℚ) : ℝ) ≤ 1 + Real.log L := harmonic_le_one_add_log L
    _ ≤ 1 + ε⁻¹ * ((L : ℝ) ^ ε - 1) := by linarith
    _ ≤ (1 + ε⁻¹) * ((L : ℝ) ^ ε) := by
      have hinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
      nlinarith
    _ ≤ (1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε) := by
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

end RiemannZeta.GuthMaynard
