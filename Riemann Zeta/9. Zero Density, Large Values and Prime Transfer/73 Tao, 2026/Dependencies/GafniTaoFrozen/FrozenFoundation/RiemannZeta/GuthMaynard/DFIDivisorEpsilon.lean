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

/-- Taking the canonical representative modulo `q` does not change its
gcd with `q`. -/
theorem gcd_zmod_intCast_val (q : ℕ) [NeZero q] (z : ℤ) :
    Nat.gcd ((z : ZMod q).val) q = z.gcd q := by
  rw [← Int.gcd_emod z q, ← ZMod.val_intCast]
  rfl

/-- Source form of `gcd_zmod_intCast_val` for the first argument `-h` in
DFI's Kloosterman sum. -/
theorem gcd_neg_intCast_zmod_val (q : ℕ) [NeZero q] (h : ℤ) :
    Nat.gcd ((-h : ZMod q).val) q = Nat.gcd h.natAbs q := by
  rw [← Int.cast_neg]
  calc
    Nat.gcd (((-h : ℤ) : ZMod q).val) q = (-h).gcd q :=
      gcd_zmod_intCast_val q (-h)
    _ = Nat.gcd h.natAbs q := by simp [Int.gcd_def]

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

/-- Square-root analogue of the sparse-multiple estimate.  This is the
arithmetic summation used after DFI equation (29): writing `q = d r`
cancels the factor `sqrt d`, and Cauchy--Schwarz leaves only the ordinary
harmonic sum. -/
theorem sum_Ioo_dvd_sqrt_div_sqrt_le
    (K L d : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then Real.sqrt d / Real.sqrt q else 0) ≤
      Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
  rw [← Finset.sum_filter]
  let S := (Finset.Ioo K L).filter (d ∣ ·)
  have hterm : ∀ q ∈ S,
      Real.sqrt d / Real.sqrt q = 1 / Real.sqrt ((q / d : ℕ) : ℝ) := by
    intro q hq
    have hdq := (Finset.mem_filter.mp hq).2
    have hqPos := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
    have hdNe : (d : ℝ) ≠ 0 := hdR.ne'
    rw [← Real.sqrt_div (Nat.cast_nonneg d) q]
    have hcast : (d : ℝ) / q = 1 / ((q / d : ℕ) : ℝ) := by
      rw [Nat.cast_div hdq hdNe]
      field_simp
    rw [hcast, Real.sqrt_div (by positivity)]
    simp
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun _ : ℕ ↦ (1 : ℝ))
    (fun q ↦ 1 / Real.sqrt ((q / d : ℕ) : ℝ))
  have hsq :
      (∑ q ∈ S, (1 / Real.sqrt ((q / d : ℕ) : ℝ)) ^ 2) =
        ∑ q ∈ S, 1 / ((q / d : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqDivPos : 0 < q / d := by
      have hqPos := lt_of_le_of_lt (Nat.zero_le K)
        (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).1
      exact Nat.div_pos (Nat.le_of_dvd hqPos (Finset.mem_filter.mp hq).2) hd
    rw [div_pow, one_pow, Real.sq_sqrt (by exact_mod_cast hqDivPos.le)]
  have hcard : (S.card : ℝ) ≤ L := by
    have hc := Finset.card_le_card (show S ⊆ Finset.range L by
      intro q hq
      exact Finset.mem_range.mpr
        (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).2)
    simpa using hc
  have hsum := sum_Ioo_filter_dvd_one_div_quotient_le_harmonic K L d hd
  change (∑ q ∈ S, Real.sqrt d / Real.sqrt q) ≤ _
  calc
    ∑ q ∈ S, Real.sqrt d / Real.sqrt q =
        ∑ q ∈ S, 1 / Real.sqrt ((q / d : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          exact hterm
    _ = ∑ q ∈ S, (1 : ℝ) *
        (1 / Real.sqrt ((q / d : ℕ) : ℝ)) := by simp
    _ ≤ Real.sqrt (∑ _q ∈ S, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ q ∈ S,
          (1 / Real.sqrt ((q / d : ℕ) : ℝ)) ^ 2) := hCS
    _ = Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ q ∈ S, 1 / ((q / d : ℕ) : ℝ)) := by
          rw [hsq]
          simp
    _ ≤ Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      gcongr

/-- The square root of a gcd is dominated by the sparse divisor expansion
over the fixed first argument.  Unlike the pointwise estimate
`sqrt (gcd H q) ≤ sqrt q`, this keeps the divisibility condition needed for
the uniform modulus average in DFI equation (24). -/
theorem sqrt_gcd_le_sum_divisors_filter_dvd
    (H q : ℕ) (hH : H ≠ 0) :
    Real.sqrt (Nat.gcd H q) ≤
      ∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0 := by
  let g := Nat.gcd H q
  have hgH : g ∈ H.divisors := Nat.mem_divisors.mpr
    ⟨Nat.gcd_dvd_left H q, hH⟩
  have hgq : g ∣ q := Nat.gcd_dvd_right H q
  calc
    Real.sqrt (Nat.gcd H q) = if g ∣ q then Real.sqrt g else 0 := by
      simp [g, hgq]
    _ ≤ ∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0 := by
      refine Finset.single_le_sum (s := H.divisors)
        (f := fun d ↦ if d ∣ q then Real.sqrt d else 0) ?_ hgH
      intro d hd
      dsimp
      split_ifs <;> positivity

/-- Uniform average of the square-root gcd factor that occurs in Weil's
bound.  The fixed shift enters only through its divisor count; the modulus
range has the sharp square-root length required by DFI's double-dual term. -/
theorem sum_Ioo_sqrt_gcd_div_sqrt_le
    (K L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Ioo K L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q) ≤
      (H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
  calc
    ∑ q ∈ Finset.Ioo K L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q ≤
      ∑ q ∈ Finset.Ioo K L,
        (∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0) /
          Real.sqrt q := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact sqrt_gcd_le_sum_divisors_filter_dvd H q hH
    _ = ∑ d ∈ H.divisors, ∑ q ∈ Finset.Ioo K L,
        if d ∣ q then Real.sqrt d / Real.sqrt q else 0 := by
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ ≤ ∑ _d ∈ H.divisors,
        Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact sum_Ioo_dvd_sqrt_div_sqrt_le K L d
        (Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hH))
    _ = (H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      simp
      ring

/-- Weil's square-root gcd factor averaged together with the divisor
factor from equation (25).  This is the exact finite estimate used in the
DFI error assembly before the harmless harmonic and divisor losses are
absorbed into `Q^ε`. -/
theorem sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_le
    (L H : ℕ) (hH : H ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    (∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        ((H.divisors.card : ℝ) * Real.sqrt L *
          Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
  let D := divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (divisorEpsilonConstant_pos δ).le
      (zero_le_one.trans (le_max_left 1 ((L : ℝ) ^ δ)))
  calc
    ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (q.divisors.card : ℝ) ≤
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) * D := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      have hqLt := (Finset.mem_Ioo.mp hq).2
      have hdiv := card_divisors_le_const_mul_rpow hδ hqPos.ne'
      have hqL : (q : ℝ) ^ δ ≤ max 1 ((L : ℝ) ^ δ) := by
        apply le_max_of_le_right
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqLt.le) hδ.le
      gcongr
      exact hdiv.trans (mul_le_mul_of_nonneg_left hqL
        (divisorEpsilonConstant_pos δ).le)
    _ = D * (∑ q ∈ Finset.Ioo 0 L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ D * ((H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
      gcongr
      exact sum_Ioo_sqrt_gcd_div_sqrt_le 0 L H hH

/-- Uniform-in-the-shift version of the equation-(25) modulus average.
This is the estimate used in DFI Theorem 1: `gcd(H,q) ≤ q` removes every
dependence on `H`, while the pointwise divisor bound costs only `L^δ`. -/
theorem sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_uniform_le
    (K L H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (∑ q ∈ Finset.Ioo K L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L := by
  let D := divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (divisorEpsilonConstant_pos δ).le
      (zero_le_one.trans (le_max_left 1 ((L : ℝ) ^ δ)))
  have hcard : ((Finset.Ioo K L).card : ℝ) ≤ L := by
    have hs : Finset.Ioo K L ⊆ Finset.range L := by
      intro q hq
      exact Finset.mem_range.mpr (Finset.mem_Ioo.mp hq).2
    have hc : (Finset.Ioo K L).card ≤ L := by
      simpa using Finset.card_le_card hs
    exact_mod_cast hc
  calc
    _ ≤ ∑ _q ∈ Finset.Ioo K L, D := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        lt_of_le_of_lt (Nat.zero_le K) (Finset.mem_Ioo.mp hq).1
      have hqLt : q < L := (Finset.mem_Ioo.mp hq).2
      have hgcd : Nat.gcd H q ≤ q := Nat.gcd_le_right H hqPos
      have hsqrt : Real.sqrt (Nat.gcd H q) ≤ Real.sqrt q := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast hgcd)
      have hratio : Real.sqrt (Nat.gcd H q) / Real.sqrt q ≤ 1 := by
        exact (div_le_one (Real.sqrt_pos.2 (by exact_mod_cast hqPos))).2 hsqrt
      have hdiv := card_divisors_le_const_mul_rpow hδ hqPos.ne'
      have hqL : (q : ℝ) ^ δ ≤ max 1 ((L : ℝ) ^ δ) := by
        apply le_max_of_le_right
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqLt.le) hδ.le
      have hdivD : (q.divisors.card : ℝ) ≤ D := by
        exact hdiv.trans (mul_le_mul_of_nonneg_left hqL
          (divisorEpsilonConstant_pos δ).le)
      calc
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
            (q.divisors.card : ℝ) ≤ 1 * (q.divisors.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
        _ = (q.divisors.card : ℝ) := one_mul _
        _ ≤ D := hdivD
    _ = ((Finset.Ioo K L).card : ℝ) * D := by simp
    _ ≤ (L : ℝ) * D := mul_le_mul_of_nonneg_right hcard hD
    _ = divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) * L := by
      dsimp [D]
      ring
    _ = _ := by rfl

/-- A gcd is bounded by the sparse divisor expansion over either fixed
argument.  This is the non-square-root companion of
`sqrt_gcd_le_sum_divisors_filter_dvd`. -/
theorem gcd_le_sum_divisors_filter_dvd
    (H q : ℕ) (hH : H ≠ 0) :
    (Nat.gcd H q : ℝ) ≤
      ∑ d ∈ H.divisors, if d ∣ q then (d : ℝ) else 0 := by
  let g := Nat.gcd H q
  have hgH : g ∈ H.divisors := Nat.mem_divisors.mpr
    ⟨Nat.gcd_dvd_left H q, hH⟩
  have hgq : g ∣ q := Nat.gcd_dvd_right H q
  calc
    (Nat.gcd H q : ℝ) = if g ∣ q then (g : ℝ) else 0 := by
      simp [g, hgq]
    _ ≤ ∑ d ∈ H.divisors, if d ∣ q then (d : ℝ) else 0 := by
      refine Finset.single_le_sum (s := H.divisors)
        (f := fun d ↦ if d ∣ q then (d : ℝ) else 0) ?_ hgH
      intro d hd
      dsimp
      split_ifs <;> positivity

/-- The harmonic sparse-modulus average of `gcd(H,q)/q`. -/
theorem sum_Ioo_gcd_div_le
    (K L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Ioo K L,
        (Nat.gcd H q : ℝ) / q) ≤
      (H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ)) := by
  calc
    ∑ q ∈ Finset.Ioo K L, (Nat.gcd H q : ℝ) / q ≤
      ∑ q ∈ Finset.Ioo K L,
        (∑ d ∈ H.divisors, if d ∣ q then (d : ℝ) else 0) / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : (0 : ℝ) < q := by
        exact_mod_cast lt_of_le_of_lt (Nat.zero_le K) (Finset.mem_Ioo.mp hq).1
      exact div_le_div_of_nonneg_right
        (gcd_le_sum_divisors_filter_dvd H q hH) hqPos.le
    _ = ∑ d ∈ H.divisors, ∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / q else 0 := by
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ ≤ ∑ _d ∈ H.divisors, (((harmonic L : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hH)
      calc
        (∑ q ∈ Finset.Ioo K L, if d ∣ q then (d : ℝ) / q else 0) =
            ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
              1 / ((q / d : ℕ) : ℝ) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro q hq
          have hdq := (Finset.mem_filter.mp hq).2
          have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
            (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).1
          have hdR : (0 : ℝ) < d := by exact_mod_cast hdPos
          have hcast : (q : ℝ) / d = (q / d : ℕ) := by
            rw [Nat.cast_div hdq hdR.ne']
          rw [← hcast]
          field_simp
        _ ≤ (((harmonic L : ℚ) : ℝ)) :=
          sum_Ioo_filter_dvd_one_div_quotient_le_harmonic K L d hdPos
    _ = (H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ)) := by simp

/-- The unweighted sparse-modulus average of `gcd(H,q)`.  Expanding the
gcd through divisors of the fixed integer `H`, each divisor `d` occurs on at
most `L / d` moduli and its weight `d` cancels that density. -/
theorem sum_Ioo_gcd_le
    (K L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Ioo K L, (Nat.gcd H q : ℝ)) ≤
      (H.divisors.card : ℝ) * L := by
  calc
    ∑ q ∈ Finset.Ioo K L, (Nat.gcd H q : ℝ) ≤
        ∑ q ∈ Finset.Ioo K L,
          ∑ d ∈ H.divisors, if d ∣ q then (d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _hq
      exact gcd_le_sum_divisors_filter_dvd H q hH
    _ = ∑ d ∈ H.divisors,
        ∑ q ∈ Finset.Ioo K L, if d ∣ q then (d : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _d ∈ H.divisors, (L : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hH)
      have hsub : (Finset.Ioo K L).filter (d ∣ ·) ⊆
          (Finset.Ioc 0 L).filter (d ∣ ·) := by
        intro q hq
        have hqMem := Finset.mem_filter.mp hq
        have hqIoo := Finset.mem_Ioo.mp hqMem.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨lt_of_le_of_lt (Nat.zero_le K) hqIoo.1, hqIoo.2.le⟩, hqMem.2⟩
      have hcard : ((Finset.Ioo K L).filter (d ∣ ·)).card ≤ L / d := by
        calc
          ((Finset.Ioo K L).filter (d ∣ ·)).card ≤
              ((Finset.Ioc 0 L).filter (d ∣ ·)).card :=
            Finset.card_le_card hsub
          _ = L / d := Nat.Ioc_filter_dvd_card_eq_div L d
      have hweighted : ((Finset.Ioo K L).filter (d ∣ ·)).card * d ≤ L := by
        exact (Nat.mul_le_mul_right d hcard).trans (Nat.div_mul_le_self L d)
      calc
        (∑ q ∈ Finset.Ioo K L, if d ∣ q then (d : ℝ) else 0) =
            ∑ _q ∈ (Finset.Ioo K L).filter (d ∣ ·), (d : ℝ) := by
          rw [← Finset.sum_filter]
        _ = (((Finset.Ioo K L).filter (d ∣ ·)).card : ℝ) * d := by simp
        _ ≤ (L : ℝ) := by exact_mod_cast hweighted
    _ = (H.divisors.card : ℝ) * L := by simp

/-- Sharp average for the two square-root gcd factors in a single-dual DFI
term.  Cauchy--Schwarz converts both factors to the harmonic gcd average;
the divisor function of the running modulus is absorbed by its standard
epsilon bound. -/
theorem sum_Ioo_two_sqrt_gcd_mul_divisors_div_le
    (K L H A : ℕ) (hH : H ≠ 0) (hA : A ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) :
    (∑ q ∈ Finset.Ioo K L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd A q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        (Real.sqrt ((H.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt ((A.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ)))) := by
  let S := Finset.Ioo K L
  let D := divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ)
  have hD : 0 ≤ D := mul_nonneg (divisorEpsilonConstant_pos δ).le
    (zero_le_one.trans (le_max_left 1 ((L : ℝ) ^ δ)))
  have hpoint (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card : ℝ) ≤ D := by
    have hqIoo := Finset.mem_Ioo.mp hq
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
    have hdiv := card_divisors_le_const_mul_rpow hδ hqPos.ne'
    have hqL : (q : ℝ) ^ δ ≤ max 1 ((L : ℝ) ^ δ) := by
      apply le_max_of_le_right
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqIoo.2.le) hδ.le
    exact hdiv.trans (mul_le_mul_of_nonneg_left hqL
      (divisorEpsilonConstant_pos δ).le)
  have hsqH :
      (∑ q ∈ S, (Real.sqrt (Nat.gcd H q) / Real.sqrt q) ^ 2) =
        ∑ q ∈ S, (Nat.gcd H q : ℝ) / q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (by exact_mod_cast hqPos.le)]
  have hsqA :
      (∑ q ∈ S, (Real.sqrt (Nat.gcd A q) / Real.sqrt q) ^ 2) =
        ∑ q ∈ S, (Nat.gcd A q : ℝ) / q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (by exact_mod_cast hqPos.le)]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun q ↦ Real.sqrt (Nat.gcd H q) / Real.sqrt q)
    (fun q ↦ Real.sqrt (Nat.gcd A q) / Real.sqrt q)
  have hHsum := sum_Ioo_gcd_div_le K L H hH
  have hAsum := sum_Ioo_gcd_div_le K L A hA
  change (∑ q ∈ S,
      (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
        (Real.sqrt (Nat.gcd A q) / Real.sqrt q) *
        (q.divisors.card : ℝ)) ≤ _
  calc
    _ ≤ ∑ q ∈ S, D *
        ((Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd A q) / Real.sqrt q)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hu : 0 ≤ Real.sqrt (Nat.gcd H q) / Real.sqrt q := by positivity
      have hv : 0 ≤ Real.sqrt (Nat.gcd A q) / Real.sqrt q := by positivity
      calc
        _ ≤ (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd A q) / Real.sqrt q) * D := by
          exact mul_le_mul_of_nonneg_left (hpoint q hq) (mul_nonneg hu hv)
        _ = _ := by ring
    _ = D * ∑ q ∈ S,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd A q) / Real.sqrt q) := by rw [Finset.mul_sum]
    _ ≤ D * (Real.sqrt (∑ q ∈ S,
          (Real.sqrt (Nat.gcd H q) / Real.sqrt q) ^ 2) *
        Real.sqrt (∑ q ∈ S,
          (Real.sqrt (Nat.gcd A q) / Real.sqrt q) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hCS hD
    _ = D * (Real.sqrt (∑ q ∈ S, (Nat.gcd H q : ℝ) / q) *
        Real.sqrt (∑ q ∈ S, (Nat.gcd A q : ℝ) / q)) := by
      rw [hsqH, hsqA]
    _ ≤ D * (Real.sqrt ((H.divisors.card : ℝ) *
          (((harmonic L : ℚ) : ℝ))) *
        Real.sqrt ((A.divisors.card : ℝ) *
          (((harmonic L : ℚ) : ℝ)))) := by
      gcongr
    _ = _ := by rfl

/-- Coprimality combines the two reduced-modulus gcds into the single fixed
integer `A * B`.  This is the arithmetic compression used in the double-dual
part of DFI equation (30). -/
theorem gcd_mul_gcd_le_gcd_mul_of_coprime
    (A B q : ℕ) (hAB : A.Coprime B) (hq : 0 < q) :
    Nat.gcd A q * Nat.gcd B q ≤ Nat.gcd (A * B) q := by
  have hleft : Nat.gcd A q * Nat.gcd B q ∣ A * B :=
    mul_dvd_mul (Nat.gcd_dvd_left A q) (Nat.gcd_dvd_left B q)
  have hright : Nat.gcd A q * Nat.gcd B q ∣ q :=
    by
      simpa [Nat.gcd_comm] using
        (hAB.gcd_both q q).mul_dvd_of_dvd_of_dvd
          (Nat.gcd_dvd_left q A) (Nat.gcd_dvd_left q B)
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right (A * B) hq)
    (Nat.dvd_gcd hleft hright)

/-- Sharp average for the three square-root gcd factors in the double-dual
DFI term.  Coprimality combines the coefficient gcds, after which
Cauchy--Schwarz gives exactly the square-root length in equation (30). -/
theorem sum_Ioo_three_sqrt_gcd_mul_divisors_div_sqrt_le
    (K L H A B : ℕ) (hH : H ≠ 0) (hA : 0 < A) (hB : 0 < B)
    (hAB : A.Coprime B) (δ : ℝ) (hδ : 0 < δ) :
    (∑ q ∈ Finset.Ioo K L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd A q * Nat.gcd B q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        (Real.sqrt ((H.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt (((A * B).divisors.card : ℝ) * L)) := by
  let S := Finset.Ioo K L
  let D := divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ)
  have hD : 0 ≤ D := mul_nonneg (divisorEpsilonConstant_pos δ).le
    (zero_le_one.trans (le_max_left 1 ((L : ℝ) ^ δ)))
  have hpoint (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card : ℝ) ≤ D := by
    have hqIoo := Finset.mem_Ioo.mp hq
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
    have hdiv := card_divisors_le_const_mul_rpow hδ hqPos.ne'
    have hqL : (q : ℝ) ^ δ ≤ max 1 ((L : ℝ) ^ δ) := by
      apply le_max_of_le_right
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqIoo.2.le) hδ.le
    exact hdiv.trans (mul_le_mul_of_nonneg_left hqL
      (divisorEpsilonConstant_pos δ).le)
  have hcompress (q : ℕ) (hq : q ∈ S) :
      Real.sqrt (Nat.gcd A q * Nat.gcd B q) ≤
        Real.sqrt (Nat.gcd (A * B) q) := by
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    exact Real.sqrt_le_sqrt (by exact_mod_cast
      gcd_mul_gcd_le_gcd_mul_of_coprime A B q hAB hqPos)
  have hsqH :
      (∑ q ∈ S, (Real.sqrt (Nat.gcd H q) / Real.sqrt q) ^ 2) =
        ∑ q ∈ S, (Nat.gcd H q : ℝ) / q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (by exact_mod_cast hqPos.le)]
  have hsqAB :
      (∑ q ∈ S, (Real.sqrt (Nat.gcd (A * B) q)) ^ 2) =
        ∑ q ∈ S, (Nat.gcd (A * B) q : ℝ) := by
    apply Finset.sum_congr rfl
    intro q _hq
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun q ↦ Real.sqrt (Nat.gcd H q) / Real.sqrt q)
    (fun q ↦ Real.sqrt (Nat.gcd (A * B) q))
  have hHsum := sum_Ioo_gcd_div_le K L H hH
  have hABne : A * B ≠ 0 := Nat.mul_ne_zero hA.ne' hB.ne'
  have hABsum := sum_Ioo_gcd_le K L (A * B) hABne
  change (∑ q ∈ S,
      (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
        Real.sqrt (Nat.gcd A q * Nat.gcd B q) *
        (q.divisors.card : ℝ)) ≤ _
  calc
    _ ≤ ∑ q ∈ S, D *
        ((Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd (A * B) q)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hu : 0 ≤ Real.sqrt (Nat.gcd H q) / Real.sqrt q := by positivity
      calc
        _ ≤ (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd (A * B) q) *
            (q.divisors.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcompress q hq) hu)
            (Nat.cast_nonneg _)
        _ ≤ (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd (A * B) q) * D := by
          exact mul_le_mul_of_nonneg_left (hpoint q hq)
            (mul_nonneg hu (Real.sqrt_nonneg _))
        _ = _ := by ring
    _ = D * ∑ q ∈ S,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd (A * B) q) := by rw [Finset.mul_sum]
    _ ≤ D * (Real.sqrt (∑ q ∈ S,
          (Real.sqrt (Nat.gcd H q) / Real.sqrt q) ^ 2) *
        Real.sqrt (∑ q ∈ S,
          (Real.sqrt (Nat.gcd (A * B) q)) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hCS hD
    _ = D * (Real.sqrt (∑ q ∈ S, (Nat.gcd H q : ℝ) / q) *
        Real.sqrt (∑ q ∈ S, (Nat.gcd (A * B) q : ℝ))) := by
      rw [hsqH, hsqAB]
    _ ≤ D * (Real.sqrt ((H.divisors.card : ℝ) *
          (((harmonic L : ℚ) : ℝ))) *
        Real.sqrt (((A * B).divisors.card : ℝ) * L)) := by
      gcongr
    _ = _ := by rfl

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
