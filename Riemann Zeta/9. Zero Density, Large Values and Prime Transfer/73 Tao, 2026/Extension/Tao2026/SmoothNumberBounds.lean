import Tao2026.SmoothNumbers
import Mathlib.NumberTheory.Chebyshev

/-!
# Iterated finite bounds for smooth numbers

Mathlib's square-times-squarefree decomposition gives the familiar estimate
`Ψ(x,y) ≤ 2^π(y) √x`.  Retaining the fact that the square root is itself
smooth lets us iterate this estimate.  The exact recurrence below is the
finite combinatorial core of the much sharper consequence needed in the
bounded-length branch of Theorem 1.9: for `y = O(log x)`, one may choose an
arbitrarily deep fixed iteration and combine it with the prime-counting bound.
-/

open Filter Asymptotics

namespace Tao2026

noncomputable section

/-- A smooth number is a square times a squarefree prime product, with the
square root still smooth. -/
theorem smoothNumbersUpTo_subset_image_smoothRoot (N k : ℕ) :
    Nat.smoothNumbersUpTo N k ⊆
      Finset.image (fun (s, m) => m ^ 2 * s.prod id)
        (k.primesBelow.powerset.product
          (Nat.smoothNumbersUpTo N.sqrt k)) := by
  intro n hn
  obtain ⟨hnLe, hnSmooth⟩ := Nat.mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ :=
    Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers hnSmooth
  have hmDvd : m ∣ n := by
    refine ⟨m * s.prod id, ?_⟩
    rw [hm, pow_two]
    ring
  have hmSmooth : m ∈ Nat.smoothNumbers k :=
    Nat.mem_smoothNumbers_of_dvd hnSmooth hmDvd
  have hmNe : m ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hmSmooth
  have hmSqLe : m ^ 2 ≤ n := by
    rw [hm]
    nth_rw 1 [← mul_one (m ^ 2)]
    gcongr
    exact Finset.one_le_prod' fun p hp =>
      (Nat.prime_of_mem_primesBelow
        (Finset.mem_powerset.mp hs hp)).one_le
  have hmLe : m ≤ N.sqrt := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using hmSqLe.trans hnLe
  rw [Finset.mem_image]
  refine ⟨(s, m), Finset.mem_product.mpr
    ⟨hs, Nat.mem_smoothNumbersUpTo.mpr ⟨hmLe, hmSmooth⟩⟩, ?_⟩
  exact hm.symm

/-- One retained-smoothness step: unlike the standard square-root bound, the
right side still contains a smooth-number count and can be iterated. -/
theorem card_smoothNumbersUpTo_le_pow_two_mul_smoothRoot (N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤
      2 ^ k.primesBelow.card *
        (Nat.smoothNumbersUpTo N.sqrt k).card := by
  calc
    (Nat.smoothNumbersUpTo N k).card ≤
        (Finset.image (fun (s, m) => m ^ 2 * s.prod id)
          (k.primesBelow.powerset.product
            (Nat.smoothNumbersUpTo N.sqrt k))).card :=
      Finset.card_le_card (smoothNumbersUpTo_subset_image_smoothRoot N k)
    _ ≤ (k.primesBelow.powerset.product
          (Nat.smoothNumbersUpTo N.sqrt k)).card :=
      Finset.card_image_le
    _ = 2 ^ k.primesBelow.card *
        (Nat.smoothNumbersUpTo N.sqrt k).card := by simp

/-- Repeated natural square root, arranged so that the first step is taken at
the outermost cutoff. -/
def iteratedNatSqrt : ℕ → ℕ → ℕ
  | 0, N => N
  | r + 1, N => iteratedNatSqrt r N.sqrt

@[simp]
theorem iteratedNatSqrt_zero (N : ℕ) : iteratedNatSqrt 0 N = N := rfl

@[simp]
theorem iteratedNatSqrt_succ (r N : ℕ) :
    iteratedNatSqrt (r + 1) N = iteratedNatSqrt r N.sqrt := rfl

/-- Exact `r`-step form of the retained-smoothness recurrence. -/
theorem card_smoothNumbersUpTo_le_iteratedSqrt
    (r N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤
      (2 ^ k.primesBelow.card) ^ r *
        (Nat.smoothNumbersUpTo (iteratedNatSqrt r N) k).card := by
  induction r generalizing N with
  | zero => simp
  | succ r ihr =>
      calc
        (Nat.smoothNumbersUpTo N k).card ≤
            2 ^ k.primesBelow.card *
              (Nat.smoothNumbersUpTo N.sqrt k).card :=
          card_smoothNumbersUpTo_le_pow_two_mul_smoothRoot N k
        _ ≤ 2 ^ k.primesBelow.card *
            ((2 ^ k.primesBelow.card) ^ r *
              (Nat.smoothNumbersUpTo (iteratedNatSqrt r N.sqrt) k).card) :=
          Nat.mul_le_mul_left _ (ihr N.sqrt)
        _ = (2 ^ k.primesBelow.card) ^ (r + 1) *
            (Nat.smoothNumbersUpTo (iteratedNatSqrt (r + 1) N) k).card := by
          rw [iteratedNatSqrt_succ, pow_succ]
          ring

/-- Discarding the final smoothness condition gives a completely explicit
finite bound. -/
theorem card_smoothNumbersUpTo_le_pow_two_pow_mul_iteratedSqrt
    (r N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤
      (2 ^ k.primesBelow.card) ^ r * iteratedNatSqrt r N := by
  have hfinal :
      (Nat.smoothNumbersUpTo (iteratedNatSqrt r N) k).card ≤
        iteratedNatSqrt r N := by
    have hsum := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card
      (iteratedNatSqrt r N) k
    omega
  exact (card_smoothNumbersUpTo_le_iteratedSqrt r N k).trans
    (Nat.mul_le_mul_left _ hfinal)

/-- Source-inclusive form of the explicit iterated bound. -/
theorem psiNat_le_pow_two_primeCounting_mul_iteratedSqrt
    (r x P : ℕ) :
    psiNat x P ≤
      (2 ^ (P + 1).primesBelow.card) ^ r * iteratedNatSqrt r x := by
  simpa [psiNat] using
    card_smoothNumbersUpTo_le_pow_two_pow_mul_iteratedSqrt r x (P + 1)

/-- The terminal cutoff after `r` iterations is at most the real
`2⁻ʳ`-power of the original cutoff. -/
theorem iteratedNatSqrt_cast_le_rpow (r N : ℕ) :
    (iteratedNatSqrt r N : ℝ) ≤
      (N : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ r) := by
  induction r generalizing N with
  | zero => simp
  | succ r ihr =>
      calc
        (iteratedNatSqrt (r + 1) N : ℝ) =
            (iteratedNatSqrt r N.sqrt : ℝ) := rfl
        _ ≤ (N.sqrt : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ r) := ihr N.sqrt
        _ ≤ (Real.sqrt (N : ℝ)) ^ ((1 : ℝ) / (2 : ℝ) ^ r) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _)
            Real.nat_sqrt_le_real_sqrt (by positivity)
        _ = (N : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (r + 1)) := by
          rw [Real.sqrt_eq_rpow,
            ← Real.rpow_mul (Nat.cast_nonneg N)]
          congr 1
          rw [pow_succ]
          field_simp

/-- If the number of available smooth primes is `o(log x)`, then the
corresponding smooth-number count is subpolynomial.  This is the abstract
asymptotic consumer of the exact iterated finite bound. -/
theorem psiNat_powerUpperBound_zero_of_primeCount_isLittleO (P : ℕ → ℕ)
    (hprime : (fun x : ℕ => ((P x + 1).primesBelow.card : ℝ))
      =o[atTop] fun x : ℕ => Real.log x) :
    PowerUpperBound (fun x => (psiNat x (P x) : ℝ)) 0 := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / ε : ℝ)
  have hrpow : (2 / ε : ℝ) < (2 : ℝ) ^ r := by
    calc
      (2 / ε : ℝ) < (r : ℝ) := hr
      _ < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast r.lt_two_pow_self
      _ = (2 : ℝ) ^ r := by norm_num
  have hrpos : 0 < (r : ℝ) := by
    have : 0 < 2 / ε := by positivity
    linarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : ℝ := (r : ℝ) * Real.log 2
  have hK : 0 < K := by dsimp only [K]; positivity
  let c : ℝ := ε / (2 * K)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hprimeEvent := hprime.def hc
  have hsmall : (1 : ℝ) / (2 : ℝ) ^ r < ε / 2 := by
    have htwo : (2 : ℝ) < ε * (2 : ℝ) ^ r := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hrpow
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)]
    nlinarith
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hprimeEvent, eventually_ge_atTop (1 : ℕ)] with x hxprime hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hprime' : ((P x + 1).primesBelow.card : ℝ) ≤
      c * Real.log x := by
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg hlogx] using hxprime
  have hexponent :
      (((P x + 1).primesBelow.card : ℝ) * (r : ℝ)) * Real.log 2 ≤
        (ε / 2) * Real.log x := by
    calc
      (((P x + 1).primesBelow.card : ℝ) * (r : ℝ)) * Real.log 2 =
          ((P x + 1).primesBelow.card : ℝ) * K := by
        dsimp only [K]
        ring
      _ ≤ (c * Real.log x) * K :=
        mul_le_mul_of_nonneg_right hprime' hK.le
      _ = (ε / 2) * Real.log x := by
        dsimp only [c]
        field_simp
  have hfactor :
      (((2 ^ (P x + 1).primesBelow.card) ^ r : ℕ) : ℝ) ≤
        (x : ℝ) ^ (ε / 2) := by
    rw [← pow_mul]
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
      Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hexponent
  have hsqrt : (iteratedNatSqrt r x : ℝ) ≤
      (x : ℝ) ^ (ε / 2) := by
    exact (iteratedNatSqrt_cast_le_rpow r x).trans
      (Real.rpow_le_rpow_of_exponent_le hxone hsmall.le)
  have hfinite := psiNat_le_pow_two_primeCounting_mul_iteratedSqrt r x (P x)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  calc
    (psiNat x (P x) : ℝ) ≤
        (((2 ^ (P x + 1).primesBelow.card) ^ r : ℕ) : ℝ) *
          (iteratedNatSqrt r x : ℝ) := by exact_mod_cast hfinite
    _ ≤ (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) :=
      mul_le_mul hfactor hsqrt (Nat.cast_nonneg _) (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ (0 + ε) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring

/-- Any natural smoothness budget which tends to infinity but remains
`O(log x)` has only `o(log x)` available primes. -/
theorem card_primesBelow_succ_isLittleO_log_of_isBigO_log (P : ℕ → ℕ)
    (hP : (fun x : ℕ => (P x : ℝ)) =O[atTop]
      fun x : ℕ => Real.log x)
    (hPtop : Tendsto P atTop atTop) :
    (fun x : ℕ => ((P x + 1).primesBelow.card : ℝ))
      =o[atTop] fun x : ℕ => Real.log x := by
  obtain ⟨C, hC⟩ := hP.bound
  let D : ℝ := |C| + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hPBound : ∀ᶠ x : ℕ in atTop,
      (P x : ℝ) ≤ D * |Real.log x| := by
    filter_upwards [hC] with x hx
    have hCD : C ≤ D := by
      dsimp only [D]
      exact le_add_of_le_of_nonneg (le_abs_self C) zero_le_one
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs] using
      hx.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))
  have hPRealTop : Tendsto (fun x : ℕ => (P x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hPtop
  have hlogPTop : Tendsto (fun x : ℕ => Real.log (P x)) atTop atTop :=
    Real.tendsto_log_atTop.comp hPRealTop
  have hchebReal := Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
  have hcheb := hPRealTop.eventually hchebReal
  apply IsLittleO.of_bound
  intro c hc
  let K : ℝ := Real.log 4 + 1
  have hK : 0 < K := by
    dsimp only [K]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hlargeLog : ∀ᶠ x : ℕ in atTop, K * D / c ≤ Real.log (P x) :=
    hlogPTop.eventually (eventually_ge_atTop (K * D / c))
  filter_upwards [hPBound, hcheb, hlargeLog,
    eventually_ge_atTop (1 : ℕ), hPtop.eventually (eventually_ge_atTop 2)] with
      x hxP hxCheb hxLog hx hxPtwo
  have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxOne
  have hlogP : 0 < Real.log (P x) := Real.log_pos (by exact_mod_cast hxPtwo)
  have hxP' : (P x : ℝ) ≤ D * Real.log x := by
    simpa [abs_of_nonneg hlogx] using hxP
  have hxCheb' : (P x).primeCounting ≤
      K * (P x : ℝ) / Real.log (P x) := by
    simpa [K] using hxCheb
  have hKD : K * D ≤ c * Real.log (P x) := by
    rw [div_le_iff₀ hc] at hxLog
    nlinarith
  have hbound : ((P x).primeCounting : ℝ) ≤ c * Real.log x := by
    calc
      ((P x).primeCounting : ℝ) ≤
          K * (P x : ℝ) / Real.log (P x) := hxCheb'
      _ ≤ K * (D * Real.log x) / Real.log (P x) := by gcongr
      _ ≤ c * Real.log x := by
        rw [div_le_iff₀ hlogP]
        nlinarith
  have hcard : (P x + 1).primesBelow.card = (P x).primeCounting := by
    rw [Nat.primesBelow_card_eq_primeCounting',
      ← Nat.primeCounting_eq_primeCounting'_succ]
  rw [hcard]
  simpa [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg hlogx] using hbound

/-- Direct specialized consequence needed by the bounded-length branch: an
`O(log x)` smoothness budget tending to infinity has `x^o(1)` smooth
numbers. -/
theorem psiNat_powerUpperBound_zero_of_isBigO_log
    (P : ℕ → ℕ)
    (hP : (fun x : ℕ => (P x : ℝ)) =O[atTop]
      fun x : ℕ => Real.log x)
    (hPtop : Tendsto P atTop atTop) :
    PowerUpperBound (fun x => (psiNat x (P x) : ℝ)) 0 :=
  psiNat_powerUpperBound_zero_of_primeCount_isLittleO P
    (card_primesBelow_succ_isLittleO_log_of_isBigO_log P hP hPtop)

noncomputable def logarithmicSmoothnessBudget (C : ℝ) (x : ℕ) : ℕ :=
  ⌈C * Real.log (x + 2)⌉₊

/-- A positive constant multiple of `log (x+2)`, rounded upward to a
natural smoothness budget, tends to infinity. -/
theorem tendsto_logarithmicSmoothnessBudget_atTop {C : ℝ} (hC : 0 < C) :
    Tendsto (logarithmicSmoothnessBudget C) atTop atTop := by
  have hshift : Tendsto (fun x : ℕ => (x : ℝ) + 2) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 2)
  have hlog : Tendsto (fun x : ℕ => Real.log (x + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  have hmul : Tendsto (fun x : ℕ => C * Real.log (x + 2)) atTop atTop :=
    hlog.const_mul_atTop hC
  exact (tendsto_nat_ceil_atTop :
    Tendsto (fun y : ℝ => ⌈y⌉₊) atTop atTop).comp hmul

/-- The rounded logarithmic budget remains `O(log x)`. -/
theorem logarithmicSmoothnessBudget_isBigO_log {C : ℝ} (hC : 0 < C) :
    (fun x : ℕ => (logarithmicSmoothnessBudget C x : ℝ)) =O[atTop]
      fun x : ℕ => Real.log x := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : ℝ := 2 * C + 1 / Real.log 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hxTwo : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have harg : (x : ℝ) + 2 ≤ (x : ℝ) ^ 2 := by
    nlinarith
  have hlogshift : Real.log (x + 2) ≤ 2 * Real.log x := by
    calc
      Real.log (x + 2) ≤ Real.log ((x : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hceil : (logarithmicSmoothnessBudget C x : ℝ) <
      C * Real.log (x + 2) + 1 := by
    exact Nat.ceil_lt_add_one
      (mul_nonneg hC.le (Real.log_nonneg (by
        exact_mod_cast (by omega : 1 ≤ x + 2))))
  have hlogTwoLe : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hxTwo
  have hone : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log x := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hlogTwo]
    simpa [mul_comm] using hlogTwoLe
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg hlogx.le]
  calc
    (logarithmicSmoothnessBudget C x : ℝ) ≤ C * Real.log (x + 2) + 1 := hceil.le
    _ ≤ C * (2 * Real.log x) +
        (1 / Real.log 2) * Real.log x := by gcongr
    _ = K * Real.log x := by
      dsimp only [K]
      ring

/-- Every fixed rounded logarithmic budget is itself subpolynomial. -/
theorem logarithmicSmoothnessBudget_powerUpperBound_zero
    {C : ℝ} (hC : 0 < C) :
    PowerUpperBound
      (fun x => (logarithmicSmoothnessBudget C x : ℝ)) 0 := by
  intro ε hε
  have hlog : (fun x : ℕ => Real.log x) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ ε) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hε).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (logarithmicSmoothnessBudget_isBigO_log hC).trans
    (by simpa using hlog.isBigO)

/-- Fully concrete bounded-length smooth-number estimate: every fixed
positive logarithmic smoothness budget contains only `x^o(1)` positive
smooth numbers up to `x`. -/
theorem psiNat_logarithmicSmoothnessBudget_powerUpperBound_zero
    {C : ℝ} (hC : 0 < C) :
    PowerUpperBound
      (fun x => (psiNat x (logarithmicSmoothnessBudget C x) : ℝ)) 0 :=
  psiNat_powerUpperBound_zero_of_isBigO_log
    (logarithmicSmoothnessBudget C)
    (logarithmicSmoothnessBudget_isBigO_log hC)
    (tendsto_logarithmicSmoothnessBudget_atTop hC)

end

end Tao2026
