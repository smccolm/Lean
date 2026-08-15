import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- The two error terms on the last line of DFI page 217, before the
choice `U = Q² = P⁻¹ (X + Y)⁻¹ X Y` is substituted. -/
noncomputable def dfiEquation30PreoptimizedError
    (a b : ℕ) (X Y Q ε : ℝ) : ℝ :=
  (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-1 + ε)) +
    (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ) + ε)

/-- The scale of the error in DFI Theorem 1.  The implicit constant in
the paper is represented separately from this expression. -/
noncomputable def dfiTheorem1ErrorScale
    (P X Y ε : ℝ) : ℝ :=
  P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
    (X * Y) ^ (1 / 4 + ε)

/-- The last small modulus in DFI's equation-(27) approximation range
`q < Q^(1-η)`.  Subtracting one from the ceiling makes the strict real
cutoff and the finite natural interval agree exactly. -/
noncomputable def dfiEquation27SourceSplitCutoff (Q η : ℝ) : ℕ :=
  ⌈Q ^ (1 - η)⌉₊ - 1

/-- The source split cutoff is nonempty, lies strictly below the complete
delta-modulus range, and has successor equal to the real cutoff's ceiling. -/
theorem dfiEquation27SourceSplitCutoff_spec {Q η : ℝ} (hQ : 2 ≤ Q)
    (hη0 : 0 < η) (hη1 : η < 1) :
    1 ≤ dfiEquation27SourceSplitCutoff Q η ∧
      dfiEquation27SourceSplitCutoff Q η < ⌈2 * Q⌉₊ ∧
      dfiEquation27SourceSplitCutoff Q η + 1 = ⌈Q ^ (1 - η)⌉₊ := by
  have hQ1 : 1 < Q := lt_of_lt_of_le (by norm_num) hQ
  have he : 0 < 1 - η := by linarith
  have hpow1 : 1 < Q ^ (1 - η) := Real.one_lt_rpow hQ1 he
  have hceil2 : 2 ≤ ⌈Q ^ (1 - η)⌉₊ := by
    have hltR : (1 : ℝ) < (⌈Q ^ (1 - η)⌉₊ : ℝ) :=
      hpow1.trans_le (Nat.le_ceil _)
    have hltN : 1 < ⌈Q ^ (1 - η)⌉₊ := by exact_mod_cast hltR
    omega
  have hsub : 1 ≤ ⌈Q ^ (1 - η)⌉₊ - 1 := by omega
  have hpowQ : Q ^ (1 - η) ≤ Q := by
    have h := Real.rpow_le_rpow_of_exponent_le hQ1.le
      (by linarith : 1 - η ≤ 1)
    simpa using h
  have hceilLe : ⌈Q ^ (1 - η)⌉₊ ≤ ⌈Q⌉₊ := Nat.ceil_mono hpowQ
  have hceilQLt : ⌈Q⌉₊ < ⌈2 * Q⌉₊ := by
    have hceilQ : (⌈Q⌉₊ : ℝ) < Q + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2ceil : 2 * Q ≤ (⌈2 * Q⌉₊ : ℝ) := Nat.le_ceil _
    have hGap : Q + 1 ≤ 2 * Q := by linarith
    exact_mod_cast hceilQ.trans_le (hGap.trans h2ceil)
  refine ⟨?_, ?_, ?_⟩
  · simpa [dfiEquation27SourceSplitCutoff] using hsub
  · unfold dfiEquation27SourceSplitCutoff
    omega
  · unfold dfiEquation27SourceSplitCutoff
    omega

/-- The integer split scale differs from `Q^(1-η)` by at most the harmless
factor two.  Both inequalities are used when positive and negative powers
of the cutoff are absorbed into the DFI epsilon loss. -/
theorem dfiEquation27SourceSplitCutoff_scale {Q η : ℝ} (hQ : 2 ≤ Q)
    (hη0 : 0 < η) (hη1 : η < 1) :
    Q ^ (1 - η) ≤
        ((dfiEquation27SourceSplitCutoff Q η + 1 : ℕ) : ℝ) ∧
      ((dfiEquation27SourceSplitCutoff Q η + 1 : ℕ) : ℝ) ≤
        2 * Q ^ (1 - η) := by
  have hspec := dfiEquation27SourceSplitCutoff_spec hQ hη0 hη1
  rw [hspec.2.2]
  constructor
  · exact Nat.le_ceil _
  · have hpow1 : 1 ≤ Q ^ (1 - η) :=
      (Real.one_lt_rpow (lt_of_lt_of_le (by norm_num) hQ) (by linarith)).le
    have hceil : (⌈Q ^ (1 - η)⌉₊ : ℝ) < Q ^ (1 - η) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
    linarith

/-- The reciprocal split scale has the exact negative power required by
the large-modulus equation-(30) contribution. -/
theorem dfiEquation27SourceSplitCutoff_inv_le {Q η : ℝ} (hQ : 2 ≤ Q)
    (hη0 : 0 < η) (hη1 : η < 1) :
    (1 / ((dfiEquation27SourceSplitCutoff Q η + 1 : ℕ) : ℝ)) ≤
      Q ^ (-(1 - η)) := by
  have hlower :=
    (dfiEquation27SourceSplitCutoff_scale hQ hη0 hη1).1
  have hpow : 0 < Q ^ (1 - η) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hcut : 0 <
      ((dfiEquation27SourceSplitCutoff Q η + 1 : ℕ) : ℝ) := by
    positivity
  rw [one_div, Real.rpow_neg (by linarith : 0 ≤ Q)]
  exact (inv_le_inv₀ hcut hpow).2 hlower

/-- A positive shift larger than the complete `x`-support cannot meet the
line `x-y=h`, since the dyadic source has `y ≥ Y ≥ 1`. -/
theorem dfiEquation2_eq_zero_on_large_positive_shift
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h) :
    ∀ x : ℝ, f x (x - h) = 0 := by
  intro x
  by_contra hne
  have hmem : (x, x - (h : ℝ)) ∈
      Function.support (Function.uncurry f) := hne
  have hs := hbox.support_subset hmem
  have hypos : 0 < x - (h : ℝ) := by linarith [hs.2.1]
  have hxupper : x ≤ 2 * X := hs.1.2
  exact (not_lt_of_ge hxupper) (hh.trans (by linarith))

/-- The source equation-(3) central integral vanishes identically beyond
the positive-shift support. -/
theorem dfiEquation27CentralIntegral_eq_zero_of_large_positive_shift
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral a b qx qy f h = 0 := by
  have hfzero :=
    dfiEquation2_eq_zero_on_large_positive_shift hbox h hY hh
  unfold dfiEquation27CentralIntegral
  simp_rw [dfiEquation27C, hfzero]
  simp

/-- Consequently the complete Ramanujan main series, not merely each finite
truncation, is zero outside the positive-shift support. -/
theorem dfiEquation27CentralSeries_eq_zero_of_large_positive_shift
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b : ℕ) :
    dfiEquation27CentralSeries a b h f = 0 := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand,
    dfiEquation27CentralIntegral_eq_zero_of_large_positive_shift
      hbox h hY hh a b]
  simp

/-- The finite shifted-divisor source sum has the same exact support cutoff
as its equation-(3) main term. -/
theorem dfiDyadicShiftedDivisorSum_eq_zero_of_large_positive_shift
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b M N : ℕ) :
    dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) = 0 := by
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = (h : ℤ)
  · rw [if_pos hs]
    have hreal : (a : ℝ) * m - (b : ℝ) * n = h := by
      unfold quadraticDivisorShift at hs
      exact_mod_cast hs
    have hfzero :=
      dfiEquation2_eq_zero_on_large_positive_shift hbox h hY hh
        ((a : ℝ) * m)
    have hy : (a : ℝ) * m - h = (b : ℝ) * n := by linarith
    rw [hy] at hfzero
    simp [hfzero]
  · simp [hs]

/-- The real source transition is below its natural-number ceiling. -/
theorem dfiEquation29SourceXTransition_le_cutoff
    (a : ℕ) (X Q ε : ℝ) :
    dfiEquation29SourceXTransition a X Q ε ≤
      (dfiEquation29SourceXCutoff a X Q ε : ℝ) := by
  unfold dfiEquation29SourceXCutoff
  exact Nat.le_ceil _

/-- Symmetric source transition/ceiling comparison. -/
theorem dfiEquation29SourceYTransition_le_cutoff
    (b : ℕ) (Y Q ε : ℝ) :
    dfiEquation29SourceYTransition b Y Q ε ≤
      (dfiEquation29SourceYCutoff b Y Q ε : ℝ) := by
  unfold dfiEquation29SourceYCutoff
  exact Nat.le_ceil _

/-- A negative real power of the exact integer cutoff is bounded by the
same power of DFI's source transition. -/
theorem dfiEquation29SourceXCutoff_neg_natCast_le_transition
    (a : ℕ) (ha : 0 < a) {X Q ε : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (k : ℕ) :
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (-(k : ℝ)) ≤
      dfiEquation29SourceXTransition a X Q ε ^ (-(k : ℝ)) := by
  exact Real.rpow_le_rpow_of_nonpos
    (by unfold dfiEquation29SourceXTransition; positivity)
    (dfiEquation29SourceXTransition_le_cutoff a X Q ε)
    (neg_nonpos.mpr (Nat.cast_nonneg k))

/-- Symmetric negative-power cutoff estimate. -/
theorem dfiEquation29SourceYCutoff_neg_natCast_le_transition
    (b : ℕ) (hb : 0 < b) {Y Q ε : ℝ} (hY : 0 < Y) (hQ : 0 < Q)
    (k : ℕ) :
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (-(k : ℝ)) ≤
      dfiEquation29SourceYTransition b Y Q ε ^ (-(k : ℝ)) := by
  exact Real.rpow_le_rpow_of_nonpos
    (by unfold dfiEquation29SourceYTransition; positivity)
    (dfiEquation29SourceYTransition_le_cutoff b Y Q ε)
    (neg_nonpos.mpr (Nat.cast_nonneg k))

/-- The quantitative cancellation behind DFI equation (29).  If the tail
starts beyond `A * Q^ε`, then the `k` recurrence factors `A^k` are
cancelled by the negative `k`-th power of the tail cutoff and leave the
source saving `Q^(-ε k)`.  This form deliberately retains the nonnegative
recurrence constant `R`; later applications choose `k` after the derivative
profiles have been fixed. -/
theorem dfiEquation29_recurrence_cutoff_cancellation
    {A Q L R ε s : ℝ} (hA : 0 < A) (hQ : 1 ≤ Q) (hL : 0 < L)
    (hTransition : A * Q ^ ε ≤ L) (hR : 0 ≤ R)
    (k : ℕ) :
    (R * A) ^ k * L ^ (s - k) ≤
      R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ s := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hQeps : 0 < Q ^ ε := Real.rpow_pos_of_pos hQ0 _
  have hAL : A / L ≤ Q ^ (-ε) := by
    rw [Real.rpow_neg hQ0.le]
    apply (div_le_iff₀ hL).2
    have h := (le_div_iff₀ hQeps).2 hTransition
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hAL0 : 0 ≤ A / L := div_nonneg hA.le hL.le
  have hPow : (A / L) ^ k ≤ (Q ^ (-ε)) ^ k := by
    exact pow_le_pow_left₀ hAL0 hAL k
  have hSplit : L ^ (s - k) = L ^ s * L ^ (-(k : ℝ)) := by
    rw [show s - (k : ℝ) = s + -(k : ℝ) by ring,
      Real.rpow_add hL]
  have hRatio : A ^ k * L ^ (-(k : ℝ)) = (A / L) ^ k := by
    rw [Real.rpow_neg hL.le, Real.rpow_natCast, div_pow,
      div_eq_mul_inv]
  have hQPow : (Q ^ (-ε)) ^ k = Q ^ (-ε * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
  calc
    (R * A) ^ k * L ^ (s - k) =
        R ^ k * L ^ s * (A ^ k * L ^ (-(k : ℝ))) := by
      rw [hSplit, mul_pow]
      ring
    _ = R ^ k * L ^ s * (A / L) ^ k := by rw [hRatio]
    _ ≤ R ^ k * L ^ s * (Q ^ (-ε)) ^ k :=
      mul_le_mul_of_nonneg_left hPow
        (mul_nonneg (pow_nonneg hR k) (Real.rpow_nonneg hL.le s))
    _ = R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ s := by
      rw [hQPow]
      ring

/-- Equation (28)'s mixed negative-line majorant with the physical source
factor and the dyadic logarithmic width exposed exactly. -/
theorem dfiEquation28NonposMixedMajorant_neg_half_sub_nat
    (C : ℕ → ℝ) (p k : ℕ) (Q S R : ℝ)
    (a b q qMain c d : ℕ) (hS : 0 < S) (hc : 0 < c) :
    dfiEquation28NonposMixedMajorant C p (-(1 / 2 : ℝ) - k)
        Q S R a b q qMain c d =
      let Csum := ∑ i ∈ Finset.range (p + 1), C i
      let qQ := (q : ℝ) * Q
      let ratio := ((a : ℝ) * b) / qQ
      dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
        ((1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p * Real.log 2 *
          (S / c) ^ (-(1 / 2 : ℝ) - k) *
          (1 + (1 / 2 + (k : ℝ) + (p : ℝ) +
            (2 * S / c) * ratio) ^ p) *
          (Csum * qQ⁻¹)) := by
  dsimp only
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hSc : 0 < S / (c : ℝ) := div_pos hS hcR
  have hTwo : 2 * S / (c : ℝ) = 2 * (S / c) := by ring
  have hLog : (-Real.log (S / (c : ℝ))) -
      (-Real.log (2 * S / c)) = Real.log 2 := by
    rw [hTwo, Real.log_mul (by norm_num) hSc.ne']
    ring
  simp only [dfiEquation28NonposMixedMajorant,
    dfiMellinNonposProfileMajorant, abs_neg_half_sub_natCast, hLog]
  ring

/-- Uncoarsened companion of equation (28): on the `x` or `y` Mellin
line the derivative ratio is the corresponding coefficient `c/(qQ)`. -/
theorem dfiEquation28SeparatedNonposMixedMajorant_neg_half_sub_nat
    (C : ℕ → ℝ) (p k : ℕ) (Q S R : ℝ)
    (q qMain c d : ℕ) (hS : 0 < S) (hc : 0 < c) :
    dfiEquation28SeparatedNonposMixedMajorant C p (-(1 / 2 : ℝ) - k)
        Q S R q qMain c d =
      let Csum := ∑ i ∈ Finset.range (p + 1), C i
      let qQ := (q : ℝ) * Q
      let ratio := (c : ℝ) / qQ
      dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
        ((1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p * Real.log 2 *
          (S / c) ^ (-(1 / 2 : ℝ) - k) *
          (1 + (1 / 2 + (k : ℝ) + (p : ℝ) +
            (2 * S / c) * ratio) ^ p) *
          (Csum * qQ⁻¹)) := by
  dsimp only
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hSc : 0 < S / (c : ℝ) := div_pos hS hcR
  have hTwo : 2 * S / (c : ℝ) = 2 * (S / c) := by ring
  have hLog : (-Real.log (S / (c : ℝ))) -
      (-Real.log (2 * S / c)) = Real.log 2 := by
    rw [hTwo, Real.log_mul (by norm_num) hSc.ne']
    ring
  simp only [dfiEquation28SeparatedNonposMixedMajorant,
    dfiMellinNonposProfileMajorant, abs_neg_half_sub_natCast, hLog]
  ring

/-- The uncoarsened two-variable equation-(28) majorant on DFI's common
left line.  The two derivative scales remain `a/(qQ)` and `b/(qQ)`, which
is the form that cancels the two literal equation-(29) cutoffs. -/
theorem dfiEquation28BiSeparatedNonposShiftMajorant_neg_half_sub_nat
    (K : ℕ → ℕ → ℝ) (p k : ℕ) (Q X Y : ℝ) (a b q : ℕ) :
    dfiEquation28BiSeparatedNonposShiftMajorant K p (-(1 / 2 : ℝ) - k)
        Q X Y a b q =
      let Csum := ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (p + 1), K i j
      let qQ := (q : ℝ) * Q
      let M := Csum * qQ⁻¹
      let Rx := (a : ℝ) / qQ
      let Ry := (b : ℝ) / qQ
      (1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p *
        ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
        (Y / b) ^ (-(1 / 2 : ℝ) - k) *
        (1 + (1 / 2 + (k : ℝ) + (p : ℝ) + (2 * Y / b) * Ry) ^ p) *
      ((1 + 2 * Real.pi) ^ p * (2 : ℝ) ^ p *
        ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
        (X / a) ^ (-(1 / 2 : ℝ) - k) *
        (1 + (1 / 2 + (k : ℝ) + (p : ℝ) + (2 * X / a) * Rx) ^ p) * M) := by
  simp only [dfiEquation28BiSeparatedNonposShiftMajorant,
    dfiMellinNonposProfileMajorant, abs_neg_half_sub_natCast]
  ring

/-- Under DFI's optimized choice of `Q`, its square is no larger than
either physical dyadic length. -/
theorem dfiEquation30_optimized_Q_sq_le_lengths
    {P X Y Q : ℝ} (hP : 1 ≤ P) (hX : 0 < X) (hY : 0 < Y)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    Q ^ 2 ≤ X ∧ Q ^ 2 ≤ Y := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hSum : 0 < X + Y := add_pos hX hY
  have hPinv : P⁻¹ ≤ 1 := (inv_le_one₀ hP0).2 hP
  have hRatioX : (X + Y)⁻¹ * (X * Y) ≤ X := by
    rw [inv_mul_eq_div]
    rw [div_le_iff₀ hSum]
    nlinarith
  have hRatioY : (X + Y)⁻¹ * (X * Y) ≤ Y := by
    rw [inv_mul_eq_div]
    rw [div_le_iff₀ hSum]
    nlinarith
  rw [hQsq]
  constructor
  · simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hPinv
      (by positivity : 0 ≤ (X + Y)⁻¹ * (X * Y))).trans
        (by simpa only [one_mul] using hRatioX)
  · simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hPinv
      (by positivity : 0 ≤ (X + Y)⁻¹ * (X * Y))).trans
        (by simpa only [one_mul] using hRatioY)

/-- In the optimized regime the first transition in DFI equation (29) is
at least one.  Consequently, enlarging the strict source window through a
natural-number ceiling costs only an absolute factor. -/
theorem dfiEquation29SourceXTransition_one_le_optimized
    {a : ℕ} {P X Y Q ε : ℝ} (ha : 0 < a) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    1 ≤ dfiEquation29SourceXTransition a X Q ε := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hQsqPos : 0 < Q ^ 2 := sq_pos_of_pos hQ0
  have hQsqLeX :=
    (dfiEquation30_optimized_Q_sq_le_lengths hP hX hY hQsq).1
  have hXdiv : 1 ≤ X * (Q ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hQsqPos]
    simpa only [one_mul] using hQsqLeX
  have hQeps : 1 ≤ Q ^ ε := Real.one_le_rpow hQ hε
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  unfold dfiEquation29SourceXTransition
  rw [show -2 + ε = -(2 : ℝ) + ε by ring,
    Real.rpow_add hQ0, Real.rpow_neg hQ0.le,
    show Q ^ (2 : ℝ) = Q ^ 2 by norm_num]
  nlinarith [mul_nonneg (sub_nonneg.mpr haR)
    (mul_nonneg (show 0 ≤ X * (Q ^ 2)⁻¹ by positivity)
      (show 0 ≤ Q ^ ε by positivity))]

/-- Symmetric optimized lower bound for the second DFI transition. -/
theorem dfiEquation29SourceYTransition_one_le_optimized
    {b : ℕ} {P X Y Q ε : ℝ} (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    1 ≤ dfiEquation29SourceYTransition b Y Q ε := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hQsqPos : 0 < Q ^ 2 := sq_pos_of_pos hQ0
  have hQsqLeY :=
    (dfiEquation30_optimized_Q_sq_le_lengths hP hX hY hQsq).2
  have hYdiv : 1 ≤ Y * (Q ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hQsqPos]
    simpa only [one_mul] using hQsqLeY
  have hQeps : 1 ≤ Q ^ ε := Real.one_le_rpow hQ hε
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold dfiEquation29SourceYTransition
  rw [show -2 + ε = -(2 : ℝ) + ε by ring,
    Real.rpow_add hQ0, Real.rpow_neg hQ0.le,
    show Q ^ (2 : ℝ) = Q ^ 2 by norm_num]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbR)
    (mul_nonneg (show 0 ≤ Y * (Q ^ 2)⁻¹ by positivity)
      (show 0 ≤ Q ^ ε by positivity))]

/-- The ceiling-enlarged first retained window is at most twice the
literal source transition in the optimized regime. -/
theorem dfiEquation29SourceXCutoff_le_two_mul_transition_optimized
    {a : ℕ} {P X Y Q ε : ℝ} (ha : 0 < a) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ≤
      2 * dfiEquation29SourceXTransition a X Q ε := by
  have hTransition := dfiEquation29SourceXTransition_one_le_optimized
    ha hP hX hY hQ hε hQsq
  calc
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ≤
        dfiEquation29SourceXTransition a X Q ε + 1 :=
      (dfiEquation29SourceXCutoff_lt_transition_add_one a hX
        (zero_lt_one.trans_le hQ)).le
    _ ≤ 2 * dfiEquation29SourceXTransition a X Q ε := by linarith

/-- Symmetric ceiling estimate for the second retained window. -/
theorem dfiEquation29SourceYCutoff_le_two_mul_transition_optimized
    {b : ℕ} {P X Y Q ε : ℝ} (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ≤
      2 * dfiEquation29SourceYTransition b Y Q ε := by
  have hTransition := dfiEquation29SourceYTransition_one_le_optimized
    hb hP hX hY hQ hε hQsq
  calc
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ≤
        dfiEquation29SourceYTransition b Y Q ε + 1 :=
      (dfiEquation29SourceYCutoff_lt_transition_add_one b hY
        (zero_lt_one.trans_le hQ)).le
    _ ≤ 2 * dfiEquation29SourceYTransition b Y Q ε := by linarith

/-- Source-specialized recurrence cancellation for the first one-sided
equation-(29) tail.  The final cutoff is replaced by twice the literal DFI
transition, leaving the additional `Q^(-ε k)` saving. -/
theorem dfiEquation29_xSingle_tail_recurrence_factor_le
    {a : ℕ} {P X Y Q ε : ℝ} (ha : 0 < a) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (k : ℕ) :
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((a : ℝ) * X) / Q ^ 2)) ^ k) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
          (ε + 3 / 4 - k) ≤
      ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ)) *
        (2 * dfiEquation29SourceXTransition a X Q ε) ^
          (ε + 3 / 4) := by
  let A : ℝ := ((a : ℝ) * X) / Q ^ 2
  let R : ℝ := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2
  let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let Z : ℝ := dfiEquation29SourceXTransition a X Q ε
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceXCutoff_pos ha hX hQ0 ε
  have hAZ : A * Q ^ ε = Z := by
    dsimp only [A, Z]
    unfold dfiEquation29SourceXTransition
    rw [show -2 + ε = -(2 : ℝ) + ε by ring,
      Real.rpow_add hQ0, Real.rpow_neg hQ0.le]
    rw [div_eq_mul_inv, mul_assoc]
    rw [← Real.rpow_natCast]
    rfl
  have hZL : A * Q ^ ε ≤ L := by
    rw [hAZ]
    exact dfiEquation29SourceXTransition_le_cutoff a X Q ε
  have hCore := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hL hZL hR k (s := ε + 3 / 4)
  have hCut : L ≤ 2 * Z := by
    simpa only [L, Z] using
      dfiEquation29SourceXCutoff_le_two_mul_transition_optimized
        ha hP hX hY hQ hε hQsq
  have hPow : L ^ (ε + 3 / 4) ≤ (2 * Z) ^ (ε + 3 / 4) :=
    Real.rpow_le_rpow hL.le hCut (by linarith)
  calc
    _ ≤ R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ (ε + 3 / 4) := by
      simpa only [A, R, L] using hCore
    _ ≤ R ^ k * Q ^ (-ε * (k : ℝ)) *
        (2 * Z) ^ (ε + 3 / 4) := by gcongr
    _ = _ := by rfl

/-- Symmetric recurrence cancellation for the second one-sided tail. -/
theorem dfiEquation29_ySingle_tail_recurrence_factor_le
    {b : ℕ} {P X Y Q ε : ℝ} (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (k : ℕ) :
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((b : ℝ) * Y) / Q ^ 2)) ^ k) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
          (ε + 3 / 4 - k) ≤
      ((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ)) *
        (2 * dfiEquation29SourceYTransition b Y Q ε) ^
          (ε + 3 / 4) := by
  let A : ℝ := ((b : ℝ) * Y) / Q ^ 2
  let R : ℝ := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2
  let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
  let Z : ℝ := dfiEquation29SourceYTransition b Y Q ε
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceYCutoff_pos hb hY hQ0 ε
  have hAZ : A * Q ^ ε = Z := by
    dsimp only [A, Z]
    unfold dfiEquation29SourceYTransition
    rw [show -2 + ε = -(2 : ℝ) + ε by ring,
      Real.rpow_add hQ0, Real.rpow_neg hQ0.le]
    rw [div_eq_mul_inv, mul_assoc]
    rw [← Real.rpow_natCast]
    rfl
  have hZL : A * Q ^ ε ≤ L := by
    rw [hAZ]
    exact dfiEquation29SourceYTransition_le_cutoff b Y Q ε
  have hCore := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hL hZL hR k (s := ε + 3 / 4)
  have hCut : L ≤ 2 * Z := by
    simpa only [L, Z] using
      dfiEquation29SourceYCutoff_le_two_mul_transition_optimized
        hb hP hX hY hQ hε hQsq
  have hPow : L ^ (ε + 3 / 4) ≤ (2 * Z) ^ (ε + 3 / 4) :=
    Real.rpow_le_rpow hL.le hCut (by linarith)
  calc
    _ ≤ R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ (ε + 3 / 4) := by
      simpa only [A, R, L] using hCore
    _ ≤ R ^ k * Q ^ (-ε * (k : ℝ)) *
        (2 * Z) ^ (ε + 3 / 4) := by gcongr
    _ = _ := by rfl

/-- Exact algebraic normalization of the first one-sided equation-(29)
tail.  This exposes the same source factor as the retained branch, with
the recurrence and tail power isolated in the final parenthesis. -/
theorem dfiEquation29_xSingle_tail_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ} {C D Q X Y ε : ℝ} :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
    W * dfiEquation29XSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) =
      (C * D * (14 * Real.pi + 8) *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          ((X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k))) := by
  dsimp only
  have hqx0 : (0 : ℝ) ≤ qx := Nat.cast_nonneg qx
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qx : ℝ) =
      (14 * Real.pi + 8) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hqx0]
  unfold dfiEquation29XSingleMainTailCoefficient
  rw [hsqrt]
  ring

/-- Exact algebraic normalization of the source-sharp first one-sided
equation-(29) tail.  The physical source mass is now the literal
`(ab)⁻¹ min(X,Y) log Q`, with no support-length surrogate. -/
theorem dfiEquation29_xSingle_tail_l1_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ} {C D Q X Y ε : ℝ} :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
    W * dfiEquation29XSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) =
      (C * D * (14 * Real.pi + 8) *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k))) := by
  dsimp only
  have hqx0 : (0 : ℝ) ≤ qx := Nat.cast_nonneg qx
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qx : ℝ) =
      (14 * Real.pi + 8) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hqx0]
  unfold dfiEquation29XSingleMainTailL1Coefficient
  rw [hsqrt]
  ring

/-- The raw physical factor in the preceding identity is exactly DFI's
`(ab)⁻¹ XY/(qQ)` normalization. -/
theorem dfiEquation29_xSingle_physical_factor_identity
    {a b q : ℕ} {Q X Y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹) =
      ((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

/-- Symmetric exact normalization of the second one-sided equation-(29)
tail. -/
theorem dfiEquation29_ySingle_tail_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ} {C D Q X Y ε : ℝ} :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * dfiEquation29YSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) =
      (C * D * (14 * Real.pi + 8) *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          ((Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k))) := by
  dsimp only
  have hqy0 : (0 : ℝ) ≤ qy := Nat.cast_nonneg qy
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qy : ℝ) =
      (14 * Real.pi + 8) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hqy0]
  unfold dfiEquation29YSingleMainTailCoefficient
  rw [hsqrt]
  ring

/-- Symmetric exact normalization of the source-sharp second one-sided
equation-(29) tail. -/
theorem dfiEquation29_ySingle_tail_l1_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ} {C D Q X Y ε : ℝ} :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * dfiEquation29YSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) =
      (C * D * (14 * Real.pi + 8) *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k))) := by
  dsimp only
  have hqy0 : (0 : ℝ) ≤ qy := Nat.cast_nonneg qy
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qy : ℝ) =
      (14 * Real.pi + 8) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv,
      ← Real.rpow_neg hqy0]
  unfold dfiEquation29YSingleMainTailL1Coefficient
  rw [hsqrt]
  ring

/-- Symmetric physical normalization for the second one-sided branch. -/
theorem dfiEquation29_ySingle_physical_factor_identity
    {a b q : ℕ} {Q X Y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹) =
      ((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

/-- Exact algebra behind the retained first-variable contribution in DFI
equations (25), (29), and (30).  The factor `a` generated by the transition
is kept beside `(ab)⁻¹`, where the reduced-modulus Weil estimate cancels it. -/
theorem dfiEquation29_xSingle_source_factor_identity
    {a b q : ℕ} [NeZero q] {X Q η R : ℝ}
    (ha : 0 < a) (hX : 0 < X) (hQ : 0 < Q) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceXTransition a X Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (a : ℝ) * (((a : ℝ) * b)⁻¹)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  change W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceXTransition a X Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (a : ℝ) * (((a : ℝ) * b)⁻¹))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hSource :
      dfiEquation29SourceXTransition a X Q η ^ (3 / 4 + η) =
        (a : ℝ) ^ (3 / 4 + η) * X ^ (3 / 4 + η) *
          Q ^ ((-2 + η) * (3 / 4 + η)) :=
    dfiEquation29SourceXTransition_rpow a hX hQ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by unfold dfiEquation29SourceXTransition; positivity :
        0 ≤ dfiEquation29SourceXTransition a X Q η),
    hSource]
  have hXa :
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) =
        X ^ (-(1 / 4 : ℝ)) * (a : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hX.le haR.le, Real.rpow_neg haR.le]
    field_simp
  rw [hXa]
  have hXpow : X ^ (-(1 / 4 : ℝ)) * X ^ (3 / 4 + η) =
      X ^ (1 / 2 + η) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hapow : (a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ (3 / 4 + η) =
      (a : ℝ) * (a : ℝ) ^ η := by
    calc
      _ = (a : ℝ) ^ ((1 / 4 : ℝ) + (3 / 4 + η)) :=
        (Real.rpow_add haR _ _).symm
      _ = (a : ℝ) ^ (1 + η) := by
        congr 1
        ring
      _ = (a : ℝ) ^ (1 : ℝ) * (a : ℝ) ^ η :=
        Real.rpow_add haR 1 η
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = 2 ^ (3 / 4 + η) *
        (X ^ (-(1 / 4 : ℝ)) * X ^ (3 / 4 + η)) *
        ((a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ (3 / 4 + η)) *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (((a : ℝ) * b)⁻¹)) := by ring
    _ = _ := by
      rw [hXpow, hapow]
      ring

private theorem dfiEquation29_weil_mul_xSingle_source_scale_sharp_early
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ *
        (a : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hgb : (Nat.gcd b q : ℝ) ≤ b := by
    exact_mod_cast Nat.gcd_le_left q hb
  have hratio : (Nat.gcd b q : ℝ) / b ≤ 1 :=
    (div_le_one hbR).2 hgb
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  calc
    _ = ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q)) *
        ((Nat.gcd b q : ℝ) / b) * (q.divisors.card : ℝ) := by
      field_simp
      rw [Real.sq_sqrt hq.le]
      ring
    _ ≤ ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q)) *
        1 * (q.divisors.card : ℝ) := by
      gcongr
    _ = _ := by ring

private theorem dfiEquation29_weil_mul_ySingle_source_scale_sharp_early
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ)⁻¹ *
        (b : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  simpa only [mul_comm (a : ℝ) b] using
    dfiEquation29_weil_mul_xSingle_source_scale_sharp_early q b a hb ha h

/-- Sharp retained first-variable source factor after the Weil
normalization.  This is the inequality form consumed by the modulus sum. -/
theorem dfiEquation29_xSingle_source_factor_le
    {a b q : ℕ} [NeZero q] {P X Y Q η R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ (3 / 4 + η) ≤
      2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) * (a : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let A : ℝ := W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
    (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R)
  have hα : 0 ≤ (3 / 4 : ℝ) + η := by linarith
  have hCut := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceXCutoff_le_two_mul_transition_optimized
      ha hP hX hY hQ hη hQsq) hα
  have hA : 0 ≤ A := by dsimp [A, W, qx, qy]; positivity
  have hWindow :
      A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ (3 / 4 + η) ≤
        A * (2 * dfiEquation29SourceXTransition a X Q η) ^
          (3 / 4 + η) := mul_le_mul_of_nonneg_left hCut hA
  have hIdentity := dfiEquation29_xSingle_source_factor_identity
    (q := q) (b := b) (η := η) (R := R) ha hX
      (zero_lt_one.trans_le hQ) h
  have hWeil : W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (a : ℝ) * (((a : ℝ) * b)⁻¹) ≤
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
    dsimp [W, qx, qy]
    exact dfiEquation29_weil_mul_xSingle_source_scale_sharp_early q a b ha hb h
  let K : ℝ := 2 ^ (3 / 4 + η) * X ^ (1 / 2 + η) *
    (a : ℝ) ^ η * Q ^ ((-2 + η) * (3 / 4 + η)) * R
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^
      (3 / 4 + η) ≤ _
  calc
    _ ≤ A * (2 * dfiEquation29SourceXTransition a X Q η) ^
        (3 / 4 + η) := hWindow
    _ = K * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (a : ℝ) * (((a : ℝ) * b)⁻¹)) := by
      simpa only [A, K, W, qx, qy] using hIdentity
    _ ≤ K * ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) /
        Real.sqrt q) * (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        hWeil hK
    _ = _ := by rfl

/-- The exact source scaling identity for the retained `y`-dual branch. -/
theorem dfiEquation29_ySingle_source_factor_identity
    {a b q : ℕ} [NeZero q] {Y Q η R : ℝ}
    (hb : 0 < b) (hY : 0 < Y) (hQ : 0 < Q) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceYTransition b Y Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (b : ℝ) * (((a : ℝ) * b)⁻¹)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  change W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceYTransition b Y Q η) ^ (3 / 4 + η) =
      2 ^ (3 / 4 + η) * Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (b : ℝ) * (((a : ℝ) * b)⁻¹))
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hSource :
      dfiEquation29SourceYTransition b Y Q η ^ (3 / 4 + η) =
        (b : ℝ) ^ (3 / 4 + η) * Y ^ (3 / 4 + η) *
          Q ^ ((-2 + η) * (3 / 4 + η)) :=
    dfiEquation29SourceYTransition_rpow b hY hQ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by unfold dfiEquation29SourceYTransition; positivity :
        0 ≤ dfiEquation29SourceYTransition b Y Q η),
    hSource]
  have hYb :
      (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) =
        Y ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hY.le hbR.le, Real.rpow_neg hbR.le]
    field_simp
  rw [hYb]
  have hYpow : Y ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 + η) =
      Y ^ (1 / 2 + η) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  have hbpow : (b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ (3 / 4 + η) =
      (b : ℝ) * (b : ℝ) ^ η := by
    calc
      _ = (b : ℝ) ^ ((1 / 4 : ℝ) + (3 / 4 + η)) :=
        (Real.rpow_add hbR _ _).symm
      _ = (b : ℝ) ^ (1 + η) := by
        congr 1
        ring
      _ = (b : ℝ) ^ (1 : ℝ) * (b : ℝ) ^ η :=
        Real.rpow_add hbR 1 η
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = 2 ^ (3 / 4 + η) *
        (Y ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 + η)) *
        ((b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ (3 / 4 + η)) *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (((a : ℝ) * b)⁻¹)) := by ring
    _ = _ := by
      rw [hYpow, hbpow]
      ring

/-- Sharp retained second-variable source factor after Weil normalization. -/
theorem dfiEquation29_ySingle_source_factor_le
    {a b q : ℕ} [NeZero q] {P X Y Q η R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ (3 / 4 + η) ≤
      2 ^ (3 / 4 + η) * Y ^ (1 / 2 + η) * (b : ℝ) ^ η *
        Q ^ ((-2 + η) * (3 / 4 + η)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let A : ℝ := W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R)
  have hα : 0 ≤ (3 / 4 : ℝ) + η := by linarith
  have hCut := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceYCutoff_le_two_mul_transition_optimized
      hb hP hX hY hQ hη hQsq) hα
  have hA : 0 ≤ A := by dsimp [A, W, qx, qy]; positivity
  have hWindow :
      A * (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ (3 / 4 + η) ≤
        A * (2 * dfiEquation29SourceYTransition b Y Q η) ^
          (3 / 4 + η) := mul_le_mul_of_nonneg_left hCut hA
  have hIdentity := dfiEquation29_ySingle_source_factor_identity
    (q := q) (a := a) (η := η) (R := R) hb hY
      (zero_lt_one.trans_le hQ) h
  have hWeil : W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
      (b : ℝ) * (((a : ℝ) * b)⁻¹) ≤
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
    dsimp [W, qx, qy]
    exact dfiEquation29_weil_mul_ySingle_source_scale_sharp_early q a b ha hb h
  let K : ℝ := 2 ^ (3 / 4 + η) * Y ^ (1 / 2 + η) *
    (b : ℝ) ^ η * Q ^ ((-2 + η) * (3 / 4 + η)) * R
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change A * (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^
      (3 / 4 + η) ≤ _
  calc
    _ ≤ A * (2 * dfiEquation29SourceYTransition b Y Q η) ^
        (3 / 4 + η) := hWindow
    _ = K * (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (b : ℝ) * (((a : ℝ) * b)⁻¹)) := by
      simpa only [A, K, W, qx, qy] using hIdentity
    _ ≤ K * ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) /
        Real.sqrt q) * (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        hWeil hK
    _ = _ := by rfl

/-- The first one-sided tail has the retained source normalization, times
the explicit recurrence saving.  This is the quantitative heart of DFI
equation (29), before the harmless logarithmic/profile constants are
restored. -/
theorem dfiEquation29_xSingle_tail_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        ((X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹)) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((a : ℝ) * X) / Q ^ 2)) ^ k *
          L ^ (ε + 3 / 4 - k)) ≤
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
          (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
          (X * Y / ((q : ℝ) * Q)) *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let A : ℝ := ((a : ℝ) * X) / Q ^ 2
  let R : ℝ := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2
  let S : ℝ := X * Y / ((q : ℝ) * Q)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceXCutoff_pos ha hX hQ0 ε
  have hTransition : A * Q ^ ε ≤ L := by
    have hAZ : A * Q ^ ε = dfiEquation29SourceXTransition a X Q ε := by
      dsimp only [A]
      unfold dfiEquation29SourceXTransition
      rw [show -2 + ε = -(2 : ℝ) + ε by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le]
      rw [div_eq_mul_inv, mul_assoc, ← Real.rpow_natCast]
      rfl
    rw [hAZ]
    exact dfiEquation29SourceXTransition_le_cutoff a X Q ε
  have hRec := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hL hTransition hR k (s := ε + 3 / 4)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hPrefix : 0 ≤ W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S) := by
    dsimp [W, qx, qy]
    positivity
  have hSource := dfiEquation29_xSingle_source_factor_le
    (q := q) ha hb hP hX hY hQ hε hS hQsq h
  dsimp only at hSource
  rw [dfiEquation29_xSingle_physical_factor_identity ha hb]
  change (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S)) *
        ((R * A) ^ k * L ^ (ε + 3 / 4 - k)) ≤ _
  calc
    _ ≤ (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S)) *
          (R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ (ε + 3 / 4)) :=
      mul_le_mul_of_nonneg_left hRec hPrefix
    _ = (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S) *
          L ^ (3 / 4 + ε)) := by ring
    _ ≤ (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
          (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * S *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
      gcongr
    _ = _ := by rfl

/-- Source-sharp first one-sided tail core.  The recurrence cancellation is
identical to DFI equation (29), but the physical mass is an arbitrary
nonnegative source factor `M`; the application takes
`M = min X Y * log Q`. -/
theorem dfiEquation29_xSingle_tail_l1_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hM : 0 ≤ M)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((a : ℝ) * X) / Q ^ 2)) ^ k *
          L ^ (ε + 3 / 4 - k)) ≤
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
          (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let A : ℝ := ((a : ℝ) * X) / Q ^ 2
  let R : ℝ := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceXCutoff_pos ha hX hQ0 ε
  have hTransition : A * Q ^ ε ≤ L := by
    have hAZ : A * Q ^ ε = dfiEquation29SourceXTransition a X Q ε := by
      dsimp only [A]
      unfold dfiEquation29SourceXTransition
      rw [show -2 + ε = -(2 : ℝ) + ε by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le]
      rw [div_eq_mul_inv, mul_assoc, ← Real.rpow_natCast]
      rfl
    rw [hAZ]
    exact dfiEquation29SourceXTransition_le_cutoff a X Q ε
  have hRec := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hL hTransition hR k (s := ε + 3 / 4)
  have hPrefix : 0 ≤ W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * M) := by
    dsimp [W, qx, qy]
    positivity
  have hSource := dfiEquation29_xSingle_source_factor_le
    (q := q) ha hb hP hX hY hQ hε hM hQsq h
  dsimp only at hSource
  change (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * M)) *
        ((R * A) ^ k * L ^ (ε + 3 / 4 - k)) ≤ _
  calc
    _ ≤ (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * M)) *
          (R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ (ε + 3 / 4)) :=
      mul_le_mul_of_nonneg_left hRec hPrefix
    _ = (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * M) *
          L ^ (3 / 4 + ε)) := by ring
    _ ≤ (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
          (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
      gcongr
    _ = _ := by rfl

/-- Symmetric one-sided tail core for DFI equation (29). -/
theorem dfiEquation29_ySingle_tail_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) *
        ((Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹)) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((b : ℝ) * Y) / Q ^ 2)) ^ k *
          L ^ (ε + 3 / 4 - k)) ≤
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
          (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
          (X * Y / ((q : ℝ) * Q)) *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
  let A : ℝ := ((b : ℝ) * Y) / Q ^ 2
  let R : ℝ := ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2
  let S : ℝ := X * Y / ((q : ℝ) * Q)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceYCutoff_pos hb hY hQ0 ε
  have hTransition : A * Q ^ ε ≤ L := by
    have hAZ : A * Q ^ ε = dfiEquation29SourceYTransition b Y Q ε := by
      dsimp only [A]
      unfold dfiEquation29SourceYTransition
      rw [show -2 + ε = -(2 : ℝ) + ε by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le]
      rw [div_eq_mul_inv, mul_assoc, ← Real.rpow_natCast]
      rfl
    rw [hAZ]
    exact dfiEquation29SourceYTransition_le_cutoff b Y Q ε
  have hRec := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hL hTransition hR k (s := ε + 3 / 4)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hPrefix : 0 ≤ W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
      (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S) := by
    dsimp [W, qx, qy]
    positivity
  have hSource := dfiEquation29_ySingle_source_factor_le
    (q := q) ha hb hP hX hY hQ hε hS hQsq h
  dsimp only at hSource
  rw [dfiEquation29_ySingle_physical_factor_identity ha hb]
  change (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
      (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S)) *
        ((R * A) ^ k * L ^ (ε + 3 / 4 - k)) ≤ _
  calc
    _ ≤ (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S)) *
          (R ^ k * Q ^ (-ε * (k : ℝ)) * L ^ (ε + 3 / 4)) :=
      mul_le_mul_of_nonneg_left hRec hPrefix
    _ = (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * S) *
          L ^ (3 / 4 + ε)) := by ring
    _ ≤ (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
          (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * S *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
      gcongr
    _ = _ := by rfl

/-- Symmetric source-sharp one-sided tail core. -/
theorem dfiEquation29_ySingle_tail_l1_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hM : 0 ≤ M)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
            (((b : ℝ) * Y) / Q ^ 2)) ^ k *
          L ^ (ε + 3 / 4 - k)) ≤
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
        Q ^ (-ε * (k : ℝ))) *
        (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
          (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
            (q.divisors.card : ℝ))) := by
  simpa only [mul_comm (a : ℝ) b, min_comm X Y] using
    dfiEquation29_xSingle_tail_l1_source_core_le
      (a := b) (b := a) (q := q) (k := k)
      (P := P) (X := Y) (Y := X) (Q := Q) (ε := ε) (M := M)
      hb ha hP hY hX hQ hε hM
      (by simpa [add_comm, mul_comm] using hQsq) h

/-- Source-sharp pointwise form of the complete two-sign first one-sided
tail in DFI equation (29). -/
theorem exists_dfiEquation29_xSingleTail_l1_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ) (q : ℕ)
        (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29XSingleLogMajorant Q Y b /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ))) := by
  obtain ⟨C, D, hC, hD, hRaw⟩ :=
    exists_dfiEquation29_xSingleTailWeilTotal_source_l1_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h q hq hqQ
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * D * (14 * Real.pi + 8) /
    ((k : ℝ) - ε - 3 / 4)
  let G : ℝ := |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  let M : ℝ := min X Y * Real.log Q
  have hqPos : 0 < q := NeZero.pos q
  have hlogq : |Real.log (qy : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le b q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hG : G ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    dsimp [G, dfiEquation29XSingleLogMajorant]
    linarith
  have hMaj : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmin : 0 ≤ min X Y :=
      le_min (zero_lt_one.trans_le hf.one_le_X).le
        (zero_lt_one.trans_le hf.one_le_Y).le
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hCore := dfiEquation29_xSingle_tail_l1_source_core_le
    (q := q) (k := k) (M := M) ha hb hP
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε.le hM hQsq h
  dsimp only at hCore
  have hProfile := hRaw a b q ha hb hq hqQ h
  dsimp only at hProfile
  have hFactor := dfiEquation29_xSingle_tail_l1_source_factorization
    (a := a) (b := b) (q := q) (qx := qx) (qy := qy) (k := k)
    (h := h) (C := C) (D := D) (Q := Q) (X := X) (Y := Y) (ε := ε)
  dsimp only at hFactor
  have hLpos : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceXCutoff_pos ha
      (zero_lt_one.trans_le hf.one_le_X) (by linarith : 0 < Q) ε
  have hRawCore : 0 ≤ W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) *
      (((a : ℝ) * b)⁻¹ * M) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((a : ℝ) * X) / Q ^ 2)) ^ k *
        L ^ (ε + 3 / 4 - k)) := by
    have hW0 : 0 ≤ W := by dsimp [W]; positivity
    have hqx0 : 0 ≤ (qx : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg qx) _
    have hqy0 : 0 ≤ (qy : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg qy)
    have hXa0 : 0 ≤ (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (zero_lt_one.trans_le hf.one_le_X).le
          (Nat.cast_nonneg a)) _
    have hab0 : 0 ≤ (((a : ℝ) * b)⁻¹) := by positivity
    have hR0 : 0 ≤ ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg Real.pi)
    have hscale0 : 0 ≤ ((a : ℝ) * X) / Q ^ 2 :=
      div_nonneg
        (mul_nonneg (Nat.cast_nonneg a)
          (zero_lt_one.trans_le hf.one_le_X).le) (sq_nonneg Q)
    have hrec0 : 0 ≤ (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((a : ℝ) * X) / Q ^ 2)) ^ k) :=
      pow_nonneg (mul_nonneg hR0 hscale0) k
    have hL0 : 0 ≤ L ^ (ε + 3 / 4 - k) :=
      Real.rpow_nonneg hLpos.le _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hW0 hqx0) hqy0) hXa0)
          (mul_nonneg hab0 hM))
      (mul_nonneg hrec0 hL0)
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        dfiEquation29XSingleMainTailL1Coefficient
            C D k Q X Y a b qx qy *
          (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      simpa only [W, qx, qy, L] using hProfile
    _ = 2 * (W * dfiEquation29XSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ = 2 * ((B * G) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * M) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      rw [hFactor]
      dsimp [B, G, M]
      ring
    _ ≤ 2 * ((B * dfiEquation29XSingleLogMajorant Q Y b) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * M) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      gcongr
    _ ≤ 2 * ((B * dfiEquation29XSingleLogMajorant Q Y b) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
          Q ^ (-ε * (k : ℝ)) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * M *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ))))) := by
      gcongr
    _ = _ := by dsimp [B, M]; ring

/-- Source-profile pointwise form of the complete two-sign first
one-sided tail in DFI equation (29).  No transformed-sum hypothesis is
present: the constants come from the equation-(2), cutoff, and delta-weight
profiles. -/
theorem exists_dfiEquation29_xSingleTail_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ) (q : ℕ)
        (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        dfiEquation29XSingleTailWeilTotal X w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29XSingleLogMajorant Q Y b /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ))) := by
  obtain ⟨C, D, hC, hD, hRaw⟩ :=
    exists_dfiEquation29_xSingleTailWeilTotal_source_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hU ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h q hq hqQ
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * D * (14 * Real.pi + 8) /
    ((k : ℝ) - ε - 3 / 4)
  let G : ℝ := |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  have hqPos : 0 < q := NeZero.pos q
  have hlogq : |Real.log (qy : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le b q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hG : G ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    dsimp [G, dfiEquation29XSingleLogMajorant]
    linarith
  have hMaj : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hCore := dfiEquation29_xSingle_tail_source_core_le
    (q := q) (k := k) ha hb hP
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε.le hQsq h
  dsimp only at hCore
  have hProfile := hRaw a b q ha hb hq hqQ h
  dsimp only at hProfile
  have hFactor := dfiEquation29_xSingle_tail_source_factorization
    (a := a) (b := b) (q := q) (qx := qx) (qy := qy) (k := k)
    (h := h) (C := C) (D := D) (Q := Q) (X := X) (Y := Y) (ε := ε)
  dsimp only at hFactor
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hRawCore : 0 ≤ W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
      (X / a) ^ (-(1 / 4 : ℝ)) *
      ((X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((a : ℝ) * X) / Q ^ 2)) ^ k *
        L ^ (ε + 3 / 4 - k)) := by
    dsimp [W, qx, qy, L]
    positivity
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        dfiEquation29XSingleMainTailCoefficient
            C D k Q X Y a b q qx qy *
          (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      simpa only [W, qx, qy, L] using hProfile
    _ = 2 * (W * dfiEquation29XSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ = 2 * ((B * G) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          ((X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      rw [hFactor]
      dsimp [B, G]
      ring
    _ ≤ 2 * ((B * dfiEquation29XSingleLogMajorant Q Y b) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
          (X / a) ^ (-(1 / 4 : ℝ)) *
          ((X / a) * (Y / b) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      gcongr
    _ ≤ 2 * ((B * dfiEquation29XSingleLogMajorant Q Y b) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
          Q ^ (-ε * (k : ℝ)) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ))))) := by
      gcongr
    _ = _ := by dsimp [B]; ring

/-- Source-sharp symmetric pointwise form of the complete two-sign second
one-sided tail in DFI equation (29). -/
theorem exists_dfiEquation29_ySingleTail_l1_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ) (q : ℕ)
        (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29YSingleLogMajorant Q X a /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ))) := by
  obtain ⟨C, D, hC, hD, hRaw⟩ :=
    exists_dfiEquation29_ySingleTailWeilTotal_source_l1_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h q hq hqQ
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * D * (14 * Real.pi + 8) /
    ((k : ℝ) - ε - 3 / 4)
  let G : ℝ := |Real.log (X / a)| + |Real.log (2 * X / a)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  let M : ℝ := min X Y * Real.log Q
  have hqPos : 0 < q := NeZero.pos q
  have hlogq : |Real.log (qx : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le a q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hG : G ≤ dfiEquation29YSingleLogMajorant Q X a := by
    dsimp [G, dfiEquation29YSingleLogMajorant]
    linarith
  have hMaj : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmin : 0 ≤ min X Y :=
      le_min (zero_lt_one.trans_le hf.one_le_X).le
        (zero_lt_one.trans_le hf.one_le_Y).le
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hCore := dfiEquation29_ySingle_tail_l1_source_core_le
    (q := q) (k := k) (M := M) ha hb hP
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε.le hM hQsq h
  dsimp only at hCore
  have hProfile := hRaw a b q ha hb hq hqQ h
  dsimp only at hProfile
  have hFactor := dfiEquation29_ySingle_tail_l1_source_factorization
    (a := a) (b := b) (q := q) (qx := qx) (qy := qy) (k := k)
    (h := h) (C := C) (D := D) (Q := Q) (X := X) (Y := Y) (ε := ε)
  dsimp only at hFactor
  have hLpos : 0 < L := by
    dsimp only [L]
    exact_mod_cast dfiEquation29SourceYCutoff_pos hb
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 0 < Q) ε
  have hRawCore : 0 ≤ W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
      (Y / b) ^ (-(1 / 4 : ℝ)) *
      (((a : ℝ) * b)⁻¹ * M) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((b : ℝ) * Y) / Q ^ 2)) ^ k *
        L ^ (ε + 3 / 4 - k)) := by
    have hW0 : 0 ≤ W := by dsimp [W]; positivity
    have hqy0 : 0 ≤ (qy : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg qy) _
    have hqx0 : 0 ≤ (qx : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg qx)
    have hYb0 : 0 ≤ (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg
        (div_nonneg (zero_lt_one.trans_le hf.one_le_Y).le
          (Nat.cast_nonneg b)) _
    have hab0 : 0 ≤ (((a : ℝ) * b)⁻¹) := by positivity
    have hR0 : 0 ≤ ((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg Real.pi)
    have hscale0 : 0 ≤ ((b : ℝ) * Y) / Q ^ 2 :=
      div_nonneg
        (mul_nonneg (Nat.cast_nonneg b)
          (zero_lt_one.trans_le hf.one_le_Y).le) (sq_nonneg Q)
    have hrec0 : 0 ≤ (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((b : ℝ) * Y) / Q ^ 2)) ^ k) :=
      pow_nonneg (mul_nonneg hR0 hscale0) k
    have hL0 : 0 ≤ L ^ (ε + 3 / 4 - k) :=
      Real.rpow_nonneg hLpos.le _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hW0 hqy0) hqx0) hYb0)
          (mul_nonneg hab0 hM))
      (mul_nonneg hrec0 hL0)
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        dfiEquation29YSingleMainTailL1Coefficient
            C D k Q X Y a b qx qy *
          (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      simpa only [W, qx, qy, L] using hProfile
    _ = 2 * (W * dfiEquation29YSingleMainTailL1Coefficient
          C D k Q X Y a b qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ = 2 * ((B * G) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * M) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      rw [hFactor]
      dsimp [B, G, M]
      ring
    _ ≤ 2 * ((B * dfiEquation29YSingleLogMajorant Q X a) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * M) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      gcongr
    _ ≤ 2 * ((B * dfiEquation29YSingleLogMajorant Q X a) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
          Q ^ (-ε * (k : ℝ)) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * M *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ))))) := by
      gcongr
    _ = _ := by dsimp [B, M]; ring

/-- Symmetric source-profile pointwise form of the complete two-sign
second one-sided tail in DFI equation (29). -/
theorem exists_dfiEquation29_ySingleTail_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ)) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ) (q : ℕ)
        (_hq : NeZero q), (q : ℝ) ≤ 2 * Q →
        dfiEquation29YSingleTailWeilTotal Y w
            (dfiLocalizedWeight f φ h) a b h ε q ≤
          2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29YSingleLogMajorant Q X a /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ))) := by
  obtain ⟨C, D, hC, hD, hRaw⟩ :=
    exists_dfiEquation29_ySingleTailWeilTotal_source_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hU ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h q hq hqQ
  letI : NeZero q := hq
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let L : ℝ := dfiEquation29SourceYCutoff b Y Q ε
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let B : ℝ := C * D * (14 * Real.pi + 8) /
    ((k : ℝ) - ε - 3 / 4)
  let G : ℝ := |Real.log (X / a)| + |Real.log (2 * X / a)| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  have hqPos : 0 < q := NeZero.pos q
  have hlogq : |Real.log (qx : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le a q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hG : G ≤ dfiEquation29YSingleLogMajorant Q X a := by
    dsimp [G, dfiEquation29YSingleLogMajorant]
    linarith
  have hMaj : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hCore := dfiEquation29_ySingle_tail_source_core_le
    (q := q) (k := k) ha hb hP
      (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε.le hQsq h
  dsimp only at hCore
  have hProfile := hRaw a b q ha hb hq hqQ h
  dsimp only at hProfile
  have hFactor := dfiEquation29_ySingle_tail_source_factorization
    (a := a) (b := b) (q := q) (qx := qx) (qy := qy) (k := k)
    (h := h) (C := C) (D := D) (Q := Q) (X := X) (Y := Y) (ε := ε)
  dsimp only at hFactor
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hRawCore : 0 ≤ W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
      (Y / b) ^ (-(1 / 4 : ℝ)) *
      ((Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
          (((b : ℝ) * Y) / Q ^ 2)) ^ k *
        L ^ (ε + 3 / 4 - k)) := by
    dsimp [W, qx, qy, L]
    positivity
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        dfiEquation29YSingleMainTailCoefficient
            C D k Q X Y a b q qx qy *
          (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      simpa only [W, qx, qy, L] using hProfile
    _ = 2 * (W * dfiEquation29YSingleMainTailCoefficient
          C D k Q X Y a b q qx qy *
        (L ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4))) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ = 2 * ((B * G) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          ((Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      rw [hFactor]
      dsimp [B, G]
      ring
    _ ≤ 2 * ((B * dfiEquation29YSingleLogMajorant Q X a) *
        (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
          (Y / b) ^ (-(1 / 4 : ℝ)) *
          ((Y / b) * (X / a) * (((q : ℝ) * Q)⁻¹)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k *
            L ^ (ε + 3 / 4 - k)))) := by
      gcongr
    _ ≤ 2 * ((B * dfiEquation29YSingleLogMajorant Q X a) *
        (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
          Q ^ (-ε * (k : ℝ)) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ))))) := by
      gcongr
    _ = _ := by dsimp [B]; ring

/-- The source-sharp first one-sided tail summed over DFI's equation-(22)
moduli. -/
theorem exists_sum_dfiEquation29_xSingleTail_l1_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29XSingleLogMajorant Q Y b /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε))) *
          (min X Y * Real.log Q)) *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((a.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_xSingleTail_l1_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hU hP hQ hQsq ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h hh
  let A : ℝ := 2 * (C * D * (14 * Real.pi + 8) *
      dfiEquation29XSingleLogMajorant Q Y b /
        ((k : ℝ) - ε - 3 / 4)) *
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
      Q ^ (-ε * (k : ℝ))) *
    (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
      (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)))
  let M : ℝ := min X Y * Real.log Q
  let K : ℝ := A * M
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hMaj : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmin : 0 ≤ min X Y :=
      le_min (zero_lt_one.trans_le hf.one_le_X).le
        (zero_lt_one.trans_le hf.one_le_Y).le
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := mul_nonneg hA hM
  let Lmod := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 Lmod := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 Lmod, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      have hp := hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
      simpa only [K, A, M, mul_assoc] using hp
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((Lmod : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))) *
          Real.sqrt ((a.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 Lmod h.natAbs a
          (Int.natAbs_ne_zero.mpr hh) ha.ne' δ hδ) hK
    _ = _ := by dsimp [K, A, M, Lmod]

/-- The source-sharp second one-sided tail summed over DFI's equation-(22)
moduli. -/
theorem exists_sum_dfiEquation29_ySingleTail_l1_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29YSingleLogMajorant Q X a /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε))) *
          (min X Y * Real.log Q)) *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((b.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_ySingleTail_l1_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hU hP hQ hQsq ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h hh
  let A : ℝ := 2 * (C * D * (14 * Real.pi + 8) *
      dfiEquation29YSingleLogMajorant Q X a /
        ((k : ℝ) - ε - 3 / 4)) *
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
      Q ^ (-ε * (k : ℝ))) *
    (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
      (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)))
  let M : ℝ := min X Y * Real.log Q
  let K : ℝ := A * M
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hMaj : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    have hmin : 0 ≤ min X Y :=
      le_min (zero_lt_one.trans_le hf.one_le_X).le
        (zero_lt_one.trans_le hf.one_le_Y).le
    have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    positivity
  have hK : 0 ≤ K := mul_nonneg hA hM
  let Lmod := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 Lmod := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 Lmod, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      have hp := hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
      simpa only [K, A, M, mul_assoc] using hp
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((Lmod : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))) *
          Real.sqrt ((b.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 Lmod h.natAbs b
          (Int.natAbs_ne_zero.mpr hh) hb.ne' δ hδ) hK
    _ = _ := by dsimp [K, A, M, Lmod]

/-- The complete first one-sided tail summed over DFI's equation-(22)
moduli.  The extra `1/q` in the physical tail scale is discarded only
after using `q ≥ 1`; the remaining normalized Weil average is the same
one used by the retained branch. -/
theorem exists_sum_dfiEquation29_xSingleTail_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29XSingleLogMajorant Q Y b /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
            (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / Q))) *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((a.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_xSingleTail_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hU hP hQ hQsq ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h hh
  let A : ℝ := 2 * (C * D * (14 * Real.pi + 8) *
      dfiEquation29XSingleLogMajorant Q Y b /
        ((k : ℝ) - ε - 3 / 4)) *
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
      Q ^ (-ε * (k : ℝ))) *
    (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
      (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)))
  let K : ℝ := A * (X * Y / Q)
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hMaj : 0 ≤ dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let Lmod := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 Lmod := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 Lmod, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      have hS : X * Y / ((q : ℝ) * Q) ≤ X * Y / Q := by
        have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPos
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hinv : ((q : ℝ) * Q)⁻¹ ≤ Q⁻¹ := by
          exact inv_anti₀ hQ0
            (by nlinarith)
        gcongr
      have hp := hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
      calc
        _ ≤ A * (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ)) := by
          simpa only [A, mul_assoc] using hp
        _ ≤ A * (X * Y / Q) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
              (q.divisors.card : ℝ)) := by gcongr
        _ = _ := by rfl
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((Lmod : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))) *
          Real.sqrt ((a.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 Lmod h.natAbs a
          (Int.natAbs_ne_zero.mpr hh) ha.ne' δ hδ) hK
    _ = _ := by dsimp [K, A, Lmod]; ring

/-- The symmetric complete one-sided tail summed over equation-(22)
moduli. -/
theorem exists_sum_dfiEquation29_ySingleTail_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hU : U = Q ^ 2) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : ε + 3 / 4 < (k : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        (2 * (C * D * (14 * Real.pi + 8) *
            dfiEquation29YSingleLogMajorant Q X a /
              ((k : ℝ) - ε - 3 / 4)) *
          (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
            Q ^ (-ε * (k : ℝ))) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
            (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (X * Y / Q))) *
          (divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((b.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, D, hC, hD, hPoint⟩ :=
    exists_dfiEquation29_ySingleTail_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hU hP hQ hQsq ε hε k hk
  refine ⟨C, D, hC, hD, ?_⟩
  intro a b ha hb h hh
  let A : ℝ := 2 * (C * D * (14 * Real.pi + 8) *
      dfiEquation29YSingleLogMajorant Q X a /
        ((k : ℝ) - ε - 3 / 4)) *
    (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) ^ k) *
      Q ^ (-ε * (k : ℝ))) *
    (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
      (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)))
  let K : ℝ := A * (X * Y / Q)
  have hden : 0 < (k : ℝ) - ε - 3 / 4 := by linarith
  have hX0 : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY0 : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hQ0 : 0 < Q := by linarith
  have hMaj : 0 ≤ dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    have hlog : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let Lmod := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 Lmod := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 Lmod, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      have hS : X * Y / ((q : ℝ) * Q) ≤ X * Y / Q := by
        have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPos
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hinv : ((q : ℝ) * Q)⁻¹ ≤ Q⁻¹ := by
          exact inv_anti₀ hQ0
            (by nlinarith)
        gcongr
      have hp := hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
      calc
        _ ≤ A * (X * Y / ((q : ℝ) * Q)) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ)) := by
          simpa only [A, mul_assoc] using hp
        _ ≤ A * (X * Y / Q) *
            ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
              (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
              (q.divisors.card : ℝ)) := by gcongr
        _ = _ := by rfl
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 Lmod,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((Lmod : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))) *
          Real.sqrt ((b.divisors.card : ℝ) *
            (((harmonic Lmod : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 Lmod h.natAbs b
          (Int.natAbs_ne_zero.mpr hh) hb.ne' δ hδ) hK
    _ = _ := by dsimp [K, A, Lmod]; ring

/-- The coprime two-transform reduced-modulus normalization used by the
double-dual term in DFI equation (29). -/
theorem dfiEquation29_weil_mul_double_reduced_moduli_le
    (q a b : ℕ) [NeZero q] (hab : a.Coprime b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hgdvd := gcd_mul_gcd_dvd_right_of_coprime a b q hab
  have hgleN : Nat.gcd a q * Nat.gcd b q ≤ q := Nat.le_of_dvd hqN hgdvd
  have hgle : (Nat.gcd a q : ℝ) * Nat.gcd b q ≤ q := by
    exact_mod_cast hgleN
  have hsqrtprod :
      Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q) ≤ Real.sqrt q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd a q))]
    exact Real.sqrt_le_sqrt hgle
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_rpow_neg_half_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q)) /
          Real.sqrt q) := by field_simp
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) * (Real.sqrt q / Real.sqrt q) := by
      gcongr
    _ = _ := by field_simp

/-- Source-sharp normalization for the `x`-dual/`y`-main branch.  Unlike the
coarser uniform estimate, this keeps the square-root gcd from reducing the
`a`-modulus.  Its product with the shift gcd has a harmonic Cauchy average. -/
theorem dfiEquation29_weil_mul_xSingle_source_scale_sharp_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ *
        (a : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hgb : (Nat.gcd b q : ℝ) ≤ b := by
    exact_mod_cast Nat.gcd_le_left q hb
  have hratio : (Nat.gcd b q : ℝ) / b ≤ 1 :=
    (div_le_one hbR).2 hgb
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  calc
    _ = ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q)) *
        ((Nat.gcd b q : ℝ) / b) * (q.divisors.card : ℝ) := by
      field_simp
      rw [Real.sq_sqrt hq.le]
      ring
    _ ≤ ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q)) *
        1 * (q.divisors.card : ℝ) := by
      gcongr
    _ = _ := by ring

/-- Symmetric source-sharp normalization for the `y`-dual branch. -/
theorem dfiEquation29_weil_mul_ySingle_source_scale_sharp_le
    (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ)⁻¹ *
        (b : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  simpa only [mul_comm (a : ℝ) b] using
    dfiEquation29_weil_mul_xSingle_source_scale_sharp_le q b a hb ha h

/-- Exact source-sharp normalization for the double-dual branch.  The two
coefficient gcds are deliberately retained for the coprime square-root
average rather than bounded separately. -/
theorem dfiEquation29_weil_mul_double_reduced_moduli_sharp_eq
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
        (q.divisors.card : ℝ) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_rpow_neg_half_eq]
  rw [show Real.sqrt (Nat.gcd a q * Nat.gcd b q) =
      Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q) by
        rw [Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd a q))]]
  field_simp

/-- Exact simultaneous source scaling for the retained double-dual
rectangle in DFI equation (29). -/
theorem dfiEquation29_double_source_factor_identity
    {a b q : ℕ} [NeZero q] {X Y Q η R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hY : 0 < Y)
    (hQ : 0 < Q) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let α : ℝ := 3 / 4 + η / 2
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
        (2 * dfiEquation29SourceYTransition b Y Q η) ^ α =
      (2 ^ α * 2 ^ α) * X ^ (1 / 2 + η / 2) *
        Y ^ (1 / 2 + η / 2) * (a : ℝ) ^ (η / 2) *
        (b : ℝ) ^ (η / 2) *
        (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((a : ℝ) * b) * (((a : ℝ) * b)⁻¹)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let α : ℝ := 3 / 4 + η / 2
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hSourceX :
      dfiEquation29SourceXTransition a X Q η ^ α =
        (a : ℝ) ^ α * X ^ α * Q ^ ((-2 + η) * α) := by
    simpa only [α] using dfiEquation29SourceXTransition_rpow a hX hQ
  have hSourceY :
      dfiEquation29SourceYTransition b Y Q η ^ α =
        (b : ℝ) ^ α * Y ^ α * Q ^ ((-2 + η) * α) := by
    simpa only [α] using dfiEquation29SourceYTransition_rpow b hY hQ
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by unfold dfiEquation29SourceXTransition; positivity :
        0 ≤ dfiEquation29SourceXTransition a X Q η),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by unfold dfiEquation29SourceYTransition; positivity :
        0 ≤ dfiEquation29SourceYTransition b Y Q η),
    hSourceX, hSourceY]
  have hXa :
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) =
        X ^ (-(1 / 4 : ℝ)) * (a : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hX.le haR.le, Real.rpow_neg haR.le]
    field_simp
  have hYb :
      (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) =
        Y ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hY.le hbR.le, Real.rpow_neg hbR.le]
    field_simp
  rw [hXa, hYb]
  have hXpow : X ^ (-(1 / 4 : ℝ)) * X ^ α =
      X ^ (1 / 2 + η / 2) := by
    rw [← Real.rpow_add hX]
    congr 1
    dsimp [α]
    ring
  have hYpow : Y ^ (-(1 / 4 : ℝ)) * Y ^ α =
      Y ^ (1 / 2 + η / 2) := by
    rw [← Real.rpow_add hY]
    congr 1
    dsimp [α]
    ring
  have hapow : (a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ α =
      (a : ℝ) * (a : ℝ) ^ (η / 2) := by
    calc
      _ = (a : ℝ) ^ ((1 / 4 : ℝ) + α) :=
        (Real.rpow_add haR _ _).symm
      _ = (a : ℝ) ^ (1 + η / 2) := by
        congr 1
        dsimp [α]
        ring
      _ = (a : ℝ) ^ (1 : ℝ) * (a : ℝ) ^ (η / 2) :=
        Real.rpow_add haR 1 (η / 2)
      _ = _ := by rw [Real.rpow_one]
  have hbpow : (b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ α =
      (b : ℝ) * (b : ℝ) ^ (η / 2) := by
    calc
      _ = (b : ℝ) ^ ((1 / 4 : ℝ) + α) :=
        (Real.rpow_add hbR _ _).symm
      _ = (b : ℝ) ^ (1 + η / 2) := by
        congr 1
        dsimp [α]
        ring
      _ = (b : ℝ) ^ (1 : ℝ) * (b : ℝ) ^ (η / 2) :=
        Real.rpow_add hbR 1 (η / 2)
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = (2 ^ α * 2 ^ α) *
        (X ^ (-(1 / 4 : ℝ)) * X ^ α) *
        (Y ^ (-(1 / 4 : ℝ)) * Y ^ α) *
        ((a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ α) *
        ((b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ α) *
        (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (((a : ℝ) * b)⁻¹)) := by ring
    _ = _ := by
      rw [hXpow, hYpow, hapow, hbpow]
      ring

/-- The complete retained double-dual source factor after cutoff enlargement
and coprime reduced-modulus normalization. -/
theorem dfiEquation29_double_source_factor_le
    {a b q : ℕ} [NeZero q] {P X Y Q η R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let α : ℝ := 3 / 4 + η / 2
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
        (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤
      (2 ^ α * 2 ^ α) * X ^ (1 / 2 + η / 2) *
        Y ^ (1 / 2 + η / 2) * (a : ℝ) ^ (η / 2) *
        (b : ℝ) ^ (η / 2) *
        (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let α : ℝ := 3 / 4 + η / 2
  let A : ℝ := W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R)
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hCutX := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceXCutoff_le_two_mul_transition_optimized
      ha hP hX hY hQ hη hQsq) hα
  have hCutY := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceYCutoff_le_two_mul_transition_optimized
      hb hP hX hY hQ hη hQsq) hα
  have hA : 0 ≤ A := by dsimp [A, W, qx, qy]; positivity
  have hWindow :
      A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
          (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤
        A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
          (2 * dfiEquation29SourceYTransition b Y Q η) ^ α := by
    calc
      _ ≤ A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
          (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCutX hA)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hCutY
        (mul_nonneg hA (Real.rpow_nonneg
          (by unfold dfiEquation29SourceXTransition; positivity) _))
  have hIdentity := dfiEquation29_double_source_factor_identity
    (q := q) (η := η) (R := R) ha hb hX hY
      (zero_lt_one.trans_le hQ) h
  have hWeil := dfiEquation29_weil_mul_double_reduced_moduli_sharp_eq
    q a b h
  let K : ℝ := (2 ^ α * 2 ^ α) * X ^ (1 / 2 + η / 2) *
    Y ^ (1 / 2 + η / 2) * (a : ℝ) ^ (η / 2) *
    (b : ℝ) ^ (η / 2) *
    (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R
  have hK : 0 ≤ K := by dsimp [K, α]; positivity
  change A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
      (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤ _
  calc
    _ ≤ A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
        (2 * dfiEquation29SourceYTransition b Y Q η) ^ α := hWindow
    _ = K * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((a : ℝ) * b) * (((a : ℝ) * b)⁻¹)) := by
      simpa only [A, K, W, qx, qy, α] using hIdentity
    _ = K * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have habR : (0 : ℝ) < (a : ℝ) * b := mul_pos (by exact_mod_cast ha)
        (by exact_mod_cast hb)
      field_simp
    _ = K * ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
        (q.divisors.card : ℝ)) := by
      rw [show W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) =
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ) by
        simpa only [W, qx, qy] using hWeil]
    _ = _ := by rfl

/-- Two-parameter form of the double-dual source scaling.  The cutoff
transition carries DFI's epsilon `η`, while `α` is the real part of the
Mellin line.  Keeping these parameters independent is essential for the
complement of equation (29), where `α = 3/4 + η` rather than the retained
rectangle's `3/4 + η/2`. -/
theorem dfiEquation29_double_source_factor_le_general
    {a b q : ℕ} [NeZero q] {P X Y Q η α R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hη : 0 ≤ η) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
        (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤
      (2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
        (a : ℝ) ^ (α - 3 / 4) * (b : ℝ) ^ (α - 3 / 4) *
        (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ)) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let A : ℝ := W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R)
  have hCutX := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceXCutoff_le_two_mul_transition_optimized
      ha hP hX hY hQ hη hQsq) hα
  have hCutY := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (dfiEquation29SourceYCutoff_le_two_mul_transition_optimized
      hb hP hX hY hQ hη hQsq) hα
  have hA : 0 ≤ A := by dsimp [A, W, qx, qy]; positivity
  have hWindow :
      A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
          (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤
        A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
          (2 * dfiEquation29SourceYTransition b Y Q η) ^ α := by
    calc
      _ ≤ A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
          (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCutX hA)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hCutY
        (mul_nonneg hA (Real.rpow_nonneg
          (by unfold dfiEquation29SourceXTransition; positivity) _))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hSourceX :
      dfiEquation29SourceXTransition a X Q η ^ α =
        (a : ℝ) ^ α * X ^ α * Q ^ ((-2 + η) * α) :=
    dfiEquation29SourceXTransition_rpow a hX hQ0
  have hSourceY :
      dfiEquation29SourceYTransition b Y Q η ^ α =
        (b : ℝ) ^ α * Y ^ α * Q ^ ((-2 + η) * α) :=
    dfiEquation29SourceYTransition_rpow b hY hQ0
  have hXa :
      (X / (a : ℝ)) ^ (-(1 / 4 : ℝ)) =
        X ^ (-(1 / 4 : ℝ)) * (a : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hX.le haR.le, Real.rpow_neg haR.le]
    field_simp
  have hYb :
      (Y / (b : ℝ)) ^ (-(1 / 4 : ℝ)) =
        Y ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow hY.le hbR.le, Real.rpow_neg hbR.le]
    field_simp
  have hXpow : X ^ (-(1 / 4 : ℝ)) * X ^ α = X ^ (α - 1 / 4) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hYpow : Y ^ (-(1 / 4 : ℝ)) * Y ^ α = Y ^ (α - 1 / 4) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  have hapow : (a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ α =
      (a : ℝ) * (a : ℝ) ^ (α - 3 / 4) := by
    calc
      _ = (a : ℝ) ^ ((1 / 4 : ℝ) + α) :=
        (Real.rpow_add haR _ _).symm
      _ = (a : ℝ) ^ (1 + (α - 3 / 4)) := by
        congr 1
        ring
      _ = (a : ℝ) ^ (1 : ℝ) * (a : ℝ) ^ (α - 3 / 4) :=
        Real.rpow_add haR 1 (α - 3 / 4)
      _ = _ := by rw [Real.rpow_one]
  have hbpow : (b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ α =
      (b : ℝ) * (b : ℝ) ^ (α - 3 / 4) := by
    calc
      _ = (b : ℝ) ^ ((1 / 4 : ℝ) + α) :=
        (Real.rpow_add hbR _ _).symm
      _ = (b : ℝ) ^ (1 + (α - 3 / 4)) := by
        congr 1
        ring
      _ = (b : ℝ) ^ (1 : ℝ) * (b : ℝ) ^ (α - 3 / 4) :=
        Real.rpow_add hbR 1 (α - 3 / 4)
      _ = _ := by rw [Real.rpow_one]
  have hWeil := dfiEquation29_weil_mul_double_reduced_moduli_sharp_eq
    q a b h
  let K : ℝ := (2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) *
    Y ^ (α - 1 / 4) * (a : ℝ) ^ (α - 3 / 4) *
    (b : ℝ) ^ (α - 3 / 4) *
    (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R
  change A * (dfiEquation29SourceXCutoff a X Q η : ℝ) ^ α *
      (dfiEquation29SourceYCutoff b Y Q η : ℝ) ^ α ≤ _
  calc
    _ ≤ A * (2 * dfiEquation29SourceXTransition a X Q η) ^ α *
        (2 * dfiEquation29SourceYTransition b Y Q η) ^ α := hWindow
    _ = K * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) * ((a : ℝ) * b) *
        (((a : ℝ) * b)⁻¹)) := by
      dsimp [A, K]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by unfold dfiEquation29SourceXTransition; positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by unfold dfiEquation29SourceYTransition; positivity),
        hSourceX, hSourceY, hXa, hYb]
      calc
        _ = (2 ^ α * 2 ^ α) *
            (X ^ (-(1 / 4 : ℝ)) * X ^ α) *
            (Y ^ (-(1 / 4 : ℝ)) * Y ^ α) *
            ((a : ℝ) ^ (1 / 4 : ℝ) * (a : ℝ) ^ α) *
            ((b : ℝ) ^ (1 / 4 : ℝ) * (b : ℝ) ^ α) *
            (Q ^ ((-2 + η) * α) * Q ^ ((-2 + η) * α)) * R *
            (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (((a : ℝ) * b)⁻¹)) := by ring
        _ = _ := by rw [hXpow, hYpow, hapow, hbpow]; ring
    _ = K * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have habR : (0 : ℝ) < (a : ℝ) * b := mul_pos haR hbR
      field_simp
    _ = K * ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
        (q.divisors.card : ℝ)) := by
      rw [show W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) =
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ) by
        simpa only [W, qx, qy] using hWeil]
    _ = _ := by rfl

/-- Cancellation and source normalization for the retained-`x`, tail-`y`
region of DFI equation (29). -/
theorem dfiEquation29_double_yTail_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε α M R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hε : 0 ≤ ε) (hα : 0 ≤ α) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let Lx : ℝ := dfiEquation29SourceXCutoff a X Q ε
    let Ly : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) *
        (((R * (((b : ℝ) * Y) / Q ^ 2)) ^ k) *
          Lx ^ α * Ly ^ (α - k)) ≤
      (R ^ k * Q ^ (-ε * (k : ℝ))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (a : ℝ) ^ (α - 3 / 4) * (b : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + ε) * α) * Q ^ ((-2 + ε) * α)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
            (q.divisors.card : ℝ))) := by
  dsimp only
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let Lx : ℝ := dfiEquation29SourceXCutoff a X Q ε
  let Ly : ℝ := dfiEquation29SourceYCutoff b Y Q ε
  let A : ℝ := ((b : ℝ) * Y) / Q ^ 2
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hA : 0 < A := by dsimp [A]; positivity
  have hLy : 0 < Ly := by
    dsimp only [Ly]
    exact_mod_cast dfiEquation29SourceYCutoff_pos hb hY hQ0 ε
  have hTransition : A * Q ^ ε ≤ Ly := by
    have hEq : A * Q ^ ε = dfiEquation29SourceYTransition b Y Q ε := by
      dsimp only [A]
      unfold dfiEquation29SourceYTransition
      rw [show -2 + ε = -(2 : ℝ) + ε by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le,
        show Q ^ (2 : ℝ) = Q ^ 2 by norm_num]
      field_simp
    rw [hEq]
    exact dfiEquation29SourceYTransition_le_cutoff b Y Q ε
  have hRec := dfiEquation29_recurrence_cutoff_cancellation
    hA hQ hLy hTransition hR k (s := α)
  have hPrefix : 0 ≤
      W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) * Lx ^ α := by
    dsimp [W, qx, qy, Lx]
    positivity
  have hSource := dfiEquation29_double_source_factor_le_general
    (q := q) (η := ε) (α := α) (R := M)
      ha hb hP hX hY hQ hε hα hM hQsq h
  dsimp only at hSource
  rw [show W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) *
        ((R * A) ^ k * Lx ^ α * Ly ^ (α - k)) =
      (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) * Lx ^ α) *
        ((R * A) ^ k * Ly ^ (α - k)) by ring]
  calc
    _ ≤ (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) * Lx ^ α) *
        (R ^ k * Q ^ (-ε * (k : ℝ)) * Ly ^ α) :=
      mul_le_mul_of_nonneg_left hRec hPrefix
    _ = (R ^ k * Q ^ (-ε * (k : ℝ))) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * M) * Lx ^ α * Ly ^ α) := by ring
    _ ≤ (R ^ k * Q ^ (-ε * (k : ℝ))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (a : ℝ) ^ (α - 3 / 4) * (b : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + ε) * α) * Q ^ ((-2 + ε) * α)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
            (q.divisors.card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hSource
        (mul_nonneg (pow_nonneg hR k) (Real.rpow_nonneg hQ0.le _))

/-- Symmetric cancellation and normalization for the tail-`x`,
retained-`y` region of equation (29). -/
theorem dfiEquation29_double_xTail_source_core_le
    {a b q k : ℕ} [NeZero q] {P X Y Q ε α M R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hP : 1 ≤ P)
    (hX : 0 < X) (hY : 0 < Y) (hQ : 1 ≤ Q)
    (hε : 0 ≤ ε) (hα : 0 ≤ α) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) (h : ℤ) :
    let W := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let qx := (dfiReducedModulus a q).denominator
    let qy := (dfiReducedModulus b q).denominator
    let Lx : ℝ := dfiEquation29SourceXCutoff a X Q ε
    let Ly : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
        (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
        (((a : ℝ) * b)⁻¹ * M) *
        (((R * (((a : ℝ) * X) / Q ^ 2)) ^ k) *
          Lx ^ (α - k) * Ly ^ α) ≤
      (R ^ k * Q ^ (-ε * (k : ℝ))) *
        ((2 ^ α * 2 ^ α) * X ^ (α - 1 / 4) * Y ^ (α - 1 / 4) *
          (a : ℝ) ^ (α - 3 / 4) * (b : ℝ) ^ (α - 3 / 4) *
          (Q ^ ((-2 + ε) * α) * Q ^ ((-2 + ε) * α)) * M *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
            (q.divisors.card : ℝ))) := by
  have hSwap := dfiEquation29_double_yTail_source_core_le
      (a := b) (b := a) (q := q) (k := k)
      (P := P) (X := Y) (Y := X) (Q := Q) (ε := ε)
      (α := α) (M := M) (R := R)
      hb ha hP hY hX hQ hε hα hM hR
      (by simpa [add_comm, mul_comm] using hQsq) h
  unfold dfiEquation29SourceXCutoff dfiEquation29SourceYCutoff at hSwap ⊢
  unfold dfiEquation29SourceXTransition dfiEquation29SourceYTransition at hSwap ⊢
  simp only [mul_comm] at hSwap
  convert hSwap using 1 <;> ring

/-- Exact factorization of the retained-`x`, tail-`y` summand in the
tail-only equation-(29) bound. -/
theorem dfiEquation29_double_yTail_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ}
    {Cy Dy Ky Q X Y ε : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let Lx : ℝ := dfiEquation29SourceXCutoff a X Q ε
    let Ly : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    let α : ℝ := 3 / 4 + ε
    W * dfiEquation29YTailCoefficient Cy Dy Ky k Q X Y a b q qx qy *
        ((3 / 4 + ε)⁻¹ * Lx ^ (3 / 4 + ε)) *
        (Ly ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) =
      (Ky * Cy * Dy * (14 * Real.pi + 8) * α⁻¹ /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q))) *
          ((((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((b : ℝ) * Y) / Q ^ 2)) ^ k) *
            Lx ^ α * Ly ^ (α - k))) := by
  dsimp only
  have hqy0 : (0 : ℝ) ≤ qy := Nat.cast_nonneg qy
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qy : ℝ) =
      (14 * Real.pi + 8) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hqy0]
  have hphysical :
      (X / (a : ℝ)) * (Y / (b : ℝ)) *
          (Cy * (((q : ℝ) * Q)⁻¹)) =
        Cy * (((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q))) := by
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
  unfold dfiEquation29YTailCoefficient
  rw [hsqrt]
  rw [show (2 * X / (a : ℝ) - X / a) = X / a by ring]
  rw [show ε + 3 / 4 - (k : ℝ) = (3 / 4 + ε) - k by ring]
  let Z : ℝ :=
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) * Ky * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
      (X / a) ^ (-(1 / 4 : ℝ)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((b : ℝ) * Y) / Q ^ 2)) ^ k) * Dy *
      (14 * Real.pi + 8) * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
      (Y / b) ^ (-(1 / 4 : ℝ)) * (3 / 4 + ε)⁻¹ *
      (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) *
      ((dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^
        (3 / 4 + ε - k) / ((k : ℝ) - ε - 3 / 4))
  calc
    _ = Z * ((X / (a : ℝ)) * (Y / (b : ℝ)) *
        (Cy * (((q : ℝ) * Q)⁻¹))) := by dsimp [Z]; ring
    _ = Z * (Cy * (((a : ℝ) * b)⁻¹ *
        (X * Y / ((q : ℝ) * Q)))) := by rw [hphysical]
    _ = _ := by dsimp [Z]; ring

/-- Exact symmetric factorization of the tail-`x`, retained-`y` summand. -/
theorem dfiEquation29_double_xTail_source_factorization
    {a b q qx qy k : ℕ} {h : ℤ}
    {Cx Dx Kx Q X Y ε : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
      (q.divisors.card : ℝ)
    let Lx : ℝ := dfiEquation29SourceXCutoff a X Q ε
    let Ly : ℝ := dfiEquation29SourceYCutoff b Y Q ε
    let α : ℝ := 3 / 4 + ε
    W * dfiEquation29XTailCoefficient Cx Dx Kx k Q X Y a b q qx qy *
        (Lx ^ (ε + 3 / 4 - k) / ((k : ℝ) - ε - 3 / 4)) *
        ((3 / 4 + ε)⁻¹ * Ly ^ (3 / 4 + ε)) =
      (Kx * Cx * Dx * (14 * Real.pi + 8) * α⁻¹ /
          ((k : ℝ) - ε - 3 / 4)) *
        (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
          (((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q))) *
          ((((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
              (((a : ℝ) * X) / Q ^ 2)) ^ k) *
            Lx ^ (α - k) * Ly ^ α)) := by
  dsimp only
  have hqx0 : (0 : ℝ) ≤ qx := Nat.cast_nonneg qx
  have hsqrt : (14 * Real.pi + 8) / Real.sqrt (qx : ℝ) =
      (14 * Real.pi + 8) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hqx0]
  have hphysical :
      (Y / (b : ℝ)) * (X / (a : ℝ)) *
          (Cx * (((q : ℝ) * Q)⁻¹)) =
        Cx * (((a : ℝ) * b)⁻¹ * (X * Y / ((q : ℝ) * Q))) := by
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
  unfold dfiEquation29XTailCoefficient
  rw [hsqrt]
  rw [show (2 * Y / (b : ℝ) - Y / b) = Y / b by ring]
  rw [show ε + 3 / 4 - (k : ℝ) = (3 / 4 + ε) - k by ring]
  let Z : ℝ :=
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) * Kx * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
      (Y / b) ^ (-(1 / 4 : ℝ)) *
      (((((2 * k + 3 : ℕ) : ℝ) / Real.pi ^ 2) *
        (((a : ℝ) * X) / Q ^ 2)) ^ k) * Dx *
      (14 * Real.pi + 8) * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
      (X / a) ^ (-(1 / 4 : ℝ)) *
      ((dfiEquation29SourceXCutoff a X Q ε : ℝ) ^
        (3 / 4 + ε - k) / ((k : ℝ) - ε - 3 / 4)) *
      (3 / 4 + ε)⁻¹ *
      (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)
  calc
    _ = Z * ((Y / (b : ℝ)) * (X / (a : ℝ)) *
        (Cx * (((q : ℝ) * Q)⁻¹))) := by dsimp [Z]; ring
    _ = Z * (Cx * (((a : ℝ) * b)⁻¹ *
        (X * Y / ((q : ℝ) * Q)))) := by rw [hphysical]
    _ = _ := by dsimp [Z]; ring

/-- The retained `x`-dual source contribution at one delta modulus, now
with the optimized transition substituted before the arithmetic estimate. -/
theorem exists_dfiEquation29_xSingleRetained_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
      (q : ℕ) (_hq0 : NeZero q),
      (q : ℝ) ≤ 2 * Q →
      dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q ≤
        (2 * C * dfiEquation29XSingleLogMajorant Q Y b) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) * (a : ℝ) ^ ε *
            Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q)) *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨Kret, hKret, hRaw⟩ :=
    exists_dfiEquation29_xSingleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hKmass : 0 ≤ Kmass := by
    dsimp [Kmass]
    have hf0 := (hfC.finiteConstant_pos 0).le
    have hφ0 : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      simp [dfiCutoffFiniteConstant, (hφC.positive 0).le]
    have hw0 : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    positivity
  let C : ℝ := Kret * Kmass
  have hC : 0 ≤ C := mul_nonneg hKret hKmass
  refine ⟨C, hC, ?_⟩
  intro a b ha hb h q hq0 hqQ
  letI : NeZero q := hq0
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29XSingleRetainedWeilTotal, dif_neg hqPos.ne']
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let R : ℝ := min X Y * Real.log Q
  let B : ℝ := C * dfiEquation29XSingleLogMajorant Q Y b
  have hlogq : |Real.log (qy : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le b q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hlog :
      |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| ≤
        dfiEquation29XSingleLogMajorant Q Y b := by
    unfold dfiEquation29XSingleLogMajorant
    linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    have hmin : 0 ≤ min X Y := le_min
      (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    exact mul_nonneg hmin hlogQ
  have hB : 0 ≤ B := by
    dsimp [B, dfiEquation29XSingleLogMajorant]
    have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hm := mul_nonneg (inv_nonneg.mpr (mul_nonneg
      (Nat.cast_nonneg a) (Nat.cast_nonneg b))) hR
    dsimp [R] at hm
    nlinarith
  have hprefix : 0 ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
      (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ := by
    dsimp [qx, qy]
    have hXa : 0 ≤ X / (a : ℝ) := div_nonneg
      (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)
    positivity
  have hEach (branch : DFIVoronoiDualBranch) :
      (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
        B * ((qx : ℝ) ^ (-(1 / 2 : ℝ)) * (X / a) ^ (-(1 / 4 : ℝ)) *
          (qy : ℝ)⁻¹ * (((a : ℝ) * b)⁻¹ * R) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)) := by
    have hr := hRaw a b ha hb h q hq0 branch
    dsimp only [qx, qy, E] at hr
    calc
      _ ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (|Real.log (Y / b)| + |Real.log (2 * Y / b)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
        simpa only [C, Kmass] using hr
      _ ≤ C * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          dfiEquation29XSingleLogMajorant Q Y b *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε) := by
        gcongr
      _ = _ := by dsimp [B, R]; ring
  have hSource := dfiEquation29_xSingle_source_factor_le
    (q := q) ha hb hP (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε₀.le hR hQsq h
  dsimp only at hSource
  change W * (∑ branch : DFIVoronoiDualBranch,
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ‖dfiVoronoiDualTerm qx branch
          (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤ _
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        B * ((qx : ℝ) ^ (-(1 / 2 : ℝ)) *
          (X / a) ^ (-(1 / 4 : ℝ)) * (qy : ℝ)⁻¹ *
          (((a : ℝ) * b)⁻¹ * R) *
          (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε))) := by
      gcongr with branch
      exact hEach branch
    _ = 2 * B * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) * (qy : ℝ)⁻¹ *
        (X / a) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε)) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ ≤ 2 * B * (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
        (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [W, qx, qy, R] using hSource)
        (mul_nonneg (by norm_num) hB)
    _ = _ := by dsimp [B, R]; ring

/-- The retained `x`-dual branch summed over DFI's equation-(22) moduli,
using the shift-uniform normalized Weil average. -/
theorem exists_sum_dfiEquation29_xSingleRetained_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        ((2 * C * dfiEquation29XSingleLogMajorant Q Y b) *
          (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) * (a : ℝ) ^ ε *
            Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q))) *
          (divisorEpsilonConstant δ *
            max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((a.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_xSingleRetained_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hP hQsq ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro a b ha hb h hh
  let K : ℝ := (2 * C * dfiEquation29XSingleLogMajorant Q Y b) *
    (2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) * (a : ℝ) ^ ε *
      Q ^ ((-2 + ε) * (3 / 4 + ε)) * (min X Y * Real.log Q))
  have hK : 0 ≤ K := by
    dsimp [K, dfiEquation29XSingleLogMajorant]
    have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    have hmin : 0 ≤ min X Y := le_min
      (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    have hXpos : 0 < X := zero_lt_one.trans_le hf.one_le_X
    have hQpos : 0 < Q := by linarith
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hMaj : 0 ≤ |Real.log (Y / ↑b)| + |Real.log (2 * Y / ↑b)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
      have h1 : 0 ≤ |Real.log (Y / ↑b)| := abs_nonneg _
      have h2 : 0 ≤ |Real.log (2 * Y / ↑b)| := abs_nonneg _
      have h3 : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
      linarith
    have hLeft : 0 ≤ 2 * C *
        (|Real.log (Y / ↑b)| + |Real.log (2 * Y / ↑b)| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) hMaj
    have hRight : 0 ≤ 2 ^ (3 / 4 + ε) * X ^ (1 / 2 + ε) *
        (a : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) *
        (min X Y * Real.log Q) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg hXpos.le _))
            (Real.rpow_nonneg haR.le _))
          (Real.rpow_nonneg hQpos.le _))
        (mul_nonneg hmin hlogQ)
    exact mul_nonneg hLeft hRight
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 L, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      simpa only [K, mul_assoc] using hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt ((a.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 L h.natAbs a
          (Int.natAbs_ne_zero.mpr hh) ha.ne' δ hδ) hK
    _ = _ := by rfl

/-- Symmetric one-modulus optimized bound for the retained `y`-dual
source contribution. -/
theorem exists_dfiEquation29_ySingleRetained_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
      (q : ℕ) (_hq0 : NeZero q),
      (q : ℝ) ≤ 2 * Q →
      dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q ≤
        (2 * C * dfiEquation29YSingleLogMajorant Q X a) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) * (b : ℝ) ^ ε *
            Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q)) *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨Kret, hKret, hRaw⟩ :=
    exists_dfiEquation29_ySingleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hKmass : 0 ≤ Kmass := by
    dsimp [Kmass]
    have hf0 := (hfC.finiteConstant_pos 0).le
    have hφ0 : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      simp [dfiCutoffFiniteConstant, (hφC.positive 0).le]
    have hw0 : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    positivity
  let C : ℝ := Kret * Kmass
  have hC : 0 ≤ C := mul_nonneg hKret hKmass
  refine ⟨C, hC, ?_⟩
  intro a b ha hb h q hq0 hqQ
  letI : NeZero q := hq0
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29YSingleRetainedWeilTotal, dif_neg hqPos.ne']
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let R : ℝ := min X Y * Real.log Q
  let B : ℝ := C * dfiEquation29YSingleLogMajorant Q X a
  have hlogq : |Real.log (qx : ℝ)| ≤ Real.log (2 * Q) :=
    (abs_log_dfiReducedModulus_denominator_le a q).trans
      (Real.log_le_log (by exact_mod_cast hqPos) hqQ)
  have hlog :
      |Real.log (X / a)| + |Real.log (2 * X / a)| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| ≤
        dfiEquation29YSingleLogMajorant Q X a := by
    unfold dfiEquation29YSingleLogMajorant
    linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y]))
      (Real.log_nonneg (by linarith))
  have hB : 0 ≤ B := by
    dsimp [B, dfiEquation29YSingleLogMajorant]
    have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ |Real.log (X / ↑a)| := abs_nonneg _
    have h2 : 0 ≤ |Real.log (2 * X / ↑a)| := abs_nonneg _
    have h3 : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
    positivity
  have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
    have hm := mul_nonneg (inv_nonneg.mpr (mul_nonneg
      (Nat.cast_nonneg a) (Nat.cast_nonneg b))) hR
    dsimp [R] at hm
    nlinarith
  have hprefix : 0 ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
      (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ := by
    dsimp [qx, qy]
    have hYb : 0 ≤ Y / (b : ℝ) := div_nonneg
      (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)
    positivity
  have hEach (branch : DFIVoronoiDualBranch) :
      (∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
        B * ((qy : ℝ) ^ (-(1 / 2 : ℝ)) * (Y / b) ^ (-(1 / 4 : ℝ)) *
          (qx : ℝ)⁻¹ * (((a : ℝ) * b)⁻¹ * R) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)) := by
    have hr := hRaw a b ha hb h q hq0 branch
    dsimp only [qx, qy, E] at hr
    calc
      _ ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (|Real.log (X / a)| + |Real.log (2 * X / a)| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
        simpa only [C, Kmass] using hr
      _ ≤ C * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          dfiEquation29YSingleLogMajorant Q X a *
          (((a : ℝ) * b)⁻¹ * min X Y * Real.log Q) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε) := by
        gcongr
      _ = _ := by dsimp [B, R]; ring
  have hSource := dfiEquation29_ySingle_source_factor_le
    (q := q) ha hb hP (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε₀.le hR hQsq h
  dsimp only at hSource
  change W * (∑ branch : DFIVoronoiDualBranch,
      ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
        ‖dfiVoronoiDualTerm qy branch
          (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤ _
  calc
    _ ≤ W * (∑ _branch : DFIVoronoiDualBranch,
        B * ((qy : ℝ) ^ (-(1 / 2 : ℝ)) *
          (Y / b) ^ (-(1 / 4 : ℝ)) * (qx : ℝ)⁻¹ *
          (((a : ℝ) * b)⁻¹ * R) *
          (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε))) := by
      gcongr with branch
      exact hEach branch
    _ = 2 * B * (W * (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (qx : ℝ)⁻¹ *
        (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε)) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring
    _ ≤ 2 * B * (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) *
        (b : ℝ) ^ ε * Q ^ ((-2 + ε) * (3 / 4 + ε)) * R *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [W, qx, qy, R] using hSource)
        (mul_nonneg (by norm_num) hB)
    _ = _ := by dsimp [B, R]; ring

/-- The retained `y`-dual branch summed over equation-(22) moduli with the
normalized shift-uniform Weil average. -/
theorem exists_sum_dfiEquation29_ySingleRetained_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        ((2 * C * dfiEquation29YSingleLogMajorant Q X a) *
          (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) * (b : ℝ) ^ ε *
            Q ^ ((-2 + ε) * (3 / 4 + ε)) *
            (min X Y * Real.log Q))) *
          (divisorEpsilonConstant δ *
            max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt ((b.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))))) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_ySingleRetained_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hP hQsq ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro a b ha hb h hh
  let K : ℝ := (2 * C * dfiEquation29YSingleLogMajorant Q X a) *
    (2 ^ (3 / 4 + ε) * Y ^ (1 / 2 + ε) * (b : ℝ) ^ ε *
      Q ^ ((-2 + ε) * (3 / 4 + ε)) * (min X Y * Real.log Q))
  have hK : 0 ≤ K := by
    dsimp [K, dfiEquation29YSingleLogMajorant]
    have hlog2Q : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
    have hmin : 0 ≤ min X Y := le_min
      (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    have hYpos : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
    have hQpos : 0 < Q := by linarith
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hMaj : 0 ≤ |Real.log (X / ↑a)| + |Real.log (2 * X / ↑a)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
      have h1 : 0 ≤ |Real.log (X / ↑a)| := abs_nonneg _
      have h2 : 0 ≤ |Real.log (2 * X / ↑a)| := abs_nonneg _
      have h3 : 0 ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
      linarith
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC) hMaj)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg hYpos.le _))
            (Real.rpow_nonneg hbR.le _))
          (Real.rpow_nonneg hQpos.le _))
        (mul_nonneg hmin hlogQ))
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 L, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      have hqMod : q ∈ dfiEquation22Moduli Q := by rw [hset]; exact hqMem
      have hqQ : (q : ℝ) ≤ 2 * Q :=
        (mem_dfiEquation22Moduli_iff q).1 hqMod |>.2.le
      simpa only [K, mul_assoc] using hPoint a b ha hb h q ⟨hqPos.ne'⟩ hqQ
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (Real.sqrt (Nat.gcd b q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt ((b.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_two_sqrt_gcd_mul_divisors_div_le 0 L h.natAbs b
          (Int.natAbs_ne_zero.mpr hh) hb.ne' δ hδ) hK
    _ = _ := by rfl

/-- One-modulus optimized bound for all four retained double-dual sign
pairs in DFI equation (29). -/
theorem exists_dfiEquation29_doubleRetained_optimized_pointwise_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ), 0 < a → 0 < b → ∀ (h : ℤ)
      (q : ℕ) (_hq0 : NeZero q),
      dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q ≤
        (4 * C) *
          ((2 ^ (3 / 4 + ε / 2) * 2 ^ (3 / 4 + ε / 2)) *
            X ^ (1 / 2 + ε / 2) * Y ^ (1 / 2 + ε / 2) *
            (a : ℝ) ^ (ε / 2) * (b : ℝ) ^ (ε / 2) *
            (Q ^ ((-2 + ε) * (3 / 4 + ε / 2)) *
              Q ^ ((-2 + ε) * (3 / 4 + ε / 2))) *
            (min X Y * Real.log Q)) *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
            (q.divisors.card : ℝ)) := by
  obtain ⟨Kret, hKret, hRaw⟩ :=
    exists_dfiEquation29_doubleDual_source_retained_bound_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hQ hU ε hε₀ hε
  let Kmass : ℝ := (dfiEquation2FiniteConstant Cf 0 *
      dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))
  have hKmass : 0 ≤ Kmass := by
    dsimp [Kmass]
    have hf0 := (hfC.finiteConstant_pos 0).le
    have hφ0 : 0 ≤ dfiCutoffFiniteConstant Cφ 0 := by
      simp [dfiCutoffFiniteConstant, (hφC.positive 0).le]
    have hw0 : 0 ≤ max (Cw 0) (Cw 1) :=
      (hwC.positive 0).le.trans (le_max_left _ _)
    positivity
  let C : ℝ := Kret * Kmass
  have hC : 0 ≤ C := mul_nonneg hKret hKmass
  refine ⟨C, hC, ?_⟩
  intro a b ha hb h q hq0
  letI : NeZero q := hq0
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29DoubleRetainedWeilTotal, dif_neg hqPos.ne']
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let W : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  let R : ℝ := min X Y * Real.log Q
  let A : ℝ := (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
    (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (X / a) ^ (-(1 / 4 : ℝ)) *
    (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R) *
    (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
    (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2)
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (le_min (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y]))
      (Real.log_nonneg (by linarith))
  have hA : 0 ≤ A := by
    dsimp [A]
    have hmass : 0 ≤ ((a : ℝ) * b)⁻¹ * R :=
      mul_nonneg (inv_nonneg.mpr (mul_nonneg
        (Nat.cast_nonneg a) (Nat.cast_nonneg b))) hR
    have hXa : 0 ≤ X / (a : ℝ) := div_nonneg
      (by linarith [hf.one_le_X]) (Nat.cast_nonneg a)
    have hYb : 0 ≤ Y / (b : ℝ) := div_nonneg
      (by linarith [hf.one_le_Y]) (Nat.cast_nonneg b)
    positivity
  have hEach (xBranch yBranch : DFIVoronoiDualBranch) :
      (∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
        ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤ C * A := by
    have hr := hRaw a b ha hb h q hq0 xBranch yBranch
    dsimp only [qx, qy, E] at hr
    simpa only [C, Kmass, A, R, mul_assoc] using hr
  have hSource := dfiEquation29_double_source_factor_le
    (q := q) ha hb hP (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y) (by linarith : 1 ≤ Q)
      hε₀.le hR hQsq h
  dsimp only at hSource
  have hW : 0 ≤ W := by dsimp [W]; positivity
  change W * (∑ xBranch : DFIVoronoiDualBranch,
      ∑ yBranch : DFIVoronoiDualBranch,
        ∑ m ∈ Finset.Icc 1 (dfiEquation29SourceXCutoff a X Q ε),
          ∑ n ∈ Finset.Icc 1 (dfiEquation29SourceYCutoff b Y Q ε),
            ‖dfiEquation24DoubleDualMellinAmplitude
              qx xBranch qy yBranch E m n‖) ≤ _
  calc
    _ ≤ W * (∑ _xBranch : DFIVoronoiDualBranch,
        ∑ _yBranch : DFIVoronoiDualBranch, C * A) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply Finset.sum_le_sum
      intro xb _
      apply Finset.sum_le_sum
      intro yb _
      exact hEach xb yb
    _ = 4 * C * (W * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
        (qy : ℝ) ^ (-(1 / 2 : ℝ)) * (X / a) ^ (-(1 / 4 : ℝ)) *
        (Y / b) ^ (-(1 / 4 : ℝ)) * (((a : ℝ) * b)⁻¹ * R) *
        (dfiEquation29SourceXCutoff a X Q ε : ℝ) ^ (3 / 4 + ε / 2) *
        (dfiEquation29SourceYCutoff b Y Q ε : ℝ) ^ (3 / 4 + ε / 2)) := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      dsimp [A]
      ring
    _ ≤ 4 * C *
        ((2 ^ (3 / 4 + ε / 2) * 2 ^ (3 / 4 + ε / 2)) *
          X ^ (1 / 2 + ε / 2) * Y ^ (1 / 2 + ε / 2) *
          (a : ℝ) ^ (ε / 2) * (b : ℝ) ^ (ε / 2) *
          (Q ^ ((-2 + ε) * (3 / 4 + ε / 2)) *
            Q ^ ((-2 + ε) * (3 / 4 + ε / 2))) * R *
          ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
            Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
            (q.divisors.card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [W, qx, qy, R] using hSource)
        (mul_nonneg (by norm_num) hC)
    _ = _ := by dsimp [R]; ring

/-- The retained double-dual rectangle summed over all DFI moduli with the
coprime equation-(25) modulus estimate. -/
theorem exists_sum_dfiEquation29_doubleRetained_optimized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (hP : 1 ≤ P)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y))
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a b : ℕ), 0 < a → 0 < b → a.Coprime b →
      ∀ (h : ℤ), h ≠ 0 →
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) ≤
        ((4 * C) *
          ((2 ^ (3 / 4 + ε / 2) * 2 ^ (3 / 4 + ε / 2)) *
            X ^ (1 / 2 + ε / 2) * Y ^ (1 / 2 + ε / 2) *
            (a : ℝ) ^ (ε / 2) * (b : ℝ) ^ (ε / 2) *
            (Q ^ ((-2 + ε) * (3 / 4 + ε / 2)) *
              Q ^ ((-2 + ε) * (3 / 4 + ε / 2))) *
            (min X Y * Real.log Q))) *
          (divisorEpsilonConstant δ *
            max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
            (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
                (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
              Real.sqrt (((a * b).divisors.card : ℝ) * ⌈2 * Q⌉₊))) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiEquation29_doubleRetained_optimized_pointwise_le
      hf hfC hbox hφ hφC hscale w hwC hQ hU hP hQsq ε hε₀ hε
  refine ⟨C, hC, ?_⟩
  intro a b ha hb hab h hh
  let K : ℝ := (4 * C) *
    ((2 ^ (3 / 4 + ε / 2) * 2 ^ (3 / 4 + ε / 2)) *
      X ^ (1 / 2 + ε / 2) * Y ^ (1 / 2 + ε / 2) *
      (a : ℝ) ^ (ε / 2) * (b : ℝ) ^ (ε / 2) *
      (Q ^ ((-2 + ε) * (3 / 4 + ε / 2)) *
        Q ^ ((-2 + ε) * (3 / 4 + ε / 2))) *
      (min X Y * Real.log Q))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hmin : 0 ≤ min X Y := le_min
      (by linarith [hf.one_le_X]) (by linarith [hf.one_le_Y])
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    have hXpos : 0 < X := zero_lt_one.trans_le hf.one_le_X
    have hYpos : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
    have hQpos : 0 < Q := by linarith
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    positivity
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    _ ≤ ∑ q ∈ Finset.Ioo 0 L, K *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      simpa only [K, mul_assoc] using hPoint a b ha hb h q ⟨hqPos.ne'⟩
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ)) := by rw [Finset.mul_sum]
    _ = K * ∑ q ∈ Finset.Ioo 0 L,
        ((Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          Real.sqrt (Nat.gcd a q * Nat.gcd b q) *
          (q.divisors.card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hqMem
      have hqPos : 0 < q := (Finset.mem_Ioo.mp hqMem).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ K * (divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        (Real.sqrt ((h.natAbs.divisors.card : ℝ) *
            (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt (((a * b).divisors.card : ℝ) * L))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_three_sqrt_gcd_mul_divisors_div_sqrt_le
          0 L h.natAbs a b (Int.natAbs_ne_zero.mpr hh) ha hb hab δ hδ) hK
    _ = _ := by rfl

/-- After the optimized DFI choice of `Q`, the second pre-optimized
error term with `ε = 0` is exactly the published error scale. -/
theorem dfiEquation30_second_optimized_eq
    {P X Y Q : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ)) =
      P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) := by
  have hXY : 0 < X * Y := mul_pos hX hY
  have hSum : 0 < X + Y := add_pos hX hY
  have hQpow : Q ^ (-(5 / 2 : ℝ)) =
      (Q ^ 2) ^ (-(5 / 4 : ℝ)) := by
    rw [show Q ^ 2 = Q ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [hQpow, hQsq]
  rw [Real.mul_rpow (by positivity : 0 ≤ P⁻¹ * (X + Y)⁻¹) hXY.le,
    Real.mul_rpow (inv_nonneg.mpr hP.le) (inv_nonneg.mpr hSum.le),
    Real.inv_rpow hP.le, Real.inv_rpow hSum.le]
  rw [← Real.rpow_neg hP.le, ← Real.rpow_neg hSum.le]
  field_simp
  rw [show (X * Y) ^ (3 / 2 : ℝ) * (X + Y) ^ (5 / 4 : ℝ) *
        (X * Y) ^ (-(5 / 4 : ℝ)) =
      ((X * Y) ^ (3 / 2 : ℝ) * (X * Y) ^ (-(5 / 4 : ℝ))) *
        (X + Y) ^ (5 / 4 : ℝ) by ring,
    ← Real.rpow_add hXY,
    show (3 / 2 : ℝ) + -(5 / 4 : ℝ) = 1 / 4 by norm_num,
    show (X + Y) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) =
      ((X + Y) ^ (1 : ℝ) * (X + Y) ^ (1 / 4 : ℝ)) *
        (X * Y) ^ (1 / 4 : ℝ) by rw [Real.rpow_one],
    ← Real.rpow_add hSum]
  norm_num
  ring

/-- The first pre-optimized error term at `ε = 0` is no larger than
the published scale.  The factor `(ab)⁻¹` only improves this estimate. -/
theorem dfiEquation30_first_optimized_le
    {a b : ℕ} {P X Y Q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-(1 : ℝ))) ≤
      P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (1 / 4 : ℝ) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have hSum : 0 < X + Y := add_pos hX0 hY0
  have hQpow : Q ^ (-(1 : ℝ)) =
      (Q ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [show Q ^ 2 = Q ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hQ.le]
    congr 1
    ring
  have hQinv : Q ^ (-(1 : ℝ)) =
      P ^ (1 / 2 : ℝ) * (X + Y) ^ (1 / 2 : ℝ) *
        (X * Y) ^ (-(1 / 2 : ℝ)) := by
    rw [hQpow, hQsq]
    rw [Real.mul_rpow (by positivity : 0 ≤ P⁻¹ * (X + Y)⁻¹) hXY.le,
      Real.mul_rpow (inv_nonneg.mpr hP0.le) (inv_nonneg.mpr hSum.le),
      Real.inv_rpow hP0.le, Real.inv_rpow hSum.le]
    rw [← Real.rpow_neg hP0.le, ← Real.rpow_neg hSum.le]
    congr 1
    ring
  have hsumOne : 1 ≤ X + Y := by linarith
  have hxsum : X ≤ X + Y := by linarith
  have hysum : Y ≤ X + Y := by linarith
  have hXYsumSq : X * Y ≤ (X + Y) * (X + Y) :=
    mul_le_mul hxsum hysum hY0.le (by linarith)
  have hXYsumCube : X * Y ≤ (X + Y) ^ 3 := by
    calc
      X * Y ≤ (X + Y) * (X + Y) := hXYsumSq
      _ ≤ (X + Y) ^ 3 := by nlinarith
  have hroot : (X * Y) ^ (1 / 4 : ℝ) ≤
      (X + Y) ^ (3 / 4 : ℝ) := by
    have hr := Real.rpow_le_rpow hXY.le hXYsumCube
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      _ ≤ ((X + Y) ^ 3) ^ (1 / 4 : ℝ) := hr
      _ = _ := by
        rw [show (X + Y) ^ 3 = (X + Y) ^ (3 : ℝ) by norm_num,
          ← Real.rpow_mul hSum.le]
        congr 1
        ring
  have hXYhalf : (X * Y) ^ (1 / 2 : ℝ) =
      (X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hXY]
    congr 1
    ring
  have hXYhalfSq : ((X * Y) ^ (1 / 2 : ℝ)) ^ 2 = X * Y := by
    rw [show ((X * Y) ^ (1 / 2 : ℝ)) ^ 2 =
        ((X * Y) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hXY.le]
    norm_num
  have hSumHalfSq : ((X + Y) ^ (1 / 2 : ℝ)) ^ 2 = X + Y := by
    rw [show ((X + Y) ^ (1 / 2 : ℝ)) ^ 2 =
        ((X + Y) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul hSum.le]
    norm_num
  have hscale : (X + Y) ^ (-(1 / 2 : ℝ)) *
      (X * Y) ^ (1 / 2 : ℝ) ≤
      (X + Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ) := by
    calc
      _ = ((X + Y) ^ (-(1 / 2 : ℝ)) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ (1 / 4 : ℝ) := by
        rw [hXYhalf]
        ring
      _ ≤ ((X + Y) ^ (-(1 / 2 : ℝ)) *
          (X + Y) ^ (3 / 4 : ℝ)) * (X * Y) ^ (1 / 4 : ℝ) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_add hSum]
        congr 1
        ring
  rw [hQinv]
  have habInv : (((a : ℝ) * b)⁻¹) ≤ 1 := by
    apply (inv_le_one₀ (by positivity : (0 : ℝ) < (a : ℝ) * b)).2
    have habOne : 1 ≤ a * b :=
      Nat.one_le_iff_ne_zero.2 (mul_ne_zero ha.ne' hb.ne')
    exact_mod_cast habOne
  have hPpow : P ^ (1 / 2 : ℝ) ≤ P ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  calc
    _ = (((a : ℝ) * b)⁻¹) * P ^ (1 / 2 : ℝ) *
        ((X + Y) ^ (-(1 / 2 : ℝ)) *
          (X * Y) ^ (1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_neg hSum.le,
        Real.rpow_neg hXY.le]
      field_simp
      rw [hSumHalfSq, hXYhalfSq]
      ring
    _ ≤ 1 * P ^ (5 / 4 : ℝ) *
        ((X + Y) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 4 : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- DFI's two pre-optimized errors are bounded by twice the published
Theorem 1 scale.  The harmless factor `2` is absorbed by the theorem's
implicit constant. -/
theorem dfiEquation30_preoptimizedError_le_two_mul_theorem1ErrorScale
    {a b : ℕ} {P X Y Q ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 0 < Q)
    (hε : 0 ≤ ε)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    dfiEquation30PreoptimizedError a b X Y Q ε ≤
      2 * dfiTheorem1ErrorScale P X Y ε := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have hSum : 0 < X + Y := add_pos hX0 hY0
  have hXYOne : 1 ≤ X * Y := by
    nlinarith [mul_nonneg (show 0 ≤ X by linarith)
      (show 0 ≤ Y by linarith)]
  have hPinv : P⁻¹ ≤ 1 := (inv_le_one₀ hP0).2 hP
  have hSumInv : (X + Y)⁻¹ ≤ 1 :=
    (inv_le_one₀ hSum).2 (by linarith)
  have hQsqLe : Q ^ 2 ≤ X * Y := by
    rw [hQsq]
    calc
      P⁻¹ * (X + Y)⁻¹ * (X * Y) ≤ 1 * 1 * (X * Y) := by gcongr
      _ = X * Y := by ring
  have hQle : Q ≤ X * Y := by
    nlinarith [sq_nonneg (Q - X * Y)]
  have hQeps : Q ^ ε ≤ (X * Y) ^ ε :=
    Real.rpow_le_rpow hQ.le hQle hε
  have hFirst0 := dfiEquation30_first_optimized_le
    ha hb hP hX hY hQ hQsq
  have hSecond0 := dfiEquation30_second_optimized_eq
    hP0 hX0 hY0 hQ hQsq
  have hTargetFactor :
      (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε =
        dfiTheorem1ErrorScale P X Y ε := by
    unfold dfiTheorem1ErrorScale
    calc
      _ = P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          ((X * Y) ^ (1 / 4 : ℝ) * (X * Y) ^ ε) := by ring
      _ = _ := by rw [← Real.rpow_add hXY]
  have hFirst :
      ((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) * Q ^ (-1 + ε) ≤
        dfiTheorem1ErrorScale P X Y ε := by
    rw [Real.rpow_add hQ]
    rw [show ((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) *
          (Q ^ (-(1 : ℝ)) * Q ^ ε) =
        (((a : ℝ) * b)⁻¹ * (X * Y) / (X + Y) *
          Q ^ (-(1 : ℝ))) * Q ^ ε by ring]
    calc
      _ ≤ (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε := by gcongr
      _ = _ := hTargetFactor
  have hSecond :
      (X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
          Q ^ (-(5 / 2 : ℝ) + ε) ≤
        dfiTheorem1ErrorScale P X Y ε := by
    rw [Real.rpow_add hQ]
    rw [show (X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
          (Q ^ (-(5 / 2 : ℝ)) * Q ^ ε) =
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
          Q ^ (-(5 / 2 : ℝ))) * Q ^ ε by ring,
      hSecond0]
    calc
      _ ≤ (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 : ℝ)) * (X * Y) ^ ε := by gcongr
      _ = _ := hTargetFactor
  unfold dfiEquation30PreoptimizedError
  linarith

/-- The geometric core of the retained first-variable Voronoi range.  Once
`Q^2 = P^-1 (X+Y)^-1 XY` is imposed, the apparent `Q^(-3/2)` term gains the
extra inverse power of `Q` occurring in the second error on the last line of
DFI (30).  The factor `sqrt 2` is the uniform cost of not ordering `X,Y`. -/
theorem dfiEquation29_xRetained_core_le_secondErrorCore
    {P X Y Q : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    X ^ (1 / 2 : ℝ) * min X Y * Q ≤
      Real.sqrt 2 * ((X * Y) ^ (3 / 2 : ℝ) / (X + Y)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have hSum : 0 < X + Y := add_pos hX0 hY0
  have hPinv : P⁻¹ ≤ 1 := (inv_le_one₀ hP0).2 hP
  have hQsqScale : Q ^ 2 * (X + Y) ≤ X * Y := by
    rw [hQsq]
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hPinv) hXY.le]
  have hXhalfSq : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hX0.le]
  have hXYhalfSq : ((X * Y) ^ (1 / 2 : ℝ)) ^ 2 = X * Y := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hXY.le]
  have hTwoSqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hThreeHalf : (X * Y) ^ (3 / 2 : ℝ) =
      (X * Y) * (X * Y) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      Real.rpow_add hXY, Real.rpow_one]
  have hMinNonneg : 0 ≤ min X Y := le_min hX0.le hY0.le
  have hLeftNonneg : 0 ≤
      X ^ (1 / 2 : ℝ) * min X Y * Q * (X + Y) := by positivity
  have hRightNonneg : 0 ≤
      Real.sqrt 2 * (X * Y) ^ (3 / 2 : ℝ) := by positivity
  have hLeftSq :
      (X ^ (1 / 2 : ℝ) * min X Y * Q * (X + Y)) ^ 2 =
        X * (min X Y) ^ 2 * Q ^ 2 * (X + Y) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hXhalfSq]
  have hRightSq :
      (Real.sqrt 2 * (X * Y) ^ (3 / 2 : ℝ)) ^ 2 =
        2 * (X * Y) ^ 3 := by
    rw [mul_pow, hTwoSqrtSq, hThreeHalf, mul_pow, hXYhalfSq]
    ring
  have hSq :
      (X ^ (1 / 2 : ℝ) * min X Y * Q * (X + Y)) ^ 2 ≤
        (Real.sqrt 2 * (X * Y) ^ (3 / 2 : ℝ)) ^ 2 := by
    rw [hLeftSq, hRightSq]
    by_cases hXYord : X ≤ Y
    · rw [min_eq_left hXYord]
      have hsum : X + Y ≤ 2 * Y := by linarith
      calc
        X * X ^ 2 * Q ^ 2 * (X + Y) ^ 2 =
            (X * X ^ 2 * (X + Y)) * (Q ^ 2 * (X + Y)) := by ring
        _ ≤ (X * X ^ 2 * (X + Y)) * (X * Y) := by gcongr
        _ ≤ (X * X ^ 2 * (2 * Y)) * (X * Y) := by gcongr
        _ ≤ 2 * (X * Y) ^ 3 := by
          have hmono : X ^ 3 * Y ^ 2 * X ≤ X ^ 3 * Y ^ 2 * Y :=
            mul_le_mul_of_nonneg_left hXYord
              (mul_nonneg (pow_nonneg hX0.le 3) (pow_nonneg hY0.le 2))
          nlinarith
    · have hYXord : Y ≤ X := le_of_not_ge hXYord
      rw [min_eq_right hYXord]
      have hsum : X + Y ≤ 2 * X := by linarith
      calc
        X * Y ^ 2 * Q ^ 2 * (X + Y) ^ 2 =
            (X * Y ^ 2 * (X + Y)) * (Q ^ 2 * (X + Y)) := by ring
        _ ≤ (X * Y ^ 2 * (X + Y)) * (X * Y) := by gcongr
        _ ≤ (X * Y ^ 2 * (2 * X)) * (X * Y) := by gcongr
        _ = 2 * (X * Y) ^ 3 := by ring
  have hCore :
      X ^ (1 / 2 : ℝ) * min X Y * Q * (X + Y) ≤
        Real.sqrt 2 * (X * Y) ^ (3 / 2 : ℝ) := by
    nlinarith [sq_nonneg
      (X ^ (1 / 2 : ℝ) * min X Y * Q * (X + Y) -
        Real.sqrt 2 * (X * Y) ^ (3 / 2 : ℝ))]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hSum).2
  simpa [mul_assoc] using hCore

/-- Symmetric geometric core for the retained second-variable range. -/
theorem dfiEquation29_yRetained_core_le_secondErrorCore
    {P X Y Q : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    Y ^ (1 / 2 : ℝ) * min X Y * Q ≤
      Real.sqrt 2 * ((X * Y) ^ (3 / 2 : ℝ) / (X + Y)) := by
  have hswap : Q ^ 2 = P⁻¹ * (Y + X)⁻¹ * (Y * X) := by
    simpa [add_comm, mul_comm] using hQsq
  calc
    Y ^ (1 / 2 : ℝ) * min X Y * Q =
        Y ^ (1 / 2 : ℝ) * min Y X * Q := by rw [min_comm]
    _ ≤ Real.sqrt 2 * ((Y * X) ^ (3 / 2 : ℝ) / (Y + X)) :=
      dfiEquation29_xRetained_core_le_secondErrorCore
        hP hY hX hQ hswap
    _ = _ := by rw [mul_comm Y X, add_comm Y X]

/-- First retained source window with its exact zero-epsilon powers in the
form used on the last line of DFI (30). -/
theorem dfiEquation29_xRetained_zeroEpsilon_le_secondError
    {P X Y Q : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y ≤
      Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ))) := by
  have hCore := dfiEquation29_xRetained_core_le_secondErrorCore
    hP hX hY hQ hQsq
  have hPow : Q * Q ^ (-(5 / 2 : ℝ)) = Q ^ (-(3 / 2 : ℝ)) := by
    calc
      Q * Q ^ (-(5 / 2 : ℝ)) =
          Q ^ (1 : ℝ) * Q ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = Q ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by rw [Real.rpow_add hQ]
      _ = Q ^ (-(3 / 2 : ℝ)) := by congr 1; ring
  have hNonneg : 0 ≤ Q ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hQ.le _
  have hScaled := mul_le_mul_of_nonneg_right hCore hNonneg
  rw [show
      (X ^ (1 / 2 : ℝ) * min X Y * Q) * Q ^ (-(5 / 2 : ℝ)) =
        X ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y by
      rw [← hPow]; ring,
    show
      (Real.sqrt 2 * ((X * Y) ^ (3 / 2 : ℝ) / (X + Y))) *
          Q ^ (-(5 / 2 : ℝ)) =
        Real.sqrt 2 *
          ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) *
            Q ^ (-(5 / 2 : ℝ))) by ring] at hScaled
  exact hScaled

/-- Symmetric zero-epsilon retained source window. -/
theorem dfiEquation29_yRetained_zeroEpsilon_le_secondError
    {P X Y Q : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 0 < Q)
    (hQsq : Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y)) :
    Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y ≤
      Real.sqrt 2 *
        ((X * Y) ^ (3 / 2 : ℝ) / (X + Y) * Q ^ (-(5 / 2 : ℝ))) := by
  have hswap : Q ^ 2 = P⁻¹ * (Y + X)⁻¹ * (Y * X) := by
    simpa [add_comm, mul_comm] using hQsq
  calc
    Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min X Y =
        Y ^ (1 / 2 : ℝ) * Q ^ (-(3 / 2 : ℝ)) * min Y X := by rw [min_comm]
    _ ≤ Real.sqrt 2 *
        ((Y * X) ^ (3 / 2 : ℝ) / (Y + X) * Q ^ (-(5 / 2 : ℝ))) :=
      dfiEquation29_xRetained_zeroEpsilon_le_secondError
        hP hY hX hQ hswap
    _ = _ := by rw [mul_comm Y X, add_comm Y X]

/-- A quotient of two positive source scales whose denominator is at most
twice the numerator has logarithm bounded by the common dyadic logarithm.
This is the elementary logarithmic step used in DFI (29). -/
theorem abs_log_div_le_two_log_two_mul
    {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hvu : v ≤ 2 * u) :
    |Real.log (u / v)| ≤ 2 * Real.log (2 * u) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have h2u0 : 0 < 2 * u := mul_pos (by norm_num) hu0
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg hv
  have hlogu : Real.log u ≤ Real.log (2 * u) :=
    Real.strictMonoOn_log.monotoneOn hu0 h2u0 (by linarith)
  have hlogv : Real.log v ≤ Real.log (2 * u) :=
    Real.strictMonoOn_log.monotoneOn hv0 h2u0 hvu
  rw [Real.log_div hu0.ne' hv0.ne']
  calc
    |Real.log u - Real.log v| ≤ |Real.log u| + |Real.log v| := abs_sub _ _
    _ = Real.log u + Real.log v := by
      rw [abs_of_nonneg hlogu0, abs_of_nonneg hlogv0]
    _ ≤ 2 * Real.log (2 * u) := by linarith

/-- All logarithms in the retained first-variable branch cost one arbitrary
positive power of the common physical scale `XY`, uniformly in the source
coefficient `b` and the optimized modulus scale. -/
theorem dfiEquation29XSingleLogMajorant_le_rpow
    {X Y Q δ : ℝ} {b : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (hb : 0 < b) (hbY : (b : ℝ) ≤ 2 * Y) (hδ : 0 < δ) :
    dfiEquation29XSingleLogMajorant Q Y b ≤
      (8 * Real.log 2 + 6 * δ⁻¹ +
        2 * |Real.eulerMascheroniConstant|) * (X * Y) ^ δ := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hXY1 : 1 ≤ X * Y := by nlinarith
  have hYXY : Y ≤ X * Y := by nlinarith
  have hlogY := abs_log_div_le_two_log_two_mul hY hbR hbY
  have hlog2Y := abs_log_div_le_two_log_two_mul
    (show 1 ≤ 2 * Y by nlinarith) hbR (by linarith : (b : ℝ) ≤ 2 * (2 * Y))
  have hlog2YXY : Real.log (2 * Y) ≤ Real.log (2 * (X * Y)) :=
    Real.strictMonoOn_log.monotoneOn (mul_pos (by norm_num) hY0)
      (mul_pos (by norm_num) hXY0) (by nlinarith)
  have hlog4YXY : Real.log (2 * (2 * Y)) ≤ Real.log (4 * (X * Y)) :=
    Real.strictMonoOn_log.monotoneOn
      (by positivity : 0 < 2 * (2 * Y))
      (by positivity : 0 < 4 * (X * Y)) (by nlinarith)
  have hlog2QXY : Real.log (2 * Q) ≤ Real.log (2 * (X * Y)) :=
    Real.strictMonoOn_log.monotoneOn (mul_pos (by norm_num) hQ0)
      (mul_pos (by norm_num) hXY0) (by nlinarith)
  have hlogSplit : Real.log (2 * (X * Y)) =
      Real.log 2 + Real.log (X * Y) := by
    rw [Real.log_mul (by norm_num) hXY0.ne']
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogFourSplit : Real.log (4 * (X * Y)) =
      2 * Real.log 2 + Real.log (X * Y) := by
    rw [Real.log_mul (by norm_num) hXY0.ne']
    rw [hlogFour]
  have hlogPower := Real.log_le_rpow_div hXY0.le hδ
  have hpowOne : 1 ≤ (X * Y) ^ δ := Real.one_le_rpow hXY1 hδ.le
  have hδinv : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold dfiEquation29XSingleLogMajorant
  calc
    |Real.log (Y / b)| + |Real.log (2 * Y / b)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) ≤
      4 * Real.log (2 * (X * Y)) + 2 * Real.log (4 * (X * Y)) +
        2 * |Real.eulerMascheroniConstant| := by linarith
    _ = 8 * Real.log 2 + 6 * Real.log (X * Y) +
        2 * |Real.eulerMascheroniConstant| := by
      rw [hlogSplit, hlogFourSplit]
      ring
    _ ≤ (8 * Real.log 2 + 6 * δ⁻¹ +
          2 * |Real.eulerMascheroniConstant|) * (X * Y) ^ δ := by
      rw [div_eq_mul_inv] at hlogPower
      nlinarith [mul_nonneg hδinv (Real.rpow_nonneg hXY0.le δ),
        abs_nonneg Real.eulerMascheroniConstant]

/-- Symmetric logarithmic absorption for the retained second-variable
branch. -/
theorem dfiEquation29YSingleLogMajorant_le_rpow
    {X Y Q δ : ℝ} {a : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hQXY : Q ≤ X * Y)
    (ha : 0 < a) (haX : (a : ℝ) ≤ 2 * X) (hδ : 0 < δ) :
    dfiEquation29YSingleLogMajorant Q X a ≤
      (8 * Real.log 2 + 6 * δ⁻¹ +
        2 * |Real.eulerMascheroniConstant|) * (X * Y) ^ δ := by
  have h := dfiEquation29XSingleLogMajorant_le_rpow
    hY hX hQ (by simpa [mul_comm] using hQXY) ha haX hδ
  simpa [mul_comm] using h

/-- The natural modulus endpoint in equation (22) is at most `3Q` once
`Q ≥ 1`; this removes all ceiling artefacts before epsilon absorption. -/
theorem natCeil_two_mul_le_three_mul {Q : ℝ} (hQ : 1 ≤ Q) :
    (⌈2 * Q⌉₊ : ℝ) ≤ 3 * Q := by
  have hceil : (⌈2 * Q⌉₊ : ℝ) < 2 * Q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

/-- A reusable square-root absorption lemma.  It keeps the square-root
structure of the two gcd averages rather than discarding it and thereby
losing an additional epsilon power. -/
theorem sqrt_mul_le_sqrt_mul_mul
    {u v A B Z : ℝ} (hv : 0 ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (huA : u ≤ A * Z) (hvB : v ≤ B * Z) :
    Real.sqrt (u * v) ≤ Real.sqrt (A * B) * Z := by
  have huv : u * v ≤ (A * Z) * (B * Z) :=
    mul_le_mul huA hvB hv (mul_nonneg hA hZ)
  calc
    Real.sqrt (u * v) ≤ Real.sqrt ((A * Z) * (B * Z)) :=
      Real.sqrt_le_sqrt huv
    _ = Real.sqrt ((A * B) * Z ^ 2) := by congr 1; ring
    _ = Real.sqrt (A * B) * Real.sqrt (Z ^ 2) := by
      rw [Real.sqrt_mul (mul_nonneg hA hB)]
    _ = Real.sqrt (A * B) * Z := by rw [Real.sqrt_sq hZ]

/-- Uniform epsilon absorption of the two normalized gcd averages in either
one-sided equation-(29) branch.  The hypotheses `H ≤ 4XY` and `A ≤ 2XY`
are exactly the support bounds later supplied by a nonempty shifted divisor
configuration. -/
theorem dfiEquation29_twoGcdAverageLoss_le_rpow
    {X Y Q δ : ℝ} {H A : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hQXY : Q ≤ X * Y)
    (hH : H ≠ 0) (hA : A ≠ 0)
    (hHXY : (H : ℝ) ≤ 4 * (X * Y))
    (hAXY : (A : ℝ) ≤ 2 * (X * Y)) (hδ : 0 < δ) :
    divisorEpsilonConstant δ * max 1 ((⌈2 * Q⌉₊ : ℝ) ^ δ) *
        (Real.sqrt ((H.divisors.card : ℝ) *
            (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
          Real.sqrt ((A.divisors.card : ℝ) *
            (((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ)))) ≤
      (divisorEpsilonConstant δ * 3 ^ δ *
          Real.sqrt ((divisorEpsilonConstant δ * 4 ^ δ) *
            ((1 + δ⁻¹) * 3 ^ δ)) *
          Real.sqrt ((divisorEpsilonConstant δ * 2 ^ δ) *
            ((1 + δ⁻¹) * 3 ^ δ))) *
        ((X * Y) ^ δ) ^ 3 := by
  let S : ℝ := X * Y
  let L : ℕ := ⌈2 * Q⌉₊
  let Z : ℝ := S ^ δ
  let D : ℝ := divisorEpsilonConstant δ
  let K : ℝ := 1 + δ⁻¹
  let CL : ℝ := 3 ^ δ
  let CH : ℝ := D * 4 ^ δ
  let CA : ℝ := D * 2 ^ δ
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; exact (divisorEpsilonConstant_pos δ).le
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hCL0 : 0 ≤ CL := by dsimp [CL]; positivity
  have hCH0 : 0 ≤ CH := by
    dsimp [CH]
    positivity
  have hCA0 : 0 ≤ CA := by
    dsimp [CA]
    positivity
  have hLlower : 2 * Q ≤ (L : ℝ) := by
    dsimp only [L]
    exact Nat.le_ceil _
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hLpos.ne')
  have hLupper : (L : ℝ) ≤ 3 * S := by
    calc
      (L : ℝ) ≤ 3 * Q := by
        dsimp only [L]
        exact natCeil_two_mul_le_three_mul hQ
      _ ≤ 3 * S := by gcongr
  have hLpow : (L : ℝ) ^ δ ≤ CL * Z := by
    have := Real.rpow_le_rpow (Nat.cast_nonneg L) hLupper hδ.le
    calc
      (L : ℝ) ^ δ ≤ (3 * S) ^ δ := this
      _ = CL * Z := by
        dsimp [CL, Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hMax : max 1 ((L : ℝ) ^ δ) = (L : ℝ) ^ δ := by
    rw [max_eq_right]
    exact Real.one_le_rpow hLone hδ.le
  have hHpow : (H : ℝ) ^ δ ≤ 4 ^ δ * Z := by
    have := Real.rpow_le_rpow (Nat.cast_nonneg H) hHXY hδ.le
    calc
      (H : ℝ) ^ δ ≤ (4 * S) ^ δ := this
      _ = 4 ^ δ * Z := by
        dsimp [Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hApow : (A : ℝ) ^ δ ≤ 2 ^ δ * Z := by
    have := Real.rpow_le_rpow (Nat.cast_nonneg A) hAXY hδ.le
    calc
      (A : ℝ) ^ δ ≤ (2 * S) ^ δ := this
      _ = 2 ^ δ * Z := by
        dsimp [Z]
        rw [Real.mul_rpow (by norm_num) hS0.le]
  have hHcard : (H.divisors.card : ℝ) ≤ CH * Z := by
    calc
      (H.divisors.card : ℝ) ≤ D * (H : ℝ) ^ δ := by
        simpa only [D] using card_divisors_le_const_mul_rpow hδ hH
      _ ≤ D * (4 ^ δ * Z) := by gcongr
      _ = CH * Z := by dsimp [CH]; ring
  have hAcard : (A.divisors.card : ℝ) ≤ CA * Z := by
    calc
      (A.divisors.card : ℝ) ≤ D * (A : ℝ) ^ δ := by
        simpa only [D] using card_divisors_le_const_mul_rpow hδ hA
      _ ≤ D * (2 ^ δ * Z) := by gcongr
      _ = CA * Z := by dsimp [CA]; ring
  have hHarm : (((harmonic L : ℚ) : ℝ)) ≤ (K * CL) * Z := by
    calc
      (((harmonic L : ℚ) : ℝ)) ≤ K * max 1 ((L : ℝ) ^ δ) := by
        simpa only [K] using harmonic_le_epsilon_rpow hδ L
      _ = K * (L : ℝ) ^ δ := by rw [hMax]
      _ ≤ K * (CL * Z) := by gcongr
      _ = (K * CL) * Z := by ring
  have hHarm0 : 0 ≤ (((harmonic L : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos hLpos.ne').le
  have hHsqrt :
      Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) ≤
        Real.sqrt (CH * (K * CL)) * Z :=
    sqrt_mul_le_sqrt_mul_mul hHarm0 hCH0 (mul_nonneg hK0 hCL0) hZ0
      hHcard hHarm
  have hAsqrt :
      Real.sqrt ((A.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) ≤
        Real.sqrt (CA * (K * CL)) * Z :=
    sqrt_mul_le_sqrt_mul_mul hHarm0 hCA0 (mul_nonneg hK0 hCL0) hZ0
      hAcard hHarm
  change D * max 1 ((L : ℝ) ^ δ) *
      (Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) *
        Real.sqrt ((A.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ)))) ≤ _
  rw [hMax]
  calc
    D * (L : ℝ) ^ δ *
        (Real.sqrt ((H.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ))) *
          Real.sqrt ((A.divisors.card : ℝ) * (((harmonic L : ℚ) : ℝ)))) ≤
      D * (CL * Z) *
        ((Real.sqrt (CH * (K * CL)) * Z) *
          (Real.sqrt (CA * (K * CL)) * Z)) := by gcongr
    _ = (D * CL * Real.sqrt (CH * (K * CL)) *
          Real.sqrt (CA * (K * CL))) * Z ^ 3 := by ring
    _ = _ := by dsimp [D, K, CL, CH, CA, Z, S]

/-- Exact equations-(22)--(30) assembly before any power absorption.  The
distance from the source shifted-divisor sum to DFI's infinite central
series is bounded by the concrete main-branch discrepancy and the six
disjoint retained/tail regions of equation (29).  In particular, every
quantity on the right is computed from the source weight; no error
certificate or transformed-sum hypothesis is present. -/
theorem norm_dfiDyadicShiftedDivisorSum_sub_sourceCentralSeries_le_equation29_parts
    {Q U P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N h : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) (ε : ℝ) :
    ‖dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) -
        dfiEquation27CentralSeries a b h f‖ ≤
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) := by
  have hSource := norm_dfiDyadicShiftedDivisorSum_sub_sourceCentralSeries_le
    w hf hbox hφ hQU a b M N h ha hb hM hN
  have hError :
      ‖∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24ErrorTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)‖ ≤
        ∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24WeilMassTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q) := by
    simpa only [Int.cast_natCast] using
      (norm_sum_dfiEquation24ErrorTotal_le_weil_masses
        w hf hbox hφ a b ha hb (h : ℤ))
  have hPartition :
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24WeilMassTotal q a b (h : ℤ)
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b (h : ℤ) q)) =
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleRetainedWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29XSingleTailWeilTotal X w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleRetainedWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29YSingleTailWeilTotal Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleRetainedWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation29DoubleTailWeilTotal X Y w
          (dfiLocalizedWeight f φ h) a b h ε q) := by
    simp_rw [dfiEquation24WeilMassTotal_eq_equation29_parts
      X Y w (dfiLocalizedWeight f φ h) a b _ (h : ℤ) ε]
    simp only [Finset.sum_add_distrib]
  calc
    _ ≤ ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      ‖∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24ErrorTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)‖ := hSource
    _ ≤ ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h)‖ +
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24WeilMassTotal q a b (h : ℤ)
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b (h : ℤ) q)) := add_le_add le_rfl hError
    _ = _ := by rw [hPartition]; ring

/-! ## Signed shifts

DFI Theorem 1 is stated for every nonzero integer shift, whereas equations
(22)--(30) above use a positive natural shift while the divisor variables
are kept in their source order.  The following definitions and exact
identity provide the required negative-shift entry: interchange the two
divisor variables and negate the shift.  This is an equality of the actual
finite shifted-divisor sums, not an estimate or an assumed symmetry.
-/

/-- Interchange the two coordinates of a DFI test weight. -/
noncomputable def dfiSwapWeight (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y ↦ f y x

/-- Exact signed-shift symmetry of the source sum. -/
theorem dfiDyadicShiftedDivisorSum_swap
    (f : ℝ → ℝ → ℂ) (a b M N : ℕ) (h : ℤ) :
    dfiDyadicShiftedDivisorSum f a b M N h =
      dfiDyadicShiftedDivisorSum (dfiSwapWeight f) b a N M (-h) := by
  unfold dfiDyadicShiftedDivisorSum dfiSwapWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hshift : quadraticDivisorShift b a n m =
      -quadraticDivisorShift a b m n := by
    unfold quadraticDivisorShift
    push_cast
    ring
  rw [hshift]
  by_cases hs : quadraticDivisorShift a b m n = h
  · rw [if_pos hs, if_pos]
    · ring
    · rw [hs]
  · rw [if_neg hs, if_neg]
    intro hn
    apply hs
    have hneg := congrArg Neg.neg hn
    simpa using hneg

/-- The equation-(3) main series with the same signed-shift convention as
the finite source sum.  The negative branch is the positive series after
the exact coordinate swap above. -/
noncomputable def dfiSignedCentralSeries
    (a b : ℕ) (h : ℤ) (f : ℝ → ℝ → ℂ) : ℂ :=
  if 0 ≤ h then dfiEquation27CentralSeries a b h.toNat f
  else dfiEquation27CentralSeries b a (-h).toNat (dfiSwapWeight f)

@[simp]
theorem dfiSignedCentralSeries_ofNat
    (a b h : ℕ) (f : ℝ → ℝ → ℂ) :
    dfiSignedCentralSeries a b (h : ℤ) f =
      dfiEquation27CentralSeries a b h f := by
  simp [dfiSignedCentralSeries]

theorem dfiSignedCentralSeries_neg_ofNat
    (a b h : ℕ) (hh : 0 < h) (f : ℝ → ℝ → ℂ) :
    dfiSignedCentralSeries a b (-(h : ℤ)) f =
      dfiEquation27CentralSeries b a h (dfiSwapWeight f) := by
  simp [dfiSignedCentralSeries, hh.ne']

end RiemannZeta.GuthMaynard
