import GafniTao.FordLemma34BackwardComposition

/-!
# Ford Lemma 3.4: real-power algebra in the raw-bound absorption

This file isolates the positivity and square-root identities used to turn
the literal output of Lemmas 3.2 and 3.3 into Ford's backward `E_J`
recurrence.  Keeping these identities separate makes the final induction
consumer both source-readable and elaboration-stable.
-/

namespace GafniTao

noncomputable section

/-- Every entry of a source `E` schedule between the active index and the
terminal index is at least one. -/
theorem FordESchedule.one_le
    {s k j : ℕ} {eta : ℝ} (Esch : FordESchedule s k j eta)
    (hk : 1 ≤ k) (heta : 1 ≤ eta) :
    ∀ J, J < j → 1 ≤ Esch.E J := by
  intro J hJj
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hJle : J ≤ j - 1 := by omega
  refine Nat.decreasingInduction (motive := fun J _ => 1 ≤ Esch.E J) ?_ ?_ hJle
  · intro d hd ih
    have hd1 : 1 ≤ d + 1 := by omega
    have hdj : d + 1 < j := by omega
    rw [show d = (d + 1) - 1 by omega, Esch.recurrence (d + 1) hd1 hdj]
    have hstep : 0 ≤ fordEStepExponent s k (d + 1) := by
      unfold fordEStepExponent
      have hkdiff : 0 ≤ (k : ℝ) ^ 2 - k := by
        nlinarith
      have hddiff : 0 ≤ ((d + 1 : ℕ) : ℝ) ^ 2 - (d + 1 : ℕ) := by
        push_cast
        nlinarith
      have hs : 0 ≤ (s : ℝ) := by positivity
      linarith
    have hkpow : 1 ≤ (k : ℝ) ^ k := one_le_pow₀ hkR
    have hetapow : 1 ≤ eta ^ fordEStepExponent s k (d + 1) :=
      Real.one_le_rpow heta hstep
    have hsqrt : 1 ≤ √(Esch.E (d + 1)) := by
      simpa using Real.sqrt_le_sqrt ih
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hkpow hetapow) hsqrt
  · dsimp
    rw [Esch.terminal]

/-- Square roots commute with real powers of a nonnegative base, with the
exponent divided by two. -/
theorem ford_sqrt_rpow
    {x a : ℝ} (hx : 0 ≤ x) :
    √(x ^ a) = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The natural-power specialization of `ford_sqrt_rpow`. -/
theorem ford_sqrt_nat_pow
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    √(x ^ n) = x ^ ((n : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact ford_sqrt_rpow hx

/-- Ford's numeric coefficient has the displayed square root
`2 sqrt(k^3 k!)`. -/
theorem ford_lemma_3_4_sqrt_numeric_factor (k : ℕ) :
    √(((4 * k ^ 3 * k.factorial : ℕ) : ℝ)) =
      2 * √((k : ℝ) ^ 3 * k.factorial) := by
  push_cast
  rw [show (4 : ℝ) * (k : ℝ) ^ 3 * k.factorial =
      4 * ((k : ℝ) ^ 3 * k.factorial) by ring,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
  norm_num

/-- The square root of the product occurring in the off-diagonal branch,
with the repeated moment coefficient exposed as a single factor. -/
theorem ford_sqrt_repeated_coefficient_product
    {A B E P Q Qnext C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hQnext : 0 ≤ Qnext)
    (hC : 0 ≤ C) :
    √((C * Q) * (A * B * (E * C * P * Qnext))) =
      √A * √B * √E * C * √P * √Q * √Qnext := by
  rw [show (C * Q) * (A * B * (E * C * P * Qnext)) =
      A * (B * (E * (P * (Q * (Qnext * C ^ 2))))) by ring]
  rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_mul hE,
    Real.sqrt_mul hP, Real.sqrt_mul hQ, Real.sqrt_mul hQnext,
    Real.sqrt_sq hC]
  ring

/-- A prime from the canonical packet supplies exactly the negative-power
factor used in Ford's cancellation. -/
theorem ford_prime_inverse_power_le_scale
    {P phi : ℝ} {p r k : ℕ}
    (hP : 0 < P) (hp : P ^ phi < p) :
    ((p : ℝ) ^ (r * k))⁻¹ ≤
      P ^ (-(r : ℝ) * k * phi) := by
  have hpR : 0 < (p : ℝ) := (Real.rpow_pos_of_pos hP phi).trans hp
  have hscale : 0 < P ^ phi := Real.rpow_pos_of_pos hP _
  have hz : -((r * k : ℕ) : ℝ) ≤ 0 :=
    neg_nonpos.mpr (Nat.cast_nonneg _)
  have hmono := Real.rpow_le_rpow_of_nonpos hscale hp.le hz
  rw [Real.rpow_neg (show 0 ≤ (p : ℝ) by positivity),
    Real.rpow_natCast] at hmono
  rw [← Real.rpow_mul hP.le] at hmono
  have hexp : phi * -((r * k : ℕ) : ℝ) =
      -(r : ℝ) * k * phi := by
    push_cast
    ring
  rw [hexp] at hmono
  exact hmono

/-- Replacing the integral Lemma-3.2 exponent by Ford's displayed real
exponent is monotone because the inflated prime scale is at least one. -/
theorem ford_prime_scale_exponent_inflation
    {eta M eReal : ℝ} {e : ℕ}
    (heta : 1 ≤ eta) (hM : 1 ≤ M) (he : (e : ℝ) ≤ eReal) :
    (eta * M) ^ e ≤ eta ^ eReal * M ^ eReal := by
  have hbase : 1 ≤ eta * M :=
    one_le_mul_of_one_le_of_one_le heta hM
  calc
    (eta * M) ^ e = (eta * M) ^ (e : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (eta * M) ^ eReal :=
      Real.rpow_le_rpow_of_exponent_le hbase he
    _ = eta ^ eReal * M ^ eReal :=
      Real.mul_rpow (zero_le_one.trans heta) (zero_le_one.trans hM)

/-- The two half-powers of consecutive `Q` scales expose the factor
`M^(-lambda/2)` which participates in Ford's exact cancellation. -/
theorem ford_consecutive_Q_half_powers
    {M Q Qnext lambda : ℝ}
    (hM : 0 < M) (hQnext : 0 < Qnext)
    (hQ : Q = M * Qnext) :
    Q ^ (lambda / 2) * Qnext ^ (lambda / 2) =
      Q ^ lambda * M ^ (-lambda / 2) := by
  subst Q
  rw [Real.mul_rpow hM.le hQnext.le,
    Real.mul_rpow hM.le hQnext.le]
  rw [show M ^ (lambda / 2) * Qnext ^ (lambda / 2) *
        Qnext ^ (lambda / 2) =
      M ^ (lambda / 2) *
        (Qnext ^ (lambda / 2) * Qnext ^ (lambda / 2)) by ring,
    ← Real.rpow_add hQnext]
  rw [show M ^ lambda * Qnext ^ lambda * M ^ (-lambda / 2) =
      (M ^ lambda * M ^ (-lambda / 2)) * Qnext ^ lambda by ring,
    ← Real.rpow_add hM]
  congr 1 <;> ring

/-- The square root of the integral prime-scale factor is controlled by the
half of Ford's real exponent. -/
theorem ford_sqrt_prime_scale_exponent_inflation
    {eta M eReal : ℝ} {e : ℕ}
    (heta : 1 ≤ eta) (hM : 1 ≤ M) (he : (e : ℝ) ≤ eReal) :
    √((eta * M) ^ e) ≤
      eta ^ (eReal / 2) * M ^ (eReal / 2) := by
  have hinflate := ford_prime_scale_exponent_inflation heta hM he
  calc
    √((eta * M) ^ e) ≤ √(eta ^ eReal * M ^ eReal) :=
      Real.sqrt_le_sqrt hinflate
    _ = √(eta ^ eReal) * √(M ^ eReal) :=
      Real.sqrt_mul (Real.rpow_nonneg (zero_le_one.trans heta) _) _
    _ = eta ^ (eReal / 2) * M ^ (eReal / 2) := by
      rw [ford_sqrt_rpow (zero_le_one.trans heta),
        ford_sqrt_rpow (zero_le_one.trans hM)]

/-- The real exponent contributed by Lemma 3.2 is bounded by the exponent
in the `E_J` recurrence once `r ≤ k`. -/
theorem ford_lemma_3_4_eta_exponent_le
    {s k r J : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    (2 * (s : ℝ) +
        ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2 ≤
      fordEStepExponent s k J := by
  unfold fordEStepExponent
  have hpred := ford_square_pred_mono hrk
  have hreal : (r : ℝ) ^ 2 - r ≤ (k : ℝ) ^ 2 - k := by
    calc
      (r : ℝ) ^ 2 - r = ((r * (r - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub hr]
        ring
      _ ≤ ((k * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hpred
      _ = (k : ℝ) ^ 2 - k := by
        rw [Nat.cast_mul, Nat.cast_sub (hr.trans hrk)]
        ring
  linarith

/-- The negative packet-prime power, the `P^(k/2)` factor, and the two
`M_{J+1}` powers cancel exactly by Ford's `phi` recurrence. -/
theorem ford_lemma_3_4_expanded_scale_cancellation
    {s k r J : ℕ} {P delta phiJ phiNext : ℝ}
    (hP : 0 < P) (hk : 0 < k) (hr : 0 < r)
    (hphi : phiJ = fordPhiStep k r J delta phiNext) :
    P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
        (P ^ phiNext) ^
          ((2 * (s : ℝ) +
            ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2) *
        (P ^ phiNext) ^ (-fordLambda34 s k delta / 2) = 1 := by
  rw [← Real.rpow_add hP]
  rw [show P ^ (-(r : ℝ) * k * phiJ + (k : ℝ) / 2) *
          (P ^ phiNext) ^
            ((2 * (s : ℝ) +
              ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2) *
          (P ^ phiNext) ^ (-fordLambda34 s k delta / 2) =
        P ^ (-(r : ℝ) * k * phiJ + (k : ℝ) / 2) *
          ((P ^ phiNext) ^
            ((2 * (s : ℝ) +
              ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2) *
           (P ^ phiNext) ^ (-fordLambda34 s k delta / 2)) by ring,
    ← Real.rpow_add (Real.rpow_pos_of_pos hP phiNext)]
  have hcancel := ford_lemma_3_4_scale_cancellation
    (s := s) (k := k) (r := r) (J := J) hP hk hr hphi
  have hPexp : -(r : ℝ) * k * phiJ + (k : ℝ) / 2 =
      (k : ℝ) / 2 - (k : ℝ) * r * phiJ := by ring
  have hMexp :
      (2 * (s : ℝ) +
          ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2 +
          -fordLambda34 s k delta / 2 =
        (s : ℝ) - fordLambda34 s k delta / 2 +
          ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 4 := by ring
  rw [hPexp, hMexp]
  exact hcancel

/-- Ford's complete normalized estimate for the off-diagonal alternative in
the maximum returned by Lemma 3.3.  All scales in this statement are the
literal consecutive scales from equation (3.10). -/
theorem ford_lemma_3_4_off_diagonal_normalized
    {s k r J p : ℕ} {C delta P eta M Q Qnext E phiJ phiNext : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k) (hJs : J ≤ s)
    (hJr : J < r) (hP : 1 ≤ P) (heta : 1 ≤ eta) (hM : 1 ≤ M)
    (hQnext : 0 < Qnext) (hMdef : M = P ^ phiNext) (hQ : Q = M * Qnext)
    (hp : P ^ phiJ < p)
    (hphi : phiJ = fordPhiStep k r J delta phiNext)
    (hC : 1 ≤ C) (hE : 1 ≤ E) :
    2 * ((p : ℝ) ^ (r * k))⁻¹ *
        √(fordLemma34JBound s k C delta Q *
          fordLemma34KBound s k r J C delta P eta M Qnext E) ≤
      4 * √((k : ℝ) ^ 3 * k.factorial) * √E *
        eta ^ fordEStepExponent s k J *
          fordLemma34JBound s k C delta Q := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  let eReal : ℝ :=
    2 * (s : ℝ) +
      ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2
  have he : (fordLemma34PrimeExponent s J r : ℝ) ≤ eReal :=
    fordLemma34PrimeExponent_cast_le_source hJs hJr
  have hinv : ((p : ℝ) ^ (r * k))⁻¹ ≤
      P ^ (-(r : ℝ) * k * phiJ) :=
    ford_prime_inverse_power_le_scale hP0 hp
  have hscaleSqrt : √((eta * M) ^ fordLemma34PrimeExponent s J r) ≤
      eta ^ (eReal / 2) * M ^ (eReal / 2) :=
    ford_sqrt_prime_scale_exponent_inflation heta hM he
  have hetaExp : eta ^ (eReal / 2) ≤
      eta ^ fordEStepExponent s k J :=
    Real.rpow_le_rpow_of_exponent_le heta
      (ford_lemma_3_4_eta_exponent_le hr hrk)
  have hcancel :
      P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
          M ^ (eReal / 2) * M ^ (-fordLambda34 s k delta / 2) = 1 := by
    rw [hMdef]
    exact ford_lemma_3_4_expanded_scale_cancellation hP0 hk hr hphi
  unfold fordLemma34JBound fordLemma34KBound fordLemma34LBound
  rw [ford_sqrt_repeated_coefficient_product
      (show 0 ≤ (((4 * k ^ 3 * k.factorial : ℕ) : ℝ)) by positivity)
      (show 0 ≤ (eta * M) ^ fordLemma34PrimeExponent s J r by positivity)
      (show 0 ≤ E by linarith)
      (show 0 ≤ P ^ k by positivity)
      (Real.rpow_nonneg hQ0.le _)
      (Real.rpow_nonneg hQnext.le _)
      (show 0 ≤ C by linarith),
    ford_lemma_3_4_sqrt_numeric_factor,
    ford_sqrt_nat_pow hP0.le,
    ford_sqrt_rpow hQ0.le,
    ford_sqrt_rpow hQnext.le]
  calc
    2 * ((p : ℝ) ^ (r * k))⁻¹ *
        (2 * √((k : ℝ) ^ 3 * k.factorial) *
          √((eta * M) ^ fordLemma34PrimeExponent s J r) * √E * C *
          P ^ ((k : ℝ) / 2) * Q ^ (fordLambda34 s k delta / 2) *
          Qnext ^ (fordLambda34 s k delta / 2)) ≤
      2 * P ^ (-(r : ℝ) * k * phiJ) *
        (2 * √((k : ℝ) ^ 3 * k.factorial) *
          (eta ^ (eReal / 2) * M ^ (eReal / 2)) * √E * C *
          P ^ ((k : ℝ) / 2) * Q ^ (fordLambda34 s k delta / 2) *
          Qnext ^ (fordLambda34 s k delta / 2)) := by
        gcongr
    _ = 4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
        eta ^ (eReal / 2) * Q ^ fordLambda34 s k delta *
          (P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
            M ^ (eReal / 2) * M ^ (-fordLambda34 s k delta / 2)) := by
        calc
          2 * P ^ (-(r : ℝ) * k * phiJ) *
              (2 * √((k : ℝ) ^ 3 * k.factorial) *
                (eta ^ (eReal / 2) * M ^ (eReal / 2)) * √E * C *
                P ^ ((k : ℝ) / 2) * Q ^ (fordLambda34 s k delta / 2) *
                Qnext ^ (fordLambda34 s k delta / 2)) =
            4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
              eta ^ (eReal / 2) *
              (Q ^ (fordLambda34 s k delta / 2) *
                Qnext ^ (fordLambda34 s k delta / 2)) *
              (P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
                M ^ (eReal / 2)) := by ring
          _ = 4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
              eta ^ (eReal / 2) *
              (Q ^ fordLambda34 s k delta *
                M ^ (-fordLambda34 s k delta / 2)) *
              (P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
                M ^ (eReal / 2)) := by
                  rw [ford_consecutive_Q_half_powers hM0 hQnext hQ]
          _ = 4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
              eta ^ (eReal / 2) * Q ^ fordLambda34 s k delta *
                (P ^ (-(r : ℝ) * k * phiJ) * P ^ ((k : ℝ) / 2) *
                  M ^ (eReal / 2) * M ^ (-fordLambda34 s k delta / 2)) := by ring
    _ = 4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
        eta ^ (eReal / 2) * Q ^ fordLambda34 s k delta := by rw [hcancel, mul_one]
    _ ≤ 4 * √((k : ℝ) ^ 3 * k.factorial) * √E * C *
        eta ^ fordEStepExponent s k J * Q ^ fordLambda34 s k delta := by
          gcongr
    _ = 4 * √((k : ℝ) ^ 3 * k.factorial) * √E *
        eta ^ fordEStepExponent s k J *
          (C * Q ^ fordLambda34 s k delta) := by ring

/-- The outer box cardinality contributes at most Ford's explicit
`2^k P^k` factor. -/
theorem ford_lemma_3_4_outer_box_bound
    {P : ℝ} {k : ℕ} (hP : 0 ≤ P) :
    (((2 * ⌊P⌋₊ : ℕ) : ℝ) ^ k) ≤ (2 : ℝ) ^ k * P ^ k := by
  have hfloor : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hP
  calc
    (((2 * ⌊P⌋₊ : ℕ) : ℝ) ^ k) =
        (2 * ((⌊P⌋₊ : ℕ) : ℝ)) ^ k := by push_cast; rfl
    _ ≤ (2 * P) ^ k := pow_le_pow_left₀ (by positivity) (by gcongr) k
    _ = (2 : ℝ) ^ k * P ^ k := mul_pow 2 P k

/-- The complete raw output of Lemmas 3.2 and 3.3 is absorbed by the exact
preceding entry of Ford's `E` schedule. -/
theorem ford_lemma_3_4_raw_absorption
    {s k r j J p : ℕ} {C delta P eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr : 2 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hJ : 1 ≤ J) (hJj : J < j) (hjr : j ≤ r)
    (hP : 1 ≤ P) (heta : 1 ≤ eta)
    (homega : 1 / (3 * Real.log k) ≤ omega) (hetaEq : eta = 1 + omega)
    (hM : 1 ≤ fordMScale P Φ (J + 1))
    (hmoment : FordVinogradovMomentBound s k C delta)
    (hp : p ∈ fordPrimeSet k ⌊fordMScale P Φ J⌋₊) :
    fordLemma34RawBound s k r J p C delta P eta
        (fordMScale P Φ (J + 1)) (fordQScale P Φ J)
        (fordQScale P Φ (J + 1)) (Esch.E J) ≤
      Esch.E (J - 1) * C * P ^ k *
        (fordQScale P Φ J) ^ fordLambda34 s k delta := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hC : 1 ≤ C := hmoment.one_le_coefficient
  have hE : 1 ≤ Esch.E J := Esch.one_le (show 1 ≤ k by omega) heta J hJj
  have hQ0 : 0 < fordQScale P Φ J := fordQScale_pos hP0 Φ J
  have hJB : 0 ≤ fordLemma34JBound s k C delta (fordQScale P Φ J) := by
    unfold fordLemma34JBound
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hQ0.le _)
  have hoff := ford_lemma_3_4_off_diagonal_normalized
    (s := s) (k := k) (r := r) (J := J) (p := p)
    (C := C) (delta := delta) (P := P) (eta := eta)
    (M := fordMScale P Φ (J + 1))
    (Q := fordQScale P Φ J) (Qnext := fordQScale P Φ (J + 1))
    (E := Esch.E J) (phiJ := Φ.phi J) (phiNext := Φ.phi (J + 1))
    (show 1 ≤ k by omega) (show 1 ≤ r by omega) hrk
    (show J ≤ s by omega) (show J < r by omega) hP heta hM
    (fordQScale_pos hP0 Φ (J + 1)) rfl
    (fordQScale_eq_MScale_mul_succ hP0 Φ J)
    (by simpa [fordMScale] using fordPrimeSet_gt_real hp)
    (Φ.recurrence J hJ hJj) hC hE
  let B : ℝ := 4 * √((k : ℝ) ^ 3 * k.factorial) *
    √(Esch.E J) * eta ^ fordEStepExponent s k J
  have hmax :
      max (((k ^ k : ℕ) : ℝ) *
          fordLemma34JBound s k C delta (fordQScale P Φ J))
        (2 * ((p : ℝ) ^ (r * k))⁻¹ *
          √(fordLemma34JBound s k C delta (fordQScale P Φ J) *
            fordLemma34KBound s k r J C delta P eta
              (fordMScale P Φ (J + 1)) (fordQScale P Φ (J + 1))
              (Esch.E J))) ≤
        max (((k ^ k : ℕ) : ℝ) *
            fordLemma34JBound s k C delta (fordQScale P Φ J))
          (B * fordLemma34JBound s k C delta (fordQScale P Φ J)) := by
    apply max_le
    · exact le_max_left _ _
    · exact hoff.trans (le_max_right _ _)
  have hmaxFactor :
      max (((k ^ k : ℕ) : ℝ) *
          fordLemma34JBound s k C delta (fordQScale P Φ J))
        (B * fordLemma34JBound s k C delta (fordQScale P Φ J)) =
      max ((k ^ k : ℕ) : ℝ) B *
        fordLemma34JBound s k C delta (fordQScale P Φ J) := by
    exact (max_mul_of_nonneg _ _ hJB).symm
  have houter := ford_lemma_3_4_outer_box_bound (k := k) hP0.le
  have habs := ford_lemma_3_4_max_absorption
    (s := s) (k := k) (J := J) (E := Esch.E J)
    hk hks homega hetaEq hE
  have habsB :
      max ((2 : ℝ) ^ k * (k : ℝ) ^ k) ((2 : ℝ) ^ k * B) ≤
        (k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √(Esch.E J) := by
    simpa [B, mul_assoc] using habs
  unfold fordLemma34RawBound
  calc
    (((2 * ⌊P⌋₊ : ℕ) : ℝ) ^ k) *
        max (((k ^ k : ℕ) : ℝ) *
          fordLemma34JBound s k C delta (fordQScale P Φ J))
          (2 * ((p : ℝ) ^ (r * k))⁻¹ *
            √(fordLemma34JBound s k C delta (fordQScale P Φ J) *
              fordLemma34KBound s k r J C delta P eta
                (fordMScale P Φ (J + 1)) (fordQScale P Φ (J + 1))
                (Esch.E J))) ≤
      ((2 : ℝ) ^ k * P ^ k) *
        max (((k ^ k : ℕ) : ℝ) *
          fordLemma34JBound s k C delta (fordQScale P Φ J))
          (2 * ((p : ℝ) ^ (r * k))⁻¹ *
            √(fordLemma34JBound s k C delta (fordQScale P Φ J) *
              fordLemma34KBound s k r J C delta P eta
                (fordMScale P Φ (J + 1)) (fordQScale P Φ (J + 1))
                (Esch.E J))) := by gcongr
    _ ≤ ((2 : ℝ) ^ k * P ^ k) *
        max (((k ^ k : ℕ) : ℝ) *
          fordLemma34JBound s k C delta (fordQScale P Φ J))
          (B * fordLemma34JBound s k C delta (fordQScale P Φ J)) := by
            gcongr
    _ = P ^ k *
        max ((2 : ℝ) ^ k * (k : ℝ) ^ k)
          ((2 : ℝ) ^ k * B) *
        fordLemma34JBound s k C delta (fordQScale P Φ J) := by
          rw [hmaxFactor]
          rw [show (2 : ℝ) ^ k * P ^ k *
                (max ((k ^ k : ℕ) : ℝ) B *
                  fordLemma34JBound s k C delta (fordQScale P Φ J)) =
              P ^ k * ((2 : ℝ) ^ k * max ((k ^ k : ℕ) : ℝ) B) *
                fordLemma34JBound s k C delta (fordQScale P Φ J) by ring,
            mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]
          push_cast
          rfl
    _ ≤ P ^ k *
        ((k : ℝ) ^ k * eta ^ fordEStepExponent s k J * √(Esch.E J)) *
        fordLemma34JBound s k C delta (fordQScale P Φ J) := by
          gcongr
    _ = Esch.E (J - 1) * C * P ^ k *
        (fordQScale P Φ J) ^ fordLambda34 s k delta := by
          rw [Esch.recurrence J hJ hJj]
          unfold fordLemma34JBound
          ring

#print axioms FordESchedule.one_le
#print axioms ford_sqrt_rpow
#print axioms ford_sqrt_nat_pow
#print axioms ford_lemma_3_4_sqrt_numeric_factor
#print axioms ford_sqrt_repeated_coefficient_product
#print axioms ford_prime_inverse_power_le_scale
#print axioms ford_prime_scale_exponent_inflation
#print axioms ford_consecutive_Q_half_powers
#print axioms ford_sqrt_prime_scale_exponent_inflation
#print axioms ford_lemma_3_4_eta_exponent_le
#print axioms ford_lemma_3_4_expanded_scale_cancellation
#print axioms ford_lemma_3_4_off_diagonal_normalized
#print axioms ford_lemma_3_4_outer_box_bound
#print axioms ford_lemma_3_4_raw_absorption

end

end GafniTao
