import GafniTao.FordLemma34Initial

/-!
# Ford Lemma 3.4: final source assembly

This file performs the last application of Lemma 3.2 at `J=0`, identifies
the initial `K`-count with the Vinogradov moment of length `s+k`, and carries
out the remaining source exponent calculation.  The prime packets used below
are the canonical packets supplied eventually by the audited PNT theorem.
-/

open Filter
open scoped Topology

namespace GafniTao

noncomputable section

/-- At the initial scale, the `Q₀=M₁Q₁` relation converts the residual
`M₁`, `P`, and `Q₁` powers into the exact exponent in Ford's last display. -/
theorem ford_lemma_3_4_initial_scale_power
    {s k r j : ℕ} {delta P : ℝ}
    (Φ : FordPhiSchedule k r j delta) (hP : 0 < P) :
    (fordMScale P Φ 1) ^
          (2 * (s : ℝ) + ((r : ℝ) ^ 2 - r) / 2) *
        P ^ (k : ℝ) *
        (fordQScale P Φ 1) ^ fordLambda34 s k delta =
      P ^ (fordLambda34 s k delta + k) *
        (fordMScale P Φ 1) ^
          (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2 - delta) := by
  have hM : 0 < fordMScale P Φ 1 := fordMScale_pos hP Φ 1
  have hQ : 0 < fordQScale P Φ 1 := fordQScale_pos hP Φ 1
  have hscale : P = fordMScale P Φ 1 * fordQScale P Φ 1 := by
    simpa using fordQScale_eq_MScale_mul_succ hP Φ 0
  have hexp :
      2 * (s : ℝ) + ((r : ℝ) ^ 2 - r) / 2 - fordLambda34 s k delta =
        ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2 - delta := by
    unfold fordLambda34
    ring
  rw [← hexp]
  have hPlambda :
      P ^ fordLambda34 s k delta =
        fordMScale P Φ 1 ^ fordLambda34 s k delta *
          fordQScale P Φ 1 ^ fordLambda34 s k delta := by
    calc
      P ^ fordLambda34 s k delta =
          (fordMScale P Φ 1 * fordQScale P Φ 1) ^
            fordLambda34 s k delta :=
        congrArg (fun x : ℝ => x ^ fordLambda34 s k delta) hscale
      _ = fordMScale P Φ 1 ^ fordLambda34 s k delta *
          fordQScale P Φ 1 ^ fordLambda34 s k delta :=
        Real.mul_rpow hM.le hQ.le
  have hMpower :
      fordMScale P Φ 1 ^
          (2 * (s : ℝ) + ((r : ℝ) ^ 2 - r) / 2) =
        fordMScale P Φ 1 ^ fordLambda34 s k delta *
          fordMScale P Φ 1 ^
            (2 * (s : ℝ) + ((r : ℝ) ^ 2 - r) / 2 -
              fordLambda34 s k delta) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  rw [Real.rpow_add hP, hPlambda, hMpower]
  ring

/-- The `J=0` `K`-bound is no larger than Ford's final source-shaped
coefficient and power. -/
theorem ford_lemma_3_4_initial_K_bound_le
    {s k r j : ℕ} {C delta P eta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hj : 2 ≤ j)
    (hphiOne : 0 ≤ Φ.phi 1) (heta : 1 ≤ eta)
    (hP : 1 ≤ P) (hC : 0 ≤ C) :
    fordLemma34KBound s k r 0 C delta P eta
        (fordMScale P Φ 1) (fordQScale P Φ 1) (Esch.E 0) ≤
      ((k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C *
        P ^ (2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
          fordDeltaPrime34 k r delta (Φ.phi 1)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hM : 1 ≤ fordMScale P Φ 1 := by
    exact Real.one_le_rpow hP hphiOne
  have hE0 : 0 < Esch.E 0 := Esch.positive 0 (by omega)
  let e : ℝ := 2 * (s : ℝ) + ((r : ℝ) ^ 2 - r) / 2
  let eK : ℝ := 2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2
  have he : (fordLemma34PrimeExponent s 0 r : ℝ) ≤ e := by
    simpa [e] using
      (fordLemma34PrimeExponent_cast_le_source (s := s) (d := 0) (r := r)
        (by omega) (by omega : 0 < r))
  have hinflate :
      (eta * fordMScale P Φ 1) ^ fordLemma34PrimeExponent s 0 r ≤
        eta ^ e * (fordMScale P Φ 1) ^ e :=
    ford_prime_scale_exponent_inflation heta hM he
  have herk : (r : ℝ) ^ 2 - r ≤ (k : ℝ) ^ 2 - k := by
    have hrR : (r : ℝ) ≤ k := by exact_mod_cast hrk
    have hsum : (0 : ℝ) ≤ (k : ℝ) + r - 1 := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      have hk0 : (0 : ℝ) ≤ k := by positivity
      linarith
    have hprod : 0 ≤ ((k : ℝ) - r) * ((k : ℝ) + r - 1) :=
      mul_nonneg (sub_nonneg.mpr hrR) hsum
    nlinarith
  have heeK : e ≤ eK := by
    dsimp [e, eK]
    linarith
  have hetaPow : eta ^ e ≤ eta ^ eK :=
    Real.rpow_le_rpow_of_exponent_le heta heeK
  have hscale := ford_lemma_3_4_initial_scale_power
    (s := s) (k := k) (r := r) Φ hP0
  have hPk : P ^ k = P ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
  have hterminal := ford_lemma_3_4_terminal_constant hk heta
    (Esch.zero_le_source_bound (show 1 ≤ k by omega) heta hj)
  unfold fordLemma34KBound fordLemma34LBound
  dsimp [e, eK] at hinflate hetaPow hterminal ⊢
  have hrest : 0 ≤ Esch.E 0 * C * P ^ k *
      fordQScale P Φ 1 ^ fordLambda34 s k delta := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hE0.le hC) (by positivity))
      (Real.rpow_nonneg (fordQScale_pos hP0 Φ 1).le _)
  have hscaleRest : 0 ≤ fordMScale P Φ 1 ^ e * P ^ k *
      fordQScale P Φ 1 ^ fordLambda34 s k delta := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (fordMScale_pos hP0 Φ 1).le _) (by positivity))
      (Real.rpow_nonneg (fordQScale_pos hP0 Φ 1).le _)
  calc
    ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (eta * fordMScale P Φ 1) ^ fordLemma34PrimeExponent s 0 r *
          (Esch.E 0 * C * P ^ k *
            fordQScale P Φ 1 ^ fordLambda34 s k delta) ≤
        ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (eta ^ e * fordMScale P Φ 1 ^ e) *
          (Esch.E 0 * C * P ^ k *
            fordQScale P Φ 1 ^ fordLambda34 s k delta) := by
      gcongr
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (eta ^ eK * fordMScale P Φ 1 ^ e) *
          (Esch.E 0 * C * P ^ k *
            fordQScale P Φ 1 ^ fordLambda34 s k delta) := by
      gcongr
    _ = (((4 : ℝ) * k ^ 3 * k.factorial * eta ^ eK * Esch.E 0) * C) *
          (fordMScale P Φ 1 ^ e * P ^ k *
            fordQScale P Φ 1 ^ fordLambda34 s k delta) := by
      push_cast
      ring
    _ ≤ (((k : ℝ) ^ (3 * k) *
          eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C) *
          (fordMScale P Φ 1 ^ e * P ^ k *
            fordQScale P Φ 1 ^ fordLambda34 s k delta) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hterminal hC) hscaleRest
    _ = ((k : ℝ) ^ (3 * k) *
          eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C *
        P ^ (2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
          fordDeltaPrime34 k r delta (Φ.phi 1)) := by
      rw [show fordMScale P Φ 1 ^ e * P ^ k *
          fordQScale P Φ 1 ^ fordLambda34 s k delta =
          P ^ (fordLambda34 s k delta + k) *
            fordMScale P Φ 1 ^
              (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2 - delta) by
        rw [hPk]
        simpa [e] using hscale]
      rw [fordMScale, ford_lemma_3_4_terminal_power hP0]

/-- The complete large-parameter form of Ford Lemma 3.4.  It has the exact
source coefficient and updated exponent; only Ford's printed explicit
Rosser--Schoenfeld threshold is replaced by an eventual threshold derived
from the audited PNT. -/
theorem eventually_ford_lemma_3_4
    {s k r j : ℕ} {C delta eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    ∀ᶠ P : ℝ in atTop,
      (fordVinogradovMoment (s + k) k P : ℝ) ≤
        ((k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C *
          P ^ (2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
            fordDeltaPrime34 k r delta (Φ.phi 1)) := by
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have homega0 : 0 ≤ omega := by
    have : 0 < 1 / (3 * Real.log (k : ℝ)) := by positivity
    linarith
  have heta : 1 ≤ eta := by rw [hetaEq]; linarith
  let Esch := fordCanonicalESchedule s k j eta (show 1 ≤ k by omega) heta
  filter_upwards
      [eventually_ford_equation_3_10_inputs Φ hk hr hrk hj hjr h38 hlower
        homegaLower hetaEq,
       eventually_ford_equation_3_10_all_indices Φ Esch hk hr hrk hks hj hjr h38
        hlower homegaLower homegaUpper hetaEq hmoment]
    with P hinputs h310
  rcases hinputs with ⟨hP, hPbig, hMlarge, hQbox, hpacket⟩
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hMreal := hMlarge 1 (by omega) (by omega)
  have hM : 1 < fordMScale P Φ 1 := by
    have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    exact hkR.trans_le hMreal
  have hkM : k ≤ ⌊fordMScale P Φ 1⌋₊ := ford_nat_le_floor_scale hMreal
  have hPM : P ≤ fordMScale P Φ 1 ^ (k + 1) :=
    ford_P_le_MScale_pow hP (show 1 ≤ k by omega) Φ
      (hlower 1 (by omega) (by omega))
  have hbox := ford_floor_Q_box (hQbox 0 (by omega))
  have hpacketBound := hpacket 1 (by omega) (by omega)
  have hpacketTwo := fordPrimeSet_upper_box_of_real_relative
    (fordMScale_pos hP0 Φ 1).le (show omega ≤ 1 by linarith)
    (by simpa [hetaEq] using hpacketBound)
  have hquotient :
      ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ 1⌋₊,
        ((⌊fordQScale P Φ 0⌋₊ / p : ℕ) : ℝ) ≤ fordQScale P Φ 1 := by
    intro p hp
    exact ford_floor_div_prime_le_next_scale
      (fordQScale_pos hP0 Φ 0) (fordMScale_pos hP0 Φ 1)
      (fordPrimeSet_gt_real hp) (fordQScale_div_MScale hP0 Φ 0)
  have hIH : FordEquation310Eta s k r j C delta P eta Φ Esch 0 :=
    h310 0 (by omega)
  have hK := ford_equation_3_10_K_bound Φ Esch
    (fordInitialIntegerPowerSystem k) hk (show 2 ≤ r by omega) hrk hks
    (show 0 < j by omega) (show j ≤ r by omega) hP hPbig hM hkM hPM hbox
    hpacketTwo hpacketBound hquotient (show 0 < (1 : ℕ) by omega)
    (show 0 < (1 : ℕ) by omega) (by simp) hmoment hIH
  rw [fordQScale_zero, fordKCountReal_initial_eq_vinogradov] at hK
  exact hK.trans (ford_lemma_3_4_initial_K_bound_le Φ Esch hk hr hrk hj
    ((show (0 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ)) by positivity).trans
      (hlower 1 (by omega) (by omega)))
    heta hP (hmoment.one_le_coefficient.trans' zero_le_one))

#print axioms ford_lemma_3_4_initial_scale_power
#print axioms ford_lemma_3_4_initial_K_bound_le
#print axioms eventually_ford_lemma_3_4

end

end GafniTao
