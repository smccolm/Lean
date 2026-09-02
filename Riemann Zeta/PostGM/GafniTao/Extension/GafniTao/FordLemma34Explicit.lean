import GafniTao.FordLemma34Final
import GafniTao.FordLemma34ExplicitData
import GafniTao.FordLemma35OneStep
import GafniTao.FordLemma36Equation320

/-!
# Ford Lemma 3.4 with a quantitative endpoint

This is the non-eventual form needed when the degree varies later in Ford's
zeta argument.  Its coefficient and exponent are unchanged; the only new
premise is the explicit common endpoint proved from the fixed-width PNT
packet in `FordLemma34ExplicitData`.
-/

namespace GafniTao

noncomputable section

/-- The equation-(3.10) induction at every index, now above a stated common
endpoint rather than under an eventual quantifier. -/
theorem ford_equation_3_10_all_indices_explicit
    {s k r j : ℕ} {C delta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j (53 / 50 : ℝ))
    (hk : 1000 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k)
    (hks : k ≤ s) (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (hmoment : FordVinogradovMomentBound s k C delta)
    {P : ℝ} (hthreshold : fordLemma34ExplicitThreshold s k ≤ P) :
    ∀ J, J ≤ j - 1 →
      FordEquation310Eta s k r j C delta P (53 / 50 : ℝ) Φ Esch J := by
  have hlog := ford_log_k_lower hk
  have homegaLower : 1 / (3 * Real.log (k : ℝ)) ≤ (3 / 50 : ℝ) := by
    have hlog0 : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    rw [div_le_iff₀ (by positivity : 0 < 3 * Real.log (k : ℝ))]
    nlinarith
  rcases ford_equation_3_10_inputs_explicit Φ (by omega) hr hrk hj hjr h38
      hlower hthreshold with ⟨hP, hPbig, hMlarge, hQbox, hpacket⟩
  exact ford_equation_3_10_all_indices Φ Esch (by omega) hr hrk hks hj hjr h38
    hlower hP hPbig homegaLower (by norm_num) (by norm_num) hMlarge
      (fun i _hi hij => hQbox i hij) hpacket hmoment

/-- Ford Lemma 3.4 with the exact source coefficient and an explicit common
endpoint. -/
theorem ford_lemma_3_4_explicit
    {s k r j : ℕ} {C delta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hk : 1000 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    (hmoment : FordVinogradovMomentBound s k C delta)
    {P : ℝ} (hthreshold : fordLemma34ExplicitThreshold s k ≤ P) :
      (fordVinogradovMoment (s + k) k P : ℝ) ≤
        fordStepCoefficient35 s k C (53 / 50 : ℝ) *
          P ^ (2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
            fordDeltaPrime34 k r delta (Φ.phi 1)) := by
  have heta : (1 : ℝ) ≤ 53 / 50 := by norm_num
  let Esch := fordCanonicalESchedule s k j (53 / 50 : ℝ)
    (show 1 ≤ k by omega) heta
  rcases ford_equation_3_10_inputs_explicit Φ (by omega) hr hrk hj hjr h38
      hlower hthreshold with ⟨hP, hPbig, hMlarge, hQbox, hpacket⟩
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
    (fordMScale_pos hP0 Φ 1).le (show (3 / 50 : ℝ) ≤ 1 by norm_num)
    (by simpa only [show (1 : ℝ) + 3 / 50 = 53 / 50 by norm_num]
      using hpacketBound)
  have hquotient :
      ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ 1⌋₊,
        ((⌊fordQScale P Φ 0⌋₊ / p : ℕ) : ℝ) ≤ fordQScale P Φ 1 := by
    intro p hp
    exact ford_floor_div_prime_le_next_scale
      (fordQScale_pos hP0 Φ 0) (fordMScale_pos hP0 Φ 1)
      (fordPrimeSet_gt_real hp) (fordQScale_div_MScale hP0 Φ 0)
  have hIH : FordEquation310Eta s k r j C delta P (53 / 50 : ℝ) Φ Esch 0 :=
    ford_equation_3_10_all_indices_explicit Φ Esch hk hr hrk hks hj hjr h38
      hlower hmoment hthreshold 0 (by omega)
  have hK := ford_equation_3_10_K_bound Φ Esch
    (fordInitialIntegerPowerSystem k) (by omega : 26 ≤ k)
    (show 2 ≤ r by omega) hrk hks (show 0 < j by omega)
    (show j ≤ r by omega) hP hPbig hM hkM hPM hbox hpacketTwo
    hpacketBound hquotient (show 0 < (1 : ℕ) by omega)
    (show 0 < (1 : ℕ) by omega) (by simp) hmoment hIH
  rw [fordQScale_zero, fordKCountReal_initial_eq_vinogradov] at hK
  have hfinal := ford_lemma_3_4_initial_K_bound_le Φ Esch (by omega : 26 ≤ k)
    hr hrk hj
    ((show (0 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ)) by positivity).trans
      (hlower 1 (by omega) (by omega)))
    heta hP (hmoment.one_le_coefficient.trans' zero_le_one)
  simpa [fordStepCoefficient35] using hK.trans hfinal

#print axioms ford_equation_3_10_all_indices_explicit
#print axioms ford_lemma_3_4_explicit

end

end GafniTao
