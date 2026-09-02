import GafniTao.FordLemma35Schedule

/-!
# Ford Lemma 3.5: the `phi*` comparison

This file proves the comparison following equation (3.11).  In particular,
the lower bound required by Lemma 3.4 is derived from Ford's explicit
`phi*`, the maximal-`j` inequality (3.8), and the backwards recurrence; it is
not accepted as an independent schedule hypothesis.
-/

namespace GafniTao

noncomputable section

/-- Ford's auxiliary quantity
`y = 2 Delta - (k-r)(k-r+1)` in the proof of Lemma 3.5. -/
def fordY35 (k r : ℕ) (delta : ℝ) : ℝ :=
  2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1)

/-- Ford's comparison value in equation (3.11). -/
def fordPhiStar35 (k r : ℕ) (delta : ℝ) : ℝ :=
  2 * (k : ℝ) / (2 * (r : ℝ) * k + fordY35 k r delta)

/-- The coefficient in the recurrence for `theta_J = phi_J - phi*`. -/
def fordThetaCoefficient35 (k r J : ℕ) (delta : ℝ) : ℝ :=
  (2 * (r : ℝ) * k + (J : ℝ) ^ 2 - J - fordY35 k r delta) /
    (4 * k * r)

theorem ford_phi_step_sub_phiStar35
    {k r : ℕ} (J : ℕ) (delta next : ℝ)
    (hk : 0 < k) (hr : 0 < r)
    (hden : 2 * (r : ℝ) * k + fordY35 k r delta ≠ 0) :
    fordPhiStep k r J delta next - fordPhiStar35 k r delta =
      fordThetaCoefficient35 k r J delta *
          (next - fordPhiStar35 k r delta) +
        (((J : ℝ) ^ 2 - J) / (4 * k * r)) *
          fordPhiStar35 k r delta := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  simp only [fordY35] at hden
  simp only [fordPhiStep, fordPhiStar35, fordThetaCoefficient35, fordY35]
  field_simp [hk0, hr0, hden]
  ring

theorem ford_theta_coefficient35_nonneg
    {k r J : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k) :
    0 ≤ fordThetaCoefficient35 k r J delta := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  unfold fordThetaCoefficient35 fordY35
  apply div_nonneg
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hJ : (0 : ℝ) ≤ (J : ℝ) ^ 2 - J := by
      rcases Nat.eq_zero_or_pos J with rfl | hJ
      · norm_num
      · have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ J by positivity) (sub_nonneg.mpr hJ1)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hr1)]
  · positivity

theorem ford_theta_coefficient35_le_half
    {k r j J : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hJ : 1 ≤ J) (hJj : J < j)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) :
    fordThetaCoefficient35 k r J delta ≤ 1 / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hJnat : J * (J - 1) ≤ (j - 1) * (j - 2) := by
    have hle : J ≤ j - 1 := by omega
    simpa [show j - 2 = (j - 1) - 1 by omega] using ford_square_pred_mono hle
  have hJreal : (J : ℝ) ^ 2 - J ≤
      (((j - 1) * (j - 2) : ℕ) : ℝ) := by
    calc
      (J : ℝ) ^ 2 - J = (J : ℝ) * ((J - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hJ]
        ring
      _ ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by exact_mod_cast hJnat
  unfold fordThetaCoefficient35
  have hnum : 2 * (r : ℝ) * k + (J : ℝ) ^ 2 - J - fordY35 k r delta ≤
      2 * (r : ℝ) * k := by linarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k * r)).2
  nlinarith

theorem ford_phiStar35_nonneg
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) :
    0 ≤ fordPhiStar35 k r delta := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy : 0 ≤ fordY35 k r delta := by
    have : (0 : ℝ) ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by positivity
    linarith
  unfold fordPhiStar35
  positivity

theorem ford_phiStar35_le_inv_r
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) :
    fordPhiStar35 k r delta ≤ 1 / (r : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy : 0 ≤ fordY35 k r delta := by
    have : (0 : ℝ) ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by positivity
    linarith
  unfold fordPhiStar35
  apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 * (r : ℝ) * k + fordY35 k r delta)).2
  field_simp
  nlinarith

/-- Ford's induction following (3.11): every value of the canonical schedule
dominates `phi*`. -/
theorem fordCanonicalPhiSchedule_phiStar_le
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k) :
    ∀ i, 1 ≤ i → i ≤ j →
      fordPhiStar35 k r delta ≤
        (fordCanonicalPhiSchedule k r j delta).phi i := by
  let Φ := fordCanonicalPhiSchedule k r j delta
  have hkpos : 0 < k := by omega
  have hrpos : 0 < r := by omega
  have hy : 0 ≤ fordY35 k r delta := by
    have : (0 : ℝ) ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by positivity
    linarith
  have hdenpos : (0 : ℝ) < 2 * (r : ℝ) * k + fordY35 k r delta := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
    positivity
  intro i hi hij
  refine Nat.decreasingInduction (motive := fun i _ =>
      1 ≤ i → fordPhiStar35 k r delta ≤ Φ.phi i) ?_ ?_ hij hi
  · intro J hJlt ih hJpos
    have hJnext : 1 ≤ J + 1 := by omega
    have hrec := Φ.recurrence J hJpos (by omega)
    rw [hrec]
    have hid := ford_phi_step_sub_phiStar35 J delta (Φ.phi (J + 1))
      hkpos hrpos (ne_of_gt hdenpos)
    have hcoeff := ford_theta_coefficient35_nonneg hk hr hdelta
      (J := J)
    have hstar := ford_phiStar35_nonneg hk hr h38
    have hJsq : (0 : ℝ) ≤ (J : ℝ) ^ 2 - J := by
      have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ J by positivity) (sub_nonneg.mpr hJ1)]
    have hnext : 0 ≤ Φ.phi (J + 1) - fordPhiStar35 k r delta := by
      linarith [ih hJnext]
    have htheta : 0 ≤
        fordThetaCoefficient35 k r J delta *
            (Φ.phi (J + 1) - fordPhiStar35 k r delta) +
          (((J : ℝ) ^ 2 - J) / (4 * k * r)) *
            fordPhiStar35 k r delta := by positivity
    linarith
  · intro _
    rw [Φ.terminal]
    exact ford_phiStar35_le_inv_r hk hr h38

/-- Equation (3.11) now supplies the actual lower-bound input expected by
Lemma 3.4 for Ford's canonical schedule. -/
theorem fordCanonicalPhiSchedule_lower
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤ fordPhiStar35 k r delta) :
    ∀ i, 1 ≤ i → i ≤ j →
      1 / (((k + 1 : ℕ) : ℝ)) ≤
        (fordCanonicalPhiSchedule k r j delta).phi i := by
  intro i hi hij
  exact hstar.trans (fordCanonicalPhiSchedule_phiStar_le
    hk hr h38 hdelta i hi hij)

#print axioms ford_phi_step_sub_phiStar35
#print axioms ford_theta_coefficient35_nonneg
#print axioms ford_theta_coefficient35_le_half
#print axioms fordCanonicalPhiSchedule_phiStar_le
#print axioms fordCanonicalPhiSchedule_lower

end

end GafniTao
