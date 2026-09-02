import GafniTao.FordLemma36Admissible

/-!
# Ford Lemma 3.6: iteration of equation (3.12)
-/

namespace GafniTao

noncomputable section

open Finset

def fordQuadraticHalfSum (j : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ico 1 j,
    ((h : ℝ) ^ 2 - h) / (2 : ℝ) ^ (h - 1)

theorem fordQuadraticHalfSum_formula
    {j : ℕ} (hj : 2 ≤ j) :
    fordQuadraticHalfSum j =
      8 - ((j : ℝ) ^ 2 + j + 2) / (2 : ℝ) ^ (j - 2) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [fordQuadraticHalfSum]
  | succ j hj ih =>
      have hj1 : 1 ≤ j := by omega
      have hexp : j - 1 = (j - 2) + 1 := by omega
      have hnew : j + 1 - 2 = j - 1 := by omega
      unfold fordQuadraticHalfSum at ih ⊢
      rw [Finset.sum_Ico_succ_top hj1, ih, hnew, hexp, pow_succ]
      push_cast
      have hpow : (2 : ℝ) ^ (j - 2) ≠ 0 := by positivity
      field_simp [hpow]
      ring

theorem fordQuadraticHalfSum_le_eight (j : ℕ) :
    fordQuadraticHalfSum j ≤ 8 := by
  by_cases hj : 2 ≤ j
  · rw [fordQuadraticHalfSum_formula hj]
    exact sub_le_self _ (by positivity)
  · interval_cases j <;> norm_num [fordQuadraticHalfSum]

/-- A finite unrolling lemma for the one-half recurrence in (3.12). -/
theorem ford_half_recurrence_unroll
    (theta b : ℕ → ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hrec : ∀ J, 1 ≤ J → J < j →
      theta J ≤ theta (J + 1) / 2 + b J) :
    theta 1 ≤ theta j / (2 : ℝ) ^ (j - 1) +
      ∑ h ∈ Finset.Ico 1 j, b h / (2 : ℝ) ^ (h - 1) := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      have hjpos : 1 ≤ j := by omega
      have hstep := hrec j hjpos (by omega)
      have hih := ih (fun J hJ hJj => hrec J hJ (by omega))
      calc
        theta 1 ≤ theta j / (2 : ℝ) ^ (j - 1) +
            ∑ h ∈ Finset.Ico 1 j, b h / (2 : ℝ) ^ (h - 1) := hih
        _ ≤ (theta (j + 1) / 2 + b j) / (2 : ℝ) ^ (j - 1) +
            ∑ h ∈ Finset.Ico 1 j, b h / (2 : ℝ) ^ (h - 1) := by
          gcongr
        _ = theta (j + 1) / (2 : ℝ) ^ (j + 1 - 1) +
            ∑ h ∈ Finset.Ico 1 (j + 1), b h / (2 : ℝ) ^ (h - 1) := by
          rw [Finset.sum_Ico_succ_top hjpos]
          have hpowEq : (2 : ℝ) ^ j =
              2 * (2 : ℝ) ^ (j - 1) := by
            calc
              (2 : ℝ) ^ j = (2 : ℝ) ^ ((j - 1) + 1) := by
                congr 1
                omega
              _ = (2 : ℝ) ^ (j - 1) * 2 := by rw [pow_succ]
              _ = 2 * (2 : ℝ) ^ (j - 1) := by ring
          rw [show j + 1 - 1 = j by omega, hpowEq]
          field_simp
          ring

theorem fordCanonicalTheta_recurrence
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) :
    let Φ := fordCanonicalPhiSchedule k r j delta
    let theta := fun J => Φ.phi J - fordPhiStar35 k r delta
    ∀ J, 1 ≤ J → J < j →
      theta J ≤ theta (J + 1) / 2 +
        (((J : ℝ) ^ 2 - J) / (4 * k * r)) *
          fordPhiStar35 k r delta := by
  dsimp only
  intro J hJ hJj
  let Φ := fordCanonicalPhiSchedule k r j delta
  have hrec := Φ.recurrence J hJ hJj
  rw [hrec]
  have hy : 0 ≤ fordY35 k r delta := by
    have : (0 : ℝ) ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by positivity
    linarith
  have hden : 0 < 2 * (r : ℝ) * k + fordY35 k r delta := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    positivity
  have hid := ford_phi_step_sub_phiStar35 J delta (Φ.phi (J + 1))
    (show 0 < k by omega) (show 0 < r by omega) (ne_of_gt hden)
  have hcoeff0 := ford_theta_coefficient35_nonneg hk hr hdelta (J := J)
  have hcoeffHalf := ford_theta_coefficient35_le_half hk hr hJ hJj h38
  have hthetaNext : 0 ≤ Φ.phi (J + 1) - fordPhiStar35 k r delta := by
    exact sub_nonneg.mpr (fordCanonicalPhiSchedule_phiStar_le hk hr h38 hdelta
      (J + 1) (by omega) (by omega))
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_right hcoeffHalf hthetaNext]

/-- Ford's first displayed consequence of iterating (3.12). -/
theorem fordCanonicalTheta_one_le
    {k r j : ℕ} {delta : ℝ}
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hj : 2 ≤ j)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) :
    let Φ := fordCanonicalPhiSchedule k r j delta
    Φ.phi 1 - fordPhiStar35 k r delta ≤
      (1 / (r : ℝ)) / (2 : ℝ) ^ (j - 1) +
        2 * fordPhiStar35 k r delta / ((k : ℝ) * r) := by
  let Φ := fordCanonicalPhiSchedule k r j delta
  let theta : ℕ → ℝ := fun J => Φ.phi J - fordPhiStar35 k r delta
  let b : ℕ → ℝ := fun J =>
    (((J : ℝ) ^ 2 - J) / (4 * k * r)) * fordPhiStar35 k r delta
  have hunroll := ford_half_recurrence_unroll theta b (show 1 ≤ j by omega)
    (fordCanonicalTheta_recurrence hk hr hdelta h38)
  have hterminal : theta j ≤ 1 / (r : ℝ) := by
    dsimp [theta]
    rw [Φ.terminal]
    have hstar := ford_phiStar35_nonneg hk hr h38
    linarith
  have hstar0 := ford_phiStar35_nonneg hk hr h38
  have hsumEq :
      (∑ h ∈ Finset.Ico 1 j, b h / (2 : ℝ) ^ (h - 1)) =
        fordPhiStar35 k r delta / (4 * k * r) *
          fordQuadraticHalfSum j := by
    unfold b fordQuadraticHalfSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [hsumEq] at hunroll
  calc
    theta 1 ≤ theta j / (2 : ℝ) ^ (j - 1) +
        fordPhiStar35 k r delta / (4 * k * r) *
          fordQuadraticHalfSum j := hunroll
    _ ≤ (1 / (r : ℝ)) / (2 : ℝ) ^ (j - 1) +
        fordPhiStar35 k r delta / (4 * k * r) * 8 := by
      have hpow : 0 < (2 : ℝ) ^ (j - 1) := by positivity
      have hfactor : 0 ≤ fordPhiStar35 k r delta / (4 * k * r) := by positivity
      gcongr
      exact fordQuadraticHalfSum_le_eight j
    _ = (1 / (r : ℝ)) / (2 : ℝ) ^ (j - 1) +
        2 * fordPhiStar35 k r delta / ((k : ℝ) * r) := by ring

#print axioms fordQuadraticHalfSum_formula
#print axioms ford_half_recurrence_unroll
#print axioms fordCanonicalTheta_recurrence
#print axioms fordCanonicalTheta_one_le

end

end GafniTao
