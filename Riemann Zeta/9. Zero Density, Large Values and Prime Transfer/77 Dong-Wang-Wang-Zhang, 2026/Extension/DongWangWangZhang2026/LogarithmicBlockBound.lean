import DongWangWangZhang2026.ZetaSum
import DongWangWangZhang2026.LogarithmicDerivativeBounds
import GuthMaynard.WeylExplicit

/-!
# Finite logarithmic blocks for the large-x estimate

The existing foundation A-after-B theorem is retained. Its uniform
correlation majorant is evaluated on a wider physical range, sufficient
for the paper's one-thirteenth saving without another exponent-pair package.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set
open RiemannZeta.GuthMaynard

/-- The existing correlation majorant on blocks up to the two-thirds height scale. -/
theorem logarithmic_correlation_extended_scale {Z : ℝ} (hZ : 1 ≤ Z)
    (A H : ℕ) (hA : 0 < A) (hHY : (H : ℝ) * Z ^ (4 : ℕ) ≤ A)
    (hAZ : (A : ℝ) ≤ Z ^ (8 : ℕ)) :
    simpleLogarithmicCorrelationBound (Z ^ (12 : ℕ)) A A H ≤
      100 * (Z ^ (4 : ℕ) + 3 * (A : ℝ) / Z ^ (2 : ℕ)) := by
  have hZ0 : 0 < Z := by linarith
  have hA0 : 0 < (A : ℝ) := Nat.cast_pos.mpr hA
  let q := Z ^ (12 : ℕ) / (8 * (A : ℝ) ^ (3 : ℕ))
  have hq : 0 < q := by dsimp only [q]; positivity
  have hhigh : q * H ≤ (Z ^ (4 : ℕ) / (A : ℝ)) ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hHY
      (by positivity : 0 ≤ Z ^ (8 : ℕ) / (8 * (A : ℝ) ^ (3 : ℕ)))
    have he : (H : ℝ) * Z ^ (4 : ℕ) * (Z ^ (8 : ℕ) / (8 * (A : ℝ) ^ (3 : ℕ))) =
        q * H := by dsimp only [q]; ring
    rw [he] at h
    apply h.trans
    field_simp
    nlinarith [pow_nonneg hZ0.le 8]
  have hfirst : (A : ℝ) * Real.sqrt (q * H) ≤ Z ^ (4 : ℕ) := by
    have h := Real.sqrt_le_iff.mpr ⟨by positivity, hhigh⟩
    have hm := mul_le_mul_of_nonneg_left h hA0.le
    simpa only [mul_div_cancel₀ _ hA0.ne'] using hm
  have hlow : (Z ^ (2 : ℕ) / (3 * (A : ℝ))) ^ (2 : ℕ) ≤ q := by
    dsimp only [q]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : 0 < (3 * (A : ℝ)) ^ (2 : ℕ))
      (by positivity : 0 < 8 * (A : ℝ) ^ (3 : ℕ))).mpr
    have h := mul_le_mul_of_nonneg_right hAZ
      (by positivity : 0 ≤ (A : ℝ) ^ (2 : ℕ) * Z ^ (4 : ℕ))
    nlinarith [mul_nonneg (sq_nonneg (A : ℝ)) (pow_nonneg hZ0.le 12)]
  have hsqrt := Real.le_sqrt_of_sq_le hlow
  have hsecond : 1 / Real.sqrt q ≤ 3 * (A : ℝ) / Z ^ (2 : ℕ) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hq) (sq_pos_of_pos hZ0)).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 3 * (A : ℝ))).mp hsqrt
    nlinarith only [h]
  unfold simpleLogarithmicCorrelationBound
  change 100 * ((A : ℝ) * Real.sqrt (q * H) + 1 / Real.sqrt q) ≤ _
  linarith

/-- A genuine all-prefix A-after-B bound on the extended physical range. -/
theorem logarithmic_weyl_prefix_extended {Z : ℝ} (hZ : 1 ≤ Z)
    (A N : ℕ) (hA : 0 < A) (hNA : N ≤ A)
    (hYA : Z ^ (4 : ℕ) ≤ A) (hAZ : (A : ℝ) ≤ Z ^ (8 : ℕ)) :
    ‖logarithmicSum (Z ^ (12 : ℕ)) A (A + N)‖ ≤
      30 * (Real.sqrt ((A : ℝ) * Z ^ (4 : ℕ)) + (A : ℝ) / Z) := by
  have hZ0 : 0 < Z := by linarith
  have hY1 : 1 ≤ Z ^ (4 : ℕ) := one_le_pow₀ hZ
  obtain ⟨hH, hHA, hHY, hAH⟩ :=
    classicalWeylShiftLength_spec (Z ^ (4 : ℕ)) A hY1 hA hYA
  let H := classicalWeylShiftLength (Z ^ (4 : ℕ)) A
  have hH0 : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hA0 : 0 < (A : ℝ) := Nat.cast_pos.mpr hA
  have hNreal : (N : ℝ) ≤ A := by exact_mod_cast hNA
  have hHAreal : (H : ℝ) ≤ A := by exact_mod_cast hHA
  by_cases hHN : H ≤ N
  · have hsmall : Z ^ (12 : ℕ) * (H : ℝ) / (8 * (A : ℝ) ^ (3 : ℕ)) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 8 * (A : ℝ) ^ (3 : ℕ))).mpr
      have h := mul_le_mul_of_nonneg_right hHY (pow_nonneg hZ0.le 8)
      have hsq := (sq_le_sq₀ (pow_nonneg hZ0.le 4) hA0.le).mpr hYA
      have h' := mul_le_mul_of_nonneg_right hsq hA0.le
      nlinarith [pow_nonneg hA0.le 3]
    let B := Z ^ (4 : ℕ) + 3 * (A : ℝ) / Z ^ (2 : ℕ)
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hYB : Z ^ (4 : ℕ) ≤ B := by
      dsimp only [B]
      have h : 0 ≤ 3 * (A : ℝ) / Z ^ (2 : ℕ) := by positivity
      linarith
    have hc : simpleLogarithmicCorrelationBound (Z ^ (12 : ℕ)) A N H ≤ 100 * B := by
      apply le_trans _ (logarithmic_correlation_extended_scale hZ A H hA hHY hAZ)
      unfold simpleLogarithmicCorrelationBound
      dsimp only
      gcongr
    have hab := logarithmic_weyl_AB_process_simple
      (Z ^ (12 : ℕ)) A N H (pow_pos hZ0 _) hA0 hHN hNreal hsmall
    rw [integerLogarithmicSum_eq] at hab
    have hab' : (H : ℝ) ^ 2 * ‖logarithmicSum (Z ^ (12 : ℕ)) A (A + N)‖ ^ 2 ≤
        (((N + H : ℕ) : ℝ) * ((H : ℝ) * N + (H : ℝ) ^ 2 * (100 * B))) :=
      hab.trans (by gcongr)
    push_cast at hab'
    have hinner : (H : ℝ) * N + (H : ℝ) ^ 2 * (100 * B) ≤
        102 * (H : ℝ) ^ 2 * B := by
      have h := mul_le_mul_of_nonneg_left (hNreal.trans hAH) hH0.le
      have h' := mul_le_mul_of_nonneg_left hYB (sq_nonneg (H : ℝ))
      nlinarith only [h, h']
    have houter : (N : ℝ) + H ≤ 2 * A := by linarith
    have hfull : (H : ℝ) ^ 2 * ‖logarithmicSum (Z ^ (12 : ℕ)) A (A + N)‖ ^ 2 ≤
        (H : ℝ) ^ 2 * (204 * (A : ℝ) * B) := by
      apply hab'.trans
      calc
        _ ≤ (2 * A) * (102 * (H : ℝ) ^ 2 * B) :=
          mul_le_mul houter hinner (by positivity) (by positivity)
        _ = _ := by ring
    have hsq : ‖logarithmicSum (Z ^ (12 : ℕ)) A (A + N)‖ ^ 2 ≤ 204 * (A : ℝ) * B :=
      (mul_le_mul_iff_right₀ (sq_pos_of_pos hH0)).mp hfull
    have hroot : Real.sqrt ((A : ℝ) * Z ^ (4 : ℕ)) ^ 2 = (A : ℝ) * Z ^ (4 : ℕ) :=
      Real.sq_sqrt (by positivity)
    have hdiv : ((A : ℝ) / Z) ^ (2 : ℕ) = (A : ℝ) ^ (2 : ℕ) / Z ^ (2 : ℕ) := div_pow _ _ _
    have hnonneg : 0 ≤ (A : ℝ) / Z := by positivity
    have hcross := mul_nonneg (Real.sqrt_nonneg ((A : ℝ) * Z ^ (4 : ℕ))) hnonneg
    have he : 204 * (A : ℝ) * B =
        204 * ((A : ℝ) * Z ^ (4 : ℕ)) + 612 * ((A : ℝ) / Z) ^ (2 : ℕ) := by
      dsimp only [B]
      rw [hdiv]
      ring
    rw [he] at hsq
    nlinarith only [hsq, hroot, hcross, Real.sqrt_nonneg ((A : ℝ) * Z ^ (4 : ℕ)),
      hnonneg, norm_nonneg (logarithmicSum (Z ^ (12 : ℕ)) A (A + N))]
  · have htriv := norm_logarithmicSum_le_length (Z ^ (12 : ℕ)) A (A + N)
    rw [Nat.add_sub_cancel_left] at htriv
    have hNH : (N : ℝ) ≤ H := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hHN))
    have hZZ : Z ≤ Z ^ (4 : ℕ) := by
      simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 4)
    have hHZ := (mul_le_mul_of_nonneg_left hZZ hH0.le).trans hHY
    have hHdiv : (H : ℝ) ≤ (A : ℝ) / Z := (le_div_iff₀ hZ0).mpr hHZ
    have hnonneg : 0 ≤ (A : ℝ) / Z := by positivity
    linarith [htriv.trans (hNH.trans hHdiv), Real.sqrt_nonneg ((A : ℝ) * Z ^ (4 : ℕ))]


/-- The three derivative ranges give one uniform prefix bound at every block size. -/
theorem source_logarithmic_prefix_uniform {Z : ℝ} (hZ : 2 ≤ Z)
    (A N : ℕ) (hA : 0 < A) (hNA : N ≤ A) :
    ‖∑ n ∈ Finset.range N,
      unitaryPhase (logarithmicPhase (Z ^ (12 : ℕ)) (A + 1 + n))‖ ≤
        120 * (Z ^ (2 : ℕ) * Real.sqrt A + (A : ℝ) / Z) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : 0 < (A : ℝ) := by linarith
  have hsqrtA : Real.sqrt (A : ℝ) ^ 2 = A := Real.sq_sqrt (Nat.cast_nonneg A)
  have hnonneg : 0 ≤ (A : ℝ) / Z := by positivity
  have heq : logarithmicSum (Z ^ (12 : ℕ)) (A + 1) (A + 1 + N) =
      ∑ n ∈ Finset.range N,
        unitaryPhase (logarithmicPhase (Z ^ (12 : ℕ)) (A + 1 + n)) := by
    unfold logarithmicSum phaseSum
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
  by_cases hYA : Z ^ (4 : ℕ) ≤ (A + 1 : ℕ)
  · by_cases hAZ : ((A + 1 : ℕ) : ℝ) ≤ Z ^ (8 : ℕ)
    · have h := logarithmic_weyl_prefix_extended hZ1 (A + 1) N (by omega)
        (hNA.trans (by omega)) hYA hAZ
      rw [heq] at h
      have hroot : Real.sqrt (((A + 1 : ℕ) : ℝ) * Z ^ (4 : ℕ)) =
          Z ^ (2 : ℕ) * Real.sqrt ((A + 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg (A + 1)),
          show Z ^ (4 : ℕ) = (Z ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
          Real.sqrt_sq (sq_nonneg Z)]
        ring
      have hrootLe : Real.sqrt ((A + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (A : ℝ) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · push_cast
          nlinarith only [hsqrtA, hA1]
      have hrootLe' := mul_le_mul_of_nonneg_left hrootLe (sq_nonneg Z)
      have hdiv : ((A + 1 : ℕ) : ℝ) / Z ≤ 2 * (A : ℝ) / Z := by
        apply div_le_div_of_nonneg_right _ hZ0.le
        push_cast
        linarith
      rw [hroot] at h
      rw [mul_div_assoc] at hdiv
      have hprod : 0 ≤ Z ^ (2 : ℕ) * Real.sqrt (A : ℝ) := by positivity
      linarith
    · have hAZ' : Z ^ (8 : ℕ) < (A : ℝ) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hAZ
      have hZ7 : 1 ≤ Z ^ (7 : ℕ) := one_le_pow₀ hZ1
      have hZ8 : 2 * Z ^ (7 : ℕ) ≤ Z ^ (8 : ℕ) := by
        have h := mul_le_mul_of_nonneg_right hZ (pow_nonneg hZ0.le 7)
        nlinarith only [h]
      have hA7 : Z ^ (7 : ℕ) ≤ A := by linarith
      have hZ67 : Z ^ (6 : ℕ) ≤ Z ^ (7 : ℕ) := pow_le_pow_right₀ hZ1 (by decide)
      have hAt : Z ^ (12 : ℕ) ≤ (A : ℝ) ^ (2 : ℕ) := by
        have h := (sq_le_sq₀ (pow_nonneg hZ0.le 6) hA0.le).mpr (hZ67.trans hA7)
        nlinarith only [h]
      by_cases hheight : (A : ℝ) ≤ Z ^ (12 : ℕ)
      · have h := source_logarithmic_prefix_second_derivative A N (Z ^ (12 : ℕ))
          hA hNA hheight hAt
        have hs : Real.sqrt (Z ^ (12 : ℕ)) = Z ^ (6 : ℕ) := by
          rw [show Z ^ (12 : ℕ) = (Z ^ (6 : ℕ)) ^ (2 : ℕ) by ring,
            Real.sqrt_sq (pow_nonneg hZ0.le 6)]
        rw [hs] at h
        have hdiv : Z ^ (6 : ℕ) ≤ (A : ℝ) / Z := by
          apply (le_div_iff₀ hZ0).mpr
          nlinarith only [hA7]
        have hfirst : 0 ≤ Z ^ (2 : ℕ) * Real.sqrt (A : ℝ) := by positivity
        linarith
      · have htA : Z ^ (12 : ℕ) ≤ (A : ℝ) := (lt_of_not_ge hheight).le
        have h := source_logarithmic_prefix_first_derivative A N (Z ^ (12 : ℕ))
          hA hNA (one_le_pow₀ hZ1) htA
        have hZZ : Z ≤ Z ^ (12 : ℕ) := by
          simpa only [pow_one] using pow_le_pow_right₀ hZ1 (by decide : 1 ≤ 12)
        have hfrac : (A : ℝ) / Z ^ (12 : ℕ) ≤ (A : ℝ) / Z :=
          div_le_div_of_nonneg_left hA0.le hZ0 hZZ
        have hpi : 6 * Real.pi ≤ (24 : ℝ) := by linarith [Real.pi_lt_four]
        have hbound : 6 * Real.pi * (A : ℝ) / Z ^ (12 : ℕ) ≤ 24 * ((A : ℝ) / Z) := by
          calc
            _ = (6 * Real.pi) * ((A : ℝ) / Z ^ (12 : ℕ)) := by ring
            _ ≤ 24 * ((A : ℝ) / Z) := mul_le_mul hpi hfrac (by positivity) (by norm_num)
        have hfirst : 0 ≤ Z ^ (2 : ℕ) * Real.sqrt (A : ℝ) := by positivity
        linarith
  · have htriv := norm_logarithmicSum_le_length (Z ^ (12 : ℕ)) (A + 1) (A + 1 + N)
    rw [heq, Nat.add_sub_cancel_left] at htriv
    have hNreal : (N : ℝ) ≤ A := by exact_mod_cast hNA
    have hYA' : (A : ℝ) ≤ Z ^ (4 : ℕ) := by
      have h := lt_of_not_ge hYA
      push_cast at h
      linarith
    have hroot : (A : ℝ) ≤ Z ^ (2 : ℕ) * Real.sqrt (A : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hYA' hA0.le
      have hprod : 0 ≤ Z ^ (2 : ℕ) * Real.sqrt (A : ℝ) := by positivity
      apply (sq_le_sq₀ hA0.le hprod).mp
      rw [mul_pow, hsqrtA]
      nlinarith only [h]
    linarith


end
end DongWangWangZhang2026
