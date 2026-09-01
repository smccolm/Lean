import GafniTao.FordLocalDetectorRightBound

/-!
# Quantitative bound for the shifted detector's zeta-pole correction

The shifted centre makes the zeta pole contribute a small positive term.
Using the exact real-cotangent formula, this file bounds it by an inverse
square in the physical height.  Thus the term is retained and controlled,
not silently deleted.
-/

open Complex

namespace GafniTao

noncomputable section

theorem fordCotKernel_re_le_inv_sq_height
    {eta a t : ℝ} (heta : 0 < eta) (ha0 : 0 ≤ a) (haeta : a ≤ eta)
    (ht : 0 < t) :
    (fordCotKernel eta ((a : ℂ) + (t : ℂ) * I)).re ≤
      eta / (Real.pi * t ^ 2) := by
  let c : ℝ := Real.pi / (2 * eta)
  let x : ℝ := c * a
  let y : ℝ := c * t
  have hc : 0 < c := div_pos Real.pi_pos (mul_pos two_pos heta)
  have hx0 : 0 ≤ x := mul_nonneg hc.le ha0
  have hxpi : x ≤ Real.pi / 2 := by
    calc
      x = c * a := rfl
      _ ≤ c * eta := mul_le_mul_of_nonneg_left haeta hc.le
      _ = Real.pi / 2 := by
        dsimp only [c]
        field_simp [heta.ne']
  have hy : 0 < y := mul_pos hc ht
  have harg : ((c : ℂ) * ((a : ℂ) + (t : ℂ) * I)) =
      (x : ℂ) + (y : ℂ) * I := by
    dsimp only [x, y]
    push_cast
    ring
  have hsinOne : Real.sin (2 * x) ≤ 1 := Real.sin_le_one _
  have hsinh : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy.le
  have hsinhNonneg : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.mpr hy.le
  have hdenFormula :
      Real.cosh (2 * y) - Real.cos (2 * x) ≥ 2 * Real.sinh y ^ 2 := by
    rw [Real.cosh_two_mul]
    have hcos : Real.cos (2 * x) ≤ 1 := Real.cos_le_one _
    nlinarith [Real.cosh_sq_sub_sinh_sq y]
  have hdenLower : 2 * y ^ 2 ≤
      Real.cosh (2 * y) - Real.cos (2 * x) := by
    have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := by nlinarith
    linarith
  have hdenPos : 0 < Real.cosh (2 * y) - Real.cos (2 * x) :=
    lt_of_lt_of_le (mul_pos two_pos (sq_pos_of_pos hy)) hdenLower
  have hfrac :
      Real.sin (2 * x) /
          (Real.cosh (2 * y) - Real.cos (2 * x)) ≤
        1 / (2 * y ^ 2) := by
    apply (div_le_div_iff₀ hdenPos (mul_pos two_pos (sq_pos_of_pos hy))).2
    have hmul := mul_le_mul hsinOne hdenLower
      (by positivity : 0 ≤ 2 * y ^ 2) (by norm_num : 0 ≤ (1 : ℝ))
    nlinarith
  have hkernel :
      (fordCotKernel eta ((a : ℂ) + (t : ℂ) * I)).re =
        c * (Real.sin (2 * x) /
          (Real.cosh (2 * y) - Real.cos (2 * x))) := by
    unfold fordCotKernel
    change (((c : ℝ) : ℂ) *
      Complex.cot (((c : ℝ) : ℂ) * ((a : ℂ) + (t : ℂ) * I))).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, harg, ford_re_cot_formula]
  rw [hkernel]
  calc
    c * (Real.sin (2 * x) /
        (Real.cosh (2 * y) - Real.cos (2 * x))) ≤
        c * (1 / (2 * y ^ 2)) := mul_le_mul_of_nonneg_left hfrac hc.le
    _ = eta / (Real.pi * t ^ 2) := by
      dsimp only [c, y]
      field_simp [heta.ne', Real.pi_ne_zero, ht.ne']

theorem fordShiftedDetector_poleCorrection_le_inv_sq
    {sigma eta t : ℝ} (heta : 0 < eta) (hsigma : 1 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1 + eta) (ht : 0 < t) :
    -(fordCotKernel eta
        (1 - fordShiftedDetectorCenter sigma t)).re ≤
      eta / (Real.pi * t ^ 2) := by
  rw [fordShiftedDetector_poleCorrection_eq]
  have harg : fordShiftedDetectorCenter sigma t - 1 =
      (((sigma - 1 : ℝ) : ℂ) + (t : ℂ) * I) := by
    simp [fordShiftedDetectorCenter]
    ring
  rw [harg]
  exact fordCotKernel_re_le_inv_sq_height heta (by linarith)
    (by linarith) ht

theorem eventually_exists_fordLocalDisk_detector_rightPoleBound
    {t R : ℝ} (ht : 0 < t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T → 8 ≤ T →
        t + 2 * (3 * R) / Real.pi ≤ T →
        ∃ eta' RUpper RLower : ℝ,
          (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
          RUpper ∈ Set.Icc T (T + 1) ∧
          RLower ∈ Set.Icc T (T + 1) ∧
          -(fordDetectorZetaLogDeriv
              (fordShiftedDetectorCenter
                (1 + (6421 / 10000 : ℝ) * R) t)).re <
            -((fordLocalDiskZeroCount t R : ℝ) *
              (fordLocalCotUniformLowerConstant / R)) +
            eta' / (Real.pi * t ^ 2) +
            Real.log (1 + 1 / (3 * R)) / (2 * eta') +
            fordShiftedDetectorPhysicalVerticalBulk eta'
              (1 + (6421 / 10000 : ℝ) * R) t
              (-eta' : ℂ) (-RLower) RUpper + ε := by
  intro ε hε
  obtain ⟨T0, hT0⟩ :=
    eventually_exists_fordLocalDisk_detector_rightBound ht hR hRUpper ε hε
  refine ⟨T0, ?_⟩
  intro T hT0T hT hTlarge
  obtain ⟨eta', RUpper, RLower, hetaLower, hetaUpper,
      hRU, hRL, hdet⟩ := hT0 hT0T hT hTlarge
  have hetaPos : 0 < eta' := (mul_pos (by norm_num) hR).trans hetaLower
  have hsigma : 1 ≤ 1 + (6421 / 10000 : ℝ) * R := by nlinarith
  have hsigmaUpper : 1 + (6421 / 10000 : ℝ) * R ≤ 1 + eta' := by
    nlinarith
  have hpole := fordShiftedDetector_poleCorrection_le_inv_sq
    (eta := eta') (sigma := 1 + (6421 / 10000 : ℝ) * R)
    (t := t) hetaPos hsigma hsigmaUpper ht
  refine ⟨eta', RUpper, RLower, hetaLower, hetaUpper, hRU, hRL, ?_⟩
  exact hdet.trans_le (by linarith [hpole])

#print axioms fordShiftedDetector_poleCorrection_le_inv_sq
#print axioms eventually_exists_fordLocalDisk_detector_rightPoleBound

end

end GafniTao
