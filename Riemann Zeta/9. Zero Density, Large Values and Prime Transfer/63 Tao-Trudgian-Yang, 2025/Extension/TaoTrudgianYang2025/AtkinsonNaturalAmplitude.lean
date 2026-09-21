import TaoTrudgianYang2025.ZetaGaussianNaturalDerivatives

/-!
# Constructed natural-scale bounds for the actual saddle amplitude

The nonlinear oscillatory phase is not part of this amplitude.
The actual cutoff, Mellin profile, Gamma factor and quadratic Gaussian
give derivative scale G/sqrt(T) in the physical root variable.
-/

noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem IntervalC2Bound.comp_div {f : ℝ → ℂ} {a b M R c : ℝ}
    (hf : IntervalC2Bound f a b M R) (hc : 0 < c) :
    IntervalC2Bound (fun y => f (y / c)) (c * a) (c * b) M (R / c) := by
  have hmem {y : ℝ} (hy : y ∈ Icc (c * a) (c * b)) : y / c ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hc).2; nlinarith [hy.1]
    · apply (div_le_iff₀ hc).2; nlinarith [hy.2]
  have hg : ContDiff ℝ 2 (fun y : ℝ => y / c) := by fun_prop
  have hderiv : deriv (fun y : ℝ => y / c) = fun _ => 1 / c := by
    funext y
    exact ((hasDerivAt_id y).div_const c).deriv
  have hsecond (y : ℝ) : iteratedDeriv 2 (fun z : ℝ => z / c) y = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, deriv_const]
  refine ⟨hf.nonneg, div_nonneg hf.scale_nonneg hc.le,
    fun y hy => (hf.smooth (y / c) (hmem hy)).comp y hg.contDiffAt,
    fun y hy => hf.norm_le (y / c) (hmem hy), ?_, ?_⟩
  · intro y hy
    have hd : HasDerivAt (fun z => f (z / c)) ((1 / c : ℝ) • deriv f (y / c)) y :=
      ((hf.smooth (y / c) (hmem hy)).differentiableAt (by norm_num)).hasDerivAt.scomp
        y ((hasDerivAt_id y).div_const c)
    rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / c)]
    apply (mul_le_mul_of_nonneg_left (hf.deriv_le (y / c) (hmem hy)) (by positivity)).trans_eq
    ring
  · intro y hy
    rw [iteratedDeriv_two_comp_real (g := fun z => z / c)
      (hf.smooth (y / c) (hmem hy)) hg.contDiffAt,
      hderiv, hsecond, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    apply (mul_le_mul_of_nonneg_left (hf.second_le (y / c) (hmem hy)) (sq_nonneg (1 / c))).trans_eq
    ring

theorem IntervalC2Bound.norm_sub_le {f : ℝ → ℂ} {a b M R x y : ℝ}
    (hf : IntervalC2Bound f a b M R) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f y - f x‖ ≤ M * R * |y - x| := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf.smooth z hz).differentiableAt (by norm_num)) hf.deriv_le hx hy
  simpa only [Real.norm_eq_abs] using h

theorem exists_intervalC2Bound_zetaQuadraticLogGaussian_root_natural :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G
        (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi)))) (1 / 4) 1 (C * G) G := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_quadraticGaussian_profile_natural
    (v := atkinsonRootLogProfile) (a := 1 / 4) (b := 1) (by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      unfold atkinsonRootLogProfile
      fun_prop (disch := exact hu0.ne'))
  refine ⟨C, hC, ?_⟩
  intro T G hT hG hGT
  apply (hbound T G hT hG hGT).congr_of_eventuallyEq
  intro u hu
  filter_upwards [Ioi_mem_nhds (show 0 < u by linarith [hu.1])] with y hy
  exact (zetaQuadraticLogGaussian_root_rescale hT hy G).symm

theorem exists_intervalC2Bound_atkinsonPowerWeight_normalized_natural (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun u => atkinsonPowerWeight T G L α (T * u ^ 2))
        (1 / 4) 1 (C * G * T ^ (-α)) G := by
  obtain ⟨A, hA, hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile α
  obtain ⟨B, hB, hcutoff⟩ := exists_intervalC2Bound_zetaDivisorBandCutoff_root
  obtain ⟨D, hD, hgaussian⟩ := exists_intervalC2Bound_zetaQuadraticLogGaussian_root_natural
  let K : ℝ := 1 + 2 * Real.pi * Real.exp 1
  have hK : 1 ≤ K := by dsimp [K]; have := Real.exp_pos (1 : ℝ); nlinarith [Real.pi_pos]
  refine ⟨256 * A * B * K ^ 2 * D, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hG0 : 0 < G := by linarith
  have hc : IntervalC2Bound (fun u => (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ))
      (1 / 4) 1 (B * K ^ 2) G :=
    (hcutoff T G L hT hG0 hL hwidth).absorb_scale hK hG0.le
  have ht : IntervalC2Bound (fun _ : ℝ => ((T ^ (-α) : ℝ) : ℂ))
      (1 / 4) 1 (T ^ (-α)) G := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT _)] using
      intervalC2Bound_const ((T ^ (-α) : ℝ) : ℂ) (1 / 4) 1 hG0.le
  have hg : IntervalC2Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (1 / 4) 1 1 G := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC2Bound_const (zetaSquareReflectedGammaPhase T) (1 / 4) 1 hG0.le
  have h := (((ht.mul (hprofile.mono le_rfl hG)).mul hc).mul hg).mul (hgaussian T G hT hG hGT)
  have he : (fun u => atkinsonPowerWeight T G L α (T * u ^ 2)) =
      fun u => ((T ^ (-α) : ℝ) : ℂ) * atkinsonPowerProfile α (u ^ 2) *
        (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ) * zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi))) := by
    funext u
    unfold atkinsonPowerWeight
    rw [show T * u ^ 2 / T = u ^ 2 by field_simp]
  rw [he]
  convert h using 1
  ring

theorem exists_intervalC2Bound_atkinsonPowerWeight_root_natural (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (fun y => atkinsonPowerWeight T G L α (y ^ 2))
        (Real.sqrt T / 4) (Real.sqrt T) (C * G * T ^ (-α)) (G / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_normalized_natural α
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have h := (hbound T G L hT hG hGT hL hwidth).comp_div hs
  have he : (fun y => atkinsonPowerWeight T G L α (T * (y / Real.sqrt T) ^ 2)) =
      fun y => atkinsonPowerWeight T G L α (y ^ 2) := by
    funext y
    congr 1
    rw [div_pow, Real.sq_sqrt hT.le]
    field_simp
  simpa only [he, mul_one, mul_one_div] using h

end TaoTrudgianYang2025
