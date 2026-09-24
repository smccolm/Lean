import TaoTrudgianYang2025.ZetaSharpCoefficients

/-! Sharp truncation at arbitrary points of the closed critical strip. -/

noncomputable section
open Complex
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem norm_zeta_le_sharp_sum_add {σ t : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ht : 1 ≤ t) :
    ‖riemannZeta ((σ : ℂ)+(t : ℂ)*I)‖ ≤
      ‖∑ n ∈ Finset.Icc 1 ⌊sharpZetaCutoff t⌋₊,
        (n : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))‖+150 := by
  let s : ℂ := (σ : ℂ)+(t : ℂ)*I
  let a := sharpZetaCutoff t
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hs1 : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    rw [him,Complex.one_im] at hi
    linarith
  have ha1 : 1 ≤ a := by
    dsimp [a]
    linarith [four_mul_lt_sharpZetaCutoff t]
  have hap : 0 < a := zero_lt_one.trans_le ha1
  have ha6 : a ≤ 6*t := sharpZetaCutoff_le_six_mul (by linarith)
  have haim : a > |s.im|/(2*Real.pi) := by
    rw [him,abs_of_pos htp]
    apply (div_lt_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    have hcut : 4*t < a := four_mul_lt_sharpZetaCutoff t
    nlinarith [Real.pi_gt_three]
  have hphase := sharpZetaPhase_mem_of_im_range
    (T:=t) (s:=s) (by linarith) (by rw [him]; constructor <;> linarith)
  have hden : t ≤ ‖1-s‖ := by
    have hi := Complex.abs_im_le_norm (1-s)
    simpa only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg,him,
      abs_of_pos htp] using hi
  have hdenp : 0 < ‖1-s‖ := htp.trans_le hden
  have hpole : ‖((a : ℂ)^(1-s))/(1-s)‖ ≤ 6 := by
    rw [norm_div,norm_cpow_eq_rpow_re_of_pos hap]
    simp only [Complex.sub_re,Complex.one_re,hre]
    apply (div_le_iff₀ hdenp).mpr
    have hp : a^(1-σ) ≤ a := by
      convert Real.rpow_le_rpow_of_exponent_le ha1 (show 1-σ ≤ 1 by linarith) using 1
      rw [Real.rpow_one]
    linarith
  have hboundary : ‖sharpZetaBoundaryCoeff s a*(a : ℂ)^(-s)‖ ≤ 14 := by
    rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hap]
    simp only [Complex.neg_re,hre]
    have hb := sharpZetaBoundaryCoeff_le_of_phase s a hphase
    have hw : a^(-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
    calc
      _ ≤ 14*1 := mul_le_mul hb hw (Real.rpow_nonneg hap.le _) (by norm_num)
      _ = 14 := by norm_num
  obtain ⟨E,he,hE⟩ := riemannZeta_sharp_halfInteger_truncation hs1
    (by simpa only [hre] using hσ0) hap (sharpZetaCutoff_isHalfInteger t) haim
  have herror : ‖E‖ ≤ 129 := by
    have hc := sharpZetaErrorCoeff_le_of_phase s a hphase
      (by simpa only [hre] using hσ0) (by simpa only [hre] using hσ1)
    have hp : 1 ≤ a^(s.re+1) := Real.one_le_rpow ha1 (by rw [hre]; linarith)
    apply hE.trans
    apply (div_le_iff₀ (by positivity : 0 < a^(s.re+1))).mpr
    nlinarith
  change ‖riemannZeta s‖ ≤ ‖∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ)^(-s)‖+150
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ)^(-s)) -
          (a : ℂ)^(1-s)/(1-s) - sharpZetaBoundaryCoeff s a*(a : ℂ)^(-s)‖+‖E‖ :=
      norm_add_le _ _
    _ ≤ (‖(∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ)^(-s)) -
          (a : ℂ)^(1-s)/(1-s)‖+‖sharpZetaBoundaryCoeff s a*(a : ℂ)^(-s)‖)+‖E‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ)^(-s)‖+
          ‖(a : ℂ)^(1-s)/(1-s)‖)+
          ‖sharpZetaBoundaryCoeff s a*(a : ℂ)^(-s)‖)+‖E‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ ‖∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ)^(-s)‖+150 := by linarith

end TaoTrudgianYang2025
