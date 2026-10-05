import DongWangWangZhang2026.GammaLogBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Gamma quotients on the source horizontal segment

The real logarithm of the norm has derivative Re(Γ'/Γ). Its bounded
horizontal derivative gives the source ratio without choosing a logarithm
branch. The two generic derivative proofs are adapted from the inspected
node-74 FordLogNormDerivative; that module's larger import chain is not used.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set

/-- Differentiate the squared norm along a real-parameter complex path. -/
theorem hasDerivAt_complex_normSq
    {g : ℝ → ℂ} {x : ℝ} {g' : ℂ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun u => Complex.normSq (g u))
      (2 * (starRingEnd ℂ (g x) * g').re) x := by
  have hre : HasDerivAt (fun u => (g u).re) g'.re x := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hg
  have him : HasDerivAt (fun u => (g u).im) g'.im x := by
    simpa only [Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hg
  simp only [Complex.normSq_apply]
  convert (hre.mul hre).add (him.mul him) using 1
  simp [Complex.mul_re]
  ring

/-- The branch-independent real logarithm differentiates by the real log derivative. -/
theorem hasDerivAt_real_log_norm
    {g : ℝ → ℂ} {x : ℝ} {g' : ℂ} (hg : HasDerivAt g g' x)
    (hgne : g x ≠ 0) :
    HasDerivAt (fun u => Real.log ‖g u‖) (g' / g x).re x := by
  have hsq := hasDerivAt_complex_normSq hg
  have hsqne : Complex.normSq (g x) ≠ 0 :=
    fun h => hgne (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hsqne).comp x hsq
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hfun : (fun u => Real.log ‖g u‖) =
      fun u => (1 / 2 : ℝ) * Real.log (Complex.normSq (g u)) := by
    funext u
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    ring
  rw [hfun]
  convert hhalf using 1
  rw [Complex.div_re, Complex.normSq_apply]
  simp [Complex.mul_re]
  field_simp [hsqne]

/-- Exact horizontal derivative of the gamma log norm in its zero-free half-plane. -/
theorem hasDerivAt_log_norm_Gamma_horizontal {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log ‖Gamma ((x : ℂ) + (u : ℂ) * I / 2)‖)
      (digamma ((σ : ℂ) + (u : ℂ) * I / 2)).re σ := by
  have hre : 0 < ((σ : ℂ) + (u : ℂ) * I / 2).re := by simpa using hσ
  have hd := differentiableAt_Gamma ((σ : ℂ) + (u : ℂ) * I / 2) (fun n => by
    intro h
    have hr := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hp : HasDerivAt (fun x : ℝ => Gamma ((x : ℂ) + (u : ℂ) * I / 2))
      (deriv Gamma ((σ : ℂ) + (u : ℂ) * I / 2)) σ := by
    simpa using hd.hasDerivAt.comp σ
      (Complex.ofRealCLM.hasDerivAt.add_const ((u : ℂ) * I / 2))
  exact hasDerivAt_real_log_norm hp (Gamma_ne_zero_of_re_pos hre)

/-- Uniform coefficient-one bound on the complete source gamma segment. -/
theorem re_digamma_source_segment_upper {σ u : ℝ}
    (hσ : σ ∈ Icc (1 / 4 : ℝ) (3 / 4)) (hu : 2 ≤ |u|) :
    (digamma ((σ : ℂ) + (u : ℂ) * I / 2)).re ≤
      Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|) := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I / 2
  have hre : z.re = σ := by simp [z]
  have him : z.im = u / 2 := by simp [z]
  have hb := (abs_le.mp (abs_re_digamma_sub_log_norm_le
    (z := z) (by simpa [hre] using hσ.1))).2
  have hn : ‖z‖ + 2 ≤ 2 + |u| := by
    have ht := norm_le_abs_re_add_abs_im z
    rw [hre, him, abs_of_nonneg (by linarith [hσ.1] : 0 ≤ σ),
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith [hσ.2]
  have hl := Real.log_le_log (by positivity : 0 < ‖z‖ + 2) hn
  linarith

/-- Gamma log-norm growth has exactly the source segment length λ. -/
theorem log_norm_Gamma_source_difference_le {a u : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    Real.log ‖Gamma ((((1 + a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ -
      Real.log ‖Gamma ((((1 - a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ ≤
        a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|)) := by
  let f : ℝ → ℝ := fun x => Real.log ‖Gamma ((x : ℂ) + (u : ℂ) * I / 2)‖
  have hd (x : ℝ) (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
      HasDerivAt f (digamma ((x : ℂ) + (u : ℂ) * I / 2)).re x :=
    hasDerivAt_log_norm_Gamma_horizontal (by linarith [hx.1]) u
  have hcont : ContinuousOn f (Icc (1 / 4 : ℝ) (3 / 4)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc (1 / 4 : ℝ) (3 / 4))) :=
    fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hbound (x : ℝ) (hx : x ∈ interior (Icc (1 / 4 : ℝ) (3 / 4))) :
      deriv f x ≤ Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|) := by
    rw [(hd x (interior_subset hx)).deriv]
    exact re_digamma_source_segment_upper (interior_subset hx) hu
  have hleft : (1 - a) / 2 ∈ Icc (1 / 4 : ℝ) (3 / 4) := by constructor <;> linarith
  have hright : (1 + a) / 2 ∈ Icc (1 / 4 : ℝ) (3 / 4) := by constructor <;> linarith
  have h := (convex_Icc (1 / 4 : ℝ) (3 / 4)).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hbound _ hleft _ hright (by linarith)
  have hc (b : ℝ) : (((b / 2 : ℝ) : ℂ) + (u : ℂ) * I / 2) =
      ((b : ℂ) + (u : ℂ) * I) / 2 := by push_cast; ring
  dsimp only [f] at h
  rw [hc, hc, show (1 + a) / 2 - (1 - a) / 2 = a by ring] at h
  simpa only [mul_comm] using h

/-- The actual gamma quotient bound with the source logarithmic coefficient. -/
theorem norm_Gamma_source_ratio_le {a u : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    ‖Gamma ((((1 + a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ ≤
      ‖Gamma ((((1 - a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ *
        Real.exp (a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|))) := by
  have hp : 0 < ‖Gamma ((((1 + a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ := by
    apply norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos _)
    simp only [div_ofNat_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_self, add_zero]
    positivity
  have hm : 0 < ‖Gamma ((((1 - a : ℝ) : ℂ) + (u : ℂ) * I) / 2)‖ := by
    apply norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos _)
    simp only [div_ofNat_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_self, add_zero]
    linarith
  have h := Real.exp_le_exp.mpr (log_norm_Gamma_source_difference_le ha ha2 hu)
  rw [Real.exp_sub, Real.exp_log hp, Real.exp_log hm, div_le_iff₀ hm] at h
  simpa only [mul_comm] using h

/-- The pi factor in completed gamma can only improve the source quotient. -/
theorem norm_GammaReal_source_ratio_le {a u : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    ‖Gammaℝ (((1 + a : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      ‖Gammaℝ (((1 - a : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        Real.exp (a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|))) := by
  have h := norm_Gamma_source_ratio_le ha ha2 hu
  have hp : Real.pi ^ (-(1 + a) / 2) ≤ Real.pi ^ (-(1 - a) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.one_le_pi_div_two]) (by linarith)
  simp only [Gammaℝ, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    div_ofNat_re, neg_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    mul_zero, zero_mul, sub_self, add_zero]
  exact (mul_le_mul hp h (norm_nonneg _) (Real.rpow_pos_of_pos Real.pi_pos _).le).trans_eq
    (by ring)

/-- The lower digamma bound supplies the logarithm canceled in zero repulsion. -/
theorem re_digamma_source_lower {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.log (2 + |u|) - (14 + |Real.eulerMascheroniConstant| + Real.log 2) ≤
      (digamma ((((1 + a : ℝ) : ℂ) + (u : ℂ) * I) / 2)).re := by
  let z : ℂ := (((1 + a : ℝ) : ℂ) + (u : ℂ) * I) / 2
  have hre : z.re = (1 + a) / 2 := by simp [z]
  have him : z.im = u / 2 := by simp [z]
  have hb := (abs_le.mp (abs_re_digamma_sub_log_norm_le
    (z := z) (by rw [hre]; linarith))).1
  have hn : (2 + |u|) / 2 ≤ ‖z‖ + 2 := by
    have ht := abs_im_le_norm z
    rw [him, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith
  have hl := Real.log_le_log (by positivity : 0 < (2 + |u|) / 2) hn
  rw [Real.log_div (by positivity) (by norm_num)] at hl
  linarith

end
end DongWangWangZhang2026
