import TaoTrudgianYang2025.ZetaMellinShift

/-!
# Mellin boundary control on arbitrary fixed lines below one

The actual Abel formula controls zeta on every line 1/2 <= c < 1.
The constant retains its distance from the pole; no uniformity at c=1
or assumed growth estimate is asserted.
-/

noncomputable section
open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem norm_zeta_mellin_left_boundary {c : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c < 1) (v : ℝ) :
    ‖riemannZeta ((c : ℂ)+(v : ℂ)*I)‖ ≤ (1/(1-c)+2)*(1+|v|) := by
  let s : ℂ := (c : ℂ)+(v : ℂ)*I
  have hre : s.re = c := by simp [s]
  have hcp : 0 < c := by linarith
  have hgap : 0 < 1-c := by linarith
  have hden : 1-c ≤ ‖s-1‖ := by
    calc
      _ = |(s-1).re| := by rw [sub_re,hre,one_re,abs_of_neg (by linarith)]; ring
      _ ≤ _ := Complex.abs_re_le_norm _
  have hs : s ≠ 1 := by intro hh; rw [hh,sub_self,norm_zero] at hden; linarith
  have hrem : ‖abelZetaRemainder s‖ ≤ 2 := by
    apply (norm_abelZetaRemainder_le (hre.symm ▸ hcp)).trans
    rw [hre]
    exact (div_le_iff₀ hcp).mpr (by linarith)
  have hnorm : ‖s‖ ≤ 1+|v| := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    have he : |s.re|+|s.im| = c+|v| := by simp [s,abs_of_pos hcp]
    rw [he] at hh
    linarith
  change ‖riemannZeta s‖ ≤ _
  rw [riemannZeta_eq_abel (hre.symm ▸ hcp) hs]
  calc
    _ ≤ ‖s/(s-1)‖+‖s*abelZetaRemainder s‖ := norm_sub_le _ _
    _ ≤ ‖s‖/(1-c)+‖s‖*2 := by
      rw [norm_div,norm_mul]
      exact add_le_add
        (div_le_div_of_nonneg_left (norm_nonneg s) hgap hden)
        (mul_le_mul_of_nonneg_left hrem (norm_nonneg s))
    _ ≤ (1+|v|)/(1-c)+(1+|v|)*2 := by gcongr
    _ = _ := by ring

theorem integrable_zetaMellin_left_boundary {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {c : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    Integrable (fun u : ℝ => zetaMellinIntegrand g t ((c : ℂ)+(u : ℂ)*I)) := by
  have hcont : Continuous
      (fun u : ℝ => zetaMellinIntegrand g t ((c : ℂ)+(u : ℂ)*I)) := by
    apply Continuous.mul
    · rw [continuous_iff_continuousAt]
      intro u
      have hne : ((c : ℂ)+(u : ℂ)*I)+(t : ℂ)*I ≠ 1 := by
        intro he
        have hh := congrArg Complex.re he
        simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,
          zero_mul,sub_zero,add_zero,one_re] at hh
        linarith
      exact (differentiableAt_riemannZeta hne).continuousAt.comp
        (f := fun x : ℝ => (c : ℂ)+(x : ℂ)*I+(t : ℂ)*I) (by fun_prop)
    · exact hg.differentiable_mellin.continuous.comp (by fun_prop)
  let K : ℝ := 1/(1-c)+2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdom := (hg.integrable_sqWeight_norm_mellin c).const_mul (K*(1+|t|))
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards with u
  have hz := norm_zeta_mellin_left_boundary hc hc1 (u+t)
  have harg : ((c : ℂ)+(u : ℂ)*I)+(t : ℂ)*I =
      (c : ℂ)+((u+t : ℝ) : ℂ)*I := by push_cast; ring
  have hu : 0 ≤ |u| := abs_nonneg u
  have ht : 0 ≤ |t| := abs_nonneg t
  have hw : 1+|u+t| ≤ (1+|t|)*(1+|u|)^2 := by
    have hh := abs_add_le u t
    nlinarith [sq_nonneg |u|,mul_nonneg ht hu,mul_nonneg ht (sq_nonneg |u|)]
  unfold zetaMellinIntegrand
  rw [norm_mul,harg]
  calc
    _ ≤ (K*((1+|t|)*(1+|u|)^2))*‖mellin g ((c : ℂ)+(u : ℂ)*I)‖ :=
      mul_le_mul_of_nonneg_right
        (hz.trans (mul_le_mul_of_nonneg_left hw hK)) (norm_nonneg _)
    _ = _ := by ring

end TaoTrudgianYang2025

