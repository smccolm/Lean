import TaoTrudgianYang2025.ZetaOneLinePolynomial

/-!
# Euler--Maclaurin first moment on the line through the zeta pole

All integration intervals lie above height zero, away from the pole.
The truncation point is fixed throughout each interval.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem continuousOn_zetaOneLine_positive :
    ContinuousOn (fun t : ℝ => riemannZeta (1+(t : ℂ)*I)) (Ioi 0) := by
  intro t ht
  have hne : 1+(t : ℂ)*I ≠ 1 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp only [add_im,one_im,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,
      mul_zero,add_zero,zero_add] at hi
    exact (ne_of_gt ht) hi
  exact ((differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun u : ℝ => 1+(u : ℂ)*I) (by fun_prop)).continuousWithinAt

theorem intervalIntegrable_zetaOneLine {H : ℝ} (hH : 0 < H) :
    IntervalIntegrable (fun t : ℝ => riemannZeta (1+(t : ℂ)*I)) volume H (2*H) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_zetaOneLine_positive.mono
  intro t ht
  rw [Set.uIcc_of_le (by linarith : H ≤ 2*H)] at ht
  exact hH.trans_le ht.1

theorem norm_zetaOneLine_sub_prefix {b : ℕ} (hb : 1 ≤ b)
    {H t : ℝ} (hH : 1 ≤ H) (ht : t ∈ Icc H (2*H)) :
    ‖riemannZeta (1+(t : ℂ)*I) -
      ∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t‖ ≤
        1/H+(1+2*H)/(b : ℝ) := by
  let s : ℂ := 1+(t : ℂ)*I
  have htp : 0 < t := by linarith [ht.1]
  have hbp : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hre : s.re = 1 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp [s] at hi
    linarith
  have he := riemannZeta_truncation hb (s := s) (by rw [hre]; norm_num) hs1
  have hprefix : (∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t) =
      riemannZeta s+(b : ℂ)^(1-s)/(1-s)+s*abelZetaTail b s := he
  have htail : ‖abelZetaTail b s‖ ≤ (b : ℝ)⁻¹ := by
    have hh := norm_abelZetaTail_le (b := (b : ℝ))
      (by exact_mod_cast hb) (s := s) (by rw [hre]; norm_num)
    simpa only [hre,Real.rpow_neg_one,div_one] using hh
  have hsNorm : ‖s‖ ≤ 1+2*H := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    have heq : |s.re|+|s.im| = 1+t := by simp [s,abs_of_pos htp]
    rw [heq] at hh
    linarith [ht.2]
  have hden : ‖1-s‖ = t := by
    have hh : 1-s = -(t : ℂ)*I := by dsimp [s]; ring
    rw [hh,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htp,norm_I,mul_one]
  have hpole : ‖(b : ℂ)^(1-s)/(1-s)‖ ≤ 1/H := by
    rw [norm_div,hden]
    have hn : ‖(b : ℂ)^(1-s)‖ = 1 := by
      have hh := norm_cpow_eq_rpow_re_of_pos hbp (1-s)
      simpa [hre] using hh
    rw [hn]
    exact one_div_le_one_div_of_le (by linarith) ht.1
  change ‖riemannZeta s - _‖ ≤ _
  rw [hprefix]
  have hdiff : riemannZeta s-(riemannZeta s+(b : ℂ)^(1-s)/(1-s)+s*abelZetaTail b s) =
      -((b : ℂ)^(1-s)/(1-s)+s*abelZetaTail b s) := by ring
  rw [hdiff,norm_neg]
  calc
    _ ≤ ‖(b : ℂ)^(1-s)/(1-s)‖+‖s*abelZetaTail b s‖ := norm_add_le _ _
    _ ≤ 1/H+(1+2*H)/(b : ℝ) := by
      rw [norm_mul,div_eq_mul_inv (1+2*H)]
      exact add_le_add hpole (mul_le_mul hsNorm htail (norm_nonneg _) (by linarith))

theorem norm_integral_zetaOneLine_sub_length {b : ℕ} (hb : 1 ≤ b)
    {H : ℝ} (hH : 1 ≤ H) :
    ‖(∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))-(H : ℂ)‖ ≤
      (1/H+(1+2*H)/(b : ℝ))*H+(2/Real.log 2)*(1+Real.log (b : ℝ)) := by
  have hHpos : 0 < H := by linarith
  have hPrefix : IntervalIntegrable
      (fun t : ℝ => ∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t) volume H (2*H) :=
    (continuous_finsetSum _ (fun n hn =>
      continuous_zetaOneLineTerm (by
        have hh := (Finset.mem_Icc.mp hn).1
        omega))).intervalIntegrable H (2*H)
  have herror : ‖(∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I)) -
      (∫ t in H..2*H, ∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t)‖ ≤
      (1/H+(1+2*H)/(b : ℝ))*H := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_zetaOneLine hHpos) hPrefix]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => riemannZeta (1+(t : ℂ)*I) -
        ∑ n ∈ Finset.Icc 1 b, zetaOneLineTerm n t)
      (a := H) (b := 2*H) (C := 1/H+(1+2*H)/(b : ℝ)) (fun t ht => by
        have htc := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le (by linarith : H ≤ 2*H)] at htc
        exact norm_zetaOneLine_sub_prefix hb hH htc)
    simpa only [show 2*H-H = H by ring,abs_of_pos hHpos] using hh
  have hp := norm_integral_zetaOneLinePrefix_sub_length hb H (2*H)
  simp only [show 2*H-H = H by ring] at hp
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add herror hp)

end TaoTrudgianYang2025
