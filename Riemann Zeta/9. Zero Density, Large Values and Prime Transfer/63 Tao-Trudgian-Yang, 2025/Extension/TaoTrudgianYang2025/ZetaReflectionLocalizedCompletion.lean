import TaoTrudgianYang2025.ZetaReflectionKernelScale

/-! Localized coefficient-one convolution, with the entire tail retained. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaReflectionConvolution (S : Finset ℕ) (T t : ℝ) : ℝ :=
  ∫ u : ℝ in zetaMellinSourceWindow T t,
    ‖∑ n ∈ S, dirichletPhase n (t+u)‖/(1+|u|)

theorem continuous_reciprocalCompletion_phase_sum (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (t : ℝ) :
    Continuous (fun u : ℝ => ∑ n ∈ S, dirichletPhase n (t+u)) := by
  apply continuous_finsetSum
  intro n hn
  unfold dirichletPhase
  exact (by fun_prop : Continuous (fun u : ℝ => -(I*((t+u : ℝ) : ℂ)))).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (hS n hn)))

theorem integrableOn_zetaReflectionConvolution (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (T t : ℝ) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ S, dirichletPhase n (t+u)‖/(1+|u|))
      (zetaMellinSourceWindow T t) := by
  have hc := (continuous_reciprocalCompletion_phase_sum S hS t).norm.div
    (show Continuous (fun u : ℝ => 1+|u|) by fun_prop)
    (fun u => ne_of_gt (by positivity : 0 < 1+|u|))
  exact hc.continuousOn.integrableOn_Icc

theorem reciprocalCompletion_near_integral {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {M : ℝ} (hM : 1 ≤ M)
    (hleft : M < (a : ℝ)) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (T t : ℝ) :
    ‖∫ u : ℝ in zetaMellinSourceWindow T t,
      mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
        ∑ n ∈ S, dirichletPhase n (t+u)‖ ≤
      (4*zetaCutoffDerivativeMass 1/M)*zetaReflectionConvolution S T t := by
  have hi := integrable_reciprocal_completion_kernel (zetaIntervalCutoffTest a b ha) S hS t
  have hd := (integrableOn_zetaReflectionConvolution S hS T t).const_mul
    (4*zetaCutoffDerivativeMass 1/M)
  calc
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow T t,
        ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
          ∑ n ∈ S, dirichletPhase n (t+u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in zetaMellinSourceWindow T t,
        (4*zetaCutoffDerivativeMass 1/M)*(‖∑ n ∈ S, dirichletPhase n (t+u)‖/(1+|u|)) := by
      apply integral_mono_ae hi.norm.integrableOn hd
      filter_upwards with u
      rw [norm_mul]
      have h := mul_le_mul_of_nonneg_right (cutoff_negative_mellin_annulus_bound ha hab hM hleft u)
        (norm_nonneg (∑ n ∈ S, dirichletPhase n (t+u)))
      convert h using 1
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := integral_const_mul _ _

theorem reciprocal_interval_norm_le_common_convolution {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {M : ℝ} (hM : 1 ≤ M)
    (hleft : M < (a : ℝ)) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (hsub : Finset.Icc a b ⊆ S) {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc T (2*T)) (j : ℕ) :
    ‖∑ n ∈ Finset.Icc a b, (n : ℂ)⁻¹*dirichletPhase n t‖ ≤
      (4*zetaCutoffDerivativeMass 1/M)*zetaReflectionConvolution S T t+
        2*(S.card : ℝ)*((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2)/
          (((j : ℝ)+1)*(T/2)^(j+1)) := by
  have hi := integrable_reciprocal_completion_kernel (zetaIntervalCutoffTest a b ha) S hS t
  have hsplit := integral_add_compl (s := zetaMellinSourceWindow T t) measurableSet_Icc hi
  have hnear := reciprocalCompletion_near_integral ha hab hM hleft S hS T t
  have hfar := reciprocalCompletion_tail_integral ha hab S hS t (by linarith : 0 < T/2) j
    measurableSet_Icc.compl (zetaMellinSourceWindow_compl_subset ht)
  have hscalar : ‖(1/(2*Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  rw [reciprocal_interval_eq_common_mellin ha S hS hsub t,norm_mul]
  calc
    _ ≤ ‖∫ u : ℝ,
        mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((-1 : ℂ)+(u : ℂ)*I)*
          ∑ n ∈ S, dirichletPhase n (t+u)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
    _ ≤ _ := by
      rw [← hsplit]
      exact (norm_add_le _ _).trans (add_le_add hnear hfar)

end TaoTrudgianYang2025
