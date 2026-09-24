import TaoTrudgianYang2025.ZetaReflectionLocalizedCompletion

/-! Endpoint-free actual-pattern reflection with a uniform tail constant. -/

noncomputable section
open Complex MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaReflectionTailConstant (j : ℕ) : ℝ :=
  12*5^j*2^(j+1)*zetaCutoffDerivativeMass (j+2)/((j : ℝ)+1)

theorem zetaReflectionTailConstant_nonneg (j : ℕ) :
    0 ≤ zetaReflectionTailConstant j := by
  unfold zetaReflectionTailConstant
  have := zetaCutoffDerivativeMass_nonneg (j+2)
  positivity

theorem zetaReflectionConvolution_nonneg (S : Finset ℕ) (T t : ℝ) :
    0 ≤ zetaReflectionConvolution S T t :=
  integral_nonneg fun u => div_nonneg (norm_nonneg _) (by positivity)

theorem commonReflection_tail_scale {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hscale : 1 ≤ T/(4*Real.pi*N)) {b : ℕ} (hb : (b : ℝ) < T/(Real.pi*N)) (j : ℕ) :
    2*((zetaReflectionCommonInterval T N).card : ℝ)*((b : ℝ)+1/2)^j*
        zetaCutoffDerivativeMass (j+2)/(((j : ℝ)+1)*(T/2)^(j+1)) ≤
      zetaReflectionTailConstant j/(4*Real.pi*N)^(j+1) := by
  let M := T/(4*Real.pi*N)
  have hM : 0 < M := by dsimp [M]; positivity
  have he : T/(Real.pi*N) = 4*M := by dsimp [M]; field_simp
  have hb' : (b : ℝ)+1/2 ≤ 5*M := by rw [he] at hb; dsimp [M] at *; linarith
  have hcard := zetaReflectionCommonInterval_card_bound hT.le hN hscale
  have hmass := zetaCutoffDerivativeMass_nonneg (j+2)
  calc
    _ ≤ 2*(6*M)*(5*M)^j*zetaCutoffDerivativeMass (j+2)/
        (((j : ℝ)+1)*(T/2)^(j+1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hmass
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcard (by norm_num))
        (pow_le_pow_left₀ (by positivity) hb' j) (by positivity) (by positivity)
    _ = _ := by
      dsimp [M,zetaReflectionTailConstant]
      rw [mul_pow,div_pow,div_pow,pow_succ T j]
      field_simp
      ring

theorem moving_reciprocal_interval_uniform_localized {T N t : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hscale : 1 ≤ T/(4*Real.pi*N))
    (ht : t ∈ Icc T (2*T)) {J : Finset ℕ} (hJ : IsIntegerInterval J)
    (hw : ∀ n ∈ J, t/(4*Real.pi*N) < (n : ℝ) ∧ (n : ℝ) < t/(2*Real.pi*N))
    (j : ℕ) :
    ‖∑ n ∈ J, (n : ℂ)⁻¹*dirichletPhase n t‖ ≤
      (4*zetaCutoffDerivativeMass 1/(T/(4*Real.pi*N)))*
        zetaReflectionConvolution (zetaReflectionCommonInterval T N) T t+
      zetaReflectionTailConstant j/(4*Real.pi*N)^(j+1) := by
  by_cases hne : J.Nonempty
  · obtain ⟨a,b,ha,hab,hint,hleft,hright⟩ :=
      moving_interval_cutoff_endpoints hT hN ht.1 ht.2 hJ hne hw
    have hsub := logarithmic_moving_interval_subset_common hT hN ht.1 ht.2 hw
    rw [hint]
    exact (reciprocal_interval_norm_le_common_convolution ha hab hscale hleft
      (zetaReflectionCommonInterval T N) (fun n hn =>
        ne_of_gt (zetaReflectionCommonInterval_positive T N hn)) (hint ▸ hsub) hT ht j).trans
      (add_le_add le_rfl (commonReflection_tail_scale hT hN hscale hright j))
  · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hzero,Finset.sum_empty,norm_zero]
    have := zetaCutoffDerivativeMass_nonneg 1
    have := zetaReflectionConvolution_nonneg (zetaReflectionCommonInterval T N) T t
    have := zetaReflectionTailConstant_nonneg j
    positivity

theorem zetaPattern_uniform_localized_reflection {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ZetaLargeValuePattern, 2*Real.pi ≤ P.T →
      1 ≤ P.T/(4*Real.pi*P.N) → ∀ t ∈ P.ordinates, ∀ j : ℕ,
        P.V ≤ Real.sqrt (t/(2*Real.pi))*
          ((4*zetaCutoffDerivativeMass 1/(P.T/(4*Real.pi*P.N)))*
            zetaReflectionConvolution (zetaReflectionCommonInterval P.T P.N) P.T t+
            zetaReflectionTailConstant j/(4*Real.pi*P.N)^(j+1))+
          C*(P.N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) := by
  obtain ⟨C,hC,hentry⟩ := zetaPattern_sharp_log_reflection_entry hε
  refine ⟨C,hC,?_⟩
  intro P hPT hscale t ht j
  obtain ⟨a,b,_,hsource⟩ := hentry P hPT
  obtain ⟨hint,hw,hbound⟩ := hsource t ht
  have htime : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hlocal := moving_reciprocal_interval_uniform_localized P.T_pos
    (zero_lt_one.trans P.one_lt_N) hscale htime hint hw j
  exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_left hlocal (Real.sqrt_nonneg _)) le_rfl)

end TaoTrudgianYang2025
