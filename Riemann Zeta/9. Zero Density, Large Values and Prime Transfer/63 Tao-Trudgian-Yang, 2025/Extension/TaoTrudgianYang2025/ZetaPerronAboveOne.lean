import TaoTrudgianYang2025.ZetaMellinOrderTails

/-!
# General-line Perron entry above height exponent one

For each tau>1 a genuine cutoff order is chosen. Both the pole and the
far integral are bounded by fixed constants, then absorbed into the
actual large value. No tail estimate is left as a hypothesis.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.polynomial_norm_le_lineConvolution_order_errors
    (P : ZetaLargeValuePattern) {a b : ℕ}
    (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (j : ℕ)
    {t : ℝ} (ht : t ∈ Icc P.T (2*P.T)) :
    ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 c*P.N^c*zetaLineMomentConvolution c P.T t+
      zetaCutoffMellinConstant 4 1*P.N^4/(1+|t|)^4+
      zetaLineTailConstant j c*P.N^(c+(j : ℝ)+2)/P.T^(j+1) := by
  have hidentity := P.polynomial_eq_general_zeta_mellin hactive hc hc1 t
  simp_rw [← zetaCutoffLineIntegrand_eq] at hidentity
  rw [hidentity]
  have hsplit := integral_add_compl (s := zetaMellinSourceWindow P.T t)
    measurableSet_Icc (P.integrable_cutoff_line_integrand hactive hc hc1 t)
  have hwhole : ‖∫ u : ℝ, zetaCutoffLineIntegrand a b c t u‖ ≤
      zetaCutoffMellinConstant 1 c*P.N^c*zetaLineMomentConvolution c P.T t+
      zetaLineTailConstant j c*P.N^(c+(j : ℝ)+2)/P.T^(j+1) := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (P.cutoff_line_near_integral hactive hne hc hc1 t)
      (P.cutoff_line_order_far_integral hactive hne hc hc1 j ht))
  have hscalar : ‖(1/(2*Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have htri := norm_add_le
    (mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1-(t : ℂ)*I))
    ((1/(2*Real.pi) : ℂ)*∫ u : ℝ, zetaCutoffLineIntegrand a b c t u)
  rw [norm_mul] at htri
  have hres := P.cutoff_mellin_residue_bound hactive hne (j := 4) (by norm_num) t
  have hscale := mul_le_mul_of_nonneg_right hscalar
    (norm_nonneg (∫ u : ℝ, zetaCutoffLineIntegrand a b c t u))
  nlinarith

theorem ZetaLargeValuePattern.line_order_perron_entry (P : ZetaLargeValuePattern)
    {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (j : ℕ)
    (hNT : P.N ≤ P.T) (hscale : P.N^(c+(j : ℝ)+2) ≤ P.T^(j+1))
    (hvalue : 2*(zetaCutoffMellinConstant 4 1+zetaLineTailConstant j c) ≤ P.V)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V ≤ zetaLinePerronConstant c*P.N^c*zetaLineMomentConvolution c P.T t := by
  obtain ⟨a,b,hactive⟩ := P.active_isInterval
  have hne := P.active_nonempty_of_mem_ordinates ht
  have hinterval : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hresPower : P.N^4 ≤ (1+|t|)^4 :=
    pow_le_pow_left₀ hNpos.le (by linarith [hinterval.1,le_abs_self t]) 4
  have hres : zetaCutoffMellinConstant 4 1*P.N^4/(1+|t|)^4 ≤
      zetaCutoffMellinConstant 4 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (1+|t|)^4)).mpr
    exact mul_le_mul_of_nonneg_left hresPower (zetaCutoffMellinConstant_pos _ _).le
  have hfar : zetaLineTailConstant j c*P.N^(c+(j : ℝ)+2)/P.T^(j+1) ≤
      zetaLineTailConstant j c := by
    apply (div_le_iff₀ (pow_pos P.T_pos _)).mpr
    exact mul_le_mul_of_nonneg_left hscale (zetaLineTailConstant_pos j hc1).le
  have hpoly := (P.large t ht).trans
    (P.polynomial_norm_le_lineConvolution_order_errors hactive hne hc hc1 j hinterval)
  unfold zetaLinePerronConstant
  nlinarith

theorem exists_zetaLinePerron_aboveOne_uniform_threshold {c τ : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c < 1) (hτ : 1 < τ) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ σ δ : ℝ, 1/2 ≤ σ → δ ≤ min (1/4) ((τ-1)/4) →
        P.N^(τ-δ) ≤ P.T → P.N^(σ-δ) ≤ P.V →
          ∀ t ∈ P.ordinates,
            P.V ≤ zetaLinePerronConstant c*P.N^c*zetaLineMomentConvolution c P.T t := by
  let a : ℝ := (τ+1)/2
  have ha : 1 < a := by dsimp [a]; linarith
  obtain ⟨j,hj⟩ := exists_nat_gt ((c+1)/(a-1))
  have hjmul : c+1 < (j : ℝ)*(a-1) := (div_lt_iff₀ (by linarith)).mp hj
  have hjexp : c+(j : ℝ)+2 ≤ a*((j : ℝ)+1) := by nlinarith
  have hevent : ∀ᶠ N : ℝ in atTop,
      2*(zetaCutoffMellinConstant 4 1+zetaLineTailConstant j c) ≤ N^(1/4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually
      (eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro P hN σ δ hσ hδ hT hV t ht
  have hδone : δ ≤ 1/4 := hδ.trans (min_le_left _ _)
  have hδgap : δ ≤ (τ-1)/4 := hδ.trans (min_le_right _ _)
  have haτ : a ≤ τ-δ := by dsimp [a]; linarith
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have haScale : P.N^a ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le haτ).trans hT
  apply P.line_order_perron_entry hc hc1 j _ _ _ ht
  · apply le_trans _ haScale
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le ha.le
  · calc
      _ ≤ P.N^(a*((j : ℝ)+1)) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hjexp
      _ = (P.N^a)^(j+1) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
        push_cast
        rfl
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le a) haScale _
  · exact (hN₀ P.N ((le_max_right _ _).trans hN)).trans
      ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
        (by linarith : (1/4 : ℝ) ≤ σ-δ)).trans hV)

end TaoTrudgianYang2025
