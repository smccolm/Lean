import TaoTrudgianYang2025.ZetaGlobalConvolution

/-! The actual far-height interval moment, uniform over separated samples. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem norm_zetaInterval_le_global_convolution
    (N : ℕ) (I : Finset ℕ) (T t : ℝ) (hN : 1 < N)
    (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2*N))
    (hscale : (N : ℝ)^(11/8 : ℝ) ≤ t) (htT : t ≤ T) :
    ‖∑ n ∈ I, dirichletPhase n t‖ ≤
      zetaCutoffMellinConstant 1 (1/2)*Real.sqrt (N : ℝ)*zetaGlobalConvolution T t+
      zetaSixthPerronError := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 < t := (Real.rpow_pos_of_pos hNp _).trans_le hscale
  have hb := norm_zetaInterval_le_sixth_convolution N I t t hN hI hIN hscale
    ⟨le_rfl,by linarith⟩
  apply hb.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (zetaMomentConvolution_le_global ht.le htT)
      (mul_nonneg (zetaCutoffMellinConstant_pos _ _).le (Real.sqrt_nonneg _))) le_rfl

theorem exists_sum_zetaInterval_far_twelfth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (I : Finset ℕ) (T : ℝ) (W : Finset ℝ),
        1 < N → IsIntegerInterval I → I ⊆ Finset.Icc N (2*N) →
        T₀ ≤ T → IsOneSeparated W →
        (∀ t ∈ W, (N : ℝ)^(11/8 : ℝ) ≤ t ∧ t ≤ T) →
        (∑ t ∈ W, ‖∑ n ∈ I, dirichletPhase n t‖^12) ≤ C*(N : ℝ)^6*T^(2+ε) := by
  obtain ⟨D,T₀,hD,hT₀,hmoment⟩ := exists_sum_zetaGlobalConvolution_twelfth_bound hε
  let A := zetaCutoffMellinConstant 1 (1/2)
  let E := zetaSixthPerronError
  let C := (2 : ℝ)^11*(A^12*D+2*E^12)
  have hA : 0 < A := zetaCutoffMellinConstant_pos _ _
  have hE : 0 < E := zetaSixthPerronError_pos
  refine ⟨C,T₀,by dsimp [C]; positivity,hT₀,?_⟩
  intro N I T W hN hI hIN hTC hsep hW
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hT1 : (1 : ℝ) ≤ T := hT₀.trans hTC
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hW0 (t : ℝ) (ht : t ∈ W) : t ∈ Set.Icc 0 T :=
    ⟨(Real.rpow_nonneg hNp.le _).trans (hW t ht).1,(hW t ht).2⟩
  have hm := hmoment T W hTC hsep hW0
  have hsqrt : (Real.sqrt (N : ℝ))^12 = (N : ℝ)^6 := by
    calc
      _ = ((Real.sqrt (N : ℝ))^2)^6 := by ring
      _ = _ := by rw [Real.sq_sqrt hNp.le]
  have hpoint (t : ℝ) (ht : t ∈ W) :
      ‖∑ n ∈ I, dirichletPhase n t‖^12 ≤
        (2 : ℝ)^11*(A^12*(N : ℝ)^6*zetaGlobalConvolution T t^12+E^12) := by
    have hp := norm_zetaInterval_le_global_convolution N I T t hN hI hIN
      (hW t ht).1 (hW t ht).2
    have ha : 0 ≤ A*Real.sqrt (N : ℝ)*zetaGlobalConvolution T t :=
      mul_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg _)) (zetaGlobalConvolution_nonneg hT.le t)
    have hh := (pow_le_pow_left₀ (norm_nonneg _) hp 12).trans (add_pow_le ha hE.le 12)
    simpa only [Nat.reduceSub,mul_pow,hsqrt,A,E] using hh
  have hcard : (W.card : ℝ) ≤ 2*T := by
    have hh := oneSeparated_card_cast_le_interval_length_add_one W hsep
      (by simpa only [sub_zero] using hT.le) hW0
    linarith
  have hN6 : (1 : ℝ) ≤ (N : ℝ)^6 := one_le_pow₀ hN1
  have hTpower : T ≤ T^(2+ε) := calc
    _ = T^(1 : ℝ) := (Real.rpow_one T).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hscalePower : T ≤ (N : ℝ)^6*T^(2+ε) :=
    hTpower.trans (le_mul_of_one_le_left (Real.rpow_nonneg hT.le _) hN6)
  have herror : (W.card : ℝ)*E^12 ≤ 2*E^12*((N : ℝ)^6*T^(2+ε)) := calc
    _ ≤ (2*T)*E^12 := mul_le_mul_of_nonneg_right hcard (pow_nonneg hE.le _)
    _ = (2*E^12)*T := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscalePower (by positivity)
  calc
    _ ≤ ∑ t ∈ W, (2 : ℝ)^11*(A^12*(N : ℝ)^6*zetaGlobalConvolution T t^12+E^12) :=
      Finset.sum_le_sum hpoint
    _ = (2 : ℝ)^11*(A^12*(N : ℝ)^6*(∑ t ∈ W, zetaGlobalConvolution T t^12)+
        (W.card : ℝ)*E^12) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2 : ℝ)^11*(A^12*(N : ℝ)^6*(D*T^(2+ε))+
        2*E^12*((N : ℝ)^6*T^(2+ε))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hm (by positivity)) herror
    _ = C*(N : ℝ)^6*T^(2+ε) := by dsimp [C]; ring

end TaoTrudgianYang2025
