import TaoTrudgianYang2025.ZetaIntervalPerron
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-! Actual twelfth moments of sharp interval sums on arbitrary separated samples. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem sum_zetaInterval_twelfth_le (N : ℕ) (I : Finset ℕ) (T : ℝ) (W : Finset ℝ)
    (hN : 1 < N) (hI : IsIntegerInterval I) (hIN : I ⊆ Finset.Icc N (2*N))
    (hscale : (N : ℝ)^(11/8 : ℝ) ≤ T) (hsep : IsOneSeparated W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2*T)) :
    (∑ t ∈ W, ‖∑ n ∈ I, dirichletPhase n t‖^12) ≤
      (2 : ℝ)^11*(zetaCutoffMellinConstant 1 (1/2)^12*(N : ℝ)^6*
        zetaMomentLogLoss T^12*zetaTwelfthMoment T+
        (W.card : ℝ)*zetaSixthPerronError^12) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hT : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hscale
  let A := zetaCutoffMellinConstant 1 (1/2)
  have hA : 0 < A := zetaCutoffMellinConstant_pos _ _
  have hsqrt : (Real.sqrt (N : ℝ))^12 = (N : ℝ)^6 := by
    calc
      _ = ((Real.sqrt (N : ℝ))^2)^6 := by ring
      _ = _ := by rw [Real.sq_sqrt hNp.le]
  have hpoint (t : ℝ) (ht : t ∈ W) :
      ‖∑ n ∈ I, dirichletPhase n t‖^12 ≤
        (2 : ℝ)^11*(A^12*(N : ℝ)^6*zetaMomentConvolution T t^12+
          zetaSixthPerronError^12) := by
    have hp := norm_zetaInterval_le_sixth_convolution N I T t hN hI hIN hscale (hW t ht)
    have ha : 0 ≤ A*Real.sqrt (N : ℝ)*zetaMomentConvolution T t :=
      mul_nonneg (mul_nonneg hA.le (Real.sqrt_nonneg _)) (zetaMomentConvolution_nonneg hT.le t)
    have hpow := (pow_le_pow_left₀ (norm_nonneg _) hp 12).trans
      (add_pow_le ha zetaSixthPerronError_pos.le 12)
    simpa only [Nat.reduceSub,mul_pow,hsqrt,A] using hpow
  calc
    _ ≤ ∑ t ∈ W, (2 : ℝ)^11*
        (A^12*(N : ℝ)^6*zetaMomentConvolution T t^12+zetaSixthPerronError^12) :=
      Finset.sum_le_sum hpoint
    _ = (2 : ℝ)^11*(A^12*(N : ℝ)^6*(∑ t ∈ W, zetaMomentConvolution T t^12)+
        (W.card : ℝ)*zetaSixthPerronError^12) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2 : ℝ)^11*(A^12*(N : ℝ)^6*
        (zetaMomentLogLoss T^12*zetaTwelfthMoment T)+
        (W.card : ℝ)*zetaSixthPerronError^12) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_zetaMomentConvolution_twelfth W hT hsep hW)
          (by positivity)) le_rfl
    _ = _ := by dsimp [A]; ring

theorem exists_sum_zetaInterval_twelfth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (N : ℕ) (I : Finset ℕ) (T : ℝ) (W : Finset ℝ),
        1 < N → IsIntegerInterval I → I ⊆ Finset.Icc N (2*N) →
        T₀ ≤ T → (N : ℝ)^(11/8 : ℝ) ≤ T → IsOneSeparated W →
        (∀ t ∈ W, t ∈ Set.Icc T (2*T)) →
        (∑ t ∈ W, ‖∑ n ∈ I, dirichletPhase n t‖^12) ≤
          C*(N : ℝ)^6*T^(2+ε) := by
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp
    (eventually_zetaMomentLoss_twelfth_of_dyadic zeta_twelfth_dyadic hε)
  let A := zetaCutoffMellinConstant 1 (1/2)
  let E := zetaSixthPerronError
  let C := (2 : ℝ)^11*(A^12+2*E^12)
  have hA : 0 < A := zetaCutoffMellinConstant_pos _ _
  have hE : 0 < E := zetaSixthPerronError_pos
  refine ⟨C,max 1 T₁,by dsimp [C]; positivity,le_max_left _ _,?_⟩
  intro N I T W hN hI hIN hTC hscale hsep hW
  have hT : (1 : ℝ) ≤ T := (le_max_left _ _).trans hTC
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN6 : (1 : ℝ) ≤ (N : ℝ)^6 := one_le_pow₀ hN1
  have hmoment := hT₁ T ((le_max_right _ _).trans hTC)
  have hcard : (W.card : ℝ) ≤ 2*T := by
    have hh := oneSeparated_card_cast_le_interval_length_add_one W hsep
      (by linarith : 0 ≤ 2*T-T) hW
    linarith
  have hTpower : T ≤ T^(2+ε) := calc
    _ = T^(1 : ℝ) := (Real.rpow_one T).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hscalePower : T ≤ (N : ℝ)^6*T^(2+ε) :=
    hTpower.trans (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hT) _) hN6)
  have herror : (W.card : ℝ)*E^12 ≤ 2*E^12*((N : ℝ)^6*T^(2+ε)) := calc
    _ ≤ (2*T)*E^12 := mul_le_mul_of_nonneg_right hcard (pow_nonneg hE.le _)
    _ = (2*E^12)*T := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscalePower (by positivity)
  have hfinite := sum_zetaInterval_twelfth_le N I T W hN hI hIN hscale hsep hW
  change (∑ t ∈ W, ‖∑ n ∈ I, dirichletPhase n t‖^12) ≤ _ at hfinite
  calc
    _ ≤ (2 : ℝ)^11*(A^12*(N : ℝ)^6*
        (zetaMomentLogLoss T^12*zetaTwelfthMoment T)+(W.card : ℝ)*E^12) := by
      convert hfinite using 1
      dsimp [A,E]
      ring
    _ ≤ (2 : ℝ)^11*(A^12*(N : ℝ)^6*T^(2+ε)+
        2*E^12*((N : ℝ)^6*T^(2+ε))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hmoment (by positivity)) herror
    _ = C*(N : ℝ)^6*T^(2+ε) := by dsimp [C]; ring

end TaoTrudgianYang2025
