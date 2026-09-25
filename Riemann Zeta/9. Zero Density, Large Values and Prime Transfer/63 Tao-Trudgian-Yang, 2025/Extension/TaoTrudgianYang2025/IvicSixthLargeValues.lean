import TaoTrudgianYang2025.IvicSixthAmplitude

/-!
The restricted sixth moment yields an actual zeta large-value exponent
only when the physical amplitude lies above its threshold. Both the
strict restriction and tau>1 are retained.
-/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem ivicSixth_largeValue_loss_parameters {σ τ ε : ℝ}
    (hτ : 1 < τ) (hgap : (11/72)*τ < σ-1/2) (hε : 0 < ε) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ δ ≤ min (1/4) ((τ-1)/4) ∧
      1/2+η+(τ+δ)*(11/72+3*η) ≤ σ-δ ∧
      3+(τ+δ)*(1+3*η) ≤ (τ-6*(σ-1/2)+ε)+6*(σ-δ) := by
  let g : ℝ := σ-1/2-(11/72)*τ
  have hg : 0 < g := sub_pos.mpr hgap
  have hd : 0 < τ+1 := by linarith
  let η : ℝ := min 1 (min (g/(16*(τ+1))) (ε/(12*(τ+1))))
  let δ : ℝ := min (min (1/4) ((τ-1)/4)) (min (g/20) (ε/40))
  have hη : 0 < η := lt_min (by norm_num)
    (lt_min (div_pos hg (by positivity)) (div_pos hε (by positivity)))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηg : η*(16*(τ+1)) ≤ g :=
    (le_div_iff₀ (by positivity : 0 < 16*(τ+1))).mp
      ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η*(12*(τ+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 12*(τ+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0 < δ := lt_min (lt_min (by norm_num) (by linarith))
    (lt_min (div_pos hg (by norm_num)) (div_pos hε (by norm_num)))
  have hδg : δ*20 ≤ g :=
    (le_div_iff₀ (by norm_num : (0:ℝ) < 20)).mp
      ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ*40 ≤ ε :=
    (le_div_iff₀ (by norm_num : (0:ℝ) < 40)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hδη : δ*η ≤ δ := by nlinarith
  refine ⟨η,δ,hη,hδ,min_le_left _ _,?_,?_⟩
  · dsimp [g] at hηg hδg
    nlinarith
  · nlinarith

theorem ivicSixth_zetaLargeValueBound {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hgap : (11/72)*τ < σ-1/2) :
    IsZetaLargeValueBound σ τ (τ-6*(σ-1/2)) := by
  intro ε hε
  obtain ⟨η,δ,hη,hδ,hδsmall,hgap',hexponent⟩ :=
    ivicSixth_largeValue_loss_parameters hτ hgap hε
  have hheight : 1 ≤ τ-δ := by
    have hh := hδsmall.trans (min_le_right _ _)
    linarith
  let C : ℝ := zetaLinePerronConstant (1/2)
  have hC : 0 < C := zetaLinePerronConstant_pos _
  obtain ⟨A,hA,hsmall⟩ := exists_ivicSixth_truncation_threshold hC hη hheight hgap'
  obtain ⟨B,hB,hEntry⟩ := exists_zetaLinePerron_aboveOne_uniform_threshold
    (by norm_num : (1/2:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) hτ
  obtain ⟨D,hD,hmoment⟩ := exists_ivicSixth_pattern_moment hη
  let K : ℝ := max 1 (max A (max B (max D ((2*C)^6))))
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : A ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : B ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKD : D ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hKC : (2*C)^6 ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hPN hTl hTu hVl _
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT : 0 < P.T := P.T_pos
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTl
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hheight
  have hentry : ∀ t ∈ P.ordinates, P.V ≤ C*P.N^(1/2:ℝ)*zetaMomentConvolution P.T t :=
    hEntry P (hKB.trans hPN) σ δ hσ hδsmall hTl hVl
  have hphysical := hmoment P ((hKD.trans hPN).trans hNT) C hC hentry
    (hsmall P (hKA.trans hPN) hTl hTu hVl)
  have hVp : P.N^(6*(σ-δ)) ≤ P.V^6 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hVl 6
    rw [← Real.rpow_mul_natCast hN.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_comm] using hh
  have hTp : P.T^(1+3*η) ≤ P.N^((τ+δ)*(1+3*η)) := by
    have hh := Real.rpow_le_rpow P.T_pos.le hTu (by linarith : 0 ≤ 1+3*η)
    rw [← Real.rpow_mul hN.le] at hh
    exact hh
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN (6*(σ-δ)))).mp
  calc
    _ ≤ (P.ordinates.card : ℝ)*P.V^6 :=
      mul_le_mul_of_nonneg_left hVp (Nat.cast_nonneg _)
    _ ≤ (2*C)^6*P.N^3*P.T^(1+3*η) := hphysical
    _ ≤ K*P.N^3*P.N^((τ+δ)*(1+3*η)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hKC (by positivity)) hTp
        (by positivity) (by positivity)
    _ = K*P.N^(3+(τ+δ)*(1+3*η)) := by
      rw [mul_assoc,← Real.rpow_ofNat,← Real.rpow_add hN]
    _ ≤ K*P.N^((τ-6*(σ-1/2)+ε)+6*(σ-δ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hexponent) (zero_le_one.trans hK)
    _ = _ := by rw [Real.rpow_add hN,mul_assoc]

theorem ivicSixth_zetaLargeValueExponent_le {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hgap : (11/72)*τ < σ-1/2) :
    zetaLargeValueExponent σ τ ≤ ((τ-6*(σ-1/2) : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound (ivicSixth_zetaLargeValueBound hσ hτ hgap)

end TaoTrudgianYang2025
