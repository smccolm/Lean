import TaoTrudgianYang2025.ParabolaBilinearLocalization

noncomputable section
open Expdb GafniTao Filter Asymptotics Set
open scoped NNReal Topology
namespace TaoTrudgianYang2025
private theorem eventually_const_log36_le_rpow {D q : ℝ} (hD : 0 ≤ D) (hq : 0<q) :
    ∀ᶠ T : ℝ in atTop, D*(1+Real.log T)^36 ≤ T^q := by
  have hl := ((isLittleO_log_rpow_rpow_atTop (36:ℝ) hq).const_mul_left (D*2^36)).eventuallyLE
  filter_upwards [hl,eventually_ge_atTop (Real.exp 1)] with T hh hT
  have hTp : 0<T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := by
    have ht := Real.log_le_log (Real.exp_pos 1) hT
    simpa only [Real.log_exp] using ht
  have hlog0 : 0 ≤ Real.log T := zero_le_one.trans hlog
  have hp : 0 ≤ D*2^36*(Real.log T)^(36:ℝ) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hp,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTp.le q)] at hh
  norm_num only [Real.rpow_ofNat] at hh
  calc
    _ ≤ D*(2*Real.log T)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hlog]) 36) hD
    _ = D*2^36*(Real.log T)^36 := by ring
    _ ≤ _ := by
      convert hh using 1
      norm_num

private theorem eventually_displacement_physical_scales {u K a δ : ℝ}
    (hu : 0 < u) (hlo : (1:ℝ)/3 < a-δ) (hhi : a+δ < 3/7) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0 < P → T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let U := u*T/P^3
      U ≤ 1/3600 ∧ 1 ≤ P*U*Real.sqrt U ∧ K ≤ P*U := by
  have hsmall := eventually_const_mul_rpow_le_rpow (D:=3600*u)
    (by linarith only [hlo] : (1:ℝ) < (a-δ)*3)
  have hsize := eventually_const_mul_rpow_le_rpow (D:=K/u)
    (by linarith only [hhi] : (a+δ)*2 < (1:ℝ))
  have hcurve := eventually_const_mul_rpow_le_rpow (D:=1/u^3)
    (by linarith only [hhi] : (a+δ)*7 < (3:ℝ))
  filter_upwards [hsmall,hsize,hcurve,eventually_gt_atTop (0:ℝ)] with T ht₁ ht₂ ht₃ hT
  intro P hP hPl hPh U
  have hU : 0 < U := by dsimp only [U]; positivity
  have hPlo : T^((a-δ)*3) ≤ P^3 := by
    calc
      _ = (T^(a-δ))^3 := by simpa using Real.rpow_mul_natCast hT.le (a-δ) 3
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hT.le _) hPl 3
  have hPtwo : P^2 ≤ T^((a+δ)*2) := by
    calc
      _ ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hPh 2
      _ = _ := by simpa using (Real.rpow_mul_natCast hT.le (a+δ) 2).symm
  have hPseven : P^7 ≤ T^((a+δ)*7) := by
    calc
      _ ≤ (T^(a+δ))^7 := pow_le_pow_left₀ hP.le hPh 7
      _ = _ := by simpa using (Real.rpow_mul_natCast hT.le (a+δ) 7).symm
  rw [Real.rpow_one] at ht₁ ht₂
  have hUbound : U ≤ 1/3600 := by
    apply (div_le_iff₀ (pow_pos hP 3)).mpr
    linarith only [ht₁.trans hPlo]
  have hphysicalK : K ≤ P*U := by
    have hh := mul_le_mul_of_nonneg_left ht₂ hu.le
    have hid : u*(K/u*T^((a+δ)*2))=K*T^((a+δ)*2) := by field_simp
    rw [hid] at hh
    by_cases hK : 0 ≤ K
    · have hk := (mul_le_mul_of_nonneg_left hPtwo hK).trans hh
      have he : P*U=u*T/P^2 := by dsimp only [U]; field_simp
      rw [he]
      exact (le_div_iff₀ (pow_pos hP 2)).mpr hk
    · exact (le_of_not_ge hK).trans (by positivity)
  have hcurve' : P^7 ≤ u^3*T^3 := by
    have hh := mul_le_mul_of_nonneg_left ht₃ (pow_nonneg hu.le 3)
    have hid : u^3*(1/u^3*T^((a+δ)*7))=T^((a+δ)*7) := by field_simp
    rw [hid] at hh
    norm_num only [Real.rpow_ofNat] at hh
    exact hPseven.trans hh
  have henergy : 1 ≤ P^2*U^3 := by
    have he : P^2*U^3=u^3*T^3/P^7 := by dsimp only [U]; field_simp
    rw [he]
    exact (le_div_iff₀ (pow_pos hP 7)).mpr (by simpa only [one_mul] using hcurve')
  have hidentity : (P*U*Real.sqrt U)^2=P^2*U^3 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hU.le]
    ring
  have hroot : 1 ≤ P*U*Real.sqrt U := by
    nlinarith only [henergy,hidentity,show 0 ≤ P*U*Real.sqrt U by positivity]
  exact ⟨hUbound,hroot,hphysicalK⟩

private theorem eventually_displacement_piecewise_majorant {C a δ η ε : ℝ}
    (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hgap : a+δ ≤ 1) (hδη : δ ≤ η)
    (hη : 0 < η) (hηε : η ≤ ε/100) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 1 ≤ P → P ≤ T^(a+δ) →
      C*P^η*(1+Real.log P)^36*(T*P^8+T^((8:ℝ)/3)*P^4) ≤
        T^(12*(max ((1:ℝ)/12+2/3*a) (2/9+a/3)+ε)) := by
  filter_upwards [eventually_const_log36_le_rpow (show 0 ≤ 2*C by positivity) hη,
    eventually_ge_atTop (1:ℝ)] with T hlog hT
  intro P hP hPh
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hPT : P ≤ T := hPh.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hT hgap)
  have hlogP := Real.log_nonneg hP
  have hlogT := Real.log_nonneg hT
  have hlogPT := Real.log_le_log hPp hPT
  have hPe : P^η ≤ T^η := Real.rpow_le_rpow hPp.le hPT hη.le
  let d := 12*(max ((1:ℝ)/12+2/3*a) (2/9+a/3))+8*δ
  have hmain₁ : T*P^8 ≤ T^d := by
    calc
      _ ≤ T*(T^(a+δ))^8 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPp.le hPh 8) hTp.le
      _ = T^(1+(a+δ)*8) := by
        rw [←Real.rpow_mul_natCast hTp.le,Real.rpow_add hTp,Real.rpow_one]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [le_max_left ((1:ℝ)/12+2/3*a) (2/9+a/3)])
  have hmain₂ : T^((8:ℝ)/3)*P^4 ≤ T^d := by
    calc
      _ ≤ T^((8:ℝ)/3)*(T^(a+δ))^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPp.le hPh 4) (Real.rpow_nonneg hTp.le _)
      _ = T^((8:ℝ)/3+(a+δ)*4) := by
        rw [←Real.rpow_mul_natCast hTp.le,←Real.rpow_add hTp]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [le_max_right ((1:ℝ)/12+2/3*a) (2/9+a/3),hδ])
  have hsum : T*P^8+T^((8:ℝ)/3)*P^4 ≤ 2*T^d := by linarith only [hmain₁,hmain₂]
  calc
    _ ≤ C*T^η*(1+Real.log T)^36*(2*T^d) := by gcongr
    _ = (2*C*(1+Real.log T)^36)*(T^η*T^d) := by ring
    _ ≤ T^η*(T^η*T^d) := mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = T^(d+2*η) := by rw [←Real.rpow_add hTp,←Real.rpow_add hTp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [hδη,hηε,hη])


theorem isExponentSumBoundNonAsymptotic_bourgain_piecewise
    {α : NNReal} (hα : (1:ℝ)/3 < (α:ℝ)) (hαupper : (α:ℝ) < 3/7) :
    IsExponentSumBoundNonAsymptotic α (max ((1:ℝ)/12+2/3*(α:ℝ)) (2/9+(α:ℝ)/3)) := by
  intro ε hε σ hσ
  let η := min ((1:ℝ)/1000) (ε/100)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηε : η ≤ ε/100 := min_le_right _ _
  obtain ⟨δ₀,hδ₀,C₀,hC₀,K,hK,hsource⟩ := exists_displacement_model_global_bound hσ hη
  let δ := min δ₀ (min η (min (((α:ℝ)-1/3)/2) ((3/7-(α:ℝ))/2)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hη (lt_min
    (by linarith only [hα]) (by linarith only [hαupper])))
  have hδ0 : δ ≤ δ₀ := min_le_left _ _
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδgaps : δ ≤ min (((α:ℝ)-1/3)/2) ((3/7-(α:ℝ))/2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hlow : (1:ℝ)/3 < (α:ℝ)-δ := by
    have hh := hδgaps.trans (min_le_left _ _)
    linarith only [hh,hα]
  have hhigh : (α:ℝ)+δ < 3/7 := by
    have hh := hδgaps.trans (min_le_right _ _)
    linarith only [hh,hαupper]
  let u := (modelPhaseJetCoefficient σ 2+1)/6
  have hu : 0 < u := by
    have hh := modelPhaseJetCoefficient_nonneg σ 2
    dsimp only [u]
    positivity
  have hentry := eventually_displacement_physical_scales (K:=K) hu hlow hhigh
  have hmajor := eventually_displacement_piecewise_majorant hC₀.le hδ.le
    (by linarith only [hhigh]) hδη hη hηε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hentry.and hmajor)
  let C := max 1 M
  have hC : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := le_max_right _ _
  refine ⟨δ,hδ,3,by norm_num,C,hC,?_⟩
  intro T P G a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hs.rpow_sub_le_scale
  have hP1 : 1 ≤ P := (Real.one_le_rpow hT (by linarith only [hlow] : 0 ≤ (α:ℝ)-δ)).trans
    hs.rpow_sub_le_scale
  obtain ⟨hphysical,hbudget⟩ := hM T (hMC.trans hs.threshold_le_param)
  obtain ⟨hUsmall,hcurve,hPU⟩ := hphysical P hPp hs.rpow_sub_le_scale hs.scale_le_rpow_add
  have hUid : (modelPhaseJetCoefficient σ 2+1)*T/P^3/6=u*T/P^3 := by dsimp only [u]; ring
  by_cases hab : a ≤ b
  · have hbound := hsource G T P a b hTp hPp hab hs.scale_le_start hs.end_le_two_mul_scale
      (approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδ0)
      (by simpa only [hUid] using hUsmall)
      (by simpa only [hUid] using hcurve)
      (by simpa only [hUid] using hPU)
    have hpower := hbound.trans (hbudget P hP1 hs.scale_le_rpow_add)
    have hpower' : ‖exponentialSumAt G T P a b‖^12 ≤
        (T^(max ((1:ℝ)/12+2/3*(α:ℝ)) (2/9+(α:ℝ)/3)+ε))^12 := by
      rw [←Real.rpow_mul_natCast hTp.le]
      convert hpower using 1
      congr 1
      ring
    have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Real.rpow_nonneg hTp.le _) (by norm_num : (12:ℕ)≠0)).mp hpower'
    exact hh.trans (le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC)
  · have hEmpty : Finset.Icc a b=∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [exponentialSumAt,hEmpty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)




theorem exponentSumGrowthExponent_le_bourgain_table_first
    {α : NNReal} (hα : (1:ℝ)/3 < (α:ℝ)) (hαupper : (α:ℝ) ≤ 5/12) :
    exponentSumGrowthExponent α ≤ 2/9+(α:ℝ)/3 := by
  have h := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_bourgain_piecewise hα (by linarith only [hαupper]))
  rw [max_eq_right (by linarith only [hαupper])] at h
  exact h

theorem exponentSumGrowthExponent_le_bourgain_table_second
    {α : NNReal} (hα : (5:ℝ)/12 ≤ (α:ℝ)) (hαupper : (α:ℝ) ≤ 3/7) :
    exponentSumGrowthExponent α ≤ 1/12+2/3*(α:ℝ) := by
  rcases lt_or_eq_of_le hαupper with hlt | heq
  · have h := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
      (isExponentSumBoundNonAsymptotic_bourgain_piecewise (by linarith only [hα]) hlt)
    rw [max_eq_left (by linarith only [hα])] at h
    exact h
  · have h := exponentSumGrowthExponent_le_bourgain_baseline (α:=α) (by linarith only [heq])
      (by linarith only [heq])
    linarith only [h,heq]

theorem isExponentSumBoundNonAsymptotic_bourgain_refined_from_piecewise
    {α : NNReal} (hα : (17:ℝ)/42 ≤ (α:ℝ)) (hαupper : (α:ℝ) < 3/7) :
    IsExponentSumBoundNonAsymptotic α ((13:ℝ)/84+(α:ℝ)/2) := by
  apply exponentSumGrowthExponent_le_iff_nonAsymptotic.mp
  have h := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_bourgain_piecewise (by linarith only [hα]) hαupper)
  apply h.trans
  exact max_le (by linarith only [hαupper]) (by linarith only [hα])

#print axioms isExponentSumBoundNonAsymptotic_bourgain_refined_from_piecewise
#print axioms isExponentSumBoundNonAsymptotic_bourgain_piecewise
#print axioms exponentSumGrowthExponent_le_bourgain_table_first
#print axioms exponentSumGrowthExponent_le_bourgain_table_second
end TaoTrudgianYang2025
