import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyUniformChartScratch

private theorem eventually_reference_chart_majorants
    {Ch Cc ε : ℝ} (hCh : 1 ≤ Ch) (hCc : 1 ≤ Cc) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
    let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
    let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
    ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^ε := by
  let Kb : ℝ := 222+1728/Real.log 2
  let Kc : ℝ := 1+2/Real.log (5/4)
  let K : ℝ := 6+Kc*(105+544*Kb)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlc : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have hKb : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hKc : 0 ≤ Kc := by dsimp only [Kc]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_const_log_pow_le_rpow K hK 2 hε,
    Filter.eventually_ge_atTop Ch, Filter.eventually_ge_atTop Cc,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hh hc hT hlogT
  dsimp only
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hheight1 : 1 ≤ Ch*T^3 := one_le_mul_of_one_le_of_one_le hCh (one_le_pow₀ hT)
  have hheight : (Ch*T^3)^2 ≤ T^8 := by
    calc
      _ ≤ (T*T^3)^2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hh (by positivity)) 2
      _ = _ := by ring
  have hlogh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0 < (Ch*T^3)^2) hheight
  rw [Real.logb_pow 2 T 8] at hlogh
  have hfloorh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2)
    (one_le_pow₀ hheight1 : 1 ≤ (Ch*T^3)^2))
  have hB : ((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤ Kb*Real.log T := by
    have he : Kb*Real.log T=222*Real.log T+216*(8*Real.logb 2 T) := by
      dsimp only [Kb,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogh
    linarith only [hfloorh,hlogh,hlogT]
  have hchart1 : 1 ≤ Cc*T := one_le_mul_of_one_le_of_one_le hCc hT
  have hchart : Cc*T ≤ T^2 := by nlinarith only [mul_le_mul_of_nonneg_right hc hTp.le]
  have hlogc := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
    (zero_lt_one.trans_le hchart1) hchart
  rw [Real.logb_pow] at hlogc
  have hfloorc := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<5/4) hchart1)
  have hC : ((⌊Real.logb (5/4) (Cc*T)⌋₊+1:ℕ):ℝ) ≤ Kc*Real.log T := by
    have he : Kc*Real.log T=Real.log T+2*Real.logb (5/4) T := by
      dsimp only [Kc,Real.logb]
      ring
    rw [he]
    push_cast
    norm_num only [Nat.cast_ofNat] at hlogc
    linarith only [hfloorc,hlogc,hlogT]
  have hinner : 105+544*((6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1):ℕ):ℝ) ≤
      (105+544*Kb)*Real.log T := by linarith only [hB,hlogT]
  have hmul := mul_le_mul hC hinner (by positivity) (mul_nonneg hKc (by linarith only [hlogT]))
  have hlogsq : 1 ≤ (Real.log T)^2 := one_le_pow₀ hlogT
  have hcost : ((6+(⌊Real.logb (5/4) (Cc*T)⌋₊+1)*
      (105+544*(6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1))):ℕ):ℝ) ≤ K*(Real.log T)^2 := by
    push_cast
    dsimp only [K]
    push_cast at hmul
    nlinarith only [hmul,hlogsq]
  exact hcost.trans hsmall

private theorem physical_reference_chart_ratio
    {κ Cp R U d : ℝ} (hκ : 0 < κ) (hCp : 0 < Cp+2) (hR : 0 < R)
    (hd : d ≤ 7*U/(2*R^2)) :
    d/(12*(κ/(16*(Cp+2)*R^2))) ≤ ((14:ℝ)/3)*(Cp+2)/κ*U := by
  have hh := div_le_div_of_nonneg_right hd
    (by positivity : 0 ≤ 12*(κ/(16*(Cp+2)*R^2)))
  apply hh.trans_eq
  field_simp
  ring

private theorem physical_reference_radius_le_source
    {T M N R Q : ℝ} (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hscale : T*N*R^2=M^3) : R^2 ≤ T := by
  have hN : 1 ≤ N := hR.trans (hRQ.trans hQN)
  have hNM' : N ≤ M := (by nlinarith only [hN] : N ≤ N^2).trans hNM
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) (hRQ.trans hQN) 2).trans hNM
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM' hR₂ (sq_nonneg R) hM.le
      _ = _ := by ring
  have hMT : M ≤ T := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hM)).mp
    calc
      M*M^2 = M^3 := by ring
      _ = T*(N*R^2) := by nlinarith only [hscale]
      _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
  exact hR₂.trans hMT

/-- Common logarithmic budgets are constructed from the actual physical
reference labels and gap widths. The asymptotic threshold depends only
on the fixed model and height constants, not on the finite reference system. -/
theorem eventually_physical_reference_chart_budgets
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss := by
  let Jv := modelPhaseJetCoefficient σ 1+1
  let Ch := 1+4*(3*Jref/(2*σ)+1+Jv/2)
  let κ := modelPhaseThirdLower σ
  let Cp := σ*(σ+1)+1
  let Cc := 1+((14:ℝ)/3)*(Cp+2)/κ
  have hJv : 0 ≤ Jv := add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) zero_le_one
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cp+2 := by dsimp only [Cp]; positivity
  have hCh : 1 ≤ Ch := by dsimp only [Ch]; exact le_add_of_nonneg_right (by positivity)
  have hCc : 1 ≤ Cc := by dsimp only [Cc]; exact le_add_of_nonneg_right (by positivity)
  filter_upwards [eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M N R hδ₀ hδmax hT hM hR hRQ hQN hNM
    hU hUR hscale hr hs he hv hgap Vheight P₁ P₂ εchart
  let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
  let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUr : (1:ℝ) ≤ Uref := by exact_mod_cast hU
  have hV₀ : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ₀)) (by positivity)
  have hVmax : Vheight ≤ Jv*T/(2*M^2) := by
    dsimp only [Vheight,Jv]
    rw [mul_comm (modelPhaseJetCoefficient σ 1+1) T]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδmax) hT.le) (by positivity)
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial hσ hJref hJv hT hM hR hRQ hQN hNM
      hUr hscale hV₀ hVmax (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  have hP₁ ab : 1 ≤ P₁ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV₀)) (Nat.cast_nonneg Q))
  have hP₂ ab : 1 ≤ P₂ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hV₀) (abs_nonneg _)) (Nat.cast_nonneg Q))
  have hRT := physical_reference_radius_le_source hT hM hR hRQ hQN hNM hscale
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos (zero_lt_one.trans_le (hP₁ ab)) (zero_lt_one.trans_le (hP₂ ab)))
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.2.1 (hheight ab hab).2.2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    have hε : 0 < εchart := by change 0 < κ/(16*(Cp+2)*R^2); positivity
    have hratio := physical_reference_chart_ratio hκ hCp hRp (hgap ab hab).2
    have hratio' : (ab.2-ab.1)/(12*εchart) ≤ Cc*T := by
      apply hratio.trans
      calc
        ((14:ℝ)/3)*(Cp+2)/κ*(Uref:ℝ) ≤ ((14:ℝ)/3)*(Cp+2)/κ*T :=
          mul_le_mul_of_nonneg_left (hUR.trans hRT) (by positivity)
        _ ≤ Cc*T := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hT.le
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
      (div_pos (sub_pos.mpr (hgap ab hab).1) (by positivity)) hratio'

example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M N R : ℝ},
    0 ≤ δ → δ ≤ 1 → 0 < T → 0 < M → 1 ≤ R →
    R ≤ (Q:ℝ) → (Q:ℝ) ≤ N → N^2 ≤ M →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 → T*N*R^2=M^3 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss :=
  HuxleyUniformChartScratch.eventually_physical_reference_chart_budgets (σ:=σ) (Jref:=Jref) (εloss:=εloss) hσ hJref hεloss

end HuxleyUniformChartScratch
#print axioms HuxleyUniformChartScratch.eventually_reference_chart_majorants
#print axioms HuxleyUniformChartScratch.physical_reference_chart_ratio
#print axioms HuxleyUniformChartScratch.physical_reference_radius_le_source

#print axioms HuxleyUniformChartScratch.eventually_physical_reference_chart_budgets
