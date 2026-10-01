import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularUniformScratch

private theorem eventually_triangular_source_log_losses {Du Dl ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
      0 ≤ Real.log T ∧ Real.log T ≤ T^ε ∧
      (Real.log T)^((3:ℝ)/2) ≤ T^ε ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Du*T → 3+2*Real.log (d+2) ≤ T^ε) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ Dl*T → 3+2*Real.log (d+2) ≤ T^ε) := by
  filter_upwards [eventually_const_log_pow_le_rpow 7 (by norm_num) 2 hε,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (Du+2), Filter.eventually_ge_atTop (Dl+2)]
    with T hsmall hT hlog hDu hDl
  have hlogsq : Real.log T ≤ (Real.log T)^2 := by nlinarith only [hlog]
  have hsquare : (Real.log T)^2 ≤ T^ε :=
    (by nlinarith only [sq_nonneg (Real.log T)] : (Real.log T)^2 ≤ 7*(Real.log T)^2).trans hsmall
  have hpower : (Real.log T)^((3:ℝ)/2) ≤ (Real.log T)^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (3:ℝ)/2 ≤ (2:ℝ))
  have hcut (D d : ℝ) (hD : D+2 ≤ T) (hd : 0 ≤ d) (hdT : d ≤ D*T) :
      3+2*Real.log (d+2) ≤ T^ε := by
    have hbound : d+2 ≤ T^2 := by
      calc
        _ ≤ (D+2)*T := by nlinarith only [hdT,hT]
        _ ≤ T*T := mul_le_mul_of_nonneg_right hD (zero_le_one.trans hT)
        _ = _ := pow_two T |>.symm
    have hlogd := Real.log_le_log (by linarith only [hd] : 0 < d+2) hbound
    rw [Real.log_pow] at hlogd
    norm_num only [Nat.cast_ofNat] at hlogd
    exact (by nlinarith only [hlogd,hlog,hlogsq] :
      3+2*Real.log (d+2) ≤ 7*(Real.log T)^2).trans hsmall
  exact ⟨zero_le_one.trans hlog,hlogsq.trans hsquare,hpower.trans hsquare,
    fun d hd hdT => hcut Du d hDu hd hdT,
    fun d hd hdT => hcut Dl d hDl hd hdT⟩

private theorem triangular_physical_cutoff_height
    {T M N R Du Dl : ℝ} (hT : 0 < T) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hRN : R ≤ N) (hNM : N^2 ≤ M) (hscale : T*N*R^2=M^3)
    (hDu : 0 ≤ Du) (hDl : 0 ≤ Dl) :
    Du*T/M^2 ≤ Du*T ∧ Dl*M^2/T ≤ Dl*T := by
  have hNp : 1 ≤ N := hR.trans hRN
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hNM' : N ≤ M := (by nlinarith only [hNp] : N ≤ N^2).trans hNM
  have hR₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ (zero_le_one.trans hR) hRN 2).trans hNM
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM' hR₂ (sq_nonneg R) hMp.le
      _ = _ := (pow_two M).symm
  have hMT : M ≤ T := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hMp)).mp
    calc
      M*M^2 = M^3 := by ring
      _ = T*(N*R^2) := by nlinarith only [hscale]
      _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
  refine ⟨div_le_self (mul_nonneg hDu hT.le) (one_le_pow₀ hM),?_⟩
  apply (div_le_iff₀ hT).mpr
  simpa only [mul_assoc,pow_two] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMp.le hMT 2) hDl

private theorem triangular_logarithmic_mass_absorption
    {T ε m Cost A B D d mass : ℝ}
    (hT : 0 < T) (hm : 0 ≤ m) (hCost : 0 ≤ Cost)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hmass : mass ≤ 240*m*Cost*
      (9*(A*D^2)^((3:ℝ)⁻¹)*Real.log T+
        2*B*(3+2*Real.log (d+2))+(3/2:ℝ)*D*(Real.log T)^((3:ℝ)/2)))
    (hmmajor : m ≤ T^(ε/2)) (hlog : Real.log T ≤ T^(ε/2))
    (hpow : (Real.log T)^((3:ℝ)/2) ≤ T^(ε/2))
    (hcut : 3+2*Real.log (d+2) ≤ T^(ε/2)) :
    mass ≤ (240*Cost*(9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D))*T^ε := by
  have hroot : 0 ≤ (A*D^2)^((3:ℝ)⁻¹) := by positivity
  have hterms :
      9*(A*D^2)^((3:ℝ)⁻¹)*Real.log T+
        2*B*(3+2*Real.log (d+2))+(3/2:ℝ)*D*(Real.log T)^((3:ℝ)/2) ≤
      (9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2) := by
    nlinarith only [
      mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 9*(A*D^2)^((3:ℝ)⁻¹)),
      mul_le_mul_of_nonneg_left hcut (by positivity : (0:ℝ) ≤ 2*B),
      mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (3/2:ℝ)*D)]
  have hproduct : T^(ε/2)*T^(ε/2)=T^ε := by
    rw [←Real.rpow_add hT]
    congr 1
    ring
  calc
    _ ≤ 240*m*Cost*((9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2)) :=
      hmass.trans (mul_le_mul_of_nonneg_left hterms (by positivity))
    _ ≤ 240*T^(ε/2)*Cost*((9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D)*T^(ε/2)) := by gcongr
    _ = _ := by
      calc
        _ = (240*Cost*(9*(A*D^2)^((3:ℝ)⁻¹)+2*B+(3/2:ℝ)*D))*(T^(ε/2)*T^(ε/2)) := by ring
        _ = _ := by rw [hproduct]

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
private theorem eventually_physical_reference_chart_budgets
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

private theorem physical_source_triangular_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ0 : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    0 ≤ B ∧ 0 ≤ Cthird := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Gamma Cthird
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]; positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hB) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) hB) hCc))
      (mul_nonneg (by norm_num) hCt))
      (mul_nonneg (by norm_num) hCc))
      (mul_nonneg (by norm_num) hCN))) hκ.le
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  exact ⟨hB,hCthird⟩

/-- Actual triangular original-pair mass with constructed reference budgets
and source-linked logarithmic losses absorbed uniformly. This is a fixed-phase-pair
consumer, not the complete phase-family fifth moment. -/
theorem eventually_positive_difference_actual_fourier_triangular_original_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ (240*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
          2*BupperConst+(3/2:ℝ)*DupperConst))*T^εloss) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ (240*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
          2*BlowerConst+(3/2:ℝ)*DlowerConst))*T^εloss) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_triangular_original_source_regime_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro σ Jref εloss E θ hσ hJref hεloss
  let Du := θ*(3*Usrc/σsrc)*E/2
  let Dl := 12*Usrc*θ/(csrc*modelPhaseThirdLower σ)
  have hhalf : 0 < εloss/2 := by positivity
  filter_upwards [eventually_physical_reference_chart_budgets hσ hJref hhalf,
    eventually_triangular_source_log_losses (Du:=Du) (Dl:=Dl) hhalf]
    with T hbudgets hlogs
  intro Fsrc η ya yb Tsrc chartKey Uref Refs Gaps Bselect P entry Mat gap
    N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    δ M R base Bcut A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hregime
    lambda yp F chartColor hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨Bmajor,Cmajor,hBmajor,hCmajor,hcost⟩ := hbudgets
    Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hT hM hR hRQ hQN
    hNM hUref hUR hscale hrHeight hsHeight heHeight hvHeight
    (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩)
  let m0 := 6+Cmajor*(105+544*Bmajor)
  let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
  let DupperCut := θ*Uband
  let DlowerCut := θ/lambda
  have hraw :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*(Real.log T)+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*(Real.log T)^((3:ℝ)/2))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*(Real.log T)+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*(Real.log T)^((3:ℝ)/2))) := by
    exact hmassFn Fsrc η ya yb Tsrc E (Real.log T) chartKey Uref Refs Gaps (Bselect:=Bselect)
      P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
      rat vinv parity anchor e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
      (θ:=θ) A (W:=W) (x:=x)
      hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hlogs.1 hregime hchartColor
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
      hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep
      hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
      hRQ hselectedUpper hscaleTen hfamilyGap hgap
      hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
      hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
      hsize hD hΔ hBsize hBmajor hCmajor
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hE : 0 < E := (mul_pos_iff_of_pos_right hT).mp (hTsrc.trans_le hsourceScale)
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  obtain ⟨hBnonneg,hCthird⟩ := physical_source_triangular_constants_nonneg hσ hδ₀
  have hAU : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBU : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hAL : 0 ≤ AlowerConst := by dsimp only [AlowerConst]; positivity
  have hBL : 0 ≤ BlowerConst := by dsimp only [BlowerConst]; positivity
  have hDUc : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  have hDLc : 0 ≤ DlowerConst := by dsimp only [DlowerConst]; positivity
  have hCostU : 0 ≤ CostUpper := by dsimp only [CostUpper]; positivity
  have hCostL : 0 ≤ CostLower := by dsimp only [CostLower]; positivity
  have hcuts := triangular_physical_cutoff_height hT
    (by linarith only [hMtwo] : 1 ≤ M) hR hRN hNM hscale hDUc hDLc
  have hupper : DupperCut ≤ DupperConst*T := by
    calc
      _ = DupperConst*T/M^2 := by
        dsimp only [DupperCut,Uband,DupperConst]
        ring
      _ ≤ _ := hcuts.1
  have hlower : DlowerCut ≤ DlowerConst*T := by
    calc
      _ = DlowerConst*M^2/T := by
        dsimp only [DlowerCut,lambda,DlowerConst,κ]
        field_simp
      _ ≤ _ := hcuts.2
  have hupper0 : 0 ≤ DupperCut := by dsimp only [DupperCut,Uband]; positivity
  have hlower0 : 0 ≤ DlowerCut := by dsimp only [DlowerCut,lambda]; positivity
  constructor
  · intro htri
    exact triangular_logarithmic_mass_absorption hT (Nat.cast_nonneg m0)
      hCostU hAU hBU hDUc (hraw.1 htri) hcost hlogs.2.1 hlogs.2.2.1
      (hlogs.2.2.2.1 DupperCut hupper0 hupper)
  · intro htri
    exact triangular_logarithmic_mass_absorption hT (Nat.cast_nonneg m0)
      hCostL hAL hBL hDLc (hraw.2 htri) hcost hlogs.2.1 hlogs.2.2.1
      (hlogs.2.2.2.2 DlowerCut hlower0 hlower)


example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, x ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ (240*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
          2*BupperConst+(3/2:ℝ)*DupperConst))*T^εloss) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ (240*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
          2*BlowerConst+(3/2:ℝ)*DlowerConst))*T^εloss) :=
  HuxleyTriangularUniformScratch.eventually_positive_difference_actual_fourier_triangular_original_source_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


#print axioms eventually_positive_difference_actual_fourier_triangular_original_source_mass
#print axioms eventually_triangular_source_log_losses
#print axioms triangular_physical_cutoff_height
#print axioms triangular_logarithmic_mass_absorption

end HuxleyTriangularUniformScratch
