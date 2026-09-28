import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set Expdb Filter
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

/-- Fixed real powers preserve the already-proved ANTEDB scale semantics. -/
private theorem cubic_power_rpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (p : ℝ) :
    IsPowerAsymptotic (fun i => (X i)^p) T (a*p) := by
  obtain ⟨e,he,hXe⟩ := hX
  refine ⟨fun i => e i*p,?_,?_⟩
  · convert he.const_smul p using 1
    · funext i
      exact mul_comm (e i) p
    · funext i
      exact mul_comm a p
  · filter_upwards [hXe] with i hi
    rw [hi,← Real.rpow_mul (zero_le_one.trans (hT i))]

private theorem cubic_power_natpow
    {X T : VariableObject ℝ} {a : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (n : ℕ) :
    IsPowerAsymptotic (fun i => (X i)^n) T (a*(n:ℝ)) := by
  simpa only [Real.rpow_natCast] using cubic_power_rpow hX hT (n:ℝ)

private theorem cubic_power_const
    {T : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {c : ℝ} (hc : 0 < c) :
    IsPowerAsymptotic (fun _ => c) T 0 := by
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  apply isPowerAsymptotic_of_logb_tendsto
    (hTtop.eventually (eventually_gt_atTop 1)) (Filter.Eventually.of_forall (fun _ => hc))
  simpa only [Real.logb] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log c) atTop (𝓝 (Real.log c))).div_atTop
      (Real.tendsto_log_atTop.comp hTtop)

private theorem cubic_power_eventually_le
    {X T : VariableObject ℝ} {a b : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (hab : a < b) :
    ∀ᶠ i in atTop, X i ≤ (T i)^b := by
  have hh := hX.eventually_between (Filter.Eventually.of_forall hT)
    (sub_pos.mpr hab)
  filter_upwards [hh] with i hi
  convert hi.2 using 1
  congr 1
  ring

/-- All physical smallness and lifting conditions follow on the strict refined range. -/
theorem eventually_refined_bourgain_parameters
    {T P : VariableObject ℝ} {α σ κ₀ : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hκ₀ : 0<κ₀)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    ∀ᶠ i in atTop, 0<P i ∧ 0<w i ∧ w i≤1/2 ∧ U i≤1/3600 ∧
      1≤P i*U i*Real.sqrt (U i) ∧ b≤P i*U i ∧ l*U i≤1 ∧
      P i*(U i)^2≤1 ∧
      8*Real.sqrt (U i)+(10368*b/(a^2*l))*(P i*(U i)^2)≤1/2 ∧
      (2*n*u/σ)*Real.sqrt (U i)≤κ₀ := by
  intro u l a b n U w
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hTscale := isPowerAsymptotic_self T
  have hc (c : ℝ) (hc : 0<c) := cubic_power_const hT hTunbounded hc
  let v := 1-3*α
  let omegaScale := -(3+23*α)/194
  have hv : v<0 := by dsimp only [v]; linarith only [hlo]
  have homegaScale : omegaScale<0 := by dsimp only [omegaScale]; linarith only [hlo]
  have hU : IsPowerAsymptotic U T v := by
    convert ((hc u hu).mul hTscale hT).div (cubic_power_natpow hPT hT 3) hT using 1
    ring
  have hroot : IsPowerAsymptotic (fun i => Real.sqrt (U i)) T (v/2) := by
    simpa only [Real.sqrt_eq_rpow,mul_one_div] using cubic_power_rpow hU hT ((1:ℝ)/2)
  have hPU : IsPowerAsymptotic (fun i => P i*U i) T (α+v) := hPT.mul hU hT
  have hcurve : IsPowerAsymptotic (fun i => P i*U i*Real.sqrt (U i)) T (α+v+v/2) :=
    hPU.mul hroot hT
  have hlifting : IsPowerAsymptotic (fun i => P i*(U i)^2) T (α+2*v) := by
    convert hPT.mul (cubic_power_natpow hU hT 2) hT using 1
    ring
  have hw : IsPowerAsymptotic w T omegaScale := by
    simpa using cubic_power_rpow hTscale hT omegaScale
  have hPpos := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hUzero := hU.tendsto_zero_of_neg hv hT hTunbounded
  have hrootzero := hroot.tendsto_zero_of_neg (by linarith only [hv]) hT hTunbounded
  have hliftzero := hlifting.tendsto_zero_of_neg
    (by dsimp only [v]; linarith only [hlo] : α+2*v<0) hT hTunbounded
  have hsmall := hUzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/3600))
  have hwsmall := (hw.tendsto_zero_of_neg homegaScale hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hcurveLarge := (hcurve.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v+v/2) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hPULarge := (hPU.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v) hT hTunbounded).eventually
    (eventually_ge_atTop b)
  have hLsmall := (hUzero.const_mul l).eventually
    (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  have hLiftSmall := hliftzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have hsourceLift := ((hrootzero.const_mul 8).add
    (hliftzero.const_mul (10368*b/(a^2*l)))).eventually
      (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))
  have hshift := (hrootzero.const_mul (2*n*u/σ)).eventually
    (by simpa using (eventually_lt_nhds hκ₀))
  filter_upwards [hPpos,hwsmall,hsmall,hcurveLarge,hPULarge,hLsmall,hLiftSmall,hsourceLift,hshift]
    with i hPi hwi hUi hci hpui hli hlifti hsi hki
  exact ⟨hPi,Real.rpow_pos_of_pos (zero_lt_one.trans_le (hT i)) _,
    hwi.le,hUi.le,hci,hpui,hli.le,hlifti.le,by simpa only [one_div] using hsi.le,hki.le⟩

/-- The exact refined physical cost has the claimed two-piece beta exponent. -/
theorem eventually_refined_bourgain_cost
    {T P : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    let β := max (1/12+2*α/3) (241/1164+425*α/1164)
    ∀ᶠ i in atTop,
      (P i)^η*(1+Real.log (P i))^36*
        ((P i)^11*U i+w i*(P i)^12*(U i)^((5:ℝ)/2)+
          (P i)^(11+(13/84+η)+(55/84+η))*
            (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η))) ≤
        3*(T i)^(12*β+5*η) := by
  intro u U w β
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  let v := 1-3*α
  let omegaScale := -(3+23*α)/194
  let β₁ := 1/12+2*α/3
  let β₂ := 241/1164+425*α/1164
  have hβ₁ : β₁≤β := le_max_left _ _
  have hβ₂ : β₂≤β := le_max_right _ _
  have hα1 : α<1 := by linarith only [hhi]
  have hcoef : 3*α+3*v/2-omegaScale≤3 := by dsimp only [v,omegaScale]; linarith only [hlo,hhi]
  have hc (c : ℝ) (hc : 0<c) := cubic_power_const hT hTunbounded hc
  have hTscale := isPowerAsymptotic_self T
  have hU : IsPowerAsymptotic U T v := by
    convert ((hc u hu).mul hTscale hT).div (cubic_power_natpow hPT hT 3) hT using 1
    ring
  have hw : IsPowerAsymptotic w T omegaScale := by simpa using cubic_power_rpow hTscale hT omegaScale
  let g₁ := fun i => (P i)^η*((P i)^11*U i)
  let g₂ := fun i => (P i)^η*(w i*(P i)^12*(U i)^((5:ℝ)/2))
  let g₃ := fun i => (P i)^η*((P i)^(11+(13/84+η)+(55/84+η))*
    (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η)))
  have hg₁ : IsPowerAsymptotic g₁ T (α*η+(α*11+v)) :=
    (cubic_power_rpow hPT hT η).mul ((cubic_power_natpow hPT hT 11).mul hU hT) hT
  have hg₂ : IsPowerAsymptotic g₂ T (α*η+(omegaScale+α*12+v*(5/2))) :=
    (cubic_power_rpow hPT hT η).mul
      ((hw.mul (cubic_power_natpow hPT hT 12) hT).mul (cubic_power_rpow hU hT (5/2)) hT) hT
  have hg₃ : IsPowerAsymptotic g₃ T
      (α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))) :=
    (cubic_power_rpow hPT hT η).mul
      (((cubic_power_rpow hPT hT _).mul (cubic_power_rpow hU hT _) hT).mul
        (cubic_power_rpow hw hT _) hT) hT
  have hexp₁ : α*η+(α*11+v)<12*β+4*η := by
    have hid : α*η+(α*11+v)=12*β₁+η*α := by dsimp only [v,β₁]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hα1.le hη.le
    linarith only [hh,hβ₁,hη]
  have hexp₂ : α*η+(omegaScale+α*12+v*(5/2))<12*β+4*η := by
    have hid : α*η+(omegaScale+α*12+v*(5/2))=12*β₂+η*α := by dsimp only [v,omegaScale,β₂]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hα1.le hη.le
    linarith only [hh,hβ₂,hη]
  have hexp₃ :
      α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))<
        12*β+4*η := by
    have hid : α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))=
        12*β₂+η*(3*α+3*v/2-omegaScale) := by dsimp only [v,omegaScale,β₂]; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hcoef hη.le
    linarith only [hh,hβ₂,hη]
  have hb₁ := cubic_power_eventually_le hg₁ hT hexp₁
  have hb₂ := cubic_power_eventually_le hg₂ hT hexp₂
  have hb₃ := cubic_power_eventually_le hg₃ hT hexp₃
  have hP1 := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_ge_atTop 1)
  have hPTle := cubic_power_eventually_le hPT hT hα1
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hlogT := (Real.tendsto_log_atTop.comp hTtop).eventually (eventually_ge_atTop 1)
  have hlogPower := hTtop.eventually
    (eventually_const_log_pow_le_rpow ((2:ℝ)^36) (by positivity) 36 hη)
  filter_upwards [hb₁,hb₂,hb₃,hP1,hPTle,hlogT,hlogPower] with i hi₁ hi₂ hi₃ hPi hPTi hlogi hlogPoweri
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hPp : 0<P i := zero_lt_one.trans_le hPi
  have hlogP := Real.log_nonneg hPi
  change 1≤Real.log (T i) at hlogi
  have hlog : (1+Real.log (P i))^36≤(T i)^η := by
    have hlogPT : Real.log (P i)≤Real.log (T i) := by
      apply Real.log_le_log hPp
      simpa only [Real.rpow_one] using hPTi
    calc
      _ ≤ (2*Real.log (T i))^36 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogPT,hlogi]) 36
      _ = (2:ℝ)^36*(Real.log (T i))^36 := mul_pow _ _ _
      _ ≤ _ := hlogPoweri
  have hsum : g₁ i+g₂ i+g₃ i≤3*(T i)^(12*β+4*η) := by
    linarith only [hi₁,hi₂,hi₃]
  have hg0 : 0≤g₁ i+g₂ i+g₃ i := by dsimp only [g₁,g₂,g₃,U,w]; positivity
  calc
    _ = (1+Real.log (P i))^36*(g₁ i+g₂ i+g₃ i) := by dsimp only [g₁,g₂,g₃]; ring
    _ ≤ (T i)^η*(3*(T i)^(12*β+4*η)) := mul_le_mul hlog hsum hg0 (by positivity)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hTi]; congr 2; ring

end TaoTrudgianYang2025.CubicJointCount
