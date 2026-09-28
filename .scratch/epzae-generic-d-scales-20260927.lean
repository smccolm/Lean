import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.SargosDProcessGeometry
noncomputable section
open Set Expdb Filter
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

theorem sargosD_fallthrough_interval {a b : ℝ}
    (hsecondary : 1/12+2*a/3 ≤ b)
    (hRS : b < (1+9*a)/13)
    (hhigh : 5/12 ≤ a → b < 1/12+2*a/3) :
    1/4 < a ∧ a < 5/12 := by
  constructor
  · linarith only [hsecondary,hRS]
  · by_contra hh
    exact (not_lt_of_ge hsecondary) (hhigh (le_of_not_gt hh))

theorem sargosD_fallthrough_physical {a b h : ℝ}
    (ha : 1/4 < a) (ha' : a < 5/12)
    (hh : (4*a-1)/6 ≤ h) (hb : b=(4*a+1+2*h)/8)
    (hRS : b < (1+9*a)/13) :
    0<h ∧ h<1 ∧ 0<4*a-1-5*h ∧ 0<4*a-1-3*h ∧
      4*a-1-3*h<a ∧ 4*a-1-3*h<b ∧ 2*h<b ∧ b<a ∧
      1-4*a+4*h<0 ∧ 4*a-1-6*h≤0 ∧
      1-2*a+(4*a-1-3*h)+(4*a-1-5*h)<1 := by
  have hupper : h < (20*a-5)/26 := by linarith only [hb,hRS]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith only [ha,ha',hh,hb,hupper,hRS]

/-- The new analytic beta line removes the old curvature-sign obstruction.
The assumptions are only numerical fallthroughs from genuine proved beta
bounds and the actual D scale; no analytic conclusion is assumed. -/
theorem sargosD_refined_fallthrough_curvature
    {k l a b h : ℝ}
    (hk : 0≤k) (hl : 1/2≤l)
    (ha : 1/4<a) (ha' : a<5/12)
    (hh : (4*a-1)/6≤h) (hb : b=(4*a+1+2*h)/8)
    (hD : ((2*k+4*l)*a-l)/(2+5*k+3*l)≤h)
    (hP : b<k+(l-k)*a)
    (hB : b<l-1/2+(k-l+1)*a)
    (hnew : 2/5<a →
      b < max (1/12+2*a/3) (241/1164+425*a/1164)) :
    0<1-3*a+2*h := by
  have hd : 0<2+5*k+3*l := by linarith only [hk,hl]
  have hbudget := (div_le_iff₀ hd).mp hD
  have hs : 3/4+h/2<k+l := by rw [hb] at hP hB; linarith only [hP,hB]
  by_contra hbad
  have hmu : 1-3*a+2*h≤0 := le_of_not_gt hbad
  have ha40 : 2/5≤a := by linarith only [hh,hmu]
  have hh0 : 0≤h := by linarith only [hh,ha]
  have hcoef : 0<2*a-5*h := by linarith only [hmu,ha']
  have hdelta : 0≤2*a-1+2*h := by linarith only [hh,ha40]
  have hsum := mul_lt_mul_of_pos_left hs hcoef
  have hlower := mul_le_mul_of_nonneg_left hl hdelta
  have hpoly : (5/2)*a-1/2+(a-19/4)*h-(5/2)*h^2<0 := by
    nlinarith only [hbudget,hsum,hlower]
  have hlinear : a/2-3/32<h := by
    by_contra hn
    have hlin : h≤a/2-3/32 := le_of_not_gt hn
    have hlin0 : 0≤a/2-3/32 := hh0.trans hlin
    have hsq := pow_le_pow_left₀ hh0 hlin 2
    have hprod := mul_le_mul_of_nonpos_left hlin
      (show a-19/4≤0 by linarith only [ha'])
    have hupper : a≤5/12 := ha'.le
    have hasq := pow_le_pow_left₀ (show 0≤a by linarith only [ha40]) hupper 2
    nlinarith only [hpoly,hprod,hsq,hasq,ha40]
  have hanew : 2/5<a := by linarith only [hlinear,hmu]
  have hsecondary : 1/12+2*a/3≤b := by rw [hb]; linarith only [hh]
  have hline : b<241/1164+425*a/1164 := by
    have hhnew := hnew hanew
    rcases lt_max_iff.mp hhnew with hc|hc
    · exact False.elim ((not_lt_of_ge hsecondary) hc)
    · exact hc
  rw [hb] at hline
  linarith only [hline,hlinear,hmu]

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

private theorem cubic_dyadic_index_bound
    {T X : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {q η : ℝ} (hq : 0 < q) (hη : 0 < η)
    (hX : ∀ᶠ i in atTop, 1 ≤ X i ∧ X i ≤ (T i)^q) :
    ∀ᶠ i in atTop, ∃ J : ℕ, X i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η := by
  let γ := η/(2*q)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨D,hD,hcount⟩ := exists_dyadic_count_sq_le_rpow hγ
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hconstant := hTtop.eventually (eventually_const_mul_rpow_le_rpow
    (D := 2*D*(2:ℝ)^γ) (a := η/2) (b := η) (by linarith))
  filter_upwards [hX,hconstant] with i hi hconst
  obtain ⟨J,hJlo,hJhi⟩ := exists_dyadic_cutoff hi.1
  refine ⟨J,hJlo,?_⟩
  have hJ := hcount J
  have hj : (J:ℝ)+2 ≤ 2*((J:ℝ)+1)^2 := by
    nlinarith only [(Nat.cast_nonneg J : (0:ℝ) ≤ J),sq_nonneg (J:ℝ)]
  have hTp : 0 < T i := zero_lt_one.trans_le (hT i)
  calc
    _ ≤ 2*(D*((2:ℝ)^J)^γ) := hj.trans (by gcongr)
    _ ≤ 2*(D*(2*(T i)^q)^γ) := by gcongr; exact hJhi.trans (by gcongr; exact hi.2)
    _ = (2*D*2^γ)*(T i)^(η/2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hTp.le]
      have he : q*γ=η/2 := by dsimp [γ]; field_simp
      rw [he]
      ring
    _ ≤ _ := hconst




theorem eventually_cubic_generic_parameters
    {T N : VariableObject ℝ} {α h σ κ₀ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h) (hσ : 0<σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 := by
  intro r H Y lam B L U Qcut
  let q := 4*α-1-3*h
  obtain ⟨hh,_hh1,hr,hq,hqα,_hqβ,_h2hβ,_hβα,hTaylor,_he2,_he5⟩ :=
    sargosD_fallthrough_physical hlo hhi hsecondary rfl hRS
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by
    simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1) (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hL : IsPowerAsymptotic L T (1-3*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 2)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1) (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hLH : IsPowerAsymptotic (fun i => L i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hL.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hshift : IsPowerAsymptotic (fun i => 4*U i*Qcut i*(N i)^2/(σ*T i)) T (q-α) := by
    convert ((((hc 4 (by norm_num)).mul hU hT).mul hQ hT).mul
      (cubic_power_natpow hNT hT 2) hT).div ((hc σ hσ).mul hTscale hT) hT using 1
    ring
  have htaylor : IsPowerAsymptotic (fun i => 16*B i*(H i:ℝ)^4) T (1-4*α+4*h) := by
    convert ((hc 16 (by norm_num)).mul hB hT).mul
      (cubic_power_natpow hH hT 4) hT using 1
    ring
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hHlarge := (hH.tendsto_atTop_of_pos hh hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hYlarge := (hY.tendsto_atTop_of_pos hr hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hQlarge := (hQ.tendsto_atTop_of_pos hq hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hLHlarge := (hLH.tendsto_atTop_of_pos
    hcurvature hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hshiftsmall := (hshift.tendsto_zero_of_neg
    (sub_neg.mpr hqα) hT hTunbounded).eventually
    (eventually_lt_nhds hκ₀)
  have htaylorsmall := (htaylor.tendsto_zero_of_neg
    hTaylor hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hindex := cubic_dyadic_index_bound hT hTunbounded
    (by linarith only [hq] : 0 < q+1) hη
    (hQlarge.and (cubic_power_eventually_le hQ hT (by linarith : q<q+1)))
  filter_upwards [hNlarge,hHlarge,hYlarge,hLHlarge,hshiftsmall,htaylorsmall,hindex,hQlarge]
    with i hNi hHi hYi hLHi hsi hti hJi hQi
  obtain ⟨J,hJq,hJcount⟩ := hJi
  refine ⟨hNi,by exact_mod_cast hHi,hYi,J,hQi,hJq,hJcount,?_,hsi.le,?_⟩
  · have hHp : (0:ℝ) < H i := by linarith only [hHi]
    apply (div_le_iff₀ (by positivity : 0 < 4*(H i:ℝ)^2)).mpr
    nlinarith only [hLHi]
  · have hBp : 0 < B i := by
      dsimp [B]
      positivity [modelPhaseJetCoefficient_pos hσ 3,zero_lt_one.trans_le (hT i)]
    have hsum : (H i:ℝ)+1 ≤ 2*(H i:ℝ) := by linarith only [hHi]
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H i:ℝ)+1) hsum 4
    have hm := mul_le_mul_of_nonneg_left hp hBp.le
    nlinarith only [hm,hti]

theorem eventually_cubic_generic_cost
    {T N : VariableObject ℝ} {k l α h σ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h)
    (hopt : (2*k+4*l)*α-l≤h*(2+5*k+3*l))
    (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let β := (4*α+1+2*h)/8
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(k+η)*(Qcut i)^(l+η)*(Y i)^(k+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) := by
  intro r β H Y lam B U Qcut
  let q := 4*α-1-3*h
  let V := fun i => U i/(lam i*(H i:ℝ)^2)
  let f₁ := fun i => V i/N i
  let f₂ := fun i => V i*(B i/((lam i)^2*(H i:ℝ)^4))/N i
  let f₃ := fun i => V i*(Qcut i/(H i:ℝ))/N i
  let f₄ := fun i => V i*(Qcut i/Y i)/N i
  let f₅ := fun i => V i*((T i/(N i)^2)^(k+η)*(Qcut i)^(l+η)*(Y i)^(k+η))/N i
  let f₆ := fun i => V i*((N i)^2/T i)/N i
  obtain ⟨hh,hh1,_hr,_hq,_hqα,hqβ,h2hβ,_hβα,_hTaylor,he₂,he₅⟩ :=
    sargosD_fallthrough_physical hlo hhi hsecondary rfl hRS
  change q<β at hqβ
  change 2*h<β at h2hβ
  change 1-2*α+q+r<1 at he₅
  have hTscale := isPowerAsymptotic_self T
  have hH : IsPowerAsymptotic (fun i => (H i:ℝ)) T h :=
    isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hY : IsPowerAsymptotic Y T r := by simpa using cubic_power_rpow hTscale hT r
  have hc (c : ℝ) (hc : 0 < c) := cubic_power_const hT hTunbounded hc
  have hlam : IsPowerAsymptotic lam T (1-4*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 3)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hQ : IsPowerAsymptotic Qcut T q := by
    convert (hc 3 (by norm_num)).div
      (((hc 2 (by norm_num)).mul hlam hT).mul (cubic_power_natpow hH hT 3) hT) hT using 1
    dsimp [q]
    ring
  have hV : IsPowerAsymptotic V T (α-2*h) := by
    convert hU.div (hlam.mul (cubic_power_natpow hH hT 2) hT) hT using 1
    ring
  have hf₁ : IsPowerAsymptotic f₁ T (-2*h) := by
    convert hV.div hNT hT using 1
    ring
  have hf₂ : IsPowerAsymptotic f₂ T (4*α-1-6*h) := by
    convert (hV.mul (hB.div ((cubic_power_natpow hlam hT 2).mul
      (cubic_power_natpow hH hT 4) hT) hT) hT).div hNT hT using 1
    ring
  have hf₃ : IsPowerAsymptotic f₃ T (4*α-1-6*h) := by
    convert (hV.mul (hQ.div hH hT) hT).div hNT hT using 1
    dsimp [q]
    ring
  have hf₄ : IsPowerAsymptotic f₄ T 0 := by
    convert (hV.mul (hQ.div hY hT) hT).div hNT hT using 1
    dsimp [q,r]
    ring
  have hf₅ : IsPowerAsymptotic f₅ T ((2*k+4*l)*α-l-h*(2+5*k+3*l)+η*(1-2*α+q+r)) := by
    convert (hV.mul (((cubic_power_rpow (hTscale.div
      (cubic_power_natpow hNT hT 2) hT) hT (k+η)).mul
        (cubic_power_rpow hQ hT (l+η)) hT).mul
          (cubic_power_rpow hY hT (k+η)) hT) hT).div hNT hT using 1
    dsimp [q,r]
    ring
  have hf₆ : IsPowerAsymptotic f₆ T (2*α-1-2*h) := by
    convert (hV.mul ((cubic_power_natpow hNT hT 2).div hTscale hT) hT).div hNT hT using 1
    ring
  have hmain : IsPowerAsymptotic
      (fun i => (N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η) T (8*β+h*η) := by
    convert (((cubic_power_natpow hNT hT 7).mul hU hT).mul
      (cubic_power_natpow hH hT 2) hT).mul (cubic_power_rpow hH hT η) hT using 1
    dsimp [β]
    ring
  have hwidth : IsPowerAsymptotic (fun i => U i*(H i:ℝ)^2) T (1-3*α+2*h) := by
    convert hU.mul (cubic_power_natpow hH hT 2) hT using 1
    ring
  have hhβ : h<β := by linarith only [hh,h2hβ]
  have hβ : 0<β := by linarith only [hh,hhβ]
  have he₆ : 2*α-1-2*h<0 := by linarith only [hhi,hh]
  have hb₁ := cubic_power_eventually_le hf₁ hT (by linarith only [hh,hη] : -2*h<2*η)
  have hb₂ := cubic_power_eventually_le hf₂ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₃ := cubic_power_eventually_le hf₃ hT (by linarith only [he₂,hη] : 4*α-1-6*h<2*η)
  have hb₄ := cubic_power_eventually_le hf₄ hT (by linarith only [hη] : 0<2*η)
  have hb₅ := cubic_power_eventually_le hf₅ hT
    (by
      have hh := mul_lt_mul_of_pos_left he₅ hη
      linarith only [hopt,hh,hη] :
        (2*k+4*l)*α-l-h*(2+5*k+3*l)+η*(1-2*α+q+r)<2*η)
  have hb₆ := cubic_power_eventually_le hf₆ hT (by linarith only [he₆,hη] : 2*α-1-2*h<2*η)
  have hbmain := cubic_power_eventually_le hmain hT
    (by nlinarith only [hh1,hη] : 8*β+h*η<8*β+2*η)
  have hbH := cubic_power_eventually_le hH hT hhβ
  have hbH₂ := cubic_power_eventually_le (cubic_power_natpow hH hT 2) hT
    (by linarith only [h2hβ] : h*2<β)
  have hbQ := cubic_power_eventually_le hQ hT hqβ
  have hbwidth := (hwidth.tendsto_atTop_of_pos
    hcurvature hT hTunbounded).eventually
      (eventually_ge_atTop 1)
  have hNlarge := (hNT.tendsto_atTop_of_pos
    (by linarith only [hlo] : 0 < α) hT hTunbounded).eventually (eventually_gt_atTop 0)
  filter_upwards [hb₁,hb₂,hb₃,hb₄,hb₅,hb₆,hbmain,hbH,hbH₂,hbQ,hbwidth,hNlarge]
    with i h₁ h₂ h₃ h₄ h₅ h₆ hm hHi hH₂i hQi hwi hNi
  intro J hJ E
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hHp : (0:ℝ) < H i := by exact_mod_cast floorRpow_pos T h i
  have hUp : 0 < U i := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hlampos : 0 < lam i := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQp : 0 < Qcut i := by dsimp [Qcut]; positivity
  have hVp : 0 < V i := by dsimp [V]; positivity
  have hsum : f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i ≤ 6*(T i)^(2*η) := by
    linarith only [h₁,h₂,h₃,h₄,h₅,h₆]
  have heq : E=((J:ℝ)+2)*N i*(f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i) := by
    dsimp [E,f₁,f₂,f₃,f₄,f₅,f₆,V]
    field_simp
  have hE : E ≤ 6*N i*(T i)^(3*η) := by
    rw [heq]
    calc
      _ ≤ ((J:ℝ)+2)*N i*(6*(T i)^(2*η)) := by gcongr
      _ ≤ (T i)^η*N i*(6*(T i)^(2*η)) := by gcongr
      _ = _ := by
        rw [show (T i)^η*N i*(6*(T i)^(2*η)) =
          6*N i*((T i)^η*(T i)^(2*η)) by ring,← Real.rpow_add hTi]
        congr 2
        ring
  have hone₃ : 1 ≤ (T i)^(3*η) := Real.one_le_rpow (hT i) (by positivity)
  have hNE : N i+E ≤ 7*N i*(T i)^(3*η) := by
    have hn := mul_le_mul_of_nonneg_left hone₃ hNi.le
    nlinarith only [hE,hn]
  have hUW : 1+U i*(H i:ℝ)^2 ≤ 2*U i*(H i:ℝ)^2 := by linarith only [hwi]
  have hcost : (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η ≤
      14*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (N i)^6*(7*N i*(T i)^(3*η))*(2*U i*(H i:ℝ)^2)*(H i:ℝ)^η := by gcongr
      _ = 14*((N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η)*(T i)^(3*η) := by ring
      _ ≤ 14*(T i)^(8*β+2*η)*(T i)^(3*η) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add hTi]; congr 2; ring
  have honeβ : 1 ≤ (T i)^β := Real.one_le_rpow (hT i) hβ.le
  have hR : (H i:ℝ)^2+Qcut i+1 ≤ 3*(T i)^β := by
    linarith only [hH₂i,hQi,honeβ]
  have hH8 : (H i:ℝ)^8 ≤ (T i)^(8*β+5*η) := by
    calc
      _ ≤ ((T i)^β)^8 := pow_le_pow_left₀ hHp.le hHi 8
      _ = (T i)^(8*β) := by rw [← Real.rpow_mul_natCast hTi.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])
  have hR8 : ((H i:ℝ)^2+Qcut i+1)^8 ≤ 3^8*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (3*(T i)^β)^8 := pow_le_pow_left₀ (by positivity) hR 8
      _ = 3^8*(T i)^(8*β) := by
        rw [mul_pow,← Real.rpow_mul_natCast hTi.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])) (by norm_num)
  linarith only [hcost,hH8,hR8]

theorem isExponentSumBound_cubic_generic
    {k l h : ℝ} {α : ℝ≥0} (hpair : ExponentPair k l)
    (hlo : 1/4<(α:ℝ)) (hhi : (α:ℝ)<5/12)
    (hsecondary : (4*(α:ℝ)-1)/6≤h)
    (hRS : (4*(α:ℝ)+1+2*h)/8<(1+9*(α:ℝ))/13)
    (hcurvature : 0<1-3*(α:ℝ)+2*h)
    (hopt : (2*k+4*l)*(α:ℝ)-l≤h*(2+5*k+3*l)) :
    IsExponentSumBound α ((4*(α:ℝ)+1+2*h)/8) := by
  intro N T F a b _hN hT hTunbounded hNT hF hab
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T ((4*(α:ℝ)+1+2*h)/8) hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0 < η := lt_min (by norm_num) hε
  have hηε : η ≤ ε := min_le_right _ _
  have hηsmall : k+η < 1 := by
    have hh : η ≤ (1:ℝ)/100 := min_le_left _ _
    linarith [hpair.inTriangle.2.1]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    TaoTrudgianYang2025.CubicJointCount.exists_complete_cubic_eighth_estimate
      hσ hpair hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_cubic_generic_parameters hlo hhi hsecondary hRS hcurvature hσ hκ₀ hη hT hTunbounded hNT
  have hcost := eventually_cubic_generic_cost hlo hhi hsecondary hRS hcurvature hopt hσ hη hT hTunbounded hNT
  let β := (4*(α:ℝ)+1+2*h)/8
  let C := max 1 (C₀*(15+3^8))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀*(15+3^8) ≤ C := le_max_right _ _
  have hCpow : C ≤ C^8 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C^7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _ = _ := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hNi,hHi,hYi,J,hQi,hQJ,hJ,hcurv,hshift,hTaylor⟩ := hpi
  have hTi : 0 < T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (N i)
    ((T i)^(4*(α:ℝ)-1-5*h)) (a i) (b i)
    (floorRpow T h i) J
    hFi hTi hNi hHi hYi (hab i).1 (hab i).2
    hQi hQJ hcurv hshift hTaylor
  have hmajor := mul_le_mul_of_nonneg_left (hci J hJ) hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      C₀*(15+3^8)*(T i)^(8*β+5*η) := by
    exact hs.trans (by convert hmajor using 1; ring)
  have hexp : 8*β+5*η ≤ (β+ε)*8 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      (C*(T i)^(β+ε))^8 := by
    calc
      _ ≤ C₀*(15+3^8)*(T i)^(8*β+5*η) := hbound
      _ ≤ C^8*(T i)^((β+ε)*8) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0 ≤ C*(T i)^(β+ε)) (by norm_num : (8:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh


/-- The exact max-balanced Taylor scale realizes the printed D beta line. -/
theorem sargosD_balanced_scale {k l a : ℝ} (hk : 0≤k) (hl : 0≤l) :
    let h := max (((2*k+4*l)*a-l)/(2+5*k+3*l)) ((4*a-1)/6)
    max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) a)
      (1/12+2*a/3) = (4*a+1+2*h)/8 := by
  intro h
  let hD := ((2*k+4*l)*a-l)/(2+5*k+3*l)
  have hd : 2+5*k+3*l≠0 := by positivity
  have hd' : 5*k+3*l+2≠0 := by positivity
  have hid : exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) a=
      (4*a+1+2*hD)/8 := by
    dsimp only [exponentPairLine,sargosDProcessK,sargosDProcessL,hD]
    field_simp
    ring
  rw [hid]
  have hDle : hD≤h := le_max_left _ _
  have hsle : (4*a-1)/6≤h := le_max_right _ _
  apply le_antisymm
  · apply max_le <;> linarith only [hDle,hsle]
  · rcases le_total hD ((4*a-1)/6) with hc|hc
    · have he : h=(4*a-1)/6 := max_eq_right hc
      rw [he]
      exact le_trans (by linarith) (le_max_right _ _)
    · have he : h=hD := max_eq_left hc
      rw [he]
      exact le_max_left _ _

/-- Unconditional half-interval Sargos D bound, using the actual input pair
and the refined beta theorem to discharge the curvature-sign fallthrough. -/
theorem exponentSumGrowthExponent_le_sargosD_half
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) := by
  let β := max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
    (1/12+2*(α:ℝ)/3)
  have hsec : 1/12+2*(α:ℝ)/3≤β := le_max_right _ _
  have hα1 : (α:ℝ)≤1 := by linarith only [hhalf]
  by_cases hPc : exponentPairLine k l α≤β
  · exact (exponentSumGrowthExponent_le_exponentPairLine_closed hpair α hα1).trans hPc
  have hP : β<k+(l-k)*(α:ℝ) := lt_of_not_ge hPc
  by_cases hBc : exponentPairLine (l-1/2) (k+1/2) α≤β
  · exact (exponentSumGrowthExponent_le_exponentPairLine_closed hpair.bProcess α hα1).trans hBc
  have hB : β<l-1/2+(k-l+1)*(α:ℝ) := by
    have hh := lt_of_not_ge hBc
    convert hh using 1
    unfold exponentPairLine
    ring
  have hRSbound : exponentSumGrowthExponent α≤(1+9*(α:ℝ))/13 := by
    have hh := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_robertSargos α hα1
    convert hh using 1
    unfold exponentPairLine
    ring
  by_cases hRSc : (1+9*(α:ℝ))/13≤β
  · exact hRSbound.trans hRSc
  have hRS : β<(1+9*(α:ℝ))/13 := lt_of_not_ge hRSc
  by_cases hhigh : 5/12≤(α:ℝ)
  · have hbound : exponentSumGrowthExponent α≤1/12+2*(α:ℝ)/3 := by
      by_cases hm : (α:ℝ)≤3/7
      · have hh := exponentSumGrowthExponent_le_bourgain_table_second hhigh hm
        linarith only [hh]
      · have hh := exponentSumGrowthExponent_le_bourgain_baseline (le_of_not_ge hm) hhalf
        linarith only [hh,le_of_not_ge hm]
    exact hbound.trans hsec
  have hhi : (α:ℝ)<5/12 := lt_of_not_ge hhigh
  have hlo : 1/4<(α:ℝ) := by linarith only [hsec,hRS]
  by_cases hnewCover : 2/5<(α:ℝ) ∧
      max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)≤β
  · exact (exponentSumGrowthExponent_le_refined_bourgain hnewCover.1
      (by linarith only [hhi])).trans hnewCover.2
  have hnew : 2/5<(α:ℝ) →
      β < max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164) := by
    intro ha
    exact lt_of_not_ge (fun hh => hnewCover ⟨ha,hh⟩)
  have hk : 0≤k := hpair.inTriangle.1
  have hl : 1/2≤l := hpair.inTriangle.2.2.1
  have hl0 : 0≤l := by linarith only [hl]
  let h := max (((2*k+4*l)*(α:ℝ)-l)/(2+5*k+3*l)) ((4*(α:ℝ)-1)/6)
  have hb : β=(4*(α:ℝ)+1+2*h)/8 := sargosD_balanced_scale hk hl0
  have hsecondary : (4*(α:ℝ)-1)/6≤h := le_max_right _ _
  have hD : ((2*k+4*l)*(α:ℝ)-l)/(2+5*k+3*l)≤h := le_max_left _ _
  have hcurvature := sargosD_refined_fallthrough_curvature hk hl hlo hhi
    hsecondary hb hD hP hB hnew
  have hden : 0<2+5*k+3*l := by positivity
  have hopt := (div_le_iff₀ hden).mp hD
  have hRS' : (4*(α:ℝ)+1+2*h)/8<(1+9*(α:ℝ))/13 := by rw [←hb]; exact hRS
  have hbound := isExponentSumBound_cubic_generic hpair hlo hhi hsecondary hRS' hcurvature hopt
  have hh := exponentSumGrowthExponent_le_iff.mpr hbound
  change exponentSumGrowthExponent α≤β
  simpa only [hb] using hh

/-- Exact printed D-process source contract on the full closed unit interval.
The upper half follows from the proved reflection of the actual beta function. -/
theorem exponentSumGrowthExponent_le_sargosD
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) := by
  by_cases hhalf : (α:ℝ)≤1/2
  · exact exponentSumGrowthExponent_le_sargosD_half hpair hhalf
  have hαNN : α≤1 := by exact_mod_cast hα
  let γ : ℝ≥0 := 1-α
  have hγreal : (γ:ℝ)=1-(α:ℝ) := NNReal.coe_sub hαNN
  have hγhalf : (γ:ℝ)≤1/2 := by rw [hγreal]; linarith only [le_of_not_ge hhalf]
  have hγ : (γ:ℝ)≤1 := by linarith only [hγhalf]
  have hγNN : γ≤1 := by exact_mod_cast hγ
  have hdouble : (1-γ:ℝ≥0)=α := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hγNN,hγreal]
    norm_num
  have hrefl := exponentSumGrowthExponent_reflection hγ
  rw [hdouble] at hrefl
  have hb := exponentSumGrowthExponent_le_sargosD_half hpair hγhalf
  have hk : 0≤k := hpair.inTriangle.1
  have hl : 0≤l := by linarith [hpair.inTriangle.2.2.1]
  calc
    _ = 1/2-(γ:ℝ)+exponentSumGrowthExponent γ := hrefl
    _ ≤ 1/2-(γ:ℝ)+max
        (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) γ)
        (1/12+2*(γ:ℝ)/3) := add_le_add le_rfl hb
    _ ≤ _ := by
      rw [add_max,hγreal]
      apply max_le
      · exact (exponentPairLine_reflected_le (sargosDProcess_slope hk hl)
          (le_of_not_ge hhalf)).trans (le_max_left _ _)
      · have hh : 1/2-(1-(α:ℝ))+(1/12+2*(1-(α:ℝ))/3)≤1/12+2*(α:ℝ)/3 := by
          linarith only [le_of_not_ge hhalf]
        exact hh.trans (le_max_right _ _)

/-- Where the printed secondary line is dominated, the exact analytic
D beta contract yields the D-transformed exponent pair. -/
theorem exponentPair_sargosD {k l : ℝ}
    (hpair : ExponentPair k l) (hzero : 0≤5*k-3*l+2) (hhalf : 2≤k+3*l) :
    ExponentPair (sargosDProcessK k l) (sargosDProcessL k l) :=
  sargosDProcess_pair_of_beta_bound hpair.inTriangle.1
    (by linarith [hpair.inTriangle.2.2.1]) hzero hhalf
    (fun α hα => by
      have hh := exponentSumGrowthExponent_le_sargosD_half hpair hα
      convert hh using 1
      congr 1
      ring)

#print axioms sargosD_fallthrough_interval
#print axioms sargosD_fallthrough_physical
#print axioms sargosD_refined_fallthrough_curvature
#print axioms eventually_cubic_generic_parameters
#print axioms eventually_cubic_generic_cost
#print axioms isExponentSumBound_cubic_generic
#print axioms sargosD_balanced_scale
#print axioms exponentSumGrowthExponent_le_sargosD_half
#print axioms exponentSumGrowthExponent_le_sargosD
#print axioms exponentPair_sargosD

end TaoTrudgianYang2025.CubicJointCount
