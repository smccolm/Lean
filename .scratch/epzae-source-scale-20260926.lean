import TaoTrudgianYang2025.HeathBrownModelJets
import TaoTrudgianYang2025.PointMeanLemmaThreeEdges
import Mathlib.Algebra.Order.Floor.Semifield

noncomputable section
open Set Filter Expdb
open scoped Topology
namespace TaoTrudgianYang2025.NextPhysical

private theorem source_smallness_of_scale
    {c C D T P R n : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hT : 0 ≤ T) (hP : 0<P) (hR : 0<R)
    (hn : 1 ≤ n) (hupper : n ≤ P/R)
    (hfirst : 16*D*P^2 ≤ c^2*T)
    (hfour : D*7^4*T ≤ R^4)
    (hthird : (49*C/4)*T ≤ P*R^2) :
    let L := c*T/P^3
    let U := C*T/P^3/6
    let F := D*T/P^4
    F ≤ L^2/16 ∧ F*(6*n+1)^4 ≤ 1 ∧ (3*U/2)*(6*n+1)^2 ≤ 1 := by
  intro L U F
  have hsum : 6*n+1 ≤ 7*P/R := by
    calc
      6*n+1 ≤ 7*n := by linarith only [hn]
      _ ≤ 7*(P/R) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = _ := by ring
  have hs0 : 0 ≤ 6*n+1 := by linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hU : 0 ≤ 3*U/2 := by dsimp [U]; positivity
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ T/(16*P^6) by positivity)
    convert hh using 1 <;> dsimp only [F,L] <;> field_simp
  · calc
      F*(6*n+1)^4 ≤ F*(7*P/R)^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsum 4) hF
      _ = D*7^4*T/R^4 := by dsimp only [F]; field_simp
      _ ≤ 1 := (div_le_one (pow_pos hR 4)).mpr hfour
  · calc
      (3*U/2)*(6*n+1)^2 ≤ (3*U/2)*(7*P/R)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsum 2) hU
      _ = ((49*C/4)*T)/(P*R^2) := by dsimp only [U]; field_simp; ring
      _ ≤ 1 := (div_le_one (mul_pos hP (pow_pos hR 2))).mpr hthird

private theorem eventually_model_block_smallness
    {σ a b δ : ℝ} (hσ : 0<σ)
    (hfour : 1<4*b) (hthird : 1<a-δ+2*b)
    (hfirst : 2*(a+δ)<1) (hlen : b<a-δ) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0<P →
      T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let R := T^b
      let N : ℕ := ⌊P/R⌋₊
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      0<N ∧ P/(2*R) ≤ (N:ℝ) ∧ (N:ℝ) ≤ P/R ∧
      F ≤ L^2/16 ∧ F*(6*(N:ℝ)+1)^4 ≤ 1 ∧
        (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
  let c := modelPhaseJetLower σ 2
  let C := modelPhaseJetCoefficient σ 2+1
  let D := modelPhaseJetCoefficient σ 3+1
  have hc : 0<c := modelPhaseJetLower_pos hσ 2
  have hC : 0<C := by have h := modelPhaseJetCoefficient_pos hσ 2; dsimp [C]; linarith
  have hD : 0<D := by have h := modelPhaseJetCoefficient_pos hσ 3; dsimp [D]; linarith
  have he1 := eventually_const_mul_rpow_le_rpow (D:=16*D/c^2) hfirst
  have he4 := eventually_const_mul_rpow_le_rpow (D:=D*7^4) hfour
  have he3 := eventually_const_mul_rpow_le_rpow (D:=49*C/4) hthird
  have hel := eventually_const_mul_rpow_le_rpow (D:=(2:ℝ)) hlen
  filter_upwards [he1,he4,he3,hel,eventually_gt_atTop (0:ℝ)] with T h1 h4 h3 hl hT
  intro P hP hlo hhi R N L U F
  have hR : 0<R := Real.rpow_pos_of_pos hT b
  have hrange : 2 ≤ P/R := (le_div_iff₀ hR).mpr (hl.trans hlo)
  have hNat : 1 ≤ N := Nat.le_floor (by norm_num; linarith only [hrange])
  have hNr : 1 ≤ (N:ℝ) := by exact_mod_cast hNat
  have hupper : (N:ℝ) ≤ P/R := Nat.floor_le (div_pos hP hR).le
  have hlower : P/(2*R) ≤ (N:ℝ) := by
    have hh := (Nat.div_two_lt_floor (show 1 ≤ P/R by linarith only [hrange])).le
    convert hh using 1
    ring
  have hP2 : P^2 ≤ T^(2*(a+δ)) := by
    calc
      P^2 ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hhi 2
      _ = _ := by rw [← Real.rpow_mul_natCast hT.le]; congr 1; ring
  have hphysical1 : 16*D*P^2 ≤ c^2*T := by
    have hscaled := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    rw [Real.rpow_one] at hscaled
    have hcancel : c^2*(16*D/c^2)=16*D := by field_simp
    rw [← mul_assoc,hcancel] at hscaled
    exact (mul_le_mul_of_nonneg_left hP2 (by positivity)).trans hscaled
  have hphysical4 : D*7^4*T ≤ R^4 := by
    rw [Real.rpow_one] at h4
    convert h4 using 1
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hT.le]
    congr 1
    ring
  have hphysical3 : (49*C/4)*T ≤ P*R^2 := by
    rw [Real.rpow_one] at h3
    calc
      _ ≤ T^(a-δ+2*b) := h3
      _ = T^(a-δ)*R^2 := by
        dsimp only [R]
        rw [← Real.rpow_mul_natCast hT.le,← Real.rpow_add hT]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlo (sq_nonneg R)
  exact ⟨by omega,hlower,hupper,
    source_smallness_of_scale hC.le hD.le hT.le hP hR hNr hupper
      hphysical1 hphysical4 hphysical3⟩

private theorem eventually_baseline_model_block_smallness
    {σ a η : ℝ} (hσ : 0<σ) (ha : (3:ℝ)/7 ≤ a) (ha' : a<1/2)
    (hη : 0<η) (hη' : η<1/28) :
    ∃ δ>(0:ℝ), δ ≤ η ∧
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0<P →
      T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let R := T^((2:ℝ)/7+η)
      let N : ℕ := ⌊P/R⌋₊
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      0<N ∧ P/(2*R) ≤ (N:ℝ) ∧ (N:ℝ) ≤ P/R ∧
      F ≤ L^2/16 ∧ F*(6*(N:ℝ)+1)^4 ≤ 1 ∧
        (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
  let δ := min η ((1/2-a)/2)
  have hδ : 0<δ := lt_min hη (by linarith only [ha'])
  have hδη : δ ≤ η := min_le_left _ _
  have hδa : δ ≤ (1/2-a)/2 := min_le_right _ _
  refine ⟨δ,hδ,hδη,?_⟩
  exact eventually_model_block_smallness hσ
    (b:=(2:ℝ)/7+η) (by linarith only [hη])
    (by linarith only [ha,hδη,hη])
    (by linarith only [ha',hδa])
    (by linarith only [ha,hδη,hη'])

private theorem baseline_scale_geometry
    {a δ η T P : ℝ} (ha : (3:ℝ)/7 ≤ a) (hgap : a+δ ≤ 1/2)
    (hδη : δ ≤ η) (hη : 0 ≤ η) (hη' : η ≤ 1/100)
    (hT : 1 ≤ T) (hP : 0<P)
    (hlo : T^(a-δ) ≤ P) (hhi : P ≤ T^(a+δ)) :
    let R := T^((2:ℝ)/7+η)
    1 ≤ P ∧ 1 ≤ R ∧ P^2 ≤ T ∧ P ≤ R^2 ∧ T^2 ≤ R^7 ∧ R^3 ≤ T ∧
      R^33 ≤ T^10 ∧ T ≤ P^3 ∧ T^2 ≤ P^2*R^4 ∧
      R^3/P^2 ≤ T^(5*η) := by
  intro R
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hp : 1 ≤ P := (Real.one_le_rpow hT (by linarith only [ha,hδη,hη'])).trans hlo
  have hr : 1 ≤ R := Real.one_le_rpow hT (by positivity)
  have hP2 : P^2 ≤ T := by
    calc
      _ ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hhi 2
      _ = T^((a+δ)*2) := (Real.rpow_mul_natCast hTp.le _ 2).symm
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hgap])
      _ = T := Real.rpow_one T
  have hPR : P ≤ R^2 := by
    calc
      _ ≤ T^(a+δ) := hhi
      _ ≤ T^(((2:ℝ)/7+η)*2) :=
        Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hgap,hη])
      _ = R^2 := Real.rpow_mul_natCast hTp.le _ 2
  have hseven : T^2 ≤ R^7 := by
    rw [← Real.rpow_natCast T 2]
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hTp.le]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith only [hη])
  have hthree : R^3 ≤ T := by
    calc
      _ = T^(((2:ℝ)/7+η)*3) := (Real.rpow_mul_natCast hTp.le _ 3).symm
      _ ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hη'])
      _ = _ := Real.rpow_one T
  have hthirtythree : R^33 ≤ T^10 := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hTp.le,← Real.rpow_natCast T 10]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith only [hη'])
  have hphase : T ≤ P^3 := by
    calc
      T = T^(1:ℝ) := (Real.rpow_one T).symm
      _ ≤ T^((a-δ)*3) := Real.rpow_le_rpow_of_exponent_le hT
        (by linarith only [ha,hδη,hη'])
      _ = (T^(a-δ))^3 := Real.rpow_mul_natCast hTp.le _ 3
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 3
  have hgamma : T^2 ≤ P^2*R^4 := by
    calc
      T^2 = T^(2:ℝ) := (Real.rpow_natCast T 2).symm
      _ ≤ T^((a-δ)*2+((2:ℝ)/7+η)*4) := Real.rpow_le_rpow_of_exponent_le hT
        (by linarith only [ha,hδη,hη])
      _ = (T^(a-δ))^2*R^4 := by
        rw [Real.rpow_add hTp]
        exact congrArg₂ (fun x y : ℝ => x*y)
          (Real.rpow_mul_natCast hTp.le (a-δ) 2)
          (Real.rpow_mul_natCast hTp.le ((2:ℝ)/7+η) 4)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 2) (by positivity)
  refine ⟨hp,hr,hP2,hPR,hseven,hthree,hthirtythree,hphase,hgamma,?_⟩
  apply (div_le_iff₀ (pow_pos hP 2)).mpr
  have hPlo : (T^(a-δ))^2 ≤ P^2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hlo 2
  calc
    R^3 = T^(((2:ℝ)/7+η)*3) := (Real.rpow_mul_natCast hTp.le _ 3).symm
    _ ≤ T^(5*η+(a-δ)*2) :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith only [ha,hδη])
    _ = T^(5*η)*(T^(a-δ))^2 := by
      rw [Real.rpow_add hTp]
      exact congrArg (fun x : ℝ => T^(5*η)*x) (Real.rpow_mul_natCast hTp.le (a-δ) 2)
    _ ≤ _ := mul_le_mul_of_nonneg_left hPlo (Real.rpow_nonneg hTp.le _)

private theorem normalized_frozen_main_le
    {K T P R Q : ℝ} (hK : 0 ≤ K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hcut : T*Q^2 ≤ K*P^2*R)
    (hscale : T^2 ≤ R^7) :
    (P^2*R/(T*Q^2))^13*(T^6*Q^6/R^18)*(T*Q^2/P^2)^10*
      (T*Q^2/P^2+R^8/T^2) ≤ (K+1)*P^6*T*R^3 := by
  have htri : P^4*T^4*Q^2/R^5 ≤ K*P^6*T^3/R^4 := by
    have hh := mul_le_mul_of_nonneg_left hcut
      (show 0 ≤ P^4*T^3/R^5 by positivity)
    convert hh using 1 <;> field_simp
  have htri' : K*P^6*T^3/R^4 ≤ K*P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ K*P^6*T/R^4 by positivity)
    convert hh using 1 <;> field_simp
  calc
    _ = P^4*T^4*Q^2/R^5+P^6*T*R^3 := by field_simp
    _ ≤ K*P^6*T*R^3+P^6*T*R^3 := add_le_add (htri.trans htri') le_rfl
    _ = _ := by ring

private theorem normalized_minor_main_le
    {K T P R Q : ℝ} (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hcut : P^2*R ≤ K*T*Q^2)
    (hscale : T^2 ≤ R^7) :
    (T^6*Q^6/R^18)*(P^2*R^2/(T*Q^2))^10*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)) ≤
        (K^8+K^7+K^6)*P^6*T*R^3 := by
  have htri : P^22*R^4/(T^5*Q^16) ≤ K^8*P^6*T^3/R^4 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 8
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6/(T^5*Q^16*R^4) by positivity)
    convert hh using 1 <;> field_simp
  have htri' : K^8*P^6*T^3/R^4 ≤ K^8*P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ K^8*P^6*T/R^4 by positivity)
    convert hh using 1 <;> field_simp
  have hnontri₁ : P^20*R^10/(T^6*Q^14) ≤ K^7*P^6*T*R^3 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 7
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6*R^3/(T^6*Q^14) by positivity)
    convert hh using 1 <;> field_simp
  have hnontri₂ : P^18*R^9/(T^5*Q^12) ≤ K^6*P^6*T*R^3 := by
    have hpow := pow_le_pow_left₀ (show 0 ≤ P^2*R by positivity) hcut 6
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ P^6*R^3/(T^5*Q^12) by positivity)
    convert hh using 1 <;> field_simp
  calc
    _ = P^22*R^4/(T^5*Q^16)+P^20*R^10/(T^6*Q^14)+
        P^18*R^9/(T^5*Q^12) := by field_simp
    _ ≤ K^8*P^6*T*R^3+K^7*P^6*T*R^3+K^6*P^6*T*R^3 :=
      add_le_add (add_le_add (htri.trans htri') hnontri₁) hnontri₂
    _ = _ := by ring

private theorem physical_dual_ceiling_bounds
    {c u T P R N Q : ℝ} (hc : 0<c) (hu : 0<u) (hT : 0<T)
    (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hlo : P/(2*R) ≤ N) (hhi : N ≤ P/R)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let M : ℕ := ⌈63*(u*T/P^3)*Q*N^2⌉₊+1
    (63*u/4)*(T*Q/(P*R^2)) ≤ (M:ℝ) ∧
      (M:ℝ) ≤ (63*u+c/6)*(T*Q/(P*R^2)) := by
  intro M
  let V := T*Q/(P*R^2)
  let x := 63*(u*T/P^3)*Q*N^2
  have hN : 0<N := (div_pos hP (by positivity : 0<2*R)).trans_le hlo
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hlow : (63*u/4)*V ≤ x := by
    calc
      _ = 63*(u*T/P^3)*Q*(P/(2*R))^2 := by dsimp only [V]; field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hlo 2) (by positivity)
  have hupp : x ≤ 63*u*V := by
    calc
      x ≤ 63*(u*T/P^3)*Q*(P/R)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hN.le hhi 2) (by positivity)
      _ = _ := by dsimp only [V]; field_simp
  have hV : 12 ≤ c*V := by
    apply hdual.trans
    calc
      (c*T/P^3)*Q*N^2 ≤ (c*T/P^3)*Q*(P/R)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hhi 2) (by positivity)
      _ = _ := by dsimp only [V]; field_simp
  have hceilLow : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hceilHigh : (⌈x⌉₊:ℝ) < x+1 := Nat.ceil_lt_add_one hx
  dsimp only [M]
  rw [Nat.cast_add,Nat.cast_one]
  change (63*u/4)*V ≤ (⌈x⌉₊:ℝ)+1 ∧ (⌈x⌉₊:ℝ)+1 ≤ (63*u+c/6)*V
  constructor
  · linarith only [hlow,hceilLow]
  · nlinarith only [hupp,hV,hceilHigh]

private theorem physical_dual_sqrt_weight_bound
    {K T P R Q U M : ℝ} (hK : 0<K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hU : 0 ≤ U) (hM : 0<M)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M) :
    Real.sqrt (U*Q^3)*(Real.sqrt M/(6*M^2)) ≤ K^2*R^3/T := by
  let B := Real.sqrt (U*Q^3)*(Real.sqrt M/(6*M^2))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBsq : B^2=U*Q^3/(36*M^3) := by
    dsimp only [B]
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hM.le]
    field_simp
    ring
  have hmodel : U*Q^3*T^2 ≤ K^4*R^6*M^3 := by
    calc
      _ ≤ (K*T/P^3)*Q^3*T^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hUupper (by positivity)) (by positivity)
      _ = K^4*R^6*(T*Q/(K*P*R^2))^3 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hMlower 3) (by positivity)
  have hcross : U*Q^3*T^2 ≤ (K^4*R^6)*(36*M^3) := by
    apply hmodel.trans
    exact mul_le_mul_of_nonneg_left
      (show M^3 ≤ 36*M^3 by nlinarith only [pow_pos hM 3]) (by positivity)
  have hsq : B^2 ≤ (K^2*R^3/T)^2 := by
    calc
      _ = U*Q^3/(36*M^3) := hBsq
      _ ≤ K^4*R^6/T^2 :=
        (div_le_div_iff₀ (by positivity) (pow_pos hT 2)).mpr hcross
      _ = _ := by ring
  exact (sq_le_sq₀ hB (by positivity)).mp hsq

private theorem physical_dual_error_bounds
    {K T P R Q U M L F lam : ℝ}
    (hK : 0<K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hU : 0 ≤ U) (hM : 0<M)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hLlower : T/(K*P^3) ≤ L) (hlamLower : T/(K*P^4) ≤ lam)
    (hFupper : F ≤ K*T/P^4) (hgeom : T ≤ P*R^3) :
    let zeta := Real.sqrt M/(6*M^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    E*Q^2/L ≤ (16*K^4+3*K^2/4)*(Q^2*R^3/T) ∧
      U*rho ≤ 12*K^5*(R^3/P^2) := by
  intro zeta E rho
  let A := Real.sqrt (U*Q^3)*zeta
  let Umax := K*T/P^3
  let Amax := K^2*R^3/T
  let Emax := 16*Umax*Amax+3*(K*T/P^4)/4
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlower
  have hlam : 0<lam := (show 0<T/(K*P^4) by positivity).trans_le hlamLower
  have hA : 0 ≤ A := by dsimp only [A,zeta]; positivity
  have hAupper : A ≤ Amax :=
    physical_dual_sqrt_weight_bound hK hT hP hR hQ hU hM hUupper hMlower
  have hEmax : 0 ≤ Emax := by dsimp only [Emax,Umax,Amax]; positivity
  have hE : E ≤ Emax := by
    have hre : E=16*(U*A)+3*F/4 := by dsimp only [E,A]; ring
    rw [hre]
    have hprod : U*A ≤ Umax*Amax :=
      mul_le_mul hUupper hAupper hA (by dsimp only [Umax]; positivity)
    dsimp only [Emax]
    nlinarith only [hprod,hFupper]
  constructor
  · have hlast : 3*K^2*Q^2/(4*P) ≤ (3*K^2/4)*(Q^2*R^3/T) := by
      have hh := mul_le_mul_of_nonneg_left hgeom
        (show 0 ≤ 3*K^2*Q^2/(4*P*T) by positivity)
      convert hh using 1 <;> field_simp
    calc
      E*Q^2/L ≤ Emax*Q^2/L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE (sq_nonneg Q)) hL.le
      _ ≤ Emax*Q^2/(T/(K*P^3)) :=
        div_le_div_of_nonneg_left (mul_nonneg hEmax (sq_nonneg Q))
          (by positivity) hLlower
      _ = 16*K^4*(Q^2*R^3/T)+3*K^2*Q^2/(4*P) := by
        dsimp only [Emax,Umax,Amax]
        field_simp
      _ ≤ 16*K^4*(Q^2*R^3/T)+(3*K^2/4)*(Q^2*R^3/T) :=
        add_le_add le_rfl hlast
      _ = _ := by ring
  · have hnum : 12*U^2*A ≤ 12*Umax^2*Amax := by
      have hprod := mul_le_mul (pow_le_pow_left₀ hU hUupper 2) hAupper hA (sq_nonneg Umax)
      nlinarith only [hprod]
    calc
      U*rho = (12*U^2*A)/lam := by dsimp only [rho,A]; ring
      _ ≤ (12*Umax^2*Amax)/lam := div_le_div_of_nonneg_right hnum hlam.le
      _ ≤ (12*Umax^2*Amax)/(T/(K*P^4)) :=
        div_le_div_of_nonneg_left (by dsimp only [Amax]; positivity)
          (by positivity) hlamLower
      _ = _ := by dsimp only [Umax,Amax]; field_simp

private theorem exists_model_scale_constant {σ : ℝ} (hσ : 0<σ)
    (B₁ B₂ B₃ : ℝ) :
    let c := modelPhaseJetLower σ 2
    let u := (modelPhaseJetCoefficient σ 2+1)/6
    let ell := modelPhaseJetLower σ 3
    let f := modelPhaseJetCoefficient σ 3+1
    let x := (modelPhaseJetCoefficient σ 1+1)/2
    ∃ K ≥ (1000:ℝ), (1/K ≤ c ∧ c ≤ K) ∧ (1/K ≤ u ∧ u ≤ K) ∧
      (1/K ≤ ell ∧ ell ≤ K) ∧ f ≤ K ∧ x ≤ K ∧ B₁ ≤ K ∧ B₂ ≤ K ∧ B₃ ≤ K := by
  classical
  intro c u ell f x
  obtain ⟨K,hK⟩ := Finset.exists_le
    ({1000,c,1/c,u,1/u,ell,1/ell,f,x,B₁,B₂,B₃}:Finset ℝ)
  have hK1000 : 1000 ≤ K := hK _ (by simp)
  have hKpos : 0<K := by linarith only [hK1000]
  have hc : 0<c := modelPhaseJetLower_pos hσ 2
  have hu : 0<u := by
    have hh := modelPhaseJetCoefficient_pos hσ 2
    dsimp only [u]
    positivity
  have hell : 0<ell := modelPhaseJetLower_pos hσ 3
  refine ⟨K,hK1000,⟨?_,hK _ (by simp)⟩,⟨?_,hK _ (by simp)⟩,
    ⟨?_,hK _ (by simp)⟩,hK _ (by simp),hK _ (by simp),
    hK _ (by simp),hK _ (by simp),hK _ (by simp)⟩
  · exact (one_div_le hKpos hc).mpr (hK _ (by simp))
  · exact (one_div_le hKpos hu).mpr (hK _ (by simp))
  · exact (one_div_le hKpos hell).mpr (hK _ (by simp))

private theorem normalized_physical_dual_ceiling
    {K c u T P R N Q : ℝ} (hK : 1000 ≤ K)
    (hc : 1/K ≤ c ∧ c ≤ K) (hu : 1/K ≤ u ∧ u ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hlo : P/(2*R) ≤ N) (hhi : N ≤ P/R)
    (hdual : 12 ≤ (c*T/P^3)*Q*N^2) :
    let M : ℕ := ⌈63*(u*T/P^3)*Q*N^2⌉₊+1
    T*Q/(K*P*R^2) ≤ (M:ℝ) ∧
      (M:ℝ) ≤ K^2*T*Q/(P*R^2) := by
  intro M
  have hKpos : 0<K := by linarith only [hK]
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc.1
  have hup : 0<u := (one_div_pos.mpr hKpos).trans_le hu.1
  have hb := physical_dual_ceiling_bounds hcp hup hT hP hR hQ hlo hhi hdual
  have hlow : 1/K ≤ 63*u/4 := by linarith only [hu.1,hup]
  have hupper : 63*u+c/6 ≤ K^2 := by
    calc
      _ ≤ 64*K := by linarith only [hu.2,hc.2,hK]
      _ ≤ K*K := mul_le_mul_of_nonneg_right (by linarith only [hK]) hKpos.le
      _ = _ := by ring
  constructor
  · calc
      _ = (1/K)*(T*Q/(P*R^2)) := by field_simp
      _ ≤ (63*u/4)*(T*Q/(P*R^2)) := mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ _ := hb.1
  · calc
      _ ≤ (63*u+c/6)*(T*Q/(P*R^2)) := hb.2
      _ ≤ K^2*(T*Q/(P*R^2)) := mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = _ := by ring

private theorem direct_branch_cube_cutoff
    {K c T P R N Q : ℝ} (hK : 1000 ≤ K) (hc : 1/K ≤ c)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hRthree : R^3 ≤ T)
    (hfail : ¬(12 ≤ (c*T/P^3)*Q*N^2 ∧ 384 ≤ (c*T/P^3)^2*Q^3*N^3)) :
    T^2*Q^3 ≤ K^6*P^3*R^3 := by
  have hKpos : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc
  have hcT : (1/K)*T/P^3 ≤ c*T/P^3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hT.le) (by positivity)
  rcases not_and_or.mp hfail with hfail | hfail
  · have hlo : T*Q/(4*K*P*R^2) ≤ (c*T/P^3)*Q*N^2 := by
      calc
        _ = ((1/K)*T/P^3)*Q*(P/(2*R))^2 := by field_simp; norm_num
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcT hQ.le)
          (pow_le_pow_left₀ (by positivity) hNlo 2) (by positivity) (by positivity)
    have hh := (div_lt_iff₀ (show 0<4*K*P*R^2 by positivity)).mp
      (hlo.trans_lt (lt_of_not_ge hfail))
    have hqcut : Q ≤ 48*K*P*R^2/T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith only [hh]
    have hpow := pow_le_pow_left₀ hQ.le hqcut 3
    have hfirst : T^2*Q^3 ≤ (48*K)^3*P^3*R^6/T := by
      have hh' := mul_le_mul_of_nonneg_left hpow (sq_nonneg T)
      convert hh' using 1
      field_simp
    have hcoefficient : (48*K)^3 ≤ K^6 := by
      calc
        _ = (48:ℝ)^3*K^3 := by ring
        _ ≤ K^3*K^3 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 48)
            (by linarith only [hK]) 3) (by positivity)
        _ = _ := by ring
    have hlast : K^6*P^3*R^6/T ≤ K^6*P^3*R^3 := by
      have hh' := mul_le_mul_of_nonneg_left hRthree
        (show 0 ≤ K^6*P^3*R^3/T by positivity)
      convert hh' using 1 <;> field_simp
    calc
      _ ≤ (48*K)^3*P^3*R^6/T := hfirst
      _ ≤ K^6*P^3*R^6/T := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)) hT.le
      _ ≤ _ := hlast
  · have hlo : T^2*Q^3/(8*K^2*P^3*R^3) ≤ (c*T/P^3)^2*Q^3*N^3 := by
      calc
        _ = (((1/K)*T/P^3)^2)*Q^3*(P/(2*R))^3 := by field_simp; norm_num
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcT 2) (by positivity))
          (pow_le_pow_left₀ (by positivity) hNlo 3) (by positivity) (by positivity)
    have hh := (div_lt_iff₀ (show 0<8*K^2*P^3*R^3 by positivity)).mp
      (hlo.trans_lt (lt_of_not_ge hfail))
    have hKfour : (3072:ℝ) ≤ K^4 := by
      have hh' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 4
      norm_num at hh'
      linarith only [hh']
    have hcoefficient : 3072*K^2 ≤ K^6 := by
      calc
        _ ≤ K^4*K^2 := mul_le_mul_of_nonneg_right hKfour (sq_nonneg K)
        _ = _ := by ring
    calc
      T^2*Q^3 ≤ 3072*K^2*P^3*R^3 := by nlinarith only [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity)

private theorem minor_branch_scales
    {K c T P R N Q : ℝ} (hc : 0<c) (hcK : c ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hN : 0 ≤ N) (hQ : 0 ≤ Q)
    (hQN : Q ≤ 2*N) (hNupper : N ≤ P/R)
    (hminor : 3 ≤ (c*T/P^3)*Q^2*N/8) :
    12 ≤ (c*T/P^3)*Q*N^2 ∧ P^2*R ≤ K*T*Q^2 := by
  have hK : 0<K := hc.trans_le hcK
  have hmono := mul_le_mul_of_nonneg_left hQN
    (show 0 ≤ (c*T/P^3)*Q*N by positivity)
  have hupper : (c*T/P^3)*Q^2*N ≤ K*T*Q^2/(P^2*R) := by
    calc
      _ ≤ (K*T/P^3)*Q^2*(P/R) := mul_le_mul
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcK hT.le) (by positivity))
          (sq_nonneg Q))
        hNupper hN (by positivity)
      _ = _ := by field_simp
  constructor
  · nlinarith only [hmono,hminor]
  · have hb : 24 ≤ K*T*Q^2/(P^2*R) := by linarith only [hupper,hminor]
    have hh := (le_div_iff₀ (show 0<P^2*R by positivity)).mp hb
    nlinarith only [hh,show 0<P^2*R by positivity]

private theorem frozen_branch_scales
    {K c T P R N Q : ℝ} (hK : 1000 ≤ K) (hc : 1/K ≤ c)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hgeom : T ≤ P^2*R)
    (hcase : Q=2 ∨ (c*T/P^3)*Q^2*N/8<3) :
    T*Q^2 ≤ 48*K*P^2*R ∧
      1+32/((c*T/P^3)*Q^2*N) ≤ K^2*(P^2*R/(T*Q^2)) := by
  have hKpos : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hcp : 0<c := (one_div_pos.mpr hKpos).trans_le hc
  have hcT : (1/K)*T/P^3 ≤ c*T/P^3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hT.le) (by positivity)
  have hlo : T*Q^2/(2*K*P^2*R) ≤ (c*T/P^3)*Q^2*N := by
    calc
      _ = ((1/K)*T/P^3)*Q^2*(P/(2*R)) := by field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcT (sq_nonneg Q))
        hNlo (by positivity) (by positivity)
  have hcut : T*Q^2 ≤ 48*K*P^2*R := by
    rcases hcase with htwo | hsmall
    · calc
        _ = 4*T := by rw [htwo]; ring
        _ ≤ 4*(P^2*R) := mul_le_mul_of_nonneg_left hgeom (by norm_num)
        _ ≤ (48*K)*(P^2*R) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK]) (by positivity)
        _ = _ := by ring
    · have hh : T*Q^2/(2*K*P^2*R)<24 := by linarith only [hlo,hsmall]
      have hh' := (div_lt_iff₀ (show 0<2*K*P^2*R by positivity)).mp hh
      nlinarith only [hh']
  have hone : 1 ≤ 48*K*(P^2*R/(T*Q^2)) := by
    have hh := div_le_div_of_nonneg_right hcut (show 0 ≤ T*Q^2 by positivity)
    convert hh using 1 <;> field_simp
  have hreciprocal : 32/((c*T/P^3)*Q^2*N) ≤ 64*K*(P^2*R/(T*Q^2)) := by
    calc
      _ ≤ 32/(T*Q^2/(2*K*P^2*R)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo
      _ = _ := by field_simp; norm_num
  refine ⟨hcut,?_⟩
  calc
    _ ≤ 48*K*(P^2*R/(T*Q^2))+64*K*(P^2*R/(T*Q^2)) :=
      add_le_add hone hreciprocal
    _ = (112*K)*(P^2*R/(T*Q^2)) := by ring
    _ ≤ (K*K)*(P^2*R/(T*Q^2)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hK]) hKpos.le) (by positivity)
    _ = _ := by ring

private theorem physical_coordinate_budget_bounds
    {K T P R Q M X : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hX : 0 ≤ X) (hXupper : X ≤ K*(T/P^2))
    (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hgeom : T^2 ≤ P^2*R^4) (hPtwo : P^2 ≤ T) :
    let Gamma := Q^2/(6*M^2)
    let G0 := P^2*R^4/T^2
    let X0 := T/P^2
    Gamma ≤ K^2*G0 ∧ 2*Gamma+1 ≤ K^2*G0 ∧
      (2*X+5)^2 ≤ K^4*X0^2 := by
  intro Gamma G0 X0
  have hKpos : 0<K := by linarith only [hK]
  have hG : 1 ≤ G0 := by
    apply (le_div_iff₀ (pow_pos hT 2)).mpr
    simpa using hgeom
  have hX0 : 1 ≤ X0 := by
    apply (le_div_iff₀ (pow_pos hP 2)).mpr
    simpa using hPtwo
  have hGamma : Gamma ≤ K^2*G0/6 := by
    calc
      _ ≤ Q^2/(6*(T*Q/(K*P*R^2))^2) :=
        div_le_div_of_nonneg_left (sq_nonneg Q) (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMlower 2) (by norm_num))
      _ = _ := by dsimp only [G0]; field_simp
  have hKK : 1000*K ≤ K^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKpos.le
  have hcoef : K^2/3+1 ≤ K^2 := by nlinarith only [hKK,hK]
  have hcoefX : 2*K+5 ≤ K^2 := by nlinarith only [hKK,hK]
  refine ⟨?_,?_,?_⟩
  · have hh : 0 ≤ K^2*G0 := by dsimp only [G0]; positivity
    linarith only [hGamma,hh]
  · calc
      2*Gamma+1 ≤ (K^2/3+1)*G0 := by nlinarith only [hGamma,hG]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by linarith only [hG])
  · have hlinear : 2*X+5 ≤ K^2*X0 := by
      calc
        _ ≤ (2*K+5)*X0 := by nlinarith only [hXupper,hX0]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoefX (by linarith only [hX0])
    have hh := pow_le_pow_left₀ (show 0 ≤ 2*X+5 by positivity) hlinear 2
    convert hh using 1
    ring

private theorem physical_pair_factor_bounds
    {K T P R Q U M L F lam X : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hU : 0 ≤ U) (hM : 0<M) (hX : 0 ≤ X)
    (hUupper : U ≤ K*T/P^3) (hMlower : T*Q/(K*P*R^2) ≤ M)
    (hLlower : T/(K*P^3) ≤ L) (hlamLower : T/(K*P^4) ≤ lam)
    (hFupper : F ≤ K*T/P^4) (hXupper : X ≤ K*(T/P^2))
    (hgeom : T ≤ P*R^3) (hPthree : T ≤ P^3)
    (hgamma : T^2 ≤ P^2*R^4) (hPtwo : P^2 ≤ T) :
    let zeta := Real.sqrt M/(6*M^2)
    let E := 16*U*Real.sqrt (U*Q^3)*zeta+3*F/4
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*zeta
    let Gamma := Q^2/(6*M^2)
    let G0 := P^2*R^4/T^2
    let X0 := T/P^2
    let H := 1+R^3/P^2
    1+6*U*(rho+1) ≤ K^6*H ∧
      Gamma+48*E*Q^2/L ≤ K^6*(G0+Q^2*R^3/T) ∧
      16*(2*Gamma+1)*(2*X+5)^2*(Gamma+48*E*Q^2/L) ≤
        K^13*G0*X0^2*(G0+Q^2*R^3/T) := by
  intro zeta E rho Gamma G0 X0 H
  have hKpos : 0<K := by linarith only [hK]
  have hKone : 1 ≤ K := by linarith only [hK]
  have hE := physical_dual_error_bounds hKpos hT hP hR hQ hU hM
    hUupper hMlower hLlower hlamLower hFupper hgeom
  have hco := physical_coordinate_budget_bounds hK hT hP hR hQ
    hX hXupper hMlower hgamma hPtwo
  have hUmax : U ≤ K := hUupper.trans ((div_le_iff₀ (pow_pos hP 3)).mpr
    (mul_le_mul_of_nonneg_left hPthree hKpos.le))
  have h15 : 1 ≤ K^5 := one_le_pow₀ hKone
  have h25 : K^2 ≤ K^5 := pow_le_pow_right₀ hKone (by norm_num)
  have h45 : K^4 ≤ K^5 := pow_le_pow_right₀ hKone (by norm_num)
  have hK5 : K ≤ K^5 := by simpa using pow_le_pow_right₀ hKone (show 1 ≤ 5 by norm_num)
  have h56 : 1000*K^5 ≤ K^6 := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ K^5)
  have h26 : K^2 ≤ K^6 := pow_le_pow_right₀ hKone (by norm_num)
  have htriCoeff : 1+6*K+72*K^5 ≤ K^6 := by
    linarith only [h15,hK5,h56]
  have herrCoeff : 768*K^4+36*K^2 ≤ K^6 := by
    linarith only [h45,h25,h56,h15]
  have htri : 1+6*U*(rho+1) ≤ K^6*H := by
    have hA : 0 ≤ R^3/P^2 := by positivity
    calc
      _ ≤ 1+6*K+72*K^5*(R^3/P^2) := by nlinarith only [hUmax,hE.2]
      _ ≤ (1+6*K+72*K^5)*H := by
        dsimp only [H]
        nlinarith only [mul_nonneg (show 0 ≤ 1+6*K by positivity) hA,
          show 0 ≤ K^5 by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right htriCoeff (by dsimp only [H]; positivity)
  have hpair : Gamma+48*E*Q^2/L ≤ K^6*(G0+Q^2*R^3/T) := by
    have hErr : 48*E*Q^2/L ≤ K^6*(Q^2*R^3/T) := by
      calc
        _ = 48*(E*Q^2/L) := by ring
        _ ≤ 48*((16*K^4+3*K^2/4)*(Q^2*R^3/T)) :=
          mul_le_mul_of_nonneg_left hE.1 (by norm_num)
        _ = (768*K^4+36*K^2)*(Q^2*R^3/T) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right herrCoeff (by positivity)
    have hGamma : Gamma ≤ K^6*G0 := hco.1.trans
      (mul_le_mul_of_nonneg_right h26 (by positivity))
    nlinarith only [hGamma,hErr]
  refine ⟨htri,hpair,?_⟩
  calc
    _ ≤ 16*(2*Gamma+1)*(2*X+5)^2*(K^6*(G0+Q^2*R^3/T)) :=
      mul_le_mul_of_nonneg_left hpair (by dsimp only [Gamma]; positivity)
    _ ≤ 16*(K^2*G0)*(K^4*X0^2)*(K^6*(G0+Q^2*R^3/T)) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp only [G0]; positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hco.2.1 (by norm_num))
        hco.2.2 (sq_nonneg _) (by dsimp only [G0]; positivity)
    _ = 16*K^12*G0*X0^2*(G0+Q^2*R^3/T) := by ring
    _ ≤ _ := by
      have hh : 16*K^12 ≤ K^13 := by
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show 16 ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^12)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh
          (by dsimp only [G0]; positivity)) (sq_nonneg X0))
        (by dsimp only [G0]; positivity)

private theorem physical_block_count_bounds
    {K T P R N Q X L : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 0<P) (hR : 0<R) (hQ : 1 ≤ Q)
    (hXupper : X ≤ K*(T/P^2))
    (hLlower : T/(K*P^3) ≤ L) (hNlower : P/(2*R) ≤ N)
    (hPtwo : P^2 ≤ T) (hQR : Q ≤ 2*R) (hRT : R ≤ T) :
    let D := 16/(L*N*Q)
    let Y := 4*(X+1)*D^2+D*(2+Real.log (D+1))
    let Z := 4*Q*(2*X*Q+1)
    Y ≤ K^6*(P^2*R^2/(T*Q^2))*(1+Real.log T) ∧
      Z ≤ K^2*(T*Q^2/P^2) := by
  intro D Y Z
  let D0 := P^2*R/(T*Q)
  let Y0 := P^2*R^2/(T*Q^2)
  let X0 := T/P^2
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlower
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlower
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hX0 : 1 ≤ X0 := (one_le_div (pow_pos hP 2)).mpr hPtwo
  have hDupper : D ≤ 32*K*D0 := by
    calc
      _ ≤ 16/((T/(K*P^3))*(P/(2*R))*Q) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hLlower hNlower (by positivity) hL.le) hQp.le)
      _ = _ := by dsimp only [D0]; field_simp; norm_num
  have hD0Y : D0 ≤ 2*Y0 := by
    have hh := mul_le_mul_of_nonneg_left hQR
      (show 0 ≤ P^2*R/(T*Q^2) by positivity)
    convert hh using 1 <;> dsimp only [D0,Y0] <;> field_simp
  have hD0R : D0 ≤ R := by
    apply (div_le_iff₀ (show 0<T*Q by positivity)).mpr
    have hTQ := le_mul_of_one_le_right hTp.le hQ
    have hh := mul_le_mul_of_nonneg_right (hPtwo.trans hTQ) hR.le
    convert hh using 1
    ring
  have hlogD : 2+Real.log (D+1) ≤ K^2*Log := by
    have hd : D+1 ≤ (32*K+1)*T := by
      have hh := mul_le_mul_of_nonneg_left (hD0R.trans hRT) (by positivity : 0 ≤ 32*K)
      nlinarith only [hDupper,hh,hT]
    have hh := Real.log_le_log (by positivity : 0<D+1) hd
    rw [Real.log_mul (by positivity) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (show 0<32*K+1 by positivity)
    have hKK : 1000*K ≤ K^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
    have hc : 32*K+2 ≤ K^2 := by linarith only [hKK,hK]
    calc
      _ ≤ 32*K+2+Real.log T := by linarith only [hh,hl]
      _ ≤ (32*K+2)*Log := by
        dsimp only [Log]
        nlinarith only [mul_nonneg (show 0 ≤ 32*K+1 by positivity) (Real.log_nonneg hT)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by linarith only [hLog])
  have hXplus : X+1 ≤ 2*K*X0 := by
    have hh : X0 ≤ K*X0 := le_mul_of_one_le_left (by linarith only [hX0]) hK1
    linarith only [hXupper,hX0,hh]
  have hmain : 4*(X+1)*D^2 ≤ 8192*K^3*Y0 := by
    calc
      _ ≤ 4*(2*K*X0)*(32*K*D0)^2 := mul_le_mul
        (mul_le_mul_of_nonneg_left hXplus (by norm_num))
        (pow_le_pow_left₀ hD.le hDupper 2) (sq_nonneg D)
        (by dsimp only [X0]; positivity)
      _ = _ := by dsimp only [X0,D0,Y0]; field_simp; ring
  have herror : D*(2+Real.log (D+1)) ≤ 64*K^3*Y0*Log := by
    have hd : D ≤ 64*K*Y0 := by
      have hh := mul_le_mul_of_nonneg_left hD0Y (by positivity : 0 ≤ 32*K)
      linarith only [hDupper,hh]
    calc
      _ ≤ D*(K^2*Log) := mul_le_mul_of_nonneg_left hlogD hD.le
      _ ≤ (64*K*Y0)*(K^2*Log) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by ring
  have hcoeff : 8256*K^3 ≤ K^6 := by
    have hh : (8256:ℝ) ≤ K^3 := by
      have hk := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hk
      linarith only [hk]
    calc
      _ ≤ K^3*K^3 := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  constructor
  · calc
      Y ≤ 8192*K^3*Y0+64*K^3*Y0*Log := add_le_add hmain herror
      _ ≤ 8192*K^3*Y0*Log+64*K^3*Y0*Log := add_le_add
        (le_mul_of_one_le_right (by dsimp only [Y0]; positivity) hLog) le_rfl
      _ = (8256*K^3)*Y0*Log := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by dsimp only [Y0]; positivity))
        (by linarith only [hLog])
  · have hunit : 1 ≤ X0*Q := hX0.trans
      (le_mul_of_one_le_right (by linarith only [hX0]) hQ)
    have hcoef : 4*(2*K+1) ≤ K^2 := by
      have hh : 1000*K ≤ K^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
      linarith only [hh,hK]
    calc
      Z ≤ 4*Q*((2*K+1)*X0*Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := mul_le_mul_of_nonneg_right hXupper hQp.le
        nlinarith only [hh,hunit]
      _ = (4*(2*K+1))*(T*Q^2/P^2) := by dsimp only [X0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

private theorem normalized_pair_count_bounds
    {K T P R Q B W Y Z H Log : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hH : 1 ≤ H) (hLog : 1 ≤ Log) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : B ≤ K^6*H)
    (hW : W ≤ K^13*(P^2*R^4/T^2)*(T/P^2)^2*
      (P^2*R^4/T^2+Q^2*R^3/T))
    (hYupper : Y ≤ K^6*(P^2*R^2/(T*Q^2))*Log)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2)) :
    4*Y*B+W ≤ K^13*H*Log*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)) ∧
    (T*Q^2 ≤ 48*K*P^2*R →
      4*Z*B+W ≤ K^15*H*(T*Q^2/P^2+R^8/T^2)) := by
  have hKp : 0<K := by linarith only [hK]
  have hHp : 0 ≤ H := by linarith only [hH]
  have hLp : 0 ≤ Log := by linarith only [hLog]
  have hW' : W ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) := by
    convert hW using 1
    field_simp
  have hcoef (n : ℕ) : 4*K^n ≤ K^(n+1) := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
      (show (4:ℝ) ≤ K by linarith only [hK]) (pow_nonneg hKp.le n)
  constructor
  · have htri : 4*Y*B ≤ K^13*H*Log*(P^2*R^2/(T*Q^2)) := by
      calc
        _ ≤ 4*Y*(K^6*H) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ 4*(K^6*(P^2*R^2/(T*Q^2))*Log)*(K^6*H) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hYupper (by norm_num)) (by positivity)
        _ = (4*K^12)*(H*Log*(P^2*R^2/(T*Q^2))) := by ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right (hcoef 12)
            (show 0 ≤ H*Log*(P^2*R^2/(T*Q^2)) by positivity)
          convert hh using 1
          ring
    have hnontri : W ≤ K^13*H*Log*(R^8/T^2+Q^2*R^7/(P^2*T)) := by
      apply hW'.trans
      have hh := le_mul_of_one_le_right
        (show 0 ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) by positivity)
        (hH.trans (le_mul_of_one_le_right hHp hLog))
      convert hh using 1
      ring
    nlinarith only [htri,hnontri]
  · intro hcut
    have hnontri : W ≤ K^15*(R^8/T^2) := by
      have hlast : Q^2*R^7/(P^2*T) ≤ (48*K)*(R^8/T^2) := by
        have hh := mul_le_mul_of_nonneg_left hcut
          (show 0 ≤ R^7/(P^2*T^2) by positivity)
        convert hh using 1 <;> field_simp
      have hc : 1+48*K ≤ K^2 := by
        have hh : 1000*K ≤ K^2 := by
          simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
        linarith only [hh,hK]
      calc
        W ≤ K^13*(R^8/T^2+Q^2*R^7/(P^2*T)) := hW'
        _ ≤ K^13*((1+48*K)*(R^8/T^2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith only [hlast]
        _ ≤ K^13*(K^2*(R^8/T^2)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
        _ = _ := by ring
    have htri : 4*Z*B ≤ K^15*H*(T*Q^2/P^2) := by
      have hpow : K^9 ≤ K^15 := pow_le_pow_right₀
        (show 1 ≤ K by linarith only [hK]) (by norm_num)
      calc
        _ ≤ 4*Z*(K^6*H) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ ≤ 4*(K^2*(T*Q^2/P^2))*(K^6*H) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZupper (by norm_num)) (by positivity)
        _ = (4*K^8)*(H*(T*Q^2/P^2)) := by ring
        _ ≤ K^15*(H*(T*Q^2/P^2)) := mul_le_mul_of_nonneg_right
          ((hcoef 8).trans hpow) (by positivity)
        _ = _ := by ring
    have hlast : K^15*(R^8/T^2) ≤ K^15*H*(R^8/T^2) := by
      have hh := le_mul_of_one_le_right (show 0 ≤ K^15*(R^8/T^2) by positivity) hH
      convert hh using 1
      ring
    nlinarith only [htri,hnontri.trans hlast]

private theorem physical_moment_prefactors
    {K T P R N Q L U M : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 0<P) (hR : 1 ≤ R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R) (hQN : Q ≤ 2*N)
    (hLlo : T/(K*P^3) ≤ L) (hU : 0 ≤ U) (hUhi : U ≤ K*T/P^3)
    (hM : 0<M) (hMhi : M ≤ K^2*T*Q/(P*R^2)) :
    let d := L*Q*N/12
    let V := 756*U/L
    M ≤ K^3*T ∧
      1+Real.log M ≤ K^3*(1+Real.log T) ∧
      6*(3+8*Real.pi*V)*(1+Real.log M) ≤ K^7*(1+Real.log T) ∧
      (2/d)^6*M^12 ≤ K^36*(T^6*Q^6/R^18) := by
  intro d V
  have hKp : 0<K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hMmax : M ≤ K^3*T := by
    have hq : Q ≤ 2*(P/R) := hQN.trans (mul_le_mul_of_nonneg_left hNhi (by norm_num))
    have hr3 : 1 ≤ R^3 := one_le_pow₀ hR
    calc
      M ≤ K^2*T*Q/(P*R^2) := hMhi
      _ ≤ K^2*T*(2*(P/R))/(P*R^2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
      _ = 2*K^2*T/R^3 := by field_simp
      _ ≤ 2*K^2*T := div_le_self (by positivity) hr3
      _ ≤ K*K^2*T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hK] : (2:ℝ) ≤ K)
          (sq_nonneg K)) hTp.le
      _ = _ := by ring
  have hlog : 1+Real.log M ≤ K^3*(1+Real.log T) := by
    have hh := Real.log_le_log hM hMmax
    rw [Real.log_mul (pow_ne_zero 3 hKp.ne') hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (pow_pos hKp 3)
    have hk3 : 1 ≤ K^3 := one_le_pow₀ (show 1 ≤ K by linarith only [hK])
    nlinarith only [hh,hl,mul_nonneg (sub_nonneg.mpr hk3) hlogT]
  have hV : V ≤ K^3 := by
    calc
      V ≤ 756*(K*T/P^3)/L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hUhi (by norm_num)) hLp.le
      _ ≤ 756*(K*T/P^3)/(T/(K*P^3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hLlo
      _ = 756*K^2 := by field_simp
      _ ≤ K*K^2 := mul_le_mul_of_nonneg_right (by linarith only [hK]) (sq_nonneg K)
      _ = _ := by ring
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hVfactor : 6*(3+8*Real.pi*V) ≤ K^4 := by
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hV0
    have hscale : 1000*K^3 ≤ K^4 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ K^3)
    have hk3 : 1 ≤ K^3 := one_le_pow₀ (show 1 ≤ K by linarith only [hK])
    nlinarith only [hpi,hV,hscale,hk3]
  have hdlo : T*Q/(24*K*P^2*R) ≤ d := by
    calc
      _ = (T/(K*P^3))*Q*(P/(2*R))/12 := by field_simp; norm_num
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hLlo hQ.le) hNlo
          (by positivity) (by positivity)) (by norm_num)
  have htwo : 2/d ≤ K^2*P^2*R/(T*Q) := by
    calc
      _ ≤ 2/(T*Q/(24*K*P^2*R)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hdlo
      _ = (48*K)*(P^2*R/(T*Q)) := by field_simp; norm_num
      _ ≤ (K*K)*(P^2*R/(T*Q)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hK]) hKp.le) (by positivity)
      _ = _ := by ring
  refine ⟨hMmax,hlog,?_,?_⟩
  · calc
      _ ≤ 6*(3+8*Real.pi*V)*(K^3*(1+Real.log T)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ K^4*(K^3*(1+Real.log T)) :=
        mul_le_mul_of_nonneg_right hVfactor (by positivity)
      _ = _ := by ring
  · have hdp : 0<d := (show 0<T*Q/(24*K*P^2*R) by positivity).trans_le hdlo
    calc
      _ ≤ (K^2*P^2*R/(T*Q))^6*(K^2*T*Q/(P*R^2))^12 := mul_le_mul
        (pow_le_pow_left₀ (by positivity) htwo 6)
        (pow_le_pow_left₀ hM.le hMhi 12) (by positivity) (by positivity)
      _ = _ := by field_simp

private theorem moment_rpow_prefactor
    {K T R Q d M ε : ℝ}
    (hK : 0<K) (hT : 0<T) (hR : 0<R) (hQ : 0<Q)
    (hM : 0<M) (hε : 0 ≤ ε) (hMmax : M ≤ K^3*T)
    (hbase : (2/d)^6*M^12 ≤ K^36*(T^6*Q^6/R^18)) :
    (2/d)^6*M^((12:ℝ)+ε) ≤
      K^36*((K^3*T)^ε)*(T^6*Q^6/R^18) := by
  have hsmall : M^ε ≤ (K^3*T)^ε := Real.rpow_le_rpow hM.le hMmax hε
  calc
    _ = ((2/d)^6*M^12)*M^ε := by
      rw [Real.rpow_add hM]
      norm_num only [Real.rpow_ofNat]
      ring
    _ ≤ (K^36*(T^6*Q^6/R^18))*((K^3*T)^ε) :=
      mul_le_mul hbase hsmall (Real.rpow_nonneg hM.le _) (by positivity)
    _ = _ := by ring

private theorem normalized_minor_moment_main
    {K T P R Q C A LogM Y Pair H Log Eps : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hY : 0 ≤ Y) (hLogM : 0 ≤ LogM)
    (hH : 0 ≤ H) (hLog : 0 ≤ Log) (hEps : 0 ≤ Eps)
    (hCupper : C ≤ K) (hAupper : A ≤ K^36*Eps*(T^6*Q^6/R^18))
    (hLogUpper : LogM ≤ K^3*Log)
    (hYupper : Y ≤ K^6*(P^2*R^2/(T*Q^2))*Log)
    (hPair : Pair ≤ K^13*H*Log*
      (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))
    (hcut : P^2*R ≤ K*T*Q^2) (hscale : T^2 ≤ R^7) :
    C*(A*LogM^12*(2*Y)^10*Pair) ≤ K^165*Eps*H*Log^23*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hY2 : 2*Y ≤ K^7*(P^2*R^2/(T*Q^2))*Log := by
    have hc : 2*K^6 ≤ K^7 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
        (show (2:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^6)
    calc
      _ ≤ 2*(K^6*(P^2*R^2/(T*Q^2))*Log) :=
        mul_le_mul_of_nonneg_left hYupper (by norm_num)
      _ = (2*K^6)*(P^2*R^2/(T*Q^2))*Log := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) hLog
  have hcore := normalized_minor_main_le hT hP hR hQ hcut hscale
  have hcoeff : K^8+K^7+K^6 ≤ K^9 := by
    have h1 : 1 ≤ K := by linarith only [hK]
    have h78 : K^7 ≤ K^8 := pow_le_pow_right₀ h1 (by norm_num)
    have h68 : K^6 ≤ K^8 := pow_le_pow_right₀ h1 (by norm_num)
    have hh : 1000*K^8 ≤ K^9 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right hK
        (by positivity : 0 ≤ K^8)
    nlinarith only [h78,h68,hh,show 0 ≤ K^8 by positivity]
  calc
    _ ≤ C*(A*LogM^12*(2*Y)^10*
        (K^13*H*Log*(P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hPair (by positivity)) hC
    _ ≤ K*((K^36*Eps*(T^6*Q^6/R^18))*(K^3*Log)^12*
        (K^7*(P^2*R^2/(T*Q^2))*Log)^10*
        (K^13*H*Log*(P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T)))) := by
      gcongr
    _ = (K^156*Eps*H*Log^23)*
        ((T^6*Q^6/R^18)*(P^2*R^2/(T*Q^2))^10*
          (P^2*R^2/(T*Q^2)+R^8/T^2+Q^2*R^7/(P^2*T))) := by ring
    _ ≤ (K^156*Eps*H*Log^23)*((K^8+K^7+K^6)*P^6*T*R^3) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ (K^156*Eps*H*Log^23)*(K^9*P^6*T*R^3) := by gcongr
    _ = _ := by ring

private theorem normalized_frozen_moment_main
    {K T P R Q C A LogV W Z Pair H Log Eps : ℝ}
    (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hLogV : 0 ≤ LogV)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hEps : 0 ≤ Eps)
    (hCupper : C ≤ K) (hAupper : A ≤ K^36*Eps*(T^6*Q^6/R^18))
    (hLogUpper : LogV ≤ K^7*Log) (hWupper : W ≤ K^2*(P^2*R/(T*Q^2)))
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hPair : Pair ≤ K^15*H*(T*Q^2/P^2+R^8/T^2))
    (hcut : T*Q^2 ≤ 48*K*P^2*R) (hscale : T^2 ≤ R^7) :
    C*((5*W)^11*W^2*LogV^12*A*(2*Z)^10*Pair) ≤
      K^205*Eps*H*Log^12*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hcoeff (a : ℝ) (ha : a ≤ K) (n : ℕ) : a*K^n ≤ K^(n+1) := by
    simpa only [pow_succ'] using mul_le_mul_of_nonneg_right ha (pow_nonneg hKp.le n)
  have hZ2 : 2*Z ≤ K^3*(T*Q^2/P^2) := by
    calc
      _ ≤ 2*(K^2*(T*Q^2/P^2)) := mul_le_mul_of_nonneg_left hZupper (by norm_num)
      _ = (2*K^2)*(T*Q^2/P^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff 2 (by linarith only [hK]) 2) (by positivity)
  have hW5 : 5*W ≤ K^3*(P^2*R/(T*Q^2)) := by
    calc
      _ ≤ 5*(K^2*(P^2*R/(T*Q^2))) := mul_le_mul_of_nonneg_left hWupper (by norm_num)
      _ = (5*K^2)*(P^2*R/(T*Q^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff 5 (by linarith only [hK]) 2) (by positivity)
  have hcore := normalized_frozen_main_le (show 0 ≤ 48*K by positivity)
    hT hP hR hQ hcut hscale
  have hlast : 48*K+1 ≤ K^2 := by
    have hh := hcoeff 1000 hK 1
    norm_num only [pow_one] at hh
    linarith only [hh,hK]
  calc
    _ ≤ C*((5*W)^11*W^2*LogV^12*A*(2*Z)^10*
        (K^15*H*(T*Q^2/P^2+R^8/T^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPair (by positivity)) hC
    _ ≤ K*((K^3*(P^2*R/(T*Q^2)))^11*(K^2*(P^2*R/(T*Q^2)))^2*
        (K^7*Log)^12*(K^36*Eps*(T^6*Q^6/R^18))*(K^3*(T*Q^2/P^2))^10*
        (K^15*H*(T*Q^2/P^2+R^8/T^2))) := by
      gcongr
    _ = (K^203*Eps*H*Log^12)*
        ((P^2*R/(T*Q^2))^13*(T^6*Q^6/R^18)*(T*Q^2/P^2)^10*
          (T*Q^2/P^2+R^8/T^2)) := by ring
    _ ≤ (K^203*Eps*H*Log^12)*((48*K+1)*P^6*T*R^3) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ (K^203*Eps*H*Log^12)*(K^2*P^6*T*R^3) := by gcongr
    _ = _ := by ring

private theorem physical_common_error_powers
    {K T P R N L B : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hB : 0 ≤ B)
    (hBupper : B ≤ K^7*R*(1+Real.log T))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (B*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)))^12 ≤
      K^111*(1+Real.log T)^24*(P^6*T*R^3) := by
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hNT : N ≤ T := by
    have hP2 : P ≤ P^2 := by nlinarith only [hP]
    exact hNhi.trans ((div_le_self hPp.le hR).trans (hP2.trans hPtwo))
  have hlogN : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hlogUpper : Real.log (6*N) ≤ K*Log := by
    have hh := Real.log_le_log (by positivity : 0<6*N)
      (mul_le_mul_of_nonneg_left hNT (by norm_num))
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)
    have hlogT := Real.log_nonneg hT
    dsimp only [Log]
    nlinarith only [hh,hl,hK,mul_nonneg (show 0 ≤ K-1 by linarith only [hK]) hlogT]
  have hsqrtSq : (B*Real.sqrt (3*N)*Real.log (6*N))^2 ≤
      K^17*P*R*Log^4 := by
    calc
      _ = B^2*(3*N)*(Real.log (6*N))^2 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (K^7*R*Log)^2*(3*(P/R))*(K*Log)^2 := by gcongr
      _ = (3*K^16)*(P*R*Log^4) := by field_simp
      _ ≤ K^17*(P*R*Log^4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (3:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^16)
      _ = _ := by ring
  have hsqrtPow : (B*Real.sqrt (3*N)*Real.log (6*N))^12 ≤
      K^102*Log^24*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (sq_nonneg _) hsqrtSq 6
    calc
      _ ≤ (K^17*P*R*Log^4)^6 := by simpa only [← pow_mul] using hh
      _ = K^102*Log^24*(P^6*R^3*R^3) := by ring
      _ ≤ _ := by gcongr
  have hreciprocal : 6/(L*N^2) ≤ 24*K*P*R^2/T := by
    calc
      _ ≤ 6/((T/(K*P^3))*(P/(2*R))^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul hLlo (pow_le_pow_left₀ (by positivity) hNlo 2)
            (by positivity) hLp.le)
      _ = _ := by field_simp; norm_num
  have hrecB : B*(6/(L*N^2)) ≤ K^9*(P*R^3/T)*Log := by
    calc
      _ ≤ (K^7*R*Log)*(24*K*P*R^2/T) :=
        mul_le_mul hBupper hreciprocal (by positivity) (by positivity)
      _ = (24*K^8)*(P*R^3/T)*Log := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith only [hLog])
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (24:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^8)
  have hrecScale : (P*R^3/T)^12 ≤ P^6*T*R^3 := by
    have hp6 : P^6 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
    have hh := mul_le_mul hp6 hR33 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hrecPow : (B*(6/(L*N^2)))^12 ≤ K^108*Log^24*(P^6*T*R^3) := by
    have hlpow : Log^12 ≤ Log^24 := pow_le_pow_right₀ hLog (by norm_num)
    calc
      _ ≤ (K^9*(P*R^3/T)*Log)^12 := pow_le_pow_left₀ (by positivity) hrecB 12
      _ = K^108*Log^12*((P*R^3/T)^12) := by ring
      _ ≤ _ := by gcongr
  have hcoeff : (2:ℝ)^11*(K^102+K^108) ≤ K^111 := by
    have hpow : K^102 ≤ K^108 := pow_le_pow_right₀ hK1 (by norm_num)
    have hcube : (4096:ℝ) ≤ K^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hh
      linarith only [hh]
    calc
      _ ≤ 4096*K^108 := by nlinarith only [hpow]
      _ ≤ K^3*K^108 := mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = _ := by ring
  calc
    _ = (B*Real.sqrt (3*N)*Real.log (6*N)+B*(6/(L*N^2)))^12 := by ring
    _ ≤ 2^11*((B*Real.sqrt (3*N)*Real.log (6*N))^12+(B*(6/(L*N^2)))^12) :=
      add_pow_le (by positivity) (by positivity) 12
    _ ≤ 2^11*(K^102*Log^24*(P^6*T*R^3)+K^108*Log^24*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsqrtPow hrecPow) (by norm_num)
    _ = (2^11*(K^102+K^108))*(Log^24*(P^6*T*R^3)) := by ring
    _ ≤ K^111*(Log^24*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem direct_cut_implies_quadratic_cut
    {K T P R Q : ℝ} (hK : 0<K) (hT : 0<T) (hP : 0<P)
    (hR : 0<R) (hQ : 0<Q) (hRthree : R^3 ≤ T)
    (hcut : T^2*Q^3 ≤ K^6*P^3*R^3) :
    T*Q^2 ≤ K^4*P^2*R := by
  have hsquare := pow_le_pow_left₀ (show 0 ≤ T^2*Q^3 by positivity) hcut 2
  have hh := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 1/T by positivity)
  have hpow : (T*Q^2)^3 ≤ (K^4*P^2*R)^3 := by
    calc
      _ ≤ K^12*P^6*R^6/T := by convert hh using 1 <;> field_simp
      _ = (K^12*P^6*R^3)*(R^3/T) := by ring
      _ ≤ (K^12*P^6*R^3)*1 := mul_le_mul_of_nonneg_left
        ((div_le_one hT).mpr hRthree) (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3 ≠ 0)).mp hpow

private theorem physical_endpoint_error_power
    {K T P R N Q L Z : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hLlo : T/(K*P^3) ≤ L)
    (hZ : 0 ≤ Z) (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T*Q^2 ≤ K^4*P^2*R) (hRthree : R^3 ≤ T) :
    (Z*Real.sqrt (12/(L*N*Q)))^12 ≤ K^72*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hN : 0<N := (show 0<P/(2*R) by positivity).trans_le hNlo
  have hL : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hrec : 12/(L*N*Q) ≤ 24*K*P^2*R/(T*Q) := by
    calc
      _ ≤ 12/((T/(K*P^3))*(P/(2*R))*Q) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hLlo hNlo (by positivity) hL.le) hQ.le)
      _ = _ := by field_simp; norm_num
  have hsquare : (Z*Real.sqrt (12/(L*N*Q)))^2 ≤ K^6*(T*Q^3*R/P^2) := by
    calc
      _ = Z^2*(12/(L*N*Q)) := by rw [mul_pow,Real.sq_sqrt (by positivity)]
      _ ≤ (K^2*(T*Q^2/P^2))^2*(24*K*P^2*R/(T*Q)) := mul_le_mul
        (pow_le_pow_left₀ hZ hZupper 2) hrec (by positivity) (by positivity)
      _ = (24*K^5)*(T*Q^3*R/P^2) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (24:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^5)
  have hscale : T^6*Q^18*R^6/P^12 ≤ K^36*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ T*Q^2 by positivity) hcut 9
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ R^6/(T^3*P^12) by positivity)
    have hr := pow_le_pow_left₀ (show 0 ≤ R^3 by positivity) hRthree 4
    have hr' : R^12/T^3 ≤ T := by
      apply (div_le_iff₀ (pow_pos hT 3)).mpr
      convert hr using 1 <;> ring
    calc
      _ ≤ K^36*P^6*R^15/T^3 := by convert hh' using 1 <;> field_simp
      _ = (K^36*P^6*R^3)*(R^12/T^3) := by ring
      _ ≤ (K^36*P^6*R^3)*T := mul_le_mul_of_nonneg_left hr' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (K^6*(T*Q^3*R/P^2))^6 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hsquare 6
    _ = K^36*(T^6*Q^18*R^6/P^12) := by ring
    _ ≤ K^36*(K^36*(P^6*T*R^3)) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem physical_direct_main_power
    {K T P R N Q U Z : ℝ} (hK : 1000 ≤ K)
    (hT : 0<T) (hP : 0<P) (hR : 0<R) (hQ : 0<Q)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hNhi : N ≤ P/R) (hUhi : U ≤ K*T/P^3)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T^2*Q^3 ≤ K^6*P^3*R^3) (hRthree : R^3 ≤ T) :
    (Z*(3*N*Real.sqrt (3*U*Q*N)))^12 ≤ K^96*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hsquare : (Z*(3*N*Real.sqrt (3*U*Q*N)))^2 ≤
      K^6*(T^3*Q^5/(P^4*R^3)) := by
    calc
      _ = 27*Z^2*U*Q*N^3 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
        ring
      _ ≤ 27*(K^2*(T*Q^2/P^2))^2*(K*T/P^3)*Q*(P/R)^3 := by gcongr
      _ = (27*K^5)*(T^3*Q^5/(P^4*R^3)) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
          (show (27:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^5)
  have hscale : T^18*Q^30/(P^24*R^18) ≤ K^60*(P^6*T*R^3) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ T^2*Q^3 by positivity) hcut 10
    have hh' := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ 1/(T^2*P^24*R^18) by positivity)
    have hr : R^9/T^2 ≤ T := by
      apply (div_le_iff₀ (pow_pos hT 2)).mpr
      have hh := pow_le_pow_left₀ (show 0 ≤ R^3 by positivity) hRthree 3
      convert hh using 1 <;> ring
    calc
      _ ≤ K^60*P^6*R^12/T^2 := by convert hh' using 1 <;> field_simp
      _ = (K^60*P^6*R^3)*(R^9/T^2) := by ring
      _ ≤ (K^60*P^6*R^3)*T := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (K^6*(T^3*Q^5/(P^4*R^3)))^6 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hsquare 6
    _ = K^36*(T^18*Q^30/(P^24*R^18)) := by ring
    _ ≤ K^36*(K^60*(P^6*T*R^3)) := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem physical_boundary_power
    {K T P R N : ℝ} (hK : 1000 ≤ K) (hT : 0<T) (hP : 0<P)
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hNhi : N ≤ P/R)
    (hPtwo : P^2 ≤ T) (hTtwo : T^2 ≤ R^7) :
    (1+23*N)^12 ≤ K^12*(P^6*T*R^3) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hKp : 0<K := by linarith only [hK]
  have hlinear : 1+23*N ≤ K*(P/R) := by
    calc
      _ ≤ 24*N := by linarith only [hN]
      _ ≤ 24*(P/R) := mul_le_mul_of_nonneg_left hNhi (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hK]) (by positivity)
  have hp6 : P^6 ≤ T^3 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
  have hr715 : R^7 ≤ R^15 := pow_le_pow_right₀ hR (by norm_num)
  have hscale : (P/R)^12 ≤ P^6*T*R^3 := by
    have hh := mul_le_mul_of_nonneg_left (hTtwo.trans hr715) hT.le
    have hh' : P^6 ≤ T*R^15 := by nlinarith only [hp6,hh]
    have hh'' := mul_le_mul_of_nonneg_left hh' (show 0 ≤ P^6/R^12 by positivity)
    convert hh'' using 1 <;> field_simp
  calc
    _ ≤ (K*(P/R))^12 := pow_le_pow_left₀ (by linarith only [hN]) hlinear 12
    _ = K^12*(P/R)^12 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

private theorem physical_tail_component_bounds
    {K T P R N L X : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) :
    let D := 8/(L*N*(N+1))
    N*(4*(X+1)*D^2) ≤ K^5*(P*R^3/T) ∧
      N*(D*(2+Real.log (D+1))) ≤ K^4*(P^2*R/T)*(1+Real.log T) := by
  intro D
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hDhi : D ≤ 32*K*P*R^2/T := by
    calc
      _ ≤ 8/(L*N^2) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith only [mul_nonneg hLp.le hNp.le])
      _ ≤ 8/((T/(K*P^3))*(P/(2*R))^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul hLlo (pow_le_pow_left₀ (by positivity) hNlo 2)
            (by positivity) hLp.le)
      _ = _ := by field_simp; norm_num
  have hPR : P*R^2/T ≤ T := by
    have hp : P ≤ T := (show P ≤ P^2 by nlinarith only [hP]).trans hPtwo
    have hr : R^2 ≤ T := (pow_le_pow_right₀ hR (show 2 ≤ 3 by norm_num)).trans hRthree
    apply (div_le_iff₀ hTp).mpr
    exact mul_le_mul hp hr (sq_nonneg R) hTp.le
  have hlogD : 2+Real.log (D+1) ≤ K^2*Log := by
    have hscaled := mul_le_mul_of_nonneg_left hPR (show 0 ≤ 32*K by positivity)
    have hdT : D ≤ 32*K*T := hDhi.trans (by convert hscaled using 1; ring)
    have hd : D+1 ≤ (32*K+1)*T := by nlinarith only [hdT,hT]
    have hh := Real.log_le_log (by positivity : 0<D+1) hd
    rw [Real.log_mul (by positivity) hTp.ne'] at hh
    have hl := Real.log_le_sub_one_of_pos (show 0<32*K+1 by positivity)
    have hcoef : 32*K+2 ≤ K^2 := by
      have hh : 1000*K ≤ K^2 := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hK hKp.le
      linarith only [hh,hK]
    calc
      _ ≤ 32*K+2+Real.log T := by linarith only [hh,hl]
      _ ≤ (32*K+2)*Log := by
        dsimp only [Log]
        nlinarith only [mul_nonneg (show 0 ≤ 32*K+1 by positivity) (Real.log_nonneg hT)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by linarith only [hLog])
  have hXplus : X+1 ≤ 2*K*(T/P^2) := by
    have hX0 : 1 ≤ T/P^2 := (one_le_div (pow_pos hPp 2)).mpr hPtwo
    have hh := le_mul_of_one_le_left (show 0 ≤ T/P^2 by positivity) hK1
    nlinarith only [hXhi,hX0,hh]
  have hfirst : N*(4*(X+1)*D^2) ≤ K^5*(P*R^3/T) := by
    have hcoeff : 8192*K^3 ≤ K^5 := by
      have hkk : (8192:ℝ) ≤ K^2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 2
        norm_num at hh
        linarith only [hh]
      calc
        _ ≤ K^2*K^3 := mul_le_mul_of_nonneg_right hkk (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (P/R)*(4*(2*K*(T/P^2))*(32*K*P*R^2/T)^2) := by gcongr
      _ = (8192*K^3)*(P*R^3/T) := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hsecond : N*(D*(2+Real.log (D+1))) ≤ K^4*(P^2*R/T)*Log := by
    have hcoef : 32*K^3 ≤ K^4 := by
      simpa only [pow_succ'] using mul_le_mul_of_nonneg_right
        (show (32:ℝ) ≤ K by linarith only [hK]) (by positivity : 0 ≤ K^3)
    calc
      _ ≤ N*(D*(K^2*Log)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogD hD.le) hNp.le
      _ ≤ (P/R)*((32*K*P*R^2/T)*(K^2*Log)) := by gcongr
      _ = (32*K^3)*(P^2*R/T)*Log := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by linarith only [hLog])
  exact ⟨hfirst,hsecond⟩

private theorem physical_tail_monomial_power
    {K T P R Log : ℝ} (hK : 1000 ≤ K) (hT : 1 ≤ T)
    (hPp : 0<P) (hRp : 0<R) (hLog : 1 ≤ Log)
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (K^5*(P*R^3/T)+K^4*(P^2*R/T)*Log)^12 ≤
      K^63*Log^12*(P^6*T*R^3) := by
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hscale1 : (P*R^3/T)^12 ≤ P^6*T*R^3 := by
    have hp6 : P^6 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 3
    have hh := mul_le_mul hp6 hR33 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hscale2 : (P^2*R/T)^12 ≤ P^6*T*R^3 := by
    have hp18 : P^18 ≤ T^9 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg P) hPtwo 9
    have hr9 : R^9 ≤ T^3 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hRthree 3
    have hh : P^18*R^9 ≤ T^13 := by
      calc
        _ ≤ T^9*T^3 := mul_le_mul hp18 hr9 (by positivity) (by positivity)
        _ = T^12 := by ring
        _ ≤ _ := pow_le_pow_right₀ hT (by norm_num)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ P^6*R^3/T^12 by positivity)
    convert hh' using 1 <;> field_simp
  have hfirstPow : (K^5*(P*R^3/T))^12 ≤ K^60*Log^12*(P^6*T*R^3) := by
    calc
      _ = K^60*((P*R^3/T)^12) := by ring
      _ ≤ K^60*(P^6*T*R^3) := mul_le_mul_of_nonneg_left hscale1 (by positivity)
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ K^60*(P^6*T*R^3) by positivity)
          (one_le_pow₀ hLog : 1 ≤ Log^12)
        convert hh using 1
        ring
  have hsecondPow : (K^4*(P^2*R/T)*Log)^12 ≤ K^48*Log^12*(P^6*T*R^3) := by
    calc
      _ = K^48*Log^12*((P^2*R/T)^12) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale2 (by positivity)
  have hcoeff : (2:ℝ)^11*(K^60+K^48) ≤ K^63 := by
    have hpow : K^48 ≤ K^60 := pow_le_pow_right₀ hK1 (by norm_num)
    have hk3 : (4096:ℝ) ≤ K^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
      norm_num at hh
      linarith only [hh]
    calc
      _ ≤ 4096*K^60 := by nlinarith only [hpow]
      _ ≤ K^3*K^60 := mul_le_mul_of_nonneg_right hk3 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2^11*((K^5*(P*R^3/T))^12+(K^4*(P^2*R/T)*Log)^12) :=
      add_pow_le (by positivity) (by positivity) 12
    _ ≤ 2^11*(K^60*Log^12*(P^6*T*R^3)+K^48*Log^12*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirstPow hsecondPow) (by norm_num)
    _ = (2^11*(K^60+K^48))*(Log^12*(P^6*T*R^3)) := by ring
    _ ≤ K^63*(Log^12*(P^6*T*R^3)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

private theorem physical_tail_power
    {K T P R N L X : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hX : 0 ≤ X) (hXhi : X ≤ K*(T/P^2))
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    let D := 8/(L*N*(N+1))
    (N*(4*(X+1)*D^2+D*(2+Real.log (D+1))))^12 ≤
      K^63*(1+Real.log T)^12*(P^6*T*R^3) := by
  intro D
  let Log := 1+Real.log T
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hD : 0<D := by dsimp only [D]; positivity
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  obtain ⟨hfirst,hsecond⟩ := physical_tail_component_bounds hK hT hP hR hN
    hNlo hNhi hLlo hX hXhi hPtwo hRthree
  have hlogDpos : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  have hsum : N*(4*(X+1)*D^2+D*(2+Real.log (D+1))) ≤
      K^5*(P*R^3/T)+K^4*(P^2*R/T)*Log := by
    rw [mul_add]
    exact add_le_add hfirst hsecond
  exact (pow_le_pow_left₀ (by positivity) hsum 12).trans
    (physical_tail_monomial_power hK hT hPp hRp hLog hPtwo hRthree hR33)

private theorem sum_twelfth_common_bound
    {K D a b : ℝ} (hK : 1000 ≤ K) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (ha' : a^12 ≤ K^n*D) (hb' : b^12 ≤ K^n*D) :
    (a+b)^12 ≤ K^(n+3)*D := by
  have hKp : 0<K := by linarith only [hK]
  have hk3 : (4096:ℝ) ≤ K^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hK 3
    norm_num at hh
    linarith only [hh]
  calc
    _ ≤ 2^11*(a^12+b^12) := add_pow_le ha hb 12
    _ ≤ 2^11*(K^n*D+K^n*D) :=
      mul_le_mul_of_nonneg_left (add_le_add ha' hb') (by norm_num)
    _ = 4096*(K^n*D) := by ring
    _ ≤ K^3*(K^n*D) := mul_le_mul_of_nonneg_right hk3 (by positivity)
    _ = _ := by rw [pow_add]; ring

private theorem physical_nonminor_error_power
    {K T P R N Q L Z : ℝ} (hK : 1000 ≤ K)
    (hT : 1 ≤ T) (hP : 1 ≤ P) (hR : 1 ≤ R) (hN : 1 ≤ N) (hQ : 0<Q)
    (hNlo : P/(2*R) ≤ N) (hNhi : N ≤ P/R)
    (hLlo : T/(K*P^3) ≤ L) (hZ : 0 ≤ Z)
    (hZupper : Z ≤ K^2*(T*Q^2/P^2))
    (hcut : T*Q^2 ≤ K^4*P^2*R)
    (hPtwo : P^2 ≤ T) (hRthree : R^3 ≤ T) (hR33 : R^33 ≤ T^10) :
    (Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)+
      Real.sqrt (12/(L*N*Q))))^12 ≤
        K^114*(1+Real.log T)^24*(P^6*T*R^3) := by
  let Log := 1+Real.log T
  let D := Log^24*(P^6*T*R^3)
  have hKp : 0<K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hLp : 0<L := (show 0<T/(K*P^3) by positivity).trans_le hLlo
  have hLog : 1 ≤ Log := by dsimp only [Log]; linarith only [Real.log_nonneg hT]
  have hZR : Z ≤ K^7*R*Log := by
    have hqscale : T*Q^2/P^2 ≤ K^4*R := by
      apply (div_le_iff₀ (pow_pos hPp 2)).mpr
      nlinarith only [hcut]
    calc
      Z ≤ K^2*(T*Q^2/P^2) := hZupper
      _ ≤ K^2*(K^4*R) := mul_le_mul_of_nonneg_left hqscale (sq_nonneg K)
      _ = K^6*R := by ring
      _ ≤ K^7*R := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hK1 (by norm_num)) hRp.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLog
  have hcommon := physical_common_error_powers hK hT hP hR hN hNlo hNhi
    hLlo hZ hZR hPtwo hRthree hR33
  have hend := physical_endpoint_error_power hK hTp hPp hRp hQ hNlo hLlo hZ
    hZupper hcut hRthree
  have hend' : (Z*Real.sqrt (12/(L*N*Q)))^12 ≤ K^111*D := by
    calc
      _ ≤ K^72*(P^6*T*R^3) := hend
      _ ≤ K^111*(P^6*T*R^3) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hK1 (by norm_num)) (by positivity)
      _ ≤ K^111*((P^6*T*R^3)*Log^24) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog)) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have hlogN : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hcommon' : (Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)))^12 ≤
      K^111*D := by
    dsimp only [D,Log]
    simpa only [mul_assoc] using hcommon
  have hh := sum_twelfth_common_bound hK (show 0 ≤ D by dsimp only [D]; positivity)
    (show 0 ≤ Z*(Real.sqrt (3*N)*Real.log (6*N)+6/(L*N^2)) by positivity)
    (show 0 ≤ Z*Real.sqrt (12/(L*N*Q)) by positivity) 111
    hcommon' hend'
  dsimp only [D,Log] at hh
  simpa only [Nat.reduceAdd,mul_add,mul_assoc,add_assoc] using hh

#print axioms sum_twelfth_common_bound
#print axioms physical_nonminor_error_power
#print axioms physical_tail_power
#print axioms physical_tail_monomial_power
#print axioms physical_tail_component_bounds
#print axioms physical_direct_main_power
#print axioms physical_boundary_power
#print axioms direct_cut_implies_quadratic_cut
#print axioms physical_endpoint_error_power
#print axioms physical_common_error_powers
#print axioms normalized_frozen_moment_main
#print axioms moment_rpow_prefactor
#print axioms normalized_minor_moment_main
#print axioms physical_moment_prefactors
#print axioms normalized_pair_count_bounds
#print axioms physical_block_count_bounds
#print axioms physical_pair_factor_bounds
#print axioms physical_coordinate_budget_bounds
#print axioms minor_branch_scales
#print axioms frozen_branch_scales
#print axioms direct_branch_cube_cutoff
#print axioms normalized_physical_dual_ceiling
#print axioms exists_model_scale_constant
#print axioms source_smallness_of_scale
#print axioms eventually_model_block_smallness
#print axioms eventually_baseline_model_block_smallness
#print axioms baseline_scale_geometry
#print axioms normalized_frozen_main_le
#print axioms normalized_minor_main_le
#print axioms physical_dual_ceiling_bounds
#print axioms physical_dual_sqrt_weight_bound
#print axioms physical_dual_error_bounds
end TaoTrudgianYang2025.NextPhysical
