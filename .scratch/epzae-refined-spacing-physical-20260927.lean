import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set Expdb
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

theorem refined_spacing_physical_product
    {P U w p q : ℝ} (hP : 0<P) (hU : 0<U) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) =
    P^12*U^3+w*P^12*U^((5:ℝ)/2)+
      P^(11+p+q)*U^(2+p+q/2)*w^(-p)+P^10*U := by
  have hbase : P^10*Real.sqrt U*(P*U*Real.sqrt U)=P^11*U^2 := by
    calc
      _ = P^11*U*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hroot : U^2*Real.sqrt U=U^((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast U 2,←Real.rpow_add hU]
    norm_num
  have hpowers : P^(11+p+q)=P^11*P^p*P^q := by
    rw [Real.rpow_add hP,Real.rpow_add hP]
    norm_num
  have hupowers : U^(2+p+q/2)=U^2*U^p*U^(q/2) := by
    rw [Real.rpow_add hU,Real.rpow_add hU]
    norm_num
  have hdensity : P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q)=
      P^(11+p+q)*U^(2+p+q/2) := by
    rw [Real.mul_rpow hP.le hU.le,Real.mul_rpow hP.le (Real.sqrt_nonneg U),
      Real.sqrt_eq_rpow,←Real.rpow_mul hU.le,hpowers,hupowers]
    rw [show (1/2:ℝ)*q=q/2 by ring]
    ring
  have hinv : P^11*U^2*(1/(P*U))=P^10*U := by
    field_simp
  rw [hbase]
  calc
    _ = P^12*U^3+w*P^12*(U^2*Real.sqrt U)+
        (P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q))*w^(-p)+P^11*U^2*(1/(P*U)) := by ring
    _ = _ := by rw [hroot,hdensity,hinv]

theorem refined_spacing_physical_product_bound
    {P U w p q : ℝ} (hP : 1≤P) (hU : 0<U) (hw : 0≤w) (hsmall : P*U^2≤1) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) ≤
    2*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  rw [refined_spacing_physical_product hPp hU]
  have hfirst : P^12*U^3≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤P^11*U by positivity)
    nlinarith only [hh]
  have hlast : P^10*U≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hP (show 0≤P^10*U by positivity)
    nlinarith only [hh]
  have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
  have hdensity : 0≤P^(11+p+q)*U^(2+p+q/2)*w^(-p) := by positivity
  linarith only [hfirst,hlast,hmid,hdensity]
/-- Uniform denominator-free bound for the actual refined spacing cost.
The two elementary cardinality caps are consumed by the existing loss bound. -/
theorem exists_refined_uniform_frozen_rhs
    {l ε Cc p q : ℝ} (hl : 0<l) (hε : 0<ε) (hCc : 1≤Cc) :
    ∃ C > (0:ℝ), ∀ (P U Z w : ℝ) (Q : ℕ),
      0<P → 0<U → U≤1/3600 → 1≤P*U → P*U^2≤1 → 0≤Z → 0<w →
      0<Q → (Q:ℝ)≤P →
      Z≤Cc*P*U*(Q:ℝ)^2 → Z≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let W := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let R := Z+(P*U*Real.sqrt U)*E*(1+Real.log P)
      Loss*(2*Z)^10*R+(Z*Err)^12 ≤
        C*P^ε*(1+Real.log P)^24*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  obtain ⟨Cl,hCl,hloss⟩ := exists_displacement_frozen_loss_bound hl hε
  obtain ⟨Ce,hCe,herror⟩ := exists_displacement_frozen_error_majorant hl
  let C := Cl*Cc^10*(Cc+2)+(Cc*Ce)^12
  have hCcp : 0<Cc := zero_lt_one.trans_le hCc
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro P U Z w Q hP hU hUsmall hPU hsmall hZ hw hQ hQP hZlo hZhi
    N L M V W d Loss Err E R
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hP1 : 1≤P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  let J := 1+Real.log P
  let B := Cc*P*J
  let Cost := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)
  have hlogP := Real.log_nonneg hP1
  have hJ1 : 1≤J := by dsimp only [J]; linarith only [hlogP]
  have hJ : 0<J := zero_lt_one.trans_le hJ1
  have hB : 0<B := by dsimp only [B]; positivity
  have hCost : 0≤Cost := by dsimp only [Cost]; positivity
  have hFirst : P^11*U≤Cost := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+p+q)*U^(2+p+q/2)*w^(-p) := by positivity
    dsimp only [Cost]
    linarith only [hmid,hlast]
  have hZlo' : Z ≤ B*U*(Q:ℝ)^2 := by
    calc
      _ ≤ Cc*P*U*(Q:ℝ)^2 := hZlo
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ Cc*P*U*(Q:ℝ)^2 by positivity) hJ1
        dsimp only [B]
        nlinarith only [hh]
  have hZhi' : Z*(Q:ℝ)^2 ≤ B := by
    have hh := mul_le_mul_of_nonneg_right hZhi (sq_nonneg (Q:ℝ))
    convert hh using 1
    dsimp only [B,J]
    field_simp
  have hZgeo : Z ≤ Cc*P*J*Real.sqrt U :=
    displacement_cardinality_geometric hU.le hQr hZ hZlo' hZhi'
  have hQpow : (Q:ℝ)^ε ≤ P^ε := Real.rpow_le_rpow hQr.le hQP hε.le
  have hlogQ : 0 ≤ 1+Real.log Q := by
    have hh := Real.log_nonneg hQ1
    positivity
  have hlogQP : 1+Real.log Q ≤ J := add_le_add_right (Real.log_le_log hQr hQP) 1
  have hLoss : Loss*(2*Z)^10 ≤ Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22 := by
    calc
      _ ≤ Cl*B^10*Real.sqrt U*(Q:ℝ)^ε*(1+Real.log Q)^12 :=
        hloss U B Z Q hU hUsmall hZ hQ hZlo' hZhi'
      _ ≤ Cl*B^10*Real.sqrt U*P^ε*J^12 := by gcongr
      _ = _ := by dsimp only [B]; ring
  have hZprod : P^10*Real.sqrt U*Z≤Cc*J*(P^11*U) := by
    calc
      _ ≤ P^10*Real.sqrt U*(Cc*P*J*Real.sqrt U) :=
        mul_le_mul_of_nonneg_left hZgeo (by positivity)
      _ = Cc*J*P^11*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hprod := refined_spacing_physical_product_bound (p:=p) (q:=q) hP1 hU hw.le hsmall
  change P^10*Real.sqrt U*(P*U*Real.sqrt U)*E≤2*Cost at hprod
  have hRprod : P^10*Real.sqrt U*R≤(Cc+2)*J*Cost := by
    calc
      _ = P^10*Real.sqrt U*Z+(P^10*Real.sqrt U*(P*U*Real.sqrt U)*E)*J := by
        dsimp only [R,J]
        ring
      _ ≤ Cc*J*(P^11*U)+(2*Cost)*J :=
        add_le_add hZprod (mul_le_mul_of_nonneg_right hprod hJ.le)
      _ ≤ Cc*J*Cost+(2*Cost)*J := by gcongr
      _ = _ := by ring
  have hR : 0≤R := by dsimp only [R,E]; positivity
  have hmain : Loss*(2*Z)^10*R≤Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost := by
    calc
      _ ≤ (Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22)*R :=
        mul_le_mul_of_nonneg_right hLoss hR
      _ = (Cl*Cc^10*P^ε*J^22)*(P^10*Real.sqrt U*R) := by ring
      _ ≤ (Cl*Cc^10*P^ε*J^22)*((Cc+2)*J*Cost) :=
        mul_le_mul_of_nonneg_left hRprod (by positivity)
      _ = Cl*Cc^10*(Cc+2)*P^ε*J^23*Cost := by ring
      _ ≤ _ := by gcongr; norm_num
  have hErr : Err ≤ Ce*U^(-(1:ℝ)/4)*J := herror P U Q hP hU hUsmall hPU hQ1
  have hErr0 : 0 ≤ Err := by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (displacement_block_scale hU hUsmall).1
    have hlogN := Real.log_nonneg (show 1 ≤ 6*(N:ℝ) by linarith only [hN1])
    dsimp only [Err,L]
    positivity
  have hquarter : Real.sqrt U*U^(-(1:ℝ)/4)=U^((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hU]
    norm_num
  have hZE : Z*Err ≤ Cc*Ce*P*U^((1:ℝ)/4)*J^2 := by
    calc
      _ ≤ (Cc*P*J*Real.sqrt U)*(Ce*U^(-(1:ℝ)/4)*J) :=
        mul_le_mul hZgeo hErr hErr0 (by positivity)
      _ = Cc*Ce*P*(Real.sqrt U*U^(-(1:ℝ)/4))*J^2 := by ring
      _ = _ := by rw [hquarter]
  have herror₀ := refined_elementary_twelfth hP1 hU hU1 (mul_nonneg hZ hErr0)
    (mul_nonneg hCcp.le hCe.le) hJ1 hε.le (le_refl ((1:ℝ)/4)) hsmall hZE
  have herror' : (Z*Err)^12≤(Cc*Ce)^12*P^ε*J^24*Cost :=
    herror₀.trans (mul_le_mul_of_nonneg_left hFirst (by positivity))
  calc
    _ ≤ Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost+(Cc*Ce)^12*P^ε*J^24*Cost :=
      add_le_add hmain herror'
    _ = _ := by dsimp only [C,Cost]; ring


/-- Physical normalization of the refined count and its harmonic shift weight. -/
theorem exists_refined_physical_pair_bound
    {l a b u p q Cp : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hq : 0≤q) (hCp : 1≤Cp) :
    ∃ Ca ≥ (1:ℝ), ∀ P U M Q Z w : ℝ,
      0<P → 0<U → U≤1/3600 → 1≤P*U*Real.sqrt U →
      1≤M → 0<Q → Q≤4*M → 0≤Z → 0<w →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let lam := a*U/P
      let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
      let η := 4*D₀/Q
      let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
        (P*U/u)^p*Dmax^q*w^(-p)+u/(P*U))
      4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) ≤
        Ca*(Z+(P*U*Real.sqrt U)*E*(1+Real.log P)) := by
  let n := 2+48/a
  have hn : 1≤n := by
    have hh : 0<48/a := by positivity
    dsimp only [n]
    linarith only [hh]
  obtain ⟨Ce,hCe,hcount⟩ := refined_count_physical_majorant
    (p:=p) hl ha hb hu (le_trans zero_le_one hn) hq
  let Ch := 3*n+(1728/a)*(1+Real.log n)
  have hCh : 0<Ch := by
    have hlogn := Real.log_nonneg hn
    dsimp only [Ch]
    positivity
  let Ca := 4+6*Cp*Ce*Ch
  have hCa : 1≤Ca := by
    have hh : 0≤6*Cp*Ce*Ch := by positivity
    dsimp only [Ca]
    linarith only [hh]
  refine ⟨Ca,hCa,?_⟩
  intro P U M Q Z w hP hU hUsmall hK hM hQ hQM hZ hw
    N L lam D₀ η rho K Dmax Dweight E Count
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hcut := displacement_physical_cutoff ha hP hU hUsmall hK hM hQ hQM
  change 1≤K ∧ (K:ℝ)≤n*(P*U*Real.sqrt U) ∧ η≤4*Real.sqrt U ∧
    Dweight≤(1728/a)*(P*U*Real.sqrt U) at hcut
  have hη : 0≤η := by dsimp only [η,D₀]; positivity
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (displacement_block_scale hU hUsmall).1
  have hlam : 0<lam := by dsimp only [lam]; positivity
  have hDweight : 0≤Dweight := by dsimp only [Dweight]; positivity
  have hcount' : Count≤(Cp*Ce)*E := by
    have hh := hcount P U K η w hP hU hU1 hK (Nat.cast_nonneg K) hcut.2.1 hη hcut.2.2.1 hw
    dsimp only [Count]
    calc
      _ ≤ Cp*(Ce*E) := mul_le_mul_of_nonneg_left hh (le_trans zero_le_one hCp)
      _ = _ := by ring
  have hweight := displacement_harmonic_weight hn hscale.2.1 hU hU1
    hcut.1 hcut.2.1 hDweight hcut.2.2.2
  change _≤Ch*(P*U*Real.sqrt U)*(1+Real.log P) at hweight
  have hharm : 0≤(harmonic K:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
  have hweight0 : 0≤3*(K:ℝ)+Dweight*(harmonic K:ℝ) := by positivity
  have hlogP := Real.log_nonneg hscale.2.1
  have hE : 0≤E := by dsimp only [E]; positivity
  have hweighted : Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))≤
      (Cp*Ce*Ch)*((P*U*Real.sqrt U)*E*(1+Real.log P)) := by
    calc
      _ ≤ ((Cp*Ce)*E)*(Ch*(P*U*Real.sqrt U)*(1+Real.log P)) :=
        mul_le_mul hcount' hweight hweight0 (by positivity)
      _ = _ := by ring
  have hc0 : 0≤Cp*Ce*Ch := by positivity
  have ht0 : 0≤(P*U*Real.sqrt U)*E*(1+Real.log P) := by positivity
  dsimp only [Ca]
  nlinarith only [hweighted,mul_nonneg hc0 hZ,ht0]

/-- The physical cutoff implies all lifting and interior-margin hypotheses. -/
theorem refined_physical_lifting_domain
    {σ l a b u n P T U η K κ₀ A B : ℝ}
    (hσ : 0<σ) (hl : 0<l) (ha : 0<a) (hn : 0≤n)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hU1 : U≤1)
    (hUeq : U=u*T/P^3) (hK : 1≤P*U*Real.sqrt U)
    (hKhi : K≤n*(P*U*Real.sqrt U)) (hηhi : η≤4*Real.sqrt U)
    (hlift : 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2)
    (hκ : (2*n*u/σ)*Real.sqrt U≤κ₀)
    (hA : P+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<A)
    (hB : B+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<2*P) :
    let L := l*U
    let lam := a*U/P
    let Rmax := 36*U^2/lam
    let Dmax := K/L+1
    2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 ∧
      P<A-Rmax ∧ B+Rmax+2*Dmax<2*P ∧ 2*K*P^2/(σ*T)≤κ₀ := by
  intro L lam Rmax Dmax
  let m := 36/a+2*(n/l+1)+1
  have hL : 0<L := by dsimp only [L]; positivity
  have hRmax : Rmax≤(36/a)*(P*Real.sqrt U) := by
    have hUsqrt : U≤Real.sqrt U := by
      nlinarith only [Real.sq_sqrt hU.le,Real.sqrt_le_one.mpr hU1,Real.sqrt_nonneg U]
    calc
      _ = (36/a)*(P*U) := by dsimp only [Rmax,lam]; field_simp
      _ ≤ _ := by gcongr
  have hPS : 1≤P*Real.sqrt U := hK.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hDmax : Dmax≤(n/l+1)*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi hL.le) hPS
      _ = _ := by field_simp
  have hlift' : 2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 := by
    have hid : 10368*(b*U/P)*U^4/(lam^2*L)=
        (10368*b/(a^2*l))*(P*U^2) := by dsimp only [lam,L]; field_simp
    rw [hid]
    linarith only [hηhi,hlift]
  have hleft : P<A-Rmax := by
    have hgap : Rmax < m*(P*Real.sqrt U) := by
      have hh : 0<(2*(n/l+1)+1)*(P*Real.sqrt U) := by positivity
      dsimp only [m]
      nlinarith only [hRmax,hh]
    linarith only [hA,hgap]
  have hright : B+Rmax+2*Dmax<2*P := by
    have hh : 0<P*Real.sqrt U := by positivity
    nlinarith only [hB,hRmax,hDmax,hh]
  have hκ' : 2*K*P^2/(σ*T)≤κ₀ := by
    calc
      _ ≤ 2*(n*(P*U*Real.sqrt U))*P^2/(σ*T) := by gcongr
      _ = (2*n*u/σ)*Real.sqrt U := by simp only [hUeq]; field_simp
      _ ≤ _ := hκ
  exact ⟨hlift',hleft,hright,hκ'⟩

/-- Uniform rational-band estimate for the actual model sum.  All analytic
constants precede the model and its physical scales; the remaining assumptions
are explicit smallness and interior-margin conditions, not source bounds. -/
theorem exists_model_uniform_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let X := x*P*U
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      ∃ r : ι→ℚ,
        (∀ Q₀ : ℕ, 2≤Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀≤(r i).den)).card:ℝ)≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den≤N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
            (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (1≤j → 12≤L*(Q:ℝ)*(N:ℝ)^2 → 384≤L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
              (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
              C*P^ε*(1+Real.log P)^24*
                (P^11*U+w*P^12*U^((5:ℝ)/2)+
                  P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))))) := by
  classical
  intro u l a b x n m
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have ha : 0<a := by dsimp only [a]; positivity [modelPhaseJetLower_pos hσ 3]
  have hb : 0<b := by dsimp only [b]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hx : 0≤x := by dsimp only [x]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  have hn : 1≤n := by
    have hh : 0<48/a := by positivity
    dsimp only [n]
    linarith only [hh]
  have hm : 0 < m := by dsimp only [m]; positivity
  have hq : 0≤l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,hsource⟩ :=
    exists_model_refined_source_bands hσ hpair hε hp
  obtain ⟨Cc,hCc,hcard⟩ := exists_displacement_cardinality_majorants hl hx
  obtain ⟨Cr,hCr,hrhs⟩ := exists_refined_uniform_frozen_rhs
    (p:=k₀+ε) (q:=l₀+ε) hl hε hCc
  obtain ⟨Ca,hCa,hpairPhysical⟩ := exists_refined_physical_pair_bound
    (p:=k₀+ε) hl ha hb.le hu hq hCp
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf*Ca*Cr,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw hwhalf
    U N L X hUsmall hK hbPU hLsmall hsmall hlift hκ hA hB hmul hH base hbuffer
  have hU : 0<U := by dsimp only [U]; positivity
  have hU1 : U≤1 := by linarith only [hUsmall]
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hblock := displacement_block_scale hU hUsmall
  have hN : 0<N := hblock.1
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hL : 0<L := by dsimp only [L]; positivity
  have hmargin : 0 < m*(P*Real.sqrt U) := by positivity
  have hA₀ : P<A := by linarith only [hA,hmargin]
  have hB₀ : B<2*P := by linarith only [hB,hmargin]
  have hLeq : modelPhaseJetLower σ 2*T/P^3=L := by
    dsimp only [L,l,U]; field_simp
  have hlameq : modelPhaseJetLower σ 3*T/P^4=a*U/P := by
    dsimp only [a,U]; field_simp
  have hFeq : (modelPhaseJetCoefficient σ 3+1)*T/P^4=b*U/P := by
    dsimp only [b,U]; field_simp
  have hXeq : (modelPhaseJetCoefficient σ 1+1)*T/P^2/2=X := by
    dsimp only [X,x,U]; field_simp
  have htaylor := displacement_taylor_smallness hb hP hU hUsmall hbPU
  obtain ⟨r,htail,hbands⟩ := hsource ι S F T P k H N s A B w hF hT hP hN hw hwhalf
    hA₀ hB₀ (by change 12*U≤1; linarith only [hUsmall])
    (by rw [hLeq]; exact hLsmall)
    (by rw [hFeq]; exact htaylor.1) htaylor.2 hmul hH hbuffer
  clear hsource
  rw [hLeq,hXeq] at htail
  refine ⟨r,htail,?_⟩
  intro j Q G Zd Err
  have hband := hbands j
  clear hbands
  rw [hLeq,hlameq,hFeq,hXeq] at hband
  refine ⟨hband.2.2.1,?_⟩
  intro hj hdual hfrozen
  by_cases hempty : G=∅
  · simp only [hempty,Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    positivity
  have hQ : 0<Q := by dsimp only [Q]; positivity
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hi',hlog⟩ := Finset.mem_filter.mp hi
  have hiN := (Finset.mem_filter.mp hi').2
  have hpow := Nat.pow_log_le_self 2 (r i).pos.ne'
  rw [hlog] at hpow
  have hQN : (Q:ℝ)≤2*(N:ℝ) := by
    have hh : Q≤2*N := by
      calc
        Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
        _≤2*N := Nat.mul_le_mul_left _ (hpow.trans hiN)
    exact_mod_cast hh
  have hc := hcard P U Q hP hU hUsmall hscale.1 hQ1 hQN
  clear hcard
  have hZlo : (G.card:ℝ)≤Cc*P*U*(Q:ℝ)^2 := hband.1.trans hc.1
  have hZhi : (G.card:ℝ)≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) :=
    (hband.2.1 hj).trans hc.2
  let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
  let lam := a*U/P
  let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
  let η := 4*D₀/(Q:ℝ)
  let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
  let K := ⌈3*U*(rho+1)⌉₊
  let Rmax := 36*U^2/lam
  let Dmax := (K:ℝ)/L+1
  let Dweight := 144*U^2/(lam*N)
  let E := P*U+w*(P*Real.sqrt U)+(P*U)^(k₀+ε)*(P*Real.sqrt U)^(l₀+ε)*w^(-(k₀+ε))+1/(P*U)
  let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
    (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
  let Weight := 3*(K:ℝ)+Dweight*(harmonic K:ℝ)
  let Pair := 4*(G.card:ℝ)+6*Count*Weight
  let R := (G.card:ℝ)+(P*U*Real.sqrt U)*E*(1+Real.log P)
  have hM1 : (1:ℝ)≤M := by
    have hh : 1≤M := by dsimp only [M]; omega
    exact_mod_cast hh
  have hMscale := hblock.2.2.2.2.2 Q hQ
  have hQM : (Q:ℝ)≤4*(M:ℝ) := by
    have hh := hMscale.1
    change (7/16:ℝ)*Q≤(M:ℝ) at hh
    linarith only [hh,hQr.le]
  have hthin : (Q:ℝ)^2<6*(M:ℝ)^2 := hMscale.2.2
  have hcut := displacement_physical_cutoff ha hP hU hUsmall hK hM1 hQr hQM
  change 1≤K ∧ (K:ℝ)≤n*(P*U*Real.sqrt U) ∧ η≤4*Real.sqrt U ∧
    Dweight≤(1728/a)*(P*U*Real.sqrt U) at hcut
  obtain ⟨hlift',hleft,hright,hκ'⟩ := refined_physical_lifting_domain
    hσ hl ha (le_trans zero_le_one hn) hP hT hU hU1 rfl hK
    hcut.2.1 hcut.2.2.1 hlift hκ hA hB
  have hPair : Pair≤Ca*R := by
    have hh := hpairPhysical P U M Q G.card w hP hU hUsmall hK
      hM1 hQr hQM (by positivity) hw
    have hTP : T/P^2=P*U/u := by dsimp only [U]; field_simp
    have hPT : P^2/T=u/(P*U) := by dsimp only [U]; field_simp
    dsimp only [Pair,Count,Weight,R]
    rw [hTP,hPT]
    exact hh
  have hs := hband.2.2.2 hdual hfrozen hthin hlift' hleft hright hκ'
  have hr := hrhs P U G.card w Q hP hU hUsmall hscale.1 hsmall
    (by positivity) hw hQ (hQN.trans hscale.2.2) hZlo hZhi
  clear hband hpairPhysical hrhs
  let V := 756*U/L
  let W := 1+32/(L*(Q:ℝ)^2*N)
  let d := L*(Q:ℝ)*N/12
  let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
    (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
  change _ ≤ Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12) at hs
  change Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12≤_ at hr
  have hW0 : 0≤W := by dsimp only [W]; positivity
  have hLoss0 : 0≤Loss*(2*(G.card:ℝ))^10 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hW0) 11)
            (sq_nonneg W)) ((show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _))
          ((show Even (6:ℕ) from ⟨3,rfl⟩).pow_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg M) _))
      ((show Even (10:ℕ) from ⟨5,rfl⟩).pow_nonneg _)
  have he0 : 0≤((G.card:ℝ)*Err)^12 := (show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _
  have habsorb : Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12)≤
      (Cf*Ca)*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12) := by
    have hh := mul_le_mul_of_nonneg_left hPair hLoss0
    rw [mul_left_comm (Loss*(2*(G.card:ℝ))^10) Ca R] at hh
    have he := le_mul_of_one_le_left he0 hCa
    calc
      _ ≤ Cf*(Ca*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12)) :=
        mul_le_mul_of_nonneg_left
          ((add_le_add hh he).trans_eq (mul_add Ca _ _).symm) hCf.le
      _ = _ := (mul_assoc _ _ _).symm
  exact hs.trans (habsorb.trans (by
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤Cf*Ca by positivity)
    simpa only [mul_assoc] using hh))

/-- Sum all constructed denominator bands and the tail, preserving the actual model source. -/
theorem exists_model_refined_source_global
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      (1+23*(N:ℝ)+∑ i∈S,
        ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
          (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
        C*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n m
  let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
  have hu : 0<u := by dsimp only [u]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hl : 0<l := by dsimp only [l]; positivity [modelPhaseJetLower_pos hσ 2]
  have hx : 0≤x := by dsimp only [x]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,hsource⟩ :=
    exists_model_uniform_refined_source_bands hσ hpair hε hp
  obtain ⟨K,hK,hcutoff⟩ := exists_displacement_small_band_cutoff hl
  obtain ⟨Cs,hCs,hsmall⟩ := exists_displacement_small_band_majorant hl hx hK
  obtain ⟨Ct,hCt,htailSize⟩ := exists_displacement_tail_majorant hl hx
  let C₀ := (24:ℝ)^12+Ct^12+Cf+(Cd*Cs)^12
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,1000^12*C₀,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw₀ hwhalf U N
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH base hbuffer
  let L := l*U
  let X := x*P*U
  let f := fun t => T*F (t/P)
  have hU : 0<U := by dsimp only [U]; positivity
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hN := (displacement_block_scale hU hUsmall).1
  obtain ⟨r,htail,hband⟩ := hsource ι S F T P k H s A B w hF hT hP hw₀ hwhalf
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH hbuffer
  let weight := fun i => ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖
  let R := S.filter (fun i => N+1 ≤ (r i).den)
  let g := fun j => ∑ i∈(S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j),weight i
  let J := Nat.log 2 N+1
  let Log := 1+Real.log P
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  let Budget := C₀*P^ε*Log^24*E
  have hlog1 : 1 ≤ Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0 < Log := lt_of_lt_of_le zero_lt_one hlog1
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFirst : P^11*U≤E := by
    have hmid : 0≤w*P^12*U^((5:ℝ)/2) := by positivity
    have hlast : 0≤P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε)) := by positivity
    dsimp only [E]
    linarith only [hmid,hlast]
  have hbudget (c : ℝ) (hc : c ≤ C₀) : c*P^ε*Log^24*E ≤ Budget := by
    dsimp only [Budget]
    gcongr
  have hbaseBudget (c : ℝ) (hc0 : 0≤c) (hc : c≤C₀) :
      c*P^ε*Log^24*(P^11*U)≤Budget :=
    (mul_le_mul_of_nonneg_left hFirst (by positivity)).trans (hbudget c hc)
  have hCdp : 0 ≤ Cd := by linarith only [hCd]
  have hCf₀ : Cf ≤ C₀ := by
    dsimp only [C₀]
    linarith only [pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCs₀ : (Cd*Cs)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12]
  have hCt₀ : Ct^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCb₀ : (24:ℝ)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hw (i : ι) : 0 ≤ weight i := norm_nonneg _
  have hwH (i : ι) (hi : i∈S) : weight i ≤ N := by
    have hh := norm_sum_integer_Ioc_le (fun n => (𝐞 (f n):ℂ)) (by intro n; simp)
      (a:=s+(N:ℤ)*k i) (b:=s+(N:ℤ)*k i+H i) (by omega)
    have he : ((s+(N:ℤ)*k i+H i:ℤ):ℝ)-(s+(N:ℤ)*k i:ℤ)=H i := by push_cast; ring
    rw [he] at hh
    exact hh.trans (Nat.cast_le.mpr (hH i hi))
  have htail' : (∑ i∈R,weight i) ≤ Ct*P*Real.sqrt U := by
    have hq0 : 2 ≤ N+1 := by omega
    have hc := htail (N+1) hq0
    have hs : (∑ i∈R,weight i) ≤ (R.card:ℝ)*(N:ℝ) := by
      calc
        _ ≤ ∑ _i∈R,(N:ℝ) := Finset.sum_le_sum (fun i hi => hwH i (Finset.mem_filter.mp hi).1)
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (N:ℝ) by positivity)
    have hsize := (htailSize P U hP hU hUsmall hscale.1).2
    simp only [Nat.cast_add,Nat.cast_one] at hm
    change (N:ℝ)*(R.card:ℝ) ≤ _ at hm
    exact hs.trans (by
      calc
        _ = (N:ℝ)*(R.card:ℝ) := by ring
        _ ≤ _ := hm
        _ ≤ _ := hsize)
  have htailMoment : (∑ i∈R,weight i)^12 ≤ Budget := by
    have hh : (∑ i∈R,weight i) ≤ Ct*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htail'.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      hCt.le hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans (hbaseBudget _ (by positivity) hCt₀)
  have hboundary : (1+23*(N:ℝ))^12 ≤ Budget := by
    have hh : 1+23*(N:ℝ) ≤ 24*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact (htailSize P U hP hU hUsmall hscale.1).1.trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      (by norm_num : (0:ℝ)≤24) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans
        (hbaseBudget _ (by positivity) hCb₀)
  have hbands (j : ℕ) : (g j)^12 ≤ Budget := by
    let Q : ℕ := 2^(j+1)
    have hQ1 : (1:ℝ) ≤ Q := by dsimp only [Q]; exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) : 1 ≤ 2^(j+1))
    have hQ : (0:ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
    by_cases hlarge : 1 ≤ j ∧ 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 ∧ 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3
    · exact ((hband j).2 hlarge.1 hlarge.2.1 hlarge.2.2).trans (hbudget _ hCf₀)
    have hcases : (Q:ℝ) ≤ 2 ∨ l*U*(Q:ℝ)*(N:ℝ)^2 < 12 ∨ (l*U)^2*(Q:ℝ)^3*(N:ℝ)^3 < 384 := by
      by_cases hj : 1 ≤ j
      · by_cases hd : 12 ≤ L*(Q:ℝ)*(N:ℝ)^2
        · exact Or.inr (Or.inr (lt_of_not_ge (fun hh => hlarge ⟨hj,hd,hh⟩)))
        · exact Or.inr (Or.inl (lt_of_not_ge hd))
      · have hj0 : j=0 := by omega
        left
        simp only [Q,hj0,zero_add,pow_one,Nat.cast_ofNat,le_refl]
    have hcut := hcutoff U Q hU hUsmall hQ hcases
    have hs := hsmall P U Q hP hU hUsmall hscale.1 hQ1 hcut
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ Cd by linarith only [hCd])
    have hg : g j ≤ (Cd*Cs)*P*U^((1:ℝ)/3)*Log := by
      calc
        _ ≤ _ := (hband j).1
        _ ≤ _ := by convert hm using 1 <;> ring
    have hg' : g j≤(Cd*Cs)*P*U^((1:ℝ)/3)*Log^2 :=
      hg.trans (by
        have hh : Log≤Log^2 := by nlinarith only [hlog1]
        gcongr)
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      (mul_nonneg hCdp hCs.le) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/3) hsmall₀ hg').trans
        (hbaseBudget _ (by positivity) hCs₀)
  have hfinite := displacement_finite_moment_budget g J (by positivity)
    (Finset.sum_nonneg (fun i _ => hw i)) (fun j => Finset.sum_nonneg (fun i _ => hw i))
    hboundary htailMoment (fun j _ => hbands j)
  have hJbound : (J:ℝ)+2 ≤ 1000*Log :=
    (physical_dyadic_geometry (by norm_num : (1000:ℝ) ≤ 1000) hscale.2.1 hN
      (by linarith only [hscale.2.2,show (0:ℝ) ≤ N by positivity])).1
  change (1+23*(N:ℝ)+∑ i∈S,weight i)^12 ≤ _
  rw [sum_by_denominator_bands S (fun i => (r i).den) weight N]
  change (1+23*(N:ℝ)+((∑ i∈R,weight i)+∑ j∈Finset.range J,g j))^12 ≤ _
  calc
    _ = (1+23*(N:ℝ)+(∑ i∈R,weight i)+∑ j∈Finset.range J,g j)^12 := by congr 1; ring
    _ ≤ ((J:ℝ)+2)^12*Budget := hfinite
    _ ≤ (1000*Log)^12*Budget := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hJbound 12) (by dsimp only [Budget]; positivity)
    _ = (1000^12*C₀)*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
      change _ = (1000^12*C₀)*P^ε*Log^36*E
      dsimp only [Budget]
      ring

end TaoTrudgianYang2025.CubicJointCount
