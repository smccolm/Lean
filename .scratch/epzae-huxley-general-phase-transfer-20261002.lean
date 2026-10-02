import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.BourgainOptimizedTransfer

open scoped BigOperators FourierTransform Classical ContDiff NNReal
open Set Filter TaoTrudgianYang2025

namespace HuxleyGeneralPhaseScratch

open TaoTrudgianYang2025.HuxleyRationalPhase

private theorem physical_reference_reciprocal_bound
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hlow : 0 < (N/Q)^((2:ℝ)/3)/(2*B) := by positivity
  refine ⟨hlow.trans_le hU,?_⟩
  calc
    _ ≤ 1/((N/Q)^((2:ℝ)/3)/(2*B)) :=
      one_div_le_one_div_of_le hlow hU
    _ = _ := by
      rw [Real.div_rpow hN.le hQ.le,Real.div_rpow hQ.le hN.le]
      field_simp

private theorem selected_band_prefactor_identity
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 := by
  field_simp

private theorem selected_band_mesh_cardinality_prefactor_bound
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) := by
  have hT : 0 < T := hN.trans_le hNT
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hmesh
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hR)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) hCm.le
  have hKpow : K^((12:ℝ)+ε) ≤
      (Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε := by
    calc
      _ = K^12*K^ε := by norm_num [Real.rpow_add hK]
      _ ≤ (Cmesh*Q*N/R^2)^12*(Cmesh*T)^ε := by gcongr
      _ = _ := by rw [Real.mul_rpow hCm.le hT.le]; ring
  have hPbound : 2*P ≤ (2*Ccard)*Y*M*R^2/(N*Q^2)*L := by
    calc
      _ ≤ 2*(Ccard*Y*M*R^2/(N*Q^2)*L) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (R^2/Q)^6*((Cmesh*Q*N/R^2)^12*Cmesh^ε*T^ε)*
        ((2*Ccard)*Y*M*R^2/(N*Q^2)*L)^10 := by gcongr
    _ = (Cmesh^ε*T^ε*L^10)*
        ((R^2/Q)^6*(Cmesh*Q*N/R^2)^12*((2*Ccard)*Y*M*R^2/(N*Q^2))^10) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [selected_band_prefactor_identity hR.ne' hQ.ne' hN.ne']
      ring

private theorem physical_denominator_rpow_decay
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hh := Real.rpow_le_rpow_of_nonpos hR hRQ (sub_nonpos.mpr hs)
  rw [Real.rpow_sub_natCast hQ.ne',Real.rpow_sub_natCast hR.ne'] at hh
  calc
    _ = (Q^s/Q^p)/N^s := by
      rw [Real.div_rpow hQ.le hN.le]
      ring
    _ ≤ (R^s/R^p)/N^s :=
      div_le_div_of_nonneg_right hh (Real.rpow_nonneg hN.le _)
    _ = _ := by
      rw [Real.div_rpow hR.le hN.le]
      ring

private theorem upper_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Cupper Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cupper*M^2/(N^4*U))) ≤
      Cv*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  obtain ⟨hU,hUinv⟩ := physical_reference_reciprocal_bound hN hQ hB hUlower
  have hcost : Cupper*M^2/(N^4*U) ≤
      (Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)) := by
    calc
      _ = (Cupper*M^2/N^4)*(1/U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUinv (by positivity)
  have hQpow := pow_le_pow_left₀ hR.le hRQ 14
  have hI0 : R^12/Q^14 ≤ 1/R^2 := by
    calc
      _ ≤ R^12/R^14 := div_le_div_of_nonneg_left (by positivity) (by positivity) hQpow
      _ = _ := by field_simp
  have hI1 : R^14/Q^14 ≤ 1 := (div_le_one (by positivity)).mpr hQpow
  have hII : R^12*(Q/N)^((2:ℝ)/3)/Q^14 ≤ (R/N)^((2:ℝ)/3)/R^2 := by
    calc
      _ = R^12*((Q/N)^((2:ℝ)/3)/Q^14) := by ring
      _ ≤ R^12*((R/N)^((2:ℝ)/3)/R^14) :=
        mul_le_mul_of_nonneg_left
          (physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num)) (by positivity)
      _ = _ := by field_simp
  let A₀ := Cv*D*Y^11*M^11/N
  let A₁ := Cv*D*Cdelta*Y^11*Jsep*M^11/N^3
  let A₂ := Cv*2*B*Cupper*Y^12*M^12/N^4
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  calc
    _ ≤ (Y^10*M^10*N^2*R^8/Q^14)*
        ((Cv*R^4/N^2)*D*Y*(M/N)*(1+(Cdelta*R^2/N^2)*Jsep)+
          Y^2*(Cv*R^4/N^2)*((Cupper*M^2/N^4)*(2*B*(Q/N)^((2:ℝ)/3)))) := by
      gcongr
    _ = A₀*(R^12/Q^14)+A₁*(R^14/Q^14)+A₂*(R^12*(Q/N)^((2:ℝ)/3)/Q^14) := by
      dsimp only [A₀,A₁,A₂]
      field_simp
    _ ≤ A₀*(1/R^2)+A₁*1+A₂*((R/N)^((2:ℝ)/3)/R^2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hI0 hA₀)
        (mul_le_mul_of_nonneg_left hI1 hA₁)) (mul_le_mul_of_nonneg_left hII hA₂)
    _ = _ := by
      dsimp only [A₀,A₁,A₂]
      ring

private theorem lower_physical_family_monomial_bound
    {Y M N R Q U V Jsep D Cdelta Clower Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCl : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Clower*R^4/(N^2*U))) ≤
      Cv*(D*(Y^11*M^13/(N^3*R^6))+
        D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
        2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  let Cv' := Cv*M^2/(N^2*R^4)
  let Cu' := Clower*R^4*N^2/M^2
  have hCv' : 0 ≤ Cv' := by dsimp only [Cv']; positivity
  have hCu' : 0 ≤ Cu' := by dsimp only [Cu']; positivity
  have hVupper : V ≤ Cv'*R^4/N^2 := by
    convert hVlower using 1
    dsimp only [Cv']
    field_simp
  have hh := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu' hCv' hB hd hVupper hdelta hUlower
  calc
    _ = (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cu'*M^2/(N^4*U))) := by
      dsimp only [Cu']
      field_simp
    _ ≤ Cv'*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cu'*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := hh
    _ = _ := by
      dsimp only [Cv',Cu']
      field_simp

private theorem physical_large_pair_monomial_bound
    {Y M N R Q C : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hC : 0 ≤ C) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (Y^2*(C*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      C*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hmono := physical_denominator_rpow_decay 14 hR hRQ hN (by norm_num : (2:ℝ)/3 ≤ 14)
  calc
    _ = (C*Y^12*M^12*R^12/N^4)*((Q/N)^((2:ℝ)/3)/Q^14) := by field_simp
    _ ≤ (C*Y^12*M^12*R^12/N^4)*((R/N)^((2:ℝ)/3)/R^14) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by field_simp

private theorem general_physical_family_monomial_bound
    {Y M N R Q U Jsep D Cdelta Cupper Clower Clarge B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCl : 0 ≤ Clower) (hCb : 0 ≤ Clarge)
    (hB : 1 ≤ B) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    let V := U^((3:ℝ)/2)
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+
          Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      D*(Y^11*M^11*N^2/R^7)+
        D*Cdelta*(Y^11*Jsep*M^11/R^5)+
        2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  intro V
  have hQ : 0 < Q := hR.trans_le hRQ
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hU := (physical_reference_reciprocal_bound hN hQ hBp hUlower).1
  have hUbound : U ≤ (N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) :=
        Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_left hN.le hR hRQ) (by norm_num)
  have hVbound : V ≤ N/R := by
    have hh := Real.rpow_le_rpow hU.le hUbound (by norm_num : (0:ℝ) ≤ 3/2)
    have he : ((N/R)^((2:ℝ)/3))^((3:ℝ)/2)=N/R := by
      rw [←Real.rpow_mul (div_pos hN hR).le]
      norm_num
    exact hh.trans_eq he
  let Cvu := N^3/R^5
  let Cvl := N^5/(M^2*R)
  have hCvu : 0 ≤ Cvu := by dsimp only [Cvu]; positivity
  have hCvl : 0 ≤ Cvl := by dsimp only [Cvl]; positivity
  have hVu : V ≤ Cvu*R^4/N^2 := by
    convert hVbound using 1
    dsimp only [Cvu]
    field_simp
  have hVl : V ≤ Cvl*M^2/N^4 := by
    convert hVbound using 1
    dsimp only [Cvl]
    field_simp
  have hu := upper_physical_family_monomial_bound hY hM.le hN hR hRQ
    hJ hD hCd hCu hCvu hBp hd hVu hdelta hUlower
  have hl := lower_physical_family_monomial_bound hY hM hN hR hRQ
    hJ (show (0:ℝ) ≤ 0 by rfl) hCd hCl hCvl hBp hd hVl hdelta hUlower
  have hb := physical_large_pair_monomial_bound (Y:=Y) (M:=M) hN hR hRQ hCb
  convert add_le_add (add_le_add hu hl) hb using 1
  · ring
  · dsimp only [Cvu,Cvl]
    field_simp
    ring


private theorem general_selected_grid_family_bound
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (D*(Y^11*M^11*N^2/R^7)+D*Cdelta*(Y^11*Jsep*M^11/R^5)+
          2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
          2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
          Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  intro V
  have hQ := hR.trans_le hRQ
  have hBp := zero_lt_one.trans_le hB
  have hU := (physical_reference_reciprocal_bound hN hQ hBp hUlower).1
  have hV : 0≤V := Real.rpow_nonneg hU.le _
  have hTp := zero_lt_one.trans_le hT
  have hTpow : 1≤T^ε := Real.one_le_rpow hT hε
  let TypeI := V*D*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
    Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTypeI : 0≤TypeI := by dsimp only [TypeI]; positivity
  have hPair : 0≤Pair := by dsimp only [Pair]; positivity
  have hCpref : 0≤Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0≤Physical := by dsimp only [Physical]; positivity
  have hmass : V*D*Z*(M/N)*(1+delta*Jsep)+
      Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
        Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε ≤ (TypeI+Pair)*T^ε := by
    calc
      _ ≤ TypeI+Pair*T^ε := by dsimp only [TypeI,Pair]; gcongr
      _ ≤ TypeI*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTypeI hTpow) le_rfl
      _ = _ := (add_mul _ _ _).symm
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have hmonomial := general_physical_family_monomial_bound
    hY hM hN hR hRQ hJ hD hCd hCu hCl hCb hB hd hdelta hUupper hUlower
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    apply congrArg (fun x : ℝ => T^x)
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((TypeI+Pair)*T^ε) :=
      mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(TypeI+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(TypeI+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmonomial (by positivity)

private theorem general_selected_grid_family_total_bound
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hCo : 0≤Couter)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*(7/6:ℝ)*
        (D+D*Cdelta+2*B*(Cupper+Clower+Clarge)))*T^(2*ε)*L^10*
        (Y^11*M^11*N^2/R^7+Y^11*Jsep*M^11/R^5+
          Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
          Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  intro V
  let m₁ := Y^11*M^11*N^2/R^7
  let m₂ := Y^11*Jsep*M^11/R^5
  let m₃ := Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)
  let m₄ := Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)
  let m₅ := Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  let Cmass := D+D*Cdelta+2*B*(Cupper+Clower+Clarge)
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  have hBp := zero_lt_one.trans_le hB
  have hm₁ : 0 ≤ m₁ := by dsimp only [m₁]; positivity
  have hm₂ : 0 ≤ m₂ := by dsimp only [m₂]; positivity
  have hm₃ : 0 ≤ m₃ := by dsimp only [m₃]; positivity
  have hm₄ : 0 ≤ m₄ := by dsimp only [m₄]; positivity
  have hm₅ : 0 ≤ m₅ := by dsimp only [m₅]; positivity
  have hDc := mul_nonneg hD hCd
  have hUc : 0≤2*B*Cupper := by positivity
  have hLc : 0≤2*B*Clower := by positivity
  have hBc : 0≤2*B*Clarge := by positivity
  have hBig : Clarge≤2*B*Clarge :=
    le_mul_of_one_le_left hCb (by linarith only [hB])
  have hDmass : D≤Cmass := by dsimp only [Cmass]; nlinarith only [hDc,hUc,hLc,hBc]
  have hDcmass : D*Cdelta≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hUc,hLc,hBc]
  have hUcmass : 2*B*Cupper≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hDc,hLc,hBc]
  have hLcmass : 2*B*Clower≤Cmass := by dsimp only [Cmass]; nlinarith only [hD,hDc,hUc,hBc]
  have hBcmass : Clarge≤Cmass := by
    apply hBig.trans
    dsimp only [Cmass]
    nlinarith only [hD,hDc,hUc,hLc]
  have hWeighted : D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃+2*B*Clower*m₄+Clarge*m₅ ≤
      Cmass*(m₁+m₂+m₃+m₄+m₅) := by
    calc
      _ ≤ Cmass*m₁+Cmass*m₂+Cmass*m₃+Cmass*m₄+Cmass*m₅ :=
        add_le_add (add_le_add (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right hDmass hm₁)
            (mul_le_mul_of_nonneg_right hDcmass hm₂))
          (mul_le_mul_of_nonneg_right hUcmass hm₃))
          (mul_le_mul_of_nonneg_right hLcmass hm₄))
          (mul_le_mul_of_nonneg_right hBcmass hm₅)
      _ = _ := by ring
  have hCpref : 0≤Cpref := by dsimp only [Cpref]; positivity
  have hCmass : 0≤Cmass := hD.trans hDmass
  have hCmassScale : Cmass≤(7/6:ℝ)*Cmass :=
    le_mul_of_one_le_left hCmass (by norm_num)
  have hSum : 0 ≤ m₁+m₂+m₃+m₄+m₅ :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg hm₁ hm₂) hm₃) hm₄) hm₅
  have hWeighted' := hWeighted.trans (mul_le_mul_of_nonneg_right hCmassScale hSum)
  have hraw := general_selected_grid_family_bound
    hY hZ hZY hP hM hN hR hRQ hK hJ hD hCd hCu hCl hCb hB hd hCm hT hε
    hQN hNR hNT hmesh hcard hdelta hUupper hUlower
  have hpref : 0≤Cpref*T^(2*ε)*L^10 :=
    mul_nonneg (mul_nonneg hCpref (Real.rpow_nonneg (zero_le_one.trans hT) _)) (by positivity)
  calc
    _ = Couter*((R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
        (V*D*Z*(M/N)*(1+delta*Jsep)+
          Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε)) := by simp only [mul_assoc]
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*
        (D*m₁+D*Cdelta*m₂+2*B*Cupper*m₃+2*B*Clower*m₄+Clarge*m₅)) :=
      mul_le_mul_of_nonneg_left hraw hCo
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*((7/6:ℝ)*Cmass*(m₁+m₂+m₃+m₄+m₅))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeighted' hpref) hCo
    _ = _ := by
      change Couter*(Cpref*T^(2*ε)*L^10*((7/6:ℝ)*Cmass*(m₁+m₂+m₃+m₄+m₅))) =
        (Couter*Cpref*(7/6:ℝ)*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃+m₄+m₅)
      ac_rfl

example
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    0 < U ∧ 1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.physical_reference_reciprocal_bound (N:=N) (Q:=Q) (B:=B) (U:=U) hN hQ hB hU

example
    {R Q N M Cmesh Ccard Y : ℝ}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hN : N ≠ 0) :
    (R^2/Q)^6*(Cmesh*Q*N/R^2)^12*(Ccard*Y*M*R^2/(N*Q^2))^10 =
      Cmesh^12*Ccard^10*Y^10*M^10*N^2*R^8/Q^14 :=
  HuxleyGeneralPhaseScratch.selected_band_prefactor_identity (R:=R) (Q:=Q) (N:=N) (M:=M) (Cmesh:=Cmesh) (Ccard:=Ccard) (Y:=Y) hR hQ hN

example
    {Y M N R Q K P Cmesh Ccard L T ε : ℝ}
    (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hK : 0 < K) (hP : 0 ≤ P)
    (hCm : 0 < Cmesh) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10 ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^ε*L^10*
        (Y^10*M^10*N^2*R^8/Q^14) :=
  HuxleyGeneralPhaseScratch.selected_band_mesh_cardinality_prefactor_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (P:=P) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard

example
    {R Q N s : ℝ} (p : ℕ)
    (hR : 0 < R) (hRQ : R ≤ Q) (hN : 0 < N) (hs : s ≤ p) :
    (Q/N)^s/Q^p ≤ (R/N)^s/R^p :=
  HuxleyGeneralPhaseScratch.physical_denominator_rpow_decay (R:=R) (Q:=Q) (N:=N) (s:=s) p hR hRQ hN hs

example
    {Y M N R Q U V Jsep D Cdelta Cupper Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVupper : V ≤ Cv*R^4/N^2) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Cupper*M^2/(N^4*U))) ≤
      Cv*(D*(Y^11*M^11/(N*R^2))+
        D*Cdelta*(Y^11*Jsep*M^11/N^3)+
        2*B*Cupper*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyGeneralPhaseScratch.upper_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Cv:=Cv) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCu hCv hB hd hVupper hdelta hUlower

example
    {Y M N R Q U V Jsep D Cdelta Clower Cv B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCl : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+Y^2*V*(Clower*R^4/(N^2*U))) ≤
      Cv*(D*(Y^11*M^13/(N^3*R^6))+
        D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
        2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyGeneralPhaseScratch.lower_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Clower:=Clower) (Cv:=Cv) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCl hCv hB hd hVlower hdelta hUlower

example
    {Y M N R Q C : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hC : 0 ≤ C) :
    (Y^10*M^10*N^2*R^8/Q^14)*
        (Y^2*(C*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      C*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.physical_large_pair_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (C:=C) hN hR hRQ hC

example
    {Y M N R Q U Jsep D Cdelta Cupper Clower Clarge B delta : ℝ}
    (hY : 0 ≤ Y) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q)
    (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Cupper) (hCl : 0 ≤ Clower) (hCb : 0 ≤ Clarge)
    (hB : 1 ≤ B) (hd : 0 ≤ delta)
    (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    let V := U^((3:ℝ)/2)
    (Y^10*M^10*N^2*R^8/Q^14)*
        (V*D*Y*(M/N)*(1+delta*Jsep)+
          Y^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
            Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))) ≤
      D*(Y^11*M^11*N^2/R^7)+
        D*Cdelta*(Y^11*Jsep*M^11/R^5)+
        2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.general_physical_family_monomial_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Clower:=Clower) (Clarge:=Clarge) (B:=B) (delta:=delta) hY hM hN hR hRQ hJ hD hCd hCu hCl hCb hB hd hdelta hUupper hUlower

example
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*
        (D*(Y^11*M^11*N^2/R^7)+D*Cdelta*(Y^11*Jsep*M^11/R^5)+
          2*B*Cupper*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
          2*B*Clower*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
          Clarge*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyGeneralPhaseScratch.general_selected_grid_family_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Clower:=Clower) (Clarge:=Clarge) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hY hZ hZY hP hM hN hR hRQ hK hJ hD hCd hCu hCl hCb hB hd hCm hT hε hQN hNR hNT hmesh hcard hdelta hUupper hUlower

example
    {Y Z P M N R Q U K Jsep D Cdelta Cupper Clower Clarge B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0≤Y) (hZ : 0≤Z) (hZY : Z≤Y) (hP : 0≤P)
    (hM : 0<M) (hN : 0<N) (hR : 0<R) (hRQ : R≤Q) (hK : 0<K)
    (hJ : 0≤Jsep) (hD : 0≤D) (hCd : 0≤Cdelta)
    (hCu : 0≤Cupper) (hCl : 0≤Clower) (hCb : 0≤Clarge)
    (hB : 1≤B) (hd : 0≤delta) (hCm : 0<Cmesh) (hT : 1≤T) (hε : 0≤ε)
    (hCo : 0≤Couter)
    (hQN : Q≤N) (hNR : N≤R^2) (hNT : N≤T)
    (hmesh : K≤Cmesh*Q*N/R^2)
    (hcard : P≤Ccard*Y*M*R^2/(N*Q^2)*L)
    (hdelta : delta≤Cdelta*R^2/N^2)
    (hUupper : U≤(N/Q)^((2:ℝ)/3)/B)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B)≤U) :
    let V := U^((3:ℝ)/2)
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+
        Z^2*(V*(Cupper*M^2/(N^4*U)+Clower*R^4/(N^2*U))+
          Clarge*M^2*R^4/N^6*(Q/N)^((2:ℝ)/3))*T^ε) ≤
      (Couter*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*(7/6:ℝ)*
        (D+D*Cdelta+2*B*(Cupper+Clower+Clarge)))*T^(2*ε)*L^10*
        (Y^11*M^11*N^2/R^7+Y^11*Jsep*M^11/R^5+
          Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
          Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.general_selected_grid_family_total_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Cupper:=Cupper) (Clower:=Clower) (Clarge:=Clarge) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) (Couter:=Couter) hY hZ hZY hP hM hN hR hRQ hK hJ hD hCd hCu hCl hCb hB hd hCm hT hε hCo hQN hNR hNT hmesh hcard hdelta hUupper hUlower


#print axioms HuxleyGeneralPhaseScratch.physical_reference_reciprocal_bound
#print axioms HuxleyGeneralPhaseScratch.selected_band_prefactor_identity
#print axioms HuxleyGeneralPhaseScratch.selected_band_mesh_cardinality_prefactor_bound
#print axioms HuxleyGeneralPhaseScratch.physical_denominator_rpow_decay
#print axioms HuxleyGeneralPhaseScratch.upper_physical_family_monomial_bound
#print axioms HuxleyGeneralPhaseScratch.lower_physical_family_monomial_bound
#print axioms HuxleyGeneralPhaseScratch.physical_large_pair_monomial_bound
#print axioms HuxleyGeneralPhaseScratch.general_physical_family_monomial_bound
#print axioms HuxleyGeneralPhaseScratch.general_selected_grid_family_bound
#print axioms HuxleyGeneralPhaseScratch.general_selected_grid_family_total_bound

private theorem comparable_radius_powers
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) := by
  have hD0 : 0≤D := zero_le_one.trans hD
  have hDs : D^((2:ℝ)/3)≤D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (2:ℝ)/3≤1)
  have hpow {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (hxy : x≤D*y) :
      x^((2:ℝ)/3)≤D*y^((2:ℝ)/3) := by
    calc
      _ ≤ (D*y)^((2:ℝ)/3) := Real.rpow_le_rpow hx hxy (by norm_num)
      _ = D^((2:ℝ)/3)*y^((2:ℝ)/3) := Real.mul_rpow hD0 hy
      _ ≤ _ := mul_le_mul_of_nonneg_right hDs (Real.rpow_nonneg hy _)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_pow] using pow_le_pow_left₀ hS.le hSR 2
  · apply (div_le_div_iff₀ (sq_pos_of_pos hS) (sq_pos_of_pos hR)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS 2
  · apply hpow (div_nonneg hN.le hS.le) (div_nonneg hN.le hR.le)
    calc
      _ ≤ (D*N)/R := (div_le_div_iff₀ hS hR).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hRS hN.le])
      _ = _ := by ring
  · apply hpow (div_nonneg hS.le hN.le) (div_nonneg hR.le hN.le)
    calc
      _ ≤ (D*R)/N := div_le_div_of_nonneg_right hSR hN.le
      _ = _ := by ring


private theorem general_radius_main_bound
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11*N^2/S^7+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^12/(N*S^7)*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^10*N/S^3*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^8*(Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hInv (j : ℕ) : 1/S^j≤D^j/R^j := by
    apply (div_le_div_iff₀ (pow_pos hS j) (pow_pos hR j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS j
  have hi₇ := hInv 7
  have hi₅ := hInv 5
  have hi₃ := hInv 3
  have hi₂ := hInv 2
  have hFor := (comparable_radius_powers hN hR hS hD hSR hRS).2.2.2
  have hD78 : D^7≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD58 : D^5≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD48 : D^4≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have hD38 : D^3≤D^8 := pow_le_pow_right₀ hD (by norm_num)
  have h₁ : Ysmall^11*M^11*N^2/S^7≤D^8*(Y^11*M^11*N^2/R^7) := by
    calc
      _ = (Ysmall^11*M^11*N^2)*(1/S^7) := by ring
      _ ≤ (Y^11*M^11*N^2)*(D^7/R^7) := by gcongr
      _ = D^7*(Y^11*M^11*N^2/R^7) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD78 (by positivity)
  have h₂ : Ysmall^11*J*M^11/S^5≤D^8*(Y^11*J*M^11/R^5) := by
    calc
      _ = (Ysmall^11*J*M^11)*(1/S^5) := by ring
      _ ≤ (Y^11*J*M^11)*(D^5/R^5) := by gcongr
      _ = D^5*(Y^11*J*M^11/R^5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD58 (by positivity)
  have h₃ : Ysmall^12*M^12/(N*S^7)*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N)*(1/S^7)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N)*(D^7/R^7)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = _ := by ring
  have h₄ : Ysmall^12*M^10*N/S^3*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^10*N)*(1/S^3)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^10*N)*(D^3/R^3)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^4*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD48 (by positivity)
  have h₅ : Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3)≤
      D^8*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N^4)*(1/S^2)*(S/N)^((2:ℝ)/3) := by ring
      _ ≤ (Y^12*M^12/N^4)*(D^2/R^2)*(D*(R/N)^((2:ℝ)/3)) := by gcongr
      _ = D^3*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD38 (by positivity)
  calc
    _ ≤ D^8*(Y^11*M^11*N^2/R^7)+D^8*(Y^11*J*M^11/R^5)+
        D^8*(Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))+
        D^8*(Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))+
        D^8*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
      add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅
    _ = _ := by ring


example
    {N R S D : ℝ} (hN : 0<N) (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    S^2≤D^2*R^2 ∧ 1/S^2≤D^2/R^2 ∧
      (N/S)^((2:ℝ)/3)≤D*(N/R)^((2:ℝ)/3) ∧
      (S/N)^((2:ℝ)/3)≤D*(R/N)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.comparable_radius_powers (N:=N) (R:=R) (S:=S) (D:=D) hN hR hS hD hSR hRS

example
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hJ : 0≤J)
    (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall^11*M^11*N^2/S^7+Ysmall^11*J*M^11/S^5+
      Ysmall^12*M^12/(N*S^7)*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^10*N/S^3*(S/N)^((2:ℝ)/3)+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^8*(Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.general_radius_main_bound (Ysmall:=Ysmall) (Y:=Y) (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) (J:=J) hYsmall hY hM hN hR hS hD hJ hSR hRS


#print axioms HuxleyGeneralPhaseScratch.comparable_radius_powers
#print axioms HuxleyGeneralPhaseScratch.general_radius_main_bound

private theorem physical_band_logarithmic_bounds
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlinear (C z : ℝ) (hC : 0 ≤ C) (hz : 0 ≤ z) (hzT : z ≤ C*T) :
      2+Real.log (z+1) ≤ (3+Real.log (C+1))*(1+Real.log T) := by
    have hCp : 0 < C+1 := by linarith only [hC]
    have hbound : z+1 ≤ (C+1)*T := by nlinarith only [hzT,hT]
    have hh := Real.log_le_log (by linarith only [hz] : 0 < z+1) hbound
    rw [Real.log_mul hCp.ne' hTp.ne'] at hh
    have hlogC : 0 ≤ Real.log (C+1) := Real.log_nonneg (by linarith only [hC])
    nlinarith only [hh,hlogC,hlogT,mul_nonneg hlogC hlogT]
  have hRT : R ≤ T := hRQ.trans (hQN.trans hNT)
  have hRquot : R^2/Q ≤ R := (div_le_iff₀ hQ).mpr (by
    nlinarith only [mul_le_mul_of_nonneg_left hRQ hRp.le])
  have harg : Carg*R^2/Q ≤ Carg*T := by
    calc
      _ = Carg*(R^2/Q) := by ring
      _ ≤ Carg*T := mul_le_mul_of_nonneg_left (hRquot.trans hRT) hCarg
  have hKT : K ≤ Cmesh*T := by
    calc
      _ ≤ Cmesh*Q*N/R^2 := hKupper
      _ ≤ Cmesh*Q := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
        (mul_le_mul_of_nonneg_left hNR (by positivity))
      _ ≤ Cmesh*T := mul_le_mul_of_nonneg_left (hQN.trans hNT) (by positivity)
  refine ⟨hlinear Carg _ hCarg (by positivity) harg,?_,?_⟩
  · have hh := hlinear Cmesh K (by positivity) hK.le hKT
    have hlogK := Real.log_le_log hK (by linarith : K ≤ K+1)
    linarith only [hh,hlogK]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogN := Real.log_le_log hN hNT
    have hq := div_le_div_of_nonneg_right hlogN hlog2.le
    have hh := hkmax.trans hq
    have he : (2+1/Real.log 2)*(1+Real.log T) =
        2+Real.log T/Real.log 2+2*Real.log T+1/Real.log 2 := by ring
    rw [he]
    nlinarith only [hh,hlogT,one_div_pos.mpr hlog2]

private theorem physical_mesh_type_spacing_bound
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 := by
  have hprod : (α/(N*R^2))*Q^3*K ≤ α*Cmesh*(Q^2/R^2)^2 := by
    calc
      _ ≤ (α/(N*R^2))*Q^3*(Cmesh*Q*N/R^2) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by field_simp
  have hroot :
      Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K ≤
        Real.sqrt (α*Cmesh)*(Q^2/R^2) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ (α/(N*R^2))*Q^3)]
    calc
      _ ≤ Real.sqrt (α*Cmesh*(Q^2/R^2)^2) := Real.sqrt_le_sqrt hprod
      _ = _ := by
        rw [Real.sqrt_mul (mul_nonneg hα hC),
          Real.sqrt_sq (by positivity : 0 ≤ Q^2/R^2)]
  have hsq := pow_le_pow_left₀ (mul_pos hQ hN).le hmesh 2
  have hquot : Q^2/R^2/K^2 ≤ R^2/N^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hN)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    convert hsq using 1 <;> ring
  calc
    _ ≤ (Real.sqrt (α*Cmesh)*(Q^2/R^2))/K^2 :=
      div_le_div_of_nonneg_right hroot (sq_nonneg K)
    _ = Real.sqrt (α*Cmesh)*(Q^2/R^2/K^2) := by ring
    _ ≤ Real.sqrt (α*Cmesh)*(R^2/N^2) :=
      mul_le_mul_of_nonneg_left hquot (Real.sqrt_nonneg _)
    _ = _ := by ring

private theorem positive_difference_source_type_spacing_bound
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 := by
  intro μ₀ U₀
  have hU : U₀=(J/(2*σ))/(N*R^2) := by
    dsimp only [U₀]
    rw [←hscale]
    field_simp
  have hratio : 16*U₀/μ₀=96*J/c := by
    dsimp only [U₀,μ₀]
    field_simp
    ring
  have hh := physical_mesh_type_spacing_bound
    (show 0 ≤ J/(2*σ) by positivity) hC hN hR hQ hK hmesh hupper
  calc
    _ = (16*J/c)*(Real.sqrt (((J/(2*σ))/(N*R^2))*Q^3)*Real.sqrt K/K^2) := by
      rw [hratio,hU]
      ring
    _ ≤ (16*J/c)*(Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

private theorem selected_band_grid_cardinality_bound
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L := by
  classical
  intro Q hbands hgrids k hk r
  have hQpos (j : ℕ) : (0:ℝ) < Q j := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^j)
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hgrid : ((Grid k r).card:ℝ) ≤
      2*((Chunks.filter (fun p => band p=some k)).card:ℝ) := by
    exact_mod_cast hgrids k hk r
  cases k with
  | zero =>
    have hsub : ((Chunks.filter (fun p => band p=some 0)).card:ℝ) ≤ Chunks.card := by
      exact_mod_cast Finset.card_filter_le (s:=Chunks) (p:=fun p => band p=some 0)
    have hQsq : (Q 0:ℝ)^2 ≤ Cbase^2*R^2 := by
      simpa only [Q,pow_zero,Nat.mul_one,mul_pow] using
        pow_le_pow_left₀ (Nat.cast_nonneg Qbase) hbase 2
    have hcoef : 16*Cbase^2 ≤ (16*Cbase^2+8*Cdensity)*L := by
      calc
        _ ≤ 16*Cbase^2+8*Cdensity := by linarith only [hCd]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some 0)).card:ℝ) := hgrid
      _ ≤ 2*(Y*(8*M/N)) :=
        mul_le_mul_of_nonneg_left (hsub.trans hchunks) (by norm_num)
      _ = (16*Y*M/(N*(Q 0:ℝ)^2))*(Q 0:ℝ)^2 := by
        field_simp [(hQpos 0).ne']
        ring
      _ ≤ (16*Y*M/(N*(Q 0:ℝ)^2))*(Cbase^2*R^2) :=
        mul_le_mul_of_nonneg_left hQsq (by positivity)
      _ = (16*Cbase^2)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) := by ring
      _ ≤ ((16*Cbase^2+8*Cdensity)*L)*(Y*M*R^2/(N*(Q 0:ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  | succ j =>
    have hj : j ≤ kmax := (Nat.le_succ j).trans hk
    have hstep : (Q (j+1):ℝ)=2*(Q j:ℝ) := by
      simp only [Q,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    have hcoef : 8*Cdensity ≤ 16*Cbase^2+8*Cdensity := by
      nlinarith only [sq_nonneg Cbase]
    calc
      _ ≤ 2*((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) := hgrid
      _ ≤ 2*(Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) :=
        mul_le_mul_of_nonneg_left (hbands j hj) (by norm_num)
      _ = (8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L := by
        rw [hstep]
        field_simp
        ring
      _ ≤ (16*Cbase^2+8*Cdensity)*(Y*M*R^2/(N*(Q (j+1):ℝ)^2))*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hLp
      _ = _ := by ring

private theorem selected_terminal_density_bound
    {n N M R Q Y Cdensity Csep L : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hCd : 0 ≤ Cdensity) (hC : 0 < Csep) (hL : 0 ≤ L)
    (hscale : N=8*n) (hQlower : N/Csep ≤ Q) :
    n*Y*(Cdensity*M*R^2/(N*Q^2)*L) ≤
      (Cdensity*Csep^2/8)*(Y*M*R^2/N^2)*L := by
  have hQ : 0 < Q := (div_pos hN hC).trans_le hQlower
  have hn : n=N/8 := by linarith only [hscale]
  calc
    _ = (Cdensity*Y*M*R^2/8)/Q^2*L := by rw [hn]; field_simp
    _ ≤ (Cdensity*Y*M*R^2/8)/(N/Csep)^2*L := by
      apply mul_le_mul_of_nonneg_right _ hL
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (div_pos hN hC).le hQlower 2)
    _ = _ := by field_simp

private theorem positive_difference_completion_error_physical_bound
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hMp : 0 < M := hNp.trans_le hNM
  have hT : 1 ≤ T := hN.trans (hNM.trans hMT)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogN := Real.log_le_log hNp (hNM.trans hMT)
  have hlog : Real.log (6*N) ≤ (1+Real.log 6)*(1+Real.log T) := by
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hNp.ne']
    nlinarith only [hlogN,hlog6,hlogT,mul_nonneg hlog6 hlogT]
  have hlogPos : 0 ≤ Real.log (6*N) := Real.log_nonneg (by linarith only [hN])
  have hL : 1 ≤ 1+Real.log T := by linarith only [hlogT]
  have hratio : 1 ≤ M/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfront : M/N+1 ≤ 2*M/N := by
    calc
      _ ≤ M/N+M/N := add_le_add le_rfl hratio
      _ = _ := by ring
  have hsum : Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N ≤
      (Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T) := by
    have hc := le_mul_of_one_le_right (by positivity : 0 ≤ C*R^2/N) hL
    calc
      _ = Real.sqrt 3*Real.sqrt N*Real.log (6*N)+C*R^2/N := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ Real.sqrt 3*Real.sqrt N*((1+Real.log 6)*(1+Real.log T))+
          (C*R^2/N)*(1+Real.log T) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog (by positivity)) hc
      _ = _ := by ring
  have hcancel : M/N*Real.sqrt N=M/Real.sqrt N := by
    calc
      _ = M*(Real.sqrt N/N) := by ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  let A := 2*Real.sqrt 3*(1+Real.log 6)
  let E₁ := Y*M/Real.sqrt N
  let E₂ := Y*M*R^2/N^2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  calc
    _ ≤ Y*(2*M/N)*
        ((Real.sqrt 3*Real.sqrt N*(1+Real.log 6)+C*R^2/N)*(1+Real.log T)) := by
      gcongr
    _ = (A*(Y*(M/N*Real.sqrt N))+2*C*E₂)*(1+Real.log T) := by
      dsimp only [A,E₂]
      ring
    _ = (A*E₁+2*C*E₂)*(1+Real.log T) := by
      rw [hcancel]
      dsimp only [E₁]
      ring
    _ ≤ ((A+2*C)*(E₁+E₂))*(1+Real.log T) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith only [hlogT])
      nlinarith only [mul_nonneg hA hE₂,mul_nonneg hC hE₁]
    _ = _ := rfl

private theorem positive_difference_endpoint_error_physical_bound
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hQ : 0 < Q := hR.trans_le hRQ
  let X := (N/R)^((2:ℝ)/3)
  let A := 112/κ+28*σ/c
  let E := 2/(Cphys+2)+25/4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hn : n=N/8 := by linarith only [hscale]
  have hUX : U ≤ X := by
    calc
      _ ≤ (N/Q)^((2:ℝ)/3)/B := hUupper
      _ ≤ (N/Q)^((2:ℝ)/3) := div_le_self (by positivity) hB
      _ ≤ (N/R)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hNp.le hR hRQ) (by norm_num)
  have hX : 1 ≤ X := Real.one_le_rpow
    ((le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRQ.trans hQN)) (by norm_num)
  have hNX : N ≤ X*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hNp.le
  have hXN : 1 ≤ X*N := hN.trans hNX
  calc
    _ = Y*(A*(U*N)+E*N+4) := by
      dsimp only [A,E]
      rw [hn]
      ring
    _ ≤ Y*(A*(X*N)+E*(X*N)+4*(X*N)) := by
      apply mul_le_mul_of_nonneg_left _ hY
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUX hNp.le) hA)
          (mul_le_mul_of_nonneg_left hNX hE))
        (by nlinarith only [hXN])
    _ = _ := by
      dsimp only [A,E,X]
      ring

private theorem eventually_selected_band_logarithmic_absorption
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε := by
  filter_upwards [
    TaoTrudgianYang2025.eventually_const_log_pow_le_rpow (C*2^36) (by positivity) 36
      (show 0 < ε/2 by linarith only [hε]),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with T hsmall hlog hT
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hpoly : C*(1+Real.log T)^36 ≤ T^(ε/2) := by
    calc
      _ ≤ C*(2*Real.log T)^36 := by gcongr; linarith only [hlog]
      _ = (C*2^36)*(Real.log T)^36 := by rw [mul_pow]; ring
      _ ≤ _ := hsmall
  refine ⟨hTp,hlog,?_⟩
  calc
    _ = (C*(1+Real.log T)^36)*T^(ε/2) := by ring
    _ ≤ T^(ε/2)*T^(ε/2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [←Real.rpow_add hTp]; congr 1; ring

private theorem selected_band_finite_power_cleanup
    (kmax : ℕ) (G : ℕ → ℤ → ℝ)
    {S Terminal Endpoint E Main L Tpow Cband Cerror Cgrid : ℝ}
    (hTerminal : 0 ≤ Terminal) (hEndpoint : 0 ≤ Endpoint)
    (hMain : 0 ≤ Main) (hL : 1 ≤ L) (hTpow : 1 ≤ Tpow)
    (hCb : 0 ≤ Cband) (hCg : 0 ≤ Cgrid)
    (hband : (kmax:ℝ)+2 ≤ Cband*L)
    (hterminal : Terminal ≤ Cerror*E*L) (hendpoint : Endpoint ≤ Cerror*E*L)
    (hgrid : ∀ k∈Finset.range (kmax+1), ∀ r∈Finset.Ico (0:ℤ) 8,
      G k r ≤ Cgrid*Tpow*L^22*(E^12+Main))
    (hsource : S ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12)) :
    S ≤ (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)*
        Tpow*L^36*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT0 : 0 ≤ Tpow := zero_le_one.trans hTpow
  have hTotal : 0 ≤ E^12+Main := by positivity
  have hEtotal : E^12 ≤ E^12+Main := by linarith only [hMain]
  have hLpow (m : ℕ) (hm : m ≤ 36) : L^m ≤ L^36 :=
    pow_le_pow_right₀ hL hm
  have herror (m : ℕ) (hm : m ≤ 36) :
      E^12*L^m ≤ Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (E^12+Main)*L^36 := mul_le_mul hEtotal (hLpow m hm) (by positivity) hTotal
      _ ≤ Tpow*((E^12+Main)*L^36) :=
        le_mul_of_one_le_left (by positivity) hTpow
      _ = _ := by ring
  have hsum : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((kmax:ℝ)+1)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
          Cgrid*Tpow*L^22*(E^12+Main) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (hgrid k hk)
      _ = _ := by
        have hcard8 : (Finset.Ico (0:ℤ) 8).card=8 := by decide
        simp only [Finset.sum_const,hcard8,Finset.card_range,nsmul_eq_mul,
          Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        ring
  have hk : (kmax:ℝ)+1 ≤ Cband*L := by linarith only [hband]
  have hsumMajor : (∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      (Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)) := by
    apply hsum.trans
    gcongr
  have hterm :
      ((kmax:ℝ)+2)^11*Terminal^12 ≤
        (Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cband*L)^11*(Cerror*E*L)^12 := by gcongr
      _ = (Cband^11*Cerror^12)*(E^12*L^23) := by ring
      _ ≤ (Cband^11*Cerror^12)*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 23 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hgridCost :
      ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r) ≤
      ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main) := by
    have hkpow : ((kmax:ℝ)+2)^11 ≤ (Cband*L)^11 :=
      pow_le_pow_left₀ (by positivity) hband 11
    have hL34 : L^34 ≤ L^36 := hLpow 34 (by norm_num)
    calc
      _ ≤ ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsumMajor (by positivity)) (by positivity)
      _ ≤ (Cband*L)^11*((4:ℝ)^12*(8:ℝ)^11*
          ((Cband*L)*8*(Cgrid*Tpow*L^22*(E^12+Main)))) :=
        mul_le_mul_of_nonneg_right hkpow (by positivity)
      _ = ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^34*(E^12+Main) := by ring
      _ ≤ _ := by gcongr
  have hend : Endpoint^12 ≤ Cerror^12*Tpow*L^36*(E^12+Main) := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ hEndpoint hendpoint 12
      _ = Cerror^12*(E^12*L^12) := by ring
      _ ≤ Cerror^12*(Tpow*L^36*(E^12+Main)) :=
        mul_le_mul_of_nonneg_left (herror 12 (by norm_num)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2^11*(((kmax:ℝ)+2)^11*
        (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := hsource
    _ = 2^11*(((kmax:ℝ)+2)^11*Terminal^12+
        ((kmax:ℝ)+2)^11*((4:ℝ)^12*(8:ℝ)^11*
          ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12) := by ring
    _ ≤ 2^11*((Cband^11*Cerror^12)*Tpow*L^36*(E^12+Main)+
        ((4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid)*Tpow*L^36*(E^12+Main)+
        Cerror^12*Tpow*L^36*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm hgridCost) hend) (by positivity)
    _ = _ := by ring

private theorem upper_numerical_constants_nonnegative
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768*σsrc/csrc
    let DensityLog := 3+Real.log (Carg+1)
    let Cdensity := 128*CerrorBand*DensityLog
    let Ccard := 16*(1536:ℝ)^2+8*Cdensity
    let CKlog := 3+Real.log (Cmesh+1)
    let Cband := 2+1/Real.log 2
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
    let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
    let Cfamily := Couter*
      (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
    let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
    let Cterminal := Cdensity*Csep^2/8
    let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
    let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
    let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
    let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
    0 ≤ CtailBand ∧
    0 ≤ ClowBand ∧
    0 ≤ CerrorBand ∧
    1 ≤ Cmesh ∧
    0 ≤ Carg ∧
    0 ≤ DensityLog ∧
    0 ≤ Cdensity ∧
    0 ≤ Ccard ∧
    0 ≤ CKlog ∧
    0 ≤ Cband ∧
    0 ≤ Cdelta ∧
    0 ≤ Cmass ∧
    0 ≤ Cfamily ∧
    0 ≤ CE₀ ∧
    0 ≤ Cterminal ∧
    0 ≤ Cendpoint ∧
    0 ≤ Cerror ∧
    Csrc*CE₀ ≤ Cerror ∧
    Cterminal ≤ Cerror ∧
    Cendpoint ≤ Cerror ∧
    0 ≤ Cgrid ∧
    0 ≤ Ctotal := by
  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand Carg DensityLog Cdensity Ccard CKlog Cband Cdelta Cmass Cfamily CE₀ Cterminal Cendpoint Cerror Cgrid Ctotal
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  have hCtailBand : 0 ≤ CtailBand := by dsimp only [CtailBand]; positivity
  have hClowBand : 0 ≤ ClowBand := by dsimp only [ClowBand]; positivity
  have hCerrorBand : 0 ≤ CerrorBand := by dsimp only [CerrorBand]; positivity
  have hCmeshOne : 1 ≤ Cmesh := by
    have hh := le_max_left (1:ℝ) (63*Usrc/(2*σsrc))
    dsimp only [Cmesh]
    linarith only [hh]
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  have hCarg : 0 ≤ Carg := by dsimp only [Carg]; positivity
  have hDensityLog : 0 ≤ DensityLog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Carg+1 by linarith only [hCarg])
    dsimp only [DensityLog]
    linarith only [hh]
  have hCdensity : 0 ≤ Cdensity := by dsimp only [Cdensity]; positivity
  have hCcard : 0 ≤ Ccard := by dsimp only [Ccard]; positivity
  have hCKlog : 0 ≤ CKlog := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ Cmesh+1 by linarith only [hCmeshOne])
    dsimp only [CKlog]
    linarith only [hh]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCband : 0 ≤ Cband := by dsimp only [Cband]; positivity
  have hCdelta : 0 ≤ Cdelta := by dsimp only [Cdelta]; positivity
  have hCmass : 0 ≤ Cmass := by dsimp only [Cmass]; positivity
  have hCfamily : 0 ≤ Cfamily := by dsimp only [Cfamily]; positivity
  have hlogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hCE₀ : 0 ≤ CE₀ := by dsimp only [CE₀]; positivity
  have hCterminal : 0 ≤ Cterminal := by dsimp only [Cterminal]; positivity
  have hCendpoint : 0 ≤ Cendpoint := by dsimp only [Cendpoint]; positivity
  have hCerror : 0 ≤ Cerror := by dsimp only [Cerror]; positivity
  have hErrorCompletion : Csrc*CE₀ ≤ Cerror := by
    dsimp only [Cerror]
    linarith only [hCterminal,hCendpoint]
  have hErrorTerminal : Cterminal ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCendpoint]
  have hErrorEndpoint : Cendpoint ≤ Cerror := by
    dsimp only [Cerror]
    nlinarith only [mul_nonneg hCsrcZero hCE₀,hCterminal]
  have hCgrid : 0 ≤ Cgrid := by dsimp only [Cgrid]; positivity
  have hCtotal : 0 ≤ Ctotal := by dsimp only [Ctotal]; positivity

  exact ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩

private theorem selected_grid_completion_bound
    {a b F E Main L W Cerror Clog Cfamily : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hMain : 0 ≤ Main) (hCf : 0 ≤ Cfamily)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (haBound : a ≤ Cerror*E*L) (hbBound : b ≤ Clog*L)
    (hFBound : F ≤ Cfamily*W*L^10*Main) :
    (2:ℝ)^11*(a^12+b^12*F) ≤
      (2:ℝ)^11*(Cerror^12+Clog^12*Cfamily)*W*L^22*(E^12+Main) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hL12 : L^12 ≤ L^22 := pow_le_pow_right₀ hL (by norm_num)
  have hFirst : a^12 ≤ Cerror^12*W*L^22*E^12 := by
    calc
      _ ≤ (Cerror*E*L)^12 := pow_le_pow_left₀ ha haBound 12
      _ = Cerror^12*E^12*L^12 := by ring
      _ ≤ Cerror^12*E^12*L^22 := mul_le_mul_of_nonneg_left hL12 (by positivity)
      _ ≤ (Cerror^12*E^12*L^22)*W := le_mul_of_one_le_right (by positivity) hW
      _ = _ := by ring
  have hSecond : b^12*F ≤ (Clog^12*Cfamily)*W*L^22*Main := by
    calc
      _ ≤ b^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_left hFBound (by positivity)
      _ ≤ (Clog*L)^12*(Cfamily*W*L^10*Main) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbBound 12) (by positivity)
      _ = _ := by ring
  have hCross : Cerror^12*E^12+(Clog^12*Cfamily)*Main ≤
      (Cerror^12+Clog^12*Cfamily)*(E^12+Main) := by
    nlinarith only [
      mul_nonneg (show 0 ≤ Cerror^12 by positivity) hMain,
      mul_nonneg (show 0 ≤ Clog^12*Cfamily by positivity) (show 0 ≤ E^12 by positivity)]
  calc
    _ ≤ (2:ℝ)^11*(Cerror^12*W*L^22*E^12+(Clog^12*Cfamily)*W*L^22*Main) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) (by positivity)
    _ = ((2:ℝ)^11*W*L^22)*(Cerror^12*E^12+(Clog^12*Cfamily)*Main) := by ring
    _ ≤ ((2:ℝ)^11*W*L^22)*((Cerror^12+Clog^12*Cfamily)*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left hCross (by positivity)
    _ = _ := by ring

private theorem general_expression_nonnegative
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  positivity

private theorem eventually_general_finite_numerical_consequence
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP CLOW CLARGE Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hCLOW : 0 ≤ CLOW) (hCLARGE : 0 ≤ CLARGE)
    (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := fun k : ℕ => (Usel k:ℝ)^((3:ℝ)/2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*
              ((Vscale k)*(CUP*M^2/((N:ℝ)^4*(Usel k:ℝ))+
                CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))+
                CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) := by

  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let Carg := 512*768*σsrc/csrc
  let DensityLog := 3+Real.log (Carg+1)
  let Cdensity := 128*CerrorBand*DensityLog
  let Ccard := 16*(1536:ℝ)^2+8*Cdensity
  let CKlog := 3+Real.log (Cmesh+1)
  let Cband := 2+1/Real.log 2
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
  let Cmass := Dtype+Dtype*Cdelta+2*Bselect*(CUP+CLOW+CLARGE)
  let Cfamily := Couter*
    (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
  let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
  let Cterminal := Cdensity*Csep^2/8
  let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
  let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
  let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
  let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
    (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
  have hConstants :
      0 ≤ CtailBand ∧ 0 ≤ ClowBand ∧ 0 ≤ CerrorBand ∧ 1 ≤ Cmesh ∧
      0 ≤ Carg ∧ 0 ≤ DensityLog ∧ 0 ≤ Cdensity ∧ 0 ≤ Ccard ∧
      0 ≤ CKlog ∧ 0 ≤ Cband ∧ 0 ≤ Cdelta ∧ 0 ≤ Cmass ∧
      0 ≤ Cfamily ∧ 0 ≤ CE₀ ∧ 0 ≤ Cterminal ∧ 0 ≤ Cendpoint ∧
      0 ≤ Cerror ∧ Csrc*CE₀ ≤ Cerror ∧ Cterminal ≤ Cerror ∧
      Cendpoint ≤ Cerror ∧ 0 ≤ Cgrid ∧ 0 ≤ Ctotal :=
    upper_numerical_constants_nonnegative (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero
      hCouter (add_nonneg (add_nonneg hCUP hCLOW) hCLARGE) hDtype hBsOne hCsep
  obtain ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩ :=
    hConstants
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  filter_upwards [eventually_selected_band_logarithmic_absorption hCtotal hε,
    Filter.eventually_ge_atTop (1:ℝ)] with T hAbs hTone
  intro Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover S
    hNlink hNtwo hR hNR' hNsqM hMT hJsep hscale hQbase hBaseHi hEndLo hkmax hKpos
    Q hvalid Yc μ₀ U₀ Vscale Error Δtype Buffer Width FamilyBound Density Endpoint Selected Grid
    hChunks hBands hGridCount hGridImage hNorm ErrorTotal Main
  have hT : 0 < T := hAbs.1
  have hLogOne : 1 ≤ Real.log T := hAbs.2.1
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hM : 0 < M := (sq_pos_of_pos hNp).trans_le hNsqM
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hLogOne]
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main :=
    general_expression_nonnegative hYc hM.le hNp.le hRp hJsep
  have hErrorTotal : 0 ≤ ErrorTotal :=
    add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
          (sq_nonneg (N:ℝ))))
      (mul_nonneg (mul_nonneg hYc hNp.le)
        (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le)
  have hQpos (k : ℕ) : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hKreal (k : ℕ) : (0:ℝ) < Kmesh k := by exact_mod_cast hKpos k
  have hlogs (k : ℕ) (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤ DensityLog*L ∧
      1+Real.log (Kmesh k) ≤ CKlog*L ∧
      (kmax:ℝ)+2 ≤ Cband*L := by
    obtain ⟨hRQ,hQN,_,hKU,_,_⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    exact physical_band_logarithmic_bounds hCarg hCmeshOne hTone hR hRQ
      hQNreal hNR' hNT (hKreal k) hKU hkmax
  have hDensity (k : ℕ) (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    have harg : 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp [(hQpos k).ne']
    calc
      _ = 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (Carg*R^2/(Q k:ℝ)+1)) := by
        dsimp only [Density]
        rw [harg]
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*(DensityLog*L) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hBandCounts (k : ℕ) (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        Yc*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L) :=
    (hBands k hk).trans (mul_le_mul_of_nonneg_left (hDensity k hk) hYc)
  have hGridCard (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      ((Grid k r).card:ℝ) ≤ Ccard*Yc*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase
      hYc hM.le hNp hCdensity hL hBaseHi hChunks hBandCounts
      hGridCount k hk r
  have hGridPhase (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      (((Grid k r).image Prod.fst).card:ℝ) ≤ Yc := by
    change (((Grid k r).image Prod.fst).card:ℝ) ≤ (Y.card:ℝ)
    exact_mod_cast Finset.card_le_card (hGridImage k hk r)
  have hDeltaType (k : ℕ) (hk : k ≤ kmax) :
      Δtype k ≤ Cdelta*R^2/(N:ℝ)^2 := by
    obtain ⟨_,_,hMesh,hKU,_,_⟩ := hvalid k hk
    exact positive_difference_source_type_spacing_bound hσsrc hcsrc hUsrc.le
      hT hM hNp hRp (hQpos k) (hKreal k) hCmesh.le hscale hMesh hKU
  have hFamily (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤ Cfamily*T^(2*εloss)*L^10*Main := by
    obtain ⟨hRQ,hQN,_,hKU,hUupper,hUlower⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    have hdeltazero : 0 ≤ Δtype k := by dsimp only [Δtype,U₀,μ₀]; positivity
    exact general_selected_grid_family_total_bound
      hYc (Nat.cast_nonneg ((Grid k r).image Prod.fst).card) (hGridPhase k hk r)
      (Nat.cast_nonneg (Grid k r).card) hM hNp hRp hRQ (hKreal k)
      hJsep hDtype hCdelta hCUP hCLOW hCLARGE
      hBsOne hdeltazero hCmesh hTone hεloss.le hCouter
      hQNreal hNR' hNT hKU (hGridCard k hk r) (hDeltaType k hk) hUupper hUlower
  let E₁ := Yc*M/Real.sqrt (N:ℝ)
  let E₂ := Yc*M*R^2/(N:ℝ)^2
  let E₃ := Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  have hE₁ : 0 ≤ E₁ := div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _)
  have hE₂ : 0 ≤ E₂ := div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
    (sq_nonneg (N:ℝ))
  have hE₃ : 0 ≤ E₃ := mul_nonneg (mul_nonneg hYc hNp.le)
    (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le
  have hE₁₂Total : E₁+E₂ ≤ ErrorTotal := le_add_of_nonneg_right hE₃
  have hE₂Total : E₂ ≤ ErrorTotal := (le_add_of_nonneg_left hE₁).trans hE₁₂Total
  have hE₃Total : E₃ ≤ ErrorTotal := le_add_of_nonneg_left (add_nonneg hE₁ hE₂)
  have hCompletion : Csrc*Error ≤ Cerror*ErrorTotal*L := by
    have hraw := positive_difference_completion_error_physical_bound
      (R:=R) hYc hNOne hNM hMT (show 0 ≤ 12*σsrc/csrc by positivity)
    have he : Error ≤ CE₀*(E₁+E₂)*L := by
      convert hraw using 1
      · dsimp only [Error]
        ring
      · dsimp only [CE₀,E₁,E₂,L]
        ring
    calc
      _ ≤ Csrc*(CE₀*(E₁+E₂)*L) := mul_le_mul_of_nonneg_left he hCsrcZero
      _ = (Csrc*CE₀)*(E₁+E₂)*L := by simp only [mul_assoc]
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hErrorCompletion hE₁₂Total (add_nonneg hE₁ hE₂) hCerror) hLzero
  have hNlinkReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hTerminalBound : (n:ℝ)*Yc*Density kmax ≤ Cerror*ErrorTotal*L := by
    have hnzero : 0 ≤ (n:ℝ)*Yc := mul_nonneg (Nat.cast_nonneg n) hYc
    have hcore := selected_terminal_density_bound (R:=R) hNp hM.le hYc hCdensity
      (zero_lt_one.trans_le hCsep) hLzero hNlinkReal hEndLo
    calc
      _ ≤ (n:ℝ)*Yc*(Cdensity*M*R^2/((N:ℝ)*(Q kmax:ℝ)^2)*L) :=
        mul_le_mul_of_nonneg_left (hDensity kmax le_rfl) hnzero
      _ ≤ Cterminal*E₂*L := hcore
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hErrorTerminal hE₂Total hE₂ hCerror) hLzero
  have hEndpointBound : Endpoint ≤ Cerror*ErrorTotal*L := by
    obtain ⟨hRQ,hQN,_,_,hUupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQNreal : (Q 0:ℝ) ≤ N := by exact_mod_cast hQN
    have hraw := positive_difference_endpoint_error_physical_bound
      hYc hNOne hRp hRQ hQNreal hκ hσsrc.le hcsrc hCphys hBsOne hNlinkReal hUupper
    have he : Endpoint ≤ Cendpoint*E₃ := by
      exact hraw
    calc
      _ ≤ Cendpoint*E₃ := he
      _ ≤ Cerror*ErrorTotal := mul_le_mul hErrorEndpoint hE₃Total hE₃ hCerror
      _ ≤ Cerror*ErrorTotal*L := le_mul_of_one_le_right (mul_nonneg hCerror hErrorTotal) hL

  have hLogN : 0 ≤ Real.log (6*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hNreal])
  have hCompletionZero : 0 ≤ Csrc*Error :=
    mul_nonneg hCsrcZero
      (mul_nonneg (mul_nonneg hYc (add_nonneg (div_nonneg hM.le hNp.le) zero_le_one))
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLogN)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
            (mul_nonneg hcsrc.le hNp.le))))
  have hDensityZero (k : ℕ) : 0 ≤ Density k := by
    have hh : 0 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768)) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
        (mul_nonneg hcsrc.le (div_nonneg (hQpos k).le (by norm_num)))
    have harg : 1 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1 := le_add_of_nonneg_left hh
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCerrorBand)
        (div_nonneg (mul_nonneg hM.le (sq_nonneg R))
          (mul_nonneg hNp.le (sq_nonneg _))))
      (add_nonneg (by norm_num) (Real.log_nonneg harg))
  have hTerminalZero : 0 ≤ (n:ℝ)*Yc*Density kmax :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hYc) (hDensityZero kmax)
  have hBufferZero : 0 ≤ Buffer 0 :=
    add_nonneg
      (add_nonneg
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hκ.le) hNp.le)
        (div_nonneg hNp.le (add_nonneg hCphys (by norm_num)))) (by norm_num)
  have hWidthZero : 0 ≤ Width 0 :=
    mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hσsrc.le) hcsrc.le)
        (Nat.cast_nonneg _)) hNp.le
  have hEndpointZero : 0 ≤ Endpoint :=
    mul_nonneg hYc
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hBufferZero)
            (mul_nonneg (by norm_num) hWidthZero))
          (mul_nonneg (by norm_num) hNp.le))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  have hTpowOne : 1 ≤ T^(2*εloss) :=
    Real.one_le_rpow hTone (mul_nonneg (by norm_num) hεloss.le)
  let G := fun k r => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))
  have hG (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      G k r ≤ Cgrid*T^(2*εloss)*L^22*(ErrorTotal^12+Main) := by
    have hKone : (1:ℝ) ≤ Kmesh k := by
      have hh : 1 ≤ Kmesh k := Nat.succ_le_iff.mpr (hKpos k)
      exact_mod_cast hh
    have hlogK := Real.log_nonneg hKone
    have hLogZero : 0 ≤ Csrc*(1+Real.log (Kmesh k)) :=
      mul_nonneg hCsrcZero (add_nonneg zero_le_one hlogK)
    have hLogBound : Csrc*(1+Real.log (Kmesh k)) ≤ (Csrc*CKlog)*L := by
      calc
        _ ≤ Csrc*(CKlog*L) := mul_le_mul_of_nonneg_left (hlogs k hk).2.1 hCsrcZero
        _ = _ := by simp only [mul_assoc]
    exact selected_grid_completion_bound hCompletionZero hLogZero hMain hCfamily hL hTpowOne
      hCompletion hLogBound (hFamily k hk r)
  have hClean := selected_band_finite_power_cleanup kmax G
    hTerminalZero hEndpointZero hMain hL hTpowOne hCband hCgrid
    (hlogs 0 (Nat.zero_le _)).2.2 hTerminalBound hEndpointBound
    (fun k hk r _ => hG k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) r) hNorm
  have hExp : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  have hFactor : Ctotal*T^(2*εloss)*L^36 ≤ T^ε := by
    simpa only [hExp,L] using hAbs.2.2
  exact hClean.trans (mul_le_mul_of_nonneg_right hFactor
    (add_nonneg (pow_nonneg hErrorTotal 12) hMain))

example
    {Carg Cmesh T N R Q K kmax : ℝ}
    (hCarg : 0 ≤ Carg) (hCmesh : 1 ≤ Cmesh)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hK : 0 < K) (hKupper : K ≤ Cmesh*Q*N/R^2)
    (hkmax : kmax ≤ Real.log N/Real.log 2) :
    2+Real.log (Carg*R^2/Q+1) ≤ (3+Real.log (Carg+1))*(1+Real.log T) ∧
    1+Real.log K ≤ (3+Real.log (Cmesh+1))*(1+Real.log T) ∧
    kmax+2 ≤ (2+1/Real.log 2)*(1+Real.log T) :=
  HuxleyGeneralPhaseScratch.physical_band_logarithmic_bounds (Carg:=Carg) (Cmesh:=Cmesh) (T:=T) (N:=N) (R:=R) (Q:=Q) (K:=K) (kmax:=kmax) hCarg hCmesh hT hR hRQ hQN hNR hNT hK hKupper hkmax

example
    {α Cmesh N R Q K : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ Cmesh) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K)
    (hmesh : Q*N ≤ K*R^2)
    (hupper : K ≤ Cmesh*Q*N/R^2) :
    Real.sqrt ((α/(N*R^2))*Q^3)*Real.sqrt K/K^2 ≤
      Real.sqrt (α*Cmesh)*R^2/N^2 :=
  HuxleyGeneralPhaseScratch.physical_mesh_type_spacing_bound (α:=α) (Cmesh:=Cmesh) (N:=N) (R:=R) (Q:=Q) (K:=K) hα hC hN hR hQ hK hmesh hupper

example
    {σ c J T M N R Q K Cmesh : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hQ : 0 < Q) (hK : 0 < K) (hC : 0 ≤ Cmesh)
    (hscale : T*N*R^2=M^3)
    (hmesh : Q*N ≤ K*R^2) (hupper : K ≤ Cmesh*Q*N/R^2) :
    let μ₀ := c*T/(12*σ*M^3)
    let U₀ := J*T/(2*σ*M^3)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K/(6*K^2) ≤
      (16*J/c)*Real.sqrt ((J/(2*σ))*Cmesh)*R^2/N^2 :=
  HuxleyGeneralPhaseScratch.positive_difference_source_type_spacing_bound (σ:=σ) (c:=c) (J:=J) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (Cmesh:=Cmesh) hσ hc hJ hT hM hN hR hQ hK hC hscale hmesh hupper

example
    (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
    (Grid : ℕ → ℤ → Finset (ℝ × ℤ)) (Qbase kmax : ℕ)
    {Y M N R Cbase Cdensity L : ℝ}
    (hQbase : 0 < Qbase) (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 < N)
    (hCd : 0 ≤ Cdensity) (hL : 1 ≤ L)
    (hbase : (Qbase:ℝ) ≤ Cbase*R)
    (hchunks : (Chunks.card:ℝ) ≤ Y*(8*M/N)) :
    let Q := fun k : ℕ => Qbase*2^k
    (∀ j ≤ kmax, ((Chunks.filter (fun p => band p=some (j+1))).card:ℝ) ≤
      Y*(Cdensity*M*R^2/(N*(Q j:ℝ)^2)*L)) →
    (∀ k ≤ kmax, ∀ r : ℤ,
      (Grid k r).card ≤ 2*(Chunks.filter (fun p => band p=some k)).card) →
    ∀ k ≤ kmax, ∀ r : ℤ,
      ((Grid k r).card:ℝ) ≤
        (16*Cbase^2+8*Cdensity)*Y*M*R^2/(N*(Q k:ℝ)^2)*L :=
  HuxleyGeneralPhaseScratch.selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax (Y:=Y) (M:=M) (N:=N) (R:=R) (Cbase:=Cbase) (Cdensity:=Cdensity) (L:=L) hQbase hY hM hN hCd hL hbase hchunks

example
    {n N M R Q Y Cdensity Csep L : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hCd : 0 ≤ Cdensity) (hC : 0 < Csep) (hL : 0 ≤ L)
    (hscale : N=8*n) (hQlower : N/Csep ≤ Q) :
    n*Y*(Cdensity*M*R^2/(N*Q^2)*L) ≤
      (Cdensity*Csep^2/8)*(Y*M*R^2/N^2)*L :=
  HuxleyGeneralPhaseScratch.selected_terminal_density_bound (n:=n) (N:=N) (M:=M) (R:=R) (Q:=Q) (Y:=Y) (Cdensity:=Cdensity) (Csep:=Csep) (L:=L) hN hM hY hCd hC hL hscale hQlower

example
    {Y M N R T C : ℝ} (hY : 0 ≤ Y) (hN : 1 ≤ N)
    (hNM : N ≤ M) (hMT : M ≤ T) (hC : 0 ≤ C) :
    Y*(M/N+1)*(Real.sqrt (3*N)*Real.log (6*N)+C*R^2/N) ≤
      (2*Real.sqrt 3*(1+Real.log 6)+2*C)*
        (Y*M/Real.sqrt N+Y*M*R^2/N^2)*(1+Real.log T) :=
  HuxleyGeneralPhaseScratch.positive_difference_completion_error_physical_bound (Y:=Y) (M:=M) (N:=N) (R:=R) (T:=T) (C:=C) hY hN hNM hMT hC

example
    {Y N n R Q U κ σ c Cphys B : ℝ}
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hR : 0 < R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hc : 0 < c) (hCphys : 0 ≤ Cphys)
    (hB : 1 ≤ B) (hscale : N=8*n)
    (hUupper : U ≤ (N/Q)^((2:ℝ)/3)/B) :
    Y*(2*((56*U/κ)*N+N/(Cphys+2)+2)+
        2*((14*σ/c)*U*N)+6*N+2*n) ≤
      (112/κ+28*σ/c+2/(Cphys+2)+41/4)*
        (Y*N*(N/R)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.positive_difference_endpoint_error_physical_bound (Y:=Y) (N:=N) (n:=n) (R:=R) (Q:=Q) (U:=U) (κ:=κ) (σ:=σ) (c:=c) (Cphys:=Cphys) (B:=B) hY hN hR hRQ hQN hκ hσ hc hCphys hB hscale hUupper

example
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 0 < T ∧ 1 ≤ Real.log T ∧
      C*T^(ε/2)*(1+Real.log T)^36 ≤ T^ε :=
  HuxleyGeneralPhaseScratch.eventually_selected_band_logarithmic_absorption (C:=C) (ε:=ε) hC hε

example
    (kmax : ℕ) (G : ℕ → ℤ → ℝ)
    {S Terminal Endpoint E Main L Tpow Cband Cerror Cgrid : ℝ}
    (hTerminal : 0 ≤ Terminal) (hEndpoint : 0 ≤ Endpoint)
    (hMain : 0 ≤ Main) (hL : 1 ≤ L) (hTpow : 1 ≤ Tpow)
    (hCb : 0 ≤ Cband) (hCg : 0 ≤ Cgrid)
    (hband : (kmax:ℝ)+2 ≤ Cband*L)
    (hterminal : Terminal ≤ Cerror*E*L) (hendpoint : Endpoint ≤ Cerror*E*L)
    (hgrid : ∀ k∈Finset.range (kmax+1), ∀ r∈Finset.Ico (0:ℤ) 8,
      G k r ≤ Cgrid*Tpow*L^22*(E^12+Main))
    (hsource : S ≤ 2^11*(((kmax:ℝ)+2)^11*
      (Terminal^12+(4:ℝ)^12*(8:ℝ)^11*
        ∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,G k r)+Endpoint^12)) :
    S ≤ (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)*
        Tpow*L^36*(E^12+Main) :=
  HuxleyGeneralPhaseScratch.selected_band_finite_power_cleanup kmax G (S:=S) (Terminal:=Terminal) (Endpoint:=Endpoint) (E:=E) (Main:=Main) (L:=L) (Tpow:=Tpow) (Cband:=Cband) (Cerror:=Cerror) (Cgrid:=Cgrid) hTerminal hEndpoint hMain hL hTpow hCb hCg hband hterminal hendpoint hgrid hsource

example
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Carg := 512*768*σsrc/csrc
    let DensityLog := 3+Real.log (Carg+1)
    let Cdensity := 128*CerrorBand*DensityLog
    let Ccard := 16*(1536:ℝ)^2+8*Cdensity
    let CKlog := 3+Real.log (Cmesh+1)
    let Cband := 2+1/Real.log 2
    let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
    let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CUP
    let Cfamily := Couter*
      (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
    let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
    let Cterminal := Cdensity*Csep^2/8
    let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
    let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
    let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
    let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
      (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
    0 ≤ CtailBand ∧
    0 ≤ ClowBand ∧
    0 ≤ CerrorBand ∧
    1 ≤ Cmesh ∧
    0 ≤ Carg ∧
    0 ≤ DensityLog ∧
    0 ≤ Cdensity ∧
    0 ≤ Ccard ∧
    0 ≤ CKlog ∧
    0 ≤ Cband ∧
    0 ≤ Cdelta ∧
    0 ≤ Cmass ∧
    0 ≤ Cfamily ∧
    0 ≤ CE₀ ∧
    0 ≤ Cterminal ∧
    0 ≤ Cendpoint ∧
    0 ≤ Cerror ∧
    Csrc*CE₀ ≤ Cerror ∧
    Cterminal ≤ Cerror ∧
    Cendpoint ≤ Cerror ∧
    0 ≤ Cgrid ∧
    0 ≤ Ctotal :=
  HuxleyGeneralPhaseScratch.upper_numerical_constants_nonnegative (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ) (Cphys:=Cphys) (Csrc:=Csrc) (Couter:=Couter) (CUP:=CUP) (Dtype:=Dtype) (Bselect:=Bselect) (Csep:=Csep) (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero hCouter hCUP hDtype hBsOne hCsep

example
    {a b F E Main L W Cerror Clog Cfamily : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hMain : 0 ≤ Main) (hCf : 0 ≤ Cfamily)
    (hL : 1 ≤ L) (hW : 1 ≤ W)
    (haBound : a ≤ Cerror*E*L) (hbBound : b ≤ Clog*L)
    (hFBound : F ≤ Cfamily*W*L^10*Main) :
    (2:ℝ)^11*(a^12+b^12*F) ≤
      (2:ℝ)^11*(Cerror^12+Clog^12*Cfamily)*W*L^22*(E^12+Main) :=
  HuxleyGeneralPhaseScratch.selected_grid_completion_bound (a:=a) (b:=b) (F:=F) (E:=E) (Main:=Main) (L:=L) (W:=W) (Cerror:=Cerror) (Clog:=Clog) (Cfamily:=Cfamily) ha hb hMain hCf hL hW haBound hbBound hFBound

example
    {σsrc csrc Usrc κ Cphys Csrc Couter CUP CLOW CLARGE Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCUP : 0 ≤ CUP) (hCLOW : 0 ≤ CLOW) (hCLARGE : 0 ≤ CLARGE)
    (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Vscale := fun k : ℕ => (Usel k:ℝ)^((3:ℝ)/2)
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*
              ((Vscale k)*(CUP*M^2/((N:ℝ)^4*(Usel k:ℝ))+
                CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))+
                CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.eventually_general_finite_numerical_consequence (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ) (Cphys:=Cphys) (Csrc:=Csrc) (Couter:=Couter) (CUP:=CUP) (CLOW:=CLOW) (CLARGE:=CLARGE) (Dtype:=Dtype) (Bselect:=Bselect) (Csep:=Csep) (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero hCouter hCUP hCLOW hCLARGE hDtype hBsOne hCsep hε


#print axioms HuxleyGeneralPhaseScratch.physical_band_logarithmic_bounds
#print axioms HuxleyGeneralPhaseScratch.physical_mesh_type_spacing_bound
#print axioms HuxleyGeneralPhaseScratch.positive_difference_source_type_spacing_bound
#print axioms HuxleyGeneralPhaseScratch.selected_band_grid_cardinality_bound
#print axioms HuxleyGeneralPhaseScratch.selected_terminal_density_bound
#print axioms HuxleyGeneralPhaseScratch.positive_difference_completion_error_physical_bound
#print axioms HuxleyGeneralPhaseScratch.positive_difference_endpoint_error_physical_bound
#print axioms HuxleyGeneralPhaseScratch.eventually_selected_band_logarithmic_absorption
#print axioms HuxleyGeneralPhaseScratch.selected_band_finite_power_cleanup
#print axioms HuxleyGeneralPhaseScratch.upper_numerical_constants_nonnegative
#print axioms HuxleyGeneralPhaseScratch.selected_grid_completion_bound
#print axioms HuxleyGeneralPhaseScratch.eventually_general_finite_numerical_consequence

example
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.general_expression_nonnegative (Y:=Y) (M:=M) (N:=N) (R:=R) (J:=J) hY hM hN hR hJ


#print axioms HuxleyGeneralPhaseScratch.general_expression_nonnegative

private theorem reference_floor_physical_budgets
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 := by
  intro U
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 0 < Q := hRp.trans_le hRQ
  have hN : 0 < N := hQ.trans_le hQN
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let scale := (N/Q)^((2:ℝ)/3)/B
  have hX2L : 2*L ≤ scale := (le_div_iff₀ hBp).mpr (by nlinarith only [hlarge])
  have hX2 : 2 ≤ scale := by linarith only [hX2L,hL]
  have hU : 1 ≤ U := (Nat.one_le_floor_iff scale).mpr (by linarith only [hX2])
  have hUle : (U:ℝ) ≤ scale := Nat.floor_le (by linarith only [hX2])
  have hUlower : scale/2 ≤ (U:ℝ) := by
    have hh := Nat.lt_floor_add_one scale
    change scale < (U:ℝ)+1 at hh
    linarith only [hh,hX2]
  have hUL : L ≤ (U:ℝ) := by linarith only [hX2L,hUlower]
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hUle 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*scale^3=N^2 := by
      dsimp only [scale]
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hlinear : B*(U:ℝ)*Q ≤ N := by
    have hratio : 1 ≤ N/Q := (one_le_div hQ).mpr hQN
    have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hUle hBp.le
    have he : B*scale=(N/Q)^((2:ℝ)/3) := by dsimp only [scale]; field_simp
    rw [he] at hh
    exact (le_div_iff₀ hQ).mp (hh.trans hp)
  have hnowrap : B^2*(U:ℝ)^3*R^2 ≤ N^2 := by
    have hBpow : B^2 ≤ B^3 := by
      have hh := mul_le_mul_of_nonneg_left hB (sq_nonneg B)
      nlinarith only [hh]
    calc
      _ ≤ B^3*(U:ℝ)^3*Q^2 := by gcongr
      _ ≤ _ := hcube
  have hUN : (U:ℝ) ≤ N := by
    calc
      (U:ℝ) = 1*(U:ℝ)*1 := by ring
      _ ≤ B*(U:ℝ)*Q := by gcongr; exact hR.trans hRQ
      _ ≤ N := hlinear
  refine ⟨hU,hUL,?_,hUle,hnowrap,hUN.trans hNR⟩
  convert hUlower using 1
  dsimp only [scale]
  ring

private theorem dyadic_band_integer_physical_selection
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) := by
  classical
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hCp : 0 < Cbase := by linarith only [hCbase]
  have hCR : 1 ≤ Cbase*R := by nlinarith only [hCbase,hR]
  let Qbase : ℕ := ⌈Cbase*R⌉₊
  have hQlo : Cbase*R ≤ (Qbase:ℝ) := Nat.le_ceil _
  have hQhi : (Qbase:ℝ) ≤ 2*Cbase*R := by
    have hh := Nat.ceil_lt_add_one (mul_pos hCp hRp).le
    change (Qbase:ℝ) < Cbase*R+1 at hh
    linarith only [hh,hCR]
  have hQp : (0:ℝ) < Qbase := (mul_pos hCp hRp).trans_le hQlo
  have hratio : 1 ≤ qcap*(N:ℝ)/(Qbase:ℝ) :=
    (le_div_iff₀ hQp).mpr (by simpa only [one_mul] using hQhi.trans hroom)
  obtain ⟨kmax,hklo,hkhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  let Q := fun k : ℕ => Qbase*2^k
  have hQcast k : (Q k:ℝ)=(Qbase:ℝ)*(2:ℝ)^k := by simp only [Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hQbase k : (Qbase:ℝ) ≤ Q k := by
    rw [hQcast]
    exact le_mul_of_one_le_right hQp.le (one_le_pow₀ (by norm_num))
  have hQpos k : (0:ℝ) < Q k := hQp.trans_le (hQbase k)
  have hQupper : (Q kmax:ℝ) ≤ qcap*(N:ℝ) := by
    rw [hQcast]
    have hh := (le_div_iff₀ hQp).mp hklo
    simpa only [mul_comm] using hh
  have hQlower : qcap*(N:ℝ)/2 ≤ Q kmax := by
    have hh := (div_lt_iff₀ hQp).mp hkhi
    rw [pow_succ] at hh
    rw [hQcast]
    nlinarith only [hh]
  have hQmono k (hk : k ≤ kmax) : Q k ≤ Q kmax := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
  have hQN k (hk : k ≤ kmax) : Q k ≤ N := by
    have hh : (Q k:ℝ) ≤ N :=
      (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans (hQupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le))
    exact_mod_cast hh
  have hstrong k : 768*R ≤ (Q k:ℝ) :=
    (mul_le_mul_of_nonneg_right hCbase hRp.le).trans (hQlo.trans (hQbase k))
  have hRQ k : R ≤ (Q k:ℝ) := by
    have hh := hstrong k
    linarith only [hh,hRp]
  have hminscale k : 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul (hstrong k) hRN hRp.le (hQpos k).le
    nlinarith only [hh,sq_nonneg R]
  have hmesh k := exists_positive_difference_source_fourier_mesh
    (J:=J) hσ hNp hRp (hQpos k) (by
      have hh := hminscale k
      linarith only [hh,sq_nonneg R])
  choose Kmesh hK hSource hMesh hMeshUpper using hmesh
  let Usel := fun k => ⌊((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B⌋₊
  have hUdata k (hk : k ≤ kmax) :=
    reference_floor_physical_budgets (N:=(N:ℝ)) (B:=B) (L:=L)
      hR (hRQ k) (by exact_mod_cast hQN k hk) hNR hB hL (by
        have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
          (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
        have hratioLower : 1/qcap ≤ (N:ℝ)/(Q k:ℝ) := by
          apply (div_le_div_iff₀ hcap (hQpos k)).mpr
          nlinarith only [hqcap]
        have hpowle : (2*B*L)^((3:ℝ)/2) ≤ (N:ℝ)/(Q k:ℝ) :=
          ((le_div_iff₀ hcap).mpr (by nlinarith only [hlarge])).trans hratioLower
        have hh := (Real.le_rpow_inv_iff_of_pos
          (by positivity : (0:ℝ) ≤ 2*B*L)
          (div_pos hNp (hQpos k)).le (by norm_num : (0:ℝ) < 3/2)).mpr hpowle
        norm_num only [show ((3:ℝ)/2)⁻¹=2/3 by norm_num] at hh
        exact hh)
  have hUmono k : Usel k ≤ Usel 0 := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ (zero_le_one.trans hB)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hNp.le (hQpos 0)
    simpa only [Q,pow_zero,mul_one] using hQbase k
  have hklog : (kmax:ℝ) ≤ Real.log N/Real.log 2 := by
    have hQone : (1:ℝ) ≤ Qbase := hCR.trans hQlo
    have hpowN : (2:ℝ)^kmax ≤ N := by
      have hh : (2:ℝ)^kmax ≤ (Q kmax:ℝ) := by
        rw [hQcast]
        exact le_mul_of_one_le_left (by positivity) hQone
      exact hh.trans (by exact_mod_cast hQN kmax le_rfl)
    have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^kmax) hpowN
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hh
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlower,hQupper,hklog,hK,?_,hUmono⟩
  intro k hk
  obtain ⟨hU,hUL,hUlower,hUupper,hwrap,hUR⟩ := hUdata k hk
  refine ⟨hUL,hSource k,hMesh k,hMeshUpper k,hU,hwrap,hUupper,hUlower,
    hQN k hk,hUR,hstrong k,hminscale k,?_⟩
  have hqcap : (Q k:ℝ) ≤ qcap*(N:ℝ) :=
    (by exact_mod_cast hQmono k hk : (Q k:ℝ) ≤ Q kmax).trans hQupper
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hqcap hDcap
  have hs := mul_le_mul_of_nonneg_right hsmall hNp.le
  nlinarith only [hh,hs]

private theorem exists_uniform_dyadic_band_integer_scales
    {σ J B D₀ D₁ : ℝ} (hσ : 0 < σ)
    (hB : 1 ≤ B) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) :
    ∃ Csep : ℝ, 1 ≤ Csep ∧
      ∀ (N : ℕ) (R : ℝ), 1 ≤ R → (N:ℝ) ≤ R^2 → Csep*R ≤ N →
      ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
        let Q := fun k : ℕ => Qbase*2^k
        (768:ℝ)*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
        (N:ℝ)/Csep ≤ Q kmax ∧ (Q kmax:ℝ) ≤ N ∧
        (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
        (∀ k, 0 < Kmesh k) ∧
        (∀ k ≤ kmax,
          12*J ≤ σ*(Usel k:ℝ) ∧
          63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
          (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
          (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
          1 ≤ Usel k ∧
          B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
          (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
          ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
          Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
          768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
          D₀*(Q k:ℝ)/(N:ℝ)+D₁*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
          D₀*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
        (∀ k, Usel k ≤ Usel 0) := by
  let L := max 1 (12*J/σ)
  let Dcap := D₀+2*D₁
  let qcap := 1/(4*Dcap+(2*B*L)^((3:ℝ)/2)+1)
  let Csep := 1536/qcap
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hDc : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hpow : 0 < (2*B*L)^((3:ℝ)/2) := by positivity
  have hden : 0 < 4*Dcap+(2*B*L)^((3:ℝ)/2)+1 := by positivity
  have hcap : 0 < qcap := by dsimp only [qcap]; positivity
  have hcapOne : qcap ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc,hpow]
  have hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hDc]
  have hsmall : 4*Dcap*qcap ≤ 1 := by
    dsimp only [qcap]
    rw [one_div,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    linarith only [hpow]
  have hCsep : 1 ≤ Csep := by
    apply (le_div_iff₀ hcap).mpr
    linarith only [hcapOne]
  refine ⟨Csep,hCsep,?_⟩
  intro N R hR hNR hroom
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCsep hRp.le : R ≤ Csep*R).trans hroom
  have hNp : (0:ℝ) < N := hRp.trans_le hRN
  have hroom' : 2*(768:ℝ)*R ≤ qcap*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hroom hcap.le
    have he : qcap*(Csep*R)=1536*R := by dsimp only [Csep]; field_simp
    rw [he] at hh
    nlinarith only [hh]
  obtain ⟨Qbase,kmax,Kmesh,Usel,hQlo,hQhi,hQlast,hQlastHi,hlog,hK,hvalid,hmono⟩ :=
    dyadic_band_integer_physical_selection N (J:=J) hσ hR hRN hNR hB hL
      (by norm_num : (768:ℝ) ≤ 768) hcap hcapOne hlarge hDc hsmall hroom'
  refine ⟨Qbase,kmax,Kmesh,Usel,hQlo,by simpa only [show (2:ℝ)*768=1536 by norm_num] using hQhi,
    ?_,?_,hlog,hK,?_,hmono⟩
  · have hh : (N:ℝ)/Csep ≤ qcap*(N:ℝ)/2 := by
      have he : (N:ℝ)/Csep=qcap*(N:ℝ)/1536 := by
        dsimp only [Csep]
        field_simp
      rw [he]
      exact div_le_div_of_nonneg_left (mul_pos hcap hNp).le
        (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 1536)
    exact hh.trans hQlast
  · exact hQlastHi.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcapOne hNp.le)
  · intro k hk
    obtain ⟨hUL,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,hQN,hUR,hStrong,hMin,hD⟩ :=
      hvalid k hk
    have hULarge : 12*J ≤ σ*(Usel k:ℝ) := by
      have hh := (le_max_right (1:ℝ) (12*J/σ)).trans hUL
      have hh' := (div_le_iff₀ hσ).mp hh
      simpa only [mul_comm] using hh'
    have hDsum : D₀*(Qbase*2^k:ℕ)/(N:ℝ)+
        D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) ≤ 1/4 := by
      convert hD using 1
      dsimp only [Dcap]
      ring
    have hDlow : 0 ≤ D₁*(2*(Qbase*2^k:ℕ))/(N:ℝ) := by positivity
    refine ⟨hULarge,hSource,hMesh,hMeshUpper,hU,hwrap,hUupper,hUlower,
      hQN,hUR,hStrong,hMin,?_,?_⟩ <;> linarith only [hDsum,hDlow]

private theorem exists_uniform_source_physical_budget
    {Csep A₄ A₂ B Cbuffer Clinear Cwidth : ℝ}
    (hSep : 0 ≤ Csep) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hBuffer : 0 ≤ Cbuffer) (hLinear : 0 ≤ Clinear)
    (hWidth : 0 ≤ Cwidth) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 2 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N^2 ≤ M → U ≤ N →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N^2 ≤ M ∧ N*R ≤ M ∧ N^3 ≤ M*R^2 ∧ R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M ∧
      (∀ T : ℝ, 0 < T → T*N*R^2=M^3 → M ≤ T) := by
  let Cbudget := 43+Csep+2401*A₄+49*A₂+2*B+2*Cbuffer+2*Cwidth+2*Clinear
  have hbounds : 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧ 32 ≤ Cbudget ∧
      2401*A₄ ≤ Cbudget ∧ 49*A₂ ≤ Cbudget ∧ 2*B ≤ Cbudget ∧
      2*(Cbuffer+Cwidth)+2*Clinear+10 ≤ Cbudget := by
    dsimp only [Cbudget]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [hSep,hA₄,hA₂,hB,hBuffer,hLinear,hWidth]
  obtain ⟨hC,hSepC,h32,hC₄,hC₂,hCB,hCend⟩ := hbounds
  refine ⟨Cbudget,hC,hSepC,?_⟩
  intro N R M U hN hR hRNbudget hNRbudget hMbudget hUN
  have hNp : 0 < N := by linarith only [hN]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRN : R ≤ N :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hRp.le : R ≤ Cbudget*R).trans hRNbudget
  have hNR : N ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hNp.le : N ≤ Cbudget*N).trans hNRbudget
  have hNM₂ : N^2 ≤ M :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (sq_nonneg N) : N^2 ≤ Cbudget*N^2).trans hMbudget
  have hNsq : N ≤ N^2 := by nlinarith only [hN]
  have hNsqOne : 1 ≤ N^2 := by nlinarith only [hN]
  have hNM : N ≤ M := hNsq.trans hNM₂
  have hMp : 0 < M := hNp.trans_le hNM
  have hNRM : N*R ≤ M := by
    calc
      _ ≤ N*N := mul_le_mul_of_nonneg_left hRN hNp.le
      _ = N^2 := (pow_two N).symm
      _ ≤ M := hNM₂
  have hN₃ : N^3 ≤ M*R^2 := by
    calc
      _ = N^2*N := by ring
      _ ≤ _ := mul_le_mul hNM₂ hNR hNp.le hMp.le
  have hpad : 7*N+2 ≤ M/4 := by
    have hh := (mul_le_mul_of_nonneg_right h32 (sq_nonneg N)).trans hMbudget
    have hn := mul_le_mul_of_nonneg_left hNsq (by norm_num : (0:ℝ) ≤ 32)
    nlinarith only [hh,hn,hN]
  have hshort : 6*N+1 ≤ 7*N := by linarith only [hN]
  have hquartic : A₄*(6*N+1)^4 ≤ M*N*R^2 := by
    calc
      _ ≤ A₄*(7*N)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 4) hA₄
      _ = (2401*A₄)*N^4 := by ring
      _ ≤ Cbudget*N^4 := mul_le_mul_of_nonneg_right hC₄ (by positivity)
      _ = (Cbudget*N^2)*N^2 := by ring
      _ ≤ M*N^2 := mul_le_mul_of_nonneg_right hMbudget (sq_nonneg N)
      _ = M*N*N := by ring
      _ ≤ M*N*R^2 := mul_le_mul_of_nonneg_left hNR (by positivity)
  have hquadratic : A₂*(6*N+1)^2 ≤ N*R^2 := by
    calc
      _ ≤ A₂*(7*N)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshort 2) hA₂
      _ = (49*A₂)*N^2 := by ring
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hC₂ (sq_nonneg N)
      _ = (Cbudget*N)*N := by ring
      _ ≤ R^2*N := mul_le_mul_of_nonneg_right hNRbudget hNp.le
      _ = _ := by ring
  have hsmall : B*R^2/N^2 ≤ 1/2 := by
    have hCsq : Cbudget ≤ Cbudget^2 := by nlinarith only [hC]
    have hmul := mul_le_mul_of_nonneg_right (hCB.trans hCsq) (sq_nonneg R)
    have hsq : Cbudget^2*R^2 ≤ N^2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hRNbudget 2
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    nlinarith only [hmul,hsq]
  have hroom : 2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M := by
    have hUN' : U*N ≤ N^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hUN hNp.le
    have hb := mul_le_mul_of_nonneg_left hUN' hBuffer
    have hw := mul_le_mul_of_nonneg_left hUN' hWidth
    have hl := mul_le_mul_of_nonneg_left hNsq hLinear
    calc
      _ ≤ (2*(Cbuffer+Cwidth)+2*Clinear+10)*N^2 := by
        nlinarith only [hb,hw,hl,hNsq,hNsqOne]
      _ ≤ Cbudget*N^2 := mul_le_mul_of_nonneg_right hCend (sq_nonneg N)
      _ ≤ M := hMbudget
  refine ⟨hMp,hRN,hNR,hNM₂,hNRM,hN₃,hRN.trans hNM,hpad,hquartic,hquadratic,hsmall,hroom,?_⟩
  intro T hT hscale
  have hRM₂ : R^2 ≤ M :=
    (pow_le_pow_left₀ hRp.le hRN 2).trans hNM₂
  have hprod : N*R^2 ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul hNM hRM₂ (sq_nonneg R) hMp.le
      _ = _ := (pow_two M).symm
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMp)).mp
  calc
    M^2*M = M^3 := by ring
    _ = T*(N*R^2) := by nlinarith only [hscale]
    _ ≤ T*M^2 := mul_le_mul_of_nonneg_left hprod hT.le
    _ = M^2*T := by ring

private theorem positive_difference_source_physical_regime_coefficients
    {σ c J κ T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) (hκ : 0 < κ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hNR : N ≤ R^2) (hNM : N^2 ≤ M) :
    let lambda := c*κ*T/(12*J*M^2)
    let Uband := (3*J/σ)*T/(2*M^2)
    Uband/lambda=18*J^2/(σ*c*κ) ∧
      Uband^2*(R^8/N^4)=(3*J/(2*σ))^2*M^2*R^4/N^6 ∧
      1+R^4/(6*N^2) ≤ (7/6:ℝ)*R^4/N^2 ∧
      1+R^4*Uband^2/N^2 ≤ (1+(3*J/(2*σ))^2)*M^2/N^4 := by
  intro lambda Uband
  have hTscale : T=M^3/(N*R^2) := (eq_div_iff (by positivity)).mpr (by
    nlinarith only [hscale])
  have hUscale : Uband=(3*J/(2*σ))*M/(N*R^2) := by
    dsimp only [Uband]
    rw [hTscale]
    field_simp
  have hratio : Uband/lambda=18*J^2/(σ*c*κ) := by
    dsimp only [Uband,lambda]
    field_simp
    ring
  have hupper : 1 ≤ R^4/N^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    have hh := pow_le_pow_left₀ hN.le hNR 2
    nlinarith only [hh]
  have hlower : 1 ≤ M^2/N^4 := by
    apply (le_div_iff₀ (pow_pos hN 4)).mpr
    have hh := pow_le_pow_left₀ (sq_nonneg N) hNM 2
    nlinarith only [hh]
  refine ⟨hratio,?_,?_,?_⟩
  · rw [hUscale]
    field_simp
  · have he : R^4/(6*N^2)=(R^4/N^2)/6 := by ring
    rw [he]
    calc
      _ ≤ R^4/N^2+(R^4/N^2)/6 := add_le_add hupper le_rfl
      _ = _ := by ring
  · have he : R^4*Uband^2/N^2=(3*J/(2*σ))^2*(M^2/N^4) := by
      rw [hUscale]
      field_simp
    rw [he]
    calc
      _ ≤ M^2/N^4+(3*J/(2*σ))^2*(M^2/N^4) := add_le_add hlower le_rfl
      _ = _ := by ring

private theorem exists_source_cutoff_margins
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut := by
  let Bcut := 1+61*Ccurv*Cphys
  let Bselect := max 1 (max (2+168/κ) (max (7*Bcut/κ) (Sector/Esize)))
  have hBcut : 0 < Bcut := by dsimp only [Bcut]; positivity
  have hBs : 1 ≤ Bselect := le_max_left _ _
  have hSize : 2+168/κ ≤ Bselect := (le_max_left _ _).trans (le_max_right _ _)
  have hCut : 7*Bcut/κ ≤ Bselect :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSec : Sector/Esize ≤ Bselect :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Bcut,Bselect,hBcut,hBs,hSize,?_,(div_le_iff₀ hEsize).mp hSec,?_⟩
  · calc
      7*Bcut ≤ Bselect*κ := (div_le_iff₀ hκ).mp hCut
      _ = κ*Bselect := mul_comm _ _
  · dsimp only [Bcut]
    linarith

private theorem general_source_constants_nonnegative
    {σ δ κ Usrc σsrc csrc θ Cupper Clower Dupper Dlower : ℝ}
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hκ : 0 < κ)
    (hUsrc : 0 < Usrc) (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc)
    (hθ : 0 < θ) (hCU : 0 < Cupper) (hCL : 0 < Clower)
    (hDU : 0 < Dupper) (hDL : 0 < Dlower) :
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 < Cphys ∧
    0 < c ∧
    0 < J ∧
    1 ≤ B ∧
    0 ≤ B ∧
    0 ≤ C₂ ∧
    0 ≤ C₃ ∧
    0 ≤ modelPhaseJetCoefficient σ 4+δ ∧
    0 ≤ quarticReciprocalConstant σ δ ∧
    0 ≤ quarticNonlinearResidualConstant σ δ ∧
    0 ≤ Ct ∧
    0 ≤ Cc ∧
    0 ≤ Ccurv ∧
    0 ≤ Kres ∧
    0 < Esize ∧
    0 ≤ Dbase ∧
    0 ≤ Tbase ∧
    0 < Lunit ∧
    0 < Gamma ∧
    0 ≤ Cthird ∧
    0 ≤ AupperConst ∧
    0 ≤ BupperConst ∧
    0 ≤ DupperConst ∧
    0 ≤ AlowerConst ∧
    0 ≤ BlowerConst ∧
    0 ≤ DlowerConst ∧
    0 ≤ Cpack ∧
    0 ≤ Cfirst ∧
    0 ≤ Cgap ∧
    0 ≤ Cmain ∧
    0 ≤ Ctail := by
  intro Cphys c J B C₂ C₃ Ct Cc Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird AupperConst BupperConst DupperConst AlowerConst BlowerConst DlowerConst Cpack Cfirst Cgap Cmain Ctail
  have hModelPhase : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hBzero : 0 ≤ B := zero_le_one.trans hB
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδzero
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδzero
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδzero
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 < Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hAupper : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBupper : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hDupper : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  have hAlower : 0 ≤ AlowerConst := by dsimp only [AlowerConst]; positivity
  have hBlower : 0 ≤ BlowerConst := by dsimp only [BlowerConst]; positivity
  have hDlower : 0 ≤ DlowerConst := by dsimp only [DlowerConst]; positivity
  have hCpack : 0 ≤ Cpack := by dsimp only [Cpack]; positivity
  have hCfirst : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCgap : 0 ≤ Cgap := by dsimp only [Cgap]; positivity
  have hCmain : 0 ≤ Cmain :=
    add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hCfirst) (pow_nonneg hLunit.le 3)) _))
      (by norm_num)
  have hCtail : 0 ≤ Ctail :=
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) hCpack) (sq_nonneg Lunit)) hCgap
  exact ⟨hCphys,hc,hJ,hB,hBzero,hC₂,hC₃,hC₄,hCR,hCN,hCt,hCc,hCcurv,hKres,hEsize,hDbase,hTbase,hLunit,hGamma,hCthird,hAupper,hBupper,hDupper,hAlower,hBlower,hDlower,hCpack,hCfirst,hCgap,hCmain,hCtail⟩

private theorem eventually_general_quantitative_phase_subinterval_bound
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) := by

  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
  let Lsource := max (8*Ratio^2)
    (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
  have hLsource : 0 ≤ Lsource :=
    (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  let θ := min (1/48:ℝ) (1/(16*(Lsource+3)))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθmax : θ ≤ 1/24 := (min_le_left _ _).trans (by norm_num)
  have hθaction : θ ≤ 1/(8*(Lsource+3)) := by
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hLsource])
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hfinite⟩ :=
    HuxleyRationalPhase.eventually_positive_difference_selected_band_phase_subinterval_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
  let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
  let DupperConst := θ*(3*Usrc/σsrc)*1/2
  let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
  let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
  let DlowerConst := 12*Usrc*θ/(csrc*κ)
  let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
  let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
  let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
  let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
  let Ctail := 4*Cpack/Lunit^2+Cgap
  obtain ⟨hCphys,hc,hJ,hB,hBzero,hC₂,hC₃,hC₄,hCR,hCN,hCt,hCc,hCcurv,hKres,hEsize,hDbase,hTbase,hLunit,hGamma,hCthird,hAupper,hBupper,hDupper,hAlower,hBlower,hDlower,hCpack,hCfirst,hCgap,hCmain,hCtail⟩ :=
    general_source_constants_nonnegative hσ hδzero hκ hUsrc hσsrc hcsrc hθ hCU hCL hDU hDL
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBsOne,hBsSize,hcutMargin,hsize,hBsize⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ hCcurv hCphys.le hEsize
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let D₀ := 37*B/2+16*B*Cc+2*Ct+2*Cc
  have hD₀ : 0 ≤ D₀ := by clear hfinite; dsimp only [D₀]; positivity
  obtain ⟨Csep,hCsep,hselect⟩ :=
    exists_uniform_dyadic_band_integer_scales (J:=Usrc) hσsrc hBsOne hD₀ hCN
  obtain ⟨Cbudget,hCbudget,hCsepBudget,hbudget⟩ :=
    exists_uniform_source_physical_budget (zero_le_one.trans hCsep)
      (show 0 ≤ 3*Usrc/σsrc by positivity)
      (show 0 ≤ 3*Usrc/(4*σsrc) by positivity) hBzero
      (show 0 ≤ 56/κ by positivity)
      (show 0 ≤ 1/(Cphys+2) by positivity)
      (show 0 ≤ 14*σsrc/csrc by positivity)

  let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
  let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
  let Cap := 3*ChartCap*NarrowCap
  have hChartCap : 0 ≤ ChartCap := by clear hfinite; dsimp only [ChartCap]; positivity
  have hNarrowCap : 0 ≤ NarrowCap := by clear hfinite; dsimp only [NarrowCap]; positivity
  have hCap : 0 ≤ Cap := by clear hfinite; dsimp only [Cap]; positivity
  let CUP := 240*(9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+
    2*BupperConst+(3/2:ℝ)*DupperConst)
  have hCUP : 0 ≤ CUP := by clear hfinite; dsimp only [CUP]; positivity
  let CLOW := 240*(9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
    2*BlowerConst+(3/2:ℝ)*DlowerConst)
  let CLARGE := 2*Bselect*60*588*Ratio^2*(3*Usrc/(2*σsrc))^2*(Cmain+Ctail)
  have hCLOW : 0 ≤ CLOW :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg
          (mul_nonneg hAlower (sq_nonneg DlowerConst)) _))
          (mul_nonneg (by norm_num) hBlower))
        (mul_nonneg (by norm_num) hDlower))
  have hCLARGE : 0 ≤ CLARGE :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBs.le)
          (by norm_num)) (by norm_num)) (sq_nonneg Ratio))
        (sq_nonneg (3*Usrc/(2*σsrc))))
      (add_nonneg hCmain hCtail)
  let Couter := (48*σsrc/csrc)^6*C*Cap^11
  have hCouter : 0 ≤ Couter := by clear hfinite; dsimp only [Couter]; positivity
  let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
  let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  have hNumeric := eventually_general_finite_numerical_consequence
    hσsrc hcsrc hUsrc hκ hCphys.le (zero_le_one.trans hCsrc)
    hCouter hCUP hCLOW hCLARGE hDtype.le hBsOne hCsep hε
  have hLog : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  refine ⟨Cbudget,η₀,hCbudget,hη₀,hηcap,?_⟩
  filter_upwards [hfinite hθ hθmax hθaction,hNumeric,
    Filter.eventually_ge_atTop (1:ℝ),hLog] with T hfiniteT hNumericT hTone hLogOne
  intro Fsrc Y n N R Jsep η M hNlink hNtwo hR hη hηsmall hJsep hJM
    hy hsepY hreg hjets htests hnegative hmodels hscale
    hSepBudget hRadiusBudget hSquareBudget hNfour hNten A Bint hA hAB hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hNR : (N:ℝ) ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCbudget hNp.le :
      (N:ℝ) ≤ Cbudget*N).trans hRadiusBudget
  have hCsepRoom : Csep*R ≤ N :=
    (mul_le_mul_of_nonneg_right hCsepBudget hRp.le).trans hSepBudget
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,hEndHi,hkmax,hKpos,hvalid,hUmono⟩ :=
    hselect N R hR hNR hCsepRoom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ N := by
    obtain ⟨_,_,_,_,_,_,hUupper,_,_,_,hQstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQone : (1:ℝ) ≤ Q 0 := by nlinarith only [hQstrong,hR]
    have hQzero : (0:ℝ) < Q 0 := zero_lt_one.trans_le hQone
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hUupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBsOne
      _ ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_self hNp.le hQone) (by norm_num)
      _ ≤ N := Real.rpow_le_self_of_one_le hNOne (by norm_num)
  obtain ⟨hM,hRN,hNR',hNsqM,hNRM,hNcube,hRM,hpad,hquartic,hquadratic,hsmall,hroom,hMTall⟩ :=
    hbudget (N:ℝ) R M (Usel 0:ℝ) hNreal hR hSepBudget hRadiusBudget hSquareBudget hUzero
  have hMT : M ≤ T := hMTall T hT hscale
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hRegimeLog : (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) :=
    hNfour.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hLogOne (by norm_num)))
  let Vscale := fun k : ℕ => (Usel k:ℝ)^((3:ℝ)/2)
  let lambda := csrc*κ*T/(12*Usrc*M^2)
  let Uband := (3*Usrc/σsrc)*T/(2*M^2)
  obtain ⟨hRatio,hBandScale,_,_⟩ := positive_difference_source_physical_regime_coefficients
    hσsrc hcsrc hUsrc hκ hT hM hNp hRp hscale hNR' hNsqM

  let μ₀ := csrc*T/(12*σsrc*M^3)
  let U₀ := Usrc*T/(2*σsrc*M^3)
  let Error := Yc*(M/(N:ℝ)+1)*
    (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
  let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  let Δtype := fun k : ℕ =>
    (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
  let Δ := fun k : ℕ => D₀*(Q k:ℝ)/(N:ℝ)
  let D := fun k : ℕ =>
    Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
  let Kupper := fun k : ℕ =>
    240*(M^2/((N:ℝ)^4*(Usel k:ℝ)))*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
  let Klower := fun k : ℕ =>
    240*(R^4/((N:ℝ)^2*(Usel k:ℝ)))*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
  let Klarge := fun k : ℕ =>
    2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3)
  let Buffer := fun k : ℕ =>
    (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
  let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
  let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    (48*σsrc/csrc)^6*(R^2/(Q k:ℝ))^6*
      C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
        ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
          ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
  let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
  let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
  have hvalidGeneral : ∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2 := by
    intro k hk
    obtain ⟨hUL,hSource,hMesh,_,hU,hWrap,hUpper,hLower,hQN,hUR,hStrong,hMin,hD,hDelta⟩ :=
      hvalid k hk
    exact ⟨hUL,hSource,hMesh,hU,hWrap,hUpper,hLower,hQN,hUR,hStrong,hMin,hD,hDelta⟩
  have hRoom : 2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M := by
    convert hroom using 1
    dsimp only [Buffer,Width]
    ring
  obtain ⟨Chunks,band,Dcover,hChunks,hBands,hTerminal,hGrids,hNorm⟩ :=
    hfiniteT Fsrc Y n N Qbase kmax Kmesh Usel R Jsep
      (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hKpos hNlink hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM
      hy hsepY hreg hjets htests hnegative hmodels hscale hpad hquartic hquadratic
      hRegimeLog hBcut hBsSize hcutMargin hNten hNsqM hNRM
      hsmall hNR' hRN hNcube hsize hBsize hvalidGeneral
      (fun k _ => hUmono k) hRoom A Bint hA hAB hBint
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let NumericFamily := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
      ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
        ((P.image Prod.fst).card:ℝ)^2*
          ((Vscale k)*(CUP*M^2/((N:ℝ)^4*(Usel k:ℝ))+
            CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))+
            CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss)
  have hQbaseReal : (0:ℝ) < Qbase := by nlinarith only [hBaseLo,hRp]
  have hQbase : 0 < Qbase := by exact_mod_cast hQbaseReal
  have hvalidNumeric : ∀ k ≤ kmax,
      R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/(2*σsrc)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) := by
    intro k hk
    obtain ⟨_,_,hMesh,hKU,_,_,hUpper,hLower,hQN,_,hStrong,_,_,_⟩ := hvalid k hk
    exact ⟨by nlinarith only [hStrong,hRp],hQN,hMesh,hKU,hUpper,hLower⟩
  have hKupper (k : ℕ) : Kupper k=CUP*M^2/((N:ℝ)^4*(Usel k:ℝ)) := by
    dsimp only [Kupper,CUP]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hKlower (k : ℕ) : Klower k=CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)) := by
    dsimp only [Klower,CLOW]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hKlarge (k : ℕ) :
      Klarge k=CLARGE*M^2*R^4/(N:ℝ)^6*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3) := by
    dsimp only [Klarge]
    rw [hRatio]
    calc
      _ = (2*Bselect*60*588*Ratio^2*(Cmain+Ctail))*
          (Uband^2*(R^8/(N:ℝ)^4))*((Q k:ℝ)/(N:ℝ))^((2:ℝ)/3) := by ring
      _ = _ := by rw [hBandScale]; dsimp only [CLARGE]; ring
  have hFamilyEq (k : ℕ) (P : Finset (ℝ × ℤ)) :
      FamilyBound k P=NumericFamily k P := by
    dsimp only [FamilyBound,NumericFamily]
    rw [hKupper,hKlower,hKlarge]
    dsimp only [Couter]
    ac_rfl
  let S := (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y), (𝐞 (f y j):ℂ)‖)^12
  change S ≤ 2^11*(((kmax:ℝ)+2)^11*
    (((n:ℝ)*Yc*Density kmax)^12+
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
        (2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) at hNorm
  simp only [hFamilyEq] at hNorm
  exact hNumericT Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover
    hNlink hNtwo hR hNR' hNsqM hMT hJsep.le hscale hQbase hBaseHi hEndLo hkmax hKpos
    hvalidNumeric hChunks hBands
    (fun k hk r => (hGrids k hk).2.2.1 r)
    (fun k hk r => (hGrids k hk).2.2.2 r) hNorm

example
    {N R Q B L : ℝ} (hR : 1 ≤ R) (hRQ : R ≤ Q) (hQN : Q ≤ N)
    (hNR : N ≤ R^2) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hlarge : 2*B*L ≤ (N/Q)^((2:ℝ)/3)) :
    let U : ℕ := ⌊(N/Q)^((2:ℝ)/3)/B⌋₊
    1 ≤ U ∧ L ≤ (U:ℝ) ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      (U:ℝ) ≤ R^2 :=
  HuxleyGeneralPhaseScratch.reference_floor_physical_budgets (N:=N) (R:=R) (Q:=Q) (B:=B) (L:=L) hR hRQ hQN hNR hB hL hlarge

example
    (N : ℕ) {σ J R B L Cbase qcap Dcap : ℝ}
    (hσ : 0 < σ) (hR : 1 ≤ R) (hRN : R ≤ N) (hNR : (N:ℝ) ≤ R^2)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hCbase : 768 ≤ Cbase)
    (hcap : 0 < qcap) (hcapOne : qcap ≤ 1)
    (hlarge : qcap*(2*B*L)^((3:ℝ)/2) ≤ 1)
    (hDcap : 0 ≤ Dcap) (hsmall : 4*Dcap*qcap ≤ 1)
    (hroom : 2*Cbase*R ≤ qcap*(N:ℝ)) :
    ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
      let Q := fun k : ℕ => Qbase*2^k
      Cbase*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 2*Cbase*R ∧
      qcap*(N:ℝ)/2 ≤ Q kmax ∧ (Q kmax:ℝ) ≤ qcap*(N:ℝ) ∧
      (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
      (∀ k, 0 < Kmesh k) ∧
      (∀ k ≤ kmax,
        L ≤ (Usel k:ℝ) ∧
        63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        1 ≤ Usel k ∧
        B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
        Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
        768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
        Dcap*(Q k:ℝ)/(N:ℝ) ≤ 1/4) ∧
      (∀ k, Usel k ≤ Usel 0) :=
  HuxleyGeneralPhaseScratch.dyadic_band_integer_physical_selection N (σ:=σ) (J:=J) (R:=R) (B:=B) (L:=L) (Cbase:=Cbase) (qcap:=qcap) (Dcap:=Dcap) hσ hR hRN hNR hB hL hCbase hcap hcapOne hlarge hDcap hsmall hroom

example
    {σ J B D₀ D₁ : ℝ} (hσ : 0 < σ)
    (hB : 1 ≤ B) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) :
    ∃ Csep : ℝ, 1 ≤ Csep ∧
      ∀ (N : ℕ) (R : ℝ), 1 ≤ R → (N:ℝ) ≤ R^2 → Csep*R ≤ N →
      ∃ (Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ),
        let Q := fun k : ℕ => Qbase*2^k
        (768:ℝ)*R ≤ Qbase ∧ (Qbase:ℝ) ≤ 1536*R ∧
        (N:ℝ)/Csep ≤ Q kmax ∧ (Q kmax:ℝ) ≤ N ∧
        (kmax:ℝ) ≤ Real.log N/Real.log 2 ∧
        (∀ k, 0 < Kmesh k) ∧
        (∀ k ≤ kmax,
          12*J ≤ σ*(Usel k:ℝ) ∧
          63*(J/(2*σ*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
          (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
          (Kmesh k:ℝ) ≤ 2*(max 1 (63*J/(2*σ)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
          1 ≤ Usel k ∧
          B^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
          (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/B ∧
          ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*B) ≤ (Usel k:ℝ) ∧
          Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
          768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
          D₀*(Q k:ℝ)/(N:ℝ)+D₁*(2*(Q k:ℝ))/(N:ℝ) ≤ 1/2 ∧
          D₀*(Q k:ℝ)/(N:ℝ) < 1/2) ∧
        (∀ k, Usel k ≤ Usel 0) :=
  HuxleyGeneralPhaseScratch.exists_uniform_dyadic_band_integer_scales (σ:=σ) (J:=J) (B:=B) (D₀:=D₀) (D₁:=D₁) hσ hB hD₀ hD₁

example
    {Csep A₄ A₂ B Cbuffer Clinear Cwidth : ℝ}
    (hSep : 0 ≤ Csep) (hA₄ : 0 ≤ A₄) (hA₂ : 0 ≤ A₂)
    (hB : 0 ≤ B) (hBuffer : 0 ≤ Cbuffer) (hLinear : 0 ≤ Clinear)
    (hWidth : 0 ≤ Cwidth) :
    ∃ Cbudget : ℝ, 1 ≤ Cbudget ∧ Csep ≤ Cbudget ∧
      ∀ (N R M U : ℝ), 2 ≤ N → 1 ≤ R →
      Cbudget*R ≤ N → Cbudget*N ≤ R^2 → Cbudget*N^2 ≤ M → U ≤ N →
      0 < M ∧ R ≤ N ∧ N ≤ R^2 ∧ N^2 ≤ M ∧ N*R ≤ M ∧ N^3 ≤ M*R^2 ∧ R ≤ M ∧
      7*N+2 ≤ M/4 ∧
      A₄*(6*N+1)^4 ≤ M*N*R^2 ∧
      A₂*(6*N+1)^2 ≤ N*R^2 ∧
      B*R^2/N^2 ≤ 1/2 ∧
      2*((Cbuffer*U)*N+Clinear*N+2+(Cwidth*U)*N)+6*N ≤ M ∧
      (∀ T : ℝ, 0 < T → T*N*R^2=M^3 → M ≤ T) :=
  HuxleyGeneralPhaseScratch.exists_uniform_source_physical_budget (Csep:=Csep) (A₄:=A₄) (A₂:=A₂) (B:=B) (Cbuffer:=Cbuffer) (Clinear:=Clinear) (Cwidth:=Cwidth) hSep hA₄ hA₂ hB hBuffer hLinear hWidth

example
    {σ c J κ T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) (hκ : 0 < κ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hNR : N ≤ R^2) (hNM : N^2 ≤ M) :
    let lambda := c*κ*T/(12*J*M^2)
    let Uband := (3*J/σ)*T/(2*M^2)
    Uband/lambda=18*J^2/(σ*c*κ) ∧
      Uband^2*(R^8/N^4)=(3*J/(2*σ))^2*M^2*R^4/N^6 ∧
      1+R^4/(6*N^2) ≤ (7/6:ℝ)*R^4/N^2 ∧
      1+R^4*Uband^2/N^2 ≤ (1+(3*J/(2*σ))^2)*M^2/N^4 :=
  HuxleyGeneralPhaseScratch.positive_difference_source_physical_regime_coefficients (σ:=σ) (c:=c) (J:=J) (κ:=κ) (T:=T) (M:=M) (N:=N) (R:=R) hσ hc hJ hκ hT hM hN hR hscale hNR hNM

example
    {κ Ccurv Cphys Sector Esize : ℝ}
    (hκ : 0 < κ) (hCcurv : 0 ≤ Ccurv) (hCphys : 0 ≤ Cphys)
    (hEsize : 0 < Esize) :
    ∃ Bcut Bselect : ℝ, 0 < Bcut ∧ 1 ≤ Bselect ∧
      2+168/κ ≤ Bselect ∧ 7*Bcut ≤ κ*Bselect ∧
      Sector ≤ Bselect*Esize ∧ 61*Ccurv*Cphys ≤ Bcut :=
  HuxleyGeneralPhaseScratch.exists_source_cutoff_margins (κ:=κ) (Ccurv:=Ccurv) (Cphys:=Cphys) (Sector:=Sector) (Esize:=Esize) hκ hCcurv hCphys hEsize

example
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
        Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.eventually_general_quantitative_phase_subinterval_bound (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (δ:=δ) (ε:=ε) hσsrc hcsrc hUsrc hσ hδzero hδ hε hanchorBudget


#print axioms HuxleyGeneralPhaseScratch.reference_floor_physical_budgets
#print axioms HuxleyGeneralPhaseScratch.dyadic_band_integer_physical_selection
#print axioms HuxleyGeneralPhaseScratch.exists_uniform_dyadic_band_integer_scales
#print axioms HuxleyGeneralPhaseScratch.exists_uniform_source_physical_budget
#print axioms HuxleyGeneralPhaseScratch.positive_difference_source_physical_regime_coefficients
#print axioms HuxleyGeneralPhaseScratch.exists_source_cutoff_margins
#print axioms HuxleyGeneralPhaseScratch.eventually_general_quantitative_phase_subinterval_bound

example
    {σ δ κ Usrc σsrc csrc θ Cupper Clower Dupper Dlower : ℝ}
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hκ : 0 < κ)
    (hUsrc : 0 < Usrc) (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc)
    (hθ : 0 < θ) (hCU : 0 < Cupper) (hCL : 0 < Clower)
    (hDU : 0 < Dupper) (hDL : 0 < Dlower) :
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    0 < Cphys ∧
    0 < c ∧
    0 < J ∧
    1 ≤ B ∧
    0 ≤ B ∧
    0 ≤ C₂ ∧
    0 ≤ C₃ ∧
    0 ≤ modelPhaseJetCoefficient σ 4+δ ∧
    0 ≤ quarticReciprocalConstant σ δ ∧
    0 ≤ quarticNonlinearResidualConstant σ δ ∧
    0 ≤ Ct ∧
    0 ≤ Cc ∧
    0 ≤ Ccurv ∧
    0 ≤ Kres ∧
    0 < Esize ∧
    0 ≤ Dbase ∧
    0 ≤ Tbase ∧
    0 < Lunit ∧
    0 < Gamma ∧
    0 ≤ Cthird ∧
    0 ≤ AupperConst ∧
    0 ≤ BupperConst ∧
    0 ≤ DupperConst ∧
    0 ≤ AlowerConst ∧
    0 ≤ BlowerConst ∧
    0 ≤ DlowerConst ∧
    0 ≤ Cpack ∧
    0 ≤ Cfirst ∧
    0 ≤ Cgap ∧
    0 ≤ Cmain ∧
    0 ≤ Ctail :=
  HuxleyGeneralPhaseScratch.general_source_constants_nonnegative (σ:=σ) (δ:=δ) (κ:=κ) (Usrc:=Usrc) (σsrc:=σsrc) (csrc:=csrc) (θ:=θ) (Cupper:=Cupper) (Clower:=Clower) (Dupper:=Dupper) (Dlower:=Dlower) hσ hδzero hκ hUsrc hσsrc hcsrc hθ hCU hCL hDU hDL


#print axioms HuxleyGeneralPhaseScratch.general_source_constants_nonnegative

private theorem exponentialSumAt_eq_int_Icc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j := by
  unfold Expdb.exponentialSumAt
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  case hi =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn'.1,by exact_mod_cast hn'.2⟩
  case i_inj =>
    intro n _ m _ hnm
    exact_mod_cast hnm
  case i_surj =>
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hz0 : 0≤z := (Int.natCast_nonneg a).trans hz'.1
    refine ⟨z.toNat,Finset.mem_Icc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hz0⟩
    · omega
    · omega
  case h =>
    intro n _
    simp only [Int.cast_natCast]

private theorem norm_exponentialSumAt_le_int_Ioc
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ := by
  rw [exponentialSumAt_eq_int_Icc,
    Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab : (a:ℤ)≤b),Finset.sum_cons]
  simpa only [Expdb.norm_oscillatory] using
    norm_add_le (Expdb.oscillatory F X M (a:ℤ))
      (∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j)

private theorem norm_sourceShiftCorrelation_le_difference_Ioc
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r k : ℕ) (hk : 0<k) (hrL : r≤L) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r):ℕ):ℤ),
        Expdb.oscillatory
          (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k)))/((k:ℝ)/M))
          (X*k/M) M j‖ := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc := HuxleyRationalPhase.sourceShiftCorrelation_difference_family_sum
    F (σ:=1) (T:=X) (N:=M) (H:=(k:ℝ)) (by norm_num) hM hkR a L r hrL
  dsimp only at hc
  rw [hc]
  simpa only [one_mul,sub_add_cancel,Complex.norm_conj] using
    norm_exponentialSumAt_le_int_Ioc
      (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k-1+1)))/(1*((k:ℝ)/M)))
      (1*X*k/M) M a (a+(L-r)) (Nat.le_add_right _ _)

private theorem upper_radius_error_bound
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hD2 : 1≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  obtain ⟨hSq,_,hInv,_⟩ := comparable_radius_powers hN hR hS hD hSR hRS
  have h₁ : Ysmall*M/Real.sqrt N≤D^2*(Y*M/Real.sqrt N) := by
    calc
      _ ≤ Y*M/Real.sqrt N := by gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hD2
  have h₂ : Ysmall*M*S^2/N^2≤D^2*(Y*M*R^2/N^2) := by
    calc
      _ ≤ Y*M*(D^2*R^2)/N^2 := by gcongr
      _ = _ := by ring
  have h₃ : Ysmall*N*(N/S)^((2:ℝ)/3)≤D^2*(Y*N*(N/R)^((2:ℝ)/3)) := by
    calc
      _ ≤ Y*N*(D*(N/R)^((2:ℝ)/3)) := by gcongr
      _ = D*(Y*N*(N/R)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDD2 (by positivity)
  calc
    _ ≤ D^2*(Y*M/Real.sqrt N)+D^2*(Y*M*R^2/N^2)+
        D^2*(Y*N*(N/R)^((2:ℝ)/3)) := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

private theorem normalized_radius_comparable
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S := by
  have hD0 := zero_le_one.trans hD
  have hDD2 : D≤D^2 := by nlinarith only [hD,sq_nonneg (D-1)]
  constructor
  · apply (sq_le_sq₀ hS.le (mul_nonneg hD0 hR.le)).mp
    calc
      _ ≤ (D*γ)*S^2 := le_mul_of_one_le_left (sq_nonneg S) hDγ
      _ = D*R^2 := by rw [mul_assoc,hlink]
      _ ≤ D^2*R^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg R)
      _ = _ := (mul_pow D R 2).symm
  · apply (sq_le_sq₀ hR.le (mul_nonneg hD0 hS.le)).mp
    calc
      _ = γ*S^2 := hlink.symm
      _ ≤ D*S^2 := mul_le_mul_of_nonneg_right hγD (sq_nonneg S)
      _ ≤ D^2*S^2 := mul_le_mul_of_nonneg_right hDD2 (sq_nonneg S)
      _ = _ := (mul_pow D S 2).symm

private theorem comparable_radius_source_budgets
    {M N R S D C : ℝ} (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hD : 1≤D) (hC : 1≤C)
    (hSR : S≤D*R) (hRS : R≤D*S)
    (hRlow : C*D^7≤R) (hRN : (C*D^7)*R≤N)
    (hNR : (C*D^7)*N≤R^2) (hNM : (C*D^7)*N^2≤M)
    (hFour : (C*D^7)*N^4≤M*R^3)
    (hTen : (C*D^7)*N^10≤M^3*R^7) :
    1≤S ∧ C*S≤N ∧ C*N≤S^2 ∧ C*N^2≤M ∧
      N^4≤M*S^3 ∧ N^10≤M^3*S^7 := by
  have hDpos := zero_lt_one.trans_le hD
  have hCpos := zero_lt_one.trans_le hC
  have hpow (i : ℕ) (hi : i≤7) : C*D^i≤C*D^7 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hi) hCpos.le
  have hplain (i : ℕ) (hi : i≤7) : D^i≤C*D^7 :=
    (le_mul_of_one_le_left (pow_nonneg hDpos.le i) hC).trans (hpow i hi)
  have hB : C≤C*D^7 := by simpa only [pow_zero,mul_one] using hpow 0 (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hDb : D≤C*D^7 := by simpa only [pow_one] using hplain 1 (by omega)
    have hh := hDb.trans (hRlow.trans hRS)
    nlinarith only [hh,hDpos]
  · calc
      _ ≤ C*(D*R) := mul_le_mul_of_nonneg_left hSR hCpos.le
      _ = (C*D^1)*R := by ring
      _ ≤ (C*D^7)*R := mul_le_mul_of_nonneg_right (hpow 1 (by omega)) hR.le
      _ ≤ N := hRN
  · apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDpos)).mp
    calc
      _ = (C*D^2)*N := by ring
      _ ≤ (C*D^7)*N := mul_le_mul_of_nonneg_right (hpow 2 (by omega)) hN.le
      _ ≤ R^2 := hNR
      _ ≤ (D*S)^2 := pow_le_pow_left₀ hR.le hRS 2
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right hB (sq_nonneg N)).trans hNM
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 3)).mp
    calc
      _ ≤ (C*D^7)*N^4 :=
        mul_le_mul_of_nonneg_right (hplain 3 (by omega)) (pow_nonneg hN.le 4)
      _ ≤ M*R^3 := hFour
      _ ≤ M*(D*S)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 3) hM.le
      _ = _ := by ring
  · apply (mul_le_mul_iff_right₀ (pow_pos hDpos 7)).mp
    calc
      _ ≤ (C*D^7)*N^10 :=
        mul_le_mul_of_nonneg_right (hplain 7 le_rfl) (pow_nonneg hN.le 10)
      _ ≤ M^3*R^7 := hTen
      _ ≤ M^3*(D*S)^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 7) (pow_nonneg hM.le 3)
      _ = _ := by ring

private theorem dyadic_shift_actual_family
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
    let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
    let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*y))/
            ((k:ℝ)/M)):ℂ)‖ := by
  classical
  intro S Y Bint
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hinj : Function.Injective (fun r : ℕ => (r:ℝ)/(k:ℝ)) := by
    intro r s hrs
    have hh := (div_left_inj' hkR.ne').mp hrs
    exact_mod_cast hh
  have hcard : Y.card=S.card := Finset.card_image_of_injOn hinj.injOn
  have hSk : S.card≤k := by
    calc
      _ ≤ (Finset.Ico k (2*k)).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ico]; omega
  have hfloor (r : ℕ) : ⌊(k:ℝ)*((r:ℝ)/(k:ℝ))⌋₊=r := by
    rw [show (k:ℝ)*((r:ℝ)/(k:ℝ))=(r:ℝ) by field_simp]
    exact Nat.floor_natCast r
  have hgeom := HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hkR
  refine ⟨hcard.trans_le hSk,?_,?_,?_,?_,?_,?_⟩
  · intro y hy
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    have hr' := Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
    have hh := hgeom.1 r (by exact_mod_cast hr'.1)
      (by exact_mod_cast hr'.2.le)
    constructor <;> linarith only [hh.1,hh.2]
  · intro y hy z hz hyz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    have hrs : r≠s := fun he => hyz (congrArg (fun n : ℕ => (n:ℝ)/(k:ℝ)) he)
    have hh := hgeom.2 r s hrs
    rw [show (r:ℝ)/(k:ℝ)-1-((s:ℝ)/(k:ℝ)-1)=
      (r:ℝ)/(k:ℝ)-(s:ℝ)/(k:ℝ) by ring] at hh
    exact hh
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using ha
  · intro y _
    dsimp only [Bint]
    exact_mod_cast (Nat.le_add_right a (L-⌊(k:ℝ)*y⌋₊))
  · intro y _
    apply Int.le_floor.mpr
    have hh : ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℝ)≤((a+L:ℕ):ℝ) := by
      exact_mod_cast (show a+(L-⌊(k:ℝ)*y⌋₊)≤a+L by omega)
    exact hh.trans hb
  · let f := fun r => ‖sourceShiftCorrelation F X M a L r‖
    have hRange : (∑ j∈Finset.range k,f (k+j))=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_bij (fun (j:ℕ) _ => k+j)
      case hi =>
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
      case i_inj =>
        intro j _ l _ hjl
        omega
      case i_surj =>
        intro r hr
        have hr' := Finset.mem_Ico.mp hr
        exact ⟨r-k,Finset.mem_range.mpr (by omega),by omega⟩
      case h =>
        intro j _
        rfl
    have hFilter : (∑ r∈S,f r)=∑ r∈Finset.Ico k (2*k),f r := by
      apply Finset.sum_filter_of_ne
      intro r _ hne
      by_contra hn
      exact hne (by
        dsimp only [f]
        rw [sourceShiftCorrelation_empty F X M a L r (by omega),norm_zero])
    rw [hRange,←hFilter,hcard]
    rw [Finset.sum_image hinj.injOn]
    calc
      _ ≤ ∑ r∈S,(1+‖∑ l∈Finset.Ioc (a:ℤ) (Bint ((r:ℝ)/(k:ℝ))),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*((r:ℝ)/(k:ℝ))))/
            ((k:ℝ)/M)):ℂ)‖) := by
        apply Finset.sum_le_sum
        intro r hr
        have hh := norm_sourceShiftCorrelation_le_difference_Ioc
          F X hM.ne' a L r k hk (Finset.mem_filter.mp hr).2
        dsimp only [Bint]
        rw [hfloor]
        simpa only [Expdb.oscillatory,←mul_div_assoc] using hh
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]

private theorem upper_endpoint_error_absorption
    {Y M N R : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 1≤N)
    (hR : 0<R) (hRN : R≤N) :
    Y≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) := by
  have hNp := zero_lt_one.trans_le hN
  have hratio : 1≤N/R := (one_le_div hR).mpr hRN
  have hpow : 1≤(N/R)^((2:ℝ)/3) := Real.one_le_rpow hratio (by norm_num)
  have hunit : 1≤N*(N/R)^((2:ℝ)/3) := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hN hpow zero_le_one hNp.le
  have hh : Y≤Y*N*(N/R)^((2:ℝ)/3) := by
    calc
      _ ≤ Y*(N*(N/R)^((2:ℝ)/3)) := le_mul_of_one_le_right hY hunit
      _ = _ := (mul_assoc _ _ _).symm
  have hfirst : 0≤Y*M/Real.sqrt N+Y*M*R^2/N^2 := by positivity
  exact hh.trans (le_add_of_nonneg_left hfirst)

private theorem general_expressions_nonnegative
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  refine ⟨?_, general_expression_nonnegative hY hM hN hR hJ⟩
  positivity

private theorem approximateModelPhase_enlarged_quantitative_general
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
                Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) := by
  classical
  have hσone : 0<σ+1 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+1)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+1)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσone) zero_lt_one
  have hδmodel : 0<δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+1)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,ηsrc,a,c,J,hδ,hηsrc,hηsrcCap,ha,hc,hJ,hanchor,hsource⟩ :=
    HuxleyRationalPhase.approximateModelPhase_enlarged_colored_common_scale_source
      hσ hδmodel (by norm_num : (0:ℝ)<1) 5 le_rfl
  have hanchor' : c≤4*modelPhaseThirdLower (σ+1)*1/((σ+1)*((σ+1)+1)+3) := by
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hanchor
  obtain ⟨Cbudget,ηquant,hCbudget,hηquant,_,hquant⟩ :=
    eventually_general_quantitative_phase_subinterval_bound
      (by norm_num : (0:ℝ)<1) hc hJ hσone hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let D := 2+2*σ+1/σ
  have hD : 1≤D := by
    dsimp only [D]
    have hi : 0<1/σ := div_pos zero_lt_one hσ
    linarith only [hσ,hi]
  have hDpos := zero_lt_one.trans_le hD
  have hDσ : 1≤D*σ := by
    have hi : (1/σ)*σ=1 := div_mul_cancel₀ 1 hσ.ne'
    dsimp only [D]
    nlinarith only [hi,hσ,sq_nonneg σ]
  have hσD : 2*σ≤D := by
    dsimp only [D]
    have hi : 0<1/σ := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1≤B := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ Cbudget*D^7 := mul_le_mul hCbudget (one_le_pow₀ hD)
        zero_le_one (zero_le_one.trans hCbudget)
  let Cap := 4/a+3
  have hCap : 1≤Cap := by
    dsimp only [Cap]
    have hh : 0<4/a := by positivity
    linarith only [hh]
  let K := (2*σ)^ε*D^24
  have hK : 0≤K := mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε) (pow_nonneg hDpos.le 24)
  let C := max 1 (max (Tcut/σ) (Cap^12*K))
  have hC : 1≤C := le_max_left _ _
  have hCcut : Tcut/σ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min ηsrc ηquant,B,C,hδ,lt_min hηsrc hηquant,
    (min_le_left _ _).trans hηsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_,_,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y n N R Jsep η hT hN8 hN2 hRlow hη hηcap hJsep hJsepM
    hY hsep hphase hRN hNR hNM hFour hTen A Bint hA hAB hBint Yc ErrorTotal Main
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hRp : 0<R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0<T := zero_lt_one.trans_le (hC.trans hT)
  have hYc : 0≤Yc := Nat.cast_nonneg _
  have hSigns := general_expressions_nonnegative hYc hMp.le hNp.le hRp hJsep.le
  have hError : 0≤ErrorTotal := hSigns.1
  have hMain : 0≤Main := hSigns.2
  have hMass : 0≤ErrorTotal^12+Main := add_nonneg (pow_nonneg hError 12) hMain
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ j∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖:ℂ)
  have hzNorm (U : Finset ℝ) :
      ‖∑ y∈U,z y‖ = ∑ y∈U,‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ :=
    hcolors Y id η hY hη (hηcap.trans (min_le_left _ _))
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(ErrorTotal^12+Main) := by
    obtain ⟨y₀,hy₀,_,hreg,hjets,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := σ*y₀
    have hy₀range := hY y₀ hy₀
    have hy₀p : 0<y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0<γ := mul_pos hσ hy₀p
    have hγlo : σ≤γ := le_mul_of_one_le_right hσ.le hy₀range.1
    have hγhi : γ≤2*σ := by dsimp only [γ]; nlinarith only [hy₀range.2,hσ]
    have hγD := hγhi.trans hσD
    have hDγ : 1≤D*γ := hDσ.trans (mul_le_mul_of_nonneg_left hγlo hDpos.le)
    let Fsrc := fun w => (1/(σ*y₀))*Fext w
    let Tnew := T*σ*y₀/1
    let Rnew := R*Real.sqrt (1/(σ*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ]; rw [div_one,mul_assoc]
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [mul_one] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewFour,hnewTen⟩ :=
      comparable_radius_source_budgets hMp hNp hRp hD hCbudget hSle hRle
        hRlow hRN hNR hNM hFour hTen
    have hTnewCut : Tcut≤Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hσ).mp (hCcut.trans hT)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy : y∈Yj) : y∈Y :=
      (Finset.mem_filter.mp hy).1
    have hYjColor (y : ℝ) (hy : y∈Yj) : color y=j :=
      (Finset.mem_filter.mp hy).2
    have hmod (y : ℝ) (hy : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction
          (fun u => (Fsrc u-Fsrc (u+η*y))/(1*η)) (σ+1) 4 δmodel :=
      approximateModelPhase_mono (hmodels y (hYj y hy) (hYjColor y hy)).1
        (by norm_num) le_rfl
    have hq := hTcut Tnew hTnewCut Fsrc Yj n N Rnew Jsep hN8 hN2 hRnew1
      hη (hηcap.trans (min_le_right _ _)) hJsep hJsepM
      (fun y hy => hY y (hYj y hy))
      (fun y hy v hv hne => hsep y (hYj y hy) v (hYj v hv) hne)
      hreg hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM
      hnewFour hnewTen A Bint (fun y hy => hA y (hYj y hy))
      (fun y hy => hAB y (hYj y hy)) (fun y hy => hBint y (hYj y hy))
    have hYj0 : (0:ℝ)≤Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ)≤Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ)≤(Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^11*(N:ℝ)^2/Rnew^7+
      (Yj.card:ℝ)^11*Jsep*M^11/Rnew^5+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)*Rnew^7)*(Rnew/(N:ℝ))^((2:ℝ)/3)+
      (Yj.card:ℝ)^12*M^10*(N:ℝ)/Rnew^3*(Rnew/(N:ℝ))^((2:ℝ)/3)+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)^4*Rnew^2)*(Rnew/(N:ℝ))^((2:ℝ)/3)
    have hEnew : Enew≤D^2*ErrorTotal :=
      upper_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew≤D^8*Main :=
      general_radius_main_bound hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hSle hRle
    have hNewSigns := general_expressions_nonnegative hYj0 hMp.le hNp.le hRnew hJsep.le
    have hEnew0 : 0≤Enew := hNewSigns.1
    have hMainNew0 : 0≤MainNew := hNewSigns.2
    have hEpow : Enew^12≤D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew≤D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 8≤24)) hMain)
    have hTotal : Enew^12+MainNew≤D^24*(ErrorTotal^12+Main) := by
      calc
        _ ≤ D^24*ErrorTotal^12+D^24*Main := add_le_add hEpow hMainPow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε≤(2*σ)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*σ)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj,‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*(Fsrc ((l:ℝ)/M)-Fsrc ((l:ℝ)/M+η*y))/(1*η)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        simpa only [one_mul] using ((hmodels y (hYj y hy) (hYjColor y hy)).2.1 (l:ℝ)).symm
      _ ≤ Tnew^ε*(Enew^12+MainNew) := hq
      _ ≤ ((2*σ)^ε*T^ε)*(D^24*(ErrorTotal^12+Main)) :=
        mul_le_mul hTpow hTotal (add_nonneg (pow_nonneg hEnew0 12) hMainNew0)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε)
            (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0≤K*T^ε*(ErrorTotal^12+Main) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(ErrorTotal^12+Main)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(ErrorTotal^12+Main) :=
        Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(ErrorTotal^12+Main)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 :=
      hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(ErrorTotal^12+Main))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(ErrorTotal^12+Main)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(ErrorTotal^12+Main)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm
private theorem approximateModelPhase_enlarged_general_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11*(N:ℝ)^2/R^7+K^11*K*M^11/R^5+
              K^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_quantitative_general hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L k R hT hN8 hN2 hR hk hη hKM ha hb hphase hRN hNR hNM
    hFour hTen K E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hKp : 0<K := by
    change (0:ℝ)<k
    exact_mod_cast hk
  have hT1 : 1≤X*k/M := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
  let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
  let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hA,hAB,hBint,hcorr⟩ :=
    dyadic_shift_actual_family Fext X hMp a L k hk ha hb
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYK : (Y.card:ℝ)≤K := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^11*(N:ℝ)^2/R^7+
    (Y.card:ℝ)^11*(k:ℝ)*M^11/R^5+
    (Y.card:ℝ)^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
    (Y.card:ℝ)^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
    (Y.card:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  have hEY : EY≤E := by
    have hh := upper_radius_error_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := general_radius_main_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hKp.le (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hYSigns := general_expressions_nonnegative hY0 hMp.le hNp.le hRp hKp.le
  have hSigns := general_expressions_nonnegative hKp.le hMp.le hNp.le hRp hKp.le
  have hEY0 : 0≤EY := hYSigns.1
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hMass0 : 0≤E^12+Main := add_nonneg (pow_nonneg hE0 12) hMain0
  have hMass : EY^12+MainY≤E^12+Main :=
    add_le_add (pow_le_pow_left₀ hEY0 hEY 12) hMY
  let Z := ∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 ((X*k/M)*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+((k:ℝ)/M)*y))/
      ((k:ℝ)/M)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) := by
    have hu := hupper (X*k/M) Y n N R k ((k:ℝ)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hKp hMp) hη hKp hKM hY hsep hphase
      hRN hNR hNM hFour hTen (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*(X*k/M)^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) :=
    (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hKE : K≤E := upper_endpoint_error_absorption hKp.le hMp.le hN1 hRp hRleN
  have hKpow : K^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    ((pow_le_pow_left₀ hKp.le hKE 12).trans (le_add_of_nonneg_right hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr : (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)≤K+Z :=
    hcorr.trans (add_le_add hYK le_rfl)
  calc
    _ ≤ (K+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(K^12+Z^12) := add_pow_le hKp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*(X*k/M)^ε*(E^12+Main)+C₀*(X*k/M)^ε*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add hKpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

example
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) :
    Expdb.exponentialSumAt F X M a b =
      ∑ j∈Finset.Icc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j :=
  HuxleyGeneralPhaseScratch.exponentialSumAt_eq_int_Icc F X M a b

example
    (F : ℝ → ℝ) (X M : ℝ) (a b : ℕ) (hab : a≤b) :
    ‖Expdb.exponentialSumAt F X M a b‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) (b:ℤ),Expdb.oscillatory F X M j‖ :=
  HuxleyGeneralPhaseScratch.norm_exponentialSumAt_le_int_Ioc F X M a b hab

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : M≠0)
    (a L r k : ℕ) (hk : 0<k) (hrL : r≤L) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤
      1+‖∑ j∈Finset.Ioc (a:ℤ) ((a+(L-r):ℕ):ℤ),
        Expdb.oscillatory
          (fun u => (F u-F (u+((k:ℝ)/M)*((r:ℝ)/k)))/((k:ℝ)/M))
          (X*k/M) M j‖ :=
  HuxleyGeneralPhaseScratch.norm_sourceShiftCorrelation_le_difference_Ioc F X (M:=M) hM a L r k hk hrL

example
    {Ysmall Y M N R S D : ℝ}
    (hYsmall : 0≤Ysmall) (hY : Ysmall≤Y) (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hS : 0<S) (hD : 1≤D) (hSR : S≤D*R) (hRS : R≤D*S) :
    Ysmall*M/Real.sqrt N+Ysmall*M*S^2/N^2+Ysmall*N*(N/S)^((2:ℝ)/3) ≤
      D^2*(Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.upper_radius_error_bound (Ysmall:=Ysmall) (Y:=Y) (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) hYsmall hY hM hN hR hS hD hSR hRS

example
    {γ R S D : ℝ} (hR : 0<R) (hS : 0<S) (hD : 1≤D)
    (hγD : γ≤D) (hDγ : 1≤D*γ) (hlink : γ*S^2=R^2) :
    S≤D*R ∧ R≤D*S :=
  HuxleyGeneralPhaseScratch.normalized_radius_comparable (γ:=γ) (R:=R) (S:=S) (D:=D) hR hS hD hγD hDγ hlink

example
    {M N R S D C : ℝ} (hM : 0<M) (hN : 0<N)
    (hR : 0<R) (hD : 1≤D) (hC : 1≤C)
    (hSR : S≤D*R) (hRS : R≤D*S)
    (hRlow : C*D^7≤R) (hRN : (C*D^7)*R≤N)
    (hNR : (C*D^7)*N≤R^2) (hNM : (C*D^7)*N^2≤M)
    (hFour : (C*D^7)*N^4≤M*R^3)
    (hTen : (C*D^7)*N^10≤M^3*R^7) :
    1≤S ∧ C*S≤N ∧ C*N≤S^2 ∧ C*N^2≤M ∧
      N^4≤M*S^3 ∧ N^10≤M^3*S^7 :=
  HuxleyGeneralPhaseScratch.comparable_radius_source_budgets (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) (C:=C) hM hN hR hD hC hSR hRS hRlow hRN hNR hNM hFour hTen

example
    (F : ℝ → ℝ) (X : ℝ) {M : ℝ} (hM : 0<M)
    (a L k : ℕ) (hk : 0<k) (ha : M≤(a:ℝ)) (hb : ((a+L:ℕ):ℝ)≤2*M) :
    let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
    let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
    let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
    Y.card≤k ∧
      (∀ y∈Y, y∈Icc (1:ℝ) 2) ∧
      (∀ y∈Y, ∀ z∈Y, y≠z → 1≤(k:ℝ)*|y-z|) ∧
      ⌈M⌉≤(a:ℤ) ∧ (∀ y∈Y, (a:ℤ)≤Bint y) ∧
      (∀ y∈Y, Bint y≤⌊2*M⌋) ∧
      (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) ≤
        (Y.card:ℝ)+∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
          (𝐞 ((X*k/M)*(F ((l:ℝ)/M)-F ((l:ℝ)/M+((k:ℝ)/M)*y))/
            ((k:ℝ)/M)):ℂ)‖ :=
  HuxleyGeneralPhaseScratch.dyadic_shift_actual_family F X (M:=M) hM a L k hk ha hb

example
    {Y M N R : ℝ} (hY : 0≤Y) (hM : 0≤M) (hN : 1≤N)
    (hR : 0<R) (hRN : R≤N) :
    Y≤Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.upper_endpoint_error_absorption (Y:=Y) (M:=M) (N:=N) (R:=R) hY hM hN hR hRN

example
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0 ≤ Y^11*M^11*N^2/R^7+Y^11*J*M^11/R^5+
      Y^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      Y^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.general_expressions_nonnegative (Y:=Y) (M:=M) (N:=N) (R:=R) (J:=J) hY hM hN hR hJ

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^11*(N:ℝ)^2/R^7+Yc^11*Jsep*M^11/R^5+
                Yc^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_quantitative_general (σ:=σ) (ε:=ε) hσ hε

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^11*(N:ℝ)^2/R^7+K^11*K*M^11/R^5+
              K^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_general_correlation_moment (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyGeneralPhaseScratch.exponentialSumAt_eq_int_Icc
#print axioms HuxleyGeneralPhaseScratch.norm_exponentialSumAt_le_int_Ioc
#print axioms HuxleyGeneralPhaseScratch.norm_sourceShiftCorrelation_le_difference_Ioc
#print axioms HuxleyGeneralPhaseScratch.upper_radius_error_bound
#print axioms HuxleyGeneralPhaseScratch.normalized_radius_comparable
#print axioms HuxleyGeneralPhaseScratch.comparable_radius_source_budgets
#print axioms HuxleyGeneralPhaseScratch.dyadic_shift_actual_family
#print axioms HuxleyGeneralPhaseScratch.upper_endpoint_error_absorption
#print axioms HuxleyGeneralPhaseScratch.general_expressions_nonnegative
#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_quantitative_general
#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_general_correlation_moment

private theorem nonnegative_doubled_block_selection
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.Icc 1 (H/2)).exists_max_image
    (fun k => ∑ j∈Finset.range k,f (k+j))
    (by exact ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩)
  have hk' := Finset.mem_Icc.mp hk
  have hnorm (s : Finset ℕ) (g : ℕ → ℕ) :
      ‖∑ j∈s,(f (g j):ℂ)‖=∑ j∈s,f (g j) := by
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun j _ => hf (g j)))
  have hbound := norm_prefix_le_doubled_blocks
    (fun n => (f n:ℂ)) H (Nat.clog 2 H) H
    (congrArg (fun x : ℝ => (x:ℂ)) hf₀) le_rfl (Nat.le_pow_clog (by norm_num) H)
    A (∑ j∈Finset.range k,f (k+j)) hA
    (Finset.sum_nonneg (fun j _ => hf (k+j)))
    (fun n hn => (Complex.norm_of_nonneg (hf n)).le.trans (hcap n hn))
    (fun l hl hlH => by
      rw [hnorm (Finset.range l) (fun j => l+j)]
      exact hmax l (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  have he : ‖∑ n∈Finset.range H,(f n:ℂ)‖ = ∑ n∈Finset.range H,f n :=
    hnorm (Finset.range H) id
  rw [he] at hbound
  exact ⟨k,by omega,by omega,hbound⟩

private theorem norm_sourceShiftCorrelation_le_length
    (F : ℝ → ℝ) (X M : ℝ) (a L r : ℕ) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤ (L:ℝ)+1 := by
  unfold sourceShiftCorrelation
  calc
    _ ≤ ∑ j∈Finset.range (L+1-r),
        ‖star (Expdb.oscillatory F X M ((a:ℝ)+j))*
          Expdb.oscillatory F X M ((a:ℝ)+j+r)‖ := norm_sum_le _ _
    _ = (L+1-r:ℕ) := by simp
    _ ≤ (L:ℝ)+1 := by exact_mod_cast (Nat.sub_le (L+1) r)

private theorem weyl_prefix_twenty_fourth_power
    {S All B M H L C : ℝ} (hM : 0 < M) (hH : 0 < H)
    (hAll : 0 ≤ All) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hLM : L ≤ 2*M) (hHM : H ≤ M)
    (hWeyl : H^2*S^2 ≤ (L+H)*(H*L+2*H*All))
    (hPrefix : All ≤ C*(L+B)) :
    S^24 ≤ (18:ℝ)^12*(2:ℝ)^11*C^12*
      ((M^2/H)^12+(M/H)^12*B^12) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hRight : 0 ≤ H*L+2*H*All := by positivity
  have hAllBound : All ≤ C*(2*M+B) :=
    hPrefix.trans (mul_le_mul_of_nonneg_left (add_le_add hLM le_rfl) hC0)
  have hraw : H^2*S^2 ≤ 18*H*C*(M^2+M*B) := by
    calc
      _ ≤ (L+H)*(H*L+2*H*All) := hWeyl
      _ ≤ (3*M)*(H*L+2*H*All) :=
        mul_le_mul_of_nonneg_right (by linarith only [hLM,hHM]) hRight
      _ ≤ (3*M)*(2*H*M+2*H*C*(2*M+B)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ H*(2*M)+2*H*(C*(2*M+B)) :=
            add_le_add (mul_le_mul_of_nonneg_left hLM hH.le)
              (mul_le_mul_of_nonneg_left hAllBound (by positivity))
          _ = _ := by ring
      _ ≤ _ := by
        nlinarith only [
          mul_nonneg (show 0 ≤ H*M^2 by positivity) (sub_nonneg.mpr hC),
          mul_nonneg (show 0 ≤ H*C*M by positivity) hB]
  have hSquare : S^2 ≤ 18*C*(M^2/H+(M/H)*B) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
    calc
      _ ≤ 18*H*C*(M^2+M*B) := hraw
      _ = _ := by field_simp
  calc
    _ = (S^2)^12 := by ring
    _ ≤ (18*C*(M^2/H+(M/H)*B))^12 := pow_le_pow_left₀ (sq_nonneg S) hSquare 12
    _ = (18:ℝ)^12*C^12*(M^2/H+(M/H)*B)^12 := by ring
    _ ≤ (18:ℝ)^12*C^12*(2^11*((M^2/H)^12+((M/H)*B)^12)) :=
      mul_le_mul_of_nonneg_left (add_pow_le (by positivity) (by positivity) 12) (by positivity)
    _ = _ := by ring

private theorem source_correlation_doubled_block
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖) ≤
        (Nat.clog 2 H:ℝ)*((L:ℝ)+1+
          ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) := by
  classical
  let f := fun r : ℕ => if r=0 then 0 else ‖sourceShiftCorrelation F X M a L r‖
  have hf₀ : f 0=0 := by simp only [f,if_pos rfl]
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hcap (r : ℕ) : f r ≤ (L:ℝ)+1 := by
    dsimp only [f]
    split_ifs
    · positivity
    · exact norm_sourceShiftCorrelation_le_length F X M a L r
  obtain ⟨k,hk,hkH,hs⟩ := nonnegative_doubled_block_selection f H hH hf₀ hf
    (show 0 ≤ (L:ℝ)+1 by positivity) (fun r _ => hcap r)
  have hfilt : (∑ r∈(Finset.range H).filter (fun r => 0<r),f r) =
      ∑ r∈Finset.range H,f r := by
    apply Finset.sum_filter_of_ne
    intro r _ hne
    by_contra hn
    have hr : r=0 := by omega
    subst r
    exact hne hf₀
  have hset : (Finset.range H).filter (fun r => 0<r) = Finset.Icc 1 (H-1) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  have hall : (∑ r∈Finset.range H,f r) =
      ∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖ := by
    rw [←hfilt,hset]
    apply Finset.sum_congr rfl
    intro r hr
    exact if_neg (by have := (Finset.mem_Icc.mp hr).1; omega)
  have hblock : (∑ j∈Finset.range k,f (k+j)) =
      ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖ := by
    apply Finset.sum_congr rfl
    intro j _
    exact if_neg (by omega)
  rw [hall,hblock] at hs
  exact ⟨k,hk,hkH,hs⟩

private theorem exists_source_dyadic_twenty_fourth_power
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hM : 0 < M)
    (hH : 2 ≤ H) (hHM : (H:ℝ) ≤ M) (hLM : (L:ℝ)+1 ≤ 2*M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖Expdb.exponentialSumAt F X M a (a+L)‖^24 ≤
        (18:ℝ)^12*(2:ℝ)^11*(Nat.clog 2 H:ℝ)^12*
          ((M^2/(H:ℝ))^12+(M/(H:ℝ))^12*
            (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖)^12) := by
  obtain ⟨k,hk,hkH,hs⟩ := source_correlation_doubled_block F X M a L H hH
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hclog : 1 ≤ Nat.clog 2 H := by
    have hh := Nat.le_pow_clog (by norm_num : 1<2) H
    by_contra hn
    have hz : Nat.clog 2 H=0 := by omega
    rw [hz,pow_zero] at hh
    omega
  have hC : (1:ℝ) ≤ Nat.clog 2 H := by exact_mod_cast hclog
  have hw := source_exponentialSum_weyl F X M a L H
  simp only [Nat.cast_add,Nat.cast_one] at hw
  exact ⟨k,hk,hkH,weyl_prefix_twenty_fourth_power hM hHpos
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by positivity) hC hLM hHM hw hs⟩

private theorem upper_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K*M/Real.sqrt N)^36=K^36*M^36/N^18 ∧
    (K*M*R^2/N^2)^36=M^180/(X^36*N^108) ∧
    (K*N*(N/R)^((2:ℝ)/3))^36=X^12*K^48*N^72/M^48 ∧
    (K^11*M^11/(N*R^2))^3=X^3*K^36*M^21 ∧
    (K^11*K*M^11/N^3)^3=K^36*M^33/N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3=
      X^2*K^38*M^28/N^12 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hCubic : K*M*R^2/N^2=M^5/(X*N^3) := by
    rw [hR2]
    field_simp
  have hTypeOne : K^11*M^11/(N*R^2)=X*K^12*M^7 := by
    rw [hR2]
    field_simp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hsqrt : (Real.sqrt N)^36=N^18 := by
      calc
        _ = ((Real.sqrt N)^2)^18 := by rw [←pow_mul]
        _ = N^18 := by rw [Real.sq_sqrt hN.le]
    rw [div_pow,mul_pow,hsqrt]
  · rw [hCubic]
    simp only [div_pow,mul_pow,←pow_mul]
  · rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (div_nonneg hN.le hR.le),
      show ((2:ℝ)/3)*((36:ℕ):ℝ)=((24:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow]
    rw [show R^24=(R^2)^12 by rw [←pow_mul],hR2]
    field_simp
  · rw [hTypeOne]
    simp only [mul_pow,←pow_mul]
  · simp only [mul_pow,div_pow,←pow_mul]
    ring
  · rw [mul_pow,←Real.rpow_mul_natCast (div_nonneg hR.le hN.le),
      show ((2:ℝ)/3)*((3:ℕ):ℝ)=((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast,div_pow,
      hR2]
    field_simp
    nlinarith only [(eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mp hR2]

private theorem upper_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^11/(N*R^2))^3≤X^3*M^57 ∧
    (M/H)^36*(K^11*K*M^11/N^3)^3≤M^69/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    upper_correlation_integer_moments hX hM hN hK hR hscale
  rw [h₁,h₂,h₃,h₄,h₅,h₆]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (M/H)^36*(H^36*M^36/N^18) := by gcongr
      _ = _ := by field_simp
  · exact le_of_eq (by field_simp)
  · calc
      _ ≤ (M/H)^36*(X^12*H^48*N^72/M^48) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^3*H^36*M^21) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(H^36*M^33/N^9) := by gcongr
      _ = _ := by field_simp
  · calc
      _ ≤ (M/H)^36*(X^2*H^38*M^28/N^12) := by gcongr
      _ = _ := by field_simp

private theorem three_term_power_bound
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) := by
  let D := (2:ℝ)^(n-1)
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have hDpow : D^2≤(2:ℝ)^(2*n) := by
    dsimp only [D]
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ D*((a+b)^n+c^n) := add_pow_le (add_nonneg ha hb) hc n
    _ ≤ D*(D*(a^n+b^n)+D*c^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_pow_le ha hb n)
          (le_mul_of_one_le_left (pow_nonneg hc n) hD)) hD0
    _ = D^2*(a^n+b^n+c^n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDpow
      (add_nonneg (add_nonneg (pow_nonneg ha n) (pow_nonneg hb n)) (pow_nonneg hc n))

private theorem upper_all_shift_polynomial_budgets
    {X M N K H R B : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 1≤K) (hR : 0<R)
    (hB : 1≤B) (hKH : K≤H) (hBN : B≤N)
    (hscale : (X*K/M)*N*R^2=M^3)
    (hRN : B^2*M^4≤X*N^3) (hNR : B*X*H*N^2≤M^4)
    (hNM : B*N^2≤M)
    (hFour : B^2*X^3*H^3*N^11≤M^14)
    (hTen : B^2*X^7*H^7*N^27≤M^34) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N^2≤M ∧
      B*N^4≤M*R^3 ∧ B*N^10≤M^3*R^7 := by
  have hKp := zero_lt_one.trans_le hK
  have hHp := hKp.trans_le hKH
  have hBp := zero_lt_one.trans_le hB
  have hDen : 0<X*K*N := mul_pos (mul_pos hX hKp) hN
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff hDen.ne').mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hNR' : B*N≤R^2 := by
    rw [hR2]
    apply (le_div_iff₀ hDen).mpr
    calc
      _ = B*X*K*N^2 := by ring
      _ ≤ B*X*H*N^2 := by gcongr
      _ ≤ M^4 := hNR
  refine ⟨?_,?_,hNR',hNM,?_,?_⟩
  · apply (sq_le_sq₀ hBp.le hR.le).mp
    calc
      B^2 = B*B := pow_two B
      _ ≤ B*N := mul_le_mul_of_nonneg_left hBN hBp.le
      _ ≤ R^2 := hNR'
  · apply (sq_le_sq₀ (mul_nonneg hBp.le hR.le) hN.le).mp
    rw [mul_pow,hR2,←mul_div_assoc]
    apply (div_le_iff₀ hDen).mpr
    calc
      _ ≤ X*N^3 := hRN
      _ ≤ K*(X*N^3) := le_mul_of_one_le_left (by positivity) hK
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 4))
      (mul_nonneg hM.le (pow_nonneg hR.le 3))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^6=(R^2)^3 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 3)).mpr
    calc
      _ = B^2*X^3*K^3*N^11 := by ring
      _ ≤ B^2*X^3*H^3*N^11 := by gcongr
      _ ≤ M^14 := hFour
      _ = _ := by ring
  · apply (sq_le_sq₀ (mul_nonneg hBp.le (pow_nonneg hN.le 10))
      (mul_nonneg (pow_nonneg hM.le 3) (pow_nonneg hR.le 7))).mp
    simp only [mul_pow,←pow_mul]
    rw [show R^14=(R^2)^7 by rw [←pow_mul],hR2,div_pow,←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDen 7)).mpr
    calc
      _ = B^2*X^7*K^7*N^27 := by ring
      _ ≤ B^2*X^7*H^7*N^27 := by gcongr
      _ ≤ M^34 := hTen
      _ = _ := by ring

private theorem floor_power_scales
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V := by
  intro n N H
  have hn4 : 4≤n := Nat.le_floor (by linarith only [hU] : (4:ℝ)≤U/8)
  have hH4 : 4≤H := Nat.le_floor hV
  have hNcast : (N:ℝ)=8*(n:ℝ) := by simp only [N,Nat.cast_mul,Nat.cast_ofNat]
  have hnlo : U/8<(n:ℝ)+1 := Nat.lt_floor_add_one (U/8)
  have hnhi : (n:ℝ)≤U/8 := Nat.floor_le (by linarith only [hU])
  have hHlo : V<(H:ℝ)+1 := Nat.lt_floor_add_one V
  have hHhi : (H:ℝ)≤V := Nat.floor_le (by linarith only [hV])
  refine ⟨by dsimp only [N]; omega,by omega,?_,?_,?_,hHhi⟩
  · rw [hNcast]
    linarith only [hnlo,hU]
  · rw [hNcast]
    linarith only [hnhi]
  · linarith only [hHlo,hV]

private theorem eventually_upper_polynomial_power_window
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 := by
  have hB0 := zero_le_one.trans hB
  have hC0 := zero_le_one.trans hC
  have hNpow : ∀ᶠ X : ℝ in Filter.atTop, 32≤X^ν :=
    (tendsto_rpow_atTop hν).eventually_ge_atTop 32
  have hHpow : ∀ᶠ X : ℝ in Filter.atTop, 4≤X^h :=
    (tendsto_rpow_atTop hh).eventually_ge_atTop 4
  have hBNdom := eventually_const_mul_rpow_le_rpow (D:=2*B) (a:=0) hν
  have hRNdom := eventually_const_mul_rpow_le_rpow (D:=8*B^2) hRN
  have hNRdom := eventually_const_mul_rpow_le_rpow (D:=B) hNR
  have hNMdom := eventually_const_mul_rpow_le_rpow (D:=B) hNM
  have hFourdom := eventually_const_mul_rpow_le_rpow (D:=B^2) hFour
  have hTendom := eventually_const_mul_rpow_le_rpow (D:=B^2) hTen
  have hEtadom := eventually_const_mul_rpow_le_rpow (D:=1/η) hhℓ
  have hThreshold := eventually_const_mul_rpow_le_rpow (D:=C) hu
  filter_upwards [hNpow,hHpow,hBNdom,hRNdom,hNRdom,hNMdom,hFourdom,hTendom,
    hEtadom,hThreshold,Filter.eventually_ge_atTop (1:ℝ)] with
    X hNU hHU hBNX hRNX hNRX hNMX hFourX hTenX hEtaX hThresholdX hX
  refine ⟨hX,?_⟩
  intro M hMl hMu n N H
  have hXp := zero_lt_one.trans_le hX
  have hM1 : 1≤M := (Real.one_le_rpow hX hℓ.le).trans hMl
  have hMp := zero_lt_one.trans_le hM1
  obtain ⟨hN2,hH2,hNl,hNu,hHl,hHu⟩ := floor_power_scales hNU hHU
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hp (q : ℝ) (m : ℕ) : (X^q)^m=X^((m:ℝ)*q) := by
    simpa only [mul_comm] using (Real.rpow_mul_natCast hXp.le q m).symm
  refine ⟨hM1,hN2,hH2,hNl,hNu,hHl,hHu,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have he : X^h≤η*X^ℓ := by
      have hh' := mul_le_mul_of_nonneg_left hEtaX hη.le
      simpa [one_div,←mul_assoc,hη.ne'] using hh'
    exact hHu.trans (he.trans (mul_le_mul_of_nonneg_left hMl hη.le))
  · apply (le_div_iff₀ hMp).mpr
    calc
      _ ≤ C*X^u := mul_le_mul_of_nonneg_left hMu hC0
      _ ≤ X^1 := hThresholdX
      _ = X := Real.rpow_one X
  · have he : 2*B≤X^ν := by simpa only [Real.rpow_zero,mul_one] using hBNX
    change B≤(N:ℝ)
    linarith only [he,hNl]
  · have hlow : B^2*(X^u)^4≤X*(X^ν/2)^3 := by
      apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<8)).mp
      calc
        _ = (8*B^2)*X^(4*u) := by rw [hp]; norm_num only [Nat.cast_ofNat]; ring
        _ ≤ X^(1+3*ν) := hRNX
        _ = _ := by
          rw [div_pow,hp,Real.rpow_add hXp,Real.rpow_one]
          norm_num only [Nat.cast_ofNat]
          field_simp
    calc
      _ ≤ B^2*(X^u)^4 := by gcongr
      _ ≤ X*(X^ν/2)^3 := hlow
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*X*(X^h)*(X^ν)^2 := by gcongr
      _ = B*(X^(1:ℝ)*(X^h)*(X^ν)^2) := by rw [Real.rpow_one]; ring
      _ = B*X^(1+h+2*ν) := by
        rw [hp]
        norm_num only [Nat.cast_ofNat]
        rw [←Real.rpow_add hXp,←Real.rpow_add hXp]
      _ ≤ X^(4*ℓ) := hNRX
      _ = (X^ℓ)^4 := by simpa only [Nat.cast_ofNat] using (hp ℓ 4).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B*(X^ν)^2 := by gcongr
      _ = B*X^(2*ν) := by rw [hp]; norm_num only [Nat.cast_ofNat]
      _ ≤ X^ℓ := hNMX
      _ ≤ M := hMl
  · calc
      _ ≤ B^2*X^3*(X^h)^3*(X^ν)^11 := by gcongr
      _ = B^2*X^(3+3*h+11*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 3]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(14*ℓ) := hFourX
      _ = (X^ℓ)^14 := by simpa only [Nat.cast_ofNat] using (hp ℓ 14).symm
      _ ≤ _ := by gcongr
  · calc
      _ ≤ B^2*X^7*(X^h)^7*(X^ν)^27 := by gcongr
      _ = B^2*X^(7+7*h+27*ν) := by
        rw [hp,hp,←Real.rpow_natCast X 7]
        norm_num only [Nat.cast_ofNat]
        simp only [mul_assoc,←Real.rpow_add hXp]
      _ ≤ X^(34*ℓ) := hTenX
      _ = (X^ℓ)^34 := by simpa only [Nat.cast_ofNat] using (hp ℓ 34).symm
      _ ≤ _ := by gcongr

private theorem general_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^11*N^2/R^7)^6=X^21*K^87*N^33/M^18 ∧
    (K^11*K*M^11/R^5)^6=X^15*K^87*M^6*N^15 ∧
    (K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6=X^19*K^91*N^9/M^4 ∧
    (K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6=X^7*K^79*M^32*N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6=X^4*K^76*M^56/N^24 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  have hR42 : R^42=(R^2)^21 := by rw [←pow_mul]
  have hR30 : R^30=(R^2)^15 := by rw [←pow_mul]
  have hR18 : R^18=(R^2)^9 := by rw [←pow_mul]
  have hR12 : R^12=(R^2)^6 := by rw [←pow_mul]
  have hR4 : R^4=(R^2)^2 := by rw [←pow_mul]
  have hFrac : ((R/N)^((2:ℝ)/3))^6=(R/N)^4 := by
    rw [←Real.rpow_mul_natCast (div_nonneg hR.le hN.le)]
    norm_num
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [hR42,hR2]
    field_simp
    ac_rfl
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [hR30,hR2]
    field_simp
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR42,hR4,hR2]
    field_simp
    ac_rfl
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR18,hR4,hR2]
    field_simp
    ac_rfl
  · rw [mul_pow,hFrac]
    simp only [mul_pow,div_pow,←pow_mul]
    rw [hR12,hR4,hR2]
    field_simp
    ring

private theorem general_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^72*(K*M/Real.sqrt N)^72≤M^144/N^36 ∧
    (M/H)^72*(K*M*R^2/N^2)^72≤M^432/(H^72*X^72*N^216) ∧
    (M/H)^72*(K*N*(N/R)^((2:ℝ)/3))^72≤X^24*H^24*N^144/M^24 ∧
    (M/H)^72*(K^11*M^11*N^2/R^7)^6≤X^21*H^15*M^54*N^33 ∧
    (M/H)^72*(K^11*K*M^11/R^5)^6≤X^15*H^15*M^78*N^15 ∧
    (M/H)^72*(K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6≤X^19*H^19*M^68*N^9 ∧
    (M/H)^72*(K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6≤X^7*H^7*M^104*N^9 ∧
    (M/H)^72*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6≤X^4*H^4*M^128/N^24 := by
  obtain ⟨he₁,he₂,he₃,_,_,_⟩ :=
    upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := general_correlation_integer_moments hX hM hN hK hR hscale
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₁ 2
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₂ 2
  · simpa only [mul_pow,div_pow,←pow_mul] using
      pow_le_pow_left₀ (by positivity) he₃ 2
  · rw [h₁]
    calc
      _ ≤ (M/H)^72*(X^21*H^87*N^33/M^18) := by gcongr
      _ = _ := by field_simp
  · rw [h₂]
    calc
      _ ≤ (M/H)^72*(X^15*H^87*M^6*N^15) := by gcongr
      _ = _ := by field_simp
  · rw [h₃]
    calc
      _ ≤ (M/H)^72*(X^19*H^91*N^9/M^4) := by gcongr
      _ = _ := by field_simp
  · rw [h₄]
    calc
      _ ≤ (M/H)^72*(X^7*H^79*M^32*N^9) := by gcongr
      _ = _ := by field_simp
  · rw [h₅]
    calc
      _ ≤ (M/H)^72*(X^4*H^76*M^56/N^24) := by gcongr
      _ = _ := by field_simp


private theorem five_term_power_bound
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (n : ℕ) :
    (a+b+c+d+e)^n ≤ (2:ℝ)^(4*n)*(a^n+b^n+c^n+d^n+e^n) := by
  let D := (2:ℝ)^(2*n)
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD0 := zero_le_one.trans hD
  have habc := three_term_power_bound ha hb hc n
  have habc0 : 0 ≤ a+b+c := add_nonneg (add_nonneg ha hb) hc
  calc
    _ ≤ D*((a+b+c)^n+d^n+e^n) := three_term_power_bound habc0 hd he n
    _ ≤ D*(D*(a^n+b^n+c^n)+D*d^n+D*e^n) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add habc (le_mul_of_one_le_left (pow_nonneg hd n) hD))
          (le_mul_of_one_le_left (pow_nonneg he n) hD)) hD0
    _ = (D*D)*(a^n+b^n+c^n+d^n+e^n) := by ring
    _ = _ := by
      dsimp only [D]
      rw [←pow_add]
      congr 2
      omega

private theorem weighted_general_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^72*(E^72+Main^6)≤(2:ℝ)^144*
      ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
        (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
          X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24)) := by
  intro E Main
  let e₁ := K*M/Real.sqrt N
  let e₂ := K*M*R^2/N^2
  let e₃ := K*N*(N/R)^((2:ℝ)/3)
  let a₁ := K^11*M^11*N^2/R^7
  let a₂ := K^11*K*M^11/R^5
  let a₃ := K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)
  let a₄ := K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)
  let a₅ := K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  have he₁ : 0 ≤ e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0 ≤ e₃ := by dsimp only [e₃]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0 ≤ a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0 ≤ a₃ := by dsimp only [a₃]; positivity
  have ha₄ : 0 ≤ a₄ := by dsimp only [a₄]; positivity
  have ha₅ : 0 ≤ a₅ := by dsimp only [a₅]; positivity
  have hE : E^72≤(2:ℝ)^144*(e₁^72+e₂^72+e₃^72) :=
    three_term_power_bound he₁ he₂ he₃ 72
  have hMain : Main^6≤(2:ℝ)^144*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6) :=
    (five_term_power_bound ha₁ ha₂ ha₃ ha₄ ha₅ 6).trans
      (mul_le_mul_of_nonneg_right (by norm_num)
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg
          (pow_nonneg ha₁ 6) (pow_nonneg ha₂ 6)) (pow_nonneg ha₃ 6))
          (pow_nonneg ha₄ 6)) (pow_nonneg ha₅ 6)))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩ :=
    general_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  have hW : 0≤(M/H)^72 := pow_nonneg (div_nonneg hM.le hH.le) 72
  calc
    _ ≤ (M/H)^72*((2:ℝ)^144*(e₁^72+e₂^72+e₃^72)+
        (2:ℝ)^144*(a₁^6+a₂^6+a₃^6+a₄^6+a₅^6)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^144*(((M/H)^72*e₁^72+(M/H)^72*e₂^72+(M/H)^72*e₃^72)+
        ((M/H)^72*a₁^6+(M/H)^72*a₂^6+(M/H)^72*a₃^6+(M/H)^72*a₄^6+
          (M/H)^72*a₅^6)) := by
      simp only [mul_add]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃)
        (add_le_add (add_le_add (add_le_add (add_le_add h₄ h₅) h₆) h₇) h₈))
      (by norm_num)


private theorem general_weyl_one_hundred_forty_fourth_bound
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^144≤(2:ℝ)^154*A^6*C^6*L^72*X^(6*ε)*
      (M^144/H^72+
        ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
          (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
            X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) := by
  intro E Main hCorr hWeyl
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hSigns := general_expressions_nonnegative hK.le hM.le hN.le hR hK.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  let V := (M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
    (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
      X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24)
  have hV0 : 0≤V := by dsimp only [V]; positivity
  have hW0 : 0≤(M/H)^72 := pow_nonneg (div_nonneg hM.le hH.le) 72
  have hTpow : 0≤X^(6*ε) := Real.rpow_nonneg hXp.le _
  have hTpowOne : 1≤X^(6*ε) := Real.one_le_rpow hX (mul_nonneg (by norm_num) hε)
  have hXpSix : (X^ε)^6=X^(6*ε) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num [mul_comm]
  have hSix : S^144≤A^6*L^72*((M^2/H)^12+(M/H)^12*Z^12)^6 := by
    simpa only [mul_pow,←pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hS 24) hWeyl 6
  have hAdd : ((M^2/H)^12+(M/H)^12*Z^12)^6≤
      32*(M^144/H^72+(M/H)^72*Z^72) := by
    simpa only [div_pow,mul_pow,←pow_mul,show (2:ℝ)^(6-1)=32 by norm_num] using
      add_pow_le (by positivity : 0≤(M^2/H)^12)
        (by positivity : 0≤(M/H)^12*Z^12) 6
  have hSmain : S^144≤32*A^6*L^72*(M^144/H^72+(M/H)^72*Z^72) := by
    calc
      _ ≤ A^6*L^72*((M^2/H)^12+(M/H)^12*Z^12)^6 := hSix
      _ ≤ A^6*L^72*(32*(M^144/H^72+(M/H)^72*Z^72)) :=
        mul_le_mul_of_nonneg_left hAdd (mul_nonneg (pow_nonneg hA 6) (pow_nonneg hL 72))
      _ = _ := by ac_rfl
  have hZSix : Z^72≤C^6*X^(6*ε)*(E^12+Main)^6 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hZ 12) hCorr 6
    simpa only [mul_pow,←pow_mul,hXpSix] using hh
  have hEM : (E^12+Main)^6≤32*(E^72+Main^6) := by
    simpa only [←pow_mul,show (2:ℝ)^(6-1)=32 by norm_num] using
      add_pow_le (pow_nonneg hE0 12) hMain0 6
  have hZMoment : Z^72≤32*C^6*X^(6*ε)*(E^72+Main^6) := by
    calc
      _ ≤ C^6*X^(6*ε)*(E^12+Main)^6 := hZSix
      _ ≤ C^6*X^(6*ε)*(32*(E^72+Main^6)) :=
        mul_le_mul_of_nonneg_left hEM (mul_nonneg (pow_nonneg hC0 6) hTpow)
      _ = _ := by ac_rfl
  have hWeighted : (M/H)^72*(E^72+Main^6)≤(2:ℝ)^144*V :=
    weighted_general_integer_moment_bound hXp hM hN hK hH hR hKH hscale
  let Q := (2:ℝ)^149*C^6*X^(6*ε)
  have hQ : 1≤Q := by
    calc
      _ ≤ C^6 := one_le_pow₀ hC
      _ ≤ C^6*X^(6*ε) := le_mul_of_one_le_right (pow_nonneg hC0 6) hTpowOne
      _ ≤ (2:ℝ)^149*(C^6*X^(6*ε)) :=
        le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC0 6) hTpow) (by norm_num)
      _ = Q := (mul_assoc _ _ _).symm
  have hScaledZ : (M/H)^72*Z^72≤Q*V := by
    calc
      _ ≤ (M/H)^72*(32*C^6*X^(6*ε)*(E^72+Main^6)) :=
        mul_le_mul_of_nonneg_left hZMoment hW0
      _ = (32*C^6*X^(6*ε))*((M/H)^72*(E^72+Main^6)) := by ac_rfl
      _ ≤ (32*C^6*X^(6*ε))*((2:ℝ)^144*V) :=
        mul_le_mul_of_nonneg_left hWeighted
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 6)) hTpow)
      _ = Q*V := by
        dsimp only [Q]
        rw [show (2:ℝ)^149=32*2^144 by norm_num]
        ac_rfl
  have hDiag : M^144/H^72≤Q*(M^144/H^72) :=
    le_mul_of_one_le_left (by positivity) hQ
  calc
    _ ≤ 32*A^6*L^72*(M^144/H^72+(M/H)^72*Z^72) := hSmain
    _ ≤ 32*A^6*L^72*(Q*(M^144/H^72)+Q*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hScaledZ)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 6)) (pow_nonneg hL 72))
    _ = _ := by
      rw [←mul_add]
      dsimp only [Q,V]
      rw [show (2:ℝ)^154=32*2^149 by norm_num]
      ac_rfl


private theorem sharp_extension_power_bound_144
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^144≤D*W*P) :
    ‖u‖^144≤(2:ℝ)^143*(D+E^144)*W*(1+P) := by
  have hW0 := zero_le_one.trans hW
  have hu : ‖u‖≤‖v‖+E := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ ‖v‖+‖u-v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsharp
  have hErr : E^144≤E^144*W :=
    le_mul_of_one_le_right (pow_nonneg hE 144) hW
  have hFold : D*W*P+E^144*W≤(D+E^144)*W*(1+P) := by
    nlinarith only [mul_nonneg hD hW0,
      mul_nonneg (mul_nonneg (pow_nonneg hE 144) hW0) hP]
  calc
    _ ≤ (‖v‖+E)^144 := pow_le_pow_left₀ (norm_nonneg _) hu 144
    _ ≤ (2:ℝ)^143*(‖v‖^144+E^144) := add_pow_le (norm_nonneg _) hE 144
    _ ≤ (2:ℝ)^143*(D*W*P+E^144*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hErr) (by norm_num)
    _ ≤ (2:ℝ)^143*((D+E^144)*W*(1+P)) :=
      mul_le_mul_of_nonneg_left hFold (by norm_num)
    _ = _ := by ac_rfl

private theorem approximateModelPhase_general_original_one_hundred_forty_fourth
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^144 ≤
          C*(1+(Nat.clog 2 H:ℝ))^72*X^(6*ε)*
            (1+(M^144/(H:ℝ)^72+
              ((M^144/(N:ℝ)^36+M^432/((H:ℝ)^72*X^72*(N:ℝ)^216)+
                  X^24*(H:ℝ)^24*(N:ℝ)^144/M^24)+
                (X^21*(H:ℝ)^15*M^54*(N:ℝ)^33+X^15*(H:ℝ)^15*M^78*(N:ℝ)^15+
                  X^19*(H:ℝ)^19*M^68*(N:ℝ)^9+X^7*(H:ℝ)^7*M^104*(N:ℝ)^9+
                  X^4*(H:ℝ)^4*M^128/(N:ℝ)^24)))) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_general_correlation_moment hσ hε
  let A₀ := (18:ℝ)^12*(2:ℝ)^11
  have hA₀ : 0≤A₀ := by dsimp only [A₀]; norm_num
  let D := (2:ℝ)^154*A₀^6*C₀^6
  have hD : 0≤D := mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hA₀ 6)) (pow_nonneg (zero_le_one.trans hC₀) 6)
  let C := max C₀ ((2:ℝ)^143*(D+6^144))
  have hCC₀ : C₀≤C := le_max_left _ _
  have hCoeff : (2:ℝ)^143*(D+6^144)≤C := le_max_right _ _
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro X M F n N H a L hX hM hF hN8 hN2 hH2 hHeta hThreshold
    hBN hRN hNR hNM hFour hTen ha hb
  have hXp := zero_lt_one.trans_le hX
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHM : (H:ℝ)≤M := by
    calc
      _ ≤ η₀*M := hHeta
      _ ≤ (1:ℝ)*M := mul_le_mul_of_nonneg_right
        (hηcap.trans (by norm_num : (1:ℝ)/8≤1)) hMp.le
      _ = M := one_mul M
  have hLM : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [hb',ha,hM]
  obtain ⟨Fext,hsharp,hcorr⟩ := hsource M F hM hF
  obtain ⟨k,hk,hkH,hweyl⟩ := exists_source_dyadic_twenty_fourth_power
    Fext X M a L H hMp hH2 hHM hLM
  have hKp : (0:ℝ)<k := by exact_mod_cast hk
  have hK1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hKH : (k:ℝ)≤H := by exact_mod_cast (show k≤H by omega)
  have hKM : (k:ℝ)≤M := hKH.trans hHM
  let R := Real.sqrt (M^4/(X*(k:ℝ)*(N:ℝ)))
  have hRadicand : 0<M^4/(X*(k:ℝ)*(N:ℝ)) :=
    div_pos (pow_pos hMp 4) (mul_pos (mul_pos hXp hKp) hNp)
  have hRp : 0<R := Real.sqrt_pos.mpr hRadicand
  have hR2 : R^2=M^4/(X*(k:ℝ)*(N:ℝ)) := Real.sq_sqrt hRadicand.le
  have hphase : (X*k/M)*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    field_simp
  obtain ⟨hBR,hRNN,hNRR,hNMM,hFourR,hTenR⟩ :=
    upper_all_shift_polynomial_budgets hXp hMp hNp hK1 hRp hB hKH hBN
      hphase hRN hNR hNM hFour hTen
  have hTbase : C₀≤X*k/M := by
    calc
      _ ≤ X/M := hCC₀.trans hThreshold
      _ ≤ (X/M)*(k:ℝ) := le_mul_of_one_le_right (div_nonneg hXp.le hMp.le) hK1
      _ = _ := by ring
  have hTbasePos := zero_lt_one.trans_le (hC₀.trans hTbase)
  have hTbaseUpper : X*k/M≤X :=
    (div_le_iff₀ hMp).mpr (mul_le_mul_of_nonneg_left hKM hXp.le)
  have hEtaK : (k:ℝ)/M≤η₀ := (div_le_iff₀ hMp).mpr (hKH.trans hHeta)
  let E := (k:ℝ)*M/Real.sqrt (N:ℝ)+(k:ℝ)*M*R^2/(N:ℝ)^2+
    (k:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let Main := (k:ℝ)^11*M^11*(N:ℝ)^2/R^7+(k:ℝ)^11*(k:ℝ)*M^11/R^5+
    (k:ℝ)^12*M^12/((N:ℝ)*R^7)*(R/(N:ℝ))^((2:ℝ)/3)+
    (k:ℝ)^12*M^10*(N:ℝ)/R^3*(R/(N:ℝ))^((2:ℝ)/3)+
    (k:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  let Z := ∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZbase : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    hcorr X n N a L k R hTbase hN8 hN2 hBR hk hEtaK hKM ha hb hphase
      hRNN hNRR hNMM hFourR hTenR
  have hSigns := general_expressions_nonnegative hKp.le hMp.le hNp.le hRp hKp.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hZ : Z^12≤C₀*X^ε*(E^12+Main) :=
    hZbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTbasePos.le hTbaseUpper hε.le)
        (zero_le_one.trans hC₀)) (add_nonneg (pow_nonneg hE0 12) hMain0))
  let Poly := M^144/(H:ℝ)^72+
    ((M^144/(N:ℝ)^36+M^432/((H:ℝ)^72*X^72*(N:ℝ)^216)+
        X^24*(H:ℝ)^24*(N:ℝ)^144/M^24)+
      (X^21*(H:ℝ)^15*M^54*(N:ℝ)^33+X^15*(H:ℝ)^15*M^78*(N:ℝ)^15+
        X^19*(H:ℝ)^19*M^68*(N:ℝ)^9+X^7*(H:ℝ)^7*M^104*(N:ℝ)^9+
        X^4*(H:ℝ)^4*M^128/(N:ℝ)^24))
  have hPoly : 0≤Poly := by dsimp only [Poly]; positivity
  have hClog : (0:ℝ)≤Nat.clog 2 H := Nat.cast_nonneg _
  have hClogPlus : (1:ℝ)≤1+(Nat.clog 2 H:ℝ) := le_add_of_nonneg_right hClog
  have hClogPlus0 := zero_le_one.trans hClogPlus
  have hXpow0 : 0≤X^(6*ε) := Real.rpow_nonneg hXp.le _
  have hSext : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^144≤
      D*(Nat.clog 2 H:ℝ)^72*X^(6*ε)*Poly :=
    general_weyl_one_hundred_forty_fourth_bound (norm_nonneg _) hZ0 hA₀ hC₀ hClog hX hMp hNp
      hKp hHp hRp hε.le hKH hphase hZ hweyl
  let W := (1+(Nat.clog 2 H:ℝ))^72*X^(6*ε)
  have hW : 1≤W := by
    calc
      _ ≤ (1+(Nat.clog 2 H:ℝ))^72 := one_le_pow₀ hClogPlus
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg hClogPlus0 72)
        (Real.one_le_rpow hX (mul_nonneg (by norm_num) hε.le))
  have hLog : (Nat.clog 2 H:ℝ)^72≤(1+(Nat.clog 2 H:ℝ))^72 :=
    pow_le_pow_left₀ hClog (by linarith only) 72
  have hSext' : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^144≤D*W*Poly := by
    calc
      _ ≤ D*(Nat.clog 2 H:ℝ)^72*X^(6*ε)*Poly := hSext
      _ ≤ D*(1+(Nat.clog 2 H:ℝ))^72*X^(6*ε)*Poly :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hD) hXpow0) hPoly
      _ = _ := by dsimp only [W]; simp only [mul_assoc]
  have hOriginal := sharp_extension_power_bound_144 hD hW hPoly (by norm_num : (0:ℝ)≤6)
    (hsharp X a (a+L) ha hb) hSext'
  calc
    _ ≤ (2:ℝ)^143*(D+6^144)*W*(1+Poly) := hOriginal
    _ ≤ C*W*(1+Poly) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoeff (zero_le_one.trans hW))
        (add_nonneg zero_le_one hPoly)
    _ = _ := by dsimp only [W,Poly]; simp only [mul_assoc]

private theorem general_nine_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 144*u-72*h≤ξ)
    (hSqrt : 144*u-36*ν≤ξ)
    (hCubic : 432*u-72*h-72-216*ν≤ξ)
    (hEndpoint : 24+24*h+144*ν-24*ℓ≤ξ)
    (hType1 : 21+15*h+54*u+33*ν≤ξ)
    (hType2 : 15+15*h+78*u+15*ν≤ξ)
    (hType3 : 19+19*h+68*u+9*ν≤ξ)
    (hType4 : 7+7*h+104*u+9*ν≤ξ)
    (hPair : 4+4*h+128*u-24*ν≤ξ) :
    1+(M^144/H^72+((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
      (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
        X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) ≤ (10*(2:ℝ)^288)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  have hconst {b : ℝ} {j : ℕ} (hj : j≤288) (hb : b≤ξ) :
      (2:ℝ)^j*X^b≤(2:ℝ)^288*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hj)
      (Real.rpow_le_rpow_of_exponent_le hX hb) (Real.rpow_nonneg hXp.le _) (by positivity)
  have h₀ : 1≤(2:ℝ)^288*X^ξ :=
    (Real.one_le_rpow hX hξ).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (one_le_pow₀ (by norm_num)))
  have h₁ : M^144/H^72≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ (X^u)^144/(X^h/2)^72 := by gcongr
      _ = (2:ℝ)^72*((X^u)^144/(X^h)^72) := by field_simp
      _ = (2:ℝ)^72*X^(144*u-72*h) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        simp only [←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^72*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hDiag
  have h₂ : M^144/N^36≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ (X^u)^144/(X^ν/2)^36 := by gcongr
      _ = (2:ℝ)^36*((X^u)^144/(X^ν)^36) := by field_simp
      _ = (2:ℝ)^36*X^(144*u-36*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        simp only [←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^36*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hSqrt
  have h₃ : M^432/(H^72*X^72*N^216)≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ (X^u)^432/((X^h/2)^72*X^72*(X^ν/2)^216) := by gcongr
      _ = (2:ℝ)^288*((X^u)^432/((X^h)^72*X^72*(X^ν)^216)) := by field_simp
      _ = (2:ℝ)^288*X^(432*u-72*h-72-216*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 72]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^288*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hCubic
  have h₄ : X^24*H^24*N^144/M^24≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^24*(X^h)^24*(X^ν)^144/(X^ℓ)^24 := by gcongr
      _ = X^(24+24*h+144*ν-24*ℓ) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 24]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hEndpoint
  have h₅ : X^21*H^15*M^54*N^33≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^21*(X^h)^15*(X^u)^54*(X^ν)^33 := by gcongr
      _ = X^(21+15*h+54*u+33*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 21]
        simp only [←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType1
  have h₆ : X^15*H^15*M^78*N^15≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^15*(X^h)^15*(X^u)^78*(X^ν)^15 := by gcongr
      _ = X^(15+15*h+78*u+15*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 15]
        simp only [←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType2
  have h₇ : X^19*H^19*M^68*N^9≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^19*(X^h)^19*(X^u)^68*(X^ν)^9 := by gcongr
      _ = X^(19+19*h+68*u+9*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 19]
        simp only [←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType3
  have h₈ : X^7*H^7*M^104*N^9≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^7*(X^h)^7*(X^u)^104*(X^ν)^9 := by gcongr
      _ = X^(7+7*h+104*u+9*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 7]
        simp only [←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType4
  have h₉ : X^4*H^4*M^128/N^24≤(2:ℝ)^288*X^ξ := by
    calc
      _ ≤ X^4*(X^h)^4*(X^u)^128/(X^ν/2)^24 := by gcongr
      _ = (2:ℝ)^24*(X^4*(X^h)^4*(X^u)^128/(X^ν)^24) := by field_simp
      _ = (2:ℝ)^24*X^(4+4*h+128*u-24*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 4]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^24*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hPair
  have hTen (d : ℝ) : d+(d+((d+d+d)+(d+d+d+d+d)))=10*d := by ring
  calc
    _ ≤ (2:ℝ)^288*X^ξ+((2:ℝ)^288*X^ξ+
        (((2:ℝ)^288*X^ξ+(2:ℝ)^288*X^ξ+(2:ℝ)^288*X^ξ)+
          ((2:ℝ)^288*X^ξ+(2:ℝ)^288*X^ξ+(2:ℝ)^288*X^ξ+
            (2:ℝ)^288*X^ξ+(2:ℝ)^288*X^ξ))) :=
      add_le_add h₀ (add_le_add h₁
        (add_le_add (add_le_add (add_le_add h₂ h₃) h₄)
          (add_le_add (add_le_add (add_le_add (add_le_add h₅ h₆) h₇) h₈) h₉)))
    _ = 10*((2:ℝ)^288*X^ξ) := hTen _
    _ = _ := (mul_assoc _ _ _).symm


private theorem eventually_uniform_clog_power_loss_72
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^72≤X^ζ := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := 1+2/Real.log 2
  have hD : 0≤D := by dsimp only [D]; positivity
  have hLoss := eventually_const_log_pow_le_rpow
    (C*D^72) (mul_nonneg hC (pow_nonneg hD 72)) 72 hζ
  filter_upwards [hLoss,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with X hLossX hlogX hX
  intro H hH hHX
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hlogHX := Real.log_le_log hHp hHX
  have hc : (Nat.clog 2 H:ℝ)≤(2/Real.log 2)*Real.log X := by
    calc
      _ ≤ 2*(Real.log H/Real.log 2) := nat_clog_two_le_twice_log H hH
      _ ≤ 2*(Real.log X/Real.log 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogHX hlog2.le) (by norm_num)
      _ = _ := by ring
  have hplus : 1+(Nat.clog 2 H:ℝ)≤D*Real.log X := by
    dsimp only [D]
    nlinarith only [hc,hlogX]
  calc
    _ ≤ C*(D*Real.log X)^72 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hplus 72) hC
    _ = (C*D^72)*(Real.log X)^72 := by rw [mul_pow,mul_assoc]
    _ ≤ X^ζ := hLossX

private theorem general_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 6*εs+ζ≤144*β)
    (hDiag : 144*((α:ℝ)+δw)-72*h+6*εs+ζ≤144*β)
    (hSqrt : 144*((α:ℝ)+δw)-36*ν+6*εs+ζ≤144*β)
    (hCubic : 432*((α:ℝ)+δw)-72*h-72-216*ν+6*εs+ζ≤144*β)
    (hEndpoint : 24+24*h+144*ν-24*((α:ℝ)-δw)+6*εs+ζ≤144*β)
    (hType1 : 21+15*h+54*((α:ℝ)+δw)+33*ν+6*εs+ζ≤144*β)
    (hType2 : 15+15*h+78*((α:ℝ)+δw)+15*ν+6*εs+ζ≤144*β)
    (hType3 : 19+19*h+68*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hType4 : 7+7*h+104*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hPair : 4+4*h+128*((α:ℝ)+δw)-24*ν+6*εs+ζ≤144*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    approximateModelPhase_general_original_one_hundred_forty_fourth hσ hεs
  have hPhys := eventually_upper_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  have hLog := eventually_uniform_clog_power_loss_72
    (C:=Csrc*(10*(2:ℝ)^288))
    (mul_nonneg (zero_le_one.trans hCsrc) (by norm_num)) hζ
  obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 T₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro T M F a b setup
  have hT : 1≤T := hC.trans setup.threshold_le_param
  have hTp := zero_lt_one.trans_le hT
  have hTogether := hT₀ T ((le_max_right 1 T₀).trans setup.threshold_le_param)
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have hδwle : δ≤δw := min_le_right _ _
  have hδsrcle : δ≤δsrc := min_le_left _ _
  have hMl : T^((α:ℝ)-δw)≤M :=
    (Real.rpow_le_rpow_of_exponent_le hT (sub_le_sub_left hδwle _)).trans
      setup.rpow_sub_le_scale
  have hMu : M≤T^((α:ℝ)+δw) := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hT (add_le_add le_rfl hδwle))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl hδsrcle
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hFourM,hTenM⟩ := hTogether.1.2 M hMl hMu
  have hStart := setup.scale_le_start
  have hStop : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  have hActual := hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM hFourM hTenM hStart hStop
  let ξ := 144*β-6*εs-ζ
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hBase]
  have hPoly := general_nine_monomials_power_window hT hξ hMl hMu hNl hNu hHl hHu
    (by dsimp only [ξ]; linarith only [hDiag])
    (by dsimp only [ξ]; linarith only [hSqrt])
    (by dsimp only [ξ]; linarith only [hCubic])
    (by dsimp only [ξ]; linarith only [hEndpoint])
    (by dsimp only [ξ]; linarith only [hType1])
    (by dsimp only [ξ]; linarith only [hType2])
    (by dsimp only [ξ]; linarith only [hType3])
    (by dsimp only [ξ]; linarith only [hType4])
    (by dsimp only [ξ]; linarith only [hPair])
  have hh1 : h≤1 := by linarith only [hhℓ,hu,hδw]
  have hHT : (H:ℝ)≤T := hHu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hh1)
  have hLoss := hTogether.2 H hH2 hHT
  have hCsrc0 := zero_le_one.trans hCsrc
  have hLog0 : 0≤(1+(Nat.clog 2 H:ℝ))^72 := pow_nonneg (by positivity) _
  have hXpow0 := Real.rpow_nonneg hTp.le (6*εs)
  have hPower : ‖Expdb.exponentialSumAt F T M a b‖^144≤T^(144*β) := by
    rw [←hEnd]
    calc
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^72*T^(6*εs)*
          (1+(M^144/(H:ℝ)^72+
            ((M^144/(N:ℝ)^36+M^432/((H:ℝ)^72*T^72*(N:ℝ)^216)+
                T^24*(H:ℝ)^24*(N:ℝ)^144/M^24)+
              (T^21*(H:ℝ)^15*M^54*(N:ℝ)^33+T^15*(H:ℝ)^15*M^78*(N:ℝ)^15+
                T^19*(H:ℝ)^19*M^68*(N:ℝ)^9+T^7*(H:ℝ)^7*M^104*(N:ℝ)^9+
                T^4*(H:ℝ)^4*M^128/(N:ℝ)^24)))) := hActual
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^72*T^(6*εs)*((10*(2:ℝ)^288)*T^ξ) :=
        mul_le_mul_of_nonneg_left hPoly (mul_nonneg (mul_nonneg hCsrc0 hLog0) hXpow0)
      _ = (Csrc*(10*(2:ℝ)^288)*(1+(Nat.clog 2 H:ℝ))^72)*T^(6*εs)*T^ξ := by ac_rfl
      _ ≤ T^ζ*T^(6*εs)*T^ξ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLoss hXpow0) (Real.rpow_nonneg hTp.le _)
      _ = T^(144*β) := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
        apply congrArg (fun x : ℝ => T^x)
        dsimp only [ξ]
        ring
  have hRootPower : (T^β)^144=T^(144*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hTp.le β 144).symm
  have hRoot : ‖Expdb.exponentialSumAt F T M a b‖≤T^β :=
    le_of_pow_le_pow_left₀ (by norm_num : (144:ℕ)≠0)
      (Real.rpow_nonneg hTp.le _) (hPower.trans_eq hRootPower.symm)
  calc
    _ ≤ T^β := hRoot
    _ ≤ T^(β+ε) := Real.rpow_le_rpow_of_exponent_le hT (le_add_of_nonneg_right hε.le)
    _ ≤ C*T^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC

private theorem general_ninth_row_nonAsymptotic
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((89+908*(α:ℝ))/1282) := by
  let t := ((α:ℝ)-(423:ℝ)/1295)/((227:ℝ)/601-(423:ℝ)/1295)
  let ν := (1-t)*((115442:ℝ)/1000000)+t*((176182:ℝ)/1000000)
  let h := (1-t)*((52590:ℝ)/1000000)+t*((82521:ℝ)/1000000)
  apply general_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

private theorem exponentSumGrowthExponent_le_huxley_ninthRow
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.exponentSumGrowthExponent α≤(89+908*(α:ℝ))/1282 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (general_ninth_row_nonAsymptotic hα hα₁)


example
    (f : ℕ → ℝ) (H : ℕ) (hH : 2 ≤ H) (hf₀ : f 0=0)
    (hf : ∀ n, 0 ≤ f n) {A : ℝ} (hA : 0 ≤ A)
    (hcap : ∀ n < H, f n ≤ A) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ n∈Finset.range H,f n) ≤
        (Nat.clog 2 H:ℝ)*(A+∑ j∈Finset.range k,f (k+j)) :=
  HuxleyGeneralPhaseScratch.nonnegative_doubled_block_selection f H hH hf₀ hf (A:=A) hA hcap

example
    (F : ℝ → ℝ) (X M : ℝ) (a L r : ℕ) :
    ‖sourceShiftCorrelation F X M a L r‖ ≤ (L:ℝ)+1 :=
  HuxleyGeneralPhaseScratch.norm_sourceShiftCorrelation_le_length F X M a L r

example
    {S All B M H L C : ℝ} (hM : 0 < M) (hH : 0 < H)
    (hAll : 0 ≤ All) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hLM : L ≤ 2*M) (hHM : H ≤ M)
    (hWeyl : H^2*S^2 ≤ (L+H)*(H*L+2*H*All))
    (hPrefix : All ≤ C*(L+B)) :
    S^24 ≤ (18:ℝ)^12*(2:ℝ)^11*C^12*
      ((M^2/H)^12+(M/H)^12*B^12) :=
  HuxleyGeneralPhaseScratch.weyl_prefix_twenty_fourth_power (S:=S) (All:=All) (B:=B) (M:=M) (H:=H) (L:=L) (C:=C) hM hH hAll hB hL hC hLM hHM hWeyl hPrefix

example
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      (∑ r∈Finset.Icc 1 (H-1),‖sourceShiftCorrelation F X M a L r‖) ≤
        (Nat.clog 2 H:ℝ)*((L:ℝ)+1+
          ∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖) :=
  HuxleyGeneralPhaseScratch.source_correlation_doubled_block F X M a L H hH

example
    (F : ℝ → ℝ) (X M : ℝ) (a L H : ℕ) (hM : 0 < M)
    (hH : 2 ≤ H) (hHM : (H:ℝ) ≤ M) (hLM : (L:ℝ)+1 ≤ 2*M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖Expdb.exponentialSumAt F X M a (a+L)‖^24 ≤
        (18:ℝ)^12*(2:ℝ)^11*(Nat.clog 2 H:ℝ)^12*
          ((M^2/(H:ℝ))^12+(M/(H:ℝ))^12*
            (∑ j∈Finset.range k,‖sourceShiftCorrelation F X M a L (k+j)‖)^12) :=
  HuxleyGeneralPhaseScratch.exists_source_dyadic_twenty_fourth_power F X M a L H hM hH hHM hLM

example
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K*M/Real.sqrt N)^36=K^36*M^36/N^18 ∧
    (K*M*R^2/N^2)^36=M^180/(X^36*N^108) ∧
    (K*N*(N/R)^((2:ℝ)/3))^36=X^12*K^48*N^72/M^48 ∧
    (K^11*M^11/(N*R^2))^3=X^3*K^36*M^21 ∧
    (K^11*K*M^11/N^3)^3=K^36*M^33/N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3=
      X^2*K^38*M^28/N^12 :=
  HuxleyGeneralPhaseScratch.upper_correlation_integer_moments (X:=X) (M:=M) (N:=N) (K:=K) (R:=R) hX hM hN hK hR hscale

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^11/(N*R^2))^3≤X^3*M^57 ∧
    (M/H)^36*(K^11*K*M^11/N^3)^3≤M^69/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 :=
  HuxleyGeneralPhaseScratch.upper_integer_moments_all_shifts (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (n : ℕ) :
    (a+b+c)^n≤(2:ℝ)^(2*n)*(a^n+b^n+c^n) :=
  HuxleyGeneralPhaseScratch.three_term_power_bound (a:=a) (b:=b) (c:=c) ha hb hc n

example
    {X M N K H R B : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 1≤K) (hR : 0<R)
    (hB : 1≤B) (hKH : K≤H) (hBN : B≤N)
    (hscale : (X*K/M)*N*R^2=M^3)
    (hRN : B^2*M^4≤X*N^3) (hNR : B*X*H*N^2≤M^4)
    (hNM : B*N^2≤M)
    (hFour : B^2*X^3*H^3*N^11≤M^14)
    (hTen : B^2*X^7*H^7*N^27≤M^34) :
    B≤R ∧ B*R≤N ∧ B*N≤R^2 ∧ B*N^2≤M ∧
      B*N^4≤M*R^3 ∧ B*N^10≤M^3*R^7 :=
  HuxleyGeneralPhaseScratch.upper_all_shift_polynomial_budgets (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) (B:=B) hX hM hN hK hR hB hKH hBN hscale hRN hNR hNM hFour hTen

example
    {U V : ℝ} (hU : 32≤U) (hV : 4≤V) :
    let n := ⌊U/8⌋₊
    let N := 8*n
    let H := ⌊V⌋₊
    2≤N ∧ 2≤H ∧ U/2≤(N:ℝ) ∧ (N:ℝ)≤U ∧
      V/2≤(H:ℝ) ∧ (H:ℝ)≤V :=
  HuxleyGeneralPhaseScratch.floor_power_scales (U:=U) (V:=V) hU hV

example
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 :=
  HuxleyGeneralPhaseScratch.eventually_upper_polynomial_power_window (B:=B) (C:=C) (η:=η) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) hB hC hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen

example
    {X M N K R : ℝ} (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hR : 0<R)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^11*N^2/R^7)^6=X^21*K^87*N^33/M^18 ∧
    (K^11*K*M^11/R^5)^6=X^15*K^87*M^6*N^15 ∧
    (K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6=X^19*K^91*N^9/M^4 ∧
    (K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6=X^7*K^79*M^32*N^9 ∧
    (K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6=X^4*K^76*M^56/N^24 :=
  HuxleyGeneralPhaseScratch.general_correlation_integer_moments (X:=X) (M:=M) (N:=N) (K:=K) (R:=R) hX hM hN hK hR hscale

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^72*(K*M/Real.sqrt N)^72≤M^144/N^36 ∧
    (M/H)^72*(K*M*R^2/N^2)^72≤M^432/(H^72*X^72*N^216) ∧
    (M/H)^72*(K*N*(N/R)^((2:ℝ)/3))^72≤X^24*H^24*N^144/M^24 ∧
    (M/H)^72*(K^11*M^11*N^2/R^7)^6≤X^21*H^15*M^54*N^33 ∧
    (M/H)^72*(K^11*K*M^11/R^5)^6≤X^15*H^15*M^78*N^15 ∧
    (M/H)^72*(K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3))^6≤X^19*H^19*M^68*N^9 ∧
    (M/H)^72*(K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3))^6≤X^7*H^7*M^104*N^9 ∧
    (M/H)^72*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^6≤X^4*H^4*M^128/N^24 :=
  HuxleyGeneralPhaseScratch.general_integer_moments_all_shifts (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (n : ℕ) :
    (a+b+c+d+e)^n ≤ (2:ℝ)^(4*n)*(a^n+b^n+c^n+d^n+e^n) :=
  HuxleyGeneralPhaseScratch.five_term_power_bound (a:=a) (b:=b) (c:=c) (d:=d) (e:=e) ha hb hc hd he n

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^72*(E^72+Main^6)≤(2:ℝ)^144*
      ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
        (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
          X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24)) :=
  HuxleyGeneralPhaseScratch.weighted_general_integer_moment_bound (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^11*N^2/R^7+K^11*K*M^11/R^5+
      K^12*M^12/(N*R^7)*(R/N)^((2:ℝ)/3)+
      K^12*M^10*N/R^3*(R/N)^((2:ℝ)/3)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^144≤(2:ℝ)^154*A^6*C^6*L^72*X^(6*ε)*
      (M^144/H^72+
        ((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
          (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
            X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) :=
  HuxleyGeneralPhaseScratch.general_weyl_one_hundred_forty_fourth_bound (S:=S) (Z:=Z) (A:=A) (C:=C) (L:=L) (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) (ε:=ε) hS hZ hA hC hL hX hM hN hK hH hR hε hKH hscale

example
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^144≤D*W*P) :
    ‖u‖^144≤(2:ℝ)^143*(D+E^144)*W*(1+P) :=
  HuxleyGeneralPhaseScratch.sharp_extension_power_bound_144 (u:=u) (v:=v) (D:=D) (W:=W) (P:=P) (E:=E) hD hW hP hE hsharp hv

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^144 ≤
          C*(1+(Nat.clog 2 H:ℝ))^72*X^(6*ε)*
            (1+(M^144/(H:ℝ)^72+
              ((M^144/(N:ℝ)^36+M^432/((H:ℝ)^72*X^72*(N:ℝ)^216)+
                  X^24*(H:ℝ)^24*(N:ℝ)^144/M^24)+
                (X^21*(H:ℝ)^15*M^54*(N:ℝ)^33+X^15*(H:ℝ)^15*M^78*(N:ℝ)^15+
                  X^19*(H:ℝ)^19*M^68*(N:ℝ)^9+X^7*(H:ℝ)^7*M^104*(N:ℝ)^9+
                  X^4*(H:ℝ)^4*M^128/(N:ℝ)^24)))) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_general_original_one_hundred_forty_fourth (σ:=σ) (ε:=ε) hσ hε

example
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 144*u-72*h≤ξ)
    (hSqrt : 144*u-36*ν≤ξ)
    (hCubic : 432*u-72*h-72-216*ν≤ξ)
    (hEndpoint : 24+24*h+144*ν-24*ℓ≤ξ)
    (hType1 : 21+15*h+54*u+33*ν≤ξ)
    (hType2 : 15+15*h+78*u+15*ν≤ξ)
    (hType3 : 19+19*h+68*u+9*ν≤ξ)
    (hType4 : 7+7*h+104*u+9*ν≤ξ)
    (hPair : 4+4*h+128*u-24*ν≤ξ) :
    1+(M^144/H^72+((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
      (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
        X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) ≤ (10*(2:ℝ)^288)*X^ξ :=
  HuxleyGeneralPhaseScratch.general_nine_monomials_power_window (X:=X) (M:=M) (N:=N) (H:=H) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) (ξ:=ξ) hX hξ hMl hMu hNl hNu hHl hHu hDiag hSqrt hCubic hEndpoint hType1 hType2 hType3 hType4 hPair

example
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^72≤X^ζ :=
  HuxleyGeneralPhaseScratch.eventually_uniform_clog_power_loss_72 (C:=C) (ζ:=ζ) hC hζ

example
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 6*εs+ζ≤144*β)
    (hDiag : 144*((α:ℝ)+δw)-72*h+6*εs+ζ≤144*β)
    (hSqrt : 144*((α:ℝ)+δw)-36*ν+6*εs+ζ≤144*β)
    (hCubic : 432*((α:ℝ)+δw)-72*h-72-216*ν+6*εs+ζ≤144*β)
    (hEndpoint : 24+24*h+144*ν-24*((α:ℝ)-δw)+6*εs+ζ≤144*β)
    (hType1 : 21+15*h+54*((α:ℝ)+δw)+33*ν+6*εs+ζ≤144*β)
    (hType2 : 15+15*h+78*((α:ℝ)+δw)+15*ν+6*εs+ζ≤144*β)
    (hType3 : 19+19*h+68*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hType4 : 7+7*h+104*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hPair : 4+4*h+128*((α:ℝ)+δw)-24*ν+6*εs+ζ≤144*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β :=
  HuxleyGeneralPhaseScratch.general_beta_of_power_window (α:=α) (β:=β) (δw:=δw) (ν:=ν) (h:=h) (εs:=εs) (ζ:=ζ) hδw hν hh hεs hζ hℓ hu hhℓ hRN hNR hNM hFour hTen hBase hDiag hSqrt hCubic hEndpoint hType1 hType2 hType3 hType4 hPair

example
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((89+908*(α:ℝ))/1282) :=
  HuxleyGeneralPhaseScratch.general_ninth_row_nonAsymptotic (α:=α) hα hα₁


#print axioms HuxleyGeneralPhaseScratch.nonnegative_doubled_block_selection
#print axioms HuxleyGeneralPhaseScratch.norm_sourceShiftCorrelation_le_length
#print axioms HuxleyGeneralPhaseScratch.weyl_prefix_twenty_fourth_power
#print axioms HuxleyGeneralPhaseScratch.source_correlation_doubled_block
#print axioms HuxleyGeneralPhaseScratch.exists_source_dyadic_twenty_fourth_power
#print axioms HuxleyGeneralPhaseScratch.upper_correlation_integer_moments
#print axioms HuxleyGeneralPhaseScratch.upper_integer_moments_all_shifts
#print axioms HuxleyGeneralPhaseScratch.three_term_power_bound
#print axioms HuxleyGeneralPhaseScratch.upper_all_shift_polynomial_budgets
#print axioms HuxleyGeneralPhaseScratch.floor_power_scales
#print axioms HuxleyGeneralPhaseScratch.eventually_upper_polynomial_power_window
#print axioms HuxleyGeneralPhaseScratch.general_correlation_integer_moments
#print axioms HuxleyGeneralPhaseScratch.general_integer_moments_all_shifts
#print axioms HuxleyGeneralPhaseScratch.five_term_power_bound
#print axioms HuxleyGeneralPhaseScratch.weighted_general_integer_moment_bound
#print axioms HuxleyGeneralPhaseScratch.general_weyl_one_hundred_forty_fourth_bound
#print axioms HuxleyGeneralPhaseScratch.sharp_extension_power_bound_144
#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_general_original_one_hundred_forty_fourth
#print axioms HuxleyGeneralPhaseScratch.general_nine_monomials_power_window
#print axioms HuxleyGeneralPhaseScratch.eventually_uniform_clog_power_loss_72
#print axioms HuxleyGeneralPhaseScratch.general_beta_of_power_window
#print axioms HuxleyGeneralPhaseScratch.general_ninth_row_nonAsymptotic

example
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.exponentSumGrowthExponent α≤(89+908*(α:ℝ))/1282 :=
  HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) hα hα₁


#print axioms HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_ninthRow

private theorem lower_selected_grid_family_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Clower Cv B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Clower*R^4/(N^2*U))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*Cv*
        (D*(Y^11*M^13/(N^3*R^6))+
          D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
          2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hU := (physical_reference_reciprocal_bound hN hQ hB hUlower).1
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ T^ε := Real.one_le_rpow hT hε
  let TypeI := V*D*Y*(M/N)*(1+delta*Jsep)
  let Pair := Y^2*V*(Clower*R^4/(N^2*U))
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  let Physical := Y^10*M^10*N^2*R^8/Q^14
  have hTypeI : 0 ≤ TypeI := by dsimp only [TypeI]; positivity
  have hPair : 0 ≤ Pair := by dsimp only [Pair]; positivity
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hPhysical : 0 ≤ Physical := by dsimp only [Physical]; positivity
  have hmass : V*D*Z*(M/N)*(1+delta*Jsep)+
      Z^2*V*(Clower*R^4/(N^2*U))*T^ε ≤ (TypeI+Pair)*T^ε := by
    calc
      _ ≤ TypeI+Pair*T^ε := by dsimp only [TypeI,Pair]; gcongr
      _ ≤ TypeI*T^ε+Pair*T^ε :=
        add_le_add (le_mul_of_one_le_right hTypeI hTpow) le_rfl
      _ = _ := by ring
  have hpref := selected_band_mesh_cardinality_prefactor_bound
    hN hR hQ hK hP hCm hε hQN hNR hNT hmesh hcard
  have hmonomial := lower_physical_family_monomial_bound
    hY hM hN hR hRQ hJ hD hCd hCu hCv hB hd hVlower hdelta hUlower
  have hTproduct : T^ε*T^ε=T^(2*ε) := by
    rw [←Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ (Cpref*T^ε*L^10*Physical)*((TypeI+Pair)*T^ε) := by
      exact mul_le_mul hpref hmass (by positivity) (by positivity)
    _ = Cpref*T^(2*ε)*L^10*(Physical*(TypeI+Pair)) := by
      calc
        _ = Cpref*(T^ε*T^ε)*L^10*(Physical*(TypeI+Pair)) := by ring
        _ = _ := by rw [hTproduct]
    _ ≤ Cpref*T^(2*ε)*L^10*
        (Cv*(D*(Y^11*M^13/(N^3*R^6))+
          D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
          2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)))) :=
      mul_le_mul_of_nonneg_left hmonomial (by positivity)
    _ = _ := by dsimp only [Cpref]; ring

private theorem lower_selected_grid_family_total_bound
    {Y Z P M N R Q U K V Jsep D Cdelta Clower Cv B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε) (hCo : 0 ≤ Couter)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Clower*R^4/(N^2*U))*T^ε) ≤
      ((Couter*Cv)*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*(7/6:ℝ)*(D+D*Cdelta+2*B*Clower))*
        T^(2*ε)*L^10*
        (Y^11*M^13/(N^3*R^6)+Y^11*Jsep*M^13/(N^5*R^4)+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  let m₁ := Y^11*M^13/(N^3*R^6)
  let m₂ := Y^11*Jsep*M^13/(N^5*R^4)
  let m₃ := Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  let Cmass := D+D*Cdelta+2*B*Clower
  let Cpref := Cmesh^12*Cmesh^ε*(2*Ccard)^10
  have hm₁ : 0 ≤ m₁ := by dsimp only [m₁]; positivity
  have hm₂ : 0 ≤ m₂ := by dsimp only [m₂]; positivity
  have hm₃ : 0 ≤ m₃ := by dsimp only [m₃]; positivity
  have hDc := mul_nonneg hD hCd
  have hUc : 0 ≤ 2*B*Clower := by positivity
  have hDmass : D ≤ Cmass :=
    (le_add_of_nonneg_right hDc).trans (le_add_of_nonneg_right hUc)
  have hDcmass : D*Cdelta ≤ Cmass :=
    (le_add_of_nonneg_left hD).trans (le_add_of_nonneg_right hUc)
  have hUcmass : 2*B*Clower ≤ Cmass := le_add_of_nonneg_left (add_nonneg hD hDc)
  have hWeighted : D*m₁+D*Cdelta*m₂+2*B*Clower*m₃ ≤ Cmass*(m₁+m₂+m₃) := by
    calc
      _ ≤ Cmass*m₁+Cmass*m₂+Cmass*m₃ :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hDmass hm₁)
          (mul_le_mul_of_nonneg_right hDcmass hm₂)) (mul_le_mul_of_nonneg_right hUcmass hm₃)
      _ = _ := by rw [mul_add, mul_add]
  have hCpref : 0 ≤ Cpref := by dsimp only [Cpref]; positivity
  have hraw := lower_selected_grid_family_bound
    hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε
    hQN hNR hNT hmesh hcard hVlower hdelta hUlower
  have hpref : 0 ≤ Cpref*T^(2*ε)*L^10*Cv :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpref (Real.rpow_nonneg (zero_le_one.trans hT) _))
      (by positivity)) hCv
  calc
    _ = Couter*((R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
        (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Clower*R^4/(N^2*U))*T^ε)) := by
      simp only [mul_assoc]
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(D*m₁+D*Cdelta*m₂+2*B*Clower*m₃)) :=
      mul_le_mul_of_nonneg_left hraw hCo
    _ ≤ Couter*(Cpref*T^(2*ε)*L^10*Cv*(Cmass*(m₁+m₂+m₃))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeighted hpref) hCo
    _ = (Couter*Cv*Cpref*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃) := by ac_rfl
    _ ≤ (7/6:ℝ)*((Couter*Cv*Cpref*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃)) := by
      have hCmass : 0 ≤ Cmass := hD.trans hDmass
      apply le_mul_of_one_le_left
      · positivity
      · norm_num
    _ = _ := by
      change (7/6:ℝ)*((Couter*Cv*Cpref*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃)) =
        ((Couter*Cv)*Cpref*(7/6:ℝ)*Cmass)*T^(2*ε)*L^10*(m₁+m₂+m₃)
      ac_rfl

private theorem lower_expressions_nonnegative
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0 ≤ Y^11*M^13/(N^3*R^6)+Y^11*J*M^13/(N^5*R^4)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) := by
  constructor <;> positivity

private theorem lower_radius_main_bound
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hJ : 0 ≤ J)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) :
    Ysmall^11*M^13/(N^3*S^6)+Ysmall^11*J*M^13/(N^5*S^4)+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^6*(Y^11*M^13/(N^3*R^6)+Y^11*J*M^13/(N^5*R^4)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
  have hY0 := hYsmall.trans hY
  have hD0 := zero_le_one.trans hD
  have hInv (j : ℕ) : 1/S^j ≤ D^j/R^j := by
    apply (div_le_div_iff₀ (pow_pos hS j) (pow_pos hR j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hR.le hRS j
  have hi₆ := hInv 6
  have hi₄ := hInv 4
  have hi₂ := hInv 2
  have hFor := (comparable_radius_powers hN hR hS hD hSR hRS).2.2.2
  have hD46 : D^4 ≤ D^6 := pow_le_pow_right₀ hD (by norm_num)
  have hD36 : D^3 ≤ D^6 := pow_le_pow_right₀ hD (by norm_num)
  have h₁ : Ysmall^11*M^13/(N^3*S^6) ≤ D^6*(Y^11*M^13/(N^3*R^6)) := by
    calc
      _ = (Ysmall^11*M^13/N^3)*(1/S^6) := by ring
      _ ≤ (Y^11*M^13/N^3)*(D^6/R^6) := by gcongr
      _ = _ := by ring
  have h₂ : Ysmall^11*J*M^13/(N^5*S^4) ≤ D^6*(Y^11*J*M^13/(N^5*R^4)) := by
    calc
      _ = (Ysmall^11*J*M^13/N^5)*(1/S^4) := by ring
      _ ≤ (Y^11*J*M^13/N^5)*(D^4/R^4) := by gcongr
      _ = D^4*(Y^11*J*M^13/(N^5*R^4)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD46 (by positivity)
  have h₃ : Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
      D^6*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by
    calc
      _ = (Ysmall^12*M^12/N^4)*((1/S^2)*(S/N)^((2:ℝ)/3)) := by ring
      _ ≤ (Y^12*M^12/N^4)*((D^2/R^2)*(D*(R/N)^((2:ℝ)/3))) := by gcongr
      _ = D^3*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD36 (by positivity)
  calc
    _ ≤ D^6*(Y^11*M^13/(N^3*R^6))+D^6*(Y^11*J*M^13/(N^5*R^4))+
        D^6*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by rw [mul_add,mul_add]


example
    {Y Z P M N R Q U K V Jsep D Cdelta Clower Cv B delta Cmesh Ccard L T ε : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    (R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Clower*R^4/(N^2*U))*T^ε) ≤
      (Cmesh^12*Cmesh^ε*(2*Ccard)^10)*T^(2*ε)*L^10*Cv*
        (D*(Y^11*M^13/(N^3*R^6))+
          D*Cdelta*(Y^11*Jsep*M^13/(N^5*R^4))+
          2*B*Clower*(Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))) :=
  HuxleyGeneralPhaseScratch.lower_selected_grid_family_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Clower:=Clower) (Cv:=Cv) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε hQN hNR hNT hmesh hcard hVlower hdelta hUlower

example
    {Y Z P M N R Q U K V Jsep D Cdelta Clower Cv B delta Cmesh Ccard L T ε Couter : ℝ}
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hZY : Z ≤ Y) (hP : 0 ≤ P)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hRQ : R ≤ Q) (hK : 0 < K)
    (hV : 0 ≤ V) (hJ : 0 ≤ Jsep) (hD : 0 ≤ D) (hCd : 0 ≤ Cdelta)
    (hCu : 0 ≤ Clower) (hCv : 0 ≤ Cv) (hB : 0 < B) (hd : 0 ≤ delta)
    (hCm : 0 < Cmesh) (hT : 1 ≤ T) (hε : 0 ≤ ε) (hCo : 0 ≤ Couter)
    (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNT : N ≤ T)
    (hmesh : K ≤ Cmesh*Q*N/R^2)
    (hcard : P ≤ Ccard*Y*M*R^2/(N*Q^2)*L)
    (hVlower : V ≤ Cv*M^2/N^4) (hdelta : delta ≤ Cdelta*R^2/N^2)
    (hUlower : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    Couter*(R^2/Q)^6*K^((12:ℝ)+ε)*(2*P)^10*
      (V*D*Z*(M/N)*(1+delta*Jsep)+Z^2*V*(Clower*R^4/(N^2*U))*T^ε) ≤
      ((Couter*Cv)*(Cmesh^12*Cmesh^ε*(2*Ccard)^10)*(7/6:ℝ)*(D+D*Cdelta+2*B*Clower))*
        T^(2*ε)*L^10*
        (Y^11*M^13/(N^3*R^6)+Y^11*Jsep*M^13/(N^5*R^4)+
          Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.lower_selected_grid_family_total_bound (Y:=Y) (Z:=Z) (P:=P) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (K:=K) (V:=V) (Jsep:=Jsep) (D:=D) (Cdelta:=Cdelta) (Clower:=Clower) (Cv:=Cv) (B:=B) (delta:=delta) (Cmesh:=Cmesh) (Ccard:=Ccard) (L:=L) (T:=T) (ε:=ε) (Couter:=Couter) hY hZ hZY hP hM hN hR hRQ hK hV hJ hD hCd hCu hCv hB hd hCm hT hε hCo hQN hNR hNT hmesh hcard hVlower hdelta hUlower

example
    {Y M N R J : ℝ} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hR : 0 < R) (hJ : 0 ≤ J) :
    0 ≤ Y*M/Real.sqrt N+Y*M*R^2/N^2+Y*N*(N/R)^((2:ℝ)/3) ∧
    0 ≤ Y^11*M^13/(N^3*R^6)+Y^11*J*M^13/(N^5*R^4)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3) :=
  HuxleyGeneralPhaseScratch.lower_expressions_nonnegative (Y:=Y) (M:=M) (N:=N) (R:=R) (J:=J) hY hM hN hR hJ

example
    {Ysmall Y M N R S D J : ℝ}
    (hYsmall : 0 ≤ Ysmall) (hY : Ysmall ≤ Y) (hM : 0 < M) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S) (hD : 1 ≤ D) (hJ : 0 ≤ J)
    (hSR : S ≤ D*R) (hRS : R ≤ D*S) :
    Ysmall^11*M^13/(N^3*S^6)+Ysmall^11*J*M^13/(N^5*S^4)+
      Ysmall^12*M^12/(N^4*S^2)*(S/N)^((2:ℝ)/3) ≤
    D^6*(Y^11*M^13/(N^3*R^6)+Y^11*J*M^13/(N^5*R^4)+
      Y^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)) :=
  HuxleyGeneralPhaseScratch.lower_radius_main_bound (Ysmall:=Ysmall) (Y:=Y) (M:=M) (N:=N) (R:=R) (S:=S) (D:=D) (J:=J) hYsmall hY hM hN hR hS hD hJ hSR hRS


#print axioms HuxleyGeneralPhaseScratch.lower_selected_grid_family_bound
#print axioms HuxleyGeneralPhaseScratch.lower_selected_grid_family_total_bound
#print axioms HuxleyGeneralPhaseScratch.lower_expressions_nonnegative
#print axioms HuxleyGeneralPhaseScratch.lower_radius_main_bound

private theorem eventually_lower_finite_numerical_consequence
    {σsrc csrc Usrc κ Cphys Csrc Couter CLOW Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCLOW : 0 ≤ CLOW)
    (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Uband := (3*Usrc/σsrc)*T/(2*M^2)
      let Vscale := 1+R^4*Uband^2/(N:ℝ)^2
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*
              (CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) := by

  classical
  intro εloss Cmesh CtailBand ClowBand CerrorBand
  let Cv := 1+(3*Usrc/(2*σsrc))^2
  have hCv : 0 ≤ Cv := add_nonneg zero_le_one (sq_nonneg _)
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let Carg := 512*768*σsrc/csrc
  let DensityLog := 3+Real.log (Carg+1)
  let Cdensity := 128*CerrorBand*DensityLog
  let Ccard := 16*(1536:ℝ)^2+8*Cdensity
  let CKlog := 3+Real.log (Cmesh+1)
  let Cband := 2+1/Real.log 2
  let Cdelta := (16*Usrc/csrc)*Real.sqrt ((Usrc/(2*σsrc))*Cmesh)
  let Cmass := Dtype+Dtype*Cdelta+2*Bselect*CLOW
  let Cfamily := (Couter*Cv)*
    (Cmesh^12*Cmesh^εloss*(2*Ccard)^10)*(7/6:ℝ)*Cmass
  let CE₀ := 2*Real.sqrt 3*(1+Real.log 6)+24*σsrc/csrc
  let Cterminal := Cdensity*Csep^2/8
  let Cendpoint := 112/κ+28*σsrc/csrc+2/(Cphys+2)+41/4
  let Cerror := 1+Csrc*CE₀+Cterminal+Cendpoint
  let Cgrid := (2:ℝ)^11*(Cerror^12+(Csrc*CKlog)^12*Cfamily)
  let Ctotal := (2:ℝ)^11*(Cband^11*Cerror^12+
    (4:ℝ)^12*(8:ℝ)^12*Cband^12*Cgrid+Cerror^12)
  have hConstants :
      0 ≤ CtailBand ∧ 0 ≤ ClowBand ∧ 0 ≤ CerrorBand ∧ 1 ≤ Cmesh ∧
      0 ≤ Carg ∧ 0 ≤ DensityLog ∧ 0 ≤ Cdensity ∧ 0 ≤ Ccard ∧
      0 ≤ CKlog ∧ 0 ≤ Cband ∧ 0 ≤ Cdelta ∧ 0 ≤ Cmass ∧
      0 ≤ Cfamily ∧ 0 ≤ CE₀ ∧ 0 ≤ Cterminal ∧ 0 ≤ Cendpoint ∧
      0 ≤ Cerror ∧ Csrc*CE₀ ≤ Cerror ∧ Cterminal ≤ Cerror ∧
      Cendpoint ≤ Cerror ∧ 0 ≤ Cgrid ∧ 0 ≤ Ctotal :=
    upper_numerical_constants_nonnegative (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero
      (mul_nonneg hCouter hCv) hCLOW hDtype hBsOne hCsep
  obtain ⟨hCtailBand,hClowBand,hCerrorBand,hCmeshOne,hCarg,hDensityLog,hCdensity,hCcard,hCKlog,hCband,hCdelta,hCmass,hCfamily,hCE₀,hCterminal,hCendpoint,hCerror,hErrorCompletion,hErrorTerminal,hErrorEndpoint,hCgrid,hCtotal⟩ :=
    hConstants
  have hCmesh : 0 < Cmesh := zero_lt_one.trans_le hCmeshOne
  filter_upwards [eventually_selected_band_logarithmic_absorption hCtotal hε,
    Filter.eventually_ge_atTop (1:ℝ)] with T hAbs hTone
  intro Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover S
    hNlink hNtwo hR hNR' hNsqM hMT hJsep hscale hQbase hBaseHi hEndLo hkmax hKpos
    Q hvalid Yc μ₀ U₀ Uband Vscale Error Δtype Buffer Width FamilyBound Density Endpoint Selected Grid
    hChunks hBands hGridCount hGridImage hNorm ErrorTotal Main
  have hT : 0 < T := hAbs.1
  have hLogOne : 1 ≤ Real.log T := hAbs.2.1
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hM : 0 < M := (sq_pos_of_pos hNp).trans_le hNsqM
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hLogOne]
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  have hYc : 0 ≤ Yc := Nat.cast_nonneg _
  have hMain : 0 ≤ Main :=
    (lower_expressions_nonnegative hYc hM.le hNp.le hRp hJsep).2
  have hErrorTotal : 0 ≤ ErrorTotal :=
    add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
          (sq_nonneg (N:ℝ))))
      (mul_nonneg (mul_nonneg hYc hNp.le)
        (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le)
  have hQpos (k : ℕ) : (0:ℝ) < Q k := by
    exact_mod_cast Nat.mul_pos hQbase (by positivity : 0 < 2^k)
  have hKreal (k : ℕ) : (0:ℝ) < Kmesh k := by exact_mod_cast hKpos k
  have hlogs (k : ℕ) (hk : k ≤ kmax) :
      2+Real.log (Carg*R^2/(Q k:ℝ)+1) ≤ DensityLog*L ∧
      1+Real.log (Kmesh k) ≤ CKlog*L ∧
      (kmax:ℝ)+2 ≤ Cband*L := by
    obtain ⟨hRQ,hQN,_,hKU,_,_⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    exact physical_band_logarithmic_bounds hCarg hCmeshOne hTone hR hRQ
      hQNreal hNR' hNT (hKreal k) hKU hkmax
  have hDensity (k : ℕ) (hk : k ≤ kmax) :
      Density k ≤ Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    have harg : 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))=Carg*R^2/(Q k:ℝ) := by
      dsimp only [Carg]
      field_simp [(hQpos k).ne']
    calc
      _ = 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (Carg*R^2/(Q k:ℝ)+1)) := by
        dsimp only [Density]
        rw [harg]
      _ ≤ 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*(DensityLog*L) :=
        mul_le_mul_of_nonneg_left (hlogs k hk).1 (by positivity)
      _ = _ := by dsimp only [Cdensity]; ring
  have hBandCounts (k : ℕ) (hk : k ≤ kmax) :
      ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        Yc*(Cdensity*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L) :=
    (hBands k hk).trans (mul_le_mul_of_nonneg_left (hDensity k hk) hYc)
  have hGridCard (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      ((Grid k r).card:ℝ) ≤ Ccard*Yc*M*R^2/((N:ℝ)*(Q k:ℝ)^2)*L := by
    exact selected_band_grid_cardinality_bound Chunks band Grid Qbase kmax hQbase
      hYc hM.le hNp hCdensity hL hBaseHi hChunks hBandCounts
      hGridCount k hk r
  have hGridPhase (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      (((Grid k r).image Prod.fst).card:ℝ) ≤ Yc := by
    change (((Grid k r).image Prod.fst).card:ℝ) ≤ (Y.card:ℝ)
    exact_mod_cast Finset.card_le_card (hGridImage k hk r)
  have hDeltaType (k : ℕ) (hk : k ≤ kmax) :
      Δtype k ≤ Cdelta*R^2/(N:ℝ)^2 := by
    obtain ⟨_,_,hMesh,hKU,_,_⟩ := hvalid k hk
    exact positive_difference_source_type_spacing_bound hσsrc hcsrc hUsrc.le
      hT hM hNp hRp (hQpos k) (hKreal k) hCmesh.le hscale hMesh hKU
  have hVzero : 0 ≤ Vscale :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (pow_nonneg hRp.le 4) (sq_nonneg Uband))
      (sq_nonneg (N:ℝ)))
  have hVbound : Vscale ≤ Cv*M^2/(N:ℝ)^4 :=
    (positive_difference_source_physical_regime_coefficients
      hσsrc hcsrc hUsrc hκ hT hM hNp hRp hscale hNR' hNsqM).2.2.2
  have hFamily (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      FamilyBound k (Grid k r) ≤ Cfamily*T^(2*εloss)*L^10*Main := by
    obtain ⟨hRQ,hQN,_,hKU,hUupper,hUlower⟩ := hvalid k hk
    have hQNreal : (Q k:ℝ) ≤ N := by exact_mod_cast hQN
    have hdeltazero : 0 ≤ Δtype k := by dsimp only [Δtype,U₀,μ₀]; positivity
    exact lower_selected_grid_family_total_bound
      hYc (Nat.cast_nonneg ((Grid k r).image Prod.fst).card) (hGridPhase k hk r)
      (Nat.cast_nonneg (Grid k r).card) hM hNp hRp hRQ (hKreal k)
      hVzero hJsep hDtype hCdelta hCLOW hCv
      (zero_lt_one.trans_le hBsOne) hdeltazero hCmesh hTone hεloss.le hCouter
      hQNreal hNR' hNT hKU (hGridCard k hk r) hVbound (hDeltaType k hk) hUlower
  let E₁ := Yc*M/Real.sqrt (N:ℝ)
  let E₂ := Yc*M*R^2/(N:ℝ)^2
  let E₃ := Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  have hE₁ : 0 ≤ E₁ := div_nonneg (mul_nonneg hYc hM.le) (Real.sqrt_nonneg _)
  have hE₂ : 0 ≤ E₂ := div_nonneg (mul_nonneg (mul_nonneg hYc hM.le) (sq_nonneg R))
    (sq_nonneg (N:ℝ))
  have hE₃ : 0 ≤ E₃ := mul_nonneg (mul_nonneg hYc hNp.le)
    (Real.rpow_pos_of_pos (div_pos hNp hRp) _).le
  have hE₁₂Total : E₁+E₂ ≤ ErrorTotal := le_add_of_nonneg_right hE₃
  have hE₂Total : E₂ ≤ ErrorTotal := (le_add_of_nonneg_left hE₁).trans hE₁₂Total
  have hE₃Total : E₃ ≤ ErrorTotal := le_add_of_nonneg_left (add_nonneg hE₁ hE₂)
  have hCompletion : Csrc*Error ≤ Cerror*ErrorTotal*L := by
    have hraw := positive_difference_completion_error_physical_bound
      (R:=R) hYc hNOne hNM hMT (show 0 ≤ 12*σsrc/csrc by positivity)
    have he : Error ≤ CE₀*(E₁+E₂)*L := by
      convert hraw using 1
      · dsimp only [Error]
        ring
      · dsimp only [CE₀,E₁,E₂,L]
        ring
    calc
      _ ≤ Csrc*(CE₀*(E₁+E₂)*L) := mul_le_mul_of_nonneg_left he hCsrcZero
      _ = (Csrc*CE₀)*(E₁+E₂)*L := by simp only [mul_assoc]
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hErrorCompletion hE₁₂Total (add_nonneg hE₁ hE₂) hCerror) hLzero
  have hNlinkReal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hTerminalBound : (n:ℝ)*Yc*Density kmax ≤ Cerror*ErrorTotal*L := by
    have hnzero : 0 ≤ (n:ℝ)*Yc := mul_nonneg (Nat.cast_nonneg n) hYc
    have hcore := selected_terminal_density_bound (R:=R) hNp hM.le hYc hCdensity
      (zero_lt_one.trans_le hCsep) hLzero hNlinkReal hEndLo
    calc
      _ ≤ (n:ℝ)*Yc*(Cdensity*M*R^2/((N:ℝ)*(Q kmax:ℝ)^2)*L) :=
        mul_le_mul_of_nonneg_left (hDensity kmax le_rfl) hnzero
      _ ≤ Cterminal*E₂*L := hcore
      _ ≤ Cerror*ErrorTotal*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul hErrorTerminal hE₂Total hE₂ hCerror) hLzero
  have hEndpointBound : Endpoint ≤ Cerror*ErrorTotal*L := by
    obtain ⟨hRQ,hQN,_,_,hUupper,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQNreal : (Q 0:ℝ) ≤ N := by exact_mod_cast hQN
    have hraw := positive_difference_endpoint_error_physical_bound
      hYc hNOne hRp hRQ hQNreal hκ hσsrc.le hcsrc hCphys hBsOne hNlinkReal hUupper
    have he : Endpoint ≤ Cendpoint*E₃ := by
      exact hraw
    calc
      _ ≤ Cendpoint*E₃ := he
      _ ≤ Cerror*ErrorTotal := mul_le_mul hErrorEndpoint hE₃Total hE₃ hCerror
      _ ≤ Cerror*ErrorTotal*L := le_mul_of_one_le_right (mul_nonneg hCerror hErrorTotal) hL

  have hLogN : 0 ≤ Real.log (6*(N:ℝ)) :=
    Real.log_nonneg (by linarith only [hNreal])
  have hCompletionZero : 0 ≤ Csrc*Error :=
    mul_nonneg hCsrcZero
      (mul_nonneg (mul_nonneg hYc (add_nonneg (div_nonneg hM.le hNp.le) zero_le_one))
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hLogN)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
            (mul_nonneg hcsrc.le hNp.le))))
  have hDensityZero (k : ℕ) : 0 ≤ Density k := by
    have hh : 0 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768)) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσsrc.le) (sq_nonneg R))
        (mul_nonneg hcsrc.le (div_nonneg (hQpos k).le (by norm_num)))
    have harg : 1 ≤ 512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1 := le_add_of_nonneg_left hh
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCerrorBand)
        (div_nonneg (mul_nonneg hM.le (sq_nonneg R))
          (mul_nonneg hNp.le (sq_nonneg _))))
      (add_nonneg (by norm_num) (Real.log_nonneg harg))
  have hTerminalZero : 0 ≤ (n:ℝ)*Yc*Density kmax :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hYc) (hDensityZero kmax)
  have hBufferZero : 0 ≤ Buffer 0 :=
    add_nonneg
      (add_nonneg
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hκ.le) hNp.le)
        (div_nonneg hNp.le (add_nonneg hCphys (by norm_num)))) (by norm_num)
  have hWidthZero : 0 ≤ Width 0 :=
    mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hσsrc.le) hcsrc.le)
        (Nat.cast_nonneg _)) hNp.le
  have hEndpointZero : 0 ≤ Endpoint :=
    mul_nonneg hYc
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hBufferZero)
            (mul_nonneg (by norm_num) hWidthZero))
          (mul_nonneg (by norm_num) hNp.le))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
  have hTpowOne : 1 ≤ T^(2*εloss) :=
    Real.one_le_rpow hTone (mul_nonneg (by norm_num) hεloss.le)
  let G := fun k r => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))
  have hG (k : ℕ) (hk : k ≤ kmax) (r : ℤ) :
      G k r ≤ Cgrid*T^(2*εloss)*L^22*(ErrorTotal^12+Main) := by
    have hKone : (1:ℝ) ≤ Kmesh k := by
      have hh : 1 ≤ Kmesh k := Nat.succ_le_iff.mpr (hKpos k)
      exact_mod_cast hh
    have hlogK := Real.log_nonneg hKone
    have hLogZero : 0 ≤ Csrc*(1+Real.log (Kmesh k)) :=
      mul_nonneg hCsrcZero (add_nonneg zero_le_one hlogK)
    have hLogBound : Csrc*(1+Real.log (Kmesh k)) ≤ (Csrc*CKlog)*L := by
      calc
        _ ≤ Csrc*(CKlog*L) := mul_le_mul_of_nonneg_left (hlogs k hk).2.1 hCsrcZero
        _ = _ := by simp only [mul_assoc]
    exact selected_grid_completion_bound hCompletionZero hLogZero hMain hCfamily hL hTpowOne
      hCompletion hLogBound (hFamily k hk r)
  have hClean := selected_band_finite_power_cleanup kmax G
    hTerminalZero hEndpointZero hMain hL hTpowOne hCband hCgrid
    (hlogs 0 (Nat.zero_le _)).2.2 hTerminalBound hEndpointBound
    (fun k hk r _ => hG k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) r) hNorm
  have hExp : 2*εloss=ε/2 := by dsimp only [εloss]; ring
  have hFactor : Ctotal*T^(2*εloss)*L^36 ≤ T^ε := by
    simpa only [hExp,L] using hAbs.2.2
  exact hClean.trans (mul_le_mul_of_nonneg_right hFactor
    (add_nonneg (pow_nonneg hErrorTotal 12) hMain))

example
    {σsrc csrc Usrc κ Cphys Csrc Couter CLOW Dtype Bselect Csep ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) (hκ : 0 < κ)
    (hCphys : 0 ≤ Cphys) (hCsrcZero : 0 ≤ Csrc) (hCouter : 0 ≤ Couter)
    (hCLOW : 0 ≤ CLOW)
    (hDtype : 0 ≤ Dtype) (hBsOne : 1 ≤ Bselect)
    (hCsep : 1 ≤ Csep) (hε : 0 < ε) :
    let εloss := ε/4
    let Cmesh := 2*max 1 (63*Usrc/(2*σsrc))
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ) (R M Jsep : ℝ)
      (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)) {S : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      M ≤ T → 0 ≤ Jsep → T*(N:ℝ)*R^2=M^3 →
      0 < Qbase → (Qbase:ℝ) ≤ 1536*R → (N:ℝ)/Csep ≤ (Qbase*2^kmax:ℕ) →
      (kmax:ℝ) ≤ Real.log N/Real.log 2 → (∀ k, 0 < Kmesh k) →
      let Q := fun k : ℕ => Qbase*2^k
      (∀ k ≤ kmax,
        R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
        (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
        (Kmesh k:ℝ) ≤ Cmesh*(Q k:ℝ)*(N:ℝ)/R^2 ∧
        (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
        ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ)) →
      let Yc := (Y.card:ℝ)
      let μ₀ := csrc*T/(12*σsrc*M^3)
      let U₀ := Usrc*T/(2*σsrc*M^3)
      let Uband := (3*Usrc/σsrc)*T/(2*M^2)
      let Vscale := 1+R^4*Uband^2/(N:ℝ)^2
      let Error := Yc*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
      let Δtype := fun k : ℕ =>
        (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
      let Buffer := fun k : ℕ =>
        (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
      let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
      let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
        Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*
              (CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))*T^εloss)
      let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
      let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (Chunks.card:ℝ) ≤ Yc*(8*M/(N:ℝ)) →
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤ Yc*Density k) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).card ≤ 2*(Selected k).card) →
      (∀ k ≤ kmax, ∀ r : ℤ, (Grid k r).image Prod.fst ⊆ Y) →
      S ≤ 2^11*(((kmax:ℝ)+2)^11*
        (((n:ℝ)*Yc*Density kmax)^12+
          (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
            (2^11*((Csrc*Error)^12+
              (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) →
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      S ≤ T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.eventually_lower_finite_numerical_consequence (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ) (Cphys:=Cphys) (Csrc:=Csrc) (Couter:=Couter) (CLOW:=CLOW) (Dtype:=Dtype) (Bselect:=Bselect) (Csep:=Csep) (ε:=ε) hσsrc hcsrc hUsrc hκ hCphys hCsrcZero hCouter hCLOW hDtype hBsOne hCsep hε


#print axioms HuxleyGeneralPhaseScratch.eventually_lower_finite_numerical_consequence

private theorem eventually_lower_quantitative_phase_subinterval_bound
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M → Cbudget*T ≤ M^2 →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+
        Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) := by

  classical
  let εloss := ε/4
  have hεloss : 0 < εloss := by dsimp only [εloss]; linarith only [hε]
  let κ := modelPhaseThirdLower σ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
  let Lsource := max (8*Ratio^2)
    (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
  have hLsource : 0 ≤ Lsource :=
    (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  let θ := min (1/48:ℝ) (1/(16*(Lsource+3)))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθmax : θ ≤ 1/24 := (min_le_left _ _).trans (by norm_num)
  have hθaction : θ ≤ 1/(8*(Lsource+3)) := by
    apply (min_le_right _ _).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hLsource])
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hfinite⟩ :=
    eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  let Cphys := σ*(σ+1)+1
  let c := κ/6
  let J := Cphys/6
  let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
  let C₂ := modelPhaseJetCoefficient σ 2+δ
  let C₃ := modelPhaseJetCoefficient σ 3+δ
  let Ct := C₂/2+5*C₃/12
  let Cc := C₂/κ+C₃/(2*κ)
  let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
    2*quarticNonlinearResidualConstant σ δ)/κ
  let Esize := κ/(16*(Cphys+2))
  let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
  let Lunit := 2*κ/Cphys
  let Gamma := Cphys/κ
  let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
  let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
  let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
  let DupperConst := θ*(3*Usrc/σsrc)*1/2
  let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
  let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
  let DlowerConst := 12*Usrc*θ/(csrc*κ)
  let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ
  let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*C₃/κ)/κ^2
  let Cgap := 64*Cphys*(Gamma^2*B+Gamma*C₃/κ)/κ
  let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
  let Ctail := 4*Cpack/Lunit^2+Cgap
  obtain ⟨hCphys,hc,hJ,hB,hBzero,hC₂,hC₃,hC₄,hCR,hCN,hCt,hCc,hCcurv,hKres,hEsize,hDbase,hTbase,hLunit,hGamma,hCthird,hAupper,hBupper,hDupper,hAlower,hBlower,hDlower,hCpack,hCfirst,hCgap,hCmain,hCtail⟩ :=
    general_source_constants_nonnegative hσ hδzero hκ hUsrc hσsrc hcsrc hθ hCU hCL hDU hDL
  let Sector := 2*3840*128^2*105*(Dbase+64*Tbase*Esize^2)
  obtain ⟨Bcut,Bselect,hBcut,hBsOne,hBsSize,hcutMargin,hsize,hBsize⟩ :=
    exists_source_cutoff_margins (Sector:=Sector) hκ hCcurv hCphys.le hEsize
  have hBs : 0 < Bselect := zero_lt_one.trans_le hBsOne
  let D₀ := 37*B/2+16*B*Cc+2*Ct+2*Cc
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  obtain ⟨Csep,hCsep,hselect⟩ :=
    exists_uniform_dyadic_band_integer_scales (J:=Usrc) hσsrc hBsOne hD₀ hCN
  obtain ⟨Bphys,hBphys,hCsepPhys,hbudget⟩ :=
    exists_uniform_source_physical_budget (zero_le_one.trans hCsep)
      (show 0 ≤ 3*Usrc/σsrc by positivity)
      (show 0 ≤ 3*Usrc/(4*σsrc) by positivity) hBzero
      (show 0 ≤ 56/κ by positivity)
      (show 0 ≤ 1/(Cphys+2) by positivity)
      (show 0 ≤ 14*σsrc/csrc by positivity)

  let Cbudget := max Bphys (24*Usrc/σsrc)
  have hBphysBudget : Bphys ≤ Cbudget := le_max_left _ _
  have hCbudget : 1 ≤ Cbudget := hBphys.trans hBphysBudget
  have hCsepBudget : Csep ≤ Cbudget := hCsepPhys.trans hBphysBudget
  have hCurveCoefficient : 24*Usrc/σsrc ≤ Cbudget := le_max_right _ _
  let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
  let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
  let Cap := 3*ChartCap*NarrowCap
  have hChartCap : 0 ≤ ChartCap := by dsimp only [ChartCap]; positivity
  have hNarrowCap : 0 ≤ NarrowCap := by dsimp only [NarrowCap]; positivity
  have hCap : 0 ≤ Cap := by dsimp only [Cap]; positivity
  let CLOW := 240*(9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+
    2*BlowerConst+(3/2:ℝ)*DlowerConst)
  have hCLOW : 0 ≤ CLOW :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg
          (mul_nonneg hAlower (sq_nonneg DlowerConst)) _))
          (mul_nonneg (by norm_num) hBlower))
        (mul_nonneg (by norm_num) hDlower))
  let Couter := (48*σsrc/csrc)^6*C*Cap^11
  have hCouter : 0 ≤ Couter := by dsimp only [Couter]; positivity
  let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
  let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
  let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
  have hNumeric := eventually_lower_finite_numerical_consequence
    hσsrc hcsrc hUsrc hκ hCphys.le (zero_le_one.trans hCsrc)
    hCouter hCLOW hDtype.le hBsOne hCsep hε
  have hLog : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  refine ⟨Cbudget,η₀,hCbudget,hη₀,hηcap,?_⟩
  filter_upwards [hfinite hθ hθmax hθaction,hNumeric,
    Filter.eventually_ge_atTop (1:ℝ),hLog] with T hfiniteT hNumericT hTone hLogOne
  intro Fsrc Y n N R Jsep η M hNlink hNtwo hR hη hηsmall hJsep hJM
    hy hsepY hreg hjets htests hnegative hmodels hscale
    hSepBudget hRadiusBudget hSquareBudget hCurveBudget hNfour hNten A Bint hA hAB hBint
    Yc ErrorTotal Main
  have hT : 0 < T := zero_lt_one.trans_le hTone
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := by linarith only [hNreal]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNOne : (1:ℝ) ≤ N := by linarith only [hNreal]
  have hNR : (N:ℝ) ≤ R^2 :=
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCbudget hNp.le :
      (N:ℝ) ≤ Cbudget*N).trans hRadiusBudget
  have hCsepRoom : Csep*R ≤ N :=
    (mul_le_mul_of_nonneg_right hCsepBudget hRp.le).trans hSepBudget
  obtain ⟨Qbase,kmax,Kmesh,Usel,hBaseLo,hBaseHi,hEndLo,hEndHi,hkmax,hKpos,hvalid,hUmono⟩ :=
    hselect N R hR hNR hCsepRoom
  let Q := fun k : ℕ => Qbase*2^k
  have hUzero : (Usel 0:ℝ) ≤ N := by
    obtain ⟨_,_,_,_,_,_,hUupper,_,_,_,hQstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hQone : (1:ℝ) ≤ Q 0 := by nlinarith only [hQstrong,hR]
    have hQzero : (0:ℝ) < Q 0 := zero_lt_one.trans_le hQone
    calc
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3)/Bselect := hUupper
      _ ≤ ((N:ℝ)/(Q 0:ℝ))^((2:ℝ)/3) := div_le_self (by positivity) hBsOne
      _ ≤ (N:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity)
        (div_le_self hNp.le hQone) (by norm_num)
      _ ≤ N := Real.rpow_le_self_of_one_le hNOne (by norm_num)
  have hSepPhys : Bphys*R ≤ N :=
    (mul_le_mul_of_nonneg_right hBphysBudget hRp.le).trans hSepBudget
  have hRadiusPhys : Bphys*(N:ℝ) ≤ R^2 :=
    (mul_le_mul_of_nonneg_right hBphysBudget hNp.le).trans hRadiusBudget
  have hSquarePhys : Bphys*(N:ℝ)^2 ≤ M :=
    (mul_le_mul_of_nonneg_right hBphysBudget (sq_nonneg (N:ℝ))).trans hSquareBudget
  obtain ⟨hM,hRN,hNR',hNsqM,hNRM,hNcube,hRM,hpad,hquartic,hquadratic,hsmall,hroom,hMTall⟩ :=
    hbudget (N:ℝ) R M (Usel 0:ℝ) hNreal hR hSepPhys hRadiusPhys hSquarePhys hUzero
  have hMT : M ≤ T := hMTall T hT hscale
  have hNM : (N:ℝ) ≤ M :=
    (by nlinarith only [hNreal] : (N:ℝ) ≤ (N:ℝ)^2).trans hNsqM
  have hNT : (N:ℝ) ≤ T := hNM.trans hMT
  have hRegimeLog : (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) :=
    hNfour.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hLogOne (by norm_num)))
  let Uband := (3*Usrc/σsrc)*T/(2*M^2)
  let Vscale := 1+R^4*Uband^2/(N:ℝ)^2
  have hVscale : 1 ≤ Vscale :=
    le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (pow_nonneg hRp.le 4) (sq_nonneg Uband)) (sq_nonneg (N:ℝ)))
  have hUband : Uband ≤ 1/16 := by
    have hh : (24*Usrc/σsrc)*T ≤ M^2 :=
      (mul_le_mul_of_nonneg_right hCurveCoefficient hT.le).trans hCurveBudget
    rw [show (24*Usrc/σsrc)*T=8*((3*Usrc/σsrc)*T) by ring] at hh
    dsimp only [Uband]
    apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hM))).mpr
    nlinarith only [hh]

  let μ₀ := csrc*T/(12*σsrc*M^3)
  let U₀ := Usrc*T/(2*σsrc*M^3)
  let Error := Yc*(M/(N:ℝ)+1)*
    (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
  let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  let Δtype := fun k : ℕ =>
    (16*U₀/μ₀)*Real.sqrt (U₀*(Q k:ℝ)^3)*Real.sqrt (Kmesh k)/(6*(Kmesh k:ℝ)^2)
  let Δ := fun k : ℕ => D₀*(Q k:ℝ)/(N:ℝ)
  let D := fun k : ℕ =>
    Δ k+quarticNonlinearResidualConstant σ δ*(2*(Q k:ℝ))/(N:ℝ)
  let Klower := fun k : ℕ =>
    240*(R^4/((N:ℝ)^2*(Usel k:ℝ)))*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
  let Buffer := fun k : ℕ =>
    (56*(Usel k:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
  let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
  let FamilyBound := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    (48*σsrc/csrc)^6*(R^2/(Q k:ℝ))^6*
      C*(Kmesh k:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
        (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
          ((P.image Prod.fst).card:ℝ)^2*Vscale*(Klower k)*T^εloss)
  let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
  let Endpoint := Yc*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
  have hvalidTri : ∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧ Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2 := by
    intro k hk
    obtain ⟨hUL,hSource,hMesh,_,hU,hWrap,hUpper,_,hQN,hUR,hStrong,hMin,hD,hDelta⟩ :=
      hvalid k hk
    exact ⟨hUL,hSource,hMesh,hU,hWrap,hUpper,hQN,hUR,hStrong,hMin,hD,hDelta⟩
  have hRoom : 2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M := by
    convert hroom using 1
    dsimp only [Buffer,Width]
    ring
  obtain ⟨Chunks,band,Dcover,hChunks,hBands,hTerminal,hGrids,hNorm⟩ :=
    hfiniteT Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale false
      (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      hKpos hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM
      hy hsepY hreg hjets htests hnegative hmodels hscale hpad hquartic hquadratic
      hRegimeLog hBcut hBsSize hcutMargin hNten hNsqM hNRM
      (by exact ⟨hUband,rfl⟩) hsmall hNR' hRN hNcube hsize hBsize hvalidTri
      (fun k _ => hUmono k) hRoom A Bint hA hAB hBint
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let Grid := fun (k : ℕ) (r : ℤ) =>
    ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let NumericFamily := fun (k : ℕ) (P : Finset (ℝ × ℤ)) =>
    Couter*(R^2/(Q k:ℝ))^6*(Kmesh k:ℝ)^((12:ℝ)+εloss)*(2*(P.card:ℝ))^10*
      (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
        ((P.image Prod.fst).card:ℝ)^2*Vscale*
          (CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)))*T^εloss)
  have hQbaseReal : (0:ℝ) < Qbase := by nlinarith only [hBaseLo,hRp]
  have hQbase : 0 < Qbase := by exact_mod_cast hQbaseReal
  have hvalidNumeric : ∀ k ≤ kmax,
      R ≤ (Q k:ℝ) ∧ Q k ≤ N ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      (Kmesh k:ℝ) ≤ (2*max 1 (63*Usrc/(2*σsrc)))*(Q k:ℝ)*(N:ℝ)/R^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) := by
    intro k hk
    obtain ⟨_,_,hMesh,hKU,_,_,hUpper,hLower,hQN,_,hStrong,_,_,_⟩ := hvalid k hk
    exact ⟨by nlinarith only [hStrong,hRp],hQN,hMesh,hKU,hUpper,hLower⟩
  have hKlower (k : ℕ) : Klower k=CLOW*R^4/((N:ℝ)^2*(Usel k:ℝ)) := by
    dsimp only [Klower,CLOW]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hFamilyEq (k : ℕ) (P : Finset (ℝ × ℤ)) :
      FamilyBound k P=NumericFamily k P := by
    dsimp only [FamilyBound,NumericFamily]
    rw [hKlower]
    dsimp only [Couter]
    ac_rfl
  let S := (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y), (𝐞 (f y j):ℂ)‖)^12
  change S ≤ 2^11*(((kmax:ℝ)+2)^11*
    (((n:ℝ)*Yc*Density kmax)^12+
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),∑ r∈Finset.Ico (0:ℤ) 8,
        (2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+Endpoint^12) at hNorm
  simp only [hFamilyEq] at hNorm
  exact hNumericT Y n N Qbase kmax Kmesh Usel R M Jsep Chunks band Dcover
    hNlink hNtwo hR hNR' hNsqM hMT hJsep.le hscale hQbase hBaseHi hEndLo hkmax hKpos
    hvalidNumeric hChunks hBands
    (fun k hk r => (hGrids k hk).2.2.1 r)
    (fun k hk r => (hGrids k hk).2.2.2 r) hNorm

example
    {σsrc csrc Usrc σ δ ε : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hδzero : 0 ≤ δ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hε : 0 < ε)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    ∃ Cbudget η₀ : ℝ, 1 ≤ Cbudget ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N : ℕ) (R Jsep : ℝ) {η M : ℝ},
      N=8*n → 2 ≤ N → 1 ≤ R → 0 < η → η ≤ η₀ →
      0 < Jsep → Jsep ≤ M →
      (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
      (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
        (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
      T*(N:ℝ)*R^2=M^3 →
      Cbudget*R ≤ N → Cbudget*(N:ℝ) ≤ R^2 → Cbudget*(N:ℝ)^2 ≤ M → Cbudget*T ≤ M^2 →
      (N:ℝ)^4 ≤ M*R^3 → (N:ℝ)^10 ≤ M^3*R^7 →
      ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
      (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
      let Yc := (Y.card:ℝ)
      let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
        Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
      let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+
        Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
        Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fsrc ((j:ℝ)/M)-Fsrc ((j:ℝ)/M+η*y))/(σsrc*η)):ℂ)‖)^12 ≤
        T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.eventually_lower_quantitative_phase_subinterval_bound (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (δ:=δ) (ε:=ε) hσsrc hcsrc hUsrc hσ hδzero hδ hε hanchorBudget


#print axioms HuxleyGeneralPhaseScratch.eventually_lower_quantitative_phase_subinterval_bound

private theorem approximateModelPhase_enlarged_quantitative_lower
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M → B*T ≤ M^2 →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) := by
  classical
  have hσone : 0<σ+1 := by linarith only [hσ]
  let δmodel := min (modelPhaseThirdLower (σ+1)) 1/2
  have hmin : 0 < min (modelPhaseThirdLower (σ+1)) 1 :=
    lt_min (modelPhaseThirdLower_pos hσone) zero_lt_one
  have hδmodel : 0<δmodel := half_pos hmin
  have hδmodelCap : δmodel ≤ min (modelPhaseThirdLower (σ+1)) 1 := by
    dsimp only [δmodel]
    linarith only [hmin]
  obtain ⟨δ,ηsrc,a,c,J,hδ,hηsrc,hηsrcCap,ha,hc,hJ,hanchor,hsource⟩ :=
    HuxleyRationalPhase.approximateModelPhase_enlarged_colored_common_scale_source
      hσ hδmodel (by norm_num : (0:ℝ)<1) 5 le_rfl
  have hanchor' : c≤4*modelPhaseThirdLower (σ+1)*1/((σ+1)*((σ+1)+1)+3) := by
    simpa only [add_assoc,show (1:ℝ)+1=2 by norm_num] using hanchor
  obtain ⟨Cbudget,ηquant,hCbudget,hηquant,_,hquant⟩ :=
    eventually_lower_quantitative_phase_subinterval_bound
      (by norm_num : (0:ℝ)<1) hc hJ hσone hδmodel.le hδmodelCap hε hanchor'
  obtain ⟨Tcut,hTcut⟩ := Filter.eventually_atTop.mp hquant
  let D := 2+2*σ+1/σ
  have hD : 1≤D := by
    dsimp only [D]
    have hi : 0<1/σ := div_pos zero_lt_one hσ
    linarith only [hσ,hi]
  have hDpos := zero_lt_one.trans_le hD
  have hDσ : 1≤D*σ := by
    have hi : (1/σ)*σ=1 := div_mul_cancel₀ 1 hσ.ne'
    dsimp only [D]
    nlinarith only [hi,hσ,sq_nonneg σ]
  have hσD : 2*σ≤D := by
    dsimp only [D]
    have hi : 0<1/σ := by positivity
    linarith only [hi]
  let B := Cbudget*D^7
  have hB : 1≤B := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ Cbudget*D^7 := mul_le_mul hCbudget (one_le_pow₀ hD)
        zero_le_one (zero_le_one.trans hCbudget)
  let Cap := 4/a+3
  have hCap : 1≤Cap := by
    dsimp only [Cap]
    have hh : 0<4/a := by positivity
    linarith only [hh]
  let K := (2*σ)^ε*D^24
  have hK : 0≤K := mul_nonneg
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε) (pow_nonneg hDpos.le 24)
  let C := max 1 (max (Tcut/σ) (Cap^12*K))
  have hC : 1≤C := le_max_left _ _
  have hCcut : Tcut/σ≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : Cap^12*K≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,min ηsrc ηquant,B,C,hδ,lt_min hηsrc hηquant,
    (min_le_left _ _).trans hηsrcCap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,_,_,hsharp,hcolors⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro T Y n N R Jsep η hT hN8 hN2 hRlow hη hηcap hJsep hJsepM
    hY hsep hphase hRN hNR hNM hCurve hFour hTen A Bint hA hAB hBint Yc ErrorTotal Main
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hRp : 0<R := zero_lt_one.trans_le (hB.trans hRlow)
  have hTp : 0<T := zero_lt_one.trans_le (hC.trans hT)
  have hYc : 0≤Yc := Nat.cast_nonneg _
  have hSigns := lower_expressions_nonnegative hYc hMp.le hNp.le hRp hJsep.le
  have hError : 0≤ErrorTotal := hSigns.1
  have hMain : 0≤Main := hSigns.2
  have hMass : 0≤ErrorTotal^12+Main := add_nonneg (pow_nonneg hError 12) hMain
  let color := fun y : ℝ => ⌊y/a⌋
  let z := fun y : ℝ => (‖∑ j∈Finset.Ioc (A y) (Bint y),
    (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖:ℂ)
  have hzNorm (U : Finset ℝ) :
      ‖∑ y∈U,z y‖ = ∑ y∈U,‖∑ j∈Finset.Ioc (A y) (Bint y),
        (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖ := by
    dsimp only [z]
    rw [←Complex.ofReal_sum]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  obtain ⟨hcard,hmoment,hclasses⟩ :=
    hcolors Y id η hY hη (hηcap.trans (min_le_left _ _))
  have hlocal (j : ℤ) (hj : j∈Y.image color) :
      ‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 ≤
        K*T^ε*(ErrorTotal^12+Main) := by
    obtain ⟨y₀,hy₀,_,hreg,hjets,htests,hnegative,hscaled⟩ := hclasses j hj
    let γ := σ*y₀
    have hy₀range := hY y₀ hy₀
    have hy₀p : 0<y₀ := zero_lt_one.trans_le hy₀range.1
    have hγ : 0<γ := mul_pos hσ hy₀p
    have hγlo : σ≤γ := le_mul_of_one_le_right hσ.le hy₀range.1
    have hγhi : γ≤2*σ := by dsimp only [γ]; nlinarith only [hy₀range.2,hσ]
    have hγD := hγhi.trans hσD
    have hDγ : 1≤D*γ := hDσ.trans (mul_le_mul_of_nonneg_left hγlo hDpos.le)
    let Fsrc := fun w => (1/(σ*y₀))*Fext w
    let Tnew := T*σ*y₀/1
    let Rnew := R*Real.sqrt (1/(σ*y₀))
    obtain ⟨hTnew,hRnew,hRsq,hnewphase,hmodels⟩ :=
      hscaled T (N:ℝ) R hTp hRp hphase
    have hTnewEq : Tnew=T*γ := by dsimp only [Tnew,γ]; rw [div_one,mul_assoc]
    have hRnewSq : Rnew^2=R^2/γ := by
      simpa only [mul_one] using hRsq
    have hRg : γ*Rnew^2=R^2 := by rw [hRnewSq]; field_simp
    obtain ⟨hSle,hRle⟩ := normalized_radius_comparable hRp hRnew hD hγD hDγ hRg
    obtain ⟨hRnew1,hnewRN,hnewNR,hnewNM,hnewFour,hnewTen⟩ :=
      comparable_radius_source_budgets hMp hNp hRp hD hCbudget hSle hRle
        hRlow hRN hNR hNM hFour hTen
    have hnewCurve : Cbudget*Tnew ≤ M^2 := by
      rw [hTnewEq]
      calc
        _ ≤ Cbudget*(T*D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hγD hTp.le) (zero_le_one.trans hCbudget)
        _ = (Cbudget*D)*T := by ring
        _ ≤ (Cbudget*D^7)*T :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (by simpa only [pow_one] using pow_le_pow_right₀ hD (by norm_num : 1≤7))
              (zero_le_one.trans hCbudget)) hTp.le
        _ ≤ M^2 := hCurve
    have hTnewCut : Tcut≤Tnew := by
      rw [hTnewEq]
      exact ((div_le_iff₀ hσ).mp (hCcut.trans hT)).trans
        (mul_le_mul_of_nonneg_left hγlo hTp.le)
    let Yj := Y.filter (fun y => color y=j)
    have hYj (y : ℝ) (hy : y∈Yj) : y∈Y :=
      (Finset.mem_filter.mp hy).1
    have hYjColor (y : ℝ) (hy : y∈Yj) : color y=j :=
      (Finset.mem_filter.mp hy).2
    have hmod (y : ℝ) (hy : y∈Yj) :
        Expdb.IsApproximateModelPhaseFunction
          (fun u => (Fsrc u-Fsrc (u+η*y))/(1*η)) (σ+1) 4 δmodel :=
      approximateModelPhase_mono (hmodels y (hYj y hy) (hYjColor y hy)).1
        (by norm_num) le_rfl
    have hq := hTcut Tnew hTnewCut Fsrc Yj n N Rnew Jsep hN8 hN2 hRnew1
      hη (hηcap.trans (min_le_right _ _)) hJsep hJsepM
      (fun y hy => hY y (hYj y hy))
      (fun y hy v hv hne => hsep y (hYj y hy) v (hYj v hv) hne)
      hreg hjets htests hnegative hmod hnewphase hnewRN hnewNR hnewNM hnewCurve
      hnewFour hnewTen A Bint (fun y hy => hA y (hYj y hy))
      (fun y hy => hAB y (hYj y hy)) (fun y hy => hBint y (hYj y hy))
    have hYj0 : (0:ℝ)≤Yj.card := Nat.cast_nonneg _
    have hYjCard : (Yj.card:ℝ)≤Yc := by
      change ((Y.filter (fun y => color y=j)).card:ℝ)≤(Y.card:ℝ)
      exact_mod_cast (Finset.card_filter_le Y (fun y => color y=j))
    let Enew := (Yj.card:ℝ)*M/Real.sqrt (N:ℝ)+
      (Yj.card:ℝ)*M*Rnew^2/(N:ℝ)^2+
      (Yj.card:ℝ)*(N:ℝ)*((N:ℝ)/Rnew)^((2:ℝ)/3)
    let MainNew := (Yj.card:ℝ)^11*M^13/((N:ℝ)^3*Rnew^6)+
      (Yj.card:ℝ)^11*Jsep*M^13/((N:ℝ)^5*Rnew^4)+
      (Yj.card:ℝ)^12*M^12/((N:ℝ)^4*Rnew^2)*(Rnew/(N:ℝ))^((2:ℝ)/3)
    have hEnew : Enew≤D^2*ErrorTotal :=
      upper_radius_error_bound hYj0 hYjCard hMp hNp hRp hRnew hD hSle hRle
    have hMainNew : MainNew≤D^6*Main :=
      lower_radius_main_bound hYj0 hYjCard hMp hNp hRp hRnew hD hJsep.le hSle hRle
    have hNewSigns := lower_expressions_nonnegative hYj0 hMp.le hNp.le hRnew hJsep.le
    have hEnew0 : 0≤Enew := hNewSigns.1
    have hMainNew0 : 0≤MainNew := hNewSigns.2
    have hEpow : Enew^12≤D^24*ErrorTotal^12 := by
      calc
        _ ≤ (D^2*ErrorTotal)^12 := pow_le_pow_left₀ hEnew0 hEnew 12
        _ = _ := by rw [mul_pow,←pow_mul]
    have hMainPow : MainNew≤D^24*Main :=
      hMainNew.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hD (by norm_num : 6≤24)) hMain)
    have hTotal : Enew^12+MainNew≤D^24*(ErrorTotal^12+Main) := by
      calc
        _ ≤ D^24*ErrorTotal^12+D^24*Main := add_le_add hEpow hMainPow
        _ = _ := (mul_add _ _ _).symm
    have hTpow : Tnew^ε≤(2*σ)^ε*T^ε := by
      rw [hTnewEq,Real.mul_rpow hTp.le hγ.le]
      calc
        _ ≤ T^ε*(2*σ)^ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le hγhi hε.le)
            (Real.rpow_nonneg hTp.le _)
        _ = _ := mul_comm _ _
    rw [hzNorm]
    calc
      _ = (∑ y∈Yj,‖∑ l∈Finset.Ioc (A y) (Bint y),
          (𝐞 (Tnew*(Fsrc ((l:ℝ)/M)-Fsrc ((l:ℝ)/M+η*y))/(1*η)):ℂ)‖)^12 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        apply congrArg (fun x : ℝ => (𝐞 x:ℂ))
        simpa only [one_mul] using ((hmodels y (hYj y hy) (hYjColor y hy)).2.1 (l:ℝ)).symm
      _ ≤ Tnew^ε*(Enew^12+MainNew) := hq
      _ ≤ ((2*σ)^ε*T^ε)*(D^24*(ErrorTotal^12+Main)) :=
        mul_le_mul hTpow hTotal (add_nonneg (pow_nonneg hEnew0 12) hMainNew0)
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hσ.le) ε)
            (Real.rpow_nonneg hTp.le ε))
      _ = _ := by dsimp only [K]; ac_rfl
  have hKmass : 0≤K*T^ε*(ErrorTotal^12+Main) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hTp.le ε)) hMass
  have hcolorSum :
      (∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12) ≤
        Cap*(K*T^ε*(ErrorTotal^12+Main)) := by
    calc
      _ ≤ ∑ _j∈Y.image color,K*T^ε*(ErrorTotal^12+Main) :=
        Finset.sum_le_sum hlocal
      _ = ((Y.image color).card:ℝ)*(K*T^ε*(ErrorTotal^12+Main)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hKmass
  calc
    _ = ‖∑ y∈Y,z y‖^12 := congrArg (fun x : ℝ => x^12) (hzNorm Y).symm
    _ ≤ Cap^11*∑ j∈Y.image color,‖∑ y∈Y.filter (fun y => color y=j),z y‖^12 :=
      hmoment z
    _ ≤ Cap^11*(Cap*(K*T^ε*(ErrorTotal^12+Main))) :=
      mul_le_mul_of_nonneg_left hcolorSum (pow_nonneg (zero_le_one.trans hCap) 11)
    _ = (Cap^12*K)*(T^ε*(ErrorTotal^12+Main)) := by
      rw [show Cap^12=Cap^11*Cap from pow_succ Cap 11]
      ac_rfl
    _ ≤ C*(T^ε*(ErrorTotal^12+Main)) :=
      mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg hTp.le ε) hMass)
    _ = _ := (mul_assoc _ _ _).symm

private theorem approximateModelPhase_enlarged_lower_correlation_moment
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M → B*(X*k/M)≤M^2 →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^13/((N:ℝ)^3*R^6)+K^11*K*M^13/((N:ℝ)^5*R^4)+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_quantitative_lower hσ hε
  let C := (2:ℝ)^12*C₀
  have hCC₀ : C₀≤C := le_mul_of_one_le_left (zero_le_one.trans hC₀) (by norm_num)
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hsharp,hupper⟩ := hsource M F hM hF
  refine ⟨Fext,hsharp,?_⟩
  intro X n N a L k R hT hN8 hN2 hR hk hη hKM ha hb hphase hRN hNR hNM
    hCurve hFour hTen K E Main
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hRp := zero_lt_one.trans_le (hB.trans hR)
  have hKp : 0<K := by
    change (0:ℝ)<k
    exact_mod_cast hk
  have hT1 : 1≤X*k/M := hC.trans hT
  have hTp := zero_lt_one.trans_le hT1
  let S := (Finset.Ico k (2*k)).filter (fun r => r≤L)
  let Y := S.image (fun (r:ℕ) => (r:ℝ)/(k:ℝ))
  let Bint := fun y : ℝ => ((a+(L-⌊(k:ℝ)*y⌋₊):ℕ):ℤ)
  obtain ⟨hcard,hY,hsep,hA,hAB,hBint,hcorr⟩ :=
    dyadic_shift_actual_family Fext X hMp a L k hk ha hb
  have hY0 : (0:ℝ)≤Y.card := Nat.cast_nonneg _
  have hYK : (Y.card:ℝ)≤K := by
    change (Y.card:ℝ)≤(k:ℝ)
    exact_mod_cast hcard
  let EY := (Y.card:ℝ)*M/Real.sqrt (N:ℝ)+(Y.card:ℝ)*M*R^2/(N:ℝ)^2+
    (Y.card:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let MainY := (Y.card:ℝ)^11*M^13/((N:ℝ)^3*R^6)+
    (Y.card:ℝ)^11*(k:ℝ)*M^13/((N:ℝ)^5*R^4)+
    (Y.card:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  have hEY : EY≤E := by
    have hh := upper_radius_error_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hMY : MainY≤Main := by
    have hh := lower_radius_main_bound hY0 hYK hMp hNp hRp hRp
      (show (1:ℝ)≤1 from le_rfl) hKp.le (by rw [one_mul]) (by rw [one_mul])
    simpa only [one_pow,one_mul] using hh
  have hYSigns := lower_expressions_nonnegative hY0 hMp.le hNp.le hRp hKp.le
  have hSigns := lower_expressions_nonnegative hKp.le hMp.le hNp.le hRp hKp.le
  have hEY0 : 0≤EY := hYSigns.1
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hMass0 : 0≤E^12+Main := add_nonneg (pow_nonneg hE0 12) hMain0
  have hMass : EY^12+MainY≤E^12+Main :=
    add_le_add (pow_le_pow_left₀ hEY0 hEY 12) hMY
  let Z := ∑ y∈Y,‖∑ l∈Finset.Ioc (a:ℤ) (Bint y),
    (𝐞 ((X*k/M)*(Fext ((l:ℝ)/M)-Fext ((l:ℝ)/M+((k:ℝ)/M)*y))/
      ((k:ℝ)/M)):ℂ)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hZ : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) := by
    have hu := hupper (X*k/M) Y n N R k ((k:ℝ)/M)
      (hCC₀.trans hT) hN8 hN2 hR (div_pos hKp hMp) hη hKp hKM hY hsep hphase
      hRN hNR hNM hCurve hFour hTen (fun _ => (a:ℤ)) Bint (fun _ _ => hA) hAB hBint
    exact hu.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (zero_le_one.trans hC₀) (Real.rpow_nonneg hTp.le ε)))
  have hQ : 1≤C₀*(X*k/M)^ε := by
    calc
      _ = (1:ℝ)*1 := by norm_num
      _ ≤ _ := mul_le_mul hC₀ (Real.one_le_rpow hT1 hε.le)
        zero_le_one (zero_le_one.trans hC₀)
  have hRleN : R≤(N:ℝ) :=
    (le_mul_of_one_le_left hRp.le hB).trans hRN
  have hKE : K≤E := upper_endpoint_error_absorption hKp.le hMp.le hN1 hRp hRleN
  have hKpow : K^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    ((pow_le_pow_left₀ hKp.le hKE 12).trans (le_add_of_nonneg_right hMain0)).trans
      (le_mul_of_one_le_left hMass0 hQ)
  have hCorr : (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)≤K+Z :=
    hcorr.trans (add_le_add hYK le_rfl)
  calc
    _ ≤ (K+Z)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hCorr 12
    _ ≤ (2:ℝ)^11*(K^12+Z^12) := add_pow_le hKp.le hZ0 12
    _ ≤ (2:ℝ)^11*(C₀*(X*k/M)^ε*(E^12+Main)+C₀*(X*k/M)^ε*(E^12+Main)) :=
      mul_le_mul_of_nonneg_left (add_le_add hKpow hZ) (by norm_num)
    _ = _ := by
      rw [←two_mul]
      dsimp only [C]
      rw [show (2:ℝ)^12=2^11*2 from pow_succ 2 11]
      ac_rfl

example
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ η₀ B C : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖ ≤ 6) ∧
          ∀ (T : ℝ) (Y : Finset ℝ) (n N : ℕ) (R Jsep η : ℝ),
            C ≤ T → N=8*n → 2 ≤ N → B ≤ R →
            0 < η → η ≤ η₀ → 0 < Jsep → Jsep ≤ M →
            (∀ y∈Y, y∈Icc (1:ℝ) 2) →
            (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
            T*(N:ℝ)*R^2=M^3 →
            B*R ≤ N → B*(N:ℝ) ≤ R^2 → B*(N:ℝ)^2 ≤ M → B*T ≤ M^2 →
            B*(N:ℝ)^4 ≤ M*R^3 → B*(N:ℝ)^10 ≤ M^3*R^7 →
            ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
              (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
              let Yc := (Y.card:ℝ)
              let ErrorTotal := Yc*M/Real.sqrt (N:ℝ)+Yc*M*R^2/(N:ℝ)^2+
                Yc*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
              let Main := Yc^11*M^13/((N:ℝ)^3*R^6)+Yc^11*Jsep*M^13/((N:ℝ)^5*R^4)+
                Yc^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
              (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),
                (𝐞 (T*(Fext ((j:ℝ)/M)-Fext ((j:ℝ)/M+η*y))/η):ℂ)‖)^12 ≤
                  C*T^ε*(ErrorTotal^12+Main) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_quantitative_lower (σ:=σ) (ε:=ε) hσ hε

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1≤M →
        Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        ∃ Fext : ℝ → ℝ,
          (∀ (X : ℝ) (a b : ℕ), M≤(a:ℝ) → (b:ℝ)≤2*M →
            ‖Expdb.exponentialSumAt F X M a b-
              Expdb.exponentialSumAt Fext X M a b‖≤6) ∧
          ∀ (X : ℝ) (n N a L k : ℕ) (R : ℝ),
            C≤X*k/M → N=8*n → 2≤N → B≤R →
            0<k → (k:ℝ)/M≤η₀ → (k:ℝ)≤M →
            M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
            (X*k/M)*(N:ℝ)*R^2=M^3 →
            B*R≤N → B*(N:ℝ)≤R^2 → B*(N:ℝ)^2≤M → B*(X*k/M)≤M^2 →
            B*(N:ℝ)^4≤M*R^3 → B*(N:ℝ)^10≤M^3*R^7 →
            let K := (k:ℝ)
            let E := K*M/Real.sqrt (N:ℝ)+K*M*R^2/(N:ℝ)^2+
              K*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
            let Main := K^11*M^13/((N:ℝ)^3*R^6)+K^11*K*M^13/((N:ℝ)^5*R^4)+
              K^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
            (∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖)^12 ≤
              C*(X*k/M)^ε*(E^12+Main) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_lower_correlation_moment (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_quantitative_lower
#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_enlarged_lower_correlation_moment

private theorem lower_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0 < X) (hM : 0 < M) (hN : 0 < N) (hK : 0 < K)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^13/(N^3*R^6))^3=X^9*K^42*M^3 ∧
    (K^11*K*M^13/(N^5*R^4))^3=X^6*K^42*M^15/N^9 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  constructor
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^18=(R^2)^9 by rw [←pow_mul],hR2]
    field_simp
    ring
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],hR2]
    field_simp
    ring

private theorem lower_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^13/(N^3*R^6))^3≤X^9*H^6*M^39 ∧
    (M/H)^36*(K^11*K*M^13/(N^5*R^4))^3≤X^6*H^6*M^51/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 := by
  obtain ⟨he₁,he₂,he₃,_,_,he₆⟩ :=
    upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  obtain ⟨h₁,h₂⟩ := lower_correlation_integer_moments hX hM hN hK hscale
  refine ⟨he₁,he₂,he₃,?_,?_,he₆⟩
  · rw [h₁]
    calc
      _ ≤ (M/H)^36*(X^9*H^42*M^3) := by gcongr
      _ = _ := by field_simp
  · rw [h₂]
    calc
      _ ≤ (M/H)^36*(X^6*H^42*M^15/N^9) := by gcongr
      _ = _ := by field_simp


private theorem weighted_lower_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^13/(N^3*R^6)+K^11*K*M^13/(N^5*R^4)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12)) := by
  intro E Main
  let e₁ := K*M/Real.sqrt N
  let e₂ := K*M*R^2/N^2
  let e₃ := K*N*(N/R)^((2:ℝ)/3)
  let a₁ := K^11*M^13/(N^3*R^6)
  let a₂ := K^11*K*M^13/(N^5*R^4)
  let a₃ := K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
  have he₁ : 0≤e₁ := by dsimp only [e₁]; positivity
  have he₂ : 0≤e₂ := by dsimp only [e₂]; positivity
  have he₃ : 0≤e₃ := by dsimp only [e₃]; positivity
  have ha₁ : 0≤a₁ := by dsimp only [a₁]; positivity
  have ha₂ : 0≤a₂ := by dsimp only [a₂]; positivity
  have ha₃ : 0≤a₃ := by dsimp only [a₃]; positivity
  have hE : E^36≤(2:ℝ)^72*(e₁^36+e₂^36+e₃^36) :=
    three_term_power_bound he₁ he₂ he₃ 36
  have hMain : Main^3≤(2:ℝ)^72*(a₁^3+a₂^3+a₃^3) :=
    (three_term_power_bound ha₁ ha₂ ha₃ 3).trans
      (mul_le_mul_of_nonneg_right (by norm_num)
        (add_nonneg (add_nonneg (pow_nonneg ha₁ 3) (pow_nonneg ha₂ 3)) (pow_nonneg ha₃ 3)))
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    lower_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  have hW : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  calc
    _ ≤ (M/H)^36*((2:ℝ)^72*(e₁^36+e₂^36+e₃^36)+
        (2:ℝ)^72*(a₁^3+a₂^3+a₃^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hMain) hW
    _ = (2:ℝ)^72*(((M/H)^36*e₁^36+(M/H)^36*e₂^36+(M/H)^36*e₃^36)+
        ((M/H)^36*a₁^3+(M/H)^36*a₂^3+(M/H)^36*a₃^3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add h₁ h₂) h₃)
        (add_le_add (add_le_add h₄ h₅) h₆)) (by norm_num)

private theorem lower_weyl_seventy_second_bound
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^13/(N^3*R^6)+K^11*K*M^13/(N^5*R^4)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^72≤(2:ℝ)^76*A^3*C^3*L^36*X^(3*ε)*
      (M^72/H^36+
        ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
          (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))) := by
  intro E Main hCorr hWeyl
  have hXp := zero_lt_one.trans_le hX
  have hC0 := zero_le_one.trans hC
  have hSigns := lower_expressions_nonnegative hK.le hM.le hN.le hR hK.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  let V := (M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
    (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12)
  have hV0 : 0≤V := by dsimp only [V]; positivity
  have hW0 : 0≤(M/H)^36 := pow_nonneg (div_nonneg hM.le hH.le) 36
  have hTpow : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hTpowOne : 1≤X^(3*ε) := Real.one_le_rpow hX (mul_nonneg (by norm_num) hε)
  have hXpCube : (X^ε)^3=X^(3*ε) := by
    rw [←Real.rpow_mul_natCast hXp.le]
    congr 1
    norm_num [mul_comm]
  have hCube : S^72≤A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := by
    simpa only [mul_pow,←pow_mul] using
      pow_le_pow_left₀ (pow_nonneg hS 24) hWeyl 3
  have hAdd : ((M^2/H)^12+(M/H)^12*Z^12)^3≤
      4*(M^72/H^36+(M/H)^36*Z^36) := by
    simpa only [div_pow,mul_pow,←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (by positivity : 0≤(M^2/H)^12)
        (by positivity : 0≤(M/H)^12*Z^12) 3
  have hSmain : S^72≤4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := by
    calc
      _ ≤ A^3*L^36*((M^2/H)^12+(M/H)^12*Z^12)^3 := hCube
      _ ≤ A^3*L^36*(4*(M^72/H^36+(M/H)^36*Z^36)) :=
        mul_le_mul_of_nonneg_left hAdd (mul_nonneg (pow_nonneg hA 3) (pow_nonneg hL 36))
      _ = _ := by ac_rfl
  have hZCube : Z^36≤C^3*X^(3*ε)*(E^12+Main)^3 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hZ 12) hCorr 3
    simpa only [mul_pow,←pow_mul,hXpCube] using hh
  have hEM : (E^12+Main)^3≤4*(E^36+Main^3) := by
    simpa only [←pow_mul,show (2:ℝ)^(3-1)=4 by norm_num] using
      add_pow_le (pow_nonneg hE0 12) hMain0 3
  have hZMoment : Z^36≤4*C^3*X^(3*ε)*(E^36+Main^3) := by
    calc
      _ ≤ C^3*X^(3*ε)*(E^12+Main)^3 := hZCube
      _ ≤ C^3*X^(3*ε)*(4*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hEM (mul_nonneg (pow_nonneg hC0 3) hTpow)
      _ = _ := by ac_rfl
  have hWeighted : (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*V :=
    weighted_lower_integer_moment_bound hXp hM hN hK hH hR hKH hscale
  let Q := (2:ℝ)^74*C^3*X^(3*ε)
  have hQ : 1≤Q := by
    calc
      _ ≤ C^3 := one_le_pow₀ hC
      _ ≤ C^3*X^(3*ε) := le_mul_of_one_le_right (pow_nonneg hC0 3) hTpowOne
      _ ≤ (2:ℝ)^74*(C^3*X^(3*ε)) :=
        le_mul_of_one_le_left (mul_nonneg (pow_nonneg hC0 3) hTpow) (by norm_num)
      _ = Q := (mul_assoc _ _ _).symm
  have hScaledZ : (M/H)^36*Z^36≤Q*V := by
    calc
      _ ≤ (M/H)^36*(4*C^3*X^(3*ε)*(E^36+Main^3)) :=
        mul_le_mul_of_nonneg_left hZMoment hW0
      _ = (4*C^3*X^(3*ε))*((M/H)^36*(E^36+Main^3)) := by ac_rfl
      _ ≤ (4*C^3*X^(3*ε))*((2:ℝ)^72*V) :=
        mul_le_mul_of_nonneg_left hWeighted
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 3)) hTpow)
      _ = Q*V := by
        dsimp only [Q]
        rw [show (2:ℝ)^74=4*2^72 by norm_num]
        ac_rfl
  have hDiag : M^72/H^36≤Q*(M^72/H^36) :=
    le_mul_of_one_le_left (by positivity) hQ
  calc
    _ ≤ 4*A^3*L^36*(M^72/H^36+(M/H)^36*Z^36) := hSmain
    _ ≤ 4*A^3*L^36*(Q*(M^72/H^36)+Q*V) :=
      mul_le_mul_of_nonneg_left (add_le_add hDiag hScaledZ)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 3)) (pow_nonneg hL 36))
    _ = _ := by
      rw [←mul_add]
      dsimp only [Q,V]
      rw [show (2:ℝ)^76=4*2^74 by norm_num]
      ring

private theorem sharp_extension_power_bound
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^72≤D*W*P) :
    ‖u‖^72≤(2:ℝ)^71*(D+E^72)*W*(1+P) := by
  have hW0 := zero_le_one.trans hW
  have hu : ‖u‖≤‖v‖+E := by
    calc
      _ = ‖v+(u-v)‖ := by congr 1; abel
      _ ≤ ‖v‖+‖u-v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsharp
  have hErr : E^72≤E^72*W :=
    le_mul_of_one_le_right (pow_nonneg hE 72) hW
  have hFold : D*W*P+E^72*W≤(D+E^72)*W*(1+P) := by
    nlinarith only [mul_nonneg hD hW0,
      mul_nonneg (mul_nonneg (pow_nonneg hE 72) hW0) hP]
  calc
    _ ≤ (‖v‖+E)^72 := pow_le_pow_left₀ (norm_nonneg _) hu 72
    _ ≤ (2:ℝ)^71*(‖v‖^72+E^72) := add_pow_le (norm_nonneg _) hE 72
    _ ≤ (2:ℝ)^71*(D*W*P+E^72*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hErr) (by norm_num)
    _ ≤ (2:ℝ)^71*((D+E^72)*W*(1+P)) :=
      mul_le_mul_of_nonneg_left hFold (by norm_num)
    _ = _ := by ac_rfl

private theorem approximateModelPhase_lower_original_seventy_second
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B*X*(H:ℝ)≤M^3 → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^9*(H:ℝ)^6*M^39+X^6*(H:ℝ)^6*M^51/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := by
  classical
  obtain ⟨δ,η₀,B,C₀,hδ,hη₀,hηcap,hB,hC₀,hsource⟩ :=
    approximateModelPhase_enlarged_lower_correlation_moment hσ hε
  let A₀ := (18:ℝ)^12*(2:ℝ)^11
  have hA₀ : 0≤A₀ := by dsimp only [A₀]; norm_num
  let D := (2:ℝ)^76*A₀^3*C₀^3
  have hD : 0≤D := mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg hA₀ 3)) (pow_nonneg (zero_le_one.trans hC₀) 3)
  let C := max C₀ ((2:ℝ)^71*(D+6^72))
  have hCC₀ : C₀≤C := le_max_left _ _
  have hCoeff : (2:ℝ)^71*(D+6^72)≤C := le_max_right _ _
  have hC : 1≤C := hC₀.trans hCC₀
  refine ⟨δ,η₀,B,C,hδ,hη₀,hηcap,hB,hC,?_⟩
  intro X M F n N H a L hX hM hF hN8 hN2 hH2 hHeta hThreshold
    hBN hRN hNR hNM hCurve hFour hTen ha hb
  have hXp := zero_lt_one.trans_le hX
  have hMp := zero_lt_one.trans_le hM
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hHM : (H:ℝ)≤M := by
    calc
      _ ≤ η₀*M := hHeta
      _ ≤ (1:ℝ)*M := mul_le_mul_of_nonneg_right
        (hηcap.trans (by norm_num : (1:ℝ)/8≤1)) hMp.le
      _ = M := one_mul M
  have hLM : (L:ℝ)+1≤2*M := by
    have hb' : (a:ℝ)+(L:ℝ)≤2*M := by simpa only [Nat.cast_add] using hb
    linarith only [hb',ha,hM]
  obtain ⟨Fext,hsharp,hcorr⟩ := hsource M F hM hF
  obtain ⟨k,hk,hkH,hweyl⟩ := exists_source_dyadic_twenty_fourth_power
    Fext X M a L H hMp hH2 hHM hLM
  have hKp : (0:ℝ)<k := by exact_mod_cast hk
  have hK1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hKH : (k:ℝ)≤H := by exact_mod_cast (show k≤H by omega)
  have hKM : (k:ℝ)≤M := hKH.trans hHM
  let R := Real.sqrt (M^4/(X*(k:ℝ)*(N:ℝ)))
  have hRadicand : 0<M^4/(X*(k:ℝ)*(N:ℝ)) :=
    div_pos (pow_pos hMp 4) (mul_pos (mul_pos hXp hKp) hNp)
  have hRp : 0<R := Real.sqrt_pos.mpr hRadicand
  have hR2 : R^2=M^4/(X*(k:ℝ)*(N:ℝ)) := Real.sq_sqrt hRadicand.le
  have hphase : (X*k/M)*(N:ℝ)*R^2=M^3 := by
    rw [hR2]
    field_simp
  obtain ⟨hBR,hRNN,hNRR,hNMM,hFourR,hTenR⟩ :=
    upper_all_shift_polynomial_budgets hXp hMp hNp hK1 hRp hB hKH hBN
      hphase hRN hNR hNM hFour hTen
  have hTbase : C₀≤X*k/M := by
    calc
      _ ≤ X/M := hCC₀.trans hThreshold
      _ ≤ (X/M)*(k:ℝ) := le_mul_of_one_le_right (div_nonneg hXp.le hMp.le) hK1
      _ = _ := by ring
  have hTbasePos := zero_lt_one.trans_le (hC₀.trans hTbase)
  have hTbaseUpper : X*k/M≤X :=
    (div_le_iff₀ hMp).mpr (mul_le_mul_of_nonneg_left hKM hXp.le)
  have hEtaK : (k:ℝ)/M≤η₀ := (div_le_iff₀ hMp).mpr (hKH.trans hHeta)
  let E := (k:ℝ)*M/Real.sqrt (N:ℝ)+(k:ℝ)*M*R^2/(N:ℝ)^2+
    (k:ℝ)*(N:ℝ)*((N:ℝ)/R)^((2:ℝ)/3)
  let Main := (k:ℝ)^11*M^13/((N:ℝ)^3*R^6)+(k:ℝ)^11*(k:ℝ)*M^13/((N:ℝ)^5*R^4)+
    (k:ℝ)^12*M^12/((N:ℝ)^4*R^2)*(R/(N:ℝ))^((2:ℝ)/3)
  let Z := ∑ j∈Finset.range k,‖sourceShiftCorrelation Fext X M a L (k+j)‖
  have hZ0 : 0≤Z := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCurveK : B*(X*k/M) ≤ M^2 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hMp).mpr
    calc
      _ ≤ B*(X*(H:ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hKH hXp.le) (zero_le_one.trans hB)
      _ ≤ M^3 := by simpa only [mul_assoc] using hCurve
      _ = M^2*M := by ring
  have hZbase : Z^12≤C₀*(X*k/M)^ε*(E^12+Main) :=
    hcorr X n N a L k R hTbase hN8 hN2 hBR hk hEtaK hKM ha hb hphase
      hRNN hNRR hNMM hCurveK hFourR hTenR
  have hSigns := lower_expressions_nonnegative hKp.le hMp.le hNp.le hRp hKp.le
  have hE0 : 0≤E := hSigns.1
  have hMain0 : 0≤Main := hSigns.2
  have hZ : Z^12≤C₀*X^ε*(E^12+Main) :=
    hZbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTbasePos.le hTbaseUpper hε.le)
        (zero_le_one.trans hC₀)) (add_nonneg (pow_nonneg hE0 12) hMain0))
  let Poly := M^72/(H:ℝ)^36+
    ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
        X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
      (X^9*(H:ℝ)^6*M^39+X^6*(H:ℝ)^6*M^51/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12))
  have hPoly : 0≤Poly := by dsimp only [Poly]; positivity
  have hClog : (0:ℝ)≤Nat.clog 2 H := Nat.cast_nonneg _
  have hClogPlus : (1:ℝ)≤1+(Nat.clog 2 H:ℝ) := le_add_of_nonneg_right hClog
  have hClogPlus0 := zero_le_one.trans hClogPlus
  have hXpow0 : 0≤X^(3*ε) := Real.rpow_nonneg hXp.le _
  have hSext : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤
      D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly :=
    lower_weyl_seventy_second_bound (norm_nonneg _) hZ0 hA₀ hC₀ hClog hX hMp hNp
      hKp hHp hRp hε.le hKH hphase hZ hweyl
  let W := (1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)
  have hW : 1≤W := by
    calc
      _ ≤ (1+(Nat.clog 2 H:ℝ))^36 := one_le_pow₀ hClogPlus
      _ ≤ _ := le_mul_of_one_le_right (pow_nonneg hClogPlus0 36)
        (Real.one_le_rpow hX (mul_nonneg (by norm_num) hε.le))
  have hLog : (Nat.clog 2 H:ℝ)^36≤(1+(Nat.clog 2 H:ℝ))^36 :=
    pow_le_pow_left₀ hClog (by linarith only) 36
  have hSext' : ‖Expdb.exponentialSumAt Fext X M a (a+L)‖^72≤D*W*Poly := by
    calc
      _ ≤ D*(Nat.clog 2 H:ℝ)^36*X^(3*ε)*Poly := hSext
      _ ≤ D*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*Poly :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLog hD) hXpow0) hPoly
      _ = _ := by dsimp only [W]; simp only [mul_assoc]
  have hOriginal := sharp_extension_power_bound hD hW hPoly (by norm_num : (0:ℝ)≤6)
    (hsharp X a (a+L) ha hb) hSext'
  calc
    _ ≤ (2:ℝ)^71*(D+6^72)*W*(1+Poly) := hOriginal
    _ ≤ C*W*(1+Poly) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoeff (zero_le_one.trans hW))
        (add_nonneg zero_le_one hPoly)
    _ = _ := by dsimp only [W,Poly]; simp only [mul_assoc]

example
    {X M N K R : ℝ} (hX : 0 < X) (hM : 0 < M) (hN : 0 < N) (hK : 0 < K)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^13/(N^3*R^6))^3=X^9*K^42*M^3 ∧
    (K^11*K*M^13/(N^5*R^4))^3=X^6*K^42*M^15/N^9 :=
  HuxleyGeneralPhaseScratch.lower_correlation_integer_moments (X:=X) (M:=M) (N:=N) (K:=K) (R:=R) hX hM hN hK hscale

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^13/(N^3*R^6))^3≤X^9*H^6*M^39 ∧
    (M/H)^36*(K^11*K*M^13/(N^5*R^4))^3≤X^6*H^6*M^51/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 :=
  HuxleyGeneralPhaseScratch.lower_integer_moments_all_shifts (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^13/(N^3*R^6)+K^11*K*M^13/(N^5*R^4)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12)) :=
  HuxleyGeneralPhaseScratch.weighted_lower_integer_moment_bound (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) hX hM hN hK hH hR hKH hscale

example
    {S Z A C L X M N K H R ε : ℝ}
    (hS : 0≤S) (hZ : 0≤Z) (hA : 0≤A) (hC : 1≤C) (hL : 0≤L)
    (hX : 1≤X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hε : 0≤ε) (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^13/(N^3*R^6)+K^11*K*M^13/(N^5*R^4)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    Z^12≤C*X^ε*(E^12+Main) →
    S^24≤A*L^12*((M^2/H)^12+(M/H)^12*Z^12) →
    S^72≤(2:ℝ)^76*A^3*C^3*L^36*X^(3*ε)*
      (M^72/H^36+
        ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
          (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))) :=
  HuxleyGeneralPhaseScratch.lower_weyl_seventy_second_bound (S:=S) (Z:=Z) (A:=A) (C:=C) (L:=L) (X:=X) (M:=M) (N:=N) (K:=K) (H:=H) (R:=R) (ε:=ε) hS hZ hA hC hL hX hM hN hK hH hR hε hKH hscale

example
    {u v : ℂ} {D W P E : ℝ} (hD : 0≤D) (hW : 1≤W) (hP : 0≤P) (hE : 0≤E)
    (hsharp : ‖u-v‖≤E) (hv : ‖v‖^72≤D*W*P) :
    ‖u‖^72≤(2:ℝ)^71*(D+E^72)*W*(1+P) :=
  HuxleyGeneralPhaseScratch.sharp_extension_power_bound (u:=u) (v:=v) (D:=D) (W:=W) (P:=P) (E:=E) hD hW hP hE hsharp hv

example
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B*X*(H:ℝ)≤M^3 → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^9*(H:ℝ)^6*M^39+X^6*(H:ℝ)^6*M^51/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) :=
  HuxleyGeneralPhaseScratch.approximateModelPhase_lower_original_seventy_second (σ:=σ) (ε:=ε) hσ hε


#print axioms HuxleyGeneralPhaseScratch.lower_correlation_integer_moments
#print axioms HuxleyGeneralPhaseScratch.lower_integer_moments_all_shifts
#print axioms HuxleyGeneralPhaseScratch.weighted_lower_integer_moment_bound
#print axioms HuxleyGeneralPhaseScratch.lower_weyl_seventy_second_bound
#print axioms HuxleyGeneralPhaseScratch.sharp_extension_power_bound
#print axioms HuxleyGeneralPhaseScratch.approximateModelPhase_lower_original_seventy_second

private theorem eventually_uniform_clog_power_loss
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^36≤X^ζ := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D := 1+2/Real.log 2
  have hD : 0≤D := by dsimp only [D]; positivity
  have hLoss := eventually_const_log_pow_le_rpow
    (C*D^36) (mul_nonneg hC (pow_nonneg hD 36)) 36 hζ
  filter_upwards [hLoss,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1:ℝ)] with X hLossX hlogX hX
  intro H hH hHX
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hlogHX := Real.log_le_log hHp hHX
  have hc : (Nat.clog 2 H:ℝ)≤(2/Real.log 2)*Real.log X := by
    calc
      _ ≤ 2*(Real.log H/Real.log 2) := nat_clog_two_le_twice_log H hH
      _ ≤ 2*(Real.log X/Real.log 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogHX hlog2.le) (by norm_num)
      _ = _ := by ring
  have hplus : 1+(Nat.clog 2 H:ℝ)≤D*Real.log X := by
    dsimp only [D]
    nlinarith only [hc,hlogX]
  calc
    _ ≤ C*(D*Real.log X)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hplus 36) hC
    _ = (C*D^36)*(Real.log X)^36 := by rw [mul_pow,mul_assoc]
    _ ≤ X^ζ := hLossX

private theorem eventually_lower_polynomial_power_window
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ) (hCurve : 1+h<3*ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B*X*(H:ℝ)≤M^3 ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 := by
  have hBase := eventually_upper_polynomial_power_window
    hB hC hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  have hCurvedom := eventually_const_mul_rpow_le_rpow (D:=B) hCurve
  filter_upwards [hBase,hCurvedom] with X hBaseX hCurveX
  refine ⟨hBaseX.1,?_⟩
  intro M hMl hMu n N H
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
    hNMM,hFourM,hTenM⟩ := hBaseX.2 M hMl hMu
  have hXp := zero_lt_one.trans_le hBaseX.1
  refine ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
    hNMM,?_,hFourM,hTenM⟩
  calc
    _ ≤ B*X*(X^h) := mul_le_mul_of_nonneg_left hHu
      (mul_nonneg (zero_le_one.trans hB) hXp.le)
    _ = B*X^(1+h) := by rw [Real.rpow_add hXp,Real.rpow_one,mul_assoc]
    _ ≤ X^(3*ℓ) := hCurveX
    _ = (X^ℓ)^3 := by
      simpa only [Nat.cast_ofNat,mul_comm] using Real.rpow_mul_natCast hXp.le ℓ 3
    _ ≤ M^3 := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hMl 3


private theorem lower_seven_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 9+6*h+39*u≤ξ) (hType2 : 6+6*h+51*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ := by
  have hXp := zero_lt_one.trans_le hX
  have hMp : 0<M := (Real.rpow_pos_of_pos hXp ℓ).trans_le hMl
  have hNp : 0<N := (div_pos (Real.rpow_pos_of_pos hXp ν) (by norm_num)).trans_le hNl
  have hHp : 0<H := (div_pos (Real.rpow_pos_of_pos hXp h) (by norm_num)).trans_le hHl
  have hconst {b : ℝ} {j : ℕ} (hj : j≤144) (hb : b≤ξ) :
      (2:ℝ)^j*X^b≤(2:ℝ)^144*X^ξ :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hj)
      (Real.rpow_le_rpow_of_exponent_le hX hb) (Real.rpow_nonneg hXp.le _) (by positivity)
  have h₀ : 1≤(2:ℝ)^144*X^ξ :=
    (Real.one_le_rpow hX hξ).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by norm_num))
  have h₁ : M^72/H^36≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^h/2)^36 := by gcongr
      _ = (2:ℝ)^36*((X^u)^72/(X^h)^36) := by field_simp
      _ = (2:ℝ)^36*X^(72*u-36*h) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^36*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hDiag
  have h₂ : M^72/N^18≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^72/(X^ν/2)^18 := by gcongr
      _ = (2:ℝ)^18*((X^u)^72/(X^ν)^18) := by field_simp
      _ = (2:ℝ)^18*X^(72*u-18*ν) := by
        rw [←Real.rpow_mul_natCast hXp.le,←Real.rpow_mul_natCast hXp.le,
          ←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^18*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hSqrt
  have h₃ : M^216/(H^36*X^36*N^108)≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ (X^u)^216/((X^h/2)^36*X^36*(X^ν/2)^108) := by gcongr
      _ = (2:ℝ)^144*((X^u)^216/((X^h)^36*X^36*(X^ν)^108)) := by field_simp
      _ = (2:ℝ)^144*X^(216*u-36*h-36-108*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 36]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^144*X^y)
        push_cast
        ring
      _ ≤ _ := hconst le_rfl hCubic
  have h₄ : X^12*H^12*N^72/M^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^12*(X^h)^12*(X^ν)^72/(X^ℓ)^12 := by gcongr
      _ = X^(12+12*h+72*ν-12*ℓ) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 12]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hEndpoint
  have h₅ : X^9*H^6*M^39≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^9*(X^h)^6*(X^u)^39 := by gcongr
      _ = X^(9+6*h+39*u) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 9]
        simp only [←Real.rpow_add hXp]
        apply congrArg (fun y : ℝ => X^y)
        push_cast
        ring
      _ ≤ _ := by simpa only [pow_zero,one_mul] using hconst (j:=0) (by omega) hType1
  have h₆ : X^6*H^6*M^51/N^9≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^6*(X^h)^6*(X^u)^51/(X^ν/2)^9 := by gcongr
      _ = (2:ℝ)^9*(X^6*(X^h)^6*(X^u)^51/(X^ν)^9) := by field_simp
      _ = (2:ℝ)^9*X^(6+6*h+51*u-9*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 6]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^9*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hType2
  have h₇ : X^2*H^2*M^64/N^12≤(2:ℝ)^144*X^ξ := by
    calc
      _ ≤ X^2*(X^h)^2*(X^u)^64/(X^ν/2)^12 := by gcongr
      _ = (2:ℝ)^12*(X^2*(X^h)^2*(X^u)^64/(X^ν)^12) := by field_simp
      _ = (2:ℝ)^12*X^(2+2*h+64*u-12*ν) := by
        simp only [←Real.rpow_mul_natCast hXp.le]
        rw [←Real.rpow_natCast X 2]
        simp only [←Real.rpow_add hXp,←Real.rpow_sub hXp]
        apply congrArg (fun y : ℝ => (2:ℝ)^12*X^y)
        push_cast
        ring
      _ ≤ _ := hconst (by norm_num) hPair
  linarith only [h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]

private theorem lower_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hCurve : 1+h<3*((α:ℝ)-δw))
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 9+6*h+39*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 6+6*h+51*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    approximateModelPhase_lower_original_seventy_second hσ hεs
  have hPhys := eventually_lower_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hCurve hFour hTen
  have hLog := eventually_uniform_clog_power_loss
    (C:=Csrc*(8*(2:ℝ)^144))
    (mul_nonneg (zero_le_one.trans hCsrc) (by norm_num)) hζ
  obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp (hPhys.and hLog)
  let δ := min δsrc δw
  let C := max 1 T₀
  have hC : 1≤C := le_max_left _ _
  refine ⟨δ,lt_min hδsrc hδw,7,by norm_num,C,hC,?_⟩
  intro T M F a b setup
  have hT : 1≤T := hC.trans setup.threshold_le_param
  have hTp := zero_lt_one.trans_le hT
  have hTogether := hT₀ T ((le_max_right 1 T₀).trans setup.threshold_le_param)
  by_cases hba : b<a
  · rw [Expdb.exponentialSumAt_of_lt hba,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)
  have hab : a≤b := Nat.le_of_not_gt hba
  let L := b-a
  have hEnd : a+L=b := Nat.add_sub_of_le hab
  have hδwle : δ≤δw := min_le_right _ _
  have hδsrcle : δ≤δsrc := min_le_left _ _
  have hMl : T^((α:ℝ)-δw)≤M :=
    (Real.rpow_le_rpow_of_exponent_le hT (sub_le_sub_left hδwle _)).trans
      setup.rpow_sub_le_scale
  have hMu : M≤T^((α:ℝ)+δw) := setup.scale_le_rpow_add.trans
    (Real.rpow_le_rpow_of_exponent_le hT (add_le_add le_rfl hδwle))
  have hF := approximateModelPhase_mono setup.isApproximateModelPhase le_rfl hδsrcle
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hCurveM,hFourM,hTenM⟩ := hTogether.1.2 M hMl hMu
  have hStart := setup.scale_le_start
  have hStop : ((a+L:ℕ):ℝ)≤2*M := by rw [hEnd]; exact setup.end_le_two_mul_scale
  have hActual := hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM hCurveM hFourM hTenM hStart hStop
  let ξ := 72*β-3*εs-ζ
  have hξ : 0≤ξ := by dsimp only [ξ]; linarith only [hBase]
  have hPoly := lower_seven_monomials_power_window hT hξ hMl hMu hNl hNu hHl hHu
    (by dsimp only [ξ]; linarith only [hDiag])
    (by dsimp only [ξ]; linarith only [hSqrt])
    (by dsimp only [ξ]; linarith only [hCubic])
    (by dsimp only [ξ]; linarith only [hEndpoint])
    (by dsimp only [ξ]; linarith only [hType1])
    (by dsimp only [ξ]; linarith only [hType2])
    (by dsimp only [ξ]; linarith only [hPair])
  have hh1 : h≤1 := by linarith only [hhℓ,hu,hδw]
  have hHT : (H:ℝ)≤T := hHu.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hh1)
  have hLoss := hTogether.2 H hH2 hHT
  have hCsrc0 := zero_le_one.trans hCsrc
  have hLog0 : 0≤(1+(Nat.clog 2 H:ℝ))^36 := pow_nonneg (by positivity) _
  have hXpow0 := Real.rpow_nonneg hTp.le (3*εs)
  have hPower : ‖Expdb.exponentialSumAt F T M a b‖^72≤T^(72*β) := by
    rw [←hEnd]
    calc
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*
          (1+ (M^72/(H:ℝ)^36+
            ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*T^36*(N:ℝ)^108)+
                T^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
              (T^9*(H:ℝ)^6*M^39+T^6*(H:ℝ)^6*M^51/(N:ℝ)^9+T^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := hActual
      _ ≤ Csrc*(1+(Nat.clog 2 H:ℝ))^36*T^(3*εs)*((8*(2:ℝ)^144)*T^ξ) :=
        mul_le_mul_of_nonneg_left hPoly (mul_nonneg (mul_nonneg hCsrc0 hLog0) hXpow0)
      _ = (Csrc*(8*(2:ℝ)^144)*(1+(Nat.clog 2 H:ℝ))^36)*T^(3*εs)*T^ξ := by ac_rfl
      _ ≤ T^ζ*T^(3*εs)*T^ξ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLoss hXpow0) (Real.rpow_nonneg hTp.le _)
      _ = T^(72*β) := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
        apply congrArg (fun x : ℝ => T^x)
        dsimp only [ξ]
        ring
  have hRootPower : (T^β)^72=T^(72*β) := by
    simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hTp.le β 72).symm
  have hRoot : ‖Expdb.exponentialSumAt F T M a b‖≤T^β :=
    le_of_pow_le_pow_left₀ (by norm_num : (72:ℕ)≠0)
      (Real.rpow_nonneg hTp.le _) (hPower.trans_eq hRootPower.symm)
  calc
    _ ≤ T^β := hRoot
    _ ≤ T^(β+ε) := Real.rpow_le_rpow_of_exponent_le hT (le_add_of_nonneg_right hε.le)
    _ ≤ C*T^(β+ε) := le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC

private theorem lower_tenth_row_nonAsymptotic
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((29+173*(α:ℝ))/280) := by
  let t := ((α:ℝ)-(227:ℝ)/601)/((12:ℝ)/31-(227:ℝ)/601)
  let ν := (1-t)*((176056:ℝ)/1000000)+t*((193164:ℝ)/1000000)
  let h := (1-t)*((82482:ℝ)/1000000)+t*((89862:ℝ)/1000000)
  apply lower_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

private theorem exponentSumGrowthExponent_le_huxley_tenthRow
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.exponentSumGrowthExponent α≤(29+173*(α:ℝ))/280 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (lower_tenth_row_nonAsymptotic hα hα₁)

private theorem lower_eleventh_row_nonAsymptotic
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((4+103*(α:ℝ))/128) := by
  let t := ((α:ℝ)-(12:ℝ)/31)/((1508:ℝ)/3825-(12:ℝ)/31)
  let ν := (1-t)*((193164:ℝ)/1000000)+t*((197119:ℝ)/1000000)
  let h := (1-t)*((89862:ℝ)/1000000)+t*((92616:ℝ)/1000000)
  apply lower_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

private theorem exponentSumGrowthExponent_le_huxley_eleventhRow
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.exponentSumGrowthExponent α≤(4+103*(α:ℝ))/128 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (lower_eleventh_row_nonAsymptotic hα hα₁)


example
    {C ζ : ℝ} (hC : 0≤C) (hζ : 0<ζ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℕ, 2≤H → (H:ℝ)≤X →
      C*(1+(Nat.clog 2 H:ℝ))^36≤X^ζ :=
  HuxleyGeneralPhaseScratch.eventually_uniform_clog_power_loss (C:=C) (ζ:=ζ) hC hζ

example
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ) (hCurve : 1+h<3*ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B*X*(H:ℝ)≤M^3 ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 :=
  HuxleyGeneralPhaseScratch.eventually_lower_polynomial_power_window (B:=B) (C:=C) (η:=η) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) hB hC hη hℓ hν hh hu hhℓ hRN hNR hNM hCurve hFour hTen

example
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 9+6*h+39*u≤ξ) (hType2 : 6+6*h+51*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ :=
  HuxleyGeneralPhaseScratch.lower_seven_monomials_power_window (X:=X) (M:=M) (N:=N) (H:=H) (ℓ:=ℓ) (u:=u) (ν:=ν) (h:=h) (ξ:=ξ) hX hξ hMl hMu hNl hNu hHl hHu hDiag hSqrt hCubic hEndpoint hType1 hType2 hPair

example
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hCurve : 1+h<3*((α:ℝ)-δw))
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 9+6*h+39*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 6+6*h+51*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β :=
  HuxleyGeneralPhaseScratch.lower_beta_of_power_window (α:=α) (β:=β) (δw:=δw) (ν:=ν) (h:=h) (εs:=εs) (ζ:=ζ) hδw hν hh hεs hζ hℓ hu hhℓ hRN hNR hNM hCurve hFour hTen hBase hDiag hSqrt hCubic hEndpoint hType1 hType2 hPair

example
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((29+173*(α:ℝ))/280) :=
  HuxleyGeneralPhaseScratch.lower_tenth_row_nonAsymptotic (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.exponentSumGrowthExponent α≤(29+173*(α:ℝ))/280 :=
  HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((4+103*(α:ℝ))/128) :=
  HuxleyGeneralPhaseScratch.lower_eleventh_row_nonAsymptotic (α:=α) hα hα₁

example
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.exponentSumGrowthExponent α≤(4+103*(α:ℝ))/128 :=
  HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) hα hα₁


#print axioms HuxleyGeneralPhaseScratch.eventually_uniform_clog_power_loss
#print axioms HuxleyGeneralPhaseScratch.eventually_lower_polynomial_power_window
#print axioms HuxleyGeneralPhaseScratch.lower_seven_monomials_power_window
#print axioms HuxleyGeneralPhaseScratch.lower_beta_of_power_window
#print axioms HuxleyGeneralPhaseScratch.lower_tenth_row_nonAsymptotic
#print axioms HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_tenthRow
#print axioms HuxleyGeneralPhaseScratch.lower_eleventh_row_nonAsymptotic
#print axioms HuxleyGeneralPhaseScratch.exponentSumGrowthExponent_le_huxley_eleventhRow

open Expdb TaoTrudgianYang2025.CubicJointCount

private theorem exponentPair_taoTrudgianYang_firstNew : ExponentPair (89/1282) (997/1282) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

private theorem exponentPair_taoTrudgianYang_secondNew : ExponentPair (652397/9713986) (7599781/9713986) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

private theorem exponentPair_bourgain_piece_two_input : ExponentPair (391/4595) (3461/4595) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

private theorem exponentPair_bourgain_piece_three_input : ExponentPair (2779/38033) (58699/76066) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := exponentSumGrowthExponent_le_huxley_seventhRow (α:=α) (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := exponentSumGrowthExponent_le_huxley_eighthRow (α:=α) (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := exponentSumGrowthExponent_le_huxley_ninthRow (α:=α) (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := exponentSumGrowthExponent_le_huxley_tenthRow (α:=α) (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := exponentSumGrowthExponent_le_huxley_eleventhRow (α:=α) (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

private theorem zeroDensityExponent_le_bourgain_piece_2 {σ : ℝ}
    (hσ : 14/15 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceTwo σ):EReal) := by
  exact exponentPair_bourgain_piece_two_input.bourgain_piece_2 hσ hσ1

private theorem zeroDensityExponent_le_bourgain_piece_3 {σ : ℝ}
    (hσ : 2841/3016 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceThree σ):EReal) := by
  exact exponentPair_bourgain_piece_three_input.bourgain_piece_3 hσ hσ1

private theorem zeroDensityExponent_le_bourgain_piece_4 {σ : ℝ}
    (hσ : 859/908 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFour σ):EReal) := by
  exact exponentPair_taoTrudgianYang_firstNew.bourgain_piece_4 hσ hσ1

private theorem zeroDensityExponent_le_bourgain_piece_5 {σ : ℝ}
    (hσ : 1625/1692 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFive σ):EReal) := by
  exact exponentPair_taoTrudgianYang_secondNew.bourgain_piece_5 hσ hσ1


example : ExponentPair (89/1282) (997/1282) :=
  HuxleyGeneralPhaseScratch.exponentPair_taoTrudgianYang_firstNew 

example : ExponentPair (652397/9713986) (7599781/9713986) :=
  HuxleyGeneralPhaseScratch.exponentPair_taoTrudgianYang_secondNew 

example : ExponentPair (391/4595) (3461/4595) :=
  HuxleyGeneralPhaseScratch.exponentPair_bourgain_piece_two_input 

example : ExponentPair (2779/38033) (58699/76066) :=
  HuxleyGeneralPhaseScratch.exponentPair_bourgain_piece_three_input 

example {σ : ℝ}
    (hσ : 14/15 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceTwo σ):EReal) :=
  HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_2 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 2841/3016 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceThree σ):EReal) :=
  HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_3 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 859/908 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFour σ):EReal) :=
  HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_4 (σ:=σ) hσ hσ1

example {σ : ℝ}
    (hσ : 1625/1692 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((bourgainPieceFive σ):EReal) :=
  HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_5 (σ:=σ) hσ hσ1


#print axioms HuxleyGeneralPhaseScratch.exponentPair_taoTrudgianYang_firstNew
#print axioms HuxleyGeneralPhaseScratch.exponentPair_taoTrudgianYang_secondNew
#print axioms HuxleyGeneralPhaseScratch.exponentPair_bourgain_piece_two_input
#print axioms HuxleyGeneralPhaseScratch.exponentPair_bourgain_piece_three_input
#print axioms HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_2
#print axioms HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_3
#print axioms HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_4
#print axioms HuxleyGeneralPhaseScratch.zeroDensityExponent_le_bourgain_piece_5

end HuxleyGeneralPhaseScratch
