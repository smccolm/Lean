import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyOriginalPairMassScratch

private theorem huxley_narrowing_balanced_scale
    {U V a b : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2)) :
    V*(a/V^((5:ℝ)/3)+b/(U*V))=(a+b)/U := by
  subst V
  have hUp : 0 < U^((3:ℝ)/2) := Real.rpow_pos_of_pos hU _
  have he : (U^((3:ℝ)/2))^((5:ℝ)/3)=U*U^((3:ℝ)/2) := by
    rw [←Real.rpow_mul hU.le]
    rw [show ((3:ℝ)/2)*(5/3)=1+3/2 by norm_num,Real.rpow_add hU,Real.rpow_one]
  rw [he]
  field_simp

private theorem huxley_narrowing_balanced_mass
    {mass K a b U V : ℝ} (hU : 0 < U) (hV : V=U^((3:ℝ)/2))
    (h : mass ≤ K*(a/V^((5:ℝ)/3)+b/(U*V))) :
    V*mass ≤ K*(a+b)/U := by
  have hVp : 0 < V := by rw [hV]; exact Real.rpow_pos_of_pos hU _
  calc
    V*mass ≤ V*(K*(a/V^((5:ℝ)/3)+b/(U*V))) :=
      mul_le_mul_of_nonneg_left h hVp.le
    _ = K*(V*(a/V^((5:ℝ)/3)+b/(U*V))) := by ring
    _ = K*((a+b)/U) := by rw [huxley_narrowing_balanced_scale hU hV]
    _ = _ := by ring

private theorem huxley_reference_reciprocal_scale
    {N Q B U : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hB : 0 < B)
    (hU : (N/Q)^((2:ℝ)/3)/(2*B) ≤ U) :
    1/U ≤ 2*B*(Q/N)^((2:ℝ)/3) := by
  have hp : 0 < (N/Q)^((2:ℝ)/3) :=
    Real.rpow_pos_of_pos (div_pos hN hQ) _
  have hh := one_div_le_one_div_of_le (div_pos hp (by positivity)) hU
  apply hh.trans_eq
  rw [one_div_div,div_eq_mul_inv,←Real.inv_rpow (div_pos hN hQ).le]
  rw [inv_div]


theorem physicalModelPhase_actual_fourier_original_pair_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ}
    (hbase : ∀ ij∈P, base ≤ za ij.1.1)
    (hxa : ∀ ij∈P, x ij 0=za ij.1.1)
    (hxb : ∀ ij∈P, x ij 1=zb ij.2.1)
    (hgapMem : ∀ ij∈P, gap ij∈Gaps)
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < (N:ℝ))
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hmesh : (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband)
    (hinv : ∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : (N:ℝ)^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2)
    (hc : ∀ ij∈P, Mat ij 2 ≠ 0)
    (hlarge : ∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
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
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
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
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*(N:ℝ)^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*(N:ℝ)^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/((N:ℝ)^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kmass := 60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
    ((P.card:ℝ) ≤
      60*588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (P.card:ℝ) ≤
      60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
      V*(P.card:ℝ) ≤ 2*Bselect*Kmass*(Cmain+Ctail)*
        ((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail Kmass
  have hNnat : 0 < N := by exact_mod_cast hN
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hz ij (hij : ij∈P) : zb ij.2.1∈Ioo 0 (W 1) := by
    have hh := hx ij hij 1
    rw [hxb ij hij] at hh
    constructor <;> linarith only [hh.1,hh.2]
  have hmodelMap ij (hij : ij∈P) :
      ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f 1) (zb ij.2.1)/2 := by
    rw [←hxa ij hij,←hxb ij hij,hlevel ij hij 0,hlevel ij hij 1]
    exact hMatmap ij hij
  let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    ⌊(za ij.1.1-base)/(N:ℝ)⌋.toNat
  let S := fun B ab => (P.filter (fun ij => Mat ij=B ∧ gap ij=ab)).image block
  let Matrices := P.image Mat
  obtain ⟨pick,hpick,hpairNat⟩ := physicalModelPhase_reference_matrix_window_selection
    P Mat gap F A W za zb AlenA AlenB N Za Zb base hσ hδ hF₂ hT hM hNnat
    hA hW hbase hz hgeometryA hgeometryB hmodelMap
  have hdata B (hB : B∈Matrices) ab (_hab : ab∈Gaps) j (hj : j∈S B ab) :
      pick B ab j∈P ∧ Mat (pick B ab j)=B ∧ gap (pick B ab j)=ab ∧
        block (pick B ab j)=j ∧
        za (pick B ab j).1.1∈Icc (base+(N:ℝ)*j) (base+(N:ℝ)*((j:ℝ)+1)) := by
    obtain ⟨ij,hij,_he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    have hab' : ab∈P.image gap := Finset.mem_image.mpr ⟨ij,hh.1,hh.2.2⟩
    exact hpick B hB ab hab' j hj
  have hgapSub : P.image gap ⊆ Gaps := by
    intro ab hab
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hab
    exact hgapMem ij hij
  have hpairNat' : P.card ≤ 60*∑ B∈Matrices, ∑ ab∈Gaps, (S B ab).card := by
    apply hpairNat.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro B _hB
    exact Finset.sum_le_sum_of_subset_of_nonneg hgapSub (fun _ _ _ => Nat.zero_le _)
  have hpair : (P.card:ℝ) ≤ 60*(∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) := by
    exact_mod_cast hpairNat'
  have hmass :
      ((∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(Uband/lambda)^2*Uband^2*Gcap*
          (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
      (∑ B∈Matrices, ∑ ab∈Gaps, ((S B ab).card:ℝ)) ≤
        588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
          (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    exact physicalModelPhase_actual_fourier_charted_matrix_source_mass
      Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
      (fun B ab j => rat (pick B ab j))
      (fun B ab j => vinv (pick B ab j))
      (fun B ab j => parity (pick B ab j))
      (fun B ab j => anchor (pick B ab j)) e r v s
      (x:=fun B ab j => x (pick B ab j))
      hσ
      hδ
      hF
      hT
      hM
      hN
      hR
      hRM
      hQ
      hscale
      hmesh
      hA
      hW
      (by
        intro B hB ab hab j hj
        exact hx _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        change x (pick B ab j) 0∈_
        rw [hxa _ hp.1]
        exact hp.2.2.2.2)
      (by
        intro B hB ab hab j hj
        exact hden _ (hdata B hB ab hab j hj).1)
      hlambda
      hUband
      hθ
      hθmax
      (by
        intro B hB ab hab j hj
        exact hcurv _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hinv _ (hdata B hB ab hab j hj).1)
      hchart
      horientation
      hBcut
      hs
      hrefSet
      hparentSet
      hsep
      (by
        intro B hB ab hab j hj
        exact hwideL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hwideU _ (hdata B hB ab hab j hj).1)
      hUref
      hBselectSize
      hcutMargin
      hselectedWrap
      hreferenceDen
      hgapWidth
      hRQ
      hselectedUpper
      hscaleTen
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hfamilyGap _ hp.1
        rw [hp.2.2.1] at hh
        exact hh)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hc ij hij)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hlarge ij hij)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact haction ij hij)
      hV
      hgap
      (by
        intro B hB ab hab j hj
        exact hsourceColor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hlevel _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcolor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnear _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hnearNarrow _ (hdata B hB ab hab j hj).1)
      hsmall
      hNR
      hRN
      hNcube
      hminscale
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hMatdet ij hij)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hMatt _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      (by
        intro B hB ab hab j hj
        have hp := hdata B hB ab hab j hj
        have hh := hMatmap _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      (by
        intro B hB
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hB
        exact hMatgamma ij hij)
      hNtwo
      (by
        intro B hB ab hab j hj
        exact hL _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hU _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hanchor _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcut _ (hdata B hB ab hab j hj).1)
      (by
        intro B hB ab hab j hj
        exact hcount _ (hdata B hB ab hab j hj).1)
      hsize
      hD
      hΔ
      hBsize
      hBmajor
      hCmajor
  have hraw : (P.card:ℝ) ≤ 60*588*(Uband/lambda)^2*Uband^2*Gcap*
      (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
    simpa only [mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.1 (by norm_num : (0:ℝ) ≤ 60))
  have hnorm : (P.card:ℝ) ≤ Kmass*
      (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
    simpa only [Kmass,mul_assoc] using hpair.trans
      (mul_le_mul_of_nonneg_left hmass.2 (by norm_num : (0:ℝ) ≤ 60))
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hbalanced (hv : V=(Uref:ℝ)^((3:ℝ)/2)) :
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) :=
    huxley_narrowing_balanced_mass hUp hv hnorm
  refine ⟨hraw,hnorm,hbalanced,?_⟩
  intro hv hUlo
  have hκ := modelPhaseThirdLower_pos hσ
  have hBsel : 0 < Bselect := (by positivity : (0:ℝ) < 2+168/modelPhaseThirdLower σ).trans_le hBselectSize
  have hinvU := huxley_reference_reciprocal_scale hN
    (by exact_mod_cast hQ) hBsel hUlo
  have hVm : 0 ≤ V*(P.card:ℝ) :=
    mul_nonneg (zero_le_one.trans hV) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ Kmass*(Cmain+Ctail) :=
    (mul_nonneg hVm hUp.le).trans ((le_div_iff₀ hUp).mp (hbalanced hv))
  calc
    V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ) := hbalanced hv
    _ = Kmass*(Cmain+Ctail)*(1/(Uref:ℝ)) := by ring
    _ ≤ Kmass*(Cmain+Ctail)*(2*Bselect*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hinvU hcoef
    _ = _ := by ring


example
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ}
    (hbase : ∀ ij∈P, base ≤ za ij.1.1)
    (hxa : ∀ ij∈P, x ij 0=za ij.1.1)
    (hxb : ∀ ij∈P, x ij 1=zb ij.2.1)
    (hgapMem : ∀ ij∈P, gap ij∈Gaps)
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < (N:ℝ))
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hmesh : (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband)
    (hinv : ∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : (N:ℝ)^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2)
    (hc : ∀ ij∈P, Mat ij 2 ≠ 0)
    (hlarge : ∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
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
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
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
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*(N:ℝ)^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*(N:ℝ)^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/((N:ℝ)^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kmass := 60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
    ((P.card:ℝ) ≤
      60*588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (P.card:ℝ) ≤
      60*588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      V*(P.card:ℝ) ≤ Kmass*(Cmain+Ctail)/(Uref:ℝ)) ∧
    (V=(Uref:ℝ)^((3:ℝ)/2) →
      ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
      V*(P.card:ℝ) ≤ 2*Bselect*Kmass*(Cmain+Ctail)*
        ((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)) :=
  HuxleyOriginalPairMassScratch.physicalModelPhase_actual_fourier_original_pair_mass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Bmajor Cmajor Q K₀ N za zb AlenA AlenB Za Zb rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hbase hxa hxb hgapMem hgeometryA hgeometryB hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap


#print axioms huxley_narrowing_balanced_scale
#print axioms huxley_narrowing_balanced_mass
#print axioms huxley_reference_reciprocal_scale
#print axioms physicalModelPhase_actual_fourier_original_pair_mass
end HuxleyOriginalPairMassScratch
