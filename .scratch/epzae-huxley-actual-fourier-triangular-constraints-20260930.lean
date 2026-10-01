import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyActualTriangularScratch

private theorem charted_selected_blocks
    {b B c C n nSource nSelected : ℕ}
    (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    32*b*n ≤ nSelected := by
  have hbudget : 6+c*(105+544*b) ≤ 6+C*(105+544*B) := by gcongr
  have hlower := (Nat.mul_le_mul_right n hbudget).trans hblocks
  have hoffset : 6+105*c ≤ (6+105*c)*n := Nat.le_mul_of_pos_right _ hn
  have hmul : c*(17*(32*b*n)) ≤ c*(17*nSelected) := by
    nlinarith only [hlower,hselection,hoffset]
  have hh := Nat.le_of_mul_le_mul_left hmul hc
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (17:ℕ))

/-- The chart and height-label budgets cancel from the physical unit
length. They remain in the original-family block size, not in Lunit. -/
private theorem charted_selected_source_length
    {b B c C n nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  have hmass : (32:ℝ)*(b:ℝ)*(n:ℝ) ≤ (nSelected:ℝ) := by
    exact_mod_cast charted_selected_blocks hc hbB hcC hn hselection hblocks
  have hbreal : (0:ℝ) < b := Nat.cast_pos.mpr hb
  calc
    _ = κ/(16*(b:ℝ)*Cphys)*((32:ℝ)*(b:ℝ)*(n:ℝ)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)


/-- The actual charted Fourier selector feeds both triangular quartic
constraints. The original family-to-selected-samples loss is retained.
Source chart membership is required only for the original finite family,
not for subsequently selected continuum roots or Third witnesses. -/
theorem positive_difference_actual_fourier_charted_triangular_constraints
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ j∈S, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband) →
    (∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1) →
    (v*r-e*s=1) →
    (((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi)) →
    (0 < Bcut) →
    (s ≠ 0) →
    ((e:ℝ)/r∈Refs) →
    ((v:ℝ)/s∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (R^2 ≤ (r:ℝ)^2*(Uref:ℝ)) →
    (gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, sourceColor j 0=sourceColor j 1) →
    6+Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 →
    61*Ccurv*Cphys ≤ Bcut →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Cthird := ((σ*(σ+1)+1)/κ)*(32*Kres+9*quarticReciprocalConstant σ δ)
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    0 < L ∧
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *L^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *L^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) ∧
    ∀ Bmajor Cmajor n : ℕ, Blabels ≤ Bmajor → Ccharts ≤ Cmajor → 0 < n →
      (6+Cmajor*(105+544*Bmajor))*n ≤ S.card →
      let Lblock := (2*κ/Cphys)*(n:ℝ)
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *Lblock^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *Lblock^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) := by
  classical
  obtain ⟨aU,CU,haU,hCU,hupper⟩ :=
    positive_difference_normalized_quartic_upper_long_block_constraint hσsrc hcsrc hUsrc
  obtain ⟨η₀,aL,CL,hη₀,hηcap,haL,hCL,hlower⟩ :=
    positive_difference_normalized_quartic_lower_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨η₀,min aU aL,CU,CL,hη₀,hηcap,lt_min haU haL,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Bselect gapLo gapHi S Q K₀ inst
    rat vinv parity anchor Mat e r v s σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize Blabels Cthird
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hselected := physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S
    Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=fun i => (A i:ℝ)) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hsourceColor hS hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
  obtain ⟨_Schart,_hSchart,_hSchartMass,_G,_hG,_hGMass,_jref,_hjref,xref,hxr,hrest⟩ := hselected
  obtain ⟨d,l,w,hd,S₀,hS₀,hSmass,_hinside,j,z,curve,alpha,beta,
    hpairs,hmono,hLpos,hspan,hK,hcurve,hgap,hres⟩ := hrest hsize hD hΔ hBsize
  let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
  let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
  let Ep : Fin 2 → ℝ := fun i => ep i
  let Rp : Fin 2 → ℝ := fun i => rp i
  let Vp : Fin 2 → ℝ := fun i => vp i
  let Sp : Fin 2 → ℝ := fun i => sp i
  have hrp i : Rp i ≠ 0 := by
    have hh := (hxr i).1
    change 0 < rp i*r at hh
    intro hz
    change (rp i:ℝ)=0 at hz
    have hz' : rp i=0 := by exact_mod_cast hz
    rw [hz',zero_mul] at hh
    exact (lt_irrefl 0) hh
  have hdet i : Vp i*Rp i-Ep i*Sp i=1 := by
    have hd₀ : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
    have hd₁ : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hMatdet
    fin_cases i
    · exact hd₀
    · change ((Mat 0*v+Mat 1*s:ℤ):ℝ)*((Mat 2*e+Mat 3*r:ℤ):ℝ)-
        ((Mat 0*e+Mat 1*r:ℤ):ℝ)*((Mat 2*v+Mat 3*s:ℤ):ℝ)=1
      push_cast
      linear_combination ((v:ℝ)*r-e*s)*hd₁+hd₀
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have hbase i : iteratedDeriv 2 (f i) (xref i)/2=Ep i/Rp i := (hxr i).2.2.1
  have hxcurve t (ht : t∈Icc (z 0) (z 7)) i :
      curve t i∈Ioo (1/2:ℝ) (W i-1/2) := ((hcurve t ht).2 i).1
  have hdenL t (ht : t∈Icc (z 0) (z 7)) i : d ≤ Rp i*t+Sp i :=
    ((hcurve t ht).2 i).2.1
  have hdenU t (ht : t∈Icc (z 0) (z 7)) i : Rp i*t+Sp i ≤ 2*d :=
    ((hcurve t ht).2 i).2.2.1
  have hpoint t (ht : t∈Icc (z 0) (z 7)) i :
      iteratedDeriv 2 (f i) (curve t i)/2=(Ep i*t+Vp i)/(Rp i*t+Sp i) :=
    ((hcurve t ht).2 i).2.2.2.1
  have hsquare t (ht : t∈Icc (z 0) (z 7)) i :
      |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R :=
    ((hcurve t ht).2 i).2.2.2.2
  have hendlevel k i : iteratedDeriv 2 (f i) (curve (z k) i)/2=(rat (j k) i:ℝ) := by
    have hzk : z k∈Icc (z 0) (z 7) := ⟨hmono.monotone (by omega),hmono.monotone (by omega)⟩
    exact (hpoint _ hzk i).trans ((hpairs k).2 i).symm
  let Lsource := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
  have hupperBound : (Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *Lsource^3*N^4 ≤ 2*CU*(Cthird+1)*E^2*M^2 := by
    intro htri
    have htransport : Ep 1=Ep 0+(Mat 1:ℝ)*Rp 0 ∧
        Vp 1=Vp 0+(Mat 1:ℝ)*Sp 0 ∧ Rp 1=Rp 0 ∧ Sp 1=Sp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2]
    apply hupper Fsrc η xcenter ycenter ya yb (Mat 1) Tsrc E z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηmax hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hsourceScale hbase hpoint hsquare hgap hres
    intro t ht i
    rcases Finset.mem_insert.mp ht with he | he
    · subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).1).trans_le (min_le_left _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)):ℝ × ℝ)-center‖ < aU
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).1).trans_le (min_le_left _ _)
  have hlowerBound : (Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *Lsource^3*N^2 ≤ 8*CL*(Cthird+1)*R^4 := by
    intro htri
    have htransport : Ep 1=Ep 0 ∧ Vp 1=Vp 0 ∧
        Rp 1=Rp 0+(Mat 2:ℝ)*Ep 0 ∧ Sp 1=Sp 0+(Mat 2:ℝ)*Vp 0 := by
      simp [Ep,Rp,Vp,Sp,ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2,add_comm]
    apply hlower Fsrc η xcenter ycenter ya yb (Mat 2) Tsrc z A
      hσ hδ hF hT hM hN hR hLpos hspan hd hK hA hW hxref hxcurve hrp hdet
      hdenL hdenU hmono hscale htransport hη hηsmall hcenterx hcentery hya hyb
      hreg hjets htests hTsrc hMtwo hbase hpoint hsquare hgap hres
    intro t ht i
    rcases Finset.mem_insert.mp ht with he | he
    · subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 0) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 0).1) i).2).trans_le (min_le_right _ _)
    · have he' : t=z 7 := Finset.mem_singleton.mp he
      subst t
      change ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve (z 7) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL
      rw [hendlevel]
      exact ((hlocal _ (hS₀ (hpairs 7).1) i).2).trans_le (min_le_right _ _)
  refine ⟨S₀,hS₀,hSmass,hLpos,hupperBound,hlowerBound,?_⟩
  intro Bmajor Cmajor n hBmajor hCmajor hn hblocks Lblock
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hlength : Lblock ≤ Lsource :=
    charted_selected_source_length (by dsimp only [Blabels]; omega)
      (by dsimp only [Ccharts]; omega) hBmajor hCmajor hn hκ hCphys hSmass hblocks
  have hLblock : 0 ≤ Lblock := by dsimp only [Lblock]; positivity
  have hpower := pow_le_pow_left₀ hLblock hlength 3
  constructor
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (by positivity : 0 ≤ N^4)).trans (hupperBound htri)
  · intro htri
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hκ.le (abs_nonneg _)))
      (sq_nonneg N)).trans (hlowerBound htri)

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ j∈S, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband) →
    (∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1) →
    (v*r-e*s=1) →
    (((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi)) →
    (0 < Bcut) →
    (s ≠ 0) →
    ((e:ℝ)/r∈Refs) →
    ((v:ℝ)/s∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (R^2 ≤ (r:ℝ)^2*(Uref:ℝ)) →
    (gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, sourceColor j 0=sourceColor j 1) →
    6+Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 →
    61*Ccurv*Cphys ≤ Bcut →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Cthird := ((σ*(σ+1)+1)/κ)*(32*Kres+9*quarticReciprocalConstant σ δ)
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    0 < L ∧
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
      κ*|(Mat 1:ℝ)| *L^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
      κ*|(Mat 2:ℝ)| *L^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) ∧
    ∀ Bmajor Cmajor n : ℕ, Blabels ≤ Bmajor → Ccharts ≤ Cmajor → 0 < n →
      (6+Cmajor*(105+544*Bmajor))*n ≤ S.card →
      let Lblock := (2*κ/Cphys)*(n:ℝ)
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *Lblock^3*N^4 ≤ 2*Cupper*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *Lblock^3*N^2 ≤ 8*Clower*(Cthird+1)*R^4) :=
  HuxleyActualTriangularScratch.positive_difference_actual_fourier_charted_triangular_constraints (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


end HuxleyActualTriangularScratch
#print axioms HuxleyActualTriangularScratch.positive_difference_actual_fourier_charted_triangular_constraints
#print axioms HuxleyActualTriangularScratch.charted_selected_source_length
#print axioms HuxleyActualTriangularScratch.charted_selected_blocks
