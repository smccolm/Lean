import TaoTrudgianYang2025.HuxleyLinearForms

open Set Polynomial
open scoped ContDiff BigOperators FourierTransform Classical
namespace HuxleyLongFiberScratch
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

private theorem selected_family_long_tail
    {n a b m ell K q : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hell : 0 < ell) (hq : 0 < q)
    (hm : n ≤ a+b*m) (hlong : 2*a+2*b*ell ≤ n)
    (hcount : n ≤ a+K/(m^2*q)) :
    n ≤ 2*K/(ell^2*q) := by
  have hme : ell ≤ m := by nlinarith only [hm,hlong,ha,hb,hell]
  have hmp : 0 < m := hell.trans_le hme
  have hn : 2*a ≤ n := by nlinarith only [hlong,hb,hell]
  have hna : a < n := by nlinarith only [hlong,ha,hb,hell]
  have hquot : 0 < K/(m^2*q) := by linarith only [hna,hcount]
  have hK : 0 ≤ K := ((div_pos_iff_of_pos_right (by positivity : 0 < m^2*q)).mp hquot).le
  have hfirst : n ≤ 2*(K/(m^2*q)) := by linarith only [hn,hcount]
  have hden : ell^2*q ≤ m^2*q := by
    exact mul_le_mul_of_nonneg_right (sq_le_sq₀ hell.le hmp.le |>.mpr hme) hq.le
  calc
    n ≤ 2*(K/(m^2*q)) := hfirst
    _ ≤ 2*(K/(ell^2*q)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hK (mul_pos (sq_pos_of_pos hell) hq) hden) (by norm_num)
    _ = _ := by ring

private theorem selected_family_scaled_long_tail
    {n a b m ell K q scale : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hell : 0 < ell) (hq : 0 < q)
    (hscale : 0 < scale)
    (hm : n ≤ a+b*m) (hlong : 2*a+2*b*ell ≤ n)
    (hcount : n ≤ a+K/((scale*m)^2*q)) :
    n ≤ 2*K/((scale*ell)^2*q) := by
  have hcount' : n ≤ a+(K/scale^2)/(m^2*q) := by
    convert hcount using 1
    ring
  have hh := selected_family_long_tail ha hb hell hq hm hlong hcount'
  convert hh using 1
  field_simp

/-- The actual Fourier-family count consumes the constructed common
paired charts. The original matrix and source coordinates are unchanged;
the finite logarithmic chart loss is explicit in both mass and count. -/
theorem physicalModelPhase_actual_fourier_charted_reference_gap_count
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ Schart : Finset ℕ, Schart⊆S ∧ S.card ≤ 6+Ccharts*Schart.card ∧
    ∃ G : Finset ℕ, G⊆Schart ∧ Schart.card ≤ 6+G.card ∧
    ∃ jref : ℕ, jref∈G ∧
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
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
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      ((S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) ∧
      ∀ ell : ℝ, 0 < ell → 0 < |(Mat 2:ℝ)| →
        2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*ell ≤ (S.card:ℝ) →
        (S.card:ℝ) ≤ 34*(Ccharts:ℝ)*Ccount*R^4/
          ((κ/(16*(Blabels:ℝ)*Cphys)*ell)^2*N^2*|(Mat 2:ℝ)|)) := by
  classical
  intro Lref Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ ep rp
  have hcover := physicalModelPhase_same_color_reference_gap_paired_chart_cover
    S (fun j => x j 0) rat Q K₀ Mat e r v s
    hσ hδ (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
    hT hM hN (zero_lt_one.trans_le hR) hRN hQ (hA 0) (hW 0) hscale
    hmesh hMatgamma hchart horientation
    (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
    (fun j hj => by simpa only [mul_comm] using hwindow j hj)
    hlambda hUband hθ hθmax hcurv hden hfamilyGap hMatt
    (fun j hj => hlevel j hj 0) hsourceColor
  obtain ⟨G₀,hG₀S,hS6G₀,hcolors,hcharts⟩ := hcover.2
  let chartColor := fun j => ⌊Real.logb (5/4)
    (((r:ℝ)*(rat j 0:ℝ)-e)/(12*|(r:ℝ)| *ε))⌋₊
  let colors := G₀.image chartColor
  let fiber := fun n => G₀.filter (fun j => chartColor j=n)
  have hCap : 1 ≤ Ccharts := by dsimp only [Ccharts]; omega
  have hlargeS : 6+105 ≤ S.card := by
    apply le_trans _ hS
    nlinarith only [hCap]
  have hG₀ : G₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n,hn,hmax⟩ := colors.exists_max_image (fun n => (fiber n).card)
    (hG₀.image chartColor)
  let Schart := fiber n
  have hSchartG : Schart⊆G₀ := Finset.filter_subset _ _
  have hSchartS : Schart⊆S := hSchartG.trans hG₀S
  have hGmass : G₀.card ≤ Ccharts*Schart.card := by
    calc
      G₀.card = ∑ k∈colors,(fiber k).card :=
        Finset.card_eq_sum_card_fiberwise (fun j hj => Finset.mem_image_of_mem chartColor hj)
      _ ≤ ∑ _k∈colors,Schart.card := Finset.sum_le_sum hmax
      _ = colors.card*Schart.card := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      _ ≤ Ccharts*Schart.card := Nat.mul_le_mul_right _ hcolors
  have hSmass : S.card ≤ 6+Ccharts*Schart.card := by omega
  have hSchartLarge : 105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ Schart.card := by
    have hh : Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤
        Ccharts*Schart.card := Nat.le_of_add_le_add_left (hS.trans hSmass)
    nlinarith only [hh,hCap]
  obtain ⟨d,l,w,hd,hlw,hends,hregion,hchartLeft,hchartRight⟩ := hcharts n hn
  have hSchartEnds j (hj : j∈Schart) :
      ((v:ℝ)-s*((rat j 0:ℝ)+ε))/((r:ℝ)*((rat j 0:ℝ)+ε)-e)∈Icc l w ∧
      ((v:ℝ)-s*((rat j 0:ℝ)-ε))/((r:ℝ)*((rat j 0:ℝ)-ε)-e)∈Icc l w :=
    hends j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d :=
    (hregion l ⟨le_rfl,hlw⟩).1
  have hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d :=
    (hregion w ⟨hlw,le_rfl⟩).1
  have hconsumer := physicalModelPhase_actual_fourier_certified_reference_gap_count
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) Schart
    Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d)
    (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW
    (fun j hj => hx j (hSchartS hj))
    (fun j hj => hwindow j (hSchartS hj))
    (fun j hj => hden j (hSchartS hj))
    (fun j hj => hinv j (hSchartS hj))
    hchart horientation hd hBcut hs hrefSet hparentSet hsep hdenl hdenw
    (fun j hj => hwideL j (hSchartS hj))
    (fun j hj => hwideU j (hSchartS hj))
    hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
    hchartLeft hchartRight hRQ hselectedUpper hscaleTen
    (fun j hj => hfamilyGap j (hSchartS hj))
  obtain ⟨G,hGSchart,hSchart6G,jref,hjref,xref,hxr,hrest⟩ :=
    hconsumer hSchartLarge
      (fun j hj => hlevel j (hSchartS hj))
      (fun j hj => hcolor j (hSchartS hj))
      (fun j hj => hnear j (hSchartS hj))
      hsmall hNR hRN hNcube hminscale hMatdet
      (fun j hj => hMatt j (hSchartS hj))
      (fun j hj => hMatmap j (hSchartS hj)) hMatgamma
      hNtwo (fun j hj => hL j (hSchartS hj))
      (fun j hj => hU j (hSchartS hj))
      (fun j hj => hanchor j (hSchartS hj))
      (fun j hj => hcut j (hSchartS hj))
      (fun j hj => hcount j (hSchartS hj))
  refine ⟨Schart,hSchartS,hSmass,G,hGSchart,hSchart6G,jref,hjref,xref,hxr,?_⟩
  intro Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
  have hdenregion z (hz : z∈Icc l w) (i : Fin 2) :
      d ≤ (rp i:ℝ)*z+(![s,Mat 2*v+Mat 3*s] i:ℤ) ∧
        (rp i:ℝ)*z+(![s,Mat 2*v+Mat 3*s] i:ℤ) ≤ 2*d := by
    fin_cases i
    · exact (hregion z hz).1
    · change d ≤ ((Mat 2*e+Mat 3*r:ℤ):ℝ)*z+((Mat 2*v+Mat 3*s:ℤ):ℝ) ∧
        ((Mat 2*e+Mat 3*r:ℤ):ℝ)*z+((Mat 2*v+Mat 3*s:ℤ):ℝ) ≤ 2*d
      simpa only [Int.cast_add,Int.cast_mul] using (hregion z hz).2
  obtain ⟨S₀,hS₀Schart,hSchartMass,hbound⟩ :=
    hrest hsize hD hΔ hdenregion
      (fun j hj => hSchartEnds j (hGSchart hj)) hBsize
  refine ⟨S₀,hS₀Schart.trans hSchartS,?_,?_⟩
  · exact hSmass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hSchartMass) 6)
  · intro Blabels Γ L C Cfirst Csecond Ccount
    change |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (Schart.card:ℝ) ≤ 105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) at hbound
    rcases hbound with hentry | hcountSchart
    · exact Or.inl hentry
    · right
      have hm : (S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(Schart.card:ℝ) := by exact_mod_cast hSmass
      have hfull := hm.trans (add_le_add (le_refl 6)
        (mul_le_mul_of_nonneg_left hcountSchart (Nat.cast_nonneg Ccharts)))
      refine ⟨hfull,?_⟩
      intro ell hell hentry hlong
      let scale := κ/(16*(Blabels:ℝ)*Cphys)
      have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
      have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
      have hBlabels : (0:ℝ) < Blabels := by
        dsimp only [Blabels]
        positivity
      have hscalePos : 0 < scale := by dsimp only [scale]; positivity
      have hcharts : (0:ℝ) < Ccharts := by exact_mod_cast (show 0 < Ccharts by omega)
      have hmass : (S.card:ℝ) ≤ (6+105*(Ccharts:ℝ))+
          (17*(Ccharts:ℝ))*(S₀.card:ℝ) := by
        have hh : S.card ≤ 6+Ccharts*(105+17*S₀.card) :=
          hSmass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hSchartMass) 6)
        have hr : (S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(105+17*(S₀.card:ℝ)) := by exact_mod_cast hh
        nlinarith only [hr]
      have hcount' : (S.card:ℝ) ≤ (6+105*(Ccharts:ℝ))+
          (17*(Ccharts:ℝ)*Ccount*R^4)/
            ((scale*(S₀.card:ℝ))^2*(N^2*|(Mat 2:ℝ)|)) := by
        convert hfull using 1
        dsimp only [L,scale]
        ring
      have hlong' : 2*(6+105*(Ccharts:ℝ))+2*(17*(Ccharts:ℝ))*ell ≤ (S.card:ℝ) := by
        nlinarith only [hlong]
      have hh := selected_family_scaled_long_tail (by positivity : 0 ≤ 6+105*(Ccharts:ℝ))
        (by positivity : 0 < 17*(Ccharts:ℝ)) hell
        (by positivity : 0 < N^2*|(Mat 2:ℝ)|) hscalePos hmass hlong' hcount'
      convert hh using 1
      ring

example
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ Uband)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
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
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ Schart : Finset ℕ, Schart⊆S ∧ S.card ≤ 6+Ccharts*Schart.card ∧
    ∃ G : Finset ℕ, G⊆Schart ∧ Schart.card ≤ 6+G.card ∧
    ∃ jref : ℕ, jref∈G ∧
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
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
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+Ccharts*(105+17*S₀.card) ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      ((S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) ∧
      ∀ ell : ℝ, 0 < ell → 0 < |(Mat 2:ℝ)| →
        2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*ell ≤ (S.card:ℝ) →
        (S.card:ℝ) ≤ 34*(Ccharts:ℝ)*Ccount*R^4/
          ((κ/(16*(Blabels:ℝ)*Cphys)*ell)^2*N^2*|(Mat 2:ℝ)|)) :=
  HuxleyLongFiberScratch.physicalModelPhase_actual_fourier_charted_reference_gap_count Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap

/-- The already-proved weighted matrix enumeration also gives its pure
reciprocal-entry coefficient, without an artificial constant term. -/
private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_contra! hbad
  have hgap : 0 < Z-K := sub_pos.mpr hbad
  let W := (K*Gamma+1)/(Z-K)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hh := bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]

private theorem dyadic_rational_matrix_entry_bounds
    (Mat : Fin 4 → ℤ) (rat : Fin 2 → ℚ) (Q : ℕ) {Uband : ℝ}
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hcurv : ∀ i, |(rat i:ℝ)| ≤ Uband)
    (ht : (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den)
    (hmap : ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ)) :
    |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 ∧
      |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 := by
  have hq₀ : (0:ℝ) < (rat 0).den := by exact_mod_cast (rat 0).den_pos
  have hq₀Q : ((rat 0).den:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
  have hQq₀ : (Q:ℝ) ≤ 2*((rat 0).den:ℝ) := by exact_mod_cast (hden 0).2
  have hq₁Q : ((rat 1).den:ℝ) ≤ Q := by exact_mod_cast (hden 1).1
  have hQq₁ : (Q:ℝ) ≤ 2*((rat 1).den:ℝ) := by exact_mod_cast (hden 1).2
  have hlo : (1:ℝ)/2 ≤ ((rat 1).den:ℝ)/(rat 0).den := by
    apply (le_div_iff₀ hq₀).mpr
    linarith only [hq₀Q,hQq₁]
  have hhi : ((rat 1).den:ℝ)/(rat 0).den ≤ 2 := by
    apply (div_le_iff₀ hq₀).mpr
    linarith only [hq₁Q,hQq₀]
  exact bourgain_mobius_entry_bounds (by exact_mod_cast hdet)
    (x:=(rat 0:ℝ)) (y:=(rat 1:ℝ))
    (by simpa only [ht] using hlo) (by simpa only [ht] using hhi)
    hmap (hcurv 0) (hcurv 1)

private theorem matrix_family_sum_of_pointwise
    (Matrices : Finset (Fin 4 → ℤ)) (family : (Fin 4 → ℤ) → Finset ℕ)
    {Uband Gamma ShortCost Coeff : ℝ}
    (hUband : 0 ≤ Uband) (hGamma : 0 ≤ Gamma)
    (hShort : 0 ≤ ShortCost) (hCoeff : 0 ≤ Coeff)
    (hdet : ∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hcap : ∀ Mat∈Matrices, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hentries : ∀ Mat∈Matrices, (family Mat).Nonempty →
      |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 ∧
      |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2)
    (hfamily : ∀ Mat∈Matrices,
      ((family Mat).card:ℝ) ≤ ShortCost+Coeff/|(Mat 2:ℝ)|) :
    ∑ Mat∈Matrices,((family Mat).card:ℝ) ≤
      ((2*Gamma+1)*(2*Uband+5)^2)*(Gamma*ShortCost+Coeff) := by
  classical
  let Occupied := Matrices.filter (fun Mat => (family Mat).Nonempty)
  have hdetOcc Mat (hMat : Mat∈Occupied) := hdet Mat (Finset.mem_filter.mp hMat).1
  have hcOcc Mat (hMat : Mat∈Occupied) := hcap Mat (Finset.mem_filter.mp hMat).1
  have hentriesOcc Mat (hMat : Mat∈Occupied) :=
    hentries Mat (Finset.mem_filter.mp hMat).1 (Finset.mem_filter.mp hMat).2
  have hsum := resonance_matrix_reciprocal_sum Occupied hUband hGamma
    hdetOcc hcOcc (fun Mat hMat => (hentriesOcc Mat hMat).1)
    (fun Mat hMat => (hentriesOcc Mat hMat).2)
  have hcard : (Occupied.card:ℝ) ≤ (2*Gamma+1)*(2*Uband+5)^2*Gamma := by
    simpa only [zero_div,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one] using
      bourgain_resonance_matrix_weight_sum Occupied hUband hGamma
      (show (0:ℝ) ≤ 0 by norm_num) hdetOcc hcOcc
      (fun Mat hMat => (hentriesOcc Mat hMat).1)
      (fun Mat hMat => (hentriesOcc Mat hMat).2)
  have hsumOcc : (∑ Mat∈Matrices,((family Mat).card:ℝ))=
      ∑ Mat∈Occupied,((family Mat).card:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro Mat hMat hnot
    have hn : ¬(family Mat).Nonempty := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hMat,hh⟩)
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
  calc
    _ = ∑ Mat∈Occupied,((family Mat).card:ℝ) := hsumOcc
    _ ≤ ∑ Mat∈Occupied,(ShortCost+Coeff/|(Mat 2:ℝ)|) :=
      Finset.sum_le_sum (fun Mat hMat => hfamily Mat (Finset.mem_filter.mp hMat).1)
    _ = (Occupied.card:ℝ)*ShortCost+Coeff*(∑ Mat∈Occupied,1/|(Mat 2:ℝ)|) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
        div_eq_mul_inv,one_mul,Finset.mul_sum]
    _ ≤ ((2*Gamma+1)*(2*Uband+5)^2*Gamma)*ShortCost+
        Coeff*((2*Gamma+1)*(2*Uband+5)^2) :=
      add_le_add (mul_le_mul_of_nonneg_right hcard hShort)
        (mul_le_mul_of_nonneg_left hsum hCoeff)
    _ = _ := by ring

/-- The actual long Fourier families are summed over their nonzero
large-entry resonance matrices. Entry bounds come from observed Möbius
maps, and the existing arithmetic enumeration supplies the pure reciprocal
weight; no family-count or matrix-count certificate is assumed. -/
private theorem physicalModelPhase_actual_fourier_long_matrix_family_sum
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (family : (Fin 4 → ℤ) → Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℕ → Fin 2 → ℚ) (vinv : (Fin 4 → ℤ) → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℕ → Fin 2 → Fin 2) (anchor : (Fin 4 → ℤ) → ℕ → ℚ)
    (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ j∈family Mat, x Mat j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, (rat Mat j i).den ≤ Q ∧ Q ≤ 2*(rat Mat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, lambda ≤ |(rat Mat j i:ℝ)| ∧ |(rat Mat j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, ((rat Mat j i).den:ℤ) ∣ (rat Mat j i).num*vinv Mat j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ j∈family Mat, (rat Mat j 0:ℝ)∈Icc gapLo gapHi) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun Mat j i => (⌊((rat Mat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat Mat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ j∈family Mat, sourceColor Mat j 0=sourceColor Mat j 1) →
    (∀ Mat∈Matrices, 6+Ccharts*(105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1))) ≤ (family Mat).card) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, iteratedDeriv 2 (f i) (x Mat j i)/2=(rat Mat j i:ℝ)) →
    let q := fun Mat j i => (rat Mat j i).den
    let mu := fun Mat j i => iteratedDeriv 3 (f i) (round (x Mat j i))/6
    let ell := fun Mat j i => deriv (f i) (round (x Mat j i))
    let b := fun Mat j i => (⌊(q Mat j i:ℝ)*ell Mat j i⌋+(parity Mat j i:ℕ) : ℤ)
    let cround := fun Mat j i => round ((q Mat j i:ℝ)*ell Mat j i)
    let tau := fun Mat j i => ((b Mat j i:ℝ)-(q Mat j i:ℝ)*ell Mat j i)/2
    let dual := fun Mat j i => -2*mu Mat j i*(Real.sqrt (2/(3*mu Mat j i*(q Mat j i:ℝ))))^3
    let cloud := fun Mat j i => (![Int.fract (-(vinv Mat j i:ℝ)*b Mat j i/q Mat j i),
      Int.fract (-(vinv Mat j i:ℝ)/q Mat j i),dual Mat j i/Real.sqrt K₀,
      (3*dual Mat j i*tau Mat j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ j∈family Mat, b Mat j 0-cround Mat j 0=b Mat j 1-cround Mat j 1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ a, |cloud Mat j 0 a-cloud Mat j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, (Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3=(q Mat j 1:ℝ)/q Mat j 0) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ((Mat 0:ℝ)*(rat Mat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3)=(rat Mat j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, |(anchor Mat j:ℝ)-(rat Mat j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256*((anchor Mat j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor Mat j).den) →
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
    let Γ := Cphys/κ
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    ∀ length : ℝ, 0 < length →
    (∀ Mat∈Matrices, Mat 2 ≠ 0) →
    (∀ Mat∈Matrices, 2*Csecond*N*R^2/M < |(Mat 2:ℝ)|) →
    (∀ Mat∈Matrices, 2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*length ≤ ((family Mat).card:ℝ)) →
    let scale := κ/(16*(Blabels:ℝ)*Cphys)
    let Coeff := 34*(Ccharts:ℝ)*Ccount*R^4/((scale*length)^2*N^2)
    ∀ Gamma : ℝ, 0 ≤ Gamma →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ Gamma) →
    ∑ Mat∈Matrices,((family Mat).card:ℝ) ≤
      Coeff*((2*Gamma+1)*(2*Uband+5)^2) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor hS
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels Γ C Cfirst Csecond Ccount length hlength hnonzero hlarge hlong
    scale Coeff Gamma hGamma hcap
  have hfamily Mat (hMat : Mat∈Matrices) :
      ((family Mat).card:ℝ) ≤ Coeff/|(Mat 2:ℝ)| := by
    have hentry := physicalModelPhase_actual_fourier_charted_reference_gap_count
      Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) (family Mat)
      Q K₀ (rat Mat) (vinv Mat) (parity Mat) (anchor Mat) Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
      (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ)
      (F:=F) (A:=A) (W:=W) (x:=x Mat)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW
      (hx Mat hMat) (hwindow Mat hMat) (hden Mat hMat)
      hlambda hUband hθ hθmax (hcurv Mat hMat) (hinv Mat hMat)
      hchart horientation hBcut hs hrefSet hparentSet hsep
      (hwideL Mat hMat) (hwideU Mat hMat)
      hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
      hRQ hselectedUpper hscaleTen (hfamilyGap Mat hMat)
    obtain ⟨Schart,_,_,G,_,_,jref,_,xref,_,hrest⟩ :=
      hentry (hsourceColor Mat hMat) (hS Mat hMat) (hlevel Mat hMat)
        (hcolor Mat hMat) (hnear Mat hMat)
        hsmall hNR hRN hNcube hminscale (hMatdet Mat hMat)
        (hMatt Mat hMat) (hMatmap Mat hMat) (hMatgamma Mat hMat)
        hNtwo (hL Mat hMat) (hU Mat hMat) (hanchor Mat hMat)
        (hcut Mat hMat) (hcount Mat hMat)
    obtain ⟨S₀,_,_,hbranch⟩ := hrest hsize hD hΔ hBsize
    rcases hbranch with hsmallEntry | hbig
    · exact False.elim ((not_le_of_gt (hlarge Mat hMat)) hsmallEntry)
    · have hp : 0 < |(Mat 2:ℝ)| :=
        abs_pos.mpr (by exact_mod_cast hnonzero Mat hMat)
      have hh := hbig.2 length hlength hp (hlong Mat hMat)
      convert hh using 1
      dsimp only [Coeff,scale]
      ring
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans
    ((hF 0).2 0 (by norm_num) ⟨1,by norm_num [Expdb.phaseInterval]⟩)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hjet₂ := modelPhaseJetCoefficient_nonneg σ 2
  have hjet₃ := modelPhaseJetCoefficient_nonneg σ 3
  have hjet₄ := modelPhaseJetCoefficient_nonneg σ 4
  have hC₂ : 0 ≤ C₂ := add_nonneg hjet₂ hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg hjet₃ hδ0
  have hrecip : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hresidual : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hCoeff : 0 ≤ Coeff := by
    dsimp only [Coeff,Ccount,Cfirst,C,Γ,Kres,Ct,Cc,B,c,J,Cphys]
    positivity
  have hentries Mat (hMat : Mat∈Matrices) :
      |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 ∧
      |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 := by
    have hn : (family Mat).Nonempty := by
      apply Finset.card_pos.mp
      have hh := hS Mat hMat
      omega
    obtain ⟨j,hj⟩ := hn
    have hq₀ : (0:ℝ) < q Mat j 0 := by
      exact_mod_cast (rat Mat j 0).den_pos
    have hq₀Q : (q Mat j 0:ℝ) ≤ Q := by exact_mod_cast (hden Mat hMat j hj 0).1
    have hQq₀ : (Q:ℝ) ≤ 2*(q Mat j 0:ℝ) := by exact_mod_cast (hden Mat hMat j hj 0).2
    have hq₁Q : (q Mat j 1:ℝ) ≤ Q := by exact_mod_cast (hden Mat hMat j hj 1).1
    have hQq₁ : (Q:ℝ) ≤ 2*(q Mat j 1:ℝ) := by exact_mod_cast (hden Mat hMat j hj 1).2
    have hlo : (1:ℝ)/2 ≤ (q Mat j 1:ℝ)/q Mat j 0 := by
      apply (le_div_iff₀ hq₀).mpr
      linarith only [hq₀Q,hQq₁]
    have hhi : (q Mat j 1:ℝ)/q Mat j 0 ≤ 2 := by
      apply (div_le_iff₀ hq₀).mpr
      linarith only [hq₁Q,hQq₀]
    apply bourgain_mobius_entry_bounds
      (by exact_mod_cast hMatdet Mat hMat)
      (x:=(rat Mat j 0:ℝ)) (y:=(rat Mat j 1:ℝ))
      (by simpa only [hMatt Mat hMat j hj] using hlo)
      (by simpa only [hMatt Mat hMat j hj] using hhi)
      (hMatmap Mat hMat j hj)
      (hcurv Mat hMat j hj 0).2 (hcurv Mat hMat j hj 1).2
  have hsum := resonance_matrix_reciprocal_sum Matrices hUband hGamma
    hMatdet (fun Mat hMat => ⟨hnonzero Mat hMat,hcap Mat hMat⟩)
    (fun Mat hMat => (hentries Mat hMat).1)
    (fun Mat hMat => (hentries Mat hMat).2)
  calc
    _ ≤ ∑ Mat∈Matrices,Coeff/|(Mat 2:ℝ)| := Finset.sum_le_sum hfamily
    _ = Coeff*(∑ Mat∈Matrices,1/|(Mat 2:ℝ)|) := by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hCoeff

/-- The actual Fourier families are summed over their nonzero
large-entry resonance matrices, including ALL short families. Each long
family uses the constructed paired charts; short families retain their
explicit endpoint/threshold cost. Entry bounds are derived from observed
Möbius maps and the existing arithmetic matrix enumeration is reused. -/
theorem physicalModelPhase_actual_fourier_matrix_family_sum
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (family : (Fin 4 → ℤ) → Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℕ → Fin 2 → ℚ) (vinv : (Fin 4 → ℤ) → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℕ → Fin 2 → Fin 2) (anchor : (Fin 4 → ℤ) → ℕ → ℚ)
    (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ j∈family Mat, x Mat j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, (rat Mat j i).den ≤ Q ∧ Q ≤ 2*(rat Mat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, lambda ≤ |(rat Mat j i:ℝ)| ∧ |(rat Mat j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, ((rat Mat j i).den:ℤ) ∣ (rat Mat j i).num*vinv Mat j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ j∈family Mat, (rat Mat j 0:ℝ)∈Icc gapLo gapHi) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun Mat j i => (⌊((rat Mat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat Mat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ j∈family Mat, sourceColor Mat j 0=sourceColor Mat j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, iteratedDeriv 2 (f i) (x Mat j i)/2=(rat Mat j i:ℝ)) →
    let q := fun Mat j i => (rat Mat j i).den
    let mu := fun Mat j i => iteratedDeriv 3 (f i) (round (x Mat j i))/6
    let ell := fun Mat j i => deriv (f i) (round (x Mat j i))
    let b := fun Mat j i => (⌊(q Mat j i:ℝ)*ell Mat j i⌋+(parity Mat j i:ℕ) : ℤ)
    let cround := fun Mat j i => round ((q Mat j i:ℝ)*ell Mat j i)
    let tau := fun Mat j i => ((b Mat j i:ℝ)-(q Mat j i:ℝ)*ell Mat j i)/2
    let dual := fun Mat j i => -2*mu Mat j i*(Real.sqrt (2/(3*mu Mat j i*(q Mat j i:ℝ))))^3
    let cloud := fun Mat j i => (![Int.fract (-(vinv Mat j i:ℝ)*b Mat j i/q Mat j i),
      Int.fract (-(vinv Mat j i:ℝ)/q Mat j i),dual Mat j i/Real.sqrt K₀,
      (3*dual Mat j i*tau Mat j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ j∈family Mat, b Mat j 0-cround Mat j 0=b Mat j 1-cround Mat j 1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ a, |cloud Mat j 0 a-cloud Mat j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, (Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3=(q Mat j 1:ℝ)/q Mat j 0) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ((Mat 0:ℝ)*(rat Mat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3)=(rat Mat j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, |(anchor Mat j:ℝ)-(rat Mat j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256*((anchor Mat j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor Mat j).den) →
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
    let Γ := Cphys/κ
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    ∀ length : ℝ, 0 < length →
    (∀ Mat∈Matrices, Mat 2 ≠ 0) →
    (∀ Mat∈Matrices, 2*Csecond*N*R^2/M < |(Mat 2:ℝ)|) →
    let scale := κ/(16*(Blabels:ℝ)*Cphys)
    let Coeff := 34*(Ccharts:ℝ)*Ccount*R^4/((scale*length)^2*N^2)
    ∀ Gamma : ℝ, 0 ≤ Gamma →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ Gamma) →
    let ShortCost := max ((6+Ccharts*(105+544*Blabels):ℕ):ℝ)
      (2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*length)
    ∑ Mat∈Matrices,((family Mat).card:ℝ) ≤
      ((2*Gamma+1)*(2*Uband+5)^2)*(Gamma*ShortCost+Coeff) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels Γ C Cfirst Csecond Ccount length hlength hnonzero hlarge
    scale Coeff Gamma hGamma hcap ShortCost
  let Long := Matrices.filter (fun Mat => ShortCost ≤ ((family Mat).card:ℝ))
  let Short := Matrices.filter (fun Mat => ¬ShortCost ≤ ((family Mat).card:ℝ))
  have hLongSub : Long⊆Matrices := Finset.filter_subset _ _
  have hShortSub : Short⊆Matrices := Finset.filter_subset _ _
  have hsourceSize Mat (hMat : Mat∈Long) :
      6+Ccharts*(105+544*Blabels) ≤ (family Mat).card := by
    have hh := (le_max_left _ _).trans (Finset.mem_filter.mp hMat).2
    exact_mod_cast hh
  have hlongSize Mat (hMat : Mat∈Long) :
      2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*length ≤ ((family Mat).card:ℝ) :=
    (le_max_right _ _).trans (Finset.mem_filter.mp hMat).2
  have hlongSum := physicalModelPhase_actual_fourier_long_matrix_family_sum
    Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) Long family
    Q K₀ rat vinv parity anchor e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
    (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ)
    (F:=F) (A:=A) (W:=W) (x:=x)
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW
    (fun Mat hMat => hx Mat (hLongSub hMat))
    (fun Mat hMat => hwindow Mat (hLongSub hMat))
    (fun Mat hMat => hden Mat (hLongSub hMat))
    hlambda hUband hθ hθmax
    (fun Mat hMat => hcurv Mat (hLongSub hMat))
    (fun Mat hMat => hinv Mat (hLongSub hMat))
    hchart horientation hBcut hs hrefSet hparentSet hsep
    (fun Mat hMat => hwideL Mat (hLongSub hMat))
    (fun Mat hMat => hwideU Mat (hLongSub hMat))
    hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
    hRQ hselectedUpper hscaleTen
    (fun Mat hMat => hfamilyGap Mat (hLongSub hMat))
    (fun Mat hMat => hsourceColor Mat (hLongSub hMat))
    hsourceSize
    (fun Mat hMat => hlevel Mat (hLongSub hMat))
    (fun Mat hMat => hcolor Mat (hLongSub hMat))
    (fun Mat hMat => hnear Mat (hLongSub hMat))
    hsmall hNR hRN hNcube hminscale
    (fun Mat hMat => hMatdet Mat (hLongSub hMat))
    (fun Mat hMat => hMatt Mat (hLongSub hMat))
    (fun Mat hMat => hMatmap Mat (hLongSub hMat))
    (fun Mat hMat => hMatgamma Mat (hLongSub hMat))
    hNtwo (fun Mat hMat => hL Mat (hLongSub hMat))
    (fun Mat hMat => hU Mat (hLongSub hMat))
    (fun Mat hMat => hanchor Mat (hLongSub hMat))
    (fun Mat hMat => hcut Mat (hLongSub hMat))
    (fun Mat hMat => hcount Mat (hLongSub hMat))
    hsize hD hΔ hBsize length hlength
    (fun Mat hMat => hnonzero Mat (hLongSub hMat))
    (fun Mat hMat => hlarge Mat (hLongSub hMat))
    hlongSize Gamma hGamma (fun Mat hMat => hcap Mat (hLongSub hMat))
  have hShort : 0 ≤ ShortCost := (Nat.cast_nonneg _).trans (le_max_left _ _)
  have hentries Mat (hMat : Mat∈Short) (hn : (family Mat).Nonempty) :
      |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 ∧
      |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Uband+2 := by
    obtain ⟨j,hj⟩ := hn
    exact dyadic_rational_matrix_entry_bounds Mat (rat Mat j) Q
      (hMatdet Mat (hShortSub hMat)) (hden Mat (hShortSub hMat) j hj)
      (fun i => (hcurv Mat (hShortSub hMat) j hj i).2)
      (hMatt Mat (hShortSub hMat) j hj) (hMatmap Mat (hShortSub hMat) j hj)
  have hshortSum := matrix_family_sum_of_pointwise Short family hUband hGamma hShort
    (show (0:ℝ) ≤ 0 by norm_num)
    (fun Mat hMat => hMatdet Mat (hShortSub hMat))
    (fun Mat hMat => ⟨hnonzero Mat (hShortSub hMat),hcap Mat (hShortSub hMat)⟩)
    hentries (fun Mat hMat => by
      simpa only [zero_div,add_zero] using le_of_not_ge (Finset.mem_filter.mp hMat).2)
  have heq : (∑ Mat∈Matrices,((family Mat).card:ℝ))=
      (∑ Mat∈Long,((family Mat).card:ℝ))+(∑ Mat∈Short,((family Mat).card:ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not Matrices
      (fun Mat => ShortCost ≤ ((family Mat).card:ℝ)) (fun Mat => ((family Mat).card:ℝ))).symm
  rw [heq]
  calc
    _ ≤ Coeff*((2*Gamma+1)*(2*Uband+5)^2)+
        ((2*Gamma+1)*(2*Uband+5)^2)*(Gamma*ShortCost+0) := add_le_add hlongSum hshortSum
    _ = _ := by ring

example
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (family : (Fin 4 → ℤ) → Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℕ → Fin 2 → ℚ) (vinv : (Fin 4 → ℤ) → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℕ → Fin 2 → Fin 2) (anchor : (Fin 4 → ℤ) → ℕ → ℚ)
    (e r v s : ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ j∈family Mat, x Mat j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, (rat Mat j i).den ≤ Q ∧ Q ≤ 2*(rat Mat j i).den)
    (hlambda : 0 < lambda) (hUband : 0 ≤ Uband)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, lambda ≤ |(rat Mat j i:ℝ)| ∧ |(rat Mat j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, ((rat Mat j i).den:ℤ) ∣ (rat Mat j i).num*vinv Mat j i-1)
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ j∈family Mat, (rat Mat j 0:ℝ)∈Icc gapLo gapHi) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := ⌊Real.logb (5/4) ((gapHi-gapLo)/(12*ε))⌋₊+1
    let sourceColor := fun Mat j i => (⌊((rat Mat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat Mat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ j∈family Mat, sourceColor Mat j 0=sourceColor Mat j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, iteratedDeriv 2 (f i) (x Mat j i)/2=(rat Mat j i:ℝ)) →
    let q := fun Mat j i => (rat Mat j i).den
    let mu := fun Mat j i => iteratedDeriv 3 (f i) (round (x Mat j i))/6
    let ell := fun Mat j i => deriv (f i) (round (x Mat j i))
    let b := fun Mat j i => (⌊(q Mat j i:ℝ)*ell Mat j i⌋+(parity Mat j i:ℕ) : ℤ)
    let cround := fun Mat j i => round ((q Mat j i:ℝ)*ell Mat j i)
    let tau := fun Mat j i => ((b Mat j i:ℝ)-(q Mat j i:ℝ)*ell Mat j i)/2
    let dual := fun Mat j i => -2*mu Mat j i*(Real.sqrt (2/(3*mu Mat j i*(q Mat j i:ℝ))))^3
    let cloud := fun Mat j i => (![Int.fract (-(vinv Mat j i:ℝ)*b Mat j i/q Mat j i),
      Int.fract (-(vinv Mat j i:ℝ)/q Mat j i),dual Mat j i/Real.sqrt K₀,
      (3*dual Mat j i*tau Mat j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ j∈family Mat, b Mat j 0-cround Mat j 0=b Mat j 1-cround Mat j 1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ a, |cloud Mat j 0 a-cloud Mat j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, (Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3=(q Mat j 1:ℝ)/q Mat j 0) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ((Mat 0:ℝ)*(rat Mat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat Mat j 0:ℝ)+Mat 3)=(rat Mat j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, ∀ i, x Mat j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, |(anchor Mat j:ℝ)-(rat Mat j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256*((anchor Mat j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ j∈family Mat, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor Mat j).den) →
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
    let Γ := Cphys/κ
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    ∀ length : ℝ, 0 < length →
    (∀ Mat∈Matrices, Mat 2 ≠ 0) →
    (∀ Mat∈Matrices, 2*Csecond*N*R^2/M < |(Mat 2:ℝ)|) →
    let scale := κ/(16*(Blabels:ℝ)*Cphys)
    let Coeff := 34*(Ccharts:ℝ)*Ccount*R^4/((scale*length)^2*N^2)
    ∀ Gamma : ℝ, 0 ≤ Gamma →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ Gamma) →
    let ShortCost := max ((6+Ccharts*(105+544*Blabels):ℕ):ℝ)
      (2*(6+105*(Ccharts:ℝ))+34*(Ccharts:ℝ)*length)
    ∑ Mat∈Matrices,((family Mat).card:ℝ) ≤
      ((2*Gamma+1)*(2*Uband+5)^2)*(Gamma*ShortCost+Coeff) :=
  HuxleyLongFiberScratch.physicalModelPhase_actual_fourier_matrix_family_sum Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) Matrices family Q K₀ rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap

#print axioms physicalModelPhase_actual_fourier_matrix_family_sum
#print axioms physicalModelPhase_actual_fourier_long_matrix_family_sum
#print axioms matrix_family_sum_of_pointwise
#print axioms dyadic_rational_matrix_entry_bounds
#print axioms resonance_matrix_reciprocal_sum
#print axioms physicalModelPhase_actual_fourier_charted_reference_gap_count
#print axioms selected_family_long_tail
#print axioms selected_family_scaled_long_tail
end HuxleyLongFiberScratch
