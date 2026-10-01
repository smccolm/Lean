import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyGlobalLargeEntrySourceScratch

private theorem eventually_positive_difference_global_large_entry_source_mass
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (σsrc η Tsrc ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
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
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
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
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
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
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    V*(P.card:ℝ) ≤
      (2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss := by
  filter_upwards [eventually_physicalModelPhase_actual_fourier_original_pair_mass hσ hJref hεloss]
    with T hmass
  intro Fsrc σsrc η Tsrc ya yb Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V A W x xlocal yp F
    hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird Cpack Cfirst Cgap Cmain Ctail hvchoice hUlo
  let flocal := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  have hsource i : flocal i = fun w => f i ((A i:ℝ)+w) := by
    funext w
    dsimp only [flocal,heathBrownPhysicalPhase,F,f]
    field_simp
  have hjet ij i k : iteratedDeriv k (flocal i) (xlocal ij i) =
      iteratedDeriv k (f i) (x ij i) := by
    rw [hsource,iteratedDeriv_comp_const_add]
    simp only [xlocal,add_sub_cancel]
  have hrjet ij i k : iteratedDeriv k (flocal i) (round (xlocal ij i)) =
      iteratedDeriv k (f i) (round (x ij i)) := by
    rw [hsource,iteratedDeriv_comp_const_add]
    simp only [xlocal,round_sub_intCast,Int.cast_sub,add_sub_cancel]
  have hrderiv ij i : deriv (flocal i) (round (xlocal ij i)) =
      deriv (f i) (round (x ij i)) := by
    simpa only [iteratedDeriv_one] using hrjet ij i 1
  let mulocal := fun ij i => iteratedDeriv 3 (flocal i) (round (xlocal ij i))/6
  let elllocal := fun ij i => deriv (flocal i) (round (xlocal ij i))
  let blocal := fun ij i => (⌊(q ij i:ℝ)*elllocal ij i⌋+(parity ij i:ℕ) : ℤ)
  let taulocal := fun ij i => ((blocal ij i:ℝ)-(q ij i:ℝ)*elllocal ij i)/2
  let duallocal := fun ij i => -2*mulocal ij i*(Real.sqrt (2/(3*mulocal ij i*(q ij i:ℝ))))^3
  let cloudlocal := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*blocal ij i/q ij i),
    Int.fract (-(vinv ij i:ℝ)/q ij i),duallocal ij i/Real.sqrt K₀,
    (3*duallocal ij i*taulocal ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
  have hcloud ij i : cloudlocal ij i=cloud ij i := by
    dsimp only [cloudlocal,duallocal,mulocal,taulocal,blocal,elllocal]
    simp only [hrjet,hrderiv]
    rfl
  have hgeomA ij (hij : ij∈P) :
      N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
        round (za ij.1.1-(A 0:ℝ))+(AlenA ij.1.1:ℤ)=
          (Za-A 0)+(N:ℤ)*ij.1.1+2*(N:ℤ) := by
    obtain ⟨hlo,hhi,he⟩ := hgeometryA ij hij
    refine ⟨hlo,hhi,?_⟩
    rw [round_sub_intCast]
    omega
  have hgeomB ij (hij : ij∈P) :
      N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
        round (zb ij.2.1-(A 1:ℝ))+(AlenB ij.2.1:ℤ)=
          (Zb-A 1)+(N:ℤ)*ij.2.1+2*(N:ℤ) := by
    obtain ⟨hlo,hhi,he⟩ := hgeometryB ij hij
    refine ⟨hlo,hhi,?_⟩
    rw [round_sub_intCast]
    omega
  apply hmass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Q K₀ N
    (fun n => za n-(A 0:ℝ)) (fun n => zb n-(A 1:ℝ))
    AlenA AlenB (Za-A 0) (Zb-A 1) rat vinv parity anchor e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F)
    (A:=fun i => (A i:ℝ)) (W:=W) (x:=xlocal)
    hbase (by intro ij _; rfl) (by intro ij _; rfl) hgapMem hgeomA hgeomB
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight hsourceColor
    (by intro ij hij i; rw [show iteratedDeriv 2 (heathBrownPhysicalPhase (F i) T M (A i) 1)
      (xlocal ij i)=iteratedDeriv 2 (f i) (x ij i) from hjet ij i 2]; exact hlevel ij hij i)
    (by
      intro ij hij
      change (⌊(q ij 0:ℝ)*deriv (flocal 0) (round (xlocal ij 0))⌋+(parity ij 0:ℕ):ℤ)-
          round ((q ij 0:ℝ)*deriv (flocal 0) (round (xlocal ij 0))) =
        (⌊(q ij 1:ℝ)*deriv (flocal 1) (round (xlocal ij 1))⌋+(parity ij 1:ℕ):ℤ)-
          round ((q ij 1:ℝ)*deriv (flocal 1) (round (xlocal ij 1)))
      rw [hrderiv,hrderiv]
      exact hcolor ij hij)
    (by
      intro ij hij d
      change |cloudlocal ij 0 d-cloudlocal ij 1 d| ≤ 2*radius d
      rw [hcloud,hcloud]
      exact hnear ij hij d)
    (by
      intro ij hij
      change |cloudlocal ij 0 1-cloudlocal ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)
      rw [hcloud,hcloud]
      exact hnearNarrow ij hij)
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hvchoice hUlo


example
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (σsrc η Tsrc ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
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
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
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
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
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
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    V=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    V*(P.card:ℝ) ≤
      (2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3))*T^εloss :=
  HuxleyGlobalLargeEntrySourceScratch.eventually_positive_difference_global_large_entry_source_mass (σ:=σ) (Jref:=Jref) (εloss:=εloss) hσ hJref hεloss


#print axioms eventually_positive_difference_global_large_entry_source_mass

end HuxleyGlobalLargeEntrySourceScratch
