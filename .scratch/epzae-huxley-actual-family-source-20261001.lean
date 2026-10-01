import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyActualFamilySourceScratch

private theorem actual_phase_pair_forget_card
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ya yb : ℝ) :
    let Fiber := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
    (Fiber.image forget).card=Fiber.card ∧
      ∀ ij, ij∈Fiber.image forget ↔ embed ij∈P := by
  classical
  intro Fiber forget embed
  have hback ij (hij : ij∈Fiber) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,ip⟩,⟨⟨b,m⟩,jp⟩⟩
    have he := (Finset.mem_filter.mp hij).2
    dsimp only at he
    rcases he with ⟨rfl,rfl⟩
    rfl
  constructor
  · apply Finset.card_image_of_injOn
    intro ij hij kl hkl he
    exact (hback ij hij).symm.trans ((congrArg embed he).trans (hback kl hkl))
  · intro ij
    constructor
    · intro hij
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hij
      rw [hback kl hkl]
      exact (Finset.mem_filter.mp hkl).1
    · intro hij
      exact Finset.mem_image.mpr ⟨embed ij,Finset.mem_filter.mpr ⟨hij,by constructor <;> rfl⟩,rfl⟩


/-- ONE actual fixed-phase-pair matrix family is split into its literal
upper, lower and large-entry subsets. The existing analytic bounds are composed
with derived source curvature and canonical translation reindexing; no
injectivity of the original matrix family or pair-count certificate is assumed.
The displayed source/reference geometry remains an upstream obligation. -/
private theorem eventually_positive_difference_tagged_non_type_one_pair_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (gap : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℚ) (vinv : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℤ)
    (parity : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → Fin 2) (anchor : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut Vscale : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) => (![za ij.1.1.2,zb ij.2.1.2] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, ij.1.1.1=ya ∧ ij.2.1.1=yb) →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, base ≤ za ij.1.1.2-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1.2 ∧ AlenA ij.1.1.2 ≤ 3*N ∧
      round (za ij.1.1.2)+(AlenA ij.1.1.2:ℤ)=Za+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1.2 ∧ AlenB ij.2.1.2 ≤ 3*N ∧
      round (zb ij.2.1.2)+(AlenB ij.2.1.2:ℤ)=Zb+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey) →
    (1 ≤ Vscale) →
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
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*Vscale)) →
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
    (∀ ij∈P,
      (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0) ∨
      (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0) ∨
      (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| *κ^2*T)) →
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
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    Vscale*(P.card:ℝ) ≤ (Vscale*(Kupper+Klower)+Klarge)*T^εloss := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hcountFn⟩ :=
    eventually_positive_difference_global_non_type_one_pair_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro σ Jref εloss E θ hσ hJref hεloss
  filter_upwards [hcountFn (E:=E) (θ:=θ) hσ hJref hεloss] with T hboundFn
  intro Fsrc η ya yb Tsrc chartKey Uref Refs Gaps Bselect P Mat gap
    N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    δ M R base Bcut Vscale A W x xlocal
    hphase hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hbase hgapMem hgeometryA hgeometryB hregime
    lambda Uband yp F chartColor hchartColor
    hVscale hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hcases H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Cpack Cfirst Cgap Cmain Ctail Kupper Klower Klarge hvchoice hUlo

  let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
  let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
  let Pbar := P.image forget
  have hfilter : P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)=P :=
    Finset.filter_eq_self.mpr hphase
  have hdata := actual_phase_pair_forget_card P ya yb
  dsimp only at hdata
  rw [hfilter] at hdata
  have hcard : Pbar.card=P.card := hdata.1
  have hmem ij (hij : ij∈Pbar) : embed ij∈P := (hdata.2 ij).mp hij
  have hh := hboundFn Fsrc η ya yb Tsrc chartKey Uref Refs Gaps (Bselect:=Bselect)
    Pbar (fun ij => Mat (embed ij)) (fun ij => gap (embed ij))
    N za zb AlenA AlenB Za Zb Q K₀
    (fun ij => rat (embed ij)) (fun ij => vinv (embed ij))
    (fun ij => parity (embed ij)) (fun ij => anchor (embed ij)) e r v s
    (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) (Vscale:=Vscale) A (W:=W)
    hη
    hηsmall
    hya
    hyb
    hreg
    hjets
    htests
    hTsrc
    hMtwo
    hsourceScale
    (fun ij hij => hbase (embed ij) (hmem ij hij))
    (fun ij hij => hgapMem (embed ij) (hmem ij hij))
    (fun ij hij => hgeometryA (embed ij) (hmem ij hij))
    (fun ij hij => hgeometryB (embed ij) (hmem ij hij))
    hregime
    (fun ij hij => hchartColor (embed ij) (hmem ij hij))
    hVscale
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
    (fun ij hij => hx (embed ij) (hmem ij hij))
    (fun ij hij => hden (embed ij) (hmem ij hij))
    hθ
    hθmax
    (fun ij hij => hinv (embed ij) (hmem ij hij))
    hchart
    horientation
    hBcut
    hs
    hrefSet
    hparentSet
    hsep
    (fun ij hij => hwideL (embed ij) (hmem ij hij))
    (fun ij hij => hwideU (embed ij) (hmem ij hij))
    hUref
    hBselectSize
    hcutMargin
    hselectedWrap
    hreferenceDen
    hgapWidth
    hRQ
    hselectedUpper
    hscaleTen
    (fun ij hij => hfamilyGap (embed ij) (hmem ij hij))
    hgap
    hQN
    hNM
    hUR
    hrHeight
    hsHeight
    heHeight
    hvHeight
    (fun ij hij => hsourceColor (embed ij) (hmem ij hij))
    (fun ij hij => hlevel (embed ij) (hmem ij hij))
    (fun ij hij => hcolor (embed ij) (hmem ij hij))
    (fun ij hij => hnear (embed ij) (hmem ij hij))
    (fun ij hij => hnearNarrow (embed ij) (hmem ij hij))
    hsmall
    hNR
    hRN
    hNcube
    hminscale
    (fun ij hij => hMatdet (embed ij) (hmem ij hij))
    (fun ij hij => hMatt (embed ij) (hmem ij hij))
    (fun ij hij => hMatmap (embed ij) (hmem ij hij))
    (fun ij hij => hMatgamma (embed ij) (hmem ij hij))
    (fun ij hij => hcases (embed ij) (hmem ij hij))
    hNtwo
    (fun ij hij => hL (embed ij) (hmem ij hij))
    (fun ij hij => hU (embed ij) (hmem ij hij))
    (fun ij hij => hanchor (embed ij) (hmem ij hij))
    (fun ij hij => hcut (embed ij) (hmem ij hij))
    (fun ij hij => hcount (embed ij) (hmem ij hij))
    hsize
    hD
    hΔ
    hBsize
    hvchoice
    hUlo
  change Vscale*(Pbar.card:ℝ) ≤ (Vscale*(Kupper+Klower)+Klarge)*T^εloss at hh
  rw [hcard] at hh
  exact hh


private theorem actual_residual_phase_fiber_partition
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (ya yb : ℝ) :
    let Upper := P.filter (fun ij => Mat ij 2=0)
    let NonUpper := P.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) =>
      (E.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget
    ((phaseFiber Upper).card:ℝ)+((phaseFiber Lower).card:ℝ)+((phaseFiber Large).card:ℝ)=
      ((phaseFiber P).card:ℝ) := by
  classical
  intro Upper NonUpper Lower Large forget phaseFiber
  change (((Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)+
    (((Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)+
    (((Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)=
    (((P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)
  rw [(actual_phase_pair_forget_card Upper ya yb).1,
    (actual_phase_pair_forget_card Lower ya yb).1,
    (actual_phase_pair_forget_card Large ya yb).1,
    (actual_phase_pair_forget_card P ya yb).1]
  let Φ := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
  have hu : (Φ.filter (fun ij => Mat ij 2=0)).card+
      (Φ.filter (fun ij => Mat ij 2≠0)).card=Φ.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 2=0)
  have hl : ((Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1=0)).card+
      ((Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1≠0)).card=
      (Φ.filter (fun ij => Mat ij 2≠0)).card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 1=0)
  have hU : Φ.filter (fun ij => Mat ij 2=0)=
      Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Upper,Finset.mem_filter]
    tauto
  have hL : (Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1=0)=
      Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Lower,NonUpper,Finset.mem_filter]
    tauto
  have hH : (Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1≠0)=
      Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Large,NonUpper,Finset.mem_filter]
    tauto
  rw [hU] at hu
  rw [hL,hH] at hl
  exact_mod_cast (by omega :
    (Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card+
    (Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card+
    (Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card=Φ.card)


private theorem actual_phase_pair_source_data
    (phase : ℝ → ℝ → ℝ) (z : (ℝ × ℤ) → ℝ)
    (rat : (ℝ × ℤ) → ℚ) (vinv : (ℝ × ℤ) → ℤ) (K₀ : ℕ)
    (ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))
    (ya yb : ℝ) (hphase : ij.1.1.1=ya ∧ ij.2.1.1=yb) :
    let yp : Fin 2 → ℝ := ![ya,yb]
    let ip : Fin 2 → (ℝ × ℤ) × Fin 2 := ![ij.1,ij.2]
    let fp := fun i => phase (yp i)
    let xp : Fin 2 → ℝ := ![z (ya,ij.1.1.2),z (yb,ij.2.1.2)]
    let q := fun j => (rat j).den
    let mu := fun j => iteratedDeriv 3 (phase j.1) (round (z j))/6
    let ell := fun j => deriv (phase j.1) (round (z j))
    let qell := fun j => (q j:ℝ)*ell j
    let b := fun jp : (ℝ × ℤ) × Fin 2 => (⌊qell jp.1⌋+(jp.2:ℕ) : ℤ)
    let offset := fun jp => b jp-round (qell jp.1)
    let tau := fun jp => ((b jp:ℝ)-qell jp.1)/2
    let dual := fun j => -2*mu j*(Real.sqrt (2/(3*mu j*(q j:ℝ))))^3
    let cloud := fun jp => (![Int.fract (-(vinv jp.1:ℝ)*b jp/q jp.1),
      Int.fract (-(vinv jp.1:ℝ)/q jp.1),dual jp.1/Real.sqrt K₀,
      (3*dual jp.1*tau jp/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let qPair := fun i => q (ip i).1
    let muPair := fun i => iteratedDeriv 3 (fp i) (round (xp i))/6
    let ellPair := fun i => deriv (fp i) (round (xp i))
    let qellPair := fun i => (qPair i:ℝ)*ellPair i
    let bPair := fun i => (⌊qellPair i⌋+((ip i).2:ℕ) : ℤ)
    let tauPair := fun i => ((bPair i:ℝ)-qellPair i)/2
    let dualPair := fun i => -2*muPair i*(Real.sqrt (2/(3*muPair i*(qPair i:ℝ))))^3
    let cloudPair := fun i => (![Int.fract (-(vinv (ip i).1:ℝ)*bPair i/qPair i),
      Int.fract (-(vinv (ip i).1:ℝ)/qPair i),dualPair i/Real.sqrt K₀,
      (3*dualPair i*tauPair i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    ∀ i,
      fp i=phase (ip i).1.1 ∧ xp i=z (ip i).1 ∧
      (∀ n, iteratedDeriv n (fp i) (xp i)=
        iteratedDeriv n (phase (ip i).1.1) (z (ip i).1)) ∧
      (∀ n, iteratedDeriv n (fp i) (round (xp i))=
        iteratedDeriv n (phase (ip i).1.1) (round (z (ip i).1))) ∧
      deriv (fp i) (round (xp i))=
        deriv (phase (ip i).1.1) (round (z (ip i).1)) ∧
      bPair i-round (qellPair i) = offset (ip i) ∧
      cloudPair i=cloud (ip i) := by
  intro yp ip fp xp q mu ell qell b offset tau dual cloud
    qPair muPair ellPair qellPair bPair tauPair dualPair cloudPair i
  rcases ij with ⟨⟨⟨a,n⟩,pa⟩,⟨⟨b,m⟩,pb⟩⟩
  dsimp only at hphase
  rcases hphase with ⟨rfl,rfl⟩
  fin_cases i <;> exact ⟨rfl,rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,rfl⟩


/-- Actual-source common-mode family estimate. The SAME matrix returned by the
source sieve is consumed by the analytic Type-II/III bounds, without an assumed
matrix family or pair-count certificate. Genuine reference and point geometry
remain explicit until the source-entry construction supplies them. -/
theorem eventually_positive_difference_actual_family_source_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
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
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
 := by
  classical
  intro κ Ratio L
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hcountFn⟩ :=
    eventually_positive_difference_tagged_non_type_one_pair_mass hσsrc hcsrc hUsrc
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    exists_positive_difference_joint_type_decomposed_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro Jref θ hJref hθ hθmax hθaction
  filter_upwards [hcountFn (E:=E) (θ:=θ) hσ hJref hεloss] with T hboundFn
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale R Jsep Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation Fmodel hmodel f hlevel hminor hcomplete
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda Uband u w chart narrow qell V offset color ChartCap NarrowCap Cap
    q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge hvchoice hUlo Y
  have hηmax := hηsmall.trans hηcap
  have hθlt : θ < 1 := lt_of_le_of_lt hθmax (by norm_num)
  have hmodel₂ i (hi : i∈S) :=
    approximateModelPhase_mono (hmodel i hi) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,htype,hsplit,hstrong⟩ :=
    hsource S Fsrc z rat v Nlen Q K₀ N Vscale R Jsep Z
      (η:=η) (Tsrc:=Tsrc) (T:=T) (M:=M) (δ:=δ) (θ:=θ) (a:=a)
      hη hηmax hTsrc hT hM hδ hsourceScale hQ hθ ha hθlt hθaction
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN hJsep hJM hNM
      hmesh hgeometry hseparation hmodel₂ hlevel hminor hcomplete
  let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
    x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
  let radius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let wideRadius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
  let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
    (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
  let TypeOne := fun key => (Pairs key).filter (fun ij =>
    (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
    (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
  let Rest := fun key => (Pairs key).filter (fun ij => ij∉TypeOne key)
  let Upper := fun key => (Rest key).filter (fun ij => Mat ij 2=0)
  let NonUpper := fun key => (Rest key).filter (fun ij => Mat ij 2≠0)
  let Lower := fun key => (NonUpper key).filter (fun ij => Mat ij 1=0)
  let Large := fun key => (NonUpper key).filter (fun ij => Mat ij 1≠0)
  let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
  let phaseFiber := fun (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ab : ℝ × ℝ) =>
    (P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget

  change ∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
              (Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+∑ ab∈Y ×ˢ Y,
                (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
                  ((phaseFiber (Large key) ab).card:ℝ))) at hstrong
  have hPairData key ij (hij : ij∈Pairs key) :
      ij.1∈V ∧ ij.2∈V ∧ color ij.1=key ∧ color ij.2=key ∧ ij∈Pall := by
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have h1 := Finset.mem_filter.mp hp.1
    have h2 := Finset.mem_filter.mp hp.2
    exact ⟨h1.1,h2.1,h1.2,h2.2,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.1⟩,
        (Finset.mem_filter.mp hij).2⟩⟩
  have hMatData ij (hij : ij∈Pall) :
      Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
      (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3=(q ij.2.1:ℝ)/q ij.1.1 ∧
      ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3)=(rat ij.2.1:ℝ) ∧
      |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) := by
    have hg := hglobal ij hij
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hl1 := hlevel ij.1.1 (Finset.mem_product.mp hp.1).1
    have hl2 := hlevel ij.2.1 (Finset.mem_product.mp hp.2).1
    have ht : (Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 := hg.2.1
    have hm : ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f ij.2.1.1) (z ij.2.1)/2 := hg.2.2.2.2.1
    rw [hl1] at ht
    rw [hl1,hl2] at hm
    exact ⟨hg.1,ht,hm,hg.2.2.2.2.2.1⟩
  have hCases key ij (hij : ij∈Rest key) :
      (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0) ∨
      (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0) ∨
      (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| *κ^2*T) := by
    have hh := (htype key).2 ij (Finset.mem_filter.mp hij).1 (Finset.mem_filter.mp hij).2
    rcases hh with hu | hl | hh
    · exact Or.inl ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1⟩
    · exact Or.inr (Or.inl ⟨hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1⟩)
    · exact Or.inr (Or.inr hh)
  have hY y (hym : y∈Y) :
      y∈Icc (1:ℝ) 2 ∧ M ≤ A y ∧ A y+W y ≤ 2*M ∧
      Expdb.IsApproximateModelPhaseFunction
        (fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
    exact ⟨hy i hi,hA i hi,hW i hi,hmodel i hi⟩
  have hRadius d : radius d ≤ wideRadius d := by
    have hKpos : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
    fin_cases d
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      calc
        12*(K₀:ℝ)^2=12*(K₀:ℝ)^2*1 := by ring
        _ ≤ 12*(K₀:ℝ)^2*Vscale :=
          mul_le_mul_of_nonneg_left hVscale (by positivity)
    · exact le_rfl
    · exact le_rfl
  have hphaseBound key ab (hab : ab∈Y ×ˢ Y) :
      Vscale*((phaseFiber (Rest key) ab).card:ℝ) ≤
        (Vscale*(Kupper+Klower)+Klarge)*T^εloss := by
    let P := (Rest key).filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)
    let yp : Fin 2 → ℝ := ![ab.1,ab.2]
    let ip := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![p.1,p.2] : Fin 2 → (ℝ × ℤ) × Fin 2)
    let xp := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![z (ab.1,p.1.1.2),z (ab.2,p.2.1.2)] : Fin 2 → ℝ)
    let fp := fun i => f (yp i)
    let Ap := fun i => A (yp i)
    let Wp := fun i => W (yp i)
    let rp := fun p i => rat (ip p i).1
    let vp := fun p i => v (ip p i).1
    let pp := fun p i => (ip p i).2
    let qp := fun p i => (rp p i).den
    let mup := fun p i => iteratedDeriv 3 (fp i) (round (xp p i))/6
    let ellp := fun p i => deriv (fp i) (round (xp p i))
    let bp := fun p i => (⌊(qp p i:ℝ)*ellp p i⌋+(pp p i:ℕ) : ℤ)
    let crp := fun p i => round ((qp p i:ℝ)*ellp p i)
    let taup := fun p i => ((bp p i:ℝ)-(qp p i:ℝ)*ellp p i)/2
    let dualp := fun p i => -2*mup p i*(Real.sqrt (2/(3*mup p i*(qp p i:ℝ))))^3
    let cloudp := fun p i => (![Int.fract (-(vp p i:ℝ)*bp p i/qp p i),
      Int.fract (-(vp p i:ℝ)/qp p i),dualp p i/Real.sqrt K₀,
      (3*dualp p i*taup p i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    have hRest p (hp : p∈P) : p∈Rest key := (Finset.mem_filter.mp hp).1
    have hPairs p (hp : p∈P) : p∈Pairs key := (Finset.mem_filter.mp (hRest p hp)).1
    have hPhase p (hp : p∈P) : p.1.1.1=ab.1 ∧ p.2.1.1=ab.2 :=
      (Finset.mem_filter.mp hp).2
    have hSlot p (hp : p∈P) i : ip p i∈V := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).1
      · exact (hPairData key p (hPairs p hp)).2.1
    have hS p (hp : p∈P) i : (ip p i).1∈S :=
      (Finset.mem_product.mp (hSlot p hp i)).1
    have hColor p (hp : p∈P) i : color (ip p i)=key := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).2.2.1
      · exact (hPairData key p (hPairs p hp)).2.2.2.1
    have hYP p (hp : p∈P) i : yp i=(ip p i).1.1 := by
      fin_cases i
      · exact (hPhase p hp).1.symm
      · exact (hPhase p hp).2.symm
    have hPointA p (hp : p∈P) : (ab.1,p.1.1.2)=p.1.1 :=
      Prod.ext (hPhase p hp).1.symm rfl
    have hPointB p (hp : p∈P) : (ab.2,p.2.1.2)=p.2.1 :=
      Prod.ext (hPhase p hp).2.symm rfl
    have hData p (hp : p∈P) i :
        xp p i=z (ip p i).1 ∧
        (∀ n, iteratedDeriv n (fp i) (xp p i)=
          iteratedDeriv n (f (ip p i).1.1) (z (ip p i).1)) ∧
        bp p i-crp p i = offset (ip p i) ∧ cloudp p i=cloud (ip p i) := by
      have hh := actual_phase_pair_source_data f z rat v K₀ p ab.1 ab.2 (hPhase p hp) i
      exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2⟩
    have hLoc p (hp : p∈P) i : xp p i-(Ap i:ℝ)=xlocal (ip p i).1 := by
      change xp p i-(A (yp i):ℝ)=z (ip p i).1-(A (ip p i).1.1:ℝ)
      rw [(hData p hp i).1,hYP p hp i]
    have hWp p (hp : p∈P) i : Wp i=W (ip p i).1.1 :=
      congrArg W (hYP p hp i)
    have hChartColor p (hp : p∈P) i :
        (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rp p i:ℝ))/a⌋,
          ⌊((Tsrc/(2*M^2))*(rp p i:ℝ)⁻¹)/a⌋)=key.1 := by
      rw [hYP p hp i]
      exact congrArg Prod.fst (hColor p hp i)
    have hNear p (hp : p∈P) d :
        |cloudp p 0 d-cloudp p 1 d| ≤ 2*wideRadius d := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      exact ((Finset.mem_filter.mp (hPairs p hp)).2 d).trans
        (mul_le_mul_of_nonneg_left (hRadius d) (by norm_num))
    have hNearNarrow p (hp : p∈P) :
        |cloudp p 0 1-cloudp p 1 1| ≤ 1/(6*(K₀:ℝ)^2*Vscale) := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      have hn := (Finset.mem_filter.mp (hPairs p hp)).2 (1 : Fin 4)
      change |cloud p.1 1-cloud p.2 1| ≤ 2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
      convert hn using 1
      ring
    have hYa := hY ab.1 (Finset.mem_product.mp hab).1
    have hYb := hY ab.2 (Finset.mem_product.mp hab).2
    have hAp i : M ≤ Ap i := by
      fin_cases i
      · exact hYa.2.1
      · exact hYb.2.1
    have hWpair i : (Ap i:ℝ)+Wp i ≤ 2*M := by
      fin_cases i
      · exact hYa.2.2.1
      · exact hYb.2.2.1
    have hFp i : Expdb.IsApproximateModelPhaseFunction
        (fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)) σ 4 δ := by
      fin_cases i
      · exact hYa.2.2.2
      · exact hYb.2.2.2
    have hGeoA p (hp : p∈P) :
        N ≤ Nlen (ab.1,p.1.1.2) ∧ Nlen (ab.1,p.1.1.2) ≤ 3*N ∧
        round (z (ab.1,p.1.1.2))+(Nlen (ab.1,p.1.1.2):ℤ)=
          Z ab.1+(N:ℤ)*p.1.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.1.1 (hS p hp 0)
      rw [←hPointA p hp] at hh
      exact hh
    have hGeoB p (hp : p∈P) :
        N ≤ Nlen (ab.2,p.2.1.2) ∧ Nlen (ab.2,p.2.1.2) ≤ 3*N ∧
        round (z (ab.2,p.2.1.2))+(Nlen (ab.2,p.2.1.2):ℤ)=
          Z ab.2+(N:ℤ)*p.2.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.2.1 (hS p hp 1)
      rw [←hPointB p hp] at hh
      exact hh

    have hh := hboundFn Fsrc η ab.1 ab.2 Tsrc key.1 Uref Refs Gaps
      (Bselect:=Bselect) P Mat (fun p => gap p.1.1) N
      (fun n => z (ab.1,n)) (fun n => z (ab.2,n))
      (fun n => Nlen (ab.1,n)) (fun n => Nlen (ab.2,n)) (Z ab.1) (Z ab.2)
      Q K₀ rp vp pp (fun p => anchor p.1.1) e r vRef s
      (δ:=δ) (M:=M) (R:=R) (base:=0) (Bcut:=Bcut) (Vscale:=Vscale) Ap (W:=Wp)
      hPhase hη hηsmall hYa.1 hYb.1 hreg hjets htests hTsrc hMtwo hsourceScale
      (fun p hp => by
        change 0 ≤ xp p 0-(Ap 0:ℝ)
        rw [hLoc p hp 0]
        exact le_of_lt (lt_trans (by norm_num) (hx _ (hS p hp 0)).1))
      (fun p hp => hgapMem _ (hS p hp 0))
      hGeoA hGeoB hregime hChartColor hVscale hδ hFp hT hM
      (Nat.cast_pos.mpr hN) hR hRM hQ hscale hmesh hAp hWpair
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hx _ (hS p hp i))
      (fun p hp i => hden _ (hS p hp i))
      hθ hθmax (fun p hp i => hinv _ (hS p hp i))
      hchart horientation hBcut hs hrefSet hparentSet hsep
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideU _ (hS p hp i))
      hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen (fun p hp => hfamilyGap _ (hS p hp 0))
      hgap hQN hNsqM hUR hrHeight hsHeight heHeight hvHeight
      (fun p hp => by
        exact congrArg (fun cc => cc.2.1) ((hColor p hp 0).trans (hColor p hp 1).symm))
      (fun p hp i => by
        change iteratedDeriv 2 (fp i) (xp p i)/2=(rp p i:ℝ)
        rw [(hData p hp i).2.1 2]
        exact hlevel _ (hS p hp i))
      (fun p hp => by
        change bp p 0-crp p 0=bp p 1-crp p 1
        rw [(hData p hp 0).2.2.1,(hData p hp 1).2.2.1]
        exact (hratios _ (hSlot p hp 0) _ (hSlot p hp 1)
          ((hColor p hp 0).trans (hColor p hp 1).symm)).2.2)
      hNear hNearNarrow hsmall hNR hRN hNcube hminscale
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.2)
      (fun p hp => hCases key p (hRest p hp)) hNtwo
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hU _ (hS p hp i))
      (fun p hp => hanchor _ (hS p hp 0))
      (fun p hp => hcut _ (hS p hp 0))
      (fun p hp => hcount _ (hS p hp 0))
      hsize hD hΔ hBsize hvchoice hUlo
    change Vscale*(P.card:ℝ) ≤ (Vscale*(Kupper+Klower)+Klarge)*T^εloss at hh
    have hforget : (phaseFiber (Rest key) ab).card=P.card :=
      (actual_phase_pair_forget_card (Rest key) ab.1 ab.2).1
    rw [hforget]
    exact hh
  let typeMass := Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)
  let residual := fun key => ∑ ab∈Y ×ˢ Y,
    (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
      ((phaseFiber (Large key) ab).card:ℝ))
  let totalMass := (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss
  have hResidual key : Vscale*residual key ≤ totalMass := by
    dsimp only [residual]
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _ab∈Y ×ˢ Y, (Vscale*(Kupper+Klower)+Klarge)*T^εloss := by
        apply Finset.sum_le_sum
        intro ab hab
        have hparts := actual_residual_phase_fiber_partition (Rest key) Mat ab.1 ab.2
        change ((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
          ((phaseFiber (Large key) ab).card:ℝ)=((phaseFiber (Rest key) ab).card:ℝ) at hparts
        rw [hparts]
        exact hphaseBound key ab hab
      _ = totalMass := by
        simp only [Finset.sum_const,Finset.card_product,nsmul_eq_mul,Nat.cast_mul,totalMass]
        ring
  have hLinear :
      Vscale*(∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key))=
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(Vscale*typeMass+Vscale*residual key) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro key _
    ring
  refine ⟨hcard,?_⟩
  intro k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
  calc
    _ ≤ C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key) :=
      hstrong k
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (Vscale*∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key)) := by ac_rfl
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(Vscale*typeMass+Vscale*residual key) := by
      rw [hLinear]
    _ ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
          (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+totalMass) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg hCap 11))
      apply Finset.sum_le_sum
      intro key _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) 10)
      have he : Vscale*typeMass=Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := by
        simp only [typeMass,mul_assoc]
      rw [he]
      exact add_le_add le_rfl (hResidual key)


example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
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
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
 :=
  HuxleyActualFamilySourceScratch.eventually_positive_difference_actual_family_source_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss

#print axioms actual_phase_pair_forget_card
#print axioms eventually_positive_difference_tagged_non_type_one_pair_mass
#print axioms actual_residual_phase_fiber_partition
#print axioms actual_phase_pair_source_data
#print axioms eventually_positive_difference_actual_family_source_sieve
end HuxleyActualFamilySourceScratch
