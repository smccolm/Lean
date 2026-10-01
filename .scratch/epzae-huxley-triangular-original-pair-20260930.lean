import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularPairScratch

theorem physicalModelPhase_reference_translation_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ) (hMat : Function.Injective Mat)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun t ab => (P.filter (fun ij => entry ij=t ∧ gap ij=ab)).image block
    ∃ pick : ℤ → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ t∈P.image entry, ∀ ab∈P.image gap, ∀ j∈S t ab,
        pick t ab j∈P ∧ entry (pick t ab j)=t ∧ gap (pick t ab j)=ab ∧
        block (pick t ab j)=j ∧
        za (pick t ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ t∈P.image entry, ∑ ab∈P.image gap, (S t ab).card := by
  classical
  intro f h hmap block S
  obtain ⟨pickM,hpick,hcard⟩ := physicalModelPhase_reference_matrix_window_selection
    P (fun ij => Mat (entry ij)) gap F A Wlim za zb AlenA Alen N Za Z W
    hσ hδ hF hT hM hN hA hW hbase hz hgeometryA hgeometry hmap
  have hS t ab : (P.filter (fun ij => Mat (entry ij)=Mat t ∧ gap ij=ab)).image block=S t ab := by
    simp only [S,hMat.eq_iff]
  have himage : P.image (fun ij => Mat (entry ij))=(P.image entry).image Mat := by
    simp only [Finset.image_image,Function.comp_def]
  refine ⟨fun t ab j => pickM (Mat t) ab j,?_,?_⟩
  · intro t ht ab hab j hj
    have hmt : Mat t∈P.image (fun ij => Mat (entry ij)) := by
      rw [himage]
      exact Finset.mem_image_of_mem Mat ht
    have hj' : j∈(P.filter (fun ij => Mat (entry ij)=Mat t ∧ gap ij=ab)).image block := by
      rw [hS]
      exact hj
    have hp := hpick (Mat t) hmt ab hab j hj'
    exact ⟨hp.1,hMat hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  · change P.card ≤ 60*∑ m∈P.image (fun ij => Mat (entry ij)), ∑ ab∈P.image gap,
        ((P.filter (fun ij => Mat (entry ij)=m ∧ gap ij=ab)).image block).card at hcard
    rw [himage,Finset.sum_image (fun _ _ _ _ he => hMat he)] at hcard
    simpa only [hS] using hcard

/-- The actual source-defined Fourier-pair set is reindexed by its
triangular translation and selected reference windows, then consumed by
the source-cutoff mass theorem with the proved factor-60 multiplicity. -/
theorem positive_difference_actual_fourier_triangular_original_pair_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_source_cutoff_sample_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut lambda Uband θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  have hNnat : 0 < N := by exact_mod_cast hN
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hz ij (hij : ij∈P) : zb ij.2.1∈Ioo 0 (W 1) := by
    have hh := hx ij hij 1
    rw [hxb ij hij] at hh
    constructor <;> linarith only [hh.1,hh.2]
  have hmodelMap ij (hij : ij∈P) :
      ((Mat (entry ij) 0:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(iteratedDeriv 2 (f 0) (za ij.1.1)/2)+Mat (entry ij) 3)=
        iteratedDeriv 2 (f 1) (zb ij.2.1)/2 := by
    rw [←hxa ij hij,←hxb ij hij,hlevel ij hij 0,hlevel ij hij 1]
    exact hMatmap ij hij
  let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    ⌊(za ij.1.1-base)/(N:ℝ)⌋.toNat
  let S := fun t ab => (P.filter (fun ij => entry ij=t ∧ gap ij=ab)).image block
  obtain ⟨pick,hpick,hpairNat⟩ := physicalModelPhase_reference_translation_window_selection
    P entry Mat hMat gap F (fun i => (A i:ℝ)) W za zb AlenA AlenB N Za Zb base
    hσ hδ hF₂ hT hM hNnat hA hW hbase hz hgeometryA hgeometryB hmodelMap
  have hdata t (ht : t∈P.image entry) ab (_hab : ab∈Gaps) j (hj : j∈S t ab) :
      pick t ab j∈P ∧ entry (pick t ab j)=t ∧ gap (pick t ab j)=ab ∧
        block (pick t ab j)=j ∧
        za (pick t ab j).1.1∈Icc (base+(N:ℝ)*j) (base+(N:ℝ)*((j:ℝ)+1)) := by
    obtain ⟨ij,hij,_he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    have hab' : ab∈P.image gap := Finset.mem_image.mpr ⟨ij,hh.1,hh.2.2⟩
    exact hpick t ht ab hab' j hj
  have hgapSub : P.image gap ⊆ Gaps := by
    intro ab hab
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hab
    exact hgapMem ij hij
  have hpairNat' : P.card ≤ 60*∑ t∈P.image entry, ∑ ab∈Gaps, (S t ab).card := by
    apply hpairNat.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro t _
    exact Finset.sum_le_sum_of_subset_of_nonneg hgapSub (fun _ _ _ => Nat.zero_le _)
  have hpair : (P.card:ℝ) ≤ 60*(∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) := by
    exact_mod_cast hpairNat'
  have hmass :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (∑ t∈P.image entry, ∑ ab∈Gaps, ((S t ab).card:ℝ)) ≤ 4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := by
    exact hmassFn Fsrc η ya yb Tsrc E (P.image entry) chartKey Uref Refs (fun _ => Gaps)
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀
      (fun t ab j => rat (pick t ab j)) (fun t ab j => vinv (pick t ab j))
      (fun t ab j => parity (pick t ab j)) (fun t ab j => anchor (pick t ab j))
      Mat (fun _ => e) (fun _ => r) (fun _ => v) (fun _ => s)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=(N:ℝ)) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=fun t ab j => x (pick t ab j))
      hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      (by
        intro t ht
        obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ht
        exact hentry ij hij)
      (by
        intro t ht ab hab j hj i
        have hp := hdata t ht ab hab j hj
        have hh := hchartColor _ hp.1 i
        rw [hp.2.1] at hh
        exact hh)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun t ht ab hab j hj => hx _ (hdata t ht ab hab j hj).1)
      (by
        intro t ht ab hab j hj
        have hp := hdata t ht ab hab j hj
        change x (pick t ab j) 0∈_
        rw [hxa _ hp.1]
        exact hp.2.2.2.2)
      (fun t ht ab hab j hj => hden _ (hdata t ht ab hab j hj).1) hlambda hUband hθ hθmax (fun t ht ab hab j hj => hcurv _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hinv _ (hdata t ht ab hab j hj).1) (fun _ _ => hchart) (fun _ _ => horientation) hBcut (fun _ _ => hs) (fun _ _ => hrefSet) (fun _ _ => hparentSet) hsep (fun t ht ab hab j hj => hwideL _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hwideU _ (hdata t ht ab hab j hj).1) hUref hBselectSize hcutMargin hselectedWrap (fun _ _ => hreferenceDen) (fun _ _ => hgapWidth) hRQ hselectedUpper hscaleTen
      (by
        intro t ht ab hab j hj
        have hp := hdata t ht ab hab j hj
        have hh := hfamilyGap _ hp.1
        rw [hp.2.2.1] at hh
        exact hh)
      (fun _ _ => hgap) (fun t ht ab hab j hj => hsourceColor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hlevel _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcolor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hnear _ (hdata t ht ab hab j hj).1) hsmall hNR hRN hNcube hminscale
      hMatdet
      (by
        intro t ht ab hab j hj
        have hp := hdata t ht ab hab j hj
        have hh := hMatt _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      (by
        intro t ht ab hab j hj
        have hp := hdata t ht ab hab j hj
        have hh := hMatmap _ hp.1
        rw [hp.2.1] at hh
        exact hh)
      hMatgamma hNtwo (fun t ht ab hab j hj => hL _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hU _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hanchor _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcut _ (hdata t ht ab hab j hj).1) (fun t ht ab hab j hj => hcount _ (hdata t ht ab hab j hj).1) hsize hD hΔ hBsize (fun _ _ => hBmajor) (fun _ _ => hCmajor)
  constructor
  · intro htri
    exact hpair.trans (mul_le_mul_of_nonneg_left (hmass.1 htri) (by norm_num : (0:ℝ) ≤ 60))
  · intro htri
    exact hpair.trans (mul_le_mul_of_nonneg_left (hmass.2 htri) (by norm_num : (0:ℝ) ≤ 60))

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ) (hMat : Function.Injective Mat)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*h 0 (za ij.1.1)+Mat (entry ij) 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun t ab => (P.filter (fun ij => entry ij=t ∧ gap ij=ab)).image block
    ∃ pick : ℤ → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ t∈P.image entry, ∀ ab∈P.image gap, ∀ j∈S t ab,
        pick t ab j∈P ∧ entry (pick t ab j)=t ∧ gap (pick t ab j)=ab ∧
        block (pick t ab j)=j ∧
        za (pick t ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ t∈P.image entry, ∑ ab∈P.image gap, (S t ab).card :=
  HuxleyTriangularPairScratch.physicalModelPhase_reference_translation_window_selection P entry Mat hMat gap F A Wlim za zb AlenA Alen N Za Z W (σ:=σ) (δ:=δ) (T:=T) (M:=M) hσ hδ hF hT hM hN hA hW hbase hz hgeometryA hgeometry

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) :=
  HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_pair_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


/-- The model third derivative prevents the actual normalized source
amplitude from degenerating. No lower comparison between Tsrc and T
is assumed. -/
private theorem positive_difference_approximate_model_source_amplitude
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc := by
  intro F hF
  let G := fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)
  have hFu : F=fun u => (Tsrc/T)*G u := by
    funext u
    dsimp only [F,G]
    ring
  have hd : iteratedDeriv 3 F (3/2)=
      (Tsrc/T)*iteratedDeriv 3 G (3/2) := by
    rw [hFu,iteratedDeriv_const_mul_field]
  have hlow : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F (3/2) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
  have hu := positive_jets_difference_mixed_upper Fsrc hσsrc hUsrc hη hηmax
    (by norm_num : (3/2:ℝ)∈Icc (3/4:ℝ) (9/4))
    (show y∈Icc (1/2:ℝ) 3 from
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
    hreg hjets 3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hupper : |iteratedDeriv 3 F (3/2)| ≤ (Tsrc/T)*(3*Usrc/σsrc) := by
    rw [hd,abs_mul,abs_of_pos (div_pos hTsrc hT)]
    exact mul_le_mul_of_nonneg_left hu (div_pos hTsrc hT).le
  have hh := hlow.trans ((le_abs_self _).trans hupper)
  have he : (Tsrc/T)*(3*Usrc/σsrc)=3*Usrc*Tsrc/(σsrc*T) := by ring
  rw [he] at hh
  have hc := (le_div_iff₀ (mul_pos hσsrc hT)).mp hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hUsrc)).mpr
  nlinarith only [hc]

/-- The same source and model phases yield a physical curvature band
scaled by T, with the Tsrc lower comparison derived from their jets. -/
private theorem positive_difference_model_normalized_curvature_band
    (Fsrc : ℝ → ℝ) {σsrc csrc Usrc η y₀ Tsrc T E M σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy₀ : y₀∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hscale : Tsrc ≤ E*T)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y₀))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
    let f := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    ∀ y∈Icc (1:ℝ) 2, ∀ z∈Icc M (2*M),
      csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2) ≤
        |iteratedDeriv 2 (f y) z/2| ∧
      |iteratedDeriv 2 (f y) z/2| ≤ (3*Usrc/σsrc)*E*T/(2*M^2) := by
  intro F hF f y hy z hz
  have hsource := positive_difference_approximate_model_source_amplitude Fsrc
    hσsrc hUsrc hη hηmax hy₀ hTsrc hT hσ hδ hreg hjets hF
  have hh := positive_difference_half_curvature_source_bounds Fsrc
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM hy hz hreg hjets htests
  constructor
  · apply le_trans _ hh.1
    calc
      _ = (csrc/(4*σsrc*M^2))*(modelPhaseThirdLower σ*σsrc*T/(3*Usrc)) := by
        field_simp
        ring
      _ ≤ (csrc/(4*σsrc*M^2))*Tsrc :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  · apply hh.2.trans
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
      (by positivity : (0:ℝ) ≤ 2*M^2)

/-- The original-pair bound with its curvature band derived from the
SAME source and model phases. Neither a curvature-band certificate nor
a lower Tsrc/T comparison is supplied. -/
theorem positive_difference_actual_fourier_triangular_original_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by

  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_triangular_original_pair_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB
    lambda Uband yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Aupper Bupper Alower Blower DupperCut DlowerCut
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hE : 0 < E := (mul_pos_iff_of_pos_right hT).mp (hTsrc.trans_le hsourceScale)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 ≤ Uband := by dsimp only [Uband]; positivity
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hmodel₀ := approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl
  have hband := positive_difference_model_normalized_curvature_band Fsrc
    hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hya
    hTsrc hT hM hσ hδ hsourceScale hreg hjets htests hmodel₀
  have hcurv ij (hij : ij∈P) i :
      lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband := by
    have hyi : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
    have hxi := hx ij hij i
    have hpoint : (A i:ℝ)+x ij i∈Icc M (2*M) :=
      ⟨by linarith only [hA i,hxi.1],by linarith only [hW i,hxi.2]⟩
    rw [←hlevel ij hij i,hjet]
    exact hband (yp i) hyi _ hpoint
  exact hmassFn Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps (Bselect:=Bselect)
    P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
    rat vinv parity anchor e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
    hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep
    hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
    hRQ hselectedUpper hscaleTen hfamilyGap hgap
    hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let Aupper := 2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
    let Bupper := Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
      Dupper*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
    let Alower := 8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
    let Blower := 4*Clower*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
      (4*Dlower*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) :=
  HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_source_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

private theorem two_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x^((2:ℝ)/3))^3=x^2 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

/-- The single physical regime from (10.7) controls both cubic-root
and short-family translation terms; the logarithmic budget is explicit. -/
private theorem triangular_translation_source_regime
    {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    N^2*U ≤ (M*R^2)^((2:ℝ)/3)*L ∧
      N^3*U ≤ M*R^2*L^((3:ℝ)/2) := by
  have hLpow : (L^((3:ℝ)/2))^2=L^3 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL]
    norm_num
  have hN8 : N^8 ≤ M^2*R^6*L^3 := by
    calc
      _ = (N^4)^2 := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))^2 := by gcongr
      _ = _ := by rw [mul_pow,mul_pow,hLpow]; ring
  have hUcube : U^3 ≤ (N/R)^2 := by
    calc
      _ ≤ ((N/R)^((2:ℝ)/3))^3 := by gcongr
      _ = _ := two_thirds_cube (div_nonneg hN.le hR.le)
  have hcube : (N^2*U)^3 ≤ ((M*R^2)^((2:ℝ)/3)*L)^3 := by
    calc
      _ = N^6*U^3 := by ring
      _ ≤ N^6*(N/R)^2 := mul_le_mul_of_nonneg_left hUcube (by positivity)
      _ = N^8/R^2 := by field_simp
      _ ≤ (M^2*R^6*L^3)/R^2 :=
        div_le_div_of_nonneg_right hN8 (sq_nonneg R)
      _ = _ := by rw [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)]; field_simp
  constructor
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3≠0)).mp hcube
  · have hratio : 1 ≤ N/R := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRN)
    have hlinear : U ≤ N/R := hselected.trans
      ((Real.rpow_le_rpow_of_exponent_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)).trans_eq (Real.rpow_one _))
    calc
      _ ≤ N^3*(N/R) := mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = N^4/R := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))/R := div_le_div_of_nonneg_right hregime hR.le
      _ = _ := by field_simp


private theorem triangular_physical_regime_costs
    {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    (M^2/N^4)*(M/(N*R^2))^2 ≤ ((M^2/(N^4*U))*L)^3 ∧
    (R^4/N^2)*(N*R^2/M)^2 ≤ ((R^4/(N^2*U))*L)^3 ∧
    M/(N*R^2) ≤ (M^2/(N^4*U))*L^((3:ℝ)/2) ∧
    N*R^2/M ≤ (R^4/(N^2*U))*L^((3:ℝ)/2) := by
  obtain ⟨hfirst,hshort⟩ := triangular_translation_source_regime
    hM hN hR hU.le hL hRN hselected hregime
  have hcore : N^6*U^3 ≤ M^2*R^4*L^3 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ N^2*U) hfirst 3
    simp only [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)] at hh
    convert hh using 1 <;> ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [show (M^2/N^4)*(M/(N*R^2))^2=M^4/(N^6*R^4) by field_simp,
      show ((M^2/(N^4*U))*L)^3=M^6*L^3/(N^12*U^3) by field_simp]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ M^4*N^6)
    nlinarith only [hh]
  · rw [show (R^4/N^2)*(N*R^2/M)^2=R^8/M^2 by field_simp,
      show ((R^4/(N^2*U))*L)^3=R^12*L^3/(N^6*U^3) by field_simp]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ R^8)
    nlinarith only [hh]
  · rw [show (M^2/(N^4*U))*L^((3:ℝ)/2)=M^2*L^((3:ℝ)/2)/(N^4*U) by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hshort (by positivity : (0:ℝ) ≤ M*N)
    nlinarith only [hh]
  · rw [show (R^4/(N^2*U))*L^((3:ℝ)/2)=R^4*L^((3:ℝ)/2)/(N^2*U) by ring]
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hshort (sq_nonneg R)
    nlinarith only [hh]


private theorem triangular_weight_regime_absorption
    {Aconst Dconst Bconst abase dbase Cost L : ℝ}
    (hAconst : 0 ≤ Aconst) (hDconst : 0 ≤ Dconst)
    (habase : 0 ≤ abase) (hdbase : 0 ≤ dbase)
    (hCost : 0 ≤ Cost) (hL : 0 ≤ L)
    (hD : 1 ≤ Dconst*dbase)
    (hcubeBase : abase*dbase^2 ≤ (Cost*L)^3)
    (hshortBase : dbase ≤ Cost*L^((3:ℝ)/2)) :
    3*(Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*(9*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*L+
        2*Bconst*(3+2*Real.log (Dconst*dbase+2))+
        (3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
  have hrootCube (z : ℝ) (hz : 0 ≤ z) : (z^((3:ℝ)⁻¹))^3=z := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hz (by norm_num : (3:ℕ)≠0)
  have hDnonneg : 0 ≤ Dconst*dbase := mul_nonneg hDconst hdbase
  have hthree : Dconst*dbase+2 ≤ 3*(Dconst*dbase) := by linarith only [hD]
  have hcube :
      ((Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3))^3 ≤
        (3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)^3 := by
    calc
      _ = (Aconst*abase)*(Dconst*dbase+2)^2 := by
        rw [mul_pow,hrootCube (Aconst*abase) (mul_nonneg hAconst habase),
          two_thirds_cube (by positivity)]
      _ ≤ (Aconst*abase)*(3*(Dconst*dbase))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hthree 2) (mul_nonneg hAconst habase)
      _ = 9*(Aconst*Dconst^2)*(abase*dbase^2) := by ring
      _ ≤ 9*(Aconst*Dconst^2)*(Cost*L)^3 :=
        mul_le_mul_of_nonneg_left hcubeBase (by positivity)
      _ ≤ 27*(Aconst*Dconst^2)*(Cost*L)^3 := by
        have hh : 0 ≤ (Aconst*Dconst^2)*(Cost*L)^3 := by positivity
        nlinarith only [hh]
      _ = _ := by
        simp only [mul_pow,hrootCube (Aconst*Dconst^2) (mul_nonneg hAconst (sq_nonneg Dconst))]
        ring
  have hroot := (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (3:ℕ)≠0)).mp hcube
  have hroot3 := mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 3)
  have hshort : (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
    have hh := mul_le_mul_of_nonneg_left hshortBase hDconst
    nlinarith only [hD,hh]
  calc
    _ ≤ 3*(3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) :=
      by simpa only [mul_assoc] using add_le_add (add_le_add hroot3 (le_refl (2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))))) hshort
    _ = _ := by ring


private theorem triangular_source_weight_scale_identities
    {M N R U T σsrc csrc Usrc κ Lunit E θ CU CL DU DL Cthird B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hT : 0 < T)
    (hscale : T*N*R^2=M^3) :
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*U)+DU*(B+1)*E^2*M^2/(4*N^4*U)
    let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*U)+(4*DL*(B+1)*R^4)/(4*N^2*U)
    let AupperConst := 2*CU*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := CU*(Cthird+1)*E^2/Lunit^2+DU*(B+1)*E^2/4
    let AlowerConst := 8*CL*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*CL*(Cthird+1)/Lunit^2+DL*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    Aupper=AupperConst*(M^2/N^4) ∧
    Bupper=BupperConst*(M^2/(N^4*U)) ∧
    Alower=AlowerConst*(R^4/N^2) ∧
    Blower=BlowerConst*(R^4/(N^2*U)) ∧
    θ*Uband=DupperConst*(M/(N*R^2)) ∧
    θ/lambda=DlowerConst*(N*R^2/M) := by
  intro lambda Uband Aupper Bupper Alower Blower AupperConst BupperConst
    AlowerConst BlowerConst DupperConst DlowerConst
  have hforward : T/M^2=M/(N*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hscale]
  have hreverse : M^2/T=N*R^2/M := by
    apply (div_eq_div_iff hT.ne' hM.ne').mpr
    nlinarith only [hscale]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · dsimp only [Aupper,AupperConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Bupper,BupperConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Alower,AlowerConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Blower,BlowerConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · calc
      _ = DupperConst*(T/M^2) := by dsimp only [Uband,DupperConst]; ring
      _ = _ := by rw [hforward]
  · calc
      _ = DlowerConst*(M^2/T) := by
        dsimp only [lambda,DlowerConst]
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
      _ = _ := by rw [hreverse]

private theorem physical_source_triangular_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ0 : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    0 ≤ B ∧ 0 ≤ Cthird := by
  intro κ Cphys c J B C₂ C₃ Ct Cc Kres Gamma Cthird
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]; positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hB) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) hB) hCc))
      (mul_nonneg (by norm_num) hCt))
      (mul_nonneg (by norm_num) hCc))
      (mul_nonneg (by norm_num) hCN))) hκ.le
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  exact ⟨hB,hCthird⟩


private theorem rational_narrow_triangular_translation_bounds
    (p : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (Q : ℕ)
    {lambda U θ : ℝ} (hQ : 0 < Q) (hlambda : 0 < lambda)
    (hU : 0 ≤ U) (hθ : 0 < θ)
    (hcurv : ∀ i, lambda ≤ |(p i:ℝ)| ∧ |(p i:ℝ)| ≤ U)
    (hden : ∀ i, (p i).den ≤ Q ∧ Q ≤ 2*(p i).den)
    (hcolor : (⌊((p 0).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 0).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)=
      (⌊((p 1).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((p 1).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋))
    (hdenmap : (Mat 2:ℝ)*(p 0:ℝ)+Mat 3=((p 1).den:ℝ)/(p 0).den)
    (hmap : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(p 0:ℝ)+Mat 3)=(p 1:ℝ)) :
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → |(Mat 1:ℝ)| ≤ θ*U) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → |(Mat 2:ℝ)| ≤ θ/lambda) := by
  have hb := (rational_narrow_band_partition (Finset.univ : Finset (Fin 2)) p Q
    hQ hlambda hU hθ (fun i _ => hcurv i) (fun i _ => hden i)).2
    0 (Finset.mem_univ 0) 1 (Finset.mem_univ 1) hcolor
  have hxabs : 0 < |(p 0:ℝ)| := hlambda.trans_le (hcurv 0).1
  have hx : (p 0:ℝ)≠0 := abs_pos.mp hxabs
  have hdpos : (0:ℝ) < (Mat 2:ℝ)*(p 0:ℝ)+Mat 3 := by
    rw [hdenmap]
    exact div_pos (by exact_mod_cast (p 1).pos) (by exact_mod_cast (p 0).pos)
  have hnumeq : ((Mat 0:ℝ)*(p 0:ℝ)+Mat 1)/(p 0:ℝ)=
      ((p 1).num:ℝ)/(p 0).num := by
    rw [(div_eq_iff hdpos.ne').mp hmap,hdenmap]
    simp only [Rat.cast_def]
    field_simp
  constructor
  · intro htri
    have hh := hb.2
    rw [←hnumeq,htri.1,Int.cast_one,one_mul] at hh
    have he : ((p 0:ℝ)+Mat 1)/(p 0:ℝ)-1=(Mat 1:ℝ)/(p 0:ℝ) := by
      field_simp
      ring
    rw [he,abs_div] at hh
    exact ((div_le_iff₀ hxabs).mp hh).trans
      (mul_le_mul_of_nonneg_left (hcurv 0).2 hθ.le)
  · intro htri
    have hh := hb.1
    rw [←hdenmap,htri.2.2,Int.cast_one,add_sub_cancel_right,abs_mul] at hh
    apply (le_div_iff₀ hlambda).mpr
    exact (mul_le_mul_of_nonneg_left (hcurv 0).1 (abs_nonneg _)).trans hh

private theorem triangular_original_mass_regime_assembly
    (m0 : ℕ) {M N R U T σsrc csrc Usrc κ Lunit E θ CU CL DU DL Cthird B Lregime mass : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hRpos : 0 < R) (hUp : 0 < U) (hT : 0 < T)
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hκ : 0 < κ) (hLunit : 0 < Lunit) (hE : 0 ≤ E) (hθ : 0 ≤ θ)
    (hCU : 0 ≤ CU) (hCL : 0 ≤ CL) (hDU : 0 ≤ DU) (hDL : 0 ≤ DL)
    (hCthird : 0 ≤ Cthird) (hBnonneg : 0 ≤ B)
    (hLregime : 0 ≤ Lregime) (hRN : R ≤ N) (hscale : T*N*R^2=M^3)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*Lregime^((3:ℝ)/2)) :

    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*U)+DU*(B+1)*E^2*M^2/(4*N^4*U)
    let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*U)+(4*DL*(B+1)*R^4)/(4*N^2*U)
    let AupperConst := 2*CU*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := CU*(Cthird+1)*E^2/Lunit^2+DU*(B+1)*E^2/4
    let AlowerConst := 8*CL*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*CL*(Cthird+1)/Lunit^2+DL*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/(N^4*U)
    let CostLower := R^4/(N^2*U)
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    (mass ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) →
      (mass=0 ∨ 1 ≤ DupperCut) →
      mass ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2))) ∧
    (mass ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) →
      (mass=0 ∨ 1 ≤ DlowerCut) →
      mass ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2))) := by
  intro lambda Uband Aupper Bupper Alower Blower AupperConst BupperConst
    AlowerConst BlowerConst DupperConst DlowerConst CostUpper CostLower DupperCut DlowerCut
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 ≤ Uband := by dsimp only [Uband]; positivity
  have hAU : 0 ≤ AupperConst := by dsimp only [AupperConst]; positivity
  have hBU : 0 ≤ BupperConst := by dsimp only [BupperConst]; positivity
  have hAL : 0 ≤ AlowerConst := by dsimp only [AlowerConst]; positivity
  have hBL : 0 ≤ BlowerConst := by dsimp only [BlowerConst]; positivity
  have hDUc : 0 ≤ DupperConst := by dsimp only [DupperConst]; positivity
  have hDLc : 0 ≤ DlowerConst := by dsimp only [DlowerConst]; positivity
  have hCostU : 0 ≤ CostUpper := by dsimp only [CostUpper]; positivity
  have hCostL : 0 ≤ CostLower := by dsimp only [CostLower]; positivity
  have hphysical := triangular_physical_regime_costs hM hN hRpos hUp hLregime hRN
    hselected hregime
  have hid :
      Aupper=AupperConst*(M^2/N^4) ∧
      Bupper=BupperConst*CostUpper ∧
      Alower=AlowerConst*(R^4/N^2) ∧
      Blower=BlowerConst*CostLower ∧
      DupperCut=DupperConst*(M/(N*R^2)) ∧
      DlowerCut=DlowerConst*(N*R^2/M) :=
    triangular_source_weight_scale_identities
      (U:=U) (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (κ:=κ)
      (Lunit:=Lunit) (E:=E) (θ:=θ) (CU:=CU) (CL:=CL) (DU:=DU) (DL:=DL)
      (Cthird:=Cthird) (B:=B) hM hN hRpos hT hscale
  constructor
  · intro hraw hnonempty
    rcases hnonempty with hzero | hDcut
    · rw [hzero]
      have hDcut0 : 0 ≤ DupperCut := by dsimp only [DupperCut]; positivity
      have hlog : 0 ≤ Real.log (DupperCut+2) :=
        Real.log_nonneg (by linarith only [hDcut0])
      positivity
    ·
      have hw := triangular_weight_regime_absorption (Bconst:=BupperConst)
        hAU hDUc (by positivity : (0:ℝ) ≤ M^2/N^4)
        (by positivity : (0:ℝ) ≤ M/(N*R^2))
        hCostU hLregime
        (by rw [←hid.2.2.2.2.1]; exact hDcut) hphysical.1 hphysical.2.2.1
      rw [←hid.1,←hid.2.1,←hid.2.2.2.2.1] at hw
      calc
        _ ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
            2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1))) := hraw
        _ ≤ 60*(4*(m0:ℝ)*(CostUpper*
            (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
              2*BupperConst*(3+2*Real.log (DupperCut+2))+
              (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (by norm_num)
        _ = _ := by ring
  · intro hraw hnonempty
    rcases hnonempty with hzero | hDcut
    · rw [hzero]
      have hDcut0 : 0 ≤ DlowerCut := by dsimp only [DlowerCut]; positivity
      have hlog : 0 ≤ Real.log (DlowerCut+2) :=
        Real.log_nonneg (by linarith only [hDcut0])
      positivity
    ·
      have hw := triangular_weight_regime_absorption (Bconst:=BlowerConst)
        hAL hDLc (by positivity : (0:ℝ) ≤ R^4/N^2)
        (by positivity : (0:ℝ) ≤ N*R^2/M)
        hCostL hLregime
        (by rw [←hid.2.2.2.2.2]; exact hDcut) hphysical.2.1 hphysical.2.2.2
      rw [←hid.2.2.1,←hid.2.2.2.1,←hid.2.2.2.2.2] at hw
      calc
        _ ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
            2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1))) := hraw
        _ ≤ 60*(4*(m0:ℝ)*(CostLower*
            (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
              2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
              (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (by norm_num)
        _ = _ := by ring

/-- The actual original Fourier pairs satisfy the triangular source-regime
bound. The SAME physical scale absorbs both cubic-root and short-family
terms; source curvature, translation cutoffs and pair multiplicities are
derived, and the logarithmic/budget losses remain explicit. -/
theorem positive_difference_actual_fourier_triangular_original_source_regime_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Lregime : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    0 ≤ Lregime →
    (N:ℝ)^4 ≤ M*R^3*Lregime^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2))) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_triangular_original_source_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E Lregime chartKey Uref Refs Gaps Bselect P entry Mat gap
    Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    σ δ T M R base Bcut θ A W x
    hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hLregime hregime
    lambda Uband yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst CostUpper CostLower DupperCut DlowerCut
  let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*(N:ℝ)^4)
  let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*(N:ℝ)^4*(Uref:ℝ))+
    DU*(B+1)*E^2*M^2/(4*(N:ℝ)^4*(Uref:ℝ))
  let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*(N:ℝ)^2)
  let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*(N:ℝ)^2*(Uref:ℝ))+
    (4*DL*(B+1)*R^4)/(4*(N:ℝ)^2*(Uref:ℝ))
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hE : 0 < E := (mul_pos_iff_of_pos_right hT).mp (hTsrc.trans_le hsourceScale)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 ≤ Uband := by dsimp only [Uband]; positivity
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hmodel₀ := approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl
  have hband := positive_difference_model_normalized_curvature_band Fsrc
    hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hya
    hTsrc hT hM hσ hδ hsourceScale hreg hjets htests hmodel₀
  have hcurv ij (hij : ij∈P) i :
      lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband := by
    have hyi : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
    have hxi := hx ij hij i
    have hpoint : (A i:ℝ)+x ij i∈Icc M (2*M) :=
      ⟨by linarith only [hA i,hxi.1],by linarith only [hW i,hxi.2]⟩
    rw [←hlevel ij hij i,hjet]
    exact hband (yp i) hyi _ hpoint
  have hraw :
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Aupper^((3:ℝ)⁻¹)*(DupperCut+2)^((2:ℝ)/3)+
        2*Bupper*(3+2*Real.log (DupperCut+2))+(1/2:ℝ)*(2*DupperCut+1)))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 60*(4*(m0:ℝ)*(3*Alower^((3:ℝ)⁻¹)*(DlowerCut+2)^((2:ℝ)/3)+
        2*Blower*(3+2*Real.log (DlowerCut+2))+(1/2:ℝ)*(2*DlowerCut+1)))) := by
    exact hmassFn Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps (Bselect:=Bselect)
      P entry Mat gap Bmajor Cmajor N za zb AlenA AlenB Za Zb Q K₀
      rat vinv parity anchor e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
      (θ:=θ) A (W:=W) (x:=x)
      hMat hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
      hentry hbase hxa hxb hgapMem hgeometryA hgeometryB hchartColor
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden
      hθ hθmax hinv hchart horientation hBcut hs hrefSet hparentSet hsep
      hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth
      hRQ hselectedUpper hscaleTen hfamilyGap hgap
      hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
      hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor
  
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  obtain ⟨hBnonneg,hCthird⟩ := physical_source_triangular_constants_nonneg hσ
    (approximateModelPhase_tolerance_nonneg (hF 0))
  have hBselOne : 1 ≤ Bselect := by
    have hh : 0 ≤ 168/modelPhaseThirdLower σ := by positivity
    linarith only [hBselectSize,hh]
  have hselected : (Uref:ℝ) ≤ ((N:ℝ)/R)^((2:ℝ)/3) := by
    calc
      _ ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect := hselectedUpper
      _ ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3) :=
        div_le_self (by positivity) hBselOne
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left hN.le hRpos hRQ) (by norm_num)
  have hassembly := triangular_original_mass_regime_assembly m0
    (mass:=(P.card:ℝ)) hM hN hRpos hUp hT hσsrc hcsrc hUsrc hκ hLunit hE.le hθ.le
    hCU.le hCL.le hDU.le hDL.le hCthird hBnonneg hLregime hRN hscale hselected hregime
  have hcuts ij (hij : ij∈P) :
      ((Mat (entry ij) 0=1 ∧ Mat (entry ij) 2=0 ∧ Mat (entry ij) 3=1) →
        |(Mat (entry ij) 1:ℝ)| ≤ DupperCut) ∧
      ((Mat (entry ij) 0=1 ∧ Mat (entry ij) 1=0 ∧ Mat (entry ij) 3=1) →
        |(Mat (entry ij) 2:ℝ)| ≤ DlowerCut) :=
    rational_narrow_triangular_translation_bounds (rat ij) (Mat (entry ij)) Q
      hQ hlambda hUband hθ (hcurv ij hij) (hden ij hij)
      (hsourceColor ij hij) (hMatt ij hij) (hMatmap ij hij)
  constructor
  · intro htri
    apply hassembly.1 (hraw.1 htri)
    by_cases hne : P.Nonempty
    · obtain ⟨ij,hij⟩ := hne
      have hsides := htri (entry ij) (Finset.mem_image_of_mem entry hij)
      have hcut := (hcuts ij hij).1 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      rw [hsides.2.2.2] at hcut
      have hone : (1:ℝ) ≤ |(entry ij:ℝ)| := by exact_mod_cast Int.one_le_abs (hentry ij hij)
      exact Or.inr (hone.trans hcut)
    · exact Or.inl (by simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero])
  · intro htri
    apply hassembly.2 (hraw.2 htri)
    by_cases hne : P.Nonempty
    · obtain ⟨ij,hij⟩ := hne
      have hsides := htri (entry ij) (Finset.mem_image_of_mem entry hij)
      have hcut := (hcuts ij hij).2 ⟨hsides.1,hsides.2.1,hsides.2.2.1⟩
      rw [hsides.2.2.2] at hcut
      have hone : (1:ℝ) ≤ |(entry ij:ℝ)| := by exact_mod_cast Int.one_le_abs (hentry ij hij)
      exact Or.inr (hone.trans hcut)
    · exact Or.inl (by simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero])

end HuxleyTriangularPairScratch
example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E Lregime : ℝ) (chartKey : ℤ → ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (entry : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (Mat : ℤ → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ) (Bmajor Cmajor : ℕ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M R base Bcut θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ} {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    Function.Injective Mat →
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, entry ij≠0) →
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    0 ≤ Lregime →
    (N:ℝ)^4 ≤ M*R^3*Lregime^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey (entry ij)) →
    (0 < σ) →
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
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
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
    (∀ t∈P.image entry, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat (entry ij) 0:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 1)/
      ((Mat (entry ij) 2:ℝ)*(rat ij 0:ℝ)+Mat (entry ij) 3)=(rat ij 1:ℝ)) →
    (∀ t∈P.image entry, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
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
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let DupperCut := θ*Uband
    let DlowerCut := θ/lambda
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 2=0 ∧ Mat t 3=1 ∧ Mat t 1=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostUpper*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BupperConst*(3+2*Real.log (DupperCut+2))+
          (3/2:ℝ)*DupperConst*Lregime^((3:ℝ)/2))) ∧
    ((∀ t∈P.image entry, Mat t 0=1 ∧ Mat t 1=0 ∧ Mat t 3=1 ∧ Mat t 2=t) →
      (P.card:ℝ) ≤ 240*(m0:ℝ)*CostLower*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)*Lregime+
          2*BlowerConst*(3+2*Real.log (DlowerCut+2))+
          (3/2:ℝ)*DlowerConst*Lregime^((3:ℝ)/2))) :=
  HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_source_regime_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc



#print axioms HuxleyTriangularPairScratch.physicalModelPhase_reference_translation_window_selection
#print axioms HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_pair_mass
#print axioms HuxleyTriangularPairScratch.positive_difference_approximate_model_source_amplitude
#print axioms HuxleyTriangularPairScratch.positive_difference_model_normalized_curvature_band
#print axioms HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_source_mass
#print axioms HuxleyTriangularPairScratch.positive_difference_actual_fourier_triangular_original_source_regime_mass
#print axioms HuxleyTriangularPairScratch.triangular_original_mass_regime_assembly
