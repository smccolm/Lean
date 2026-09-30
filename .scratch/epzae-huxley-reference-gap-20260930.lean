import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyReferenceGapScratch

/-- The actual physical cubic coefficient and an endpoint of a constructed
reference gap imply source cutoff (6.6). Both reference orientations are
allowed. The coordinate cutoff itself is not assumed. -/
theorem physicalModelPhase_reference_gap_minorArc_cutoff
    {σ δ T M A W xref N R U B Bcut a b e r v s l : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hxref : xref ∈ Ioo (1/2:ℝ) (W-1/2))
    (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hB : 0 < B) (hBcut : 0 < Bcut)
    (hscale : T*N*R^2=M^3)
    (hmargin : 7*Bcut ≤ modelPhaseThirdLower σ*B)
    (hr : r ≠ 0) (hchart : r*l+s ≠ 0) (hdet : v*r-e*s=1)
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hden : R^2 ≤ r^2*U) (hwrap : B^2*U^3*R^2 ≤ N^2)
    (hpoint : (e*l+v)/(r*l+s) ∈ Icc a b) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f xref/2=e/r →
    (iteratedDeriv 2 f xref/2=a ∨ iteratedDeriv 2 f xref/2=b) →
    |minorArcCoordinate (iteratedDeriv 3 f (round xref)/6) r s l| ≤
      |r| *N^2/(Bcut*R^2) := by
  intro f hbase hendpoint
  let κ := modelPhaseThirdLower σ
  let μ := iteratedDeriv 3 f (round xref)/6
  let G := minorArcCoordinate μ r s l
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hround := (physicalModelPhase_halfCurvature_round_error hσ.le
    hF hT hM hA hW hxref).1
  have hsource := physicalModelPhase_cubicCoefficient_source_scale
    hσ hδ hF hT hM hA hW hround hN hR hscale
  have hμ : 0 < μ := hsource.1
  have hlower : κ ≤ 6*μ*N*R^2 := by
    have hh := mul_le_mul_of_nonneg_left hsource.2.1 hκ.le
    change κ*1 ≤ κ*((6/κ)*μ*N*R^2) at hh
    have he : κ*((6/κ)*μ*N*R^2)=6*μ*N*R^2 := by field_simp
    simpa only [he,mul_one] using hh
  have hid : (e*l+v)/(r*l+s)-e/r=3*μ*G := by
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (μ:=μ) (u:=l) (t:=1)
        hμ.ne' hr (by norm_num) (by simpa only [mul_one] using hchart) hdet)
  have hdistance : |(e*l+v)/(r*l+s)-e/r| ≤ b-a := by
    rw [hbase] at hendpoint
    rcases hendpoint with ha | hb
    · rw [ha,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [hb,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hupper : (3*μ*|G|)*(2*R^2) ≤ 7*U := by
    have hh := hdistance.trans hgap
    rw [hid,abs_mul,abs_of_pos (mul_pos (by norm_num) hμ)] at hh
    exact (le_div_iff₀ (by positivity)).mp hh
  have hwidth : |G| ≤ 7*U*N/κ := by
    apply (le_div_iff₀ hκ).mpr
    have hlo := mul_le_mul_of_nonneg_right hlower (abs_nonneg G)
    have hhi := mul_le_mul_of_nonneg_right hupper hN.le
    nlinarith only [hlo,hhi]
  have hsq : (B*U*R^2)^2 ≤ (|r| *N)^2 := by
    calc
      _ = (B^2*U^2*R^2)*R^2 := by ring
      _ ≤ (B^2*U^2*R^2)*(r^2*U) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = r^2*(B^2*U^3*R^2) := by ring
      _ ≤ r^2*N^2 := mul_le_mul_of_nonneg_left hwrap (sq_nonneg r)
      _ = _ := by rw [mul_pow,sq_abs]
  have hnowrap : B*U*R^2 ≤ |r| *N :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hmargin' : 7/κ ≤ B/Bcut := by
    apply (div_le_div_iff₀ hκ hBcut).mpr
    nlinarith only [hmargin]
  have hwide : |G| ≤ (B/Bcut)*U*N := by
    calc
      _ ≤ 7*U*N/κ := hwidth
      _ = (7/κ)*U*N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmargin' hU) hN.le
  change |G| ≤ |r| *N^2/(Bcut*R^2)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ ((B/Bcut)*U*N)*(Bcut*R^2) :=
      mul_le_mul_of_nonneg_right hwide (by positivity)
    _ = (B*U*R^2)*N := by field_simp
    _ ≤ (|r| *N)*N := mul_le_mul_of_nonneg_right hnowrap hN.le
    _ = _ := by ring

#print axioms physicalModelPhase_reference_gap_minorArc_cutoff


/-- Two actual dyadic-denominator matrix-related phase points in one
reference gap have a derived physical displacement in BOTH phases.
The second phase uses the determinant-one identity and both actual
denominator ratios; no physical displacement bound is supplied. -/
theorem physicalModelPhase_actual_matrix_gap_displacement
    (Q : ℕ) (rat₀ rat₁ : Fin 2 → ℚ) (Mat : Fin 4 → ℤ)
    {σ δ T M N R U a b : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo 0 (W i)) (hx₁ : ∀ i, x₁ i∈Ioo 0 (W i))
    (hscale : T*N*R^2=M^3)
    (hden₀ : ∀ i, (rat₀ i).den ≤ Q ∧ Q ≤ 2*(rat₀ i).den)
    (hden₁ : ∀ i, (rat₁ i).den ≤ Q ∧ Q ≤ 2*(rat₁ i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (ht₀ : (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3=((rat₀ 1).den:ℝ)/(rat₀ 0).den)
    (ht₁ : (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3=((rat₁ 1).den:ℝ)/(rat₁ 0).den)
    (hmap₀ : ((Mat 0:ℝ)*(rat₀ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3)=(rat₀ 1:ℝ))
    (hmap₁ : ((Mat 0:ℝ)*(rat₁ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3)=(rat₁ 1:ℝ))
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hgap₀ : (rat₀ 0:ℝ)∈Icc a b) (hgap₁ : (rat₁ 0:ℝ)∈Icc a b) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat₀ i:ℝ)) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(rat₁ i:ℝ)) →
    ∀ i, |x₁ i-x₀ i| ≤ 28*U*N/modelPhaseThirdLower σ := by
  intro f hlevel₀ hlevel₁
  let κ := modelPhaseThirdLower σ
  let D := 7*U/(2*R^2)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have htlo (rat : Fin 2 → ℚ)
      (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
      (1/2:ℝ) ≤ ((rat 1).den:ℝ)/(rat 0).den := by
    apply (le_div_iff₀ (by exact_mod_cast (rat 0).pos)).mpr
    have hh : ((rat 0).den:ℝ) ≤ 2*(rat 1).den := by
      exact_mod_cast (hden 0).1.trans (hden 1).2
    linarith only [hh]
  have hlow₀ : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3 := by
    rw [ht₀]; exact htlo rat₀ hden₀
  have hlow₁ : (1/2:ℝ) ≤ (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3 := by
    rw [ht₁]; exact htlo rat₁ hden₁
  have hpos₀ : 0 < (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3 := by linarith only [hlow₀]
  have hpos₁ : 0 < (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3 := by linarith only [hlow₁]
  have hcurv₀ : |(rat₁ 0:ℝ)-(rat₀ 0:ℝ)| ≤ D := by
    apply le_trans _ hgap
    apply abs_le.mpr
    constructor <;> linarith only [hgap₀.1,hgap₀.2,hgap₁.1,hgap₁.2]
  have hcurv₁ : |(rat₁ 1:ℝ)-(rat₀ 1:ℝ)| ≤ 4*D := by
    have hdetR : (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet
    have hid : (rat₁ 1:ℝ)-(rat₀ 1:ℝ)=
        ((rat₁ 0:ℝ)-(rat₀ 0:ℝ))/
        (((Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3)*((Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3)) := by
      rw [←hmap₁,←hmap₀,div_sub_div _ _ hpos₁.ne' hpos₀.ne']
      congr 1
      linear_combination ((rat₁ 0:ℝ)-(rat₀ 0:ℝ))*hdetR
    rw [hid,abs_div,abs_of_pos (mul_pos hpos₁ hpos₀)]
    apply (div_le_iff₀ (mul_pos hpos₁ hpos₀)).mpr
    have hprod := mul_le_mul hlow₁ hlow₀ (by norm_num : (0:ℝ) ≤ 1/2) hpos₁.le
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4*D by positivity)
    nlinarith only [hcurv₀,hh]
  have hcoef : κ*T/(2*M^3)=κ/(2*N*R^2) := by
    rw [←hscale]
    field_simp
  intro i
  have hgrowth : κ/(2*N*R^2)*|x₁ i-x₀ i| ≤ |(rat₁ i:ℝ)-(rat₀ i:ℝ)| := by
    rcases le_total (x₀ i) (x₁ i) with hle | hle
    · have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i)
        hT hM (hA i) (hW i) (hx₀ i) (hx₁ i) hle
      change κ*T/(2*M^3)*(x₁ i-x₀ i) ≤ _ at hh
      rw [hcoef,hlevel₀ i,hlevel₁ i] at hh
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hh.trans (le_abs_self _)
    · have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF i)
        hT hM (hA i) (hW i) (hx₁ i) (hx₀ i) hle
      change κ*T/(2*M^3)*(x₀ i-x₁ i) ≤ _ at hh
      rw [hcoef,hlevel₀ i,hlevel₁ i] at hh
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hle),abs_sub_comm (rat₁ i:ℝ)]
      exact hh.trans (le_abs_self _)
  have hcurv : |(rat₁ i:ℝ)-(rat₀ i:ℝ)| ≤ 4*D := by
    fin_cases i
    · exact hcurv₀.trans (by linarith only [hD])
    · exact hcurv₁
  have hh := mul_le_mul_of_nonneg_left (hgrowth.trans hcurv)
    (show 0 ≤ 2*N*R^2 by positivity)
  have he : (2*N*R^2)*(κ/(2*N*R^2)*|x₁ i-x₀ i|)=κ*|x₁ i-x₀ i| := by field_simp
  rw [he] at hh
  apply (le_div_iff₀ hκ).mpr
  have he' : (2*N*R^2)*(4*D)=28*U*N := by dsimp only [D]; field_simp; ring
  rw [he'] at hh
  nlinarith only [hh]


#print axioms physicalModelPhase_actual_matrix_gap_displacement

/-- The actual reference-gap family count derives the global physical
displacements, padded square Taylor budgets and source coordinate cutoff
at the SAME selected U and constructed reference under N^10 <= M^3 R^7.
Sector/chart, density and boundary-buffer requirements remain explicit. -/
theorem physicalModelPhase_actual_fourier_selected_reference_gap_count
    (Uref : ℕ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
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
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    48+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 48+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
 classical
  intro Lref
  have hκearly : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hUone : (1:ℝ) ≤ Uref := by exact_mod_cast hUref
  have hUp : (0:ℝ) < Uref := zero_lt_one.trans_le hUone
  have hBtwo : 2 ≤ Bselect := by
    have hp : 0 < 168/modelPhaseThirdLower σ := by positivity
    linarith only [hBselectSize,hp]
  have hBselect : 0 < Bselect := lt_of_lt_of_le (by norm_num) hBtwo
  have hLref : 0 < Lref := by dsimp only [Lref]; positivity
  have hspanMargin :
      2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ+2 ≤ Bselect*(Uref:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hBselectSize hUp.le
    have he : (2+168/modelPhaseThirdLower σ)*(Uref:ℝ)=
        2*(Uref:ℝ)+2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ := by
      dsimp only [Lref]
      ring
    rw [he] at hh
    linarith only [hh,hUone]
  have hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2 := by
    have hBsq : (4:ℝ) ≤ Bselect^2 := by nlinarith only [hBtwo]
    have hUsq : (1:ℝ) ≤ (Uref:ℝ)^2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hUone 2
    have hUcube : (Uref:ℝ) ≤ (Uref:ℝ)^3 := by
      have hh := mul_le_mul_of_nonneg_right hUsq hUp.le
      nlinarith only [hh]
    have hscaled : 4*(Uref:ℝ)*R^2 ≤ N^2 := by
      apply le_trans _ hselectedWrap
      calc
        _ ≤ Bselect^2*(Uref:ℝ)*R^2 := by gcongr
        _ ≤ Bselect^2*(Uref:ℝ)^3*R^2 := by gcongr
    have he : modelPhaseThirdLower σ*Lref*R^2=56*(Uref:ℝ)*R^2 := by
      dsimp only [Lref]
      field_simp
    rw [he]
    nlinarith only [hscaled,sq_nonneg N]
  have hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤
      modelPhaseThirdLower σ*Lref/(16*R^2) := by
    have hinside := hfamilyGap jref hjref
    have hdist : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ gapHi-gapLo := by
      rcases hreferenceEndpoint with he | he
      · rw [he,abs_of_nonpos (sub_nonpos.mpr hinside.1)]
        linarith only [hinside.2]
      · rw [he,abs_of_nonneg (sub_nonneg.mpr hinside.2)]
        linarith only [hinside.1]
    apply (hdist.trans hgapWidth).trans
    apply le_of_eq
    dsimp only [Lref]
    field_simp
    ring
  let nSpan := Bselect*(Uref:ℝ)*N
  have hsourcesquare : nSpan^2 ≤ M*R :=
    source_selected_reference_square_span_budget Uref hM hN (zero_lt_one.trans_le hR)
      hRQ hBselect hselectedUpper hscaleTen
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_height_square_span_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
  clear hlong
  refine ⟨xref,hxr,?_⟩
  intro Ccurv Ctay D η Kres hD hΔ hdenregion hends hsector hBsize
  let G := minorArcCoordinate (iteratedDeriv 3 (f 0) (round (xref 0))/6) (rp 0) (sp 0)
  have hlw : l ≤ w := (hends jref hjref).1.1.trans (hends jref hjref).1.2
  have hchartLeftPos : 0 < (r:ℝ)*l+s :=
    hd.trans_le (hdenregion l ⟨le_rfl,hlw⟩ 0).1
  have hbase : iteratedDeriv 2 (f 0) (xref 0)/2=(e:ℝ)/r := (hxr 0).2.2.1
  have hGcut : |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) := by
    exact physicalModelPhase_reference_gap_minorArc_cutoff hσ hδ
      (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM (hA 0) (hW 0) (hxr 0).2.1 hN (zero_lt_one.trans_le hR)
      (Nat.cast_nonneg Uref) hBselect hBcut hscale hcutMargin
      (by exact_mod_cast hr) hchartLeftPos.ne' (by exact_mod_cast hchart)
      hgapWidth hreferenceDen hselectedWrap hchartLeft hbase
      (by rw [hbase]; exact hreferenceEndpoint)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hpair (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-x jref i| ≤ 28*(Uref:ℝ)*N/κ := by
    exact physicalModelPhase_actual_matrix_gap_displacement Q (rat jref) (rat j) Mat
      hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM hN (zero_lt_one.trans_le hR) (Nat.cast_nonneg Uref) hA hW
      (fun i => ⟨by linarith only [(hx jref hjref i).1],
        by linarith only [(hx jref hjref i).2]⟩)
      (fun i => ⟨by linarith only [(hx j hj i).1],
        by linarith only [(hx j hj i).2]⟩)
      hscale (hden jref hjref) (hden j hj) hMatdet
      (hMatt jref hjref) (hMatt j hj) (hMatmap jref hjref) (hMatmap j hj)
      hgapWidth (hfamilyGap jref hjref) (hfamilyGap j hj)
      (hlevel jref hjref) (hlevel j hj) i
  let span := (Lref+28*(Uref:ℝ)/κ)*N
  have hspan0 : 0 ≤ span := by dsimp only [span]; positivity
  have hdisplacement (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-xref i| ≤ span := by
    calc
      _ ≤ |x j i-x jref i|+|x jref i-xref i| := abs_sub_le _ _ _
      _ ≤ 28*(Uref:ℝ)*N/κ+Lref*N := by
        apply add_le_add (hpair j hj i)
        rw [abs_sub_comm]
        exact (hxr i).2.2.2.1
      _ = span := by dsimp only [span]; ring
  have hspanBuffer : 2*span+2*N ≤ nSpan := by
    have hh := mul_le_mul_of_nonneg_right hspanMargin hN.le
    change (2*Lref+56*(Uref:ℝ)/κ+2)*N ≤ nSpan at hh
    have he : (2*Lref+56*(Uref:ℝ)/κ+2)*N=2*span+2*N := by
      dsimp only [span]
      ring
    rwa [he] at hh
  have hspan : 2*span+1 ≤ nSpan := by
    linarith only [hspanBuffer,hNtwo]
  have hHN : H ≤ N := by
    apply (div_le_iff₀ (show 0 < Cphys+2 by dsimp only [Cphys]; positivity)).mpr
    have hh : 1 ≤ Cphys+2 := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hh hN.le
  have hbudget (j : ℕ) (hj : j∈S) (i : Fin 2) :
      (H+|x j i-xref i|+1)^2 ≤ M*R := by
    have hH0 : 0 ≤ H := by dsimp only [H,Cphys]; positivity
    have hb : H+|x j i-xref i|+1 ≤ nSpan := by
      linarith only [hdisplacement j hj i,hspanBuffer,hHN,hspan0,hNtwo]
    exact (pow_le_pow_left₀ (by positivity) hb 2).trans hsourcesquare
  exact hconsumer (fun _ => span) hdisplacement (fun _ => hspan)
    hbudget hD hΔ hdenregion hends hsector hBsize hGcut


#print axioms physicalModelPhase_actual_fourier_selected_reference_gap_count

example
    {σ δ T M A W xref N R U B Bcut a b e r v s l : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hxref : xref ∈ Ioo (1/2:ℝ) (W-1/2))
    (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hB : 0 < B) (hBcut : 0 < Bcut)
    (hscale : T*N*R^2=M^3)
    (hmargin : 7*Bcut ≤ modelPhaseThirdLower σ*B)
    (hr : r ≠ 0) (hchart : r*l+s ≠ 0) (hdet : v*r-e*s=1)
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hden : R^2 ≤ r^2*U) (hwrap : B^2*U^3*R^2 ≤ N^2)
    (hpoint : (e*l+v)/(r*l+s) ∈ Icc a b) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f xref/2=e/r →
    (iteratedDeriv 2 f xref/2=a ∨ iteratedDeriv 2 f xref/2=b) →
    |minorArcCoordinate (iteratedDeriv 3 f (round xref)/6) r s l| ≤
      |r| *N^2/(Bcut*R^2) :=
  HuxleyReferenceGapScratch.physicalModelPhase_reference_gap_minorArc_cutoff (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (xref:=xref) (N:=N) (R:=R) (U:=U) (B:=B) (Bcut:=Bcut) (a:=a) (b:=b) (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (F:=F) hσ hδ hF hT hM hA hW hxref hN hR hU hB hBcut hscale hmargin hr hchart hdet hgap hden hwrap hpoint

example
    (Q : ℕ) (rat₀ rat₁ : Fin 2 → ℚ) (Mat : Fin 4 → ℤ)
    {σ δ T M N R U a b : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 ≤ U)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo 0 (W i)) (hx₁ : ∀ i, x₁ i∈Ioo 0 (W i))
    (hscale : T*N*R^2=M^3)
    (hden₀ : ∀ i, (rat₀ i).den ≤ Q ∧ Q ≤ 2*(rat₀ i).den)
    (hden₁ : ∀ i, (rat₁ i).den ≤ Q ∧ Q ≤ 2*(rat₁ i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (ht₀ : (Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3=((rat₀ 1).den:ℝ)/(rat₀ 0).den)
    (ht₁ : (Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3=((rat₁ 1).den:ℝ)/(rat₁ 0).den)
    (hmap₀ : ((Mat 0:ℝ)*(rat₀ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₀ 0:ℝ)+Mat 3)=(rat₀ 1:ℝ))
    (hmap₁ : ((Mat 0:ℝ)*(rat₁ 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat₁ 0:ℝ)+Mat 3)=(rat₁ 1:ℝ))
    (hgap : b-a ≤ 7*U/(2*R^2))
    (hgap₀ : (rat₀ 0:ℝ)∈Icc a b) (hgap₁ : (rat₁ 0:ℝ)∈Icc a b) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat₀ i:ℝ)) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(rat₁ i:ℝ)) →
    ∀ i, |x₁ i-x₀ i| ≤ 28*U*N/modelPhaseThirdLower σ :=
  HuxleyReferenceGapScratch.physicalModelPhase_actual_matrix_gap_displacement Q rat₀ rat₁ Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (a:=a) (b:=b) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (x₁:=x₁) hσ hδ hF hT hM hN hR hU hA hW hx₀ hx₁ hscale hden₀ hden₁ hdet ht₀ ht₁ hmap₀ hmap₁ hgap hgap₀ hgap₁

example
    (Uref : ℕ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
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
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    48+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 48+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyReferenceGapScratch.physicalModelPhase_actual_fourier_selected_reference_gap_count Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap


end HuxleyReferenceGapScratch
