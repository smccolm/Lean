import TaoTrudgianYang2025.HuxleyLinearForms
open Set
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff FourierTransform BigOperators
namespace HuxleyLongReferenceScratch

private theorem reference_gap_count_of_profile_width
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Ioo ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  classical
  by_cases hG : G.Nonempty
  · let Values := G.image p
    have hv : Values.Nonempty := Finset.Nonempty.image hG p
    let lo := Values.min' hv
    let hi := Values.max' hv
    obtain ⟨ab,hab,hablo⟩ := Finset.mem_image.mp (Finset.min'_mem Values hv)
    obtain ⟨cd,hcd,hcdhi⟩ := Finset.mem_image.mp (Finset.max'_mem Values hv)
    have hbounds g (hg : g∈G) : lo ≤ p g ∧ p g ≤ hi :=
      ⟨Finset.min'_le Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),
        Finset.le_max' Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)⟩
    have hlohi : lo ≤ hi := (hbounds ab hab).1.trans (hbounds ab hab).2
    have hspan : hi-lo ≤ D := by
      change Values.max' hv-Values.min' hv ≤ D
      rw [←hablo,←hcdhi]
      exact (abs_le.mp (hwidth ab hab cd hcd)).2
    have hc := adjacent_reference_gap_card S G hd hlohi hsep hgap (by
      intro g hg
      exact ⟨(hpoint g hg).1.trans_le (hbounds g hg).2,
        (hbounds g hg).1.trans_lt (hpoint g hg).2⟩)
    exact hc.trans (add_le_add (div_le_div_of_nonneg_right hspan hd.le) le_rfl)
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity


private theorem paired_large_entry_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x y : ℝ × ℝ → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M R U Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T)
    (hM : 0 < M) (hR : 0 < R) (hU : 0 < U) (hΔ : 0 ≤ Δ)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ z∈Refs, ¬(ab.1 < z ∧ z < ab.2))
    (hx : ∀ ab∈Gaps, x ab∈Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ ab∈Gaps, y ab∈Ioo (1/2:ℝ) (W 1-1/2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let p := fun ab => iteratedDeriv 2 (f 0) (x ab)/2
    let mu := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun ab => (Mat 2:ℝ)*p ab+Mat 3
    (∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*p ab+Mat 1)/t ab=iteratedDeriv 2 (f 1) (y ab)/2) →
    (∀ ab∈Gaps, t ab∈Icc (1/2:ℝ) 2) →
    (∀ ab∈Gaps, |mu 1 (y ab)*(t ab)^3/mu 0 (x ab)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let eta := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (Gaps.card:ℝ) ≤ 64*Cphys*(Gamma^2*Δ+2*Gamma*eta)*R^2/
      (κ*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f p mu t hpoint hmap ht hthird κ Cphys Gamma eta
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCp hκ
  have hC₃ : 0 ≤ modelPhaseJetCoefficient σ 3+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hcpos : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  let Width := 16*Cphys*(Gamma^2*Δ+2*Gamma*eta)/(κ*|(Mat 2:ℝ)|)
  have hw0 : 0 ≤ Width := by dsimp only [Width]; positivity
  have hordered ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) (horder : p ab ≤ p cd) :
      p cd-p ab ≤ Width := by
    exact physicalModelPhase_paired_large_entry_curvature_diameter
      ![x ab,x cd] ![y ab,y cd] (Mat 0) (Mat 1) (Mat 2) (Mat 3)
      hσ hδ hδ0 hF hT hτ hM hA hW hΔ hMat hc hlarge
      (by intro i; fin_cases i; exact hx ab hab; exact hx cd hcd)
      (by intro i; fin_cases i; exact hy ab hab; exact hy cd hcd)
      horder
      (by intro i; fin_cases i; exact hmap ab hab; exact hmap cd hcd)
      (by intro i; fin_cases i; exact ht ab hab; exact ht cd hcd)
      (by intro i; fin_cases i; exact hthird ab hab; exact hthird cd hcd)
  have hwidth ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) : |p cd-p ab| ≤ Width := by
    by_cases hle : p ab ≤ p cd
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      exact hordered ab hab cd hcd hle
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))]
      exact hordered cd hcd ab hab (le_of_not_ge hle)
  have hp := reference_gap_count_of_profile_width Refs Gaps p
    (show 0 < U/(4*R^2) by positivity) hw0 hsep hgap hpoint hwidth
  apply hp.trans_eq
  dsimp only [Width]
  field_simp
  ring_nf


private theorem reference_chart_fraction_antitone {e v r s a b : ℝ}
    (hdet : v*r-e*s=1) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hab : a ≤ b) :
    (e*b+v)/(r*b+s) ≤ (e*a+v)/(r*a+s) := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (e*a+v)*(r*b+s)-(e*b+v)*(r*a+s)=b-a := by
    linear_combination (b-a)*hdet
  have hh := sub_nonneg.mpr hab
  rw [←he] at hh
  exact sub_nonneg.mp hh


theorem physicalModelPhase_quartic_long_reference_gap_packing
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R U L K : ℝ} {A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hNL : (L*N)^2 ≤ M*R) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hcurve : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hmono : ∀ ab∈Gaps, StrictMono (x ab))
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    ∃ z : ℝ × ℝ → ℝ,
      (∀ ab∈Gaps, z ab∈Ioo (x ab 0) (x ab 3) ∧ profile ab (z ab)∈Ioo ab.1 ab.2 ∧
        let t := (Mat 2:ℝ)*profile ab (z ab)+Mat 3
        t∈Icc (1/2:ℝ) 2 ∧
        ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t=iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 ∧
        |munew ab (z ab) 1*t^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2)) ∧
      (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro f n mu munew nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres
    κ Cphys Gamma Cthird Cpack
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hGamma : 0 < Gamma := div_pos hCp hκ
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hdenpos ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      0 < Den ab t i := (hd ab hab).trans_le (hden ab hab t ht i).1
  have hex : ∀ ab∈Gaps, ∃ z∈Ioo (x ab 0) (x ab 3),
      |munew ab z 1*(Den ab z 1)^3/(munew ab z 0*(Den ab z 0)^3)-1| ≤ Cthird*R^2/(L^2*N^2) := by
    intro ab hab
    exact physicalModelPhase_quartic_long_block_third_condition (x ab)
      hσ hδ hF hT hM hN hR hL hNL (hd ab hab) hK hA hW
      (href ab hab) (hcurve ab hab) (hr ab hab) (hdet ab hab)
      (fun t ht i => (hden ab hab t ht i).1)
      (fun t ht i => (hden ab hab t ht i).2) (hmono ab hab)
      (hbase ab hab) (hpoint ab hab) (hsquare ab hab) (hspacing ab hab) (hres ab hab)
  choose! z hz hthird using hex
  have hzcc ab (hab : ab∈Gaps) : z ab∈Icc (x ab 0) (x ab 3) := ⟨(hz ab hab).1.le,(hz ab hab).2.le⟩
  have hinside ab (hab : ab∈Gaps) : profile ab (z ab)∈Ioo ab.1 ab.2 := by
    have hx03 : x ab 0 ≤ x ab 3 := (hmono ab hab).monotone (by decide)
    have hx0 : x ab 0∈Icc (x ab 0) (x ab 3) := ⟨le_rfl,hx03⟩
    have hx3 : x ab 3∈Icc (x ab 0) (x ab 3) := ⟨hx03,le_rfl⟩
    have hlow : profile ab (x ab 3) ≤ profile ab (z ab) := by
      dsimp only [profile]
      rw [hpoint ab hab _ hx3 0,hpoint ab hab _ (hzcc ab hab) 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ (hzcc ab hab) 0) (hdenpos ab hab _ hx3 0) (hzcc ab hab).2
    have hhigh : profile ab (z ab) ≤ profile ab (x ab 0) := by
      dsimp only [profile]
      rw [hpoint ab hab _ (hzcc ab hab) 0,hpoint ab hab _ hx0 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ hx0 0) (hdenpos ab hab _ (hzcc ab hab) 0) (hzcc ab hab).1
    exact ⟨(hends ab hab).2.1.trans_le hlow,hhigh.trans_lt (hends ab hab).1.2⟩
  let t := fun ab => (Mat 2:ℝ)*profile ab (z ab)+Mat 3
  have htid ab (hab : ab∈Gaps) : t ab=Den ab (z ab) 1/Den ab (z ab) 0 := by
    change (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 3=_
    rw [hpoint ab hab _ (hzcc ab hab) 0]
    apply (eq_div_iff (hdenpos ab hab _ (hzcc ab hab) 0).ne').mpr
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
    dsimp only [Den]
    rw [(htransport ab hab).2.2.1,(htransport ab hab).2.2.2]
    ring_nf
  have htband ab (hab : ab∈Gaps) : t ab∈Icc (1/2:ℝ) 2 := by
    rw [htid ab hab]
    constructor
    · apply (le_div_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).1,(hden ab hab _ (hzcc ab hab) 0).2]
    · apply (div_le_iff₀ (hdenpos ab hab _ (hzcc ab hab) 0)).mpr
      linarith only [(hden ab hab _ (hzcc ab hab) 1).2,(hden ab hab _ (hzcc ab hab) 0).1]
  have hmap ab (hab : ab∈Gaps) :
      ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t ab=
        iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 := by
    rw [htid ab hab]
    have he : (Mat 0:ℝ)*profile ab (z ab)+Mat 1=
        (e ab 1*z ab+v ab 1)/Den ab (z ab) 0 := by
      change (Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+Mat 1=_
      rw [hpoint ab hab _ (hzcc ab hab) 0]
      apply (eq_div_iff (hdenpos ab hab _ (hzcc ab hab) 0).ne').mpr
      rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
      rw [(htransport ab hab).1,(htransport ab hab).2.1]
      dsimp only [Den]
      ring_nf
    rw [he,div_div_div_cancel_right₀ (hdenpos ab hab _ (hzcc ab hab) 0).ne']
    exact (hpoint ab hab _ (hzcc ab hab) 1).symm
  have hthirdMat ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1*(t ab)^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2) := by
    rw [htid ab hab]
    have he : munew ab (z ab) 1*(Den ab (z ab) 1/Den ab (z ab) 0)^3/munew ab (z ab) 0=
        munew ab (z ab) 1*(Den ab (z ab) 1)^3/(munew ab (z ab) 0*(Den ab (z ab) 0)^3) := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hthird ab hab
  refine ⟨z,fun ab hab => ⟨hz ab hab,hinside ab hab,htband ab hab,hmap ab hab,hthirdMat ab hab⟩,?_⟩
  have hp := paired_large_entry_reference_gap_packing Refs Gaps
    (fun ab => curve ab (z ab) 0) (fun ab => curve ab (z ab) 1) Mat
    hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl)
    hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hRpos hU
    (show 0 ≤ Cthird*R^2/(L^2*N^2) by positivity) hA hW hMat hc hlarge hsep hgap
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 0)
    (fun ab hab => hcurve ab hab _ (hzcc ab hab) 1)
    hinside hmap htband hthirdMat
  have hNL' : L^2*N^2 ≤ M*R^2 := by
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    calc
      L^2*N^2 = (L*N)^2 := by ring_nf
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left hRR hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by simpa only [one_mul,mul_one,mul_comm] using hNL')
  have heta : 2*Gamma*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)) := by
    calc
      _ = (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
  apply hp.trans
  calc
    _ ≤ 64*Cphys*(Gamma^2*(Cthird*R^2/(L^2*N^2))+
        (Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)))*R^2/
          (κ*|(Mat 2:ℝ)| *U)+2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 64*Cphys)
      exact add_le_add le_rfl heta
    _ = Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
      dsimp only [Cpack]
      ring_nf

#print axioms reference_chart_fraction_antitone
#print axioms physicalModelPhase_quartic_long_reference_gap_packing
#print axioms paired_large_entry_reference_gap_packing
#print axioms reference_gap_count_of_profile_width
example
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R U L K : ℝ} {A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hNL : (L*N)^2 ≤ M*R) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hcurve : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hmono : ∀ ab∈Gaps, StrictMono (x ab))
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    ∃ z : ℝ × ℝ → ℝ,
      (∀ ab∈Gaps, z ab∈Ioo (x ab 0) (x ab 3) ∧ profile ab (z ab)∈Ioo ab.1 ab.2 ∧
        let t := (Mat 2:ℝ)*profile ab (z ab)+Mat 3
        t∈Icc (1/2:ℝ) 2 ∧
        ((Mat 0:ℝ)*profile ab (z ab)+Mat 1)/t=iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 ∧
        |munew ab (z ab) 1*t^3/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2)) ∧
      (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 :=
  HuxleyLongReferenceScratch.physicalModelPhase_quartic_long_reference_gap_packing Refs Gaps Mat x xref e r v s curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (L:=L) (K:=K) (A:=A) (W:=W) (F:=F) hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hMat hc hlarge hsep hgap hd href hcurve hr hdet hden hmono htransport

end HuxleyLongReferenceScratch
