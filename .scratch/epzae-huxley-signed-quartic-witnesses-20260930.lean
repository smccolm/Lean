import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff FourierTransform BigOperators
namespace HuxleyQuarticWitnessScratch
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


private theorem physicalModelPhase_signed_height_square_span_quartic_witnesses
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hnsquare : nSpan^2 ≤ M*R)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let K := 4*Cres/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S ∧ z a=y (j a) ∧ ∀ i,
        iteratedDeriv 2 (f i) (x (j a) i)/2=(e i*z a+v i)/(r i*z a+s i)) ∧ StrictMono z ∧
      0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ K ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ r i*t+s i ∧ r i*t+s i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=(e i*t+v i)/(r i*t+s i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8, |alpha*z i+beta-g (z i)+h (z i)| ≤ K*R^2/|r 0*G (z i)|) := by
  classical
  intro U Blabels f μ ν y g h φ G Z κ K L hGcut hpoint hy₀ hy hcurv hres
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hBpos : (0:ℝ) < Blabels := by dsimp [Blabels]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCpos : 0 < σ*(σ+1)+1 := by positivity
  have hL : 0 < L := mul_pos (div_pos hκ (mul_pos (by positivity) hCpos)) hcount
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hxref i)
  have hμbounds i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hround i).1
  have hμpos i : 0 < μ i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hμupper : μ 0 ≤ (σ*(σ+1)+1)/(6*N*R^2) := by
    have hb := (hμbounds 0).2
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (σ*(σ+1)+1)*T/(6*M^3)=(σ*(σ+1)+1)/(6*N*R^2) := by
      rw [hTeq]
      field_simp
    exact hb.trans_eq he
  have hdx (j) (hj : j∈S) : x j 0∈Ioo 0 (W 0) :=
    ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩
  obtain ⟨a,b,j,_hj,hcoeff,hanti,hphys,hG,_hmass,_hantiAll⟩ := physicalModelPhase_signed_height_common_coefficient_samples_with_mass
    (ac:=ac) (bc:=bc) (C:=Ccurv) (J:=σ*(σ+1)+1) (N:=N) (R:=R) (d:=d)
    S p (fun n => x n 0) hS hσ hδ (hF₂ 0) hT hM (hA 0) (hW 0) hN
    (hμpos 0) (hμpos 1).ne' (hr 0) (hr 1) (hdet 0)
    (fun z hz => hden z hz 0) (fun z hz => (hd.trans_le (hden z hz 1).1).ne')
    hCcurv hCpos hN hRpos hd hcoord hμupper hBcut hBsize hGcut
    hP₂ hD₀ hD hheight hpt hdx hwindow (fun n hn => hpoint n hn 0) hy₀ hy hcurv
    (fun n hn => by
      convert hres n hn using 1
      dsimp only [φ]
      congr 1
      ring)
  have hphaseLower : κ/(2*N) ≤ 3*μ 0*R^2 := by
    have hh := mul_le_mul_of_nonneg_right (hμbounds 0).1 (show 0 ≤ 3*R^2 by positivity)
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (κ*T/(6*M^3))*(3*R^2)=κ/(2*N) := by
      rw [hTeq]
      field_simp
      norm_num
    rw [he] at hh
    change κ/(2*N) ≤ μ 0*(3*R^2) at hh
    nlinarith only [hh]
  have hresnorm (n) (hn : n∈S) :
      |(ac-round (ac-deriv φ (y n)))*y n+
        (bc-round (bc-φ (y n)+y n*deriv φ (y n)))-g (y n)+h (y n)| ≤
        K*R^2/|r 0*G (y n)| := by
    exact (hres n hn).trans (quartic_integer_seed_residual_source_normalization (p n)
      (hμpos 0) (hr 0) hκ hN hCres (hpt n hn)
      (hd.trans_le (hden _ (hy n hn).1 0).1) (hQband n hn) hDupper hphaseLower)
  have hH i : 0 ≤ H i := (abs_nonneg _).trans (hdisplacement _ (hcoeff 0).1 i)
  have hsquare i : (H i+1)^2 ≤ M*R := by
    apply (pow_le_pow_left₀ (add_nonneg (hH i) zero_le_one)
      (show H i+1 ≤ nSpan by linarith only [hH i,hspan i]) 2).trans hnsquare
  have hκle : κ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF₂ 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hLspan : L*N ≤ nSpan := by
    have hrati : κ/(σ*(σ+1)+1) ≤ 1 := (div_le_one hCpos).mpr hκle
    have hsmall := mul_le_mul_of_nonneg_right hrati
      (div_pos (mul_pos hN hcount) (by positivity : (0:ℝ)<16*(Blabels:ℝ))).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/(16*(Blabels:ℝ))) := by
      dsimp only [L]
      field_simp
    rw [← he,one_mul] at hsmall
    have hg := hphys (0:Fin 7)
    have hdiff := le_abs_self (x (j (1:Fin 8)) 0-x (j (0:Fin 8)) 0)
    have htri := abs_sub_le (x (j (1:Fin 8)) 0) (xref 0) (x (j (0:Fin 8)) 0)
    rw [abs_sub_comm (xref 0)] at htri
    have hleft := hdisplacement _ (hcoeff (0:Fin 8)).1 0
    have hright := hdisplacement _ (hcoeff (1:Fin 8)).1 0
    change N*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j 1) 0-x (j 0) 0 at hg
    linarith only [hsmall,hg,hdiff,htri,hleft,hright,hspan 0]
  have hNL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2).trans hnsquare
  let z : Fin 8 → ℝ := fun i => y (j i.rev)
  have hmono : StrictMono z := hanti.comp Fin.rev_strictAnti
  have hz (i : Fin 8) : z i∈Icc l w := (hy _ (hcoeff i.rev).1).1
  have hsub : Icc (z 0) (z 7) ⊆ Icc l w :=
    fun q hq => ⟨(hz 0).1.trans hq.1,hq.2.trans (hz 7).2⟩
  have hcoef : κ/(σ*(σ+1)+1) ≤ κ*T/(6*μ 0*M^3) := by
    have hb : 6*μ 0*M^3 ≤ (σ*(σ+1)+1)*T := by
      have hh := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp (hμbounds 0).2
      change μ 0*(6*M^3) ≤ (σ*(σ+1)+1)*T at hh
      nlinarith only [hh]
    apply (div_le_div_iff₀ hCpos
      (mul_pos (mul_pos (by norm_num) (hμpos 0)) (pow_pos hM 3))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb hκ.le]
  have hgap (i : Fin 7) : L*N ≤ |G (z i.succ)-G (z i.castSucc)| := by
    have hh := mul_le_mul_of_nonneg_right hcoef
      (div_pos (mul_pos hN hcount) (by positivity : (0:ℝ) < 16*(Blabels:ℝ))).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/(16*(Blabels:ℝ))) := by
      dsimp only [L]
      field_simp
    rw [he]
    dsimp only [z]
    rw [Fin.rev_succ,Fin.rev_castSucc,abs_sub_comm]
    exact (hh.trans (hG i.rev)).trans (le_abs_self _)
  have hroot (i : Fin 8) (a : Fin 2) :
      iteratedDeriv 2 (f a) (x (j i.rev) a)/2=(e a*z i+v a)/(r a*z i+s a) := by
    rw [hpoint _ (hcoeff i.rev).1 a]
    have ht : ((p (j i.rev)).2:ℝ) ≠ 0 := by
      exact_mod_cast (hpt _ (hcoeff i.rev).1).ne'
    dsimp only [z,y]
    have hn : e a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+v a=
      (e a*(p (j i.rev)).1+v a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    have hd' : r a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+s a=
      (r a*(p (j i.rev)).1+s a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    rw [hn,hd',div_div_div_cancel_right₀ ht]
  have hex (i : Fin 2) := physicalModelPhase_interval_root_family
    (l:=z 0) (w:=z 7) (x₀:=xref i) hσ.le (hF₂ i) hT hM (hA i) (hW i)
    (hx _ (hcoeff (0:Fin 8).rev).1 i) (hx _ (hcoeff (7:Fin 8).rev).1 i)
    (hd.trans_le (hden _ (hz 0) i).1) (hd.trans_le (hden _ (hz 7) i).1)
    (hdisplacement _ (hcoeff (0:Fin 8).rev).1 i)
    (hdisplacement _ (hcoeff (7:Fin 8).rev).1 i)
    (by rw [← hroot 0 i]; exact Set.left_mem_uIcc)
    (by rw [← hroot 7 i]; exact Set.right_mem_uIcc)
  choose ρ hρ _hρdiam using hex
  refine ⟨(fun a => j a.rev),z,(fun q i => ρ i q),ac-a,bc-b,
    (fun a => ⟨(hcoeff a.rev).1,rfl,hroot a⟩),hmono,hL,hNL,hK,?_,hgap,?_⟩
  · intro t ht
    refine ⟨hsub ht,fun i => ⟨(hρ i t ht).2.1,
      (hden t (hsub ht) i).1,(hden t (hsub ht) i).2,(hρ i t ht).2.2.1,?_⟩⟩
    exact (pow_le_pow_left₀ (abs_nonneg _) (hρ i t ht).2.2.2.2 2).trans (hsquare i)
  · intro i
    have hh := hresnorm _ (hcoeff i.rev).1
    rw [(hcoeff i.rev).2.1,(hcoeff i.rev).2.2] at hh
    exact hh

theorem physicalModelPhase_signed_height_square_span_first_condition_reused
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hnsquare : nSpan^2 ≤ M*R)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
  classical
  intro U Blabels f μ ν y g h φ G Z κ K Γ L hGcut hbase hpoint hy₀ hy hcurv hres C Cfirst Csecond
  obtain ⟨_j,z,curve,alpha,beta,_hj,hmono,hL,hNL,hK,hcurve,hgap,hres'⟩ :=
    physicalModelPhase_signed_height_square_span_quartic_witnesses S p x
      hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDupper hscale hA hW hxref
      hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden
      hcoord hP₂ hCcurv hBcut hBsize hGcut hpoint hy₀ hy hcurv hres
  exact physicalModelPhase_quartic_matrix_long_block_first_condition
    (x₁:=curve) (α:=alpha) (β:=beta) z Mat
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hxref
    (fun q hq i => ((hcurve q hq).2 i).1) hr hdet
    (fun q hq i => ((hcurve q hq).2 i).2.1)
    (fun q hq i => ((hcurve q hq).2 i).2.2.1) hmono hscale hMat htransport hbase
    (fun q hq i => ((hcurve q hq).2 i).2.2.2.1)
    (fun q hq i => ((hcurve q hq).2 i).2.2.2.2)
    hgap hres'

/-- Source signed-height occupied windows produce the quartic witnesses used
to pack long reference gaps. The caller supplies the actual samples and their
source residuals, never an improved-Third or gap-count certificate. -/
theorem physicalModelPhase_signed_height_long_reference_gap_packing
    {Kcoord : ℕ}
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (S : ℝ × ℝ → Finset ℕ) (p : ℝ × ℝ → ℕ → ℤ × ℤ)
    (x : ℝ × ℝ → ℕ → Fin 2 → ℝ)
    (xref e r v s H : ℝ × ℝ → Fin 2 → ℝ)
    (d nSpan base l w y₀ ac bc : ℝ × ℝ → ℝ) (k : ℝ × ℝ → Fin 17)
    {σ δ T M N R U L Cres Q D Ccurv Bcut P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hP₂ : 0 < P₂) (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ ab∈Gaps, ∀ j∈S ab, |((p ab j).1:ℝ)| ≤ P₁ ∧ ((p ab j).2:ℝ) ≤ P₂)
    (hpt : ∀ ab∈Gaps, ∀ j∈S ab, 0 < (p ab j).2)
    (hQband : ∀ ab∈Gaps, ∀ j∈S ab, Q ≤ 2*(r ab 0*(p ab j).1+s ab 0*(p ab j).2))
    (hx : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, x ab j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈S ab,
      x ab j 0∈Icc (base ab+N*(j:ℝ)) (base ab+N*((j:ℝ)+1)))
    (hdisplacement : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, |x ab j i-xref ab i| ≤ H ab i)
    (hspan : ∀ ab∈Gaps, ∀ i, 2*H ab i+1 ≤ nSpan ab)
    (hnsquare : ∀ ab∈Gaps, (nSpan ab)^2 ≤ M*R)
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (l ab) (w ab), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hcoord : ∀ ab∈Gaps, |r ab 0| * max |l ab| |w ab| ≤ (Kcoord:ℝ)*d ab)
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let y := fun ab j => ((p ab j).1:ℝ)/(p ab j).2
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let h := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let phi := fun ab t => g ab t-h ab t
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let Vcurv := fun ab => Ccurv*R^4/(N*(d ab)^3)
    let Z := fun ab => quarticCurvatureBoundaryRoots (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1) (Vcurv ab)
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let K := 4*Cres/κ
    let Gamma := Cphys/κ
    let Lsource := fun ab => κ/(16*(Blabels:ℝ)*Cphys)*((S ab).card:ℝ)
    (∀ ab∈Gaps, 32*Blabels ≤ (S ab).card) →
    (∀ ab∈Gaps, L ≤ Lsource ab) →
    (∀ ab∈Gaps, |Gcoord ab (l ab)| ≤ |r ab 0| *N^2/(Bcut*R^2)) →
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, iteratedDeriv 2 (f i) (x ab j i)/2=
      (e ab i*(p ab j).1+v ab i*(p ab j).2)/(r ab i*(p ab j).1+s ab i*(p ab j).2)) →
    (∀ ab∈Gaps, ∀ j∈S ab, iteratedDeriv 2 (f 0) (x ab j 0)/2∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, y₀ ab∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, ∀ j∈S ab, y ab j∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, |iteratedDeriv 2 (g ab) (y₀ ab)-iteratedDeriv 2 (h ab) (y₀ ab)| ≤ Vcurv ab) →
    (∀ ab∈Gaps, ∀ j∈S ab,
      |(ac ab-round (ac ab-deriv (phi ab) (y ab j)))*y ab j+
        (bc ab-round (bc ab-phi ab (y ab j)+y ab j*deriv (phi ab) (y ab j)))-
        g ab (y ab j)+h ab (y ab j)| ≤ D/(p ab j).2) →
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 := by
  classical
  intro Blabels f mu nu y g h phi Gcoord Vcurv Z κ Cphys K Gamma Lsource
    hS hlong hGcut hbase hpoint hsourceGap hy₀ hy hcurv hres Cthird Cpack
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_cases hne : Gaps.Nonempty
  · have hex ab (hab : ab∈Gaps) :=
      physicalModelPhase_signed_height_square_span_quartic_witnesses (S ab) (p ab) (x ab)
        (hS ab hab) hσ hδ hF hT hM hN hR (hd ab hab) hCres hD₀ hD hDupper hscale
        hA hW (href ab hab) (hheight ab hab) (hpt ab hab) (hQband ab hab)
        (hx ab hab) (hwindow ab hab) (hdisplacement ab hab) (hspan ab hab)
        (hnsquare ab hab) (hr ab hab) (hdet ab hab) (hden ab hab) (hcoord ab hab)
        hP₂ hCcurv hBcut hBsize (hGcut ab hab) (hpoint ab hab)
        (hy₀ ab hab) (hy ab hab) (hcurv ab hab) (hres ab hab)
    choose! j z curve alpha beta hj hmono hLp hNL hKp hcurve hspacing hres' using hex
    let take : Fin 4 → Fin 8 := fun i => ⟨i.val,by omega⟩
    have htake : StrictMono take := fun _ _ hh => hh
    let z4 := fun ab i => z ab (take i)
    have hsub ab (hab : ab∈Gaps) : Icc (z4 ab 0) (z4 ab 3) ⊆ Icc (z ab 0) (z ab 7) := by
      intro q hq
      exact ⟨hq.1,hq.2.trans ((hmono ab hab).monotone (by change (3:Fin 8) ≤ 7; decide))⟩
    have hNLL : (L*N)^2 ≤ M*R := by
      obtain ⟨ab,hab⟩ := hne
      exact (pow_le_pow_left₀ (mul_pos hL hN).le
        (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le) 2).trans (hNL ab hab)
    have hends ab (hab : ab∈Gaps) (a : Fin 4) :
        iteratedDeriv 2 (f 0) (curve ab (z4 ab a) 0)/2∈Ioo ab.1 ab.2 := by
      have ha : z4 ab a∈Icc (z ab 0) (z ab 7) :=
        ⟨(hmono ab hab).monotone (by omega),(hmono ab hab).monotone (by omega)⟩
      rw [((hcurve ab hab _ ha).2 0).2.2.2.1,← (hj ab hab (take a)).2.2 0]
      exact hsourceGap ab hab _ (hj ab hab (take a)).1
    obtain ⟨_q,_hq,hpack⟩ := physicalModelPhase_quartic_long_reference_gap_packing
      Refs Gaps Mat z4 xref e r v s curve d alpha beta
      hσ hδ hF hT hM hN hR hU hL hNLL hK hA hW hMat hc hlarge hsep hgap hd href
      (fun ab hab q hq i => ((hcurve ab hab q (hsub ab hab hq)).2 i).1) hr hdet
      (fun ab hab q hq i => ⟨((hcurve ab hab q (hsub ab hab hq)).2 i).2.1,
        ((hcurve ab hab q (hsub ab hab hq)).2 i).2.2.1⟩)
      (fun ab hab => (hmono ab hab).comp htake) htransport hbase
      (fun ab hab q hq i => ((hcurve ab hab q (hsub ab hab hq)).2 i).2.2.2.1)
      (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
      (fun ab hab q hq i => ((hcurve ab hab q (hsub ab hab hq)).2 i).2.2.2.2)
      (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
        (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
      (fun ab hab i => hres' ab hab (take i))
    exact hpack
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
    have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
      dsimp only [quarticReciprocalConstant]
      positivity
    dsimp only [Cpack,Cthird,Gamma,Cphys]
    positivity

theorem physicalModelPhase_actual_fourier_height_square_span_fixed_reference_quartic_witnesses
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
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
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) := by
  classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  intro xref hxr Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hD hΔ
    hdenregion hleft hright hlarge hBsize hGcut Blabels L vp
  have hrp i : rp i ≠ 0 := (hxr i).1
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have href i : iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i := (hxr i).2.2
  let p : ℕ → ℤ × ℤ := fun j =>
    (v*(q j 0:ℤ)-s*(rat j 0).num,r*(rat j 0).num-e*(q j 0:ℤ))
  let y := fun j => ((p j).1:ℝ)/(p j).2
  let dr := fun i => deriv (f i) (ar i)
  let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
  let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
  let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
  let ac := θr 0-θr 1
  let bc := βr 0-βr 1
  let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
  let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
  let φ := fun z => g z-hq z
  have hMone : 1 ≤ M := hR.trans hRM
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,Cphys]; positivity
  have hNscale : N^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg N) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hN.le 3) hNcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hrect j (hj : j∈S) : 0 < (p j).2 ∧ y j∈Icc (α j) (β j) := by
    have ha : (anchor j:ℝ)∈Icc (lo j) (hi j) := by
      have hh := abs_le.mp (hanchor j hj)
      exact ⟨by dsimp only [lo]; linarith only [hh.1],
        by dsimp only [hi]; linarith only [hh.2]⟩
    have hp : (rat j 0:ℝ)∈Icc (lo j) (hi j) := by
      constructor <;> dsimp only [lo,hi] <;> linarith only [hε]
    have hh := inverseFarey_original_seed_enlarged_rectangle_signed
      hchart (hdl j hj) (hdw j hj) (hnum j hj) ha hp (hdyad j hj) (hcut j hj)
      (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
    exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
  have hy j (hj : j∈S) : y j∈finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).out (hleft j hj) (hright j hj) (hrect j hj).2
  have hlocalI j (hj : j∈S) : Icc (α j) (β j) ⊆ Icc l w :=
    fun z hz => ⟨(hleft j hj).1.1.trans hz.1,hz.2.trans (hright j hj).1.2⟩
  have hleft' j (hj : j∈S) : α j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨le_rfl,(hrect j hj).2.1.trans (hrect j hj).2.2⟩,(hleft j hj).2⟩
  have hright' j (hj : j∈S) : β j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨(hrect j hj).2.1.trans (hrect j hj).2.2,le_rfl⟩,(hright j hj).2⟩
  have hsource j (hj : j∈S) :
      |iteratedDeriv 2 g (y j)-iteratedDeriv 2 hq (y j)| ≤ U ∧
      |(ac-round (ac-deriv φ (y j)))*y j+
        (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+hq (y j)| ≤
        D/(p j).2 := by
    exact physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes
      Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
      hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
      (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
      hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) (hnum j hj)
      (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
      hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
      (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
      (hleft' j hj) (hright' j hj) (hlarge j hj)
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hcoordinates j (hj : j∈S) :
      (∀ i, (rp i:ℝ)*(p j).1+sp i*(p j).2=(q j i:ℝ)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x j i)/2=
        ((ep i:ℝ)*(p j).1+vp i*(p j).2)/((rp i:ℝ)*(p j).1+sp i*(p j).2)) := by
    have hc := farey_matrix_original_seed_coordinates (rat j) Mat e r v s
      hchart (hMatt j hj) (hMatmap j hj)
    refine ⟨fun i => (hc i).1,?_⟩
    intro i
    rw [(hc i).1,(hc i).2,hlevel j hj]
    exact Rat.cast_def _
  have hpoint j (hj : j∈S) i := (hcoordinates j hj).2 i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  let Cres := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  have hCres : 0 ≤ Cres := by
    dsimp only [Cres,Cc,Ct,C₂,C₃,quarticNonlinearResidualConstant]
    positivity
  have hDeq : D=Cres*(Q:ℝ)/N := by dsimp only [D,Δ,Cres]; ring
  have hD₀ : 0 ≤ D := by
    rw [hDeq]
    exact div_nonneg (mul_nonneg hCres (Nat.cast_nonneg Q)) hN.le
  have hVheight : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ0))
    (by positivity)
  have hP₂ : 0 < P₂ := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hVheight) (abs_nonneg _))
      (Nat.cast_nonneg Q))
  have hpheight j (hj : j∈S) :
      |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂ := by
    have hxj : x j 0∈Ioo 0 (W 0) :=
      ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩
    have hh := physicalModelPhase_original_seed_coordinate_heights (rat j 0) Q e r v s
      hσ.le (hF 0) (by norm_num : 1 ≤ 4) hT hM (hA 0) (hW 0)
      hxj (hden j hj 0).1 (hlevel j hj 0)
    exact ⟨hh.1.trans (le_add_of_nonneg_left zero_le_one),
      (le_abs_self _).trans (hh.2.trans (le_add_of_nonneg_left zero_le_one))⟩
  have hpband j (hj : j∈S) :
      (Q:ℝ) ≤ 2*((rp 0:ℝ)*(p j).1+sp 0*(p j).2) := by
    rw [(hcoordinates j hj).1 0]
    exact_mod_cast (hden j hj 0).2
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨j,z,curve,alpha,beta,hj,hmono,hLp,hNL,hKp,hcurve,hspacing,hres⟩ :=
    physicalModelPhase_signed_height_square_span_quartic_witnesses
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (Cres:=Cres) (Q:=(Q:ℝ)) (D:=D)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDeq.le hscale hA hW hxref
    hpheight (fun j hj => (hrect j hj).1) hpband hx hwindow hdisplacement hspan hsourcesquare
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hP₂ hCcurv hBcut hBsize hGcut
    hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  refine ⟨j,z,curve,alpha,beta,?_,hmono,hLp,hNL,hKp,hcurve,hspacing,hres⟩
  intro a
  refine ⟨(hj a).1,fun i => ?_⟩
  rw [← hlevel _ (hj a).1 i]
  exact (hj a).2.2 i

private theorem physicalModelPhase_actual_fourier_height_square_span_fixed_reference_first_condition_reused
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
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
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
  classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
    xref hxr Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hD hΔ
    hdenregion hleft hright hlarge hBsize hGcut Blabels Γ L C Cfirst Csecond
  obtain ⟨_j,z,curve,alpha,beta,_hj,hmono,hLp,hNL,hKp,hcurve,hspacing,hres⟩ :=
    physicalModelPhase_actual_fourier_height_square_span_fixed_reference_quartic_witnesses
      S Q K₀ rat vinv parity anchor Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare
      hden hinv hchart hd hcoord hBcut
      hS hlevel hcolor hnear hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
      hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount xref hxr Hspan hdisplacement hspan
      hbudget hD hΔ hdenregion hleft hright hlarge hBsize hGcut
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have htransport : (ep 1:ℝ)=(Mat 0:ℝ)*(ep 0)+Mat 1*(rp 0) ∧
      (vp 1:ℝ)=(Mat 0:ℝ)*(vp 0)+Mat 1*(sp 0) ∧
      (rp 1:ℝ)=(Mat 2:ℝ)*(ep 0)+Mat 3*(rp 0) ∧
      (sp 1:ℝ)=(Mat 2:ℝ)*(vp 0)+Mat 3*(sp 0) := by
    simp [ep,vp,rp,sp,Int.cast_add,Int.cast_mul]
  exact physicalModelPhase_quartic_matrix_long_block_first_condition
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    (x₁:=curve) (α:=alpha) (β:=beta) z Mat
    hσ hδ hF hT hM hN hR hLp hNL hd hKp hA hW (fun i => (hxr i).2.1)
    (fun q hq i => ((hcurve q hq).2 i).1)
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast (hxr i).1)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    (fun q hq i => ((hcurve q hq).2 i).2.1)
    (fun q hq i => ((hcurve q hq).2 i).2.2.1) hmono hscale hMatdet htransport
    (fun i => (hxr i).2.2)
    (fun q hq i => ((hcurve q hq).2 i).2.2.2.1)
    (fun q hq i => ((hcurve q hq).2 i).2.2.2.2)
    hspacing hres

#print axioms physicalModelPhase_actual_fourier_height_square_span_fixed_reference_first_condition_reused
#print axioms physicalModelPhase_actual_fourier_height_square_span_fixed_reference_quartic_witnesses
#print axioms physicalModelPhase_signed_height_long_reference_gap_packing
#print axioms physicalModelPhase_signed_height_square_span_first_condition_reused
#print axioms physicalModelPhase_signed_height_square_span_quartic_witnesses
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
  HuxleyQuarticWitnessScratch.physicalModelPhase_quartic_long_reference_gap_packing Refs Gaps Mat x xref e r v s curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (L:=L) (K:=K) (A:=A) (W:=W) (F:=F) hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hMat hc hlarge hsep hgap hd href hcurve hr hdet hden hmono htransport

example
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (Mat : Fin 4 → ℤ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hnsquare : nSpan^2 ≤ M*R)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M :=
  HuxleyQuarticWitnessScratch.physicalModelPhase_signed_height_square_span_first_condition_reused (Kcoord:=Kcoord) S p x Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord hP₂ hCcurv hBcut hBsize hMat htransport

example
    {Kcoord : ℕ}
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (S : ℝ × ℝ → Finset ℕ) (p : ℝ × ℝ → ℕ → ℤ × ℤ)
    (x : ℝ × ℝ → ℕ → Fin 2 → ℝ)
    (xref e r v s H : ℝ × ℝ → Fin 2 → ℝ)
    (d nSpan base l w y₀ ac bc : ℝ × ℝ → ℝ) (k : ℝ × ℝ → Fin 17)
    {σ δ T M N R U L Cres Q D Ccurv Bcut P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hU : 0 < U) (hL : 0 < L) (hCres : 0 ≤ Cres)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hP₂ : 0 < P₂) (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : ((2*Kcoord+1:ℕ):ℝ)*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2≠0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2))
    (hd : ∀ ab∈Gaps, 0 < d ab)
    (href : ∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ ab∈Gaps, ∀ j∈S ab, |((p ab j).1:ℝ)| ≤ P₁ ∧ ((p ab j).2:ℝ) ≤ P₂)
    (hpt : ∀ ab∈Gaps, ∀ j∈S ab, 0 < (p ab j).2)
    (hQband : ∀ ab∈Gaps, ∀ j∈S ab, Q ≤ 2*(r ab 0*(p ab j).1+s ab 0*(p ab j).2))
    (hx : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, x ab j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ ab∈Gaps, ∀ j∈S ab,
      x ab j 0∈Icc (base ab+N*(j:ℝ)) (base ab+N*((j:ℝ)+1)))
    (hdisplacement : ∀ ab∈Gaps, ∀ j∈S ab, ∀ i, |x ab j i-xref ab i| ≤ H ab i)
    (hspan : ∀ ab∈Gaps, ∀ i, 2*H ab i+1 ≤ nSpan ab)
    (hnsquare : ∀ ab∈Gaps, (nSpan ab)^2 ≤ M*R)
    (hr : ∀ ab∈Gaps, ∀ i, r ab i≠0)
    (hdet : ∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1)
    (hden : ∀ ab∈Gaps, ∀ t∈Icc (l ab) (w ab), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab)
    (hcoord : ∀ ab∈Gaps, |r ab 0| * max |l ab| |w ab| ≤ (Kcoord:ℝ)*d ab)
    (htransport : ∀ ab∈Gaps,
      e ab 1=(Mat 0:ℝ)*e ab 0+Mat 1*r ab 0 ∧
      v ab 1=(Mat 0:ℝ)*v ab 0+Mat 1*s ab 0 ∧
      r ab 1=(Mat 2:ℝ)*e ab 0+Mat 3*r ab 0 ∧
      s ab 1=(Mat 2:ℝ)*v ab 0+Mat 3*s ab 0) :
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let y := fun ab j => ((p ab j).1:ℝ)/(p ab j).2
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let h := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let phi := fun ab t => g ab t-h ab t
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let Vcurv := fun ab => Ccurv*R^4/(N*(d ab)^3)
    let Z := fun ab => quarticCurvatureBoundaryRoots (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1) (Vcurv ab)
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let K := 4*Cres/κ
    let Gamma := Cphys/κ
    let Lsource := fun ab => κ/(16*(Blabels:ℝ)*Cphys)*((S ab).card:ℝ)
    (∀ ab∈Gaps, 32*Blabels ≤ (S ab).card) →
    (∀ ab∈Gaps, L ≤ Lsource ab) →
    (∀ ab∈Gaps, |Gcoord ab (l ab)| ≤ |r ab 0| *N^2/(Bcut*R^2)) →
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, iteratedDeriv 2 (f i) (x ab j i)/2=
      (e ab i*(p ab j).1+v ab i*(p ab j).2)/(r ab i*(p ab j).1+s ab i*(p ab j).2)) →
    (∀ ab∈Gaps, ∀ j∈S ab, iteratedDeriv 2 (f 0) (x ab j 0)/2∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, y₀ ab∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, ∀ j∈S ab, y ab j∈finiteBoundaryCell (Z ab) (l ab) (w ab) (k ab)) →
    (∀ ab∈Gaps, |iteratedDeriv 2 (g ab) (y₀ ab)-iteratedDeriv 2 (h ab) (y₀ ab)| ≤ Vcurv ab) →
    (∀ ab∈Gaps, ∀ j∈S ab,
      |(ac ab-round (ac ab-deriv (phi ab) (y ab j)))*y ab j+
        (bc ab-round (bc ab-phi ab (y ab j)+y ab j*deriv (phi ab) (y ab j)))-
        g ab (y ab j)+h ab (y ab j)| ≤ D/(p ab j).2) →
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    (Gaps.card:ℝ) ≤ Cpack*R^4/(L^2*N^2*|(Mat 2:ℝ)| *U)+2 :=
  HuxleyQuarticWitnessScratch.physicalModelPhase_signed_height_long_reference_gap_packing (Kcoord:=Kcoord) Refs Gaps Mat S p x xref e r v s H d nSpan base l w y₀ ac bc k (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (L:=L) (Cres:=Cres) (Q:=Q) (D:=D) (Ccurv:=Ccurv) (Bcut:=Bcut) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) hσ hδ hF hT hM hN hR hU hL hCres hD₀ hD hDupper hscale hA hW hP₂ hCcurv hBcut hBsize hMat hc hlarge hsep hgap hd href hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord htransport

example
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
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
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    ∃ j : Fin 8 → ℕ, ∃ z : Fin 8 → ℝ, ∃ curve : ℝ → Fin 2 → ℝ, ∃ alpha beta : ℝ,
      (∀ a, j a∈S ∧ ∀ i,
        (rat (j a) i:ℝ)=((ep i:ℝ)*z a+vp i)/((rp i:ℝ)*z a+sp i)) ∧
      StrictMono z ∧ 0 < L ∧ (L*N)^2 ≤ M*R ∧ 0 ≤ Kres ∧
      (∀ t∈Icc (z 0) (z 7), t∈Icc l w ∧ ∀ i,
        curve t i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        d ≤ (rp i:ℝ)*t+sp i ∧ (rp i:ℝ)*t+sp i ≤ 2*d ∧
        iteratedDeriv 2 (f i) (curve t i)/2=((ep i:ℝ)*t+vp i)/((rp i:ℝ)*t+sp i) ∧
        |(round (curve t i):ℝ)-(round (xref i):ℝ)|^2 ≤ M*R) ∧
      (∀ i : Fin 7, L*N ≤ |G (z i.succ)-G (z i.castSucc)|) ∧
      (∀ i : Fin 8,
        |alpha*z i+beta-rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1) (z i)+
          quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1) (z i)| ≤
          Kres*R^2/|(rp 0:ℝ)*G (z i)|) :=
  HuxleyQuarticWitnessScratch.physicalModelPhase_actual_fourier_height_square_span_fixed_reference_quartic_witnesses S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut


#print axioms physicalModelPhase_quartic_long_reference_gap_packing
#print axioms reference_chart_fraction_antitone
#print axioms paired_large_entry_reference_gap_packing
#print axioms reference_gap_count_of_profile_width
example
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
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
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M :=
  HuxleyQuarticWitnessScratch.physicalModelPhase_actual_fourier_height_square_span_fixed_reference_first_condition_reused S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut

end HuxleyQuarticWitnessScratch
