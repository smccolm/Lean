import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyCertifiedFamilyScratch

private theorem source_sector_linearization_error_bound
    (K : ℕ) {D D₀ Ct E R N Q d width : ℝ}
    (hCt : 0 ≤ Ct)
    (hR : 0 < R) (hN : 0 < N) (hQ : 0 < Q) (hd : 0 < d)
    (hK : (K:ℝ) ≤ Q/d)
    (hwidth : 0 ≤ width ∧ width ≤ 8*(E/R^2)*d^2)
    (hD : D ≤ D₀*Q/N) :
    D+(K:ℝ)*(Ct*R^4/(N*d^3))*width^2 ≤
      (D₀+64*Ct*E^2)*Q/N := by
  have hw0 := hwidth.1
  have hwupper := hwidth.2
  have hterm : (K:ℝ)*(Ct*R^4/(N*d^3))*width^2 ≤ 64*Ct*E^2*Q/N := by
    calc
      _ ≤ (Q/d)*(Ct*R^4/(N*d^3))*(8*(E/R^2)*d^2)^2 := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ D₀*Q/N+64*Ct*E^2*Q/N := add_le_add hD hterm
    _ = _ := by ring

private theorem source_sector_weighted_error_bound
    {η Cη Q N height width U E B : ℝ}
    (hC : 0 ≤ Cη) (hQ : 0 < Q) (hN : 0 < N)
    (hheight : 0 ≤ height) (hwidth : 0 ≤ width)
    (hE : 0 < E) (hB : 0 < B)
    (hη : η ≤ Cη*Q/N) (hheightBound : height ≤ 105*U/E*width)
    (hselected : B*U*Q ≤ N)
    (hmargin : 2*3840*128^2*105*Cη ≤ B*E) :
    3840*128*η*height ≤ width/256 := by
  have hratio : U*Q/N ≤ 1/B := by
    apply (div_le_div_iff₀ hN hB).mpr
    nlinarith only [hselected]
  have hconstant : (3840*128*105*Cη)/(B*E) ≤ 1/256 := by
    apply (div_le_iff₀ (mul_pos hB hE)).mpr
    nlinarith only [hmargin]
  calc
    _ ≤ 3840*128*(Cη*Q/N)*height := by gcongr
    _ ≤ 3840*128*(Cη*Q/N)*(105*U/E*width) := by gcongr
    _ = ((3840*128*105*Cη)/E)*(U*Q/N)*width := by field_simp
    _ ≤ ((3840*128*105*Cη)/E)*(1/B)*width := by gcongr
    _ = ((3840*128*105*Cη)/(B*E))*width := by field_simp
    _ ≤ (1/256)*width := mul_le_mul_of_nonneg_right hconstant hwidth
    _ = width/256 := by ring

private theorem source_sector_height_width_bound
    {height width E R r d U : ℝ}
    (hE : 0 < E) (hR : 0 < R) (hr : 0 < r) (hd : 0 < d) (hU : 0 ≤ U)
    (hheight : r*height ≤ 30*d)
    (hgap : R^2 ≤ 7*r*d*U)
    (hwidth : 2*(E/R^2)*d^2 ≤ width) :
    height ≤ 105*U/E*width := by
  have hH : height ≤ 30*d/r := (le_div_iff₀ hr).mpr (by nlinarith only [hheight])
  have hmain : 30*d/r ≤ (105*U/E)*(2*(E/R^2)*d^2) := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hr (pow_pos hR 2))).mp
    have hleft : (30*d/r)*(r*R^2)=30*d*R^2 := by field_simp
    have hright : ((105*U/E)*(2*(E/R^2)*d^2))*(r*R^2)=210*U*d^2*r := by
      field_simp
      ring
    rw [hleft,hright]
    nlinarith only [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 30*d by positivity)]
  exact hH.trans (hmain.trans (mul_le_mul_of_nonneg_left hwidth (by positivity)))

/-- The actual inverse-Farey sector has enough primitive points for the
strict label-linearization test. Its density is obtained from the existing
positive/negative sector theorem, and the error budget is derived from
the SAME reference gap and selected-U scalar budget. -/
theorem reference_gap_complete_sector_linearization_size
    (e r v s : ℤ) (anchor : ℚ)
    {q ε E R Q N d l w gapLo gapHi U B D D₀ Ct : ℝ}
    (hdet : v*r-e*s=1) (hr : r ≠ 0)
    (hE : 0 < E) (hR : 0 < R) (hQ : 0 < Q) (hN : 0 < N)
    (hd : 0 < d) (hU : 0 ≤ U) (hB : 0 < B)
    (hCt : 0 ≤ Ct) (hD₀ : 0 ≤ D₀) (heps : ε=E/R^2)
    (hminus : 0 < (r:ℝ)*(q-ε)-e)
    (hplus : 0 < (r:ℝ)*(q+ε)-e)
    (hdyad : max ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) ≤
      2*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e))
    (hanchor : |(anchor:ℝ)-q| ≤ ε)
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3)
    (hcount : 256 ≤ (2*ε)*(Q/3)*anchor.den)
    (hden : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d)
    (hgap : gapHi-gapLo ≤ 7*U/(2*R^2))
    (hendpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hpoint : q+ε∈Icc gapLo gapHi)
    (hselected : B*U*Q ≤ N)
    (hmargin : 2*3840*128^2*105*(D₀+64*Ct*E^2) ≤ B*E)
    (hD : D ≤ D₀*Q/N) :
    let α := ((v:ℝ)-s*(q+ε))/((r:ℝ)*(q+ε)-e)
    let β := ((v:ℝ)-s*(q-ε))/((r:ℝ)*(q-ε)-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e)⌋₊
    let S := if 0 < α then HuxleyLinearForm.fareySector K α β
      else (HuxleyLinearForm.fareySector K (-β) (-α)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let η := D+(K:ℝ)*(Ct*R^4/(N*d^3))*(β-α)^2
    α∈Icc l w → β∈Icc l w → (0 < α ∨ β < 0) →
    3840*128*η*((max |α| |β|)*(K:ℝ))*(K:ℝ) < S.card := by
  classical
  intro α β K S η hαI hβI hsign
  have hε : 0 < ε := by rw [heps]; positivity
  have hdetR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hdet
  have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have hαden : (r:ℝ)*α+s=1/((r:ℝ)*(q+ε)-e) := by
    dsimp only [α]
    field_simp
    nlinarith only [hdetR]
  have hβden : (r:ℝ)*β+s=1/((r:ℝ)*(q-ε)-e) := by
    dsimp only [β]
    field_simp
    nlinarith only [hdetR]
  have hwidth : β-α=2*ε*((r:ℝ)*α+s)*((r:ℝ)*β+s) := by
    rw [hαden,hβden]
    have hh := inverseFarey_difference hdetR hminus.ne' hplus.ne'
    change β-α=((q+ε)-(q-ε))/(((r:ℝ)*(q-ε)-e)*((r:ℝ)*(q+ε)-e)) at hh
    rw [hh]
    field_simp
    ring
  have hαd := hden α hαI
  have hβd := hden β hβI
  have hαlo := hαd.1
  have hαhi := hαd.2
  have hβlo := hβd.1
  have hβhi := hβd.2
  have hαpos := hd.trans_le hαlo
  have hβpos := hd.trans_le hβlo
  have hwidth0 : 0 < β-α := by
    rw [hwidth]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hε) (hd.trans_le hαd.1))
      (hd.trans_le hβd.1)
  have hwidthLower : 2*(E/R^2)*d^2 ≤ β-α := by
    rw [hwidth,←heps]
    calc
      _ = 2*ε*d*d := by ring
      _ ≤ _ := by gcongr
  have hwidthUpper : β-α ≤ 8*(E/R^2)*d^2 := by
    rw [hwidth,←heps]
    calc
      _ ≤ 2*ε*(2*d)*(2*d) := by gcongr
      _ = _ := by ring
  have hAupper : (r:ℝ)*(q-ε)-e ≤ 1/d := by
    have hh := hβd.1
    rw [hβden] at hh
    have hx := (le_div_iff₀ hminus).mp hh
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hx]
  have hK : (K:ℝ) ≤ Q/d := by
    have hm : 0 < min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) := lt_min hminus hplus
    calc
      _ ≤ (Q/3)*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) := Nat.floor_le (by positivity)
      _ ≤ Q*(1/d) := by
        apply mul_le_mul
        · linarith only [hQ]
        · exact (min_le_left _ _).trans hAupper
        · exact hm.le
        · exact hQ.le
      _ = Q/d := by ring
  have hη : η ≤ (D₀+64*Ct*E^2)*Q/N :=
    source_sector_linearization_error_bound K hCt hR hN hQ hd hK
      ⟨hwidth0.le,hwidthUpper⟩ hD
  have habs (z : ℝ) (hz : z∈Icc l w) : |z| ≤ max |l| |w| := by
    apply abs_le.mpr
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le l).trans hz.1),
      hz.2.trans ((le_abs_self w).trans (le_max_right _ _))⟩
  have hheight : |(r:ℝ)| * max |α| |β| ≤ 30*d :=
    (mul_le_mul_of_nonneg_left (max_le (habs α hαI) (habs β hβI))
      (abs_nonneg _)).trans hcoord
  have hdist : |q+ε-(e:ℝ)/r| ≤ 7*U/(2*R^2) := by
    apply le_trans _ hgap
    rcases hendpoint with he | he
    · rw [he,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [he,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hid : (q+ε-(e:ℝ)/r)*(r:ℝ)*((r:ℝ)*α+s)=1 := by
    rw [hαden]
    field_simp
    exact div_self (by nlinarith only [hplus])
  have hidentity : |q+ε-(e:ℝ)/r| * |(r:ℝ)| *((r:ℝ)*α+s)=1 := by
    have hh := congrArg abs hid
    simpa only [abs_mul,abs_one,abs_of_pos (hd.trans_le hαd.1)] using hh
  have hgapScale : R^2 ≤ 7*|(r:ℝ)| *d*U := by
    have hh : (1:ℝ) ≤ 7*U/(2*R^2)*|(r:ℝ)| *(2*d) := by
      rw [←hidentity]
      gcongr
    have he : 7*U/(2*R^2)*|(r:ℝ)| *(2*d)=(7*|(r:ℝ)| *d*U)/R^2 := by
      field_simp
    rw [he] at hh
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hR 2)).mp hh
  have hheightWidth : max |α| |β| ≤ 105*U/E*(β-α) :=
    source_sector_height_width_bound hE hR (abs_pos.mpr hrR) hd hU
      hheight hgapScale hwidthLower
  have hweighted : 3840*128*η*(max |α| |β|) ≤ (β-α)/256 :=
    source_sector_weighted_error_bound (by positivity) hQ hN
      ((abs_nonneg α).trans (le_max_left _ _)) hwidth0.le hE hB
      hη hheightWidth hselected hmargin
  have hanchorI : (anchor:ℝ)∈Icc (q-ε) (q+ε) := by
    have hh := abs_le.mp hanchor
    constructor <;> linarith only [hh.1,hh.2]
  have hcount' : 256 ≤ ((q+ε)-(q-ε))*(Q/3)*anchor.den := by
    convert hcount using 1
    ring
  have hdensity : max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ (S.card:ℝ) := by
    by_cases ha : 0 < α
    · have hn : 0 < (v:ℝ)-s*(q+ε) := (div_pos_iff_of_pos_right hplus).mp ha
      have hh := completeSector_density_from_curvature_signed hdet
        (by linarith only [hε] : q-ε < q+ε) hminus hplus hn hanchorI hdyad hcut hcount'
      simpa only [S,if_pos ha] using hh.1
    · have hb : β < 0 := hsign.resolve_left ha
      have hn : (v:ℝ)-s*(q-ε) < 0 := by
        simpa only [zero_mul] using (div_lt_iff₀ hminus).mp hb
      have hh := completeNegativeSector_density_from_curvature hdet
        (by linarith only [hε] : q-ε < q+ε) hminus hplus hn hanchorI hdyad hcut hcount'
      simpa only [S,if_neg ha] using hh.1
  have hhalf : 2*(3840*128*η*((max |α| |β|)*(K:ℝ))*(K:ℝ)) ≤
      (β-α)*(K:ℝ)^2/128 := by
    have hh := mul_le_mul_of_nonneg_right hweighted
      (show 0 ≤ 2*(K:ℝ)^2 by positivity)
    nlinarith only [hh]
  have hlow := (le_max_left _ _).trans hdensity
  have hpos := (le_max_right _ _).trans hdensity
  linarith only [hhalf,hlow,hpos]

private theorem selected_reference_linear_budget
    (U : ℕ) {B N Q : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hB : 1 ≤ B) (hU : 1 ≤ U)
    (hupper : (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B) :
    B*(U:ℝ)*Q ≤ N := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hUone : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hh := (le_div_iff₀ hBp).mp hupper
  have hlower : 1 ≤ (N/Q)^((2:ℝ)/3) := by
    have hb := mul_le_mul hUone hB (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg U)
    linarith only [hb,hh]
  have hratio : 1 ≤ N/Q := by
    by_contra hn
    have ht := Real.rpow_lt_one (div_pos hN hQ).le (lt_of_not_ge hn)
      (by norm_num : (0:ℝ) < (2:ℝ)/3)
    exact (not_lt_of_ge hlower) ht
  have hp := Real.rpow_le_self_of_one_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)
  apply (le_div_iff₀ hQ).mp
  nlinarith only [hh,hp]

private theorem physical_source_quartic_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ quarticReciprocalConstant σ δ ∧ 0 ≤ quarticNonlinearResidualConstant σ δ := by
  have hκ := modelPhaseThirdLower_pos hσ
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ
  constructor
  · dsimp only [quarticReciprocalConstant]
    positivity
  · dsimp only [quarticNonlinearResidualConstant]
    positivity

/-- The actual source family derives its inverse-chart positivity,
factor-two variation AND strict complete-sector linearization size.
The SAME selected integer U controls the density/error margin; the
original family retains the explicit 105+17 loss. -/
theorem physicalModelPhase_actual_fourier_certified_reference_gap_count
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
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
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
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
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈G, α j∈Icc l w ∧ β j∈Icc l w) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 105+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
  classical
  intro Lref Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hanchor hcut hcount
    lo hi α β C₂ C₃ Ct Cc Δ ep rp sp
  let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
  let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
  have hr : r ≠ 0 := by
    rcases horientation with ⟨hr,_⟩ | ⟨hr,_⟩
    · exact_mod_cast hr.ne'
    · exact_mod_cast hr.ne
  have hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi :=
    horientation.imp And.right And.right
  obtain ⟨G,hGS,hS6G,hgeom⟩ :=
    physicalModelPhase_reference_gap_interior_chart_selection S (fun j => x j 0)
      hσ hδ (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM hN (zero_lt_one.trans_le hR) (hA 0) (hW 0) hscale horientation
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun j hj => by
        change iteratedDeriv 2 (f 0) (x j 0)/2∈Icc gapLo gapHi
        rw [hlevel j hj 0]
        exact hfamilyGap j hj)
  have hGlarge : 99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ G.card := by
    have hb := hS.trans hS6G
    exact Nat.le_of_add_le_add_left (a:=6)
      (by simpa only [←Nat.add_assoc] using hb)
  have hGpos : 0 < G.card :=
    (by decide : 0 < 99).trans_le ((Nat.le_add_right 99 _).trans hGlarge)
  obtain ⟨jref,hjref⟩ := Finset.card_pos.mp hGpos
  have hgeometry j (hj : j∈G) :
      0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e ∧
      0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e ∧
      max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
        2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) := by
    have hh := (hgeom j hj).2.2
    change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
      0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e ∧
      max ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)
          ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e) ≤
        2*min ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)
          ((r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e) ∧ _ at hh
    rw [hlevel j (hGS hj) 0] at hh
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hconsumer := physicalModelPhase_actual_fourier_separated_reference_gap_count Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) G jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun j hj => hx j (hGS hj)) (fun j hj => hwindow j (hGS hj)) (fun j hj => hden j (hGS hj)) (fun j hj => hinv j (hGS hj)) hchart hr hd hBcut hs hrefSet hparentSet hsep hdenl hdenw (hwideL jref (hGS hjref)) (hwideU jref (hGS hjref)) hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hchartRight hRQ hselectedUpper hscaleTen (fun j hj => hfamilyGap j (hGS hj))
  obtain ⟨xref,hxr,hrest⟩ := hconsumer hGlarge
    (fun j hj => hlevel j (hGS hj)) (fun j hj => hcolor j (hGS hj))
    (fun j hj => hnear j (hGS hj))
    hsmall hNR hRN hNcube hminscale hMatdet
    (fun j hj => hMatt j (hGS hj)) (fun j hj => hMatmap j (hGS hj)) hMatgamma
    hNtwo (fun j hj => hL j (hGS hj)) (fun j hj => hU j (hGS hj))
    (fun j hj => (hgeometry j hj).1) (fun j hj => (hgeometry j hj).2.1)
    (fun j hj => (hgeometry j hj).2.2)
    (fun j hj => hanchor j (hGS hj)) (fun j hj => hcut j (hGS hj))
    (fun j hj => hcount j (hGS hj))
  refine ⟨G,hGS,hS6G,jref,hjref,xref,hxr,?_⟩
  intro Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hdenregion hends hBsize
  let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
  let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
  have hEsize : 0 < Esize := by dsimp only [Esize]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hBselect : 0 < Bselect := by
    have hh : 0 < 168/κ := by positivity
    change 2+168/κ ≤ Bselect at hBselectSize
    linarith only [hBselectSize,hh]
  have hBselectOne : 1 ≤ Bselect := by
    have hh : 0 < 168/κ := by positivity
    change 2+168/κ ≤ Bselect at hBselectSize
    linarith only [hBselectSize,hh]
  have hselectedLinear : Bselect*(Uref:ℝ)*(Q:ℝ) ≤ N :=
    selected_reference_linear_budget Uref hN hQpos hBselectOne hUref hselectedUpper
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct,C₂,C₃]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc,C₂,C₃]; positivity
  have hDbase : 0 ≤ Dbase := by dsimp only [Dbase]; positivity
  have hTbase : 0 ≤ Tbase := by dsimp only [Tbase]; positivity
  have hDupper : D ≤ Dbase*(Q:ℝ)/N := by
    apply le_of_eq
    dsimp only [D,Dbase,Δ]
    ring
  have heps : ε=Esize/R^2 := by
    dsimp only [ε,Esize]
    field_simp
  have hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d :=
    separated_farey_reference_interval_coordinate_bound Refs
      (δ:=(Uref:ℝ)/R^2) (by exact_mod_cast hr) (by exact_mod_cast hs)
      (by exact_mod_cast hchart) hrefSet hparentSet hsep
      (hgapWidth.trans_eq (by ring)) hreferenceEndpoint hd hdenl hdenw
      hchartLeft hchartRight
  have hsector j (hj : j∈G) (hsign : 0 < α j ∨ β j < 0) :
      3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card := by
    have hpoint : (rat j 0:ℝ)+ε∈Icc gapLo gapHi := by
      have hh := (hgeom j hj).2.2.2.2.2
        ⟨by linarith only [hε],le_rfl⟩
      change iteratedDeriv 2 (f 0) (x j 0)/2+ε∈Icc gapLo gapHi at hh
      rw [hlevel j (hGS hj) 0] at hh
      exact hh
    exact reference_gap_complete_sector_linearization_size e r v s (anchor j)
      hchart hr hEsize hRpos hQpos hN hd (Nat.cast_nonneg Uref) hBselect
      hTbase hDbase heps (hgeometry j hj).1 (hgeometry j hj).2.1 (hgeometry j hj).2.2
      (hanchor j (hGS hj)) (hcut j (hGS hj)) (hcount j (hGS hj))
      (fun z hz => hdenregion z hz 0) hcoord hgapWidth hreferenceEndpoint hpoint
      hselectedLinear hsize hDupper (hends j hj).1 (hends j hj).2 hsign
  obtain ⟨S₀,hS₀G,hGmass,hbound⟩ := hrest hD hΔ hdenregion hends hsector hBsize
  have htotal : S.card ≤ 105+17*S₀.card := by
    calc
      S.card ≤ 6+G.card := hS6G
      _ ≤ 6+(99+17*S₀.card) := Nat.add_le_add_left hGmass 6
      _ = 105+17*S₀.card := by simp only [←Nat.add_assoc]
  refine ⟨S₀,hS₀G.trans hGS,htotal,?_⟩
  intro Blabels Γ L C Cfirst Csecond Ccount
  change |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
    (G.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) at hbound
  rcases hbound with hentry | hcountG
  · exact Or.inl hentry
  · right
    have hmass : (S.card:ℝ) ≤ 6+(G.card:ℝ) := by exact_mod_cast hS6G
    linarith only [hmass,hcountG]

example
    (e r v s : ℤ) (anchor : ℚ)
    {q ε E R Q N d l w gapLo gapHi U B D D₀ Ct : ℝ}
    (hdet : v*r-e*s=1) (hr : r ≠ 0)
    (hE : 0 < E) (hR : 0 < R) (hQ : 0 < Q) (hN : 0 < N)
    (hd : 0 < d) (hU : 0 ≤ U) (hB : 0 < B)
    (hCt : 0 ≤ Ct) (hD₀ : 0 ≤ D₀) (heps : ε=E/R^2)
    (hminus : 0 < (r:ℝ)*(q-ε)-e)
    (hplus : 0 < (r:ℝ)*(q+ε)-e)
    (hdyad : max ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e) ≤
      2*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e))
    (hanchor : |(anchor:ℝ)-q| ≤ ε)
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3)
    (hcount : 256 ≤ (2*ε)*(Q/3)*anchor.den)
    (hden : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d)
    (hgap : gapHi-gapLo ≤ 7*U/(2*R^2))
    (hendpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hpoint : q+ε∈Icc gapLo gapHi)
    (hselected : B*U*Q ≤ N)
    (hmargin : 2*3840*128^2*105*(D₀+64*Ct*E^2) ≤ B*E)
    (hD : D ≤ D₀*Q/N) :
    let α := ((v:ℝ)-s*(q+ε))/((r:ℝ)*(q+ε)-e)
    let β := ((v:ℝ)-s*(q-ε))/((r:ℝ)*(q-ε)-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*(q-ε)-e) ((r:ℝ)*(q+ε)-e)⌋₊
    let S := if 0 < α then HuxleyLinearForm.fareySector K α β
      else (HuxleyLinearForm.fareySector K (-β) (-α)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let η := D+(K:ℝ)*(Ct*R^4/(N*d^3))*(β-α)^2
    α∈Icc l w → β∈Icc l w → (0 < α ∨ β < 0) →
    3840*128*η*((max |α| |β|)*(K:ℝ))*(K:ℝ) < S.card :=
  HuxleyCertifiedFamilyScratch.reference_gap_complete_sector_linearization_size e r v s anchor (q:=q) (ε:=ε) (E:=E) (R:=R) (Q:=Q) (N:=N) (d:=d) (l:=l) (w:=w) (gapLo:=gapLo) (gapHi:=gapHi) (U:=U) (B:=B) (D:=D) (D₀:=D₀) (Ct:=Ct) hdet hr hE hR hQ hN hd hU hB hCt hD₀ heps hminus hplus hdyad hanchor hcut hcount hden hcoord hgap hendpoint hpoint hselected hmargin hD

example
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ)
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
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=gapLo) ∨
      ((r:ℝ) < 0 ∧ (e:ℝ)/r=gapHi))
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
    (hwideL : ∀ j∈S, ∀ i, x j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ j∈S, ∀ i, x j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    105+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
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
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈G, α j∈Icc l w ∧ β j∈Icc l w) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 105+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyCertifiedFamilyScratch.physicalModelPhase_actual_fourier_certified_reference_gap_count Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart horientation hd hBcut hs hrefSet hparentSet hsep hdenl hdenw hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hchartLeft hchartRight hRQ hselectedUpper hscaleTen hfamilyGap

end HuxleyCertifiedFamilyScratch

#print axioms HuxleyCertifiedFamilyScratch.reference_gap_complete_sector_linearization_size
#print axioms HuxleyCertifiedFamilyScratch.selected_reference_linear_budget
#print axioms HuxleyCertifiedFamilyScratch.physical_source_quartic_constants_nonneg
#print axioms HuxleyCertifiedFamilyScratch.physicalModelPhase_actual_fourier_certified_reference_gap_count
