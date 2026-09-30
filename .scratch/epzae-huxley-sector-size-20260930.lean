import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleySectorSizeScratch

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
  HuxleySectorSizeScratch.reference_gap_complete_sector_linearization_size e r v s anchor (q:=q) (ε:=ε) (E:=E) (R:=R) (Q:=Q) (N:=N) (d:=d) (l:=l) (w:=w) (gapLo:=gapLo) (gapHi:=gapHi) (U:=U) (B:=B) (D:=D) (D₀:=D₀) (Ct:=Ct) hdet hr hE hR hQ hN hd hU hB hCt hD₀ heps hminus hplus hdyad hanchor hcut hcount hden hcoord hgap hendpoint hpoint hselected hmargin hD

end HuxleySectorSizeScratch

#print axioms HuxleySectorSizeScratch.source_sector_linearization_error_bound
#print axioms HuxleySectorSizeScratch.source_sector_weighted_error_bound
#print axioms HuxleySectorSizeScratch.source_sector_height_width_bound
#print axioms HuxleySectorSizeScratch.reference_gap_complete_sector_linearization_size
