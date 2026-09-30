import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyReferenceChartScratch

/-- Separation from the retained determinant-one parent gives a uniform
coordinate-height bound on either side of the actual reference gap.
The constant is 30, not the stronger unproved factor 2. -/
private theorem separated_farey_reference_chart_coordinate_bound
    (S : Finset ℝ) {δ a b e r v s z d : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hdet : v*r-e*s=1)
    (href : e/r∈S) (hparent : v/s∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|)
    (hgap : b-a ≤ 7*δ/2)
    (hendpoint : e/r=a ∨ e/r=b)
    (hd : 0 < d) (hden : d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hpoint : (e*z+v)/(r*z+s)∈Icc a b) :
    |r| * |z| ≤ 30*d := by
  let D := r*z+s
  let ξ := (e*z+v)/D
  have hD : 0 < D := hd.trans_le hden.1
  have hprod : 0 < |r*s| := abs_pos.mpr (mul_ne_zero hr hs)
  have hparentGap : |v/s-e/r|=1/|r*s| := by
    rw [div_sub_div _ _ hs hr,abs_div]
    have he : v*r-s*e=1 := by nlinarith only [hdet]
    rw [he,abs_one,mul_comm s r]
  have hne : v/s ≠ e/r := by
    apply sub_ne_zero.mp
    apply abs_pos.mp
    rw [hparentGap]
    exact one_div_pos.mpr hprod
  have hseparated := hsep _ hparent _ href hne
  rw [hparentGap] at hseparated
  have hproduct : δ*|r*s| < 4 := by
    have hh := (lt_div_iff₀ hprod).mp hseparated
    nlinarith only [hh]
  have hdist : |ξ-e/r| ≤ 7*δ/2 := by
    apply le_trans _ hgap
    rcases hendpoint with ha | hb
    · rw [ha,abs_of_nonneg (sub_nonneg.mpr hpoint.1)]
      linarith only [hpoint.2]
    · rw [hb,abs_of_nonpos (sub_nonpos.mpr hpoint.2)]
      linarith only [hpoint.1]
  have hfactor : |r*s| * |ξ-e/r| ≤ 14 := by
    have hh := mul_le_mul_of_nonneg_left hdist hprod.le
    nlinarith only [hh,hproduct]
  have hid : (r*s)*(ξ-e/r)*D=s := by
    dsimp only [ξ]
    field_simp
    dsimp only [D]
    nlinarith only [hdet]
  have hsbound : |s| ≤ 14*D := by
    rw [←hid,abs_mul,abs_mul,abs_of_pos hD]
    exact mul_le_mul_of_nonneg_right hfactor hD.le
  calc
    |r| * |z| = |D-s| := by rw [←abs_mul]; congr 1; dsimp only [D]; ring
    _ ≤ |D|+|s| := abs_sub _ _
    _ = D+|s| := by rw [abs_of_pos hD]
    _ ≤ 15*D := by linarith only [hsbound]
    _ ≤ 30*d := by linarith only [hden.2]

theorem quartic_weighted_coefficient_budget_of_bounded_source_chart
    {C J μ N R r s d l w Bcut Kcoord : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ Kcoord*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : (2*Kcoord+1)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
  intro U
  let dl := r*l+s
  let r₀ := |r|
  have hr₀ : 0 < r₀ := abs_pos.mpr hr
  have hdl : 0 < dl := hd.trans_le (hdlo.trans (min_le_left _ _))
  have hdlhi : dl ≤ 2*d := (le_max_left _ _).trans hdhi
  have hdwlo : d ≤ r*w+s := hdlo.trans (min_le_right _ _)
  have hdwhi : r*w+s ≤ 2*d := (le_max_right _ _).trans hdhi
  have hG' : 1/(3*μ*r₀*dl) ≤ r₀*N^2/(Bcut*R^2) := by
    change |1/(3*μ*r*dl)| ≤ r₀*N^2/(Bcut*R^2) at hG
    simpa only [abs_div,abs_one,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_of_pos hμ,abs_of_pos hdl] using hG
  have hμmul : 6*μ*N*R^2 ≤ J := by
    have hh := (le_div_iff₀ (show 0 < 6*N*R^2 by positivity)).mp hμupper
    nlinarith only [hh]
  have hGclear : Bcut*R^2 ≤ (r₀*N^2)*(3*μ*r₀*dl) := by
    have hh := (div_le_div_iff₀
      (show 0 < 3*μ*r₀*dl by positivity)
      (show 0 < Bcut*R^2 by positivity)).mp hG'
    simpa only [one_mul] using hh
  have hGfour : Bcut*R^4 ≤ (3*μ*N*R^2)*(r₀^2*dl*N) := by
    have hh := mul_le_mul_of_nonneg_right hGclear (sq_nonneg R)
    nlinarith only [hh]
  have hμhalf : 3*μ*N*R^2 ≤ J/2 := by nlinarith only [hμmul]
  have hupper : Bcut*R^4 ≤ J*r₀^2*d*N := by
    have hh := mul_le_mul_of_nonneg_right hμhalf
      (show 0 ≤ r₀^2*dl*N by positivity)
    have hh' := mul_le_mul_of_nonneg_left hdlhi
      (show 0 ≤ J*r₀^2*N/2 by positivity)
    nlinarith only [hGfour,hh,hh']
  have hsmall : (2*Kcoord+1)*C*R^4 ≤ N*r₀^2*d := by
    have hh := mul_le_mul_of_nonneg_right hBsize (pow_nonneg hR.le 4)
    have he : J*((2*Kcoord+1)*C*R^4) ≤ J*(N*r₀^2*d) := by nlinarith only [hh,hupper]
    exact (mul_le_mul_iff_right₀ hJ).mp he
  have hdiff : w-l ≤ d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    have hdllo : d ≤ r*l+s := hdlo.trans (min_le_left _ _)
    rcases le_total 0 r with hsign | hsign
    · dsimp only [r₀]
      rw [abs_of_nonneg hsign]
      nlinarith only [hdllo,hdwhi]
    · dsimp only [r₀]
      rw [abs_of_nonpos hsign]
      change r*l+s ≤ 2*d at hdlhi
      nlinarith only [hdwlo,hdlhi]
  have hwbound : max |l| |w| ≤ Kcoord*d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    nlinarith only [hcoord]
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
    calc
      _ ≤ U*(d/r₀)*(Kcoord*d/r₀+(d/r₀)/2) := by gcongr
      _ = (2*Kcoord+1)*C*R^4/(2*N*r₀^2*d) := by dsimp only [U]; field_simp
      _ ≤ _ := by
        apply (div_le_iff₀ (show 0 < 2*N*r₀^2*d by positivity)).mpr
        nlinarith only [hsmall]
  exact hheight


private theorem nat_coordinate_budget
    {Kcoord : ℕ}
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
  exact quartic_weighted_coefficient_budget_of_bounded_source_chart
    hC hJ hμ hN hR hr hd hlw hdlo hdhi hcoord hμupper hBcut
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hBsize) hG

example
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  nat_coordinate_budget hC hJ hμ hN hR hr hd hlw hdlo hdhi hcoord hμupper hBcut hBsize hG



/-- Integer-height control on the actual source chart includes positive,
negative and zero numerators. Zero slope contributes only its literal label. -/
theorem quartic_phase_signed_integer_height_source_cutoff_coefficient_count
    {Kcoord : ℕ}
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) := by
  classical
  intro U g h φ y Z hx₀ hy hcurv hres
  have hlw : l ≤ w := hx₀.1.1.trans hx₀.1.2
  have hweighted := quartic_weighted_coefficient_budget_of_bounded_source_chart
    hC hJ hμ hN hR hr hd hlw
    (le_min (hden l ⟨le_rfl,hlw⟩).1 (hden w ⟨hlw,le_rfl⟩).1)
    (max_le (hden l ⟨le_rfl,hlw⟩).2 (hden w ⟨hlw,le_rfl⟩).2)
    hcoord hμupper hBcut
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hBsize) hG
  let T := S.filter (fun i => (p i).1 ≠ 0)
  have ht (i) (hi : i∈T) : (1:ℝ) ≤ |((p i).1:ℝ)| := by
    exact_mod_cast Int.one_le_abs (Finset.mem_filter.mp hi).2
  have hband i (hi : i∈T) : |y i|∈Icc (1/P₂) P₁ := by
    have hiS := (Finset.mem_filter.mp hi).1
    have hu : (0:ℝ) < (p i).2 := by exact_mod_cast hp i hiS
    have huone : (1:ℝ) ≤ (p i).2 := by exact_mod_cast hp i hiS
    have htone := ht i hi
    have hP₁ : 0 ≤ P₁ := (zero_le_one.trans htone).trans (hheight i hiS).1
    change |((p i).1:ℝ)/(p i).2|∈Icc (1/P₂) P₁
    rw [abs_div,abs_of_pos hu]
    constructor
    · exact (one_div_le_one_div_of_le hu (hheight i hiS).2).trans
        (div_le_div_of_nonneg_right htone hu.le)
    · apply (div_le_iff₀ hu).mpr
      exact (hheight i hiS).1.trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left huone hP₁)
  let c := fun z => (round (ac-deriv φ z),round (bc-φ z+z*deriv φ z))
  have hcount : (T.image (fun i => c (y i))).card ≤
      5+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) := by
    have hh := quartic_phase_signed_subfamily_coefficient_color_count (ac:=ac) (bc:=bc) T y
      hμ.ne' hμ₁ hr hr₁ (fun z hz => (hd.trans_le (hden z hz).1).ne') hden₁
      (one_div_pos.mpr hP₂) hband hD hweighted hx₀
      (fun i hi => hy i (Finset.mem_filter.mp hi).1) hcurv
    rw [one_div,div_inv_eq_mul] at hh
    apply hh
    intro i hi
    have hiS := (Finset.mem_filter.mp hi).1
    have hu : (0:ℝ) < (p i).2 := by exact_mod_cast hp i hiS
    apply (hres i hiS).trans
    change D/(p i).2 ≤ D*|((p i).1:ℝ)/(p i).2|
    rw [abs_div,abs_of_pos hu,←mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left (ht i hi) hD₀]) hu.le
  have hsub : S.image (fun i => c (y i)) ⊆ {c 0} ∪ T.image (fun i => c (y i)) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    by_cases ht0 : (p i).1=0
    · have hy0 : y i=0 := by simp [y,ht0]
      exact Finset.mem_union_left _ (by simp [hy0])
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨hi,ht0⟩))
  change (S.image (fun i => c (y i))).card ≤ _
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_singleton] at hh
  omega


/-- The signed integer-height count selects eight actual physical
samples with occupied mass, reverse slope order and G-spacing. No
positive numerator or positive chart endpoint is required. -/
theorem physicalModelPhase_signed_height_common_coefficient_samples_with_mass
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v P₁ P₂ : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) := by
  classical
  intro U Blabels f y g h φ Z hroot hy₀ hy hcurv hres
  have hBpos : (0:ℝ) < Blabels := by dsimp [Blabels]; positivity
  have hselect :
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*((6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1):ℕ):ℝ)) ≤
        (j i.succ:ℝ)-(j i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/(16*((6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1):ℕ):ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ) := by
    let color := fun i => (round (ac-deriv φ (y i)),round (bc-φ (y i)+y i*deriv φ (y i)))
    let T := S.image color
    let Blabels : ℕ := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    have hBposN : 0 < Blabels := by dsimp [Blabels]; omega
    have hBpos : (0:ℝ) < Blabels := by exact_mod_cast hBposN
    have hc : T.card ≤ Blabels := quartic_phase_signed_integer_height_source_cutoff_coefficient_count S p
      hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hGcut
      hP₂ hD₀ hD hpt hheight hy₀ hy hcurv hres
    have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
    have htne : T.Nonempty := hsne.image color
    have hbudget : T.card • ((S.card:ℝ)/(Blabels:ℝ)) ≤ (S.card:ℝ) := by
      rw [nsmul_eq_mul]
      have hcR : (T.card:ℝ) ≤ Blabels := by exact_mod_cast hc
      calc
        _ ≤ (Blabels:ℝ)*((S.card:ℝ)/(Blabels:ℝ)) :=
          mul_le_mul_of_nonneg_right hcR (div_nonneg (Nat.cast_nonneg _) hBpos.le)
        _ = _ := by field_simp
    obtain ⟨c,_hc,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (fun i hi => Finset.mem_image_of_mem color hi) htne hbudget
    let V := S.filter (fun i => color i=c)
    have hcount' : (S.card:ℝ) ≤ (Blabels:ℝ)*(V.card:ℝ) := by
      change (S.card:ℝ)/(Blabels:ℝ) ≤ (V.card:ℝ) at hcount
      have hh := (div_le_iff₀ hBpos).mp hcount
      nlinarith only [hh]
    have hVN : S.card ≤ Blabels*V.card := by exact_mod_cast hcount'
    have hV : 32 ≤ V.card := by
      change 32*Blabels ≤ S.card at hS
      by_contra hh
      have hvsmall : V.card ≤ 31 := by omega
      have hmul := Nat.mul_le_mul_left Blabels hvsmall
      nlinarith only [hS,hVN,hmul,hBposN]
    obtain ⟨idx,hidx,hspacing⟩ := exists_eight_block_indices hV
    let emb := V.orderEmbOfFin rfl
    have hgap (a b : Fin V.card) (hab : a ≤ b) :
        (b.val:ℝ)-(a.val:ℝ) ≤ (emb b:ℝ)-(emb a:ℝ) := by
      have hsub : (Finset.Icc a b).image emb ⊆ Finset.Icc (emb a) (emb b) := by
        intro x hx
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
        have hz' := Finset.mem_Icc.mp hz
        exact Finset.mem_Icc.mpr ⟨emb.monotone hz'.1,emb.monotone hz'.2⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ emb.injective,Fin.card_Icc,Nat.card_Icc] at hh
      have hab' : a.val ≤ b.val := hab
      have he : emb a ≤ emb b := emb.monotone hab
      have hi : b.val+emb a ≤ emb b+a.val := by omega
      have hiR : (b.val:ℝ)+(emb a:ℝ) ≤ (emb b:ℝ)+(a.val:ℝ) := by exact_mod_cast hi
      linarith only [hiR]
    refine ⟨c.1,c.2,fun i => emb (idx i),emb.strictMono.comp hidx,?_,?_,?_⟩
    · intro i
      have hi := V.orderEmbOfFin_mem rfl (idx i)
      have hv := Finset.mem_filter.mp hi
      exact ⟨hv.1,congrArg Prod.fst hv.2,congrArg Prod.snd hv.2⟩
    · intro i
      have hab : idx i.castSucc ≤ idx i.succ := (hidx Fin.castSucc_lt_succ).le
      have hg := hgap _ _ hab
      have hs := hspacing i
      change (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        (emb (idx i.succ):ℝ)-(emb (idx i.castSucc):ℝ)-1
      calc
        _ ≤ (V.card:ℝ)/16 := by
          apply (div_le_div_iff₀ (by positivity : (0:ℝ)<16*(Blabels:ℝ))
            (by norm_num : (0:ℝ)<16)).mpr
          nlinarith only [hcount']
        _ ≤ (idx i.succ).val-(idx i.castSucc).val-1 := hs
        _ ≤ _ := by linarith only [hg]
    · intro i
      let D := S.filter (fun n => emb (idx i.castSucc)<n ∧ n<emb (idx i.succ))
      have hsub : (Finset.Ioo (idx i.castSucc) (idx i.succ)).image emb ⊆ D := by
        intro n hn
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
        have hz' := Finset.mem_Ioo.mp hz
        have hm := V.orderEmbOfFin_mem rfl z
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,
          emb.strictMono hz'.1,emb.strictMono hz'.2⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ emb.injective,Fin.card_Ioo] at hh
      have hiN : (idx i.succ).val ≤ D.card+(idx i.castSucc).val+1 := by omega
      have hiR : ((idx i.succ).val:ℝ) ≤ (D.card:ℝ)+((idx i.castSucc).val:ℝ)+1 := by
        exact_mod_cast hiN
      have hs := hspacing i
      change (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (D.card:ℝ)
      calc
        _ ≤ (V.card:ℝ)/16 := by
          apply (div_le_div_iff₀ (by positivity : (0:ℝ)<16*(Blabels:ℝ))
            (by norm_num : (0:ℝ)<16)).mpr
          nlinarith only [hcount']
        _ ≤ (idx i.succ).val-(idx i.castSucc).val-1 := hs
        _ ≤ _ := by linarith only [hiR]
  obtain ⟨a,b,j,hj,hcoeff,hgap,hmass⟩ := hselect
  have hcount : (0:ℝ) < S.card := by
    exact_mod_cast (show 0 < S.card by omega)
  have hspace (i : Fin 7) : step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤
      x (j i.succ)-x (j i.castSucc) := by
    have hh := mul_le_mul_of_nonneg_left (hgap i) hstep.le
    change step*((S.card:ℝ)/(16*(Blabels:ℝ))) ≤
      step*((j i.succ:ℝ)-(j i.castSucc:ℝ)-1) at hh
    rw [←mul_div_assoc] at hh
    have hlow := (hwindow (j i.succ) (hcoeff i.succ).1).1
    have hhigh := (hwindow (j i.castSucc) (hcoeff i.castSucc).1).2
    nlinarith only [hh,hlow,hhigh]
  have hcoef : 0 < modelPhaseThirdLower σ*T/(6*μ*M^3) := by
    have hκ := modelPhaseThirdLower_pos hσ
    exact div_pos (mul_pos hκ hT) (mul_pos (mul_pos (by norm_num) hμ) (pow_pos hM 3))
  have hdenj (i : Fin 8) : 0 < r*y (j i)+s :=
    hd.trans_le (hden _ (hy _ (hcoeff i).1).1).1
  have hptj (i : Fin 8) : (0:ℝ) < (p (j i)).2 := by
    exact_mod_cast hpt _ (hcoeff i).1
  have hqj (i : Fin 8) : 0 < r*(p (j i)).1+s*(p (j i)).2 := by
    have he : r*(p (j i)).1+s*(p (j i)).2 =
        (r*y (j i)+s)*(p (j i)).2 := by
      dsimp only [y]
      field_simp [(hptj i).ne']
    rw [he]
    exact mul_pos (hdenj i) (hptj i)
  have hG (i : Fin 7) : modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
      minorArcCoordinate μ r s (y (j i.succ))-
      minorArcCoordinate μ r s (y (j i.castSucc)) := by
    have hxy : x (j i.castSucc) ≤ x (j i.succ) := by
      have hpos : 0 < step*(S.card:ℝ)/(16*(Blabels:ℝ)) :=
        div_pos (mul_pos hstep hcount) (by positivity)
      linarith only [hspace i,hpos]
    have hh := physicalModelPhase_minorArcCoordinate_growth
      ![((p (j i.castSucc)).1:ℝ),((p (j i.succ)).1:ℝ)]
      ![((p (j i.castSucc)).2:ℝ),((p (j i.succ)).2:ℝ)]
      hσ hδ hF hT hM hA hW (hx _ (hcoeff i.castSucc).1) (hx _ (hcoeff i.succ).1)
      hxy hμ hr
      (by
        intro z
        fin_cases z
        · exact (hptj i.castSucc).ne'
        · exact (hptj i.succ).ne')
      (by
        intro z
        fin_cases z
        · exact (hqj i.castSucc).ne'
        · exact (hqj i.succ).ne')
      hdet (hroot _ (hcoeff i.castSucc).1) (hroot _ (hcoeff i.succ).1)
    exact (mul_le_mul_of_nonneg_left (hspace i) hcoef.le).trans hh
  have hptAll j (hj' : j∈S) : (0:ℝ) < (p j).2 := by exact_mod_cast hpt j hj'
  have hdAll j (hj' : j∈S) : 0 < r*y j+s := hd.trans_le (hden _ (hy j hj').1).1
  have hqAll j (hj' : j∈S) : 0 < r*(p j).1+s*(p j).2 := by
    have he : r*(p j).1+s*(p j).2=(r*y j+s)*(p j).2 := by
      dsimp only [y]
      field_simp [(hptAll j hj').ne']
    rw [he]
    exact mul_pos (hdAll j hj') (hptAll j hj')
  have hantiAll : AntitoneOn y (S:Set ℕ) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact le_rfl
    have hstepR : (a:ℝ)+1 ≤ (b:ℝ) := by exact_mod_cast (show a+1 ≤ b by omega)
    have hxorder : x a ≤ x b := by
      have hh := mul_le_mul_of_nonneg_left hstepR hstep.le
      linarith only [hh,(hwindow a ha).2,(hwindow b hb).1]
    have hh := physicalModelPhase_minorArcCoordinate_growth
      ![((p a).1:ℝ),((p b).1:ℝ)] ![((p a).2:ℝ),((p b).2:ℝ)]
      hσ hδ hF hT hM hA hW (hx a ha) (hx b hb) hxorder hμ hr
      (by
        intro i
        fin_cases i
        · exact (hptAll a ha).ne'
        · exact (hptAll b hb).ne')
      (by
        intro i
        fin_cases i
        · exact (hqAll a ha).ne'
        · exact (hqAll b hb).ne')
      hdet (hroot a ha) (hroot b hb)
    have hg : 0 ≤ minorArcCoordinate μ r s (y b)-minorArcCoordinate μ r s (y a) :=
      (mul_nonneg hcoef.le (sub_nonneg.mpr hxorder)).trans hh
    rw [minorArcCoordinate_difference hμ.ne' hr (hdAll a ha).ne' (hdAll b hb).ne'] at hg
    have hn := (le_div_iff₀
      (show 0 < 3*μ*(r*y b+s)*(r*y a+s) by
        exact mul_pos (mul_pos (mul_pos (by norm_num) hμ) (hdAll b hb)) (hdAll a ha))).mp hg
    linarith only [hn]
  refine ⟨a,b,j,hj,hcoeff,?_,hspace,hG,hmass,hantiAll⟩
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  have hg : 0 < minorArcCoordinate μ r s (y (j i.succ))-
      minorArcCoordinate μ r s (y (j i.castSucc)) :=
    lt_of_lt_of_le (mul_pos hcoef (div_pos (mul_pos hstep hcount) (by positivity))) (hG i)
  rw [minorArcCoordinate_difference hμ.ne' hr (hdenj i.castSucc).ne' (hdenj i.succ).ne'] at hg
  have hn := (div_pos_iff_of_pos_right
    (show 0 < 3*μ*(r*y (j i.succ)+s)*(r*y (j i.castSucc)+s) by
      exact mul_pos (mul_pos (mul_pos (by norm_num) hμ) (hdenj i.succ)) (hdenj i.castSucc))).mp hg
  linarith only [hn]


/-- Actual signed-height occupied-window selection feeds the source-form
two-term First Condition under a SQUARE span budget. The proof derives
the samples and applies paired compression to their quartic witnesses;
no cubic-span restriction or occupied improved-Third certificate is used. -/
theorem physicalModelPhase_signed_height_square_span_first_condition
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
  have hbound := physicalModelPhase_quartic_matrix_long_block_first_condition
    (x₁:=fun q i => ρ i q) (α:=ac-a) (β:=bc-b) z Mat
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hxref
    (fun q hq i => (hρ i q hq).2.1) hr hdet
    (fun q hq i => (hden q (hsub hq) i).1)
    (fun q hq i => (hden q (hsub hq) i).2) hmono hscale hMat htransport hbase
    (fun q hq i => (hρ i q hq).2.2.1)
    (fun q hq i => (pow_le_pow_left₀ (abs_nonneg _)
      (hρ i q hq).2.2.2.2 2).trans (hsquare i))
    hgap (fun i => by
      have hh := hresnorm _ (hcoeff i.rev).1
      rw [(hcoeff i.rev).2.1,(hcoeff i.rev).2.2] at hh
      exact hh)

  exact hbound

/-- Both chart endpoints inherit the uniform factor 30 from the actual
separated reference set and retained determinant-one parent. -/
theorem separated_farey_reference_interval_coordinate_bound
    (S : Finset ℝ) {δ a b e r v s l w d : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hdet : v*r-e*s=1)
    (href : e/r∈S) (hparent : v/s∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|)
    (hgap : b-a ≤ 7*δ/2) (hendpoint : e/r=a ∨ e/r=b)
    (hd : 0 < d)
    (hdenl : d ≤ r*l+s ∧ r*l+s ≤ 2*d)
    (hdenw : d ≤ r*w+s ∧ r*w+s ≤ 2*d)
    (hleft : (e*l+v)/(r*l+s)∈Icc a b)
    (hright : (e*w+v)/(r*w+s)∈Icc a b) :
    |r| * max |l| |w| ≤ 30*d := by
  rw [mul_max_of_nonneg _ _ (abs_nonneg r)]
  exact max_le
    (separated_farey_reference_chart_coordinate_bound S hr hs hdet href hparent
      hsep hgap hendpoint hd hdenl hleft)
    (separated_farey_reference_chart_coordinate_bound S hr hs hdet href hparent
      hsep hgap hendpoint hd hdenw hright)

/-- Shared same-reference source consumer for the Section 9 First Condition. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition
    {Kcoord : ℕ}
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut) :
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
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
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
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  intro xref hxr Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hD hΔ
    hdenregion hleft hright hlarge hBsize hGcut Blabels Γ L C Cfirst Csecond
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
    rcases hnum j hj with hpos | hneg
    · have hh := inverseFarey_original_seed_enlarged_rectangle_signed
        hchart (hdl j hj) (hdw j hj) hpos ha hp (hdyad j hj) (hcut j hj)
        (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
      exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
    · have hh := inverseFarey_negative_original_seed_enlarged_rectangle
        hchart (hdl j hj) (hdw j hj) hneg ha hp (hdyad j hj) (hcut j hj)
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
    have hαβ : α j ≤ β j := (hrect j hj).2.1.trans (hrect j hj).2.2
    rcases hnum j hj with hpos | hneg
    · have hαpos : 0 < α j := div_pos hpos (hdw j hj)
      have hβpos : 0 < β j := hαpos.trans_le hαβ
      have hmax : max |α j| |β j|=β j := by
        rw [abs_of_pos hαpos,abs_of_pos hβpos,max_eq_right hαβ]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [if_pos hαpos,hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hpos
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
    · have hβneg : β j < 0 := div_neg_of_neg_of_pos hneg (hdl j hj)
      have hαneg : α j < 0 := hαβ.trans_lt hβneg
      have hmax : max |α j| |β j|= -α j := by
        rw [abs_of_neg hαneg,abs_of_neg hβneg,max_eq_left (neg_le_neg hαβ)]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [if_neg (not_lt.mpr hαneg.le),hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hneg
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
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
  have htransport : (ep 1:ℝ)=(Mat 0:ℝ)*(ep 0)+Mat 1*(rp 0) ∧
      (vp 1:ℝ)=(Mat 0:ℝ)*(vp 0)+Mat 1*(sp 0) ∧
      (rp 1:ℝ)=(Mat 2:ℝ)*(ep 0)+Mat 3*(rp 0) ∧
      (sp 1:ℝ)=(Mat 2:ℝ)*(vp 0)+Mat 3*(sp 0) := by
    simp [ep,vp,rp,sp,Int.cast_add,Int.cast_mul]
  have hbound := physicalModelPhase_signed_height_square_span_first_condition
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (Cres:=Cres) (Q:=(Q:ℝ)) (D:=D)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x Mat hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDeq.le hscale hA hW hxref
    hpheight (fun j hj => (hrect j hj).1) hpband hx hwindow hdisplacement hspan hsourcesquare
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hP₂ hCcurv hBcut hBsize hMatdet htransport hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  exact hbound

/-- Crossing slope zero costs at most three ACTUAL physical windows.
The near-boundary condition is derived from the inverse Farey endpoints. -/
private theorem physicalModelPhase_zero_crossing_window_count
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (S.filter (fun j => ¬(0 < α j ∨ β j < 0))).card ≤ 3 := by
  classical
  intro f q α β hcharts hends
  let Z : Finset ℝ := ({0}:Finset ℝ).filter (fun z => z∈Icc l w)
  have hc := physicalModelPhase_farey_boundary_crossing_count S Z x (v:=v)
    hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow
    (fun z hz => hregion z (Finset.mem_filter.mp hz).2) hcharts
  have he : S.filter (fun j => ¬(0 < α j ∨ β j < 0))=
      S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j)) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj,hnot⟩
      have hh := not_or.mp hnot
      have ha : α j ≤ 0 := le_of_not_gt hh.1
      have hb : 0 ≤ β j := le_of_not_gt hh.2
      refine ⟨hj,0,?_,ha,hb⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_singleton_self 0,
        (hends j hj).1.1.trans ha,hb.trans (hends j hj).2.2⟩
    · rintro ⟨hj,z,hz,haz,hzb⟩
      have hz0 : z=0 := Finset.mem_singleton.mp (Finset.mem_filter.mp hz).1
      subst z
      exact ⟨hj,fun hh => hh.elim (not_lt_of_ge haz) (not_lt_of_ge hzb)⟩
  rw [he]
  have hZ : Z.card ≤ 1 := by
    simpa only [Finset.card_singleton] using
      (Finset.card_filter_le (s:=({0}:Finset ℝ)) (p:=fun z => z∈Icc l w))
  exact hc.trans (by omega)

/-- The SAME actual Fourier family and constructed reference supply
the Section 9 two-term First Condition after actual curvature-cell
selection. The accepted physical span is square, not cubic; all source
sector/cutoff and displacement conditions remain explicit. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition
    {Kcoord : ℕ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
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
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
 classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
    hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
    (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hD hΔ
    hdenregion hends hlarge hBsize hGcut
  let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
  let U := Ccurv*R^4/(N*d^3)
  let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
    (μr 1) (νr 1) (rp 1) (sp 1) U
  have hκp : 0 < κ := modelPhaseThirdLower_pos hσ
  have hchartReal : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hεnonneg : 0 ≤ ε := by dsimp only [ε,Cphys]; positivity
  have hεsmall : 4*ε*R^2 ≤ κ := by
    have hCpos : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
    have heq : 4*ε*R^2=κ/(4*(Cphys+2)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num) hCpos)).mpr
    have hh : 1 ≤ 4*(Cphys+2) := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hκp.le
  obtain ⟨k,Spre,hSpreS,hSprecard,hcellsPre⟩ :=
    physicalModelPhase_farey_common_cell_selection_signed S Z (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall hεnonneg
      hchartReal
      (quarticCurvatureBoundaryRoots_card (μr 0) (νr 0) (rp 0) (sp 0)
        (μr 1) (νr 1) (rp 1) (sp 1) U)
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hh := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hh
        exact hd.trans_le hh)
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
  let good := fun j => 0 < α j ∨ β j < 0
  have hbad : (S.filter (fun j => ¬good j)).card ≤ 3 := by
    have hh := physicalModelPhase_zero_crossing_window_count S (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      (l:=l) (w:=w)
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hz' := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hz'
        exact hd.trans_le hz')
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    dsimp only [good,α,β,lo,hi]
    rw [hlevel j hj 0]
  let S₀ := Spre.filter good
  have hS₀S : S₀⊆S := (Finset.filter_subset _ _).trans hSpreS
  have hS₀card : S.card ≤ 99+17*S₀.card := by
    have hb : (Spre.filter (fun j => ¬good j)).card ≤ 3 := by
      apply le_trans (Finset.card_le_card ?_) hbad
      intro j hj
      exact Finset.mem_filter.mpr ⟨hSpreS (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
    have he := Finset.card_filter_add_card_filter_not (s:=Spre) good
    change S₀.card+(Spre.filter (fun j => ¬good j)).card=Spre.card at he
    omega
  have hcells j (hj : j∈S₀) := hcellsPre j (Finset.mem_filter.mp hj).1
  have hS₀ : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=99)
    calc
      _ = 99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) := by ring
      _ ≤ _ := hS.trans hS₀card
  have hcells' j (hj : j∈S₀) :
      α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
    have hh := hcells j hj
    change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈finiteBoundaryCell Z l w k ∧
      (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈finiteBoundaryCell Z l w k at hh
    rw [hlevel j (hS₀S hj) 0] at hh
    exact hh
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Blabels Γ L C Cfirst Csecond
  have hx j (hj : j∈S₀) := hx j (hS₀S hj)
  have hwindow j (hj : j∈S₀) := hwindow j (hS₀S hj)
  have hden j (hj : j∈S₀) := hden j (hS₀S hj)
  have hinv j (hj : j∈S₀) := hinv j (hS₀S hj)
  have hlevel j (hj : j∈S₀) := hlevel j (hS₀S hj)
  have hcolor j (hj : j∈S₀) := hcolor j (hS₀S hj)
  have hnear j (hj : j∈S₀) := hnear j (hS₀S hj)
  have hMatt j (hj : j∈S₀) := hMatt j (hS₀S hj)
  have hMatmap j (hj : j∈S₀) := hMatmap j (hS₀S hj)
  have hL j (hj : j∈S₀) := hL j (hS₀S hj)
  have hU j (hj : j∈S₀) := hU j (hS₀S hj)
  have hdl j (hj : j∈S₀) := hdl j (hS₀S hj)
  have hdw j (hj : j∈S₀) := hdw j (hS₀S hj)
  have hnum j (hj : j∈S₀) :
      0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0 := by
    rcases (Finset.mem_filter.mp hj).2 with hpos | hneg
    · left
      have hh := (lt_div_iff₀ (hdw j hj)).mp hpos
      simpa only [zero_mul] using hh
    · right
      have hh := (div_lt_iff₀ (hdl j hj)).mp hneg
      simpa only [zero_mul] using hh
  have hdyad j (hj : j∈S₀) := hdyad j (hS₀S hj)
  have hanchor j (hj : j∈S₀) := hanchor j (hS₀S hj)
  have hcut j (hj : j∈S₀) := hcut j (hS₀S hj)
  have hcount j (hj : j∈S₀) := hcount j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  have hbudget j (hj : j∈S₀) := hbudget j (hS₀S hj)
  have hlarge j (hj : j∈S₀) := hlarge j (hS₀S hj) (Finset.mem_filter.mp hj).2
  have hleft j (hj : j∈S₀) := (hcells' j hj).1
  have hright j (hj : j∈S₀) := (hcells' j hj).2
  exact physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition S₀ Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut
    hS₀ hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hdl hdw hnum hdyad
    hanchor hcut hcount xref
    (fun i => ⟨(mul_ne_zero_iff.mp (hxr i).1.ne').1,(hxr i).2.1,(hxr i).2.2.1⟩)
    Hspan hdisplacement hspan hbudget hD hΔ hdenregion hleft hright
    hlarge hBsize hGcut

/-- The square-span First Condition itself controls the whole actual
Fourier family, after an explicit small-entry alternative. This bypasses
transport of an improved Third estimate to intervening occupied points. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count
    {Kcoord : ℕ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
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
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
 classical
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hD hΔ
    hdenregion hends hsector hBsize hGcut
  obtain ⟨S₀,hS₀S,hS₀card,hfirst⟩ :=
    hconsumer Hspan hdisplacement hspan hbudget hD hΔ hdenregion hends hsector hBsize hGcut
  clear hlong hconsumer
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Blabels Γ L C Cfirst Csecond Ccount
  by_cases hsmallEntry : |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M
  · exact Or.inl hsmallEntry
  apply Or.inr
  have hS₀ : 32*Blabels ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=99)
    calc
      _ = 99+544*Blabels := by ring
      _ ≤ _ := hS.trans hS₀card
  have hBpos : (0:ℝ) < Blabels := by dsimp only [Blabels]; positivity
  have hBnat : 0 < Blabels := by exact_mod_cast hBpos
  have hScard : (0:ℝ) < S₀.card := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 32) hBnat).trans_le hS₀
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hL : 0 < L := mul_pos
    (div_pos hκ (mul_pos (mul_pos (by norm_num) hBpos) hCp)) hScard
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hsecond : 0 ≤ 2*Csecond*N*R^2/M := by
    dsimp only [Csecond]
    positivity
  have hcpos : 0 < |(Mat 2:ℝ)| := hsecond.trans_lt (lt_of_not_ge hsmallEntry)
  change |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M at hfirst
  have hsmallTerm : 2*(Csecond*N*R^2/M) < |(Mat 2:ℝ)| := by
    calc
      _ = 2*Csecond*N*R^2/M := by ring
      _ < _ := lt_of_not_ge hsmallEntry
  have hhalf : |(Mat 2:ℝ)|/2 ≤ Cfirst*R^4/(L^3*N^2) := by
    linarith only [hfirst,hsmallTerm]
  have hcube : |(Mat 2:ℝ)| *L^3*N^2 ≤ 2*Cfirst*R^4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < L^3*N^2)).mp hhalf
    nlinarith only [hh]
  have hcellcount : (S₀.card:ℝ) ≤ Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
    apply (le_div_iff₀ (by positivity : 0 < L^2*N^2*|(Mat 2:ℝ)|)).mpr
    have hLrel : (S₀.card:ℝ)=(16*(Blabels:ℝ)*Cphys/κ)*L := by
      dsimp only [L]
      field_simp
    rw [hLrel]
    calc
      _ = (16*(Blabels:ℝ)*Cphys/κ)*(|(Mat 2:ℝ)| *L^3*N^2) := by ring
      _ ≤ (16*(Blabels:ℝ)*Cphys/κ)*(2*Cfirst*R^4) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = _ := by dsimp only [Ccount]; ring
  have hmass : (S.card:ℝ) ≤ 99+17*(S₀.card:ℝ) := by exact_mod_cast hS₀card
  calc
    _ ≤ 99+17*(S₀.card:ℝ) := hmass
    _ ≤ 99+17*(Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcellcount (by norm_num))
    _ = _ := by ring

/-- The actual reference-gap family count derives the global physical
displacements, padded square Taylor budgets and source coordinate cutoff
at the SAME selected U and constructed reference under N^10 <= M^3 R^7.
The sector sign is derived after discarding at most three zero-crossing
windows. The original source matrix, selected U, labels and reference are
unchanged. Chart geometry, density and boundary buffers remain explicit. -/
theorem physicalModelPhase_actual_fourier_signed_selected_reference_gap_count
    {Kcoord : ℕ}
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
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
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
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
  have hlong := physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
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


/-- The actual separated reference set and retained Farey parent discharge
the chart-coordinate budget of the sign-free source-family count. Both
chart endpoints and their dyadic denominators are explicit geometric
inputs. The source cutoff constant is now 61*Ccurv*Cphys. -/
theorem physicalModelPhase_actual_fourier_separated_reference_gap_count
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
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
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
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
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
  have hcoord : |(r:ℝ)| * max |l| |w| ≤ 30*d :=
    separated_farey_reference_interval_coordinate_bound Refs
      (δ:=(Uref:ℝ)/R^2) (by exact_mod_cast hr) (by exact_mod_cast hs)
      (by exact_mod_cast hchart) hrefSet hparentSet hsep
      (hgapWidth.trans_eq (by ring)) hreferenceEndpoint hd hdenl hdenw
      hchartLeft hchartRight
  exact physicalModelPhase_actual_fourier_signed_selected_reference_gap_count (Kcoord:=30) Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap


example
    {C J μ N R r s d l w Bcut Kcoord : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ Kcoord*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : (2*Kcoord+1)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  HuxleyReferenceChartScratch.quartic_weighted_coefficient_budget_of_bounded_source_chart (C:=C) (J:=J) (μ:=μ) (N:=N) (R:=R) (r:=r) (s:=s) (d:=d) (l:=l) (w:=w) (Bcut:=Bcut) (Kcoord:=Kcoord) hC hJ hμ hN hR hr hd hlw hdlo hdhi hcoord hμupper hBcut hBsize hG

example
    {Kcoord : ℕ}
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  HuxleyReferenceChartScratch.quartic_phase_signed_integer_height_source_cutoff_coefficient_count (Kcoord:=Kcoord) (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (P₁:=P₁) (P₂:=P₂) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hP₂ hD₀ hD hp hheight

example
    {Kcoord : ℕ}
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v P₁ P₂ : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ (Kcoord:ℝ)*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : ((2*Kcoord+1:ℕ):ℝ)*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  HuxleyReferenceChartScratch.physicalModelPhase_signed_height_common_coefficient_samples_with_mass (Kcoord:=Kcoord) S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (D:=D) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (P₁:=P₁) (P₂:=P₂) (F:=F) (k:=k) hS hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hC hJ hN hR hd hcoord hμupper hBcut hBsize hGcut hP₂ hD₀ hD hheight hpt hx hwindow

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
  HuxleyReferenceChartScratch.physicalModelPhase_signed_height_square_span_first_condition (Kcoord:=Kcoord) S p x Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord hP₂ hCcurv hBcut hBsize hMat htransport

example
    (S : Finset ℝ) {δ a b e r v s l w d : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hdet : v*r-e*s=1)
    (href : e/r∈S) (hparent : v/s∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|)
    (hgap : b-a ≤ 7*δ/2) (hendpoint : e/r=a ∨ e/r=b)
    (hd : 0 < d)
    (hdenl : d ≤ r*l+s ∧ r*l+s ≤ 2*d)
    (hdenw : d ≤ r*w+s ∧ r*w+s ≤ 2*d)
    (hleft : (e*l+v)/(r*l+s)∈Icc a b)
    (hright : (e*w+v)/(r*w+s)∈Icc a b) :
    |r| * max |l| |w| ≤ 30*d :=
  HuxleyReferenceChartScratch.separated_farey_reference_interval_coordinate_bound S (δ:=δ) (a:=a) (b:=b) (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) (d:=d) hr hs hdet href hparent hsep hgap hendpoint hd hdenl hdenw hleft hright

example
    {Kcoord : ℕ}
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ (Kcoord:ℝ)*d) (hBcut : 0 < Bcut)
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
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    ((2*Kcoord+1:ℕ):ℝ)*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_selected_reference_gap_count (Kcoord:=Kcoord) Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap

example
    (Uref : ℕ) (Refs : Finset ℝ) {Bselect gapLo gapHi : ℝ}
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
    (hd : 0 < d) (hBcut : 0 < Bcut)
    (hs : s ≠ 0)
    (hrefSet : (e:ℝ)/r∈Refs) (hparentSet : (v:ℝ)/s∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hdenl : d ≤ (r:ℝ)*l+s ∧ (r:ℝ)*l+s ≤ 2*d)
    (hdenw : d ≤ (r:ℝ)*w+s ∧ (r:ℝ)*w+s ≤ 2*d)
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
    (hchartRight : ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    61*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_separated_reference_gap_count Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hBcut hs hrefSet hparentSet hsep hdenl hdenw hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hchartRight hRQ hselectedUpper hscaleTen hfamilyGap

example
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  HuxleyReferenceChartScratch.quartic_phase_signed_integer_height_source_cutoff_coefficient_count (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (P₁:=P₁) (P₂:=P₂) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hP₂ hD₀ hD hp hheight

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v P₁ P₂ : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  HuxleyReferenceChartScratch.physicalModelPhase_signed_height_common_coefficient_samples_with_mass S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (D:=D) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (P₁:=P₁) (P₂:=P₂) (F:=F) (k:=k) hS hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hC hJ hN hR hd hcoord hμupper hBcut hBsize hGcut hP₂ hD₀ hD hheight hpt hx hwindow

example
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
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut)
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
  HuxleyReferenceChartScratch.physicalModelPhase_signed_height_square_span_first_condition S p x Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord hP₂ hCcurv hBcut hBsize hMat htransport

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
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_selected_reference_gap_count Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap


end HuxleyReferenceChartScratch

#print axioms HuxleyReferenceChartScratch.separated_farey_reference_chart_coordinate_bound
#print axioms HuxleyReferenceChartScratch.quartic_weighted_coefficient_budget_of_bounded_source_chart
#print axioms HuxleyReferenceChartScratch.quartic_phase_signed_integer_height_source_cutoff_coefficient_count
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_signed_height_common_coefficient_samples_with_mass
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_signed_height_square_span_first_condition
#print axioms HuxleyReferenceChartScratch.separated_farey_reference_interval_coordinate_bound
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_signed_selected_reference_gap_count
#print axioms HuxleyReferenceChartScratch.physicalModelPhase_actual_fourier_separated_reference_gap_count
