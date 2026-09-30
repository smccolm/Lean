import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyPairedChartScratch

private theorem logarithmic_quarter_band_partition
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) {a₀ cap : ℝ}
    (ha₀ : 0 < a₀)
    (ha : ∀ j∈S, a₀ ≤ a j ∧ a j ≤ cap*a₀) :
    let color := fun j => ⌊Real.logb (5/4) (a j/a₀)⌋₊
    (S.image color).card ≤ ⌊Real.logb (5/4) cap⌋₊+1 ∧
    ∀ j∈S, a₀*(5/4:ℝ)^(color j) ≤ a j ∧
      a j ≤ (5/4)*(a₀*(5/4:ℝ)^(color j)) := by
  classical
  intro color
  have hbase : (1:ℝ) < 5/4 := by norm_num
  have hjpos j (hj : j∈S) : 0 < a j := ha₀.trans_le (ha j hj).1
  have hratio j (hj : j∈S) : 1 ≤ a j/a₀ :=
    (le_div_iff₀ ha₀).mpr (by simpa only [one_mul] using (ha j hj).1)
  constructor
  · have hs : S.image color ⊆ Finset.range (⌊Real.logb (5/4) cap⌋₊+1) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      have hu : a j/a₀ ≤ cap := (div_le_iff₀ ha₀).mpr (ha j hj).2
      have hh := Real.logb_le_logb_of_le hbase (div_pos (hjpos j hj) ha₀) hu
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hh))
    simpa only [Finset.card_range] using Finset.card_le_card hs
  · intro j hj
    have hp : 0 < a j/a₀ := div_pos (hjpos j hj) ha₀
    have hlog : 0 ≤ Real.logb (5/4) (a j/a₀) :=
      Real.logb_nonneg hbase (hratio j hj)
    have hlo := (Real.le_logb_iff_rpow_le hbase hp).mp (Nat.floor_le hlog)
    have hhi := (Real.logb_lt_iff_lt_rpow hbase hp).mp
      (Nat.lt_floor_add_one (Real.logb (5/4) (a j/a₀)))
    change (5/4:ℝ)^(color j:ℝ) ≤ a j/a₀ at hlo
    rw [Real.rpow_natCast] at hlo
    have hhi' : a j/a₀ < (5/4:ℝ)^(color j+1) := by
      rw [←Nat.cast_one,←Nat.cast_add,Real.rpow_natCast] at hhi
      exact hhi
    constructor
    · have hh := (le_div_iff₀ ha₀).mp hlo
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ ha₀).mp hhi'
      rw [pow_succ] at hh
      nlinarith only [hh]

private theorem inverse_paired_chart_point_bounds
    {e r v s c t q y ε a₀ : ℝ}
    (hdet : v*r-e*s=1)
    (ha₀ : 0 < a₀)
    (hcentral : 12*|r| *ε < r*q-e)
    (hband : a₀ ≤ r*q-e ∧ r*q-e ≤ (5/4)*a₀)
    (hnear : |c*q+t-1| ≤ 1/24)
    (hsmall : |c| *ε ≤ 1/24)
    (hy : |y-q| ≤ ε) :
    let z := (v-s*y)/(r*y-e)
    let d := 2/(3*a₀)
    0 < r*y-e ∧
      (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
      (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧
        (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) := by
  intro z d
  have hdiff : |r*(y-q)| ≤ |r| *ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg r)
  have habs := abs_le.mp hdiff
  have hAlo : (11/12)*a₀ ≤ r*y-e := by
    nlinarith only [hcentral,hband.1,habs.1]
  have hAhi : r*y-e ≤ (65/48)*a₀ := by
    nlinarith only [hcentral,hband.2,habs.2]
  have hA : 0 < r*y-e := lt_of_lt_of_le (by positivity) hAlo
  have hc : |c*(y-q)| ≤ 1/24 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg c)).trans hsmall
  have ht : |c*y+t-1| ≤ 1/12 := by
    calc
      _ = |(c*q+t-1)+c*(y-q)| := by congr 1; ring
      _ ≤ |c*q+t-1|+|c*(y-q)| := abs_add_le _ _
      _ ≤ 1/12 := by linarith only [hnear,hc]
  have ht' := abs_le.mp ht
  have hid : r*z+s=1/(r*y-e) := by
    dsimp only [z]
    field_simp
    nlinarith only [hdet]
  have hid₁ : (c*e+t*r)*z+(c*v+t*s)=(c*y+t)/(r*y-e) := by
    dsimp only [z]
    field_simp
    linear_combination (c*y+t)*hdet
  rw [hid,hid₁]
  refine ⟨hA,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · apply (le_div_iff₀ hA).mpr
    dsimp only [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAhi,ha₀]
  · apply (div_le_iff₀ hA).mpr
    dsimp only [d]
    rw [show 2*(2/(3*a₀))*(r*y-e)=4*(r*y-e)/(3*a₀) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAlo,ha₀]
  · apply (le_div_iff₀ hA).mpr
    dsimp only [d]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAhi,ha₀,mul_nonneg ha₀.le (show 0 ≤ c*y+t-11/12 by linarith only [ht'.1])]
  · apply (div_le_iff₀ hA).mpr
    dsimp only [d]
    rw [show 2*(2/(3*a₀))*(r*y-e)=4*(r*y-e)/(3*a₀) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 3*a₀)).mpr
    nlinarith only [hAlo,ha₀,mul_nonneg ha₀.le (show 0 ≤ 13/12-(c*y+t) by linarith only [ht'.2])]

private theorem physical_reference_gap_twelve_radius_selection
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base a b e r : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (horientation : (0 < r ∧ e/r=a) ∨ (r < 0 ∧ e/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    (∀ j∈S, q j∈Icc a b) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 6+S₀.card ∧ ∀ j∈S₀,
      a+12*ε < q j ∧ q j < b-12*ε ∧
      12*|r| *ε < r*q j-e := by
  classical
  intro ε f q hgap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+3 := by positivity
  let badA := S.filter (fun j => |q j-a| ≤ 12*ε)
  let badB := S.filter (fun j => |q j-b| ≤ 12*ε)
  let bad := fun j => |q j-a| ≤ 12*ε ∨ |q j-b| ≤ 12*ε
  let good := S.filter (fun j => ¬ bad j)
  have hrad : 4*(12*ε)*R^2 ≤ modelPhaseThirdLower σ := by
    have he : 4*(12*ε)*R^2=3*modelPhaseThirdLower σ/(σ*(σ+1)+3) := by
      dsimp only [ε]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hC).mpr
    have hh : 0 ≤ (σ*(σ+1))*modelPhaseThirdLower σ := by positivity
    nlinarith only [hh,hκ]
  have hcountA : badA.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badA x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have hcountB : badB.card ≤ 3 :=
    physicalModelPhase_curvature_boundary_window_count badB x
      hσ hδ hF hT hM hN hR hA hW hphase hrad
      (fun j hj => hx j (Finset.mem_filter.mp hj).1)
      (fun j hj => hwindow j (Finset.mem_filter.mp hj).1)
      (fun j hj => (Finset.mem_filter.mp hj).2)
  have he : S.filter bad=badA∪badB := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,bad,badA,badB]
    tauto
  have hbad : (S.filter bad).card ≤ 6 := by
    rw [he]
    exact (Finset.card_union_le _ _).trans (by omega)
  refine ⟨good,Finset.filter_subset _ _,?_,?_⟩
  · have hh := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at hh
    omega
  · intro j hj
    obtain ⟨hjS,hgood⟩ := Finset.mem_filter.mp hj
    have hleft : 12*ε < q j-a := by
      have hh : ¬ |q j-a| ≤ 12*ε := fun h => hgood (Or.inl h)
      rw [abs_of_nonneg (sub_nonneg.mpr (hgap j hjS).1)] at hh
      exact lt_of_not_ge hh
    have hright : 12*ε < b-q j := by
      have hh : ¬ |q j-b| ≤ 12*ε := fun h => hgood (Or.inr h)
      rw [abs_of_nonpos (sub_nonpos.mpr (hgap j hjS).2)] at hh
      linarith only [lt_of_not_ge hh]
    have hcentral : 12*|r| *ε < r*q j-e := by
      rcases horientation with ⟨hr,href⟩ | ⟨hr,href⟩
      · have heq : e=a*r := (div_eq_iff hr.ne').mp href
        rw [abs_of_pos hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hleft hr]
      · have heq : e=b*r := (div_eq_iff hr.ne).mp href
        rw [abs_of_neg hr,heq]
        nlinarith only [mul_lt_mul_of_pos_left hright (neg_pos.mpr hr)]
    exact ⟨by linarith only [hleft],by linarith only [hright],hcentral⟩

private theorem affine_interval_bounds
    {r s l w d z : ℝ} (hz : z∈Icc l w)
    (hl : d ≤ r*l+s ∧ r*l+s ≤ 2*d)
    (hw : d ≤ r*w+s ∧ r*w+s ≤ 2*d) :
    d ≤ r*z+s ∧ r*z+s ≤ 2*d := by
  rcases le_total 0 r with hr | hr
  · constructor
    · nlinarith only [hl.1,mul_nonneg hr (sub_nonneg.mpr hz.1)]
    · nlinarith only [hw.2,mul_nonneg hr (sub_nonneg.mpr hz.2)]
  · constructor
    · nlinarith only [hw.1,mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hz.2)]
    · nlinarith only [hl.2,mul_nonpos_of_nonpos_of_nonneg hr (sub_nonneg.mpr hz.1)]

private theorem reference_gap_quarter_band_chart_cover
    {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    {e r v s c t ε a b : ℝ}
    (hdet : v*r-e*s=1) (hr : r ≠ 0) (hε : 0 < ε)
    (hcentral : ∀ j∈S, 12*|r| *ε < r*q j-e)
    (hupper : ∀ j∈S, r*q j-e ≤ |r| *(b-a))
    (hinterval : ∀ j∈S, Icc (q j-ε) (q j+ε) ⊆ Icc a b)
    (hnear : ∀ j∈S, |c*q j+t-1| ≤ 1/24)
    (hsmall : |c| *ε ≤ 1/24) :
    let color := fun j => ⌊Real.logb (5/4) ((r*q j-e)/(12*|r| *ε))⌋₊
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (S.image color).card ≤ ⌊Real.logb (5/4) ((b-a)/(12*ε))⌋₊+1 ∧
    ∀ n∈S.image color, ∃ d l w : ℝ, 0 < d ∧ l ≤ w ∧
      (∀ j∈S, color j=n → α j∈Icc l w ∧ β j∈Icc l w) ∧
      (∀ z∈Icc l w,
        (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
        (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧ (c*e+t*r)*z+(c*v+t*s) ≤ 2*d)) ∧
      (e*l+v)/(r*l+s)∈Icc a b ∧ (e*w+v)/(r*w+s)∈Icc a b := by
  classical
  intro color α β
  let a₀ := 12*|r| *ε
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hr)) hε
  have hband := logarithmic_quarter_band_partition S (fun j => r*q j-e) ha₀
    (cap:=(b-a)/(12*ε)) (by
      intro j hj
      refine ⟨(hcentral j hj).le,?_⟩
      calc
        r*q j-e ≤ |r| *(b-a) := hupper j hj
        _ = ((b-a)/(12*ε))*a₀ := by dsimp only [a₀]; field_simp)
  refine ⟨hband.1,?_⟩
  intro n hn
  let G := S.filter (fun j => color j=n)
  obtain ⟨j₀,hj₀,hcolor₀⟩ := Finset.mem_image.mp hn
  have hG : G.Nonempty := ⟨j₀,Finset.mem_filter.mpr ⟨hj₀,hcolor₀⟩⟩
  let V := (G.image α)∪(G.image β)
  have hV : V.Nonempty := (hG.image α).mono (Finset.subset_union_left)
  let l := V.min' hV
  let w := V.max' hV
  let scale := a₀*(5/4:ℝ)^n
  let d := 2/(3*scale)
  have hscale : 0 < scale := by dsimp only [scale]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpoint j (hj : j∈G) y (hy : |y-q j| ≤ ε) :
      let z := (v-s*y)/(r*y-e)
      0 < r*y-e ∧
        (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
        (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧
          (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) := by
    obtain ⟨hjS,hcolor⟩ := Finset.mem_filter.mp hj
    have hb := hband.2 j hjS
    change a₀*(5/4:ℝ)^(color j) ≤ r*q j-e ∧
      r*q j-e ≤ (5/4)*(a₀*(5/4:ℝ)^(color j)) at hb
    rw [hcolor] at hb
    exact inverse_paired_chart_point_bounds hdet hscale (hcentral j hjS)
      hb (hnear j hjS) hsmall hy
  have hVpoint z (hz : z∈V) :
      (d ≤ r*z+s ∧ r*z+s ≤ 2*d) ∧
      (d ≤ (c*e+t*r)*z+(c*v+t*s) ∧ (c*e+t*r)*z+(c*v+t*s) ≤ 2*d) ∧
      (e*z+v)/(r*z+s)∈Icc a b := by
    have hex : ∃ j∈G, ∃ y, |y-q j| ≤ ε ∧ z=(v-s*y)/(r*y-e) := by
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        exact ⟨j,hj,q j+ε,by simpa only [add_sub_cancel_left,abs_of_pos hε] using (le_rfl : ε ≤ ε),rfl⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        exact ⟨j,hj,q j-ε,by simpa only [sub_sub_cancel_left,abs_neg,abs_of_pos hε] using (le_rfl : ε ≤ ε),rfl⟩
    obtain ⟨j,hj,y,hy,rfl⟩ := hex
    have hh := hpoint j hj y hy
    refine ⟨hh.2.1,hh.2.2,?_⟩
    have he : (e*((v-s*y)/(r*y-e))+v)/(r*((v-s*y)/(r*y-e))+s)=y := by
      apply (div_eq_iff (hd.trans_le hh.2.1.1).ne').mpr
      have hmul : (r*y-e)*(r*y-e)⁻¹=1 := mul_inv_cancel₀ hh.1.ne'
      simp only [div_eq_mul_inv]
      linear_combination -(v-s*y)*hmul
    rw [he]
    apply hinterval j (Finset.mem_filter.mp hj).1
    obtain ⟨hyl,hyu⟩ := abs_le.mp hy
    constructor <;> linarith only [hyl,hyu]
  have hlmem : l∈V := Finset.min'_mem V hV
  have hwmem : w∈V := Finset.max'_mem V hV
  have hl := hVpoint l hlmem
  have hw := hVpoint w hwmem
  refine ⟨d,l,w,hd,Finset.min'_le V w hwmem,?_,?_,hl.2.2,hw.2.2⟩
  · intro j hj hcolor
    have hjG : j∈G := Finset.mem_filter.mpr ⟨hj,hcolor⟩
    have hα : α j∈V := Finset.mem_union_left _ (Finset.mem_image_of_mem α hjG)
    have hβ : β j∈V := Finset.mem_union_right _ (Finset.mem_image_of_mem β hjG)
    exact ⟨⟨Finset.min'_le V _ hα,Finset.le_max' V _ hα⟩,
      ⟨Finset.min'_le V _ hβ,Finset.le_max' V _ hβ⟩⟩
  · intro z hz
    exact ⟨affine_interval_bounds hz hl.1 hw.1,
      affine_interval_bounds hz hl.2.1 hw.2.1⟩

/-- The actual physical family and the existing rational narrow-band
coloring construct logarithmically many common factor-two paired charts.
Only six physical windows are discarded; no paired chart, endpoint
denominator or chart-cardinality certificate is assumed. -/
theorem physicalModelPhase_same_color_reference_gap_paired_chart_cover
    (S : Finset ℕ) (x : ℕ → ℝ) (rat : ℕ → Fin 2 → ℚ)
    (Q K₀ : ℕ) [NeZero K₀] (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M A W N R base a b lambda U θ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRN : R ≤ N) (hQ : 0 < Q)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=a) ∨ ((r:ℝ) < 0 ∧ (e:ℝ)/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hlambda : 0 < lambda) (hU : 0 ≤ U)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ U)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hgap : ∀ j∈S, (rat j 0:ℝ)∈Icc a b)
    (hMatt : ∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=
      ((rat j 1).den:ℝ)/(rat j 0).den) :
    let f := heathBrownPhysicalPhase F T M A 1
    (∀ j∈S, iteratedDeriv 2 f (x j)/2=(rat j 0:ℝ)) →
    let color := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, color j 0=color j 1) →
    (((S ×ˢ (Finset.univ : Finset (Fin 2))).image
      (fun ji => color ji.1 ji.2)).card:ℝ) ≤ (4/θ+3)*(4*U/(lambda*θ)+3) ∧
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let chartColor := fun j => ⌊Real.logb (5/4)
      (((r:ℝ)*(rat j 0:ℝ)-e)/(12*|(r:ℝ)| *ε))⌋₊
    let α := fun j => ((v:ℝ)-s*((rat j 0:ℝ)+ε))/((r:ℝ)*((rat j 0:ℝ)+ε)-e)
    let β := fun j => ((v:ℝ)-s*((rat j 0:ℝ)-ε))/((r:ℝ)*((rat j 0:ℝ)-ε)-e)
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
      (G.image chartColor).card ≤ ⌊Real.logb (5/4) ((b-a)/(12*ε))⌋₊+1 ∧
      ∀ n∈G.image chartColor, ∃ d l w : ℝ, 0 < d ∧ l ≤ w ∧
        (∀ j∈G, chartColor j=n → α j∈Icc l w ∧ β j∈Icc l w) ∧
        (∀ z∈Icc l w,
          (d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d) ∧
          (d ≤ ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ∧
            ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ≤ 2*d)) ∧
        ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc a b ∧
        ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc a b := by
  classical
  intro f hlevel color hsame
  have hbands := rational_narrow_band_partition
    (S ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun ji : ℕ × Fin 2 => rat ji.1 ji.2) Q hQ hlambda hU hθ
    (fun ji hji => hcurv ji.1 (Finset.mem_product.mp hji).1 ji.2)
    (fun ji hji => hden ji.1 (Finset.mem_product.mp hji).1 ji.2)
  refine ⟨hbands.1,?_⟩
  intro ε chartColor α β
  have hnear j (hj : j∈S) :
      |(Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3-1| ≤ 1/24 := by
    rw [hMatt j hj]
    have hh := hbands.2 (j,0) (by simp only [Finset.mem_product,Finset.mem_univ,and_true]; exact hj)
      (j,1) (by simp only [Finset.mem_product,Finset.mem_univ,and_true]; exact hj)
      (hsame j hj)
    exact hh.1.trans hθmax
  have hκ := modelPhaseThirdLower_pos hσ
  have hC : 0 < σ*(σ+1)+1+2 := by positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hr : (r:ℝ) ≠ 0 := by
    rcases horientation with ⟨hr,_⟩ | ⟨hr,_⟩
    · exact hr.ne'
    · exact hr.ne
  have hK : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hgamma' : |(Mat 2:ℝ)| ≤ R^4/(6*N^2) := by
    apply hgamma.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := pow_le_pow_left₀ (mul_nonneg hQR.le hN.le) hmesh 2
    nlinarith only [hh]
  have hκC : modelPhaseThirdLower σ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ hF
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hratio : modelPhaseThirdLower σ/(σ*(σ+1)+1+2) ≤ 1 :=
    (div_le_one hC).mpr (by linarith only [hκC])
  have hRN₂ : R^2/N^2 ≤ 1 := (div_le_one (sq_pos_of_pos hN)).mpr
    (pow_le_pow_left₀ hR.le hRN 2)
  have hsmall : |(Mat 2:ℝ)| *ε ≤ 1/24 := by
    calc
      _ ≤ (R^4/(6*N^2))*ε := mul_le_mul_of_nonneg_right hgamma' hε.le
      _ = (modelPhaseThirdLower σ/(σ*(σ+1)+1+2))*(R^2/N^2)/96 := by
        dsimp only [ε]
        field_simp
        ring
      _ ≤ 1*1/96 := by gcongr
      _ ≤ _ := by norm_num
  obtain ⟨G,hGS,hmass,hgeom⟩ := physical_reference_gap_twelve_radius_selection S x
    hσ hδ hF hT hM hN hR hA hW hphase horientation hx hwindow
    (fun j hj => by change iteratedDeriv 2 f (x j)/2∈Icc a b; rw [hlevel j hj]; exact hgap j hj)
  have hgeometry j (hj : j∈G) :
      a+12*ε < (rat j 0:ℝ) ∧ (rat j 0:ℝ) < b-12*ε ∧
      12*|(r:ℝ)| *ε < (r:ℝ)*(rat j 0:ℝ)-e := by
    have hh := hgeom j hj
    change a+12*ε < iteratedDeriv 2 f (x j)/2 ∧
      iteratedDeriv 2 f (x j)/2 < b-12*ε ∧
      12*|(r:ℝ)| *ε < (r:ℝ)*(iteratedDeriv 2 f (x j)/2)-e at hh
    rw [hlevel j (hGS hj)] at hh
    exact hh
  have hupper j (hj : j∈G) : (r:ℝ)*(rat j 0:ℝ)-e ≤ |(r:ℝ)| *(b-a) := by
    have hg := hgap j (hGS hj)
    rcases horientation with ⟨hrpos,href⟩ | ⟨hrneg,href⟩
    · have heq : (e:ℝ)=a*r := (div_eq_iff hrpos.ne').mp href
      rw [heq,abs_of_pos hrpos]
      nlinarith only [mul_nonneg hrpos.le (sub_nonneg.mpr hg.2)]
    · have heq : (e:ℝ)=b*r := (div_eq_iff hrneg.ne).mp href
      rw [heq,abs_of_neg hrneg]
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg hrneg.le (sub_nonneg.mpr hg.1)]
  have hinterval j (hj : j∈G) : Icc ((rat j 0:ℝ)-ε) ((rat j 0:ℝ)+ε) ⊆ Icc a b := by
    intro y hy
    have hg := hgeometry j hj
    constructor <;> linarith only [hg.1,hg.2.1,hy.1,hy.2,hε]
  refine ⟨G,hGS,hmass,?_⟩
  exact reference_gap_quarter_band_chart_cover G (fun j => (rat j 0:ℝ))
    (by exact_mod_cast hchart) hr hε
    (fun j hj => (hgeometry j hj).2.2) hupper hinterval
    (fun j hj => hnear j (hGS hj)) hsmall

example
    (S : Finset ℕ) (x : ℕ → ℝ) (rat : ℕ → Fin 2 → ℚ)
    (Q K₀ : ℕ) [NeZero K₀] (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M A W N R base a b lambda U θ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRN : R ≤ N) (hQ : 0 < Q)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hchart : v*r-e*s=1)
    (horientation : ((0:ℝ) < r ∧ (e:ℝ)/r=a) ∨ ((r:ℝ) < 0 ∧ (e:ℝ)/r=b))
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hlambda : 0 < lambda) (hU : 0 ≤ U)
    (hθ : 0 < θ) (hθmax : θ ≤ 1/24)
    (hcurv : ∀ j∈S, ∀ i, lambda ≤ |(rat j i:ℝ)| ∧ |(rat j i:ℝ)| ≤ U)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hgap : ∀ j∈S, (rat j 0:ℝ)∈Icc a b)
    (hMatt : ∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=
      ((rat j 1).den:ℝ)/(rat j 0).den) :
    let f := heathBrownPhysicalPhase F T M A 1
    (∀ j∈S, iteratedDeriv 2 f (x j)/2=(rat j 0:ℝ)) →
    let color := fun j i => (⌊((rat j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ j∈S, color j 0=color j 1) →
    (((S ×ˢ (Finset.univ : Finset (Fin 2))).image
      (fun ji => color ji.1 ji.2)).card:ℝ) ≤ (4/θ+3)*(4*U/(lambda*θ)+3) ∧
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let chartColor := fun j => ⌊Real.logb (5/4)
      (((r:ℝ)*(rat j 0:ℝ)-e)/(12*|(r:ℝ)| *ε))⌋₊
    let α := fun j => ((v:ℝ)-s*((rat j 0:ℝ)+ε))/((r:ℝ)*((rat j 0:ℝ)+ε)-e)
    let β := fun j => ((v:ℝ)-s*((rat j 0:ℝ)-ε))/((r:ℝ)*((rat j 0:ℝ)-ε)-e)
    ∃ G : Finset ℕ, G⊆S ∧ S.card ≤ 6+G.card ∧
      (G.image chartColor).card ≤ ⌊Real.logb (5/4) ((b-a)/(12*ε))⌋₊+1 ∧
      ∀ n∈G.image chartColor, ∃ d l w : ℝ, 0 < d ∧ l ≤ w ∧
        (∀ j∈G, chartColor j=n → α j∈Icc l w ∧ β j∈Icc l w) ∧
        (∀ z∈Icc l w,
          (d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d) ∧
          (d ≤ ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ∧
            ((Mat 2:ℝ)*e+Mat 3*r)*z+((Mat 2:ℝ)*v+Mat 3*s) ≤ 2*d)) ∧
        ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc a b ∧
        ((e:ℝ)*w+v)/((r:ℝ)*w+s)∈Icc a b :=
  HuxleyPairedChartScratch.physicalModelPhase_same_color_reference_gap_paired_chart_cover S x rat Q K₀ Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (a:=a) (b:=b) (lambda:=lambda) (U:=U) (θ:=θ) (F:=F) hσ hδ hF hT hM hN hR hRN hQ hA hW hphase hmesh hgamma hchart horientation hx hwindow hlambda hU hθ hθmax hcurv hden hgap hMatt

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
      (S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) := by
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
      exact hm.trans (add_le_add (le_refl 6)
        (mul_le_mul_of_nonneg_left hcountSchart (Nat.cast_nonneg Ccharts)))

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
      (S.card:ℝ) ≤ 6+(Ccharts:ℝ)*(105+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) :=
  HuxleyPairedChartScratch.physicalModelPhase_actual_fourier_charted_reference_gap_count Uref Refs (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap

#print axioms physicalModelPhase_actual_fourier_charted_reference_gap_count
#print axioms physicalModelPhase_same_color_reference_gap_paired_chart_cover
#print axioms reference_gap_quarter_band_chart_cover
#print axioms physical_reference_gap_twelve_radius_selection
#print axioms logarithmic_quarter_band_partition
#print axioms inverse_paired_chart_point_bounds

end HuxleyPairedChartScratch
