import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical
namespace HuxleyQuarticCompressionScratch

/-- Two actual paired physical points with small rounded Third ratios
have compressed curvature separation when the matrix entry is large.
This reuses the proved paired C4 compression directly, without a span
budget or an assumed estimate between the two points. -/
theorem physicalModelPhase_paired_large_entry_curvature_diameter
    (x y : Fin 2 → ℝ) (a b c d : ℤ)
    {σ δ T M Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : Fin 2 => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    iteratedDeriv 2 (f 0) (x 0)/2 ≤ iteratedDeriv 2 (f 0) (x 1)/2 →
    (∀ p, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    iteratedDeriv 2 (f 0) (x 1)/2-iteratedDeriv 2 (f 0) (x 0)/2 ≤
      16*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)/(κ*|(c:ℝ)|) := by
  classical
  let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
  let μ := fun i z => iteratedDeriv 3 (f i) z/6
  let κ := modelPhaseThirdLower σ
  let Γ := (σ*(σ+1)+1)/κ
  let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
  let E := Γ^2*Δ+2*Γ*η
  let U := 2*(σ*(σ+1)+1)*T/(6*M^3)
  let L := κ*T/M^3
  let t := fun p : Fin 2 => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
  change _ → _ → _ → _ → _
  intro horder hmap ht hthird
  have hτpos i : 0 < τ i := hT.trans_le (hτ i).1
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hΓ : 0 < Γ := by dsimp [Γ]; positivity
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₂ : 0 < σ*(σ+1)+1 := by positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 3) le_rfl
  have hbuf i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      z ∈ Set.Ioo 0 (W i) := ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
  have hrnd i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      (round z:ℝ) ∈ Set.Ioo 0 (W i) :=
    (physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i) (hτpos i) hM
      (hA i) (hW i) hz).1
  have hbounds i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) :
      κ*τ i/(6*M^3) ≤ μ i z ∧ μ i z ≤ (σ*(σ+1)+1)*τ i/(6*M^3) :=
    physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i) (hτpos i) hM
      (hA i) (hW i) hz
  have hcommon i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) :
      L/6 ≤ μ i z ∧ μ i z ≤ U := by
    constructor
    · calc
        _ = κ*T/(6*M^3) := by dsimp [L]; ring
        _ ≤ κ*τ i/(6*M^3) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ i).1 hκ.le) (by positivity)
        _ ≤ μ i z := (hbounds i z hz).1
    · calc
        _ ≤ (σ*(σ+1)+1)*τ i/(6*M^3) := (hbounds i z hz).2
        _ ≤ (σ*(σ+1)+1)*(2*T)/(6*M^3) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ i).2 hC₂.le) (by positivity)
        _ = U := by dsimp [U]; ring
  have hμpos i (z : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) : 0 < μ i z :=
    lt_of_lt_of_le (by positivity) (hcommon i z hz).1
  have hratio i (z w : ℝ) (hz : z ∈ Set.Ioo 0 (W i)) (hw : w ∈ Set.Ioo 0 (W i)) :
      μ i z/μ i w ≤ Γ := by
    have hτi := hτpos i
    calc
      _ ≤ ((σ*(σ+1)+1)*τ i/(6*M^3))/(κ*τ i/(6*M^3)) :=
        div_le_div₀ (by positivity) (hbounds i z hz).2 (by positivity) (hbounds i w hw).1
      _ = Γ := by dsimp [Γ]; field_simp
  have hroundvar i (z : ℝ) (hz : z ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) :
      |μ i z/μ i (round z)-1| ≤ η := by
    have hb := physicalModelPhase_cubicCoefficient_relative_variation hσ hδ (hF i)
      (hτpos i).ne' hM (hA i) (hW i) (hrnd i z hz) (hbuf i z hz)
    calc
      _ ≤ (modelPhaseJetCoefficient σ 3+δ)*|z-(round z:ℝ)|/(κ*M) := hb
      _ ≤ (modelPhaseJetCoefficient σ 3+δ)*(1/2)/(κ*M) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_sub_round z) hC₃) (by positivity)
      _ = η := by dsimp [η]; ring
  have hrealThird (p : Fin 2) :
      |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ E := by
    have hxp := hμpos 0 (x p) (hbuf 0 _ (hx p))
    have hxrp := hμpos 0 (round (x p)) (hrnd 0 _ (hx p))
    have hyp := hμpos 1 (y p) (hbuf 1 _ (hy p))
    have hyrp := hμpos 1 (round (y p)) (hrnd 1 _ (hy p))
    have hrat := ratio_relative_perturbation_of_inverse_bound (div_pos hxp hxrp) hΓ.le
      (hthird p) (hroundvar 1 _ (hy p)) (hroundvar 0 _ (hx p))
      (by rw [abs_of_pos (div_pos hyp hyrp)]; exact hratio 1 _ _ (hbuf 1 _ (hy p)) (hrnd 1 _ (hy p)))
      (by rw [one_div_div]; exact hratio 0 _ _ (hrnd 0 _ (hx p)) (hbuf 0 _ (hx p)))
    change |(μ 1 (round (y p))*(t p)^3/μ 0 (round (x p)))*
      (μ 1 (y p)/μ 1 (round (y p)))/(μ 0 (x p)/μ 0 (round (x p)))-1| ≤ E at hrat
    convert hrat using 1
    congr 1
    field_simp [hxp.ne',hxrp.ne',hyrp.ne']
  have hres (p : Fin 2) : |μ 1 (y p)*(t p)^3-μ 0 (x p)| ≤ U*E := by
    calc
      _ = |μ 0 (x p)*(μ 1 (y p)*(t p)^3/μ 0 (x p)-1)| := by
        congr 1
        field_simp [(hμpos 0 _ (hbuf 0 _ (hx p))).ne']
      _ = μ 0 (x p)*|μ 1 (y p)*(t p)^3/μ 0 (x p)-1| := by
        rw [abs_mul,abs_of_pos (hμpos 0 _ (hbuf 0 _ (hx p)))]
      _ ≤ U*E := mul_le_mul (hcommon 0 _ (hbuf 0 _ (hx p))).2
        (hrealThird p) (abs_nonneg _) hU.le
  have hcf i z (hz : z ∈ Set.Ioo 0 (W i)) : ContDiffAt ℝ 4 (f i) z := by
    have hh := heathBrownPhysicalPhase_contDiffOn (hF i).1 hM (hA i) (hW i) (τ i) 1
    exact ((hh z (Set.Ioo_subset_Icc_self hz)).contDiffAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Set.Ioo_subset_Icc_self)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hthree i z (hz : z ∈ Set.Ioo 0 (W i)) : L ≤ iteratedDeriv 3 (f i) z := by
    have hh := (hcommon i z hz).1
    change L/6 ≤ iteratedDeriv 3 (f i) z/6 at hh
    linarith only [hh]
  have hfour i z (hz : z ∈ Set.Ioo 0 (W i)) :
      |iteratedDeriv 4 (f i) z| ≤ |(c:ℝ)| *L^2/16 := by
    have hτi := hτpos i
    have hyp := heathBrownPhysicalPoint_mem_interior hM (hA i) (hW i) hz
    have he := approximateModelPhase_iteratedDeriv_error (hF i) hyp 3 le_rfl
    have hm := iteratedDeriv_modelPhase_abs_le hσ.le hyp 3
    have htri := abs_add_le
      (iteratedDeriv 4 (F i) ((A i+z)/M)-iteratedDeriv 3 (Expdb.modelPhase σ) ((A i+z)/M))
      (iteratedDeriv 3 (Expdb.modelPhase σ) ((A i+z)/M))
    rw [sub_add_cancel] at htri
    have hu : |iteratedDeriv 4 (F i) ((A i+z)/M)| ≤ modelPhaseJetCoefficient σ 3+δ := by
      linarith only [he,hm,htri]
    have hj : |iteratedDeriv 4 (f i) z| ≤ τ i/M^4*(modelPhaseJetCoefficient σ 3+δ) := by
      dsimp only [f]
      rw [heathBrownPhysicalPhase_iteratedDeriv (hF i).1 hM (hA i) (hW i) hz,one_mul,
        abs_mul,abs_of_pos (by positivity : 0 < τ i/M^4)]
      exact mul_le_mul_of_nonneg_left hu (by positivity)
    apply hj.trans
    calc
      _ ≤ 2*T/M^4*(modelPhaseJetCoefficient σ 3+δ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hτ i).2 (by positivity)) hC₃
      _ ≤ _ := by
        dsimp only [L]
        apply (mul_le_mul_iff_of_pos_right (show 0 < 16*M^6 by positivity)).mp
        have hh := mul_le_mul_of_nonneg_left hscale hT.le
        convert hh using 1 <;> field_simp
        · ring
        · rfl
  have hb := scaled_paired_C4_nontriangular_resonance_compression
    (f 0) (f 1) a b c d hdet hc hL
    (hcf 0) (hthree 0) (hfour 0) (hcf 1) (hthree 1) (hfour 1)
    (hbuf 0 _ (hx 0)) (hbuf 0 _ (hx 1))
    (hbuf 1 _ (hy 0)) (hbuf 1 _ (hy 1))
    horder (hmap 0) (hmap 1) (ht 0) (ht 1) (hres 0) (hres 1)
  apply hb.trans_eq
  change 48*(U*E)/(|(c:ℝ)| *L)=16*(σ*(σ+1)+1)*E/(κ*|(c:ℝ)|)
  dsimp only [U,L]
  field_simp
  ring

#print axioms physicalModelPhase_paired_large_entry_curvature_diameter

example
    (x y : Fin 2 → ℝ) (a b c d : ℤ)
    {σ δ T M Δ : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : Fin 2 => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    iteratedDeriv 2 (f 0) (x 0)/2 ≤ iteratedDeriv 2 (f 0) (x 1)/2 →
    (∀ p, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    iteratedDeriv 2 (f 0) (x 1)/2-iteratedDeriv 2 (f 0) (x 0)/2 ≤
      16*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)/(κ*|(c:ℝ)|) :=
  HuxleyQuarticCompressionScratch.physicalModelPhase_paired_large_entry_curvature_diameter x y a b c d (σ:=σ) (δ:=δ) (T:=T) (M:=M) (Δ:=Δ) (τ:=τ) (A:=A) (W:=W) (F:=F) hσ hδ hδ0 hF hT hτ hM hA hW hΔ hdet hc hscale hx hy


/-- Direct paired compression of the two quartic witnesses proves the
large-entry First Condition under the square-span budgets of Section 9.
No cubic span or improved ratio on an intervening occupied family is
assumed. The integer matrix acts on both genuine reference columns. -/
theorem physicalModelPhase_large_entry_quartic_long_block_constraint
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2 ≠ 0)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    κ^2*|(Mat 2:ℝ)| *L^3*N^2 ≤
      128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4 := by
  intro f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  obtain ⟨z₀,hz₀,z₁,hz₁,hG,hthird⟩ := physicalModelPhase_quartic_two_long_block_witnesses
    x hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
    hden hdenUpper hmono hbase hpoint hsquare hgap hres
  have hz₀' : z₀∈Icc (x 0) (x 7) :=
    ⟨hz₀.1.le,hz₀.2.le.trans (hmono.monotone (by decide))⟩
  have hz₁' : z₁∈Icc (x 0) (x 7) :=
    ⟨(hmono.monotone (by decide)).trans hz₁.1.le,hz₁.2.le⟩
  have hzorder : z₀ ≤ z₁ := hz₀.2.le.trans
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hdpos z (hz : z∈Icc (x 0) (x 7)) i : 0 < D z i :=
    hd.trans_le (hden z hz i)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hCp : 0 < σ*(σ+1)+1 := by positivity
  have hΓ : 0 < Γ := div_pos hCp hκ
  have hcpos : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 0)
    hT hM (hA 0) (hW 0) hround.1
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  let z : Fin 2 → ℝ := ![z₁,z₀]
  let xx : Fin 2 → ℝ := fun p => x₁ (z p) 0
  let yy : Fin 2 → ℝ := fun p => x₁ (z p) 1
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₁'
    · exact hz₀'
  have hdiff : profile z₀-profile z₁=(z₁-z₀)/(D z₀ 0*D z₁ 0) := by
    dsimp only [profile]
    rw [hpoint z₀ hz₀' 0,hpoint z₁ hz₁' 0,
      div_sub_div _ _ (hdpos z₀ hz₀' 0).ne' (hdpos z₁ hz₁' 0).ne']
    congr 1
    dsimp only [D]
    linear_combination (z₁-z₀)*hdet 0
  have horder : profile z₁ ≤ profile z₀ := sub_nonneg.mp (by
    rw [hdiff]
    exact div_nonneg (sub_nonneg.mpr hzorder)
      (mul_pos (hdpos z₀ hz₀' 0) (hdpos z₁ hz₁' 0)).le)
  have hGid t (ht : t∈Icc (x 0) (x 7)) : profile t-e 0/r 0=3*μ 0*G t := by
    rw [show profile t=(e 0*t+v 0)/(r 0*t+s 0) from hpoint t ht 0]
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (u:=t) (t:=1) hμ.ne' (hr 0)
        one_ne_zero (by simpa only [mul_one] using (hdpos t ht 0).ne') (hdet 0))
  have hdiffG : profile z₀-profile z₁=3*μ 0*(G z₀-G z₁) := by
    linarith only [hGid z₀ hz₀',hGid z₁ hz₁']
  have hGorder : 0 ≤ G z₀-G z₁ := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ)<3) hμ)).mp
    rw [← hdiffG]
    exact sub_nonneg.mpr horder
  rw [abs_sub_comm,abs_of_nonneg hGorder] at hG
  have hlo : κ*L/(8*R^2) ≤ profile z₀-profile z₁ := by
    have hmul := mul_le_mul_of_nonneg_left hG
      (mul_pos (by norm_num : (0:ℝ)<3) hμ).le
    calc
      _ = 3*(κ*T/(6*M^3))*(L*N/4) := by
        have hTval : T=M^3/(N*R^2) :=
          (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
        rw [hTval]
        field_simp
        ring_nf
      _ ≤ 3*μ 0*(L*N/4) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hμbounds.1 (by norm_num : (0:ℝ) ≤ 3))
        (by positivity)
      _ ≤ _ := by linarith only [hmul,hdiffG]
  let Δ := C*R^2/(L^2*N^2)
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (hthird z₀ (by simp))
  have ht p : (Mat 2:ℝ)*profile (z p)+Mat 3=D (z p) 1/D (z p) 0 := by
    rw [show profile (z p)=(e 0*z p+v 0)/D (z p) 0 from hpoint _ (hz p) 0]
    apply (eq_div_iff (hdpos _ (hz p) 0).ne').mpr
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdpos _ (hz p) 0).ne']
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
    ring_nf
  have hmap p : ((Mat 0:ℝ)*profile (z p)+Mat 1)/
      ((Mat 2:ℝ)*profile (z p)+Mat 3)=iteratedDeriv 2 (f 1) (yy p)/2 := by
    rw [ht]
    have he : (Mat 0:ℝ)*profile (z p)+Mat 1=
        (e 1*z p+v 1)/D (z p) 0 := by
      rw [show profile (z p)=(e 0*z p+v 0)/D (z p) 0 from hpoint _ (hz p) 0]
      apply (eq_div_iff (hdpos _ (hz p) 0).ne').mpr
      rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hdpos _ (hz p) 0).ne']
      dsimp only [D]
      rw [htransport.1,htransport.2.1]
      ring_nf
    rw [he,div_div_div_cancel_right₀ (hdpos _ (hz p) 0).ne']
    exact (hpoint _ (hz p) 1).symm
  have htband p : (1:ℝ)/2 ≤ (Mat 2:ℝ)*profile (z p)+Mat 3 ∧
      (Mat 2:ℝ)*profile (z p)+Mat 3 ≤ 2 := by
    rw [ht]
    constructor
    · apply (le_div_iff₀ (hdpos _ (hz p) 0)).mpr
      linarith only [hden _ (hz p) 1,hdenUpper _ (hz p) 0]
    · apply (div_le_iff₀ (hdpos _ (hz p) 0)).mpr
      linarith only [hden _ (hz p) 0,hdenUpper _ (hz p) 1]
  have hthird' p : |μnew (z p) 1*((Mat 2:ℝ)*profile (z p)+Mat 3)^3/
      μnew (z p) 0-1| ≤ Δ := by
    rw [ht]
    have he : μnew (z p) 1*(D (z p) 1/D (z p) 0)^3/μnew (z p) 0=
        μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3) := by
      rw [div_pow]
      ring_nf
    rw [he]
    apply hthird
    fin_cases p <;> simp [z]
  have hcompression := physicalModelPhase_paired_large_entry_curvature_diameter
    (τ:=fun _ => T) xx yy (Mat 0) (Mat 1) (Mat 2) (Mat 3)
    hσ hδ hδ0 hF₃ hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩)
    hM hA hW hΔ hMat hc hlarge
    (fun p => hx₁ _ (hz p) 0) (fun p => hx₁ _ (hz p) 1)
    horder hmap htband hthird'
  have hNL' : L^2*N^2 ≤ M*R^2 := by
    calc
      _ = (L*N)^2 := by ring_nf
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_le_mul_of_nonneg_left hR hRpos.le] : R ≤ R^2) hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by simpa only [one_mul,mul_one,mul_comm] using hNL')
  have hη : 2*Γ*((modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)) ≤
      (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)) := by
    calc
      _ = (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(1/M) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv
        (div_nonneg (mul_nonneg hΓ.le hC₃) hκ.le)
  let B := Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
  have hupper : profile z₀-profile z₁ ≤
      16*(σ*(σ+1)+1)*B*R^2/((κ*|(Mat 2:ℝ)|)*(L^2*N^2)) := by
    apply hcompression.trans
    calc
      _ ≤ 16*(σ*(σ+1)+1)*(Γ^2*Δ+
          (Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(R^2/(L^2*N^2)))/
          (κ*|(Mat 2:ℝ)|) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hκ hcpos).le
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hη)
          (mul_pos (by norm_num) hCp).le
      _ = _ := by dsimp only [Δ,B]; ring_nf
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 8*R^2)
    (by positivity : 0 < (κ*|(Mat 2:ℝ)|)*(L^2*N^2))).mp (hlo.trans hupper)
  change κ^2*|(Mat 2:ℝ)| *L^3*N^2 ≤ 128*(σ*(σ+1)+1)*B*R^4
  nlinarith only [hcross]

#print axioms physicalModelPhase_large_entry_quartic_long_block_constraint

example
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1) (hc : Mat 2 ≠ 0)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    κ^2*|(Mat 2:ℝ)| *L^3*N^2 ≤
      128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4 :=
  HuxleyQuarticCompressionScratch.physicalModelPhase_large_entry_quartic_long_block_constraint (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (d:=d) (K:=K) (α:=α) (β:=β) x Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) (e:=e) (r:=r) (v:=v) (s:=s) (x₁:=x₁) hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale hMat hc htransport hlarge


/-- Source-form two-term First Condition from the actual quartic witnesses.
The large-entry branch uses direct paired compression; the complementary
branch supplies the N*R^2/M term. Only square-span budgets are required. -/
theorem physicalModelPhase_quartic_matrix_long_block_first_condition
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
  intro f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C Cfirst Csecond
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hΓ : 0 < Γ := by dsimp only [Γ]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hfirst : 0 ≤ Cfirst*R^4/(L^3*N^2) := by
    dsimp only [Cfirst]
    positivity
  have hsecond : 0 ≤ Csecond*N*R^2/M := by
    dsimp only [Csecond]
    positivity
  by_cases hc : Mat 2=0
  · rw [hc,Int.cast_zero,abs_zero]
    exact add_nonneg hfirst hsecond
  by_cases hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T
  · have hh := physicalModelPhase_large_entry_quartic_long_block_constraint
      x Mat hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
      hden hdenUpper hmono hscale hMat hc htransport hlarge
      hbase hpoint hsquare hgap hres
    have hb : |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2) := by
      apply (le_div_iff₀ (by positivity : 0 < L^3*N^2)).mpr
      have hh' : |(Mat 2:ℝ)| *(L^3*N^2) ≤
          (128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4)/κ^2 := by
        apply (le_div_iff₀ (pow_pos hκ 2)).mpr
        calc
          _ = κ^2*|(Mat 2:ℝ)| *L^3*N^2 := by ring
          _ ≤ _ := hh
      exact hh'.trans_eq (by dsimp only [Cfirst]; ring)
    exact hb.trans (le_add_of_nonneg_right hsecond)
  · have hs : |(Mat 2:ℝ)| ≤
        (32*(modelPhaseJetCoefficient σ 3+δ)*M^2)/(κ^2*T) := by
      apply (le_div_iff₀ (mul_pos (pow_pos hκ 2) hT)).mpr
      simpa only [mul_assoc] using (lt_of_not_ge hlarge).le
    have he : (32*(modelPhaseJetCoefficient σ 3+δ)*M^2)/(κ^2*T)=
        Csecond*N*R^2/M := by
      have hTval : T=M^3/(N*R^2) :=
        (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
      rw [hTval]
      dsimp only [Csecond]
      field_simp
    exact (hs.trans_eq he).trans (le_add_of_nonneg_left hfirst)

#print axioms physicalModelPhase_quartic_matrix_long_block_first_condition

example
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) (hscale : T*N*R^2=M^3)
    (hMat : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (htransport : e 1=(Mat 0:ℝ)*e 0+Mat 1*r 0 ∧
      v 1=(Mat 0:ℝ)*v 0+Mat 1*s 0 ∧
      r 1=(Mat 2:ℝ)*e 0+Mat 3*r 0 ∧
      s 1=(Mat 2:ℝ)*v 0+Mat 3*s 0)
    :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*(σ*(σ+1)+1)*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M :=
  HuxleyQuarticCompressionScratch.physicalModelPhase_quartic_matrix_long_block_first_condition (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (d:=d) (K:=K) (α:=α) (β:=β) x Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) (e:=e) (r:=r) (v:=v) (s:=s) (x₁:=x₁) hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale hMat htransport


/-- Actual signed-height occupied-window selection feeds the source-form
two-term First Condition under a SQUARE span budget. The proof derives
the samples and applies paired compression to their quartic witnesses;
no cubic-span restriction or occupied improved-Third certificate is used. -/
theorem physicalModelPhase_signed_height_square_span_first_condition
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

#print axioms physicalModelPhase_signed_height_square_span_first_condition

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
  HuxleyQuarticCompressionScratch.physicalModelPhase_signed_height_square_span_first_condition S p x Mat (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hnsquare hr hdet hden hcoord hP₂ hCcurv hBcut hBsize hMat htransport


/-- The ALREADY selected integer reference length satisfies Section 9's
square-span budget under the improved N^10 scale. This uses its actual
Q-dependent upper bound and does not impose the old N^5 condition. -/
theorem source_selected_reference_square_span_budget
    (U : ℕ) {M N R Q B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hB : 0 < B)
    (hU : (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B)
    (hscale : N^10 ≤ M^3*R^7) :
    (B*(U:ℝ)*N)^2 ≤ M*R := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hpow : ((N/Q)^((2:ℝ)/3))^3=(N/Q)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (div_pos hN hQ).le]
    norm_num
  have hcube : B^3*(U:ℝ)^3*Q^2 ≤ N^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) hU 3)
      (show 0 ≤ B^3*Q^2 by positivity)
    have he : (B^3*Q^2)*((N/Q)^((2:ℝ)/3)/B)^3=N^2 := by
      rw [div_pow,hpow,div_pow]
      field_simp
    rw [he] at hh
    nlinarith only [hh]
  apply (pow_le_pow_iff_left₀ (sq_nonneg (B*(U:ℝ)*N))
    (mul_pos hM hR).le (by decide : (3:ℕ) ≠ 0)).mp
  apply (mul_le_mul_iff_of_pos_right (pow_pos hQ 4)).mp
  calc
    _ = (B^3*(U:ℝ)^3*Q^2)^2*N^6 := by ring
    _ ≤ (N^2)^2*N^6 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hcube 2) (pow_nonneg hN.le 6)
    _ = N^10 := by ring
    _ ≤ M^3*R^7 := hscale
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hR.le hRQ 4) (show 0 ≤ M^3*R^3 by positivity)
      convert hh using 1 <;> ring

#print axioms source_selected_reference_square_span_budget

example
    (U : ℕ) {M N R Q B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hB : 0 < B)
    (hU : (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B)
    (hscale : N^10 ≤ M^3*R^7) :
    (B*(U:ℝ)*N)^2 ≤ M*R :=
  HuxleyQuarticCompressionScratch.source_selected_reference_square_span_budget U (M:=M) (N:=N) (R:=R) (Q:=Q) (B:=B) hM hN hR hRQ hB hU hscale


/-- Shared same-reference source consumer for the Section 9 First Condition. -/
private theorem physicalModelPhase_actual_fourier_height_square_span_fixed_reference_first_condition
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


/-- The SAME actual Fourier family and constructed reference supply
the Section 9 two-term First Condition after actual curvature-cell
selection. The accepted physical span is square, not cubic; all source
sector/cutoff and displacement conditions remain explicit. -/
theorem physicalModelPhase_actual_fourier_height_square_span_selected_cell_first_condition
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
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
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
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
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
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
  obtain ⟨k,S₀,hS₀S,hS₀card,hcells⟩ :=
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
  have hS₀ : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=48)
    calc
      _ = 48+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) := by ring
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
  have hnum j (hj : j∈S₀) := hnum j (hS₀S hj)
  have hdyad j (hj : j∈S₀) := hdyad j (hS₀S hj)
  have hanchor j (hj : j∈S₀) := hanchor j (hS₀S hj)
  have hcut j (hj : j∈S₀) := hcut j (hS₀S hj)
  have hcount j (hj : j∈S₀) := hcount j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  have hbudget j (hj : j∈S₀) := hbudget j (hS₀S hj)
  have hlarge j (hj : j∈S₀) := hlarge j (hS₀S hj)
  have hleft j (hj : j∈S₀) := (hcells' j hj).1
  have hright j (hj : j∈S₀) := (hcells' j hj).2
  exact physicalModelPhase_actual_fourier_height_square_span_fixed_reference_first_condition S₀ Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut
    hS₀ hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hdl hdw hnum hdyad
    hanchor hcut hcount xref
    (fun i => ⟨(mul_ne_zero_iff.mp (hxr i).1.ne').1,(hxr i).2.1,(hxr i).2.2.1⟩)
    Hspan hdisplacement hspan hbudget hD hΔ hdenregion hleft hright
    hlarge hBsize hGcut

#print axioms physicalModelPhase_actual_fourier_height_square_span_selected_cell_first_condition

example
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
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
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M :=
  HuxleyQuarticCompressionScratch.physicalModelPhase_actual_fourier_height_square_span_selected_cell_first_condition S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear


/-- The square-span First Condition itself controls the whole actual
Fourier family, after an explicit small-entry alternative. This bypasses
transport of an improved Third estimate to intervening occupied points. -/
theorem physicalModelPhase_actual_fourier_height_square_span_selected_cell_family_count
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
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
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
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
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_height_square_span_selected_cell_first_condition S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
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
    apply Nat.le_of_add_le_add_left (a:=48)
    calc
      _ = 48+544*Blabels := by ring
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
  have hmass : (S.card:ℝ) ≤ 48+17*(S₀.card:ℝ) := by exact_mod_cast hS₀card
  calc
    _ ≤ 48+17*(S₀.card:ℝ) := hmass
    _ ≤ 48+17*(Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcellcount (by norm_num))
    _ = _ := by ring

#print axioms physicalModelPhase_actual_fourier_height_square_span_selected_cell_family_count

example
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
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
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
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
  HuxleyQuarticCompressionScratch.physicalModelPhase_actual_fourier_height_square_span_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear


end HuxleyQuarticCompressionScratch
