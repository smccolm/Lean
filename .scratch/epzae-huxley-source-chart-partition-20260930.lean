import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleySourceChartScratch

/-- A finite, source-uniform coloring constructs BOTH ordinary and
reciprocal source charts around actual source points. The same coloring
carries its explicit twelfth-moment loss. -/
theorem positive_difference_source_chart_twelfth_partition
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) {σ c U η T M a : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
    let u := fun i => (2*M^2/T)*(rat i:ℝ)
    let w := fun i => (T/(2*M^2))*(rat i:ℝ)⁻¹
    let color := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let Cap := (4/a+3)*((6*U/σ)/a+3)*((4*σ/c)/a+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ k∈S.image color, ∃ iref∈S, color iref=k ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ i∈S, color i=k →
        ‖((y i,u i):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y i,w i):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤
      Cap^11*∑ k∈S.image color, ‖∑ i∈S.filter (fun i => color i=k),coeff i‖^12 := by
  classical
  intro f hlevel Hsrc u w color Cap
  have hsp : 0 < 2*M^2/T := by positivity
  have hsip : 0 < T/(2*M^2) := by positivity
  have hbounds i (hi : i∈S) :
      c*T/(4*σ*M^2) ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ (3*U/σ)*T/(2*M^2) := by
    rw [←hlevel i hi]
    exact positive_difference_half_curvature_source_bounds F hσ hc hU hη hηmax hT hM
      (hy i hi) (hz i hi) hf hbound htests
  have hu i (hi : i∈S) : |u i| ≤ 3*U/σ := by
    dsimp only [u]
    rw [abs_mul,abs_of_pos hsp]
    calc
      _ ≤ (2*M^2/T)*((3*U/σ)*T/(2*M^2)) :=
        mul_le_mul_of_nonneg_left (hbounds i hi).2 hsp.le
      _ = _ := by field_simp
  have hw i (hi : i∈S) : |w i| ≤ 2*σ/c := by
    have hp : 0 < |(rat i:ℝ)| :=
      (show 0 < c*T/(4*σ*M^2) by positivity).trans_le (hbounds i hi).1
    dsimp only [w]
    rw [abs_mul,abs_inv,abs_of_pos hsip,←div_eq_mul_inv]
    apply (div_le_iff₀ hp).mpr
    calc
      _ = (2*σ/c)*(c*T/(4*σ*M^2)) := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbounds i hi).1 (by positivity)
  have hsource i (hi : i∈S) : Hsrc (y i,z i/M)=u i := by
    have hd := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (hM.trans_le (hz i hi).1) (mul_nonneg hη.le (by linarith only [(hy i hi).1])) hf 2
    have hh := hlevel i hi
    change iteratedDeriv 2 (fun t => T*(F (t/M)-F (t/M+η*y i))/(σ*η)) (z i)/2=(rat i:ℝ) at hh
    rw [hd] at hh
    dsimp only [Hsrc,u]
    rw [←hh]
    field_simp
  have hinv i : (u i)⁻¹=w i := by
    dsimp only [u,w]
    rw [mul_inv_rev,inv_div]
    ring
  have h₁ : ((S.image (fun i => (color i).1)).card:ℝ) ≤ 4/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by intro i hi; rw [abs_of_nonneg (by linarith only [(hy i hi).1])]; simpa using (hy i hi).2)
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using hh
  have h₂ : ((S.image (fun i => (color i).2.1)).card:ℝ) ≤ (6*U/σ)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=3*U/σ) S u
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hu i hi)
    simp only [mul_one] at hh
    convert hh using 1
    ring
  have h₃ : ((S.image (fun i => (color i).2.2)).card:ℝ) ≤ (4*σ/c)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2*σ/c) S w
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hw i hi)
    simp only [mul_one] at hh
    convert hh using 1
    ring
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hsub : S.image color ⊆
        (S.image (fun i => (color i).1)) ×ˢ
          ((S.image (fun i => (color i).2.1)) ×ˢ (S.image (fun i => (color i).2.2))) := by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_product] at hh
    have hh' : ((S.image color).card:ℝ) ≤
        ((S.image (fun i => (color i).1)).card:ℝ)*
          (((S.image (fun i => (color i).2.1)).card:ℝ)*
            ((S.image (fun i => (color i).2.2)).card:ℝ)) := by exact_mod_cast hh
    apply hh'.trans
    have hm := mul_le_mul h₁ (mul_le_mul h₂ h₃ (by positivity) (by positivity))
      (by positivity) (by positivity)
    simpa only [Cap,mul_assoc] using hm
  have hsame {b d : ℝ} (he : ⌊b/a⌋=⌊d/a⌋) : |b-d| < a := by
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor he
    rw [←sub_div,abs_div,abs_of_pos ha] at hh
    exact (div_lt_iff₀ ha).mp hh |>.trans_eq (one_mul a)
  refine ⟨hcard,?_,?_⟩
  · intro k hk
    obtain ⟨iref,hiref,he⟩ := Finset.mem_image.mp hk
    refine ⟨iref,hiref,he,?_,hy iref hiref,?_⟩
    · exact ⟨(le_div_iff₀ hM).mpr (by simpa using (hz iref hiref).1),
        (div_le_iff₀ hM).mpr (by simpa [mul_comm] using (hz iref hiref).2)⟩
    · intro i _hi hci
      have heq : color i=color iref := hci.trans he.symm
      have hdy := hsame (congrArg Prod.fst heq)
      have hdu := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) heq)
      have hdw := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) heq)
      change max |y i-y iref| |u i-Hsrc (y iref,z iref/M)| < a ∧
        max |y i-y iref| |w i-(Hsrc (y iref,z iref/M))⁻¹| < a
      rw [hsource iref hiref,hinv]
      exact ⟨max_lt_iff.mpr ⟨hdy,hdu⟩,max_lt_iff.mpr ⟨hdy,hdw⟩⟩
  · intro coeff
    let Keys := S.image color
    let V := fun k => S.filter (fun i => color i=k)
    let g := fun k => ∑ i∈V k,coeff i
    have he : (∑ k∈Keys,g k)=∑ i∈S,coeff i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) coeff
    have hnorm : ‖∑ i∈S,coeff i‖ ≤ ∑ k∈Keys,‖g k‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
      (f:=fun k => ‖g k‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ k∈Keys,‖g k‖)^12 ≤ (Keys.card:ℝ)^11*∑ k∈Keys,‖g k‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Keys.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))

example
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) {σ c U η T M a : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
    let u := fun i => (2*M^2/T)*(rat i:ℝ)
    let w := fun i => (T/(2*M^2))*(rat i:ℝ)⁻¹
    let color := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let Cap := (4/a+3)*((6*U/σ)/a+3)*((4*σ/c)/a+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ k∈S.image color, ∃ iref∈S, color iref=k ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ i∈S, color i=k →
        ‖((y i,u i):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y i,w i):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤
      Cap^11*∑ k∈S.image color, ‖∑ i∈S.filter (fun i => color i=k),coeff i‖^12 :=
  HuxleySourceChartScratch.positive_difference_source_chart_twelfth_partition (ι:=ι) S F y z rat (σ:=σ) (c:=c) (U:=U) (η:=η) (T:=T) (M:=M) (a:=a) hσ hc hU hη hηmax hT hM ha hy hz hf hbound htests


end HuxleySourceChartScratch
#print axioms HuxleySourceChartScratch.positive_difference_source_chart_twelfth_partition
