import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyActualJointSourceScratch


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


/-- The literal source points and Fourier parity labels carry a single
joint coloring. Source curvature is derived from the actual normalized model;
both source charts, narrow rational ratios and parity offsets survive together. -/
theorem positive_difference_actual_source_joint_twelfth_partition
    {ι : Type*} (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (Q : ℕ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hscale : Tsrc ≤ E*T) (hQ : 0 < Q) (hθ : 0 < θ) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|)
    (hden : ∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      Cap^11*∑ key∈V.image color,
        ‖∑ ip∈V.filter (fun ip => color ip=key),coeff ip‖^12 := by
  classical
  intro Fmodel hmodel f hlevel Hsrc lambda u w chart narrow qell V offset color ChartCap NarrowCap Cap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hE : 0 < E := (mul_pos_iff_of_pos_right hT).mp (hTsrc.trans_le hscale)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
  have hband i (hi : i∈S) : lambda ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ Uband := by
    have hb := positive_difference_model_normalized_curvature_band Fsrc
      hσsrc hcsrc hUsrc hη hηmax (hy i hi) hTsrc hT hM hσ hδ hscale
      hreg hjets htests (hmodel i hi)
    rw [←hlevel i hi]
    exact hb (y i) (hy i hi) (z i) (hz i hi)
  have hchart := positive_difference_source_chart_twelfth_partition S Fsrc y z rat
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM ha hy hz hreg hjets htests hlevel
  have hnarrow := rational_narrow_band_twelfth_partition S rat Q
    (U:=Uband) hQ hlambda (by dsimp only [Uband]; positivity) hθ hband hden
  have hNcap : (4/θ+3)*(4*Uband/(lambda*θ)+3)=NarrowCap := by
    dsimp only [Uband,lambda,NarrowCap]
    field_simp
    ring
  dsimp only at hnarrow
  rw [hNcap] at hnarrow
  have hoffset := fourier_parity_round_partition S qell
  have hV (ip : ι × Fin 2) (hip : ip∈V) : ip.1∈S := (Finset.mem_product.mp hip).1
  have hsub : V.image color ⊆
      (S.image chart) ×ˢ ((S.image narrow) ×ˢ (V.image offset)) := by
    intro key hkey
    obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem chart (hV ip hip),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem narrow (hV ip hip),
        Finset.mem_image_of_mem offset hip⟩⟩
  have hCnon : 0 ≤ ChartCap := by dsimp only [ChartCap]; positivity
  have hNnon : 0 ≤ NarrowCap := by dsimp only [NarrowCap]; positivity
  have hcard : ((V.image color).card:ℝ) ≤ Cap := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_product] at hh
    have hreal : ((V.image color).card:ℝ) ≤
        ((S.image chart).card:ℝ)*(((S.image narrow).card:ℝ)*((V.image offset).card:ℝ)) := by
      exact_mod_cast hh
    have ho : ((V.image offset).card:ℝ) ≤ 3 := by exact_mod_cast hoffset.2.1
    apply hreal.trans
    calc
      _ ≤ ChartCap*(NarrowCap*3) := mul_le_mul hchart.1
        (mul_le_mul hnarrow.1 ho (Nat.cast_nonneg _) hNnon)
        (by positivity) hCnon
      _ = Cap := by dsimp only [Cap]; ring
  refine ⟨hcard,?_,?_,?_⟩
  · intro key hkey
    obtain ⟨ip,hip,he⟩ := Finset.mem_image.mp hkey
    have hk : key.1∈S.image chart := by
      rw [←he]
      exact Finset.mem_image_of_mem chart (hV ip hip)
    obtain ⟨iref,hiref,hkeyref,hxcenter,hycenter,hlocal⟩ := hchart.2.1 key.1 hk
    refine ⟨iref,hiref,hkeyref,hxcenter,hycenter,?_⟩
    intro jp hjp hjkey
    exact hlocal jp.1 (hV jp hjp) (congrArg Prod.fst hjkey)
  · intro ip hip jp hjp he
    have hn := hnarrow.2.1 ip.1 (hV ip hip) jp.1 (hV jp hjp)
      (congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.1) he)
    exact ⟨hn.1,hn.2,congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.2) he⟩
  · intro coeff
    let Keys := V.image color
    let g := fun key => ∑ ip∈V.filter (fun ip => color ip=key),coeff ip
    have he : (∑ key∈Keys,g key)=∑ ip∈V,coeff ip :=
      Finset.sum_fiberwise_of_maps_to (fun ip hip => Finset.mem_image_of_mem color hip) coeff
    have hnorm : ‖∑ ip∈V,coeff ip‖ ≤ ∑ key∈Keys,‖g key‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
      (f:=fun key => ‖g key‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ key∈Keys,‖g key‖)^12 ≤ (Keys.card:ℝ)^11*∑ key∈Keys,‖g key‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))

example
    {ι : Type*} (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (Q : ℕ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hscale : Tsrc ≤ E*T) (hQ : 0 < Q) (hθ : 0 < θ) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|)
    (hden : ∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      Cap^11*∑ key∈V.image color,
        ‖∑ ip∈V.filter (fun ip => color ip=key),coeff ip‖^12 :=
  HuxleyActualJointSourceScratch.positive_difference_actual_source_joint_twelfth_partition (ι:=ι) S Fsrc y z rat Q (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (η:=η) (Tsrc:=Tsrc) (T:=T) (M:=M) (E:=E) (σ:=σ) (δ:=δ) (θ:=θ) (a:=a) hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha hy hz hreg hjets htests hden


#print axioms positive_difference_actual_source_joint_twelfth_partition

end HuxleyActualJointSourceScratch
