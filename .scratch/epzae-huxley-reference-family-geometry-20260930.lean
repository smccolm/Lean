import TaoTrudgianYang2025.HuxleyLinearForms

open Set Polynomial TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical
namespace HuxleyReferenceFamilyScratch

private theorem adjacent_reference_pairs_order
    (S : Finset ℝ) {a b : ℝ × ℝ}
    (ha : a.1∈S ∧ a.2∈S ∧ a.1<a.2 ∧ ∀ t∈S, ¬(a.1<t ∧ t<a.2))
    (hb : b.1∈S ∧ b.2∈S ∧ b.1<b.2 ∧ ∀ t∈S, ¬(b.1<t ∧ t<b.2))
    (hne : a≠b) : a.2 ≤ b.1 ∨ b.2 ≤ a.1 := by
  rcases lt_trichotomy a.1 b.1 with hlt | he | hgt
  · left
    exact le_of_not_gt (fun hh => ha.2.2.2 _ hb.1 ⟨hlt,hh⟩)
  · exfalso
    apply hne
    apply Prod.ext he
    rcases lt_trichotomy a.2 b.2 with hlt₂ | he₂ | hgt₂
    · exact False.elim (hb.2.2.2 _ ha.2.1 ⟨by rw [←he]; exact ha.2.2.1,hlt₂⟩)
    · exact he₂
    · exact False.elim (ha.2.2.2 _ hb.2.1 ⟨by rw [he]; exact hb.2.2.1,hgt₂⟩)
  · right
    exact le_of_not_gt (fun hh => hb.2.2.2 _ ha.1 ⟨hgt,hh⟩)

private theorem adjacent_reference_crossing_family_card
    (Y S : Finset ℝ) (E : Finset (ℝ × (ℝ × ℝ))) (t : ℝ → ℝ)
    (hdata : ∀ i∈E, i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ u∈S, ¬(i.2.1 < u ∧ u < i.2.2)) ∧
      i.2.1 < t i.1 ∧ t i.1 < i.2.2) :
    E.card ≤ Y.card := by
  classical
  have hinj : Set.InjOn Prod.fst (E : Set (ℝ × (ℝ × ℝ))) := by
    intro i hi j hj he
    by_contra hne
    have hp : i.2≠j.2 := fun hh => hne (Prod.ext he hh)
    have ho := adjacent_reference_pairs_order S (hdata i hi).2.1 (hdata j hj).2.1 hp
    have hti := (hdata i hi).2.2
    have htj := (hdata j hj).2.2
    rw [←he] at htj
    rcases ho with hleft | hright
    · linarith only [hti.1,hti.2,htj.1,htj.2,hleft]
    · linarith only [hti.1,hti.2,htj.1,htj.2,hright]
  have hsub : E.image Prod.fst ⊆ Y := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact (hdata i hi).1
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub


/-- The literal occupied reference family supplies its own physical
interior endpoints and same-phase disjointness. At most two gaps per
phase meet the physical range without lying wholly inside it. -/
theorem positive_difference_reference_family_interior_geometry
    (F : ℝ → ℝ) (Y S : Finset ℝ)
    {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) := by
  classical
  intro f h V G
  have hVdata i (hi : i∈V) : i.1∈Y ∧
      (i.2.1∈S ∧ i.2.2∈S ∧ i.2.1 < i.2.2 ∧ ∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
      i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2 := by
    have hh := Finset.mem_filter.mp hi
    have hp := Finset.mem_product.mp hh.1
    have he := Finset.mem_product.mp hp.2
    exact ⟨hp.1,⟨he.1,he.2,hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩
  have hGS : G⊆V := Finset.filter_subset _ _
  let Left := V.filter (fun i => i.2.1 < h i.1 M)
  let Right := V.filter (fun i => h i.1 (2*M) < i.2.2)
  have hleft : Left.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Left (fun y => h y M)
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    exact ⟨hd.1,hd.2.1,hh.2,hd.2.2.2⟩
  have hright : Right.card ≤ Y.card := by
    apply adjacent_reference_crossing_family_card Y S Right (fun y => h y (2*M))
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    exact ⟨hd.1,hd.2.1,hd.2.2.1,hh.2⟩
  have hbadSub : V \ G ⊆ Left∪Right := by
    intro i hi
    have hh := Finset.mem_sdiff.mp hi
    by_cases hlo : h i.1 M ≤ i.2.1
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      by_contra hnot
      exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,hlo,le_of_not_gt hnot⟩)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hh.1,lt_of_not_ge hlo⟩))
  have hboundary : (V \ G).card ≤ 2*Y.card := by
    have hh := (Finset.card_le_card hbadSub).trans (Finset.card_union_le Left Right)
    omega
  have hphaseCount : (G.image Prod.fst).card ≤ Y.card := by
    apply Finset.card_le_card
    intro y hyG
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hyG
    exact (hVdata i (hGS hi)).1
  have hmono y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax
      (hy y hyY) hf hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hcont y (hyY : y∈Y) : ContinuousOn (h y) (Icc M (2*M)) := by
    intro w hw
    have hw0 : 0 < w/M := div_pos (hM.trans_le hw.1) hM
    have hs0 : 0 < w/M+η*y := add_pos hw0 (mul_pos hη (zero_lt_one.trans_le (hy y hyY).1))
    have hcf : ContDiffAt ℝ 3 (f y) w :=
      (contDiffAt_const.mul (((hf _ hw0).comp w (contDiffAt_id.div_const M)).sub
        ((hf _ hs0).comp w ((contDiffAt_id.div_const M).add contDiffAt_const)))).div_const
        (σ*η) |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
    exact ((hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) hcf).div_const 2).continuousAt.continuousWithinAt
  have hex : ∀ i∈G, ∃ a b : ℝ, a∈Icc M (2*M) ∧ b∈Icc M (2*M) ∧
      h i.1 a=i.2.1 ∧ h i.1 b=i.2.2 := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hd := hVdata i hh.1
    have ha : i.2.1∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hh.2.1,hd.2.2.1.le⟩
    have hb : i.2.2∈Icc (h i.1 M) (h i.1 (2*M)) := ⟨hd.2.2.2.le,hh.2.2⟩
    obtain ⟨a,haM,hae⟩ := intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) (hcont i.1 hd.1) ha
    obtain ⟨b,hbM,hbe⟩ := intermediate_value_Icc (by linarith only [hM] : M ≤ 2*M) (hcont i.1 hd.1) hb
    exact ⟨a,b,haM,hbM,hae,hbe⟩
  choose! x₁ x₂ hroots using hex
  have hpack := positive_difference_reference_family_packing F Y S hσ hc hJ
    hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,?_,?_⟩
  · intro i hi
    have hd := hVdata i (hGS hi)
    have hr := hroots i hi
    have hlt : x₁ i < x₂ i := by
      by_contra hnot
      have hh := (hmono i.1 hd.1).monotoneOn hr.2.1 hr.1 (le_of_not_gt hnot)
      rw [hr.2.2.1,hr.2.2.2] at hh
      exact (not_le_of_gt hd.2.1.2.2.1) hh
    refine ⟨hr.1,hr.2.1,hlt,hr.2.2.1,hr.2.2.2,?_,?_⟩
    · rw [hr.2.2.1,hr.2.2.2]
      have hh := hsep _ hd.2.1.1 _ hd.2.1.2.1 (ne_of_lt hd.2.1.2.2.1)
      rw [abs_sub_comm,abs_of_pos (sub_pos.mpr hd.2.1.2.2.1)] at hh
      exact hh
    · rw [hr.2.2.1,hr.2.2.2]
      exact hgapUpper _ hd.2.1.1 _ hd.2.1.2.1 hd.2.1.2.2.1 hd.2.1.2.2.2
  · intro i hi j hj hne hye
    have hdi := hVdata i (hGS hi)
    have hdj := hVdata j (hGS hj)
    have hp : i.2≠j.2 := fun he => hne (Prod.ext hye he)
    have ho := adjacent_reference_pairs_order S hdi.2.1 hdj.2.1 hp
    have hri := hroots i hi
    have hrj := hroots j hj
    have hjleft : h i.1 (x₁ j)=j.2.1 := by simpa only [hye] using hrj.2.2.1
    have hjright : h i.1 (x₂ j)=j.2.2 := by simpa only [hye] using hrj.2.2.2
    rcases ho with hleft | hright
    · left
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hrj.1 hri.2.1 hbad
      rw [hjleft,hri.2.2.2] at hh
      exact (not_lt_of_ge hleft) hh
    · right
      apply le_of_not_gt
      intro hbad
      have hh := hmono i.1 hdi.1 hri.1 hrj.2.1 hbad
      rw [hri.2.2.1,hjright] at hh
      exact (not_lt_of_ge hright) hh

example
    (F : ℝ → ℝ) (Y S : Finset ℝ)
    {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3)
    (hsep : ∀ a∈S, ∀ b∈S, a≠b → U/(4*R^2) ≤ |a-b|)
    (hgapUpper : ∀ a∈S, ∀ b∈S, a<b →
      (∀ t∈S, ¬(a<t ∧ t<b)) → b-a ≤ 7*U/(2*R^2)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈S, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ G).card ≤ 2*Y.card ∧ (G.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) :=
  HuxleyReferenceFamilyScratch.positive_difference_reference_family_interior_geometry F Y S (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep hgapUpper

#print axioms positive_difference_reference_family_interior_geometry
#print axioms adjacent_reference_pairs_order
#print axioms adjacent_reference_crossing_family_card
end HuxleyReferenceFamilyScratch
