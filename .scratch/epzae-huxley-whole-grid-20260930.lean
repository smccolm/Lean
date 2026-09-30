import TaoTrudgianYang2025.HuxleyLinearForms

open Set
open scoped ContDiff FourierTransform BigOperators
namespace HuxleyWholeGridScratch

private theorem finite_reference_closed_bracket (S : Finset ℝ) {l u lo hi x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlo : l ≤ lo) (hhi : hi ≤ u)
    (hwidth : lo < hi) (hx : x ∈ Icc lo hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧
      (∀ z ∈ S, ¬ (a < z ∧ z < b)) ∧ a < hi ∧ lo < b := by
  classical
  by_cases htop : x < hi
  · let A := S.filter (fun z => z ≤ x)
    let B := S.filter (fun z => x < z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,hlo.trans hx.1⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,htop.trans_le hhi⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_lt hb.2,ha.2,hb.2.le,?_,
      ha.2.trans_lt htop,hx.1.trans_lt hb.2⟩
    intro z hz hzab
    by_cases hzx : z ≤ x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,lt_of_not_ge hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2
  · have hxe : x = hi := le_antisymm hx.2 (le_of_not_gt htop)
    let A := S.filter (fun z => z < x)
    let B := S.filter (fun z => x ≤ z)
    have hA : A.Nonempty := ⟨l,Finset.mem_filter.mpr ⟨hl,by linarith⟩⟩
    have hB : B.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,by linarith⟩⟩
    let a := A.max' hA
    let b := B.min' hB
    have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
    have hb := Finset.mem_filter.mp (Finset.min'_mem B hB)
    refine ⟨a,ha.1,b,hb.1,ha.2.trans_le hb.2,ha.2.le,hb.2,?_,
      by simpa only [hxe] using ha.2,by linarith only [hwidth,hxe,hb.2]⟩
    intro z hz hzab
    by_cases hzx : z < x
    · have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz,hzx⟩
      exact (not_lt_of_ge (Finset.le_max' A z hzA)) hzab.1
    · have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz,le_of_not_gt hzx⟩
      exact (not_lt_of_ge (Finset.min'_le B z hzB)) hzab.2

private theorem grid_short_interval_card (K : Finset ℤ) {s N a : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ a+N/4) :
    K.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hiw := hK i hi
  have hjw := hK j hj
  have hij : (i:ℝ) < (j:ℝ)+1 := by nlinarith
  have hji : (j:ℝ) < (i:ℝ)+1 := by nlinarith
  have hij' : i < j+1 := by exact_mod_cast hij
  have hji' : j < i+1 := by exact_mod_cast hji
  omega

private theorem trimmed_grid_boundary_card (K : Finset ℤ) {s N a b : ℝ}
    (hN : 0 < N)
    (hK : ∀ k ∈ K, a ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b ∧
      ¬(a+N/4 ≤ s+N*(k:ℝ) ∧ s+N*(k:ℝ) ≤ b-N/4)) :
    K.card ≤ 2 := by
  classical
  let L := K.filter (fun k : ℤ => s+N*(k:ℝ) < a+N/4)
  let R := K.filter (fun k : ℤ => b-N/4 < s+N*(k:ℝ))
  have hL : L.card ≤ 1 := grid_short_interval_card L hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨(hK k hh.1).1,hh.2.le⟩)
  have hR : R.card ≤ 1 := grid_short_interval_card R hN (by
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact ⟨hh.2.le,by linarith only [(hK k hh.1).2.1]⟩)
  have hsub : K ⊆ L∪R := by
    intro k hk
    by_cases hleft : s+N*(k:ℝ) < a+N/4
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk,hleft⟩))
    · have hr : b-N/4 < s+N*(k:ℝ) := by
        by_contra hnot
        exact (hK k hk).2.2 ⟨le_of_not_gt hleft,le_of_not_gt hnot⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hk,hr⟩))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le L R)
  omega


private theorem reference_grid_missing_card
    (Y S : Finset ℝ) (I : Finset ℤ) (h : ℝ → ℝ → ℝ)
    {M N s C : ℝ} (hM : 0 < M) (hN : 0 < N) (hC : 0 ≤ C)
    (hI : ∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M))
    (hmono : ∀ y∈Y, StrictMonoOn (h y) (Icc M (2*M)))
    (henclose : ∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u)
    (x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ) :
    let V := (Y ×ˢ (S ×ˢ S)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ z∈S, ¬(i.2.1 < z ∧ z < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let G := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (∀ i∈G, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧
      h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2) →
    (∀ i∈V, ∀ j∈I, ∀ k∈I,
      h i.1 (s+N*(j:ℝ))∈Icc i.2.1 i.2.2 →
      h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2 →
      |(s+N*(k:ℝ))-(s+N*(j:ℝ))| ≤ C*N) →
    let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
      x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
    (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
  classical
  intro V G hroots hwidth Bad
  let K := fun i : ℝ × (ℝ × ℝ) => I.filter (fun k : ℤ =>
    (i.1,k)∈Bad ∧ h i.1 (s+N*(k:ℝ))∈Icc i.2.1 i.2.2)
  have hVdata i (hi : i∈V) : i.1∈Y := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1
  have hcover : Bad ⊆ V.biUnion (fun i => (K i).image (fun k => (i.1,k))) := by
    intro p hp
    have hpfull := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose p.1 hpfull.1
    have hleft : M∈Icc M (2*M) := ⟨le_rfl,by linarith only [hM]⟩
    have hright : 2*M∈Icc M (2*M) := ⟨by linarith only [hM],le_rfl⟩
    have hm := hmono p.1 hpfull.1
    have hpr := hI p.2 hpfull.2
    have hcurv : h p.1 (s+N*(p.2:ℝ))∈Icc (h p.1 M) (h p.1 (2*M)) :=
      ⟨hm.monotoneOn hleft hpr hpr.1,hm.monotoneOn hpr hright hpr.2⟩
    obtain ⟨a,ha,b,hb,hab,hax,hxb,hadj,hahi,hlob⟩ :=
      finite_reference_closed_bracket S hl hu hlo hhi
        (hm hleft hright (by linarith only [hM])) hcurv
    have hi : (p.1,(a,b))∈V :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hpfull.1,Finset.mem_product.mpr ⟨ha,hb⟩⟩,hab,hadj,hahi,hlob⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(p.1,(a,b)),hi,Finset.mem_image.mpr ?_⟩
    exact ⟨p.2,Finset.mem_filter.mpr ⟨hpfull.2,hp,hax,hxb⟩,Prod.eta p⟩
  have hKgood i (hi : i∈G) : (K i).card ≤ 2 := by
    apply trimmed_grid_boundary_card (K i) hN
    intro k hk
    have hh := Finset.mem_filter.mp hk
    have hr := hroots i hi
    have hm := hmono i.1 (hVdata i (Finset.mem_filter.mp hi).1)
    have hpk := hI k hh.1
    have hlo : x₁ i ≤ s+N*(k:ℝ) := by
      by_contra hnot
      have hz := hm hpk hr.1 (lt_of_not_ge hnot)
      rw [hr.2.2.1] at hz
      exact (not_lt_of_ge hh.2.2.1) hz
    have hhi : s+N*(k:ℝ) ≤ x₂ i := by
      by_contra hnot
      have hz := hm hr.2.1 hpk (lt_of_not_ge hnot)
      rw [hr.2.2.2] at hz
      exact (not_lt_of_ge hh.2.2.2) hz
    refine ⟨hlo,hhi,?_⟩
    intro htrim
    exact (Finset.mem_filter.mp hh.2.1).2 ⟨i,hi,rfl,htrim⟩
  have hKall i (hi : i∈V) : ((K i).card:ℝ) ≤ 2+C := by
    apply TaoTrudgianYang2025.HuxleyRationalPhase.physical_block_count_of_pairwise_width
      (K i) (fun k => s+N*(k:ℝ)) (Z:=s) hN hC
    · intro k _
      constructor <;> nlinarith only [hN]
    · intro j hj k hk
      have hjd := Finset.mem_filter.mp hj
      have hkd := Finset.mem_filter.mp hk
      exact hwidth i hi j hjd.1 k hkd.1 hjd.2.2 hkd.2.2
  have hcard : Bad.card ≤ ∑ i∈V, (K i).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun i _ => Finset.card_image_le)))
  have hcardR : (Bad.card:ℝ) ≤ ∑ i∈V, ((K i).card:ℝ) := by exact_mod_cast hcard
  have hsum : (∑ i∈V, ((K i).card:ℝ)) ≤
      ∑ i∈V, (2 + if i∈G then 0 else C) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hg : i∈G
    · simpa only [if_pos hg,add_zero] using
        (show ((K i).card:ℝ) ≤ 2 by exact_mod_cast hKgood i hg)
    · simpa only [if_neg hg] using hKall i hi
  have he : (∑ i∈V, (2 + if i∈G then (0:ℝ) else C)) =
      2*(V.card:ℝ)+C*((V\G).card:ℝ) := by
    rw [Finset.sum_add_distrib]
    have hid : (∑ i∈V, if i∈G then (0:ℝ) else C) = ∑ i∈V\G, C := by
      conv_rhs => rw [Finset.sdiff_eq_filter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈G <;> simp only [hi,if_true,if_false,not_true_eq_false,not_false_eq_true]
    rw [hid]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  exact hcardR.trans (hsum.trans_eq he)


private theorem finite_sum_le_tagged_image_add_complement
    {α β : Type*} [DecidableEq α] (A : Finset α) (B : Finset β)
    (g : β → α) (w : α → ℝ) {N : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hupper : ∀ a∈A, w a ≤ N) :
    (∑ a∈A, w a) ≤ (∑ b∈B, w (g b))+N*((A\B.image g).card:ℝ) := by
  classical
  have hc : (∑ a∈A∩B.image g, w a) ≤ ∑ b∈B, w (g b) :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun a _ _ => hw a)).trans (Finset.sum_image_le_of_nonneg (fun a _ => hw a))
  have hb : (∑ a∈A\B.image g, w a) ≤ N*((A\B.image g).card:ℝ) := by
    calc
      (∑ a∈A\B.image g, w a) ≤ ∑ _a∈A\B.image g, N :=
        Finset.sum_le_sum (fun a ha => hupper a (Finset.mem_sdiff.mp ha).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have he : (∑ a∈A∩B.image g, w a)+(∑ a∈A\B.image g, w a)=∑ a∈A, w a := by
    simpa only [Finset.filter_mem_eq_inter,←Finset.sdiff_eq_filter] using
      Finset.sum_filter_add_sum_filter_not A (fun a => a∈B.image g) w
  linarith only [hc,hb,he]


theorem positive_difference_reference_family_whole_grid_geometry
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
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      (∀ (s : ℝ) (I : Finset ℤ),
        (∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M)) →
        (∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u) →
        let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
          x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
        let Inner := (G ×ˢ I).filter (fun i =>
          x₁ i.1+N/4 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1-N/4)
        let ErrorCount := (Y.card:ℝ)*((24*J/σ)*M/(N*U)+28*σ*U/c+4)
        (Bad.card:ℝ) ≤ ErrorCount ∧
        ∀ (L : ℤ → ℤ) (H : ℝ → ℤ → ℕ),
          (∀ y∈Y, ∀ k∈I, (H y k:ℝ) ≤ N) →
          (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
            (𝐞 (f p.1 n):ℂ)‖) ≤
          (∑ i∈Inner, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),
            (𝐞 (f i.1.1 n):ℂ)‖)+N*ErrorCount) := by
  classical
  intro f h V G
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_family_interior_geometry
      F Y S hσ hc hJ hη hηmax hy hf hbound htests hnegative
      hT hM hN hR hU hphase hsep hgapUpper
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  intro s I hI henclose Bad Inner ErrorCount
  have hm y (hyY : y∈Y) : StrictMonoOn (h y) (Icc M (2*M)) := by
    apply (TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_curvature_strictMono
      F hσ hc hη hηmax (hy y hyY) hf hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hraw := reference_grid_missing_card Y S I h hM hN
    (show 0 ≤ (14*σ/c)*U by positivity) hI hm henclose x₁ x₂
    (fun i hi => ⟨(hgeometry i hi).1,(hgeometry i hi).2.1,
      (hgeometry i hi).2.2.2.1,(hgeometry i hi).2.2.2.2.1⟩) (by
      intro i hi j hj k hk hjc hkc
      have hv := Finset.mem_filter.mp hi
      have hp := Finset.mem_product.mp hv.1
      have hs := Finset.mem_product.mp hp.2
      have hgap := hgapUpper _ hs.1 _ hs.2 hv.2.1 hv.2.2.1
      apply TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width
        F hσ hc hη hηmax (hy i.1 hp.1) hf hnegative hT hM hN hR hphase
        (hI j hj) (hI k hk)
      change |h i.1 (s+N*(k:ℝ))-h i.1 (s+N*(j:ℝ))| ≤ 7*U/(2*R^2)
      apply (abs_le.mpr ?_).trans hgap
      constructor <;> linarith only [hjc.1,hjc.2,hkc.1,hkc.2])
  have hbd : ((V\G).card:ℝ) ≤ 2*(Y.card:ℝ) := by exact_mod_cast hboundary
  have hcount : (Bad.card:ℝ) ≤ ErrorCount := by
    calc
      (Bad.card:ℝ) ≤ 2*(V.card:ℝ)+((14*σ/c)*U)*((V\G).card:ℝ) := hraw
      _ ≤ 2*(((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ))+
          ((14*σ/c)*U)*(2*(Y.card:ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hpack (by norm_num))
          (mul_le_mul_of_nonneg_left hbd (by positivity))
      _ = ErrorCount := by dsimp only [ErrorCount]; ring
  refine ⟨hcount,?_⟩
  intro L H hH
  let w := fun p : ℝ × ℤ => ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
  have he : Bad=(Y ×ˢ I)\Inner.image tag := by
    ext p
    constructor
    · intro hp
      have hh := Finset.mem_filter.mp hp
      apply Finset.mem_sdiff.mpr
      refine ⟨hh.1,?_⟩
      intro hin
      obtain ⟨⟨i,k⟩,hik,hpeq⟩ := Finset.mem_image.mp hin
      have hd := Finset.mem_filter.mp hik
      have hg := Finset.mem_product.mp hd.1
      have hye : i.1=p.1 := congrArg Prod.fst hpeq
      have hke : k=p.2 := congrArg Prod.snd hpeq
      exact hh.2 ⟨i,hg.1,hye.symm,by simpa only [hke] using hd.2⟩
    · intro hp
      have hh := Finset.mem_sdiff.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hh.1,?_⟩
      rintro ⟨i,hi,hye,htrim⟩
      apply hh.2
      apply Finset.mem_image.mpr
      refine ⟨(i,p.2),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hi,(Finset.mem_product.mp hh.1).2⟩,htrim⟩,?_⟩
      exact Prod.ext hye.symm rfl
  have hwbound p (hp : p∈Y ×ˢ I) : w p ≤ N := by
    have hh := Finset.mem_product.mp hp
    have hsum : w p ≤ H p.1 p.2 := by
      apply (norm_sum_le _ _).trans_eq
      simp
    exact hsum.trans (hH p.1 hh.1 p.2 hh.2)
  have hs := finite_sum_le_tagged_image_add_complement
    (Y ×ˢ I) Inner tag w (fun _ => norm_nonneg _) hwbound
  rw [←he] at hs
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hN.le))

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
      (∀ i∈G, ∀ j∈G, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      (∀ (s : ℝ) (I : Finset ℤ),
        (∀ k∈I, s+N*(k:ℝ)∈Icc M (2*M)) →
        (∀ y∈Y, ∃ l∈S, ∃ u∈S, l ≤ h y M ∧ h y (2*M) ≤ u) →
        let Bad := (Y ×ˢ I).filter (fun p => ¬∃ i∈G, p.1=i.1 ∧
          x₁ i+N/4 ≤ s+N*(p.2:ℝ) ∧ s+N*(p.2:ℝ) ≤ x₂ i-N/4)
        let Inner := (G ×ˢ I).filter (fun i =>
          x₁ i.1+N/4 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1-N/4)
        let ErrorCount := (Y.card:ℝ)*((24*J/σ)*M/(N*U)+28*σ*U/c+4)
        (Bad.card:ℝ) ≤ ErrorCount ∧
        ∀ (L : ℤ → ℤ) (H : ℝ → ℤ → ℕ),
          (∀ y∈Y, ∀ k∈I, (H y k:ℝ) ≤ N) →
          (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),
            (𝐞 (f p.1 n):ℂ)‖) ≤
          (∑ i∈Inner, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),
            (𝐞 (f i.1.1 n):ℂ)‖)+N*ErrorCount) :=
  HuxleyWholeGridScratch.positive_difference_reference_family_whole_grid_geometry F Y S (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep hgapUpper


#print axioms positive_difference_reference_family_whole_grid_geometry
#print axioms finite_sum_le_tagged_image_add_complement
#print axioms reference_grid_missing_card
#print axioms finite_reference_closed_bracket
#print axioms grid_short_interval_card
#print axioms trimmed_grid_boundary_card
end HuxleyWholeGridScratch
