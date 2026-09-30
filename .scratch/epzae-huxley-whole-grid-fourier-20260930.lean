import TaoTrudgianYang2025.HuxleyLinearForms

open Set
open scoped ContDiff FourierTransform BigOperators
open TaoTrudgianYang2025.HuxleyRationalPhase
namespace HuxleyWholeGridFourierScratch

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


theorem positive_difference_constructed_reference_family_whole_grid_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ),
      1 ≤ N → (∀ y∈Y, ∀ k, H y k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gref,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gref.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ))
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_controlled_complement_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N s H η T M R U hN hH hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    positive_difference_constructed_reference_system F hσ hc hJ hη hηmax hf hbound htests
      hnegative hT hM hNp hR hU hUmax hphase
  refine ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps,?_⟩
  intro V Gref
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hbudget⟩ :=
    positive_difference_reference_family_whole_grid_geometry F Y Refs
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hNp hR hU hphase
      (fun a ha b hb hne => (hsep a ha b hb hne).le)
      (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1)
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  intro t L delta Vbound
  have hyG i (hi : i∈Gref) : i.1∈Y := by
    have hh := Finset.mem_filter.mp hi
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hh.1).1).1
  obtain ⟨S,anchor,za,hS,hforQ⟩ := hentry (ℝ × (ℝ × ℝ)) Gref F N s
    (fun i k => H i.1 k) η T M R U Prod.fst x₁ x₂
    hN (fun i hi => hH i.1 (hyG i hi)) hη hηmax (fun i hi => hy i.1 (hyG i hi))
    hT hM hR hU hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    (fun i hi => (hgeometry i hi).1) (fun i hi => (hgeometry i hi).2.1) hdisjoint
    (fun i hi => (hgeometry i hi).2.2.2.2.2)

  have hencloseCurv y (hyY : y∈Y) : ∃ l∈Refs, ∃ u∈Refs, l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  refine ⟨S,anchor,za,hS,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall Good G Dlow Khigh Dhigh Dlog Cost
  have hfull (I : Finset ℤ) (hI : ∀ j∈I, t j∈Icc M (2*M)) :
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖)+
        (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ)) := by
    let Inner := (Gref ×ˢ I).filter (fun i =>
      x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4)
    have hgs := (hbudget (s:ℝ) I hI hencloseCurv).2 L H
      (fun y hyY j _ => Nat.cast_le.mpr (hH y hyY j))
    have hsub : Inner⊆Sall := by
      intro i hi
      have hh := Finset.mem_filter.mp hi
      have hg := Finset.mem_product.mp hh.1
      exact Finset.mem_biUnion.mpr ⟨i.1,hg.1,
        Finset.mem_image.mpr ⟨i.2,((hS i.1 hg.1).1 i.2).mpr hh.2,rfl⟩⟩
    have hsum :
        (∑ i∈Inner, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
        ∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    have he : (N:ℝ)*((Y.card:ℝ)*((24*J/σ)*M/((N:ℝ)*U)+28*σ*U/c+4)) =
        (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ)) := by
      field_simp
    exact hgs.trans ((add_le_add hsum le_rfl).trans_eq (congrArg (fun e => _+e) he))
  obtain ⟨r,z,hr,hzin,hdense,hround,hmodes⟩ := hforQ Q hQ hQN Acut Bmajor hAcut hAQ hBmajor
  refine ⟨r,z,hr,hzin,hdense,?_⟩
  intro m A q μ ℓ U₃
  refine ⟨hround,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,k,hraw,hnorm⟩ := hmodes K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ sPhase K x
  refine ⟨k,?_⟩
  intro FourierCost Cerror
  refine ⟨hraw,hnorm,?_⟩
  intro I hI BoundaryCost
  have hs := hfull I hI
  refine ⟨hs.trans (add_le_add hraw le_rfl),?_⟩
  intro hRQ hNR
  exact hs.trans (add_le_add (hnorm hRQ hNR) le_rfl)

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
  HuxleyWholeGridFourierScratch.positive_difference_reference_family_whole_grid_geometry F Y S (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hU hphase hsep hgapUpper

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ),
      1 ≤ N → (∀ y∈Y, ∀ k, H y k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gref,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gref.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ))
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyWholeGridFourierScratch.positive_difference_constructed_reference_family_whole_grid_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms finite_reference_closed_bracket
#print axioms grid_short_interval_card
#print axioms trimmed_grid_boundary_card
#print axioms reference_grid_missing_card
#print axioms finite_sum_le_tagged_image_add_complement
#print axioms positive_difference_reference_family_whole_grid_geometry
#print axioms positive_difference_constructed_reference_family_whole_grid_fourier
end HuxleyWholeGridFourierScratch
