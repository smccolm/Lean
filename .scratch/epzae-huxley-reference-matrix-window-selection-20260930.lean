import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyPairWindowScratch

theorem positive_difference_reference_matrix_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3)=h yb (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card := by
  classical
  intro f h hmap block S
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hnonneg ij (hij : ij∈P) : 0 ≤ ⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr (hbase ij hij)) hNp.le)
  have hwindow ij (hij : ij∈P) :
      za ij.1.1∈Icc (W+(N:ℝ)*block ij) (W+(N:ℝ)*((block ij:ℝ)+1)) := by
    have he : (block ij:ℤ)=⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
      Int.toNat_of_nonneg (hnonneg ij hij)
    have heR : (block ij:ℝ)=(⌊(za ij.1.1-W)/(N:ℝ)⌋:ℝ) := by exact_mod_cast he
    have hlo := Int.floor_le ((za ij.1.1-W)/(N:ℝ))
    have hhi := Int.lt_floor_add_one ((za ij.1.1-W)/(N:ℝ))
    rw [←heR] at hlo hhi
    have hl := (le_div_iff₀ hNp).mp hlo
    have hu := (div_lt_iff₀ hNp).mp hhi
    constructor <;> nlinarith only [hl,hu]
  have hex A ab j (hj : j∈S A ab) :
      ∃ ij, ij∈P ∧ Mat ij=A ∧ gap ij=ab ∧ block ij=j := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    exact ⟨ij,hh.1,hh.2.1,hh.2.2,he⟩
  let pick := fun A ab j => if hj : j∈S A ab then
    Classical.choose (hex A ab j hj) else ((0,0),(0,0))
  refine ⟨pick,?_,?_⟩
  · intro A _hA ab _hab j hj
    have hp : pick A ab j∈P ∧ Mat (pick A ab j)=A ∧
        gap (pick A ab j)=ab ∧ block (pick A ab j)=j := by
      dsimp only [pick]
      rw [dif_pos hj]
      exact Classical.choose_spec (hex A ab j hj)
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
    simpa only [hp.2.2.2] using hwindow (pick A ab j) hp.1
  · have hp := positive_difference_pair_card_le_physical_blocks
      P Mat F za zb AlenA Alen N Za Z W hσ hc hη hηmax hyb hf hnegative
      hT hM hN hz hgeometryA hgeometry hmap
    apply hp.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro A _hA
    let E := P.filter (fun ij => Mat ij=A)
    let I := E.image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)
    have hinj : Set.InjOn Int.toNat (↑I) := by
      intro x hx y hy he
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hy
      have hix := hnonneg ij (Finset.mem_filter.mp hij).1
      have hiy := hnonneg kl (Finset.mem_filter.mp hkl).1
      omega
    have he : I.card=(E.image block).card := by
      rw [←Finset.card_image_of_injOn hinj,Finset.image_image]
      rfl
    change I.card ≤ _
    rw [he]
    have hsub : E.image block ⊆ (P.image gap).biUnion (fun ab => S A ab) := by
      intro j hj
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hj
      have hh := Finset.mem_filter.mp hij
      exact Finset.mem_biUnion.mpr ⟨gap ij,Finset.mem_image_of_mem gap hh.1,
        Finset.mem_image.mpr ⟨ij,Finset.mem_filter.mpr ⟨hh.1,hh.2,rfl⟩,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

#print axioms positive_difference_reference_matrix_window_selection
example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3)=h yb (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card :=
  HuxleyPairWindowScratch.positive_difference_reference_matrix_window_selection P Mat gap F za zb AlenA Alen N Za Z W (σ:=σ) (c:=c) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) hσ hc hη hηmax hyb hf hnegative hT hM hN hbase hz hgeometryA hgeometry



theorem physicalModelPhase_reference_matrix_window_selection
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h 0 (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h 0 (za ij.1.1)+Mat ij 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card := by
  classical
  intro f h hmap block S
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hnonneg ij (hij : ij∈P) : 0 ≤ ⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr (hbase ij hij)) hNp.le)
  have hwindow ij (hij : ij∈P) :
      za ij.1.1∈Icc (W+(N:ℝ)*block ij) (W+(N:ℝ)*((block ij:ℝ)+1)) := by
    have he : (block ij:ℤ)=⌊(za ij.1.1-W)/(N:ℝ)⌋ :=
      Int.toNat_of_nonneg (hnonneg ij hij)
    have heR : (block ij:ℝ)=(⌊(za ij.1.1-W)/(N:ℝ)⌋:ℝ) := by exact_mod_cast he
    have hlo := Int.floor_le ((za ij.1.1-W)/(N:ℝ))
    have hhi := Int.lt_floor_add_one ((za ij.1.1-W)/(N:ℝ))
    rw [←heR] at hlo hhi
    have hl := (le_div_iff₀ hNp).mp hlo
    have hu := (div_lt_iff₀ hNp).mp hhi
    constructor <;> nlinarith only [hl,hu]
  have hex A ab j (hj : j∈S A ab) :
      ∃ ij, ij∈P ∧ Mat ij=A ∧ gap ij=ab ∧ block ij=j := by
    obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_filter.mp hij
    exact ⟨ij,hh.1,hh.2.1,hh.2.2,he⟩
  let pick := fun A ab j => if hj : j∈S A ab then
    Classical.choose (hex A ab j hj) else ((0,0),(0,0))
  refine ⟨pick,?_,?_⟩
  · intro A _hA ab _hab j hj
    have hp : pick A ab j∈P ∧ Mat (pick A ab j)=A ∧
        gap (pick A ab j)=ab ∧ block (pick A ab j)=j := by
      dsimp only [pick]
      rw [dif_pos hj]
      exact Classical.choose_spec (hex A ab j hj)
    refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
    simpa only [hp.2.2.2] using hwindow (pick A ab j) hp.1
  · have hmono : StrictMonoOn (h 1) (Ioo 0 (Wlim 1)) := by
      intro a ha b hb hab
      have hh := physicalModelPhase_halfCurvature_growth hσ hδ (hF 1)
        hT hM (hA 1) (hW 1) ha hb hab.le
      have hκ := modelPhaseThirdLower_pos hσ
      have hc : 0 < modelPhaseThirdLower σ*T/(2*M^3) := by positivity
      exact sub_pos.mp ((mul_pos hc (sub_pos.mpr hab)).trans_le hh)
    have hspan ij (hij : ij∈P) :
        (N:ℝ) ≤ (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ∧
        (Z:ℝ)+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ≤ 3*N := by
      have hg := hgeometry ij hij
      have hlo : (N:ℝ) ≤ Alen ij.2.1 := by exact_mod_cast hg.1
      have hhi : (Alen ij.2.1:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hg.2.1
      have he : (round (zb ij.2.1):ℝ)+(Alen ij.2.1:ℝ)=
          (Z:ℝ)+(N:ℝ)*ij.2.1+2*(N:ℝ) := by exact_mod_cast hg.2.2
      constructor <;> nlinarith only [hlo,hhi,he]
    have hprojection := curvature_pair_card_le_matrix_blocks P Mat (h 0) (h 1)
      za zb (Ioo 0 (Wlim 1)) hNp hmono.injOn hz hspan hmap
    let Vfirst := P.image (fun ij => (Mat ij,ij.1.1))
    have hcard : Vfirst.card=∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := by
      calc
        _ = ∑ B∈P.image Mat, (Vfirst.filter (fun v => v.1=B)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro v hv
          obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hv
          exact Finset.mem_image.mpr ⟨ij,hij,rfl⟩
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          have hImage : (Vfirst.filter (fun v => v.1=B)).image Prod.snd=
              (P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1) := by
            ext k
            simp only [Vfirst,Finset.mem_image,Finset.mem_filter]
            constructor
            · rintro ⟨v,⟨⟨ij,hij,he⟩,hvB⟩,hvk⟩
              refine ⟨ij,⟨hij,?_⟩,?_⟩
              · rw [←he] at hvB
                exact hvB
              · rw [←he] at hvk
                exact hvk
            · rintro ⟨ij,⟨hij,hB⟩,hk⟩
              exact ⟨(Mat ij,ij.1.1),⟨⟨ij,hij,rfl⟩,hB⟩,hk⟩
          rw [←hImage]
          symm
          apply Finset.card_image_of_injOn
          intro x hx y hy he
          exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
            (Finset.mem_filter.mp hy).2.symm) he
    change P.card ≤ 12*Vfirst.card at hprojection
    rw [hcard] at hprojection
    have hper B : ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card ≤
        5*((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      have hh := rounded_offset_floor_block_count
        ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1))
        za AlenA N Za W hN
        (by
          intro k hk
          obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hk
          exact hgeometryA ij (Finset.mem_filter.mp hij).1)
      simpa only [Finset.image_image] using hh
    have hp : P.card ≤ 60*∑ B∈P.image Mat,
        ((P.filter (fun ij => Mat ij=B)).image
          (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card := by
      calc
        _ ≤ 12*∑ B∈P.image Mat,
            ((P.filter (fun ij => Mat ij=B)).image (fun ij => ij.1.1)).card := hprojection
        _ ≤ 12*∑ B∈P.image Mat, 5*((P.filter (fun ij => Mat ij=B)).image
            (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card :=
          Nat.mul_le_mul_left 12 (Finset.sum_le_sum (fun B _ => hper B))
        _ = _ := by rw [←Finset.mul_sum]; ring
    apply hp.trans
    apply Nat.mul_le_mul_left 60
    apply Finset.sum_le_sum
    intro A _hA
    let E := P.filter (fun ij => Mat ij=A)
    let I := E.image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)
    have hinj : Set.InjOn Int.toNat (↑I) := by
      intro x hx y hy he
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hy
      have hix := hnonneg ij (Finset.mem_filter.mp hij).1
      have hiy := hnonneg kl (Finset.mem_filter.mp hkl).1
      omega
    have he : I.card=(E.image block).card := by
      rw [←Finset.card_image_of_injOn hinj,Finset.image_image]
      rfl
    change I.card ≤ _
    rw [he]
    have hsub : E.image block ⊆ (P.image gap).biUnion (fun ab => S A ab) := by
      intro j hj
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hj
      have hh := Finset.mem_filter.mp hij
      exact Finset.mem_biUnion.mpr ⟨gap ij,Finset.mem_image_of_mem gap hh.1,
        Finset.mem_image.mpr ⟨ij,Finset.mem_filter.mpr ⟨hh.1,hh.2,rfl⟩,rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (F : Fin 2 → ℝ → ℝ) (A Wlim : Fin 2 → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ)
    (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ δ T M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+Wlim i ≤ 2*M)
    (hbase : ∀ ij∈P, W ≤ za ij.1.1)
    (hz : ∀ ij∈P, zb ij.2.1∈Ioo 0 (Wlim 1))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h 0 (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h 0 (za ij.1.1)+Mat ij 3)=h 1 (zb ij.2.1)) →
    let block := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      ⌊(za ij.1.1-W)/(N:ℝ)⌋.toNat
    let S := fun A ab => (P.filter (fun ij => Mat ij=A ∧ gap ij=ab)).image block
    ∃ pick : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → (ℤ × Fin 2) × (ℤ × Fin 2),
      (∀ A∈P.image Mat, ∀ ab∈P.image gap, ∀ j∈S A ab,
        pick A ab j∈P ∧ Mat (pick A ab j)=A ∧ gap (pick A ab j)=ab ∧
        block (pick A ab j)=j ∧
        za (pick A ab j).1.1∈Icc (W+(N:ℝ)*j) (W+(N:ℝ)*((j:ℝ)+1))) ∧
      P.card ≤ 60*∑ A∈P.image Mat, ∑ ab∈P.image gap, (S A ab).card :=
  HuxleyPairWindowScratch.physicalModelPhase_reference_matrix_window_selection P Mat gap F A Wlim za zb AlenA Alen N Za Z W (σ:=σ) (δ:=δ) (T:=T) (M:=M) hσ hδ hF hT hM hN hA hW hbase hz hgeometryA hgeometry



#print axioms physicalModelPhase_reference_matrix_window_selection
end HuxleyPairWindowScratch
