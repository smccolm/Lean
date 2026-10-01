import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical
namespace HuxleySourceEndpointTrimScratch
private theorem actual_tagged_grid_endpoint_trim
    {ι : Type*} (S : Finset (ι × ℤ)) (Y : Finset ℝ)
    (y x₁ x₂ : ι → ℝ) {M N s B C : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hinj : Set.InjOn (fun i : ι × ℤ => (y i.1,i.2)) (S : Set _))
    (hy : ∀ i∈S, y i.1∈Y)
    (hgeometry : ∀ i∈S, M ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M ∧
      x₂ i.1-x₁ i.1 ≤ C*N)
    (hwindow : ∀ i∈S, x₁ i.1 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1) :
    let Inner := S.filter (fun i => M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B)
    ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) ∧
    (∀ i∈Inner, M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) ∧
    ∀ (w : ι × ℤ → ℝ), (∀ i∈S, w i ≤ N) →
      (∑ i∈S, w i) ≤ (∑ i∈Inner, w i)+(Y.card:ℝ)*(2*N+2*B+2*C*N) := by
  classical
  intro Inner
  have hwidth : 0 ≤ B+C*N := add_nonneg hB (mul_nonneg hC hN.le)
  obtain ⟨Ileft,hIl,_hIll,hIlu⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=M) (z:=M+B+C*N) hN (by linarith only [hwidth])
  obtain ⟨Iright,hIr,_hIrl,hIru⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=2*M-B-C*N) (z:=2*M) hN (by linarith only [hwidth])
  have hcover : (S\Inner).card ≤ (Y ×ˢ (Ileft ∪ Iright)).card := by
    apply Finset.card_le_card_of_injOn (fun i : ι × ℤ => (y i.1,i.2))
    · intro i hi
      obtain ⟨hiS,hiNot⟩ := Finset.mem_sdiff.mp hi
      refine Finset.mem_product.mpr ⟨hy i hiS,?_⟩
      have hbad : ¬(M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) := by
        intro hgood
        exact hiNot (Finset.mem_filter.mpr ⟨hiS,hgood⟩)
      have hg := hgeometry i hiS
      have hw := hwindow i hiS
      by_cases hl : M+B ≤ x₁ i.1
      · apply Finset.mem_union.mpr
        right
        apply (hIr i.2).mpr
        have hr : 2*M-B < x₂ i.1 := lt_of_not_ge (fun hr => hbad ⟨hl,hr⟩)
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hr]
      · apply Finset.mem_union.mpr
        left
        apply (hIl i.2).mpr
        have hl' : x₁ i.1 < M+B := lt_of_not_ge hl
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hl']
    · intro i hi j hj he
      exact hinj (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 he
  have hcount : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) := by
    have hc : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*((Ileft.card:ℝ)+(Iright.card:ℝ)) := by
      exact_mod_cast hcover.trans
        ((Finset.card_product Y (Ileft ∪ Iright)).le.trans
          (Nat.mul_le_mul_left Y.card (Finset.card_union_le Ileft Iright)))
    have hinterval : (Ileft.card:ℝ)+(Iright.card:ℝ) ≤ 2+2*(B+C*N)/N := by
      have hh := add_le_add hIlu hIru
      convert hh using 1
      ring
    exact hc.trans (mul_le_mul_of_nonneg_left hinterval (Nat.cast_nonneg _))
  refine ⟨hcount,(fun i hi => (Finset.mem_filter.mp hi).2),?_⟩
  intro w hw
  have hcost : (∑ i∈S\Inner, w i) ≤ N*((S\Inner).card:ℝ) := by
    calc
      _ ≤ ∑ _i∈S\Inner, N := Finset.sum_le_sum (fun i hi => hw i (Finset.mem_sdiff.mp hi).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have hphysical : N*((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2*N+2*B+2*C*N) := by
    have hh := mul_le_mul_of_nonneg_left hcount hN.le
    convert hh using 1
    field_simp
    ring
  have hsplit : (∑ i∈Inner,w i)+(∑ i∈S\Inner,w i)=∑ i∈S,w i :=
    by simpa only [add_comm] using Finset.sum_sdiff (f:=w) (Finset.filter_subset _ _)
  linarith only [hcost,hphysical,hsplit]

private theorem source_integer_window_of_endpoint_buffer
    {M B D z : ℝ} (hB : D+2 ≤ B) (hz : z∈Ioo (M+B) (2*M-B)) :
    let A : ℤ := ⌈M⌉
    let W := 2*M-(A:ℝ)
    M ≤ (A:ℝ) ∧ (A:ℝ)+W=2*M ∧
    ∀ d : ℝ, |d| ≤ D → z-(A:ℝ)+d∈Ioo (1/2:ℝ) (W-1/2) := by
  intro A W
  have hceilLow : M ≤ (A:ℝ) := Int.le_ceil M
  have hceilHigh : (A:ℝ) < M+1 := Int.ceil_lt_add_one M
  refine ⟨hceilLow,by dsimp only [W]; ring,?_⟩
  intro d hd
  have hdb := abs_le.mp hd
  change (1/2:ℝ) < z-(A:ℝ)+d ∧ z-(A:ℝ)+d < 2*M-(A:ℝ)-1/2
  constructor <;> linarith only [hz.1,hz.2,hB,hdb.1,hdb.2,hceilHigh]

example
    {ι : Type*} (S : Finset (ι × ℤ)) (Y : Finset ℝ)
    (y x₁ x₂ : ι → ℝ) {M N s B C : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hinj : Set.InjOn (fun i : ι × ℤ => (y i.1,i.2)) (S : Set _))
    (hy : ∀ i∈S, y i.1∈Y)
    (hgeometry : ∀ i∈S, M ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M ∧
      x₂ i.1-x₁ i.1 ≤ C*N)
    (hwindow : ∀ i∈S, x₁ i.1 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1) :
    let Inner := S.filter (fun i => M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B)
    ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) ∧
    (∀ i∈Inner, M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) ∧
    ∀ (w : ι × ℤ → ℝ), (∀ i∈S, w i ≤ N) →
      (∑ i∈S, w i) ≤ (∑ i∈Inner, w i)+(Y.card:ℝ)*(2*N+2*B+2*C*N) :=
  HuxleySourceEndpointTrimScratch.actual_tagged_grid_endpoint_trim (ι:=ι) S Y y x₁ x₂ (M:=M) (N:=N) (s:=s) (B:=B) (C:=C) hN hB hC hinj hy hgeometry hwindow

example
    {M B D z : ℝ} (hB : D+2 ≤ B) (hz : z∈Ioo (M+B) (2*M-B)) :
    let A : ℤ := ⌈M⌉
    let W := 2*M-(A:ℝ)
    M ≤ (A:ℝ) ∧ (A:ℝ)+W=2*M ∧
    ∀ d : ℝ, |d| ≤ D → z-(A:ℝ)+d∈Ioo (1/2:ℝ) (W-1/2) :=
  HuxleySourceEndpointTrimScratch.source_integer_window_of_endpoint_buffer (M:=M) (B:=B) (D:=D) (z:=z) hB hz


#print axioms actual_tagged_grid_endpoint_trim
#print axioms source_integer_window_of_endpoint_buffer
end HuxleySourceEndpointTrimScratch
