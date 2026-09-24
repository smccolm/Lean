import TaoTrudgianYang2025.ZetaReflectionFrequencyBlocks

/-! Exact three-set selection without rounding away nonempty source families. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem exists_reflection_three_cover {α : Type*} (W : Finset α)
    (hW : W.Nonempty) (p : Fin 3 → α → Prop)
    (hcover : ∀ v ∈ W, ∃ i : Fin 3, p i v) :
    ∃ i : Fin 3, ∃ U : Finset α, U.Nonempty ∧ U ⊆ W ∧
      (W.card : ℝ)/3 ≤ (U.card : ℝ) ∧ ∀ v ∈ U, p i v := by
  have hsub : W ⊆ Finset.univ.biUnion (fun i : Fin 3 => W.filter (p i)) := by
    intro v hv
    obtain ⟨i,hi⟩ := hcover v hv
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hi⟩⟩
  have hc : W.card ≤ ∑ i : Fin 3, (W.filter (p i)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcr : (W.card : ℝ) ≤ ∑ i : Fin 3, ((W.filter (p i)).card : ℝ) := by
    exact_mod_cast hc
  have hs : (∑ _i : Fin 3, (W.card : ℝ)/3) ≤
      ∑ i : Fin 3, ((W.filter (p i)).card : ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    linarith
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  refine ⟨i,W.filter (p i),?_,Finset.filter_subset _ _,hi,
    fun _ ht => (Finset.mem_filter.mp ht).2⟩
  apply Finset.card_pos.mp
  have hp : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hq : (0 : ℝ) < (W.filter (p i)).card := lt_of_lt_of_le (by positivity) hi
  exact_mod_cast hq

theorem exists_reflection_large_frequency_block {m b : ℕ} (hb : b ≤ 8*m)
    (t A : ℝ) (hA : A ≤ ‖∑ n ∈ Finset.Icc (m+1) b, dirichletPhase n t‖) :
    ∃ i : Fin 3, A/3 ≤ ‖∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t‖ := by
  have hs : A ≤ ∑ i : Fin 3, ‖∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t‖ :=
    hA.trans ((sum_reflectionDyadicBlock hb t).symm ▸ norm_sum_le _ _)
  have hc : (∑ _i : Fin 3, A/3) ≤
      ∑ i : Fin 3, ‖∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t‖ := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    linarith
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hc
  exact ⟨i,hi⟩

theorem exists_reflection_frequency_family {m b : ℕ} (hb : b ≤ 8*m)
    (W : Finset ℝ) (hW : W.Nonempty) (A : ℝ)
    (hA : ∀ t ∈ W, A ≤ ‖∑ n ∈ Finset.Icc (m+1) b, dirichletPhase n t‖) :
    ∃ i : Fin 3, ∃ U : Finset ℝ, U.Nonempty ∧ U ⊆ W ∧
      (W.card : ℝ)/3 ≤ (U.card : ℝ) ∧
      ∀ t ∈ U, A/3 ≤ ‖∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t‖ := by
  exact exists_reflection_three_cover W hW
    (fun i t => A/3 ≤ ‖∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t‖)
    (fun t ht => exists_reflection_large_frequency_block hb t A (hA t ht))

end TaoTrudgianYang2025
