import TaoTrudgianYang2025.ZetaReflectionSourceFamily

/-! Literal disjoint dyadic frequency blocks for the reflected common interval. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

def reflectionDyadicBlock (m b : ℕ) (i : Fin 3) : Finset ℕ :=
  Finset.Icc (2^i.val*m+1) (min b (2^(i.val+1)*m))

theorem reflectionDyadicBlock_subset_dyadic (m b : ℕ) (i : Fin 3) :
    reflectionDyadicBlock m b i ⊆ Finset.Icc (2^i.val*m) (2*(2^i.val*m)) := by
  intro n hn
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hn
  apply Finset.mem_Icc.mpr
  constructor
  · omega
  · have h := hr.trans (min_le_right b (2^(i.val+1)*m))
    rw [pow_succ] at h
    nlinarith

theorem reflectionDyadicBlock_subset_source (m b : ℕ) (i : Fin 3) :
    reflectionDyadicBlock m b i ⊆ Finset.Icc (m+1) b := by
  intro n hn
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hn
  have hp : 1 ≤ (2 : ℕ)^i.val := Nat.succ_le_of_lt (pow_pos (by norm_num) _)
  have hm := Nat.mul_le_mul_right m hp
  apply Finset.mem_Icc.mpr
  constructor
  · omega
  · exact hr.trans (min_le_left _ _)

theorem reflectionDyadicBlock_cover {m b : ℕ} (hb : b ≤ 8*m) :
    (Finset.univ.biUnion (reflectionDyadicBlock m b)) = Finset.Icc (m+1) b := by
  ext n
  constructor
  · intro hn
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hn
    exact reflectionDyadicBlock_subset_source m b i hi
  · intro hn
    obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hn
    apply Finset.mem_biUnion.mpr
    by_cases htwo : n ≤ 2*m
    · refine ⟨0,Finset.mem_univ _,?_⟩
      norm_num [reflectionDyadicBlock]
      omega
    · by_cases hfour : n ≤ 4*m
      · refine ⟨1,Finset.mem_univ _,?_⟩
        norm_num [reflectionDyadicBlock]
        omega
      · refine ⟨2,Finset.mem_univ _,?_⟩
        norm_num [reflectionDyadicBlock]
        omega

theorem reflectionDyadicBlock_pairwise_disjoint (m b : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 3))) (reflectionDyadicBlock m b) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectionDyadicBlock,Finset.mem_Icc] at hn hn' hij <;> omega

theorem sum_reflectionDyadicBlock {m b : ℕ} (hb : b ≤ 8*m) (t : ℝ) :
    (∑ n ∈ Finset.Icc (m+1) b, dirichletPhase n t) =
      ∑ i : Fin 3, ∑ n ∈ reflectionDyadicBlock m b i, dirichletPhase n t := by
  rw [← reflectionDyadicBlock_cover hb,Finset.sum_biUnion (reflectionDyadicBlock_pairwise_disjoint m b)]

end TaoTrudgianYang2025
