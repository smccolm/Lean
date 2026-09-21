import TaoTrudgianYang2025.AtkinsonPrefixVectors

/-!
# Maximal Atkinson prefixes with different choices at each height

The maximizing prefix is chosen separately at every height. Its Gram entry
is a genuine partial phase-difference sum, not the full-block Gram entry.
-/

noncomputable section

open Complex
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_atkinsonPhaseBlockMax_prefix (T : ℝ) (m N : ℕ) :
    ∃ j : ℕ, j ≤ N ∧ atkinsonPhaseBlockMax T m N = ‖atkinsonPhaseBlockSum T m j‖ := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (N+1)) (by simp) (fun j => ‖atkinsonPhaseBlockSum T m j‖)
  exact ⟨j,Nat.le_of_lt_succ (Finset.mem_range.mp hj),he⟩

def atkinsonMaximizingPrefix (m N : ℕ) (T : ℝ) : ℕ :=
  Classical.choose (exists_atkinsonPhaseBlockMax_prefix T m N)

theorem atkinsonMaximizingPrefix_le (m N : ℕ) (T : ℝ) :
    atkinsonMaximizingPrefix m N T ≤ N :=
  (Classical.choose_spec (exists_atkinsonPhaseBlockMax_prefix T m N)).1

theorem atkinsonMaximizingPrefix_spec (m N : ℕ) (T : ℝ) :
    atkinsonPhaseBlockMax T m N =
      ‖atkinsonPhaseBlockSum T m (atkinsonMaximizingPrefix m N T)‖ :=
  (Classical.choose_spec (exists_atkinsonPhaseBlockMax_prefix T m N)).2

theorem sum_atkinsonPhaseBlockMax_sq_le_selectedGram (m N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, atkinsonPhaseBlockMax t m N)^2 ≤
      atkinsonBlockCoefficientEnergy m N*
        ∑ t ∈ W, ∑ u ∈ W,
          ‖atkinsonPrefixGram m
            (min (atkinsonMaximizingPrefix m N t) (atkinsonMaximizingPrefix m N u)) t u‖ := by
  let j := atkinsonMaximizingPrefix m N
  have hj (t : ℝ) : j t ≤ N := atkinsonMaximizingPrefix_le m N t
  have he (t : ℝ) :
      (∑ i ∈ Finset.range N, atkinsonAlternatingCoefficient (m+i)*atkinsonMaskedPhaseVector t m (j t) i) =
        atkinsonPhaseBlockSum t m (j t) :=
    (atkinsonPhaseBlockSum_eq_masked t m (hj t)).symm
  have hg (t u : ℝ) :
      (∑ i ∈ Finset.range N, conj (atkinsonMaskedPhaseVector t m (j t) i)*
        atkinsonMaskedPhaseVector u m (j u) i) = atkinsonPrefixGram m (min (j t) (j u)) t u :=
    atkinsonMaskedPhaseVector_gram m N ((min_le_left _ _).trans (hj t)) t u
  have h := sum_norm_coefficient_vector_sq_le_gram (Finset.range N) W
    (fun i => atkinsonAlternatingCoefficient (m+i))
    (fun t i => atkinsonMaskedPhaseVector t m (j t) i)
  simp_rw [he,hg,norm_atkinsonAlternatingCoefficient] at h
  simpa only [j,← atkinsonMaximizingPrefix_spec,atkinsonBlockCoefficientEnergy] using h

def atkinsonPrefixGramMax (m N : ℕ) (t u : ℝ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (fun j => ‖atkinsonPrefixGram m j t u‖)

theorem norm_atkinsonPrefixGram_le_max (m N j : ℕ) (hj : j ≤ N) (t u : ℝ) :
    ‖atkinsonPrefixGram m j t u‖ ≤ atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  exact Finset.le_sup' (fun k => ‖atkinsonPrefixGram m k t u‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem atkinsonPrefixGramMax_nonneg (m N : ℕ) (t u : ℝ) :
    0 ≤ atkinsonPrefixGramMax m N t u := by
  have h := norm_atkinsonPrefixGram_le_max m N 0 (Nat.zero_le N) t u
  simpa [atkinsonPrefixGram] using h

theorem atkinsonPrefixGramMax_self (m N : ℕ) (t : ℝ) :
    atkinsonPrefixGramMax m N t t = (N:ℝ) := by
  apply le_antisymm
  · unfold atkinsonPrefixGramMax
    apply Finset.sup'_le
    intro j hj
    rw [norm_atkinsonPrefixGram_self]
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  · simpa only [norm_atkinsonPrefixGram_self] using
      norm_atkinsonPrefixGram_le_max m N N le_rfl t t

theorem atkinsonPrefixGramMax_swap (m N : ℕ) (t u : ℝ) :
    atkinsonPrefixGramMax m N u t = atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  simp_rw [atkinsonPrefixGram_swap m _ u t,Complex.norm_conj]

theorem sum_atkinsonPhaseBlockMax_sq_le_gramMax (m N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, atkinsonPhaseBlockMax t m N)^2 ≤
      atkinsonBlockCoefficientEnergy m N*
        ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax m N t u := by
  apply (sum_atkinsonPhaseBlockMax_sq_le_selectedGram m N W).trans
  apply mul_le_mul_of_nonneg_left _ (atkinsonBlockCoefficientEnergy_nonneg m N)
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro u _
  exact norm_atkinsonPrefixGram_le_max m N _
    ((min_le_left _ _).trans (atkinsonMaximizingPrefix_le m N t)) t u

theorem card_mul_atkinsonPhaseBlockMax_lower_sq_le_gramMax
    (m N : ℕ) (W : Finset ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hlarge : ∀ t ∈ W, V ≤ atkinsonPhaseBlockMax t m N) :
    ((W.card:ℝ)*V)^2 ≤ atkinsonBlockCoefficientEnergy m N*
      ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax m N t u := by
  have hsum : (W.card:ℝ)*V ≤ ∑ t ∈ W, atkinsonPhaseBlockMax t m N := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hlarge
  exact (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hsum 2).trans
    (sum_atkinsonPhaseBlockMax_sq_le_gramMax m N W)

end TaoTrudgianYang2025
