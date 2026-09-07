import RiemannZeta.GuthMaynard.ClassicalLargeValues
import RiemannZeta.GuthMaynard.TerminalTypeI

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Finite estimates for the classical Type-I interface

The finite dichotomy used by this project already returns a sharp dyadic
ordinary-zeta polynomial with coefficients independent of the ordinate, so no
ordinate-dependent smooth weight has to be removed.  The terminal estimate
puts every surviving block below the ambient height.  The short side can then
use the proved Montgomery--Halasz--Huxley theorem directly, while the medium
side is controlled by a uniform finite van der Corput B-process estimate and
Abel summation, including when the sharp cutoff ends inside the block.
-/

/-- Fixed-line ordinary-zeta coefficients have modulus at most one throughout
every positive dyadic block.  This includes the sharp upper cutoff: terms past
the cutoff vanish rather than introducing an ordinate-dependent weight. -/
theorem norm_classicalZetaLongLineCoeff_le_one
    (C N : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∀ n ∈ dyadicInterval N, ‖classicalZetaLongLineCoeff C σ n‖ ≤ 1 := by
  intro n hn
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  rw [classicalZetaLongLineCoeff]
  split_ifs
  · rw [Complex.norm_natCast_cpow_of_pos hnPos]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hnPos) (by simp [hσ])
  · simp

/-- Once a dyadic block lies below the sharp cutoff, its coefficients are
literally the fixed coefficients `n^{-σ}`.  Thus the Fourier-deweighting output
required in the paper is already present in the project's dichotomy. -/
theorem typeIFourierDeweight_native
    (C N : ℕ) (σ t : ℝ) (hNC : 2 * N ≤ C) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      dirichletPoly N (fun n => (n : ℂ) ^ (-(σ : ℂ))) t := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnC : n ≤ C := (Finset.mem_Ioc.mp hn).2.trans hNC
  rw [classicalZetaLongLineCoeff, if_pos hnC]

/-- The terminal Type-I estimate puts the retained scale below the height and
gives the exhaustive short/medium split.  The hypotheses are exactly the
pointwise Type-I witness data, not a density conclusion or a disguised
analytic assumption. -/
theorem typeISmoothScaleSplit_native
    (C N : ℕ) (σ T V : ℝ) (W : Finset ℝ)
    (hσ : 0 ≤ σ) (hN : 0 < N) (hNC : N < C)
    (hW : W.Nonempty)
    (hRange : ∀ t ∈ W, 1 ≤ t ∧ t ≤ T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖)
    (hMajorant : ∀ t ∈ W,
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) :
    (N : ℝ) ≤ T ∧
      ((N : ℝ) ^ 2 ≤ T ∨ T < (N : ℝ) ^ 2) := by
  obtain ⟨t, htW⟩ := hW
  have hNt : (N : ℝ) < t := typeI_scale_lt_height_of_large
    C N σ t V hσ hN hNC (hRange t htW).1
      (hLarge t htW) (hMajorant t htW)
  constructor
  · exact hNt.le.trans (hRange t htW).2
  · exact le_or_gt ((N : ℝ) ^ 2) T

/-- The finite van der Corput B-process uniformly controls every prefix of a
medium logarithmic block.  Unlike the full-kernel lemma, this prefix form is
strong enough for Abel summation with the weight `n^{-σ}`. -/
theorem norm_logarithmicPhase_prefix_le_sqrt
    (A L : ℕ) (t : ℝ) (hA : 0 < A) (hL : L ≤ A)
    (hAt : (A : ℝ) ≤ t) (htA : t ≤ (A : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      100 * Real.sqrt t := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have ht : 0 < t := lt_of_lt_of_le (by exact_mod_cast hA) hAt
  have hlambda : 0 < t / (9 * (A : ℝ) ^ 2) := by positivity
  have hcurvLower : ∀ n < L - 1,
      t / (9 * (A : ℝ) ^ 2) ≤
        (logarithmicPhase t (A + 1 + (n + 2)) -
          logarithmicPhase t (A + 1 + (n + 1))) -
          (logarithmicPhase t (A + 1 + (n + 1)) -
            logarithmicPhase t (A + 1 + n)) := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds A n t hA ht
      (lt_of_lt_of_le hn (Nat.sub_le_sub_right hL 1))).1
  have hcurvUpper : ∀ n < L - 1,
      (logarithmicPhase t (A + 1 + (n + 2)) -
          logarithmicPhase t (A + 1 + (n + 1))) -
          (logarithmicPhase t (A + 1 + (n + 1)) -
            logarithmicPhase t (A + 1 + n)) ≤ t / (A : ℝ) ^ 2 := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds A n t hA ht
      (lt_of_lt_of_le hn (Nat.sub_le_sub_right hL 1))).2
  have hB := vanDerCorput_B_process
    (fun n => logarithmicPhase t (A + 1 + n)) (L - 1)
    (t / (9 * (A : ℝ) ^ 2)) (t / (A : ℝ) ^ 2) hlambda
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvLower n hn)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvUpper n hn)
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred] at hB
  have hfirst :
      (((L - 1 : ℕ) : ℝ) * (t / (A : ℝ) ^ 2) / (2 * Real.pi) + 2) ≤
        (((A - 1 : ℕ) : ℝ) * (t / (A : ℝ) ^ 2) / (2 * Real.pi) + 2) := by
    gcongr
  have hsecondNonneg :
      0 ≤ 2 * Real.pi / Real.sqrt (t / (9 * (A : ℝ) ^ 2)) +
        2 * (Real.sqrt (t / (9 * (A : ℝ) ^ 2)) /
          (t / (9 * (A : ℝ) ^ 2)) + 1) := by positivity
  exact hB.trans <| (mul_le_mul_of_nonneg_right hfirst hsecondNonneg).trans
    (logarithmic_B_process_majorant_le A t hA hAt htA)

/-- Abel summation transfers the prefix B-process to the genuine
`n^{-σ-it}` amplitude throughout the medium range. -/
theorem norm_mediumWeightedBlock_le
    (σ t : ℝ) (A L : ℕ) (hσ : 0 ≤ σ) (hA : 0 < A)
    (hL : 0 < L) (hLA : L ≤ A)
    (hAt : (A : ℝ) ≤ t) (htA : t ≤ (A : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range L,
        ((A + 1 + n : ℝ) ^ (-σ) : ℝ) •
          unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      (A + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun n => (A + 1 + n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n =>
    unitaryPhase (logarithmicPhase t (A + 1 + n))
  have hBound := norm_weighted_sum_le_of_antitone f g L
    (100 * Real.sqrt t) hL
    (by intro i _; dsimp only [f]; positivity)
    (by
      intro i _
      dsimp only [f]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show A + 1 + i ≤ A + 1 + (i + 1) by omega)
      · linarith)
    (by
      intro j hj
      dsimp only [g]
      exact norm_logarithmicPhase_prefix_le_sqrt A j t hA
        (hj.trans hLA) hAt htA)
  simpa only [f, g, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using hBound

/-- The medium B-process bound for the actual sharp-cutoff Type-I block.  It
remains valid if the cutoff ends inside the dyadic interval. -/
theorem mediumTypeIBProcess_native
    (C N : ℕ) (σ t : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖ ≤
      (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) := by
  let f : ℕ → ℝ := fun i =>
    if N + 1 + i ≤ C then (N + 1 + i : ℝ) ^ (-σ) else 0
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (N + 1 + i))
  have hanti : ∀ i, i + 1 < N → f (i + 1) ≤ f i := by
    intro i hi
    dsimp only [f]
    by_cases hnext : N + 1 + (i + 1) ≤ C
    · have hcurrent : N + 1 + i ≤ C := by omega
      rw [if_pos hnext, if_pos hcurrent]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show N + 1 + i ≤ N + 1 + (i + 1) by omega)
      · linarith
    · rw [if_neg hnext]
      positivity
  have hBound := norm_weighted_sum_le_of_antitone f g N
    (100 * Real.sqrt t) hN
    (by
      intro i hi
      dsimp only [f]
      split_ifs
      · positivity
      · exact le_rfl)
    hanti
    (by
      intro j hj
      dsimp only [g]
      exact norm_logarithmicPhase_prefix_le_sqrt N j t hN hj hNt htN)
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_terminal C N σ t hN]
  have hStart : N + 1 ≤ C := by omega
  simpa only [f, g, if_pos hStart, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, add_zero, ite_smul, zero_smul] using hBound

/-- A medium Type-I witness is impossible whenever its detector threshold
dominates the explicit second-derivative majorant.  This conditional exclusion
is useful in the range where the displayed comparison holds; it does not
replace the reflected `T / N` block required in the remaining medium range. -/
theorem mediumTypeILargeValue_false
    (C N : ℕ) (σ t V : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2)
    (hThreshold :
      (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) < V) :
    ¬ V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖ := by
  intro hLarge
  have hUpper := mediumTypeIBProcess_native C N σ t hσ hN hNC hNt htN
  linarith

/-- The classical MHH cardinality estimate for every Type-I witness surviving
the terminal majorant.  Endpoint assembly must still check whether this bound
has the required exponent at the selected scale. -/
theorem typeIClassicalLargeValues_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧
        ∀ (C N : ℕ) (σ T V : ℝ) (W : Finset ℝ),
          0 ≤ σ → 0 < N → N < C → 1 ≤ T → 0 < V →
          W.Nonempty → IsSeparated 1 W → InBaseInterval T W →
          (∀ t ∈ W, 1 ≤ t) →
          (∀ t ∈ W,
            V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
          (∀ t ∈ W,
            (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) →
          (W.card : ℝ) ≤
            K * T ^ ε *
              ((N : ℝ) ^ 2 / V ^ 2 +
                T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  intro ε hε
  obtain ⟨K, hK, hMHH⟩ := classical_montgomery_halasz_huxley_native ε hε
  refine ⟨K, hK, ?_⟩
  intro C N σ T V W hσ hN hNC hT hV hW hSep hBase hOne hLarge hMajorant
  have hRange : ∀ t ∈ W, 1 ≤ t ∧ t ≤ T := by
    intro t ht
    exact ⟨hOne t ht, (hBase t ht).2⟩
  have hScale := typeISmoothScaleSplit_native C N σ T V W
    hσ hN hNC hW hRange hLarge hMajorant
  exact hMHH N T V W (classicalZetaLongLineCoeff C σ)
    hN hT hScale.1 hV
      (norm_classicalZetaLongLineCoeff_le_one C N σ hσ)
      hSep hBase hLarge

end RiemannZeta.GuthMaynard
