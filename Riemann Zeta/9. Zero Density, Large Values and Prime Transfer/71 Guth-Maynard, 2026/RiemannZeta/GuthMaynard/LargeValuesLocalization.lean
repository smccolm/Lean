import RiemannZeta.GuthMaynard.LargeValuesMatrix

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Source-to-smooth localization for Guth--Maynard large values

Section 3 of Guth--Maynard replaces the sharp polynomial on `(N,2N]` by
three smooth polynomials.  This file records the exact finite identity behind
that reduction.  The coefficient masks, their rescaled dyadic intervals, and
the loss of a factor three in the large-value threshold are all explicit.
-/

/-- Restrict an ambient coefficient sequence to a finite set. -/
def gmRestrictedCoeffs (S : Finset ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ S then b n else 0

/-- A finite block lying in the plateau of the cutoff is represented exactly
by the corresponding smoothed polynomial. -/
theorem gmSmoothDirichletPoly_restricted_eq_sum
    (cutoff : GMSmoothCutoff) (Q : ℕ) (S : Finset ℕ) (b : ℕ → ℂ) (t : ℝ)
    (hS : S ⊆ dyadicInterval Q)
    (hcore : ∀ n ∈ S,
      ((n : ℝ) / Q) ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) :
    gmSmoothDirichletPoly cutoff Q (gmRestrictedCoeffs S b) t =
      ∑ n ∈ S, b n * (n : ℂ) ^ ((t : ℂ) * I) := by
  classical
  rw [gmSmoothDirichletPoly]
  let f : ℕ → ℂ := fun n =>
    cutoff ((n : ℝ) / Q) * gmRestrictedCoeffs S b n *
      (n : ℂ) ^ ((t : ℂ) * I)
  change (∑ n ∈ dyadicInterval Q, f n) = _
  calc
    (∑ n ∈ dyadicInterval Q, f n) = ∑ n ∈ S, f n := by
      symm
      apply Finset.sum_subset hS
      intro n hnQ hnS
      simp [f, gmRestrictedCoeffs, hnS]
    _ = ∑ n ∈ S, b n * (n : ℂ) ^ ((t : ℂ) * I) := by
      apply Finset.sum_congr rfl
      intro n hnS
      dsimp only [f]
      rw [cutoff.equals_one _ (hcore n hnS)]
      simp [gmRestrictedCoeffs, hnS]

/-- The three sharp pieces used in the source localization. -/
def gmSourceLeftPiece (N : ℕ) : Finset ℕ :=
  (dyadicInterval N).filter fun n => 5 * n ≤ 6 * N

/-- The `gmSourceMiddlePiece` definition used by the source-facing construction in `LargeValuesLocalization`. -/
def gmSourceMiddlePiece (N : ℕ) : Finset ℕ :=
  (dyadicInterval N).filter fun n => 6 * N < 5 * n ∧ 5 * n ≤ 9 * N

/-- The `gmSourceRightPiece` definition used by the source-facing construction in `LargeValuesLocalization`. -/
def gmSourceRightPiece (N : ℕ) : Finset ℕ :=
  (dyadicInterval N).filter fun n => 9 * N < 5 * n

/-- The left and right rescalings whose cutoff plateaux cover the two edge
pieces.  The harmless `+5` and `+4` make the integer rounding one-sided. -/
def gmSourceLeftScale (N : ℕ) : ℕ := (5 * N + 5) / 6

/-- The `gmSourceRightScale` definition used by the source-facing construction in `LargeValuesLocalization`. -/
def gmSourceRightScale (N : ℕ) : ℕ := (10 * N + 8) / 9

theorem gmSourcePieces_partition (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    sourceDirichletPoly N b t =
      (∑ n ∈ gmSourceLeftPiece N, b n * (n : ℂ) ^ ((t : ℂ) * I)) +
      (∑ n ∈ gmSourceMiddlePiece N, b n * (n : ℂ) ^ ((t : ℂ) * I)) +
      (∑ n ∈ gmSourceRightPiece N, b n * (n : ℂ) ^ ((t : ℂ) * I)) := by
  classical
  rw [sourceDirichletPoly]
  let f : ℕ → ℂ := fun n => b n * (n : ℂ) ^ ((t : ℂ) * I)
  change (∑ n ∈ dyadicInterval N, f n) = _
  rw [← Finset.sum_filter_add_sum_filter_not (s := dyadicInterval N)
    (p := fun n => 5 * n ≤ 6 * N) (f := f)]
  rw [add_assoc]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (dyadicInterval N).filter fun n => ¬ 5 * n ≤ 6 * N)
    (p := fun n => 5 * n ≤ 9 * N) (f := f)]
  congr 1
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr
    · ext n
      simp [gmSourceMiddlePiece]
      tauto
    · intro n hn
      rfl
  · apply Finset.sum_congr
    · ext n
      simp [gmSourceRightPiece]
      omega
    · intro n hn
      rfl

theorem gmSourceLeftPiece_mem_dyadic {N n : ℕ} (hN : 30 ≤ N)
    (hn : n ∈ gmSourceLeftPiece N) :
    n ∈ dyadicInterval (gmSourceLeftScale N) := by
  simp only [gmSourceLeftPiece, Finset.mem_filter, dyadicInterval,
    Finset.mem_Ioc] at hn ⊢
  dsimp only [gmSourceLeftScale]
  omega

theorem gmSourceMiddlePiece_mem_dyadic {N n : ℕ}
    (hn : n ∈ gmSourceMiddlePiece N) : n ∈ dyadicInterval N := by
  exact (Finset.mem_filter.mp hn).1

theorem gmSourceRightPiece_mem_dyadic {N n : ℕ} (hN : 30 ≤ N)
    (hn : n ∈ gmSourceRightPiece N) :
    n ∈ dyadicInterval (gmSourceRightScale N) := by
  simp only [gmSourceRightPiece, Finset.mem_filter, dyadicInterval,
    Finset.mem_Ioc] at hn ⊢
  dsimp only [gmSourceRightScale]
  omega

theorem gmSourceLeftPiece_mem_core {N n : ℕ} (hN : 30 ≤ N)
    (hn : n ∈ gmSourceLeftPiece N) :
    ((n : ℝ) / gmSourceLeftScale N) ∈
      Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ) := by
  have hn' := hn
  simp only [gmSourceLeftPiece, Finset.mem_filter, dyadicInterval,
    Finset.mem_Ioc] at hn'
  have hQpos : 0 < gmSourceLeftScale N := by
    dsimp only [gmSourceLeftScale]
    omega
  have hLowerNat : 6 * gmSourceLeftScale N ≤ 5 * n := by
    dsimp only [gmSourceLeftScale]
    omega
  have hUpperNat : 5 * n ≤ 9 * gmSourceLeftScale N := by
    dsimp only [gmSourceLeftScale]
    omega
  constructor
  · rw [le_div_iff₀ (by exact_mod_cast hQpos : (0 : ℝ) < gmSourceLeftScale N)]
    have hLowerReal : (6 : ℝ) * gmSourceLeftScale N ≤ 5 * n := by
      exact_mod_cast hLowerNat
    nlinarith
  · rw [div_le_iff₀ (by exact_mod_cast hQpos : (0 : ℝ) < gmSourceLeftScale N)]
    have hUpperReal : (5 : ℝ) * n ≤ 9 * gmSourceLeftScale N := by
      exact_mod_cast hUpperNat
    nlinarith

theorem gmSourceMiddlePiece_mem_core {N n : ℕ} (hN : 30 ≤ N)
    (hn : n ∈ gmSourceMiddlePiece N) :
    ((n : ℝ) / N) ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ) := by
  have hn' := hn
  simp only [gmSourceMiddlePiece, Finset.mem_filter] at hn'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · rw [le_div_iff₀ hNpos]
    have hLowerReal : (6 : ℝ) * N ≤ 5 * n := by
      exact_mod_cast (le_of_lt hn'.2.1)
    nlinarith
  · rw [div_le_iff₀ hNpos]
    have hUpperReal : (5 : ℝ) * n ≤ 9 * N := by
      exact_mod_cast hn'.2.2
    nlinarith

theorem gmSourceRightPiece_mem_core {N n : ℕ} (hN : 30 ≤ N)
    (hn : n ∈ gmSourceRightPiece N) :
    ((n : ℝ) / gmSourceRightScale N) ∈
      Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ) := by
  have hn' := hn
  simp only [gmSourceRightPiece, Finset.mem_filter, dyadicInterval,
    Finset.mem_Ioc] at hn'
  have hQpos : 0 < gmSourceRightScale N := by
    dsimp only [gmSourceRightScale]
    omega
  have hLowerNat : 6 * gmSourceRightScale N ≤ 5 * n := by
    dsimp only [gmSourceRightScale]
    omega
  have hUpperNat : 5 * n ≤ 9 * gmSourceRightScale N := by
    dsimp only [gmSourceRightScale]
    omega
  constructor
  · rw [le_div_iff₀ (by exact_mod_cast hQpos : (0 : ℝ) < gmSourceRightScale N)]
    have hLowerReal : (6 : ℝ) * gmSourceRightScale N ≤ 5 * n := by
      exact_mod_cast hLowerNat
    nlinarith
  · rw [div_le_iff₀ (by exact_mod_cast hQpos : (0 : ℝ) < gmSourceRightScale N)]
    have hUpperReal : (5 : ℝ) * n ≤ 9 * gmSourceRightScale N := by
      exact_mod_cast hUpperNat
    nlinarith

/-- Exact source-to-smooth three-piece identity from Section 3. -/
theorem sourceDirichletPoly_eq_three_gmSmooth
    (cutoff : GMSmoothCutoff) {N : ℕ} (hN : 30 ≤ N)
    (b : ℕ → ℂ) (t : ℝ) :
    sourceDirichletPoly N b t =
      gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
        (gmRestrictedCoeffs (gmSourceLeftPiece N) b) t +
      gmSmoothDirichletPoly cutoff N
        (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) t +
      gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
        (gmRestrictedCoeffs (gmSourceRightPiece N) b) t := by
  rw [gmSourcePieces_partition]
  rw [gmSmoothDirichletPoly_restricted_eq_sum cutoff (gmSourceLeftScale N)
      (gmSourceLeftPiece N) b t
      (fun _ hn => gmSourceLeftPiece_mem_dyadic hN hn)
      (fun _ hn => gmSourceLeftPiece_mem_core hN hn),
    gmSmoothDirichletPoly_restricted_eq_sum cutoff N
      (gmSourceMiddlePiece N) b t
      (fun _ hn => gmSourceMiddlePiece_mem_dyadic hn)
      (fun _ hn => gmSourceMiddlePiece_mem_core hN hn),
    gmSmoothDirichletPoly_restricted_eq_sum cutoff (gmSourceRightScale N)
      (gmSourceRightPiece N) b t
      (fun _ hn => gmSourceRightPiece_mem_dyadic hN hn)
      (fun _ hn => gmSourceRightPiece_mem_core hN hn)]

/-- A sharp large value selects one of the three smoothed Section 3 pieces,
with exactly the triangle-inequality loss `V/3`. -/
theorem exists_large_gmSmooth_of_source_large
    (cutoff : GMSmoothCutoff) {N : ℕ} (hN : 30 ≤ N)
    (b : ℕ → ℂ) (t V : ℝ) (hLarge : V ≤ ‖sourceDirichletPoly N b t‖) :
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
        (gmRestrictedCoeffs (gmSourceLeftPiece N) b) t‖ ∨
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff N
        (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) t‖ ∨
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
        (gmRestrictedCoeffs (gmSourceRightPiece N) b) t‖ := by
  rw [sourceDirichletPoly_eq_three_gmSmooth cutoff hN b t] at hLarge
  by_contra h
  push Not at h
  rcases h with ⟨hleft, hmiddle, hright⟩
  have htri := norm_add_le
    (gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
      (gmRestrictedCoeffs (gmSourceLeftPiece N) b) t +
     gmSmoothDirichletPoly cutoff N
      (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) t)
    (gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
      (gmRestrictedCoeffs (gmSourceRightPiece N) b) t)
  have htri' := (norm_add_le
    (gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
      (gmRestrictedCoeffs (gmSourceLeftPiece N) b) t)
    (gmSmoothDirichletPoly cutoff N
      (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) t))
  nlinarith

/-- The matrix-facing conclusion of the Section 3 localization.  A common
subfamily containing at least one third of the original ordinates uses one
fixed rescaling and one fixed coefficient sequence, and therefore satisfies
the proved sampling-matrix bound. -/
theorem source_large_values_localize_to_matrix
    (cutoff : GMSmoothCutoff) {N : ℕ} (hN : 30 ≤ N)
    (b : ℕ → ℂ) (W : Finset ℝ) (V : ℝ) (hV : 0 < V)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖sourceDirichletPoly N b t‖) :
    ∃ (W' : Finset ℝ) (Q : ℕ) (c : ℕ → ℂ),
      W' ⊆ W ∧ W.card ≤ 3 * W'.card ∧
      ((Q = gmSourceLeftScale N ∧
          c = gmRestrictedCoeffs (gmSourceLeftPiece N) b) ∨
        (Q = N ∧ c = gmRestrictedCoeffs (gmSourceMiddlePiece N) b) ∨
        (Q = gmSourceRightScale N ∧
          c = gmRestrictedCoeffs (gmSourceRightPiece N) b)) ∧
      (∀ n ∈ dyadicInterval Q, ‖c n‖ ≤ 1) ∧
      (∀ t ∈ W', V / 3 ≤ ‖gmSmoothDirichletPoly cutoff Q c t‖) ∧
      (W'.card : ℝ) ≤
        (Q : ℝ) * gmMatrixOperatorNorm cutoff Q W' ^ 2 / (V / 3) ^ 2 := by
  classical
  let L : Finset ℝ := W.filter fun t =>
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
      (gmRestrictedCoeffs (gmSourceLeftPiece N) b) t‖
  let M : Finset ℝ := W.filter fun t =>
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff N
      (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) t‖
  let R : Finset ℝ := W.filter fun t =>
    V / 3 ≤ ‖gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
      (gmRestrictedCoeffs (gmSourceRightPiece N) b) t‖
  have hcover : W ⊆ L ∪ M ∪ R := by
    intro t ht
    have htCases := exists_large_gmSmooth_of_source_large cutoff hN b t V
      (hLarge t ht)
    rcases htCases with htL | htM | htR
    · simp [L, ht, htL]
    · simp [M, ht, htM]
    · simp [R, ht, htR]
  have hcard : W.card ≤ L.card + M.card + R.card := by
    calc
      W.card ≤ (L ∪ M ∪ R).card := Finset.card_le_card hcover
      _ ≤ (L ∪ M).card + R.card := Finset.card_union_le (L ∪ M) R
      _ ≤ L.card + M.card + R.card := by
        have hLM := Finset.card_union_le L M
        omega
  have hlargePiece :
      W.card ≤ 3 * L.card ∨ W.card ≤ 3 * M.card ∨ W.card ≤ 3 * R.card := by
    omega
  rcases hlargePiece with hL | hM | hR
  · refine ⟨L, gmSourceLeftScale N,
      gmRestrictedCoeffs (gmSourceLeftPiece N) b, ?_, hL, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · exact Or.inl ⟨rfl, rfl⟩
    · intro n hn
      by_cases hnS : n ∈ gmSourceLeftPiece N
      · simpa [gmRestrictedCoeffs, hnS] using
          hb n (Finset.mem_filter.mp hnS).1
      · simp [gmRestrictedCoeffs, hnS]
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · exact gm_largeValues_card_le_operatorNorm cutoff (gmSourceLeftScale N) L
        (gmRestrictedCoeffs (gmSourceLeftPiece N) b) (V / 3)
        (div_pos hV (by norm_num))
        (by
          intro n hn
          by_cases hnS : n ∈ gmSourceLeftPiece N
          · simpa [gmRestrictedCoeffs, hnS] using
              hb n (Finset.mem_filter.mp hnS).1
          · simp [gmRestrictedCoeffs, hnS])
        (by intro t ht; exact (Finset.mem_filter.mp ht).2)
  · refine ⟨M, N, gmRestrictedCoeffs (gmSourceMiddlePiece N) b,
      ?_, hM, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · intro n hn
      by_cases hnS : n ∈ gmSourceMiddlePiece N
      · simpa [gmRestrictedCoeffs, hnS] using
          hb n (Finset.mem_filter.mp hnS).1
      · simp [gmRestrictedCoeffs, hnS]
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · exact gm_largeValues_card_le_operatorNorm cutoff N M
        (gmRestrictedCoeffs (gmSourceMiddlePiece N) b) (V / 3)
        (div_pos hV (by norm_num))
        (by
          intro n hn
          by_cases hnS : n ∈ gmSourceMiddlePiece N
          · simpa [gmRestrictedCoeffs, hnS] using
              hb n (Finset.mem_filter.mp hnS).1
          · simp [gmRestrictedCoeffs, hnS])
        (by intro t ht; exact (Finset.mem_filter.mp ht).2)
  · refine ⟨R, gmSourceRightScale N,
      gmRestrictedCoeffs (gmSourceRightPiece N) b, ?_, hR, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · intro n hn
      by_cases hnS : n ∈ gmSourceRightPiece N
      · simpa [gmRestrictedCoeffs, hnS] using
          hb n (Finset.mem_filter.mp hnS).1
      · simp [gmRestrictedCoeffs, hnS]
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · exact gm_largeValues_card_le_operatorNorm cutoff (gmSourceRightScale N) R
        (gmRestrictedCoeffs (gmSourceRightPiece N) b) (V / 3)
        (div_pos hV (by norm_num))
        (by
          intro n hn
          by_cases hnS : n ∈ gmSourceRightPiece N
          · simpa [gmRestrictedCoeffs, hnS] using
              hb n (Finset.mem_filter.mp hnS).1
          · simp [gmRestrictedCoeffs, hnS])
        (by intro t ht; exact (Finset.mem_filter.mp ht).2)

end RiemannZeta.GuthMaynard
