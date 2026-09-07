import GafniTao.HeathBrownAtkinsonPhysicalCoefficients

/-!
# Bombieri--Halász for every Atkinson prefix

The local mean-square formula contains both the terminal sum `S(K)` and the
integral of `S(x)` for `0 ≤ x ≤ K`.  This file extends the already proved
terminal Gram argument to every literal integer prefix.  The coefficient is
zero-padded to the common block `(K,2K]`, so the same equation-(7.19) Gram
kernel applies without changing its endpoints.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The Atkinson coefficient cut off after the first `j` entries of the
dyadic block and extended by zero to `(K,2K]`. -/
def heathBrownAtkinsonPrefixCoefficient
    (K j n : ℕ) : ℂ :=
  if n ≤ K + j then heathBrownAtkinsonCoefficient n else 0

theorem norm_heathBrownAtkinsonPrefixCoefficient
    (K j n : ℕ) :
    ‖heathBrownAtkinsonPrefixCoefficient K j n‖ =
      if n ≤ K + j then (heathBrownDivisorCoefficient n : ℝ) else 0 := by
  by_cases hn : n ≤ K + j
  · simp [heathBrownAtkinsonPrefixCoefficient, hn,
      norm_heathBrownAtkinsonCoefficient]
  · simp [heathBrownAtkinsonPrefixCoefficient, hn]

/-- Exact zero-padded representation of `S(j,K,t)`. -/
theorem heathBrownAtkinsonSum_prefix_eq_coefficient_vector
    {K j : ℕ} (hj : j ≤ K) (t : ℝ) :
    heathBrownAtkinsonSum (j : ℝ) K t =
      ∑ n ∈ Finset.Ioc K (2 * K),
        heathBrownAtkinsonPrefixCoefficient K j n *
          heathBrownAtkinsonVector t n := by
  have hsubset : Finset.Ioc K (K + j) ⊆ Finset.Ioc K (2 * K) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  unfold heathBrownAtkinsonSum
  rw [Nat.floor_natCast]
  calc
    (∑ n ∈ Finset.Ioc K (K + j),
        (-1 : ℂ) ^ n * (heathBrownDivisorCoefficient n : ℂ) *
          Complex.exp ((heathBrownAtkinsonPhase t n : ℂ) * Complex.I)) =
        ∑ n ∈ Finset.Ioc K (K + j),
          heathBrownAtkinsonPrefixCoefficient K j n *
            heathBrownAtkinsonVector t n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnUpper : n ≤ K + j := (Finset.mem_Ioc.mp hn).2
      simp only [heathBrownAtkinsonPrefixCoefficient, hnUpper, if_true]
      unfold heathBrownAtkinsonCoefficient heathBrownAtkinsonVector unitaryPhase
      ring_nf
    _ = ∑ n ∈ Finset.Ioc K (2 * K),
          heathBrownAtkinsonPrefixCoefficient K j n *
            heathBrownAtkinsonVector t n := by
      rw [← Finset.sum_subset hsubset]
      intro n hnFull hnPrefix
      have hnUpper : ¬n ≤ K + j := by
        intro hn
        exact hnPrefix (Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hnFull).1, hn⟩)
      simp [heathBrownAtkinsonPrefixCoefficient, hnUpper]

/-- Zero padding can only decrease the coefficient energy. -/
theorem heathBrownAtkinsonPrefixEnergy_le
    (K j : ℕ) :
    (∑ n ∈ Finset.Ioc K (2 * K),
        ‖heathBrownAtkinsonPrefixCoefficient K j n‖ ^ (2 : ℕ)) ≤
      heathBrownAtkinsonEnergy K := by
  unfold heathBrownAtkinsonEnergy
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_heathBrownAtkinsonPrefixCoefficient]
  split_ifs
  · exact le_rfl
  · norm_num

/-- Bombieri--Halász for a common integer prefix of the Atkinson block.  The
right side deliberately retains the full-block energy and Gram sum, which
makes all subsequent equation-(7.19) estimates uniform in `j`. -/
theorem heathBrownAtkinson_prefix_halasz_gram
    {K j : ℕ} {V : ℝ} {W : Finset ℝ}
    (hj : j ≤ K) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖) :
    ((W.card : ℝ) * V) ^ (2 : ℕ) ≤
      heathBrownAtkinsonEnergy K *
        ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ := by
  have h := pintz2023_finite_halasz_gram
    (Finset.Ioc K (2 * K)) W V
    (heathBrownAtkinsonPrefixCoefficient K j)
    heathBrownAtkinsonVector hV (by
      intro t ht
      rw [← heathBrownAtkinsonSum_prefix_eq_coefficient_vector hj]
      exact hLarge t ht)
  simp_rw [← heathBrownAtkinsonGram_eq_vector_gram] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (heathBrownAtkinsonPrefixEnergy_le K j) (by positivity))


end

end GafniTao
