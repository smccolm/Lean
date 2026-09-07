import GafniTao.HeathBrownAtkinsonPrefixSelection

/-!
# Partitioning a family by the selected Atkinson prefix

For a finite family of heights, the terminal-or-prefix alternative gives a
cover by the `K + 1` literal prefix-large subfamilies.  This file proves that
cover and combines it with the prefix-uniform form of Ivić's Lemma 7.1.
The factor `K + 1` is retained explicitly.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The subfamily on which the literal `j`th Atkinson prefix is large. -/
def heathBrownAtkinsonPrefixLargeSet
    (W : Finset ℝ) (K j : ℕ) (V : ℝ) : Finset ℝ :=
  W.filter fun t =>
    V / 2 ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖

@[simp] theorem mem_heathBrownAtkinsonPrefixLargeSet
    {W : Finset ℝ} {K j : ℕ} {V t : ℝ} :
    t ∈ heathBrownAtkinsonPrefixLargeSet W K j V ↔
      t ∈ W ∧ V / 2 ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
  simp [heathBrownAtkinsonPrefixLargeSet]

/-- Every height satisfying the source averaged inequality belongs to one of
the `K + 1` literal prefix-large subfamilies.  Index `K` is the terminal sum;
indices below `K` are the averaged prefixes. -/
theorem subset_biUnion_heathBrownAtkinsonPrefixLargeSet
    {W : Finset ℝ} {K : ℕ} {V : ℝ}
    (hK : 0 < K) (hV : 0 < V)
    (hsource : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
        (K : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(K : ℝ),
            ‖heathBrownAtkinsonSum x K t‖)) :
    W ⊆ (Finset.range (K + 1)).biUnion fun j =>
      heathBrownAtkinsonPrefixLargeSet W K j V := by
  intro t ht
  obtain hterminal | ⟨j, hj, hjlarge⟩ :=
    heathBrownAtkinson_terminal_or_prefix hK hV (hsource t ht)
  · rw [Finset.mem_biUnion]
    exact ⟨K, by simp, by simp [ht, hterminal]⟩
  · rw [Finset.mem_biUnion]
    have hjlt : j < K := Finset.mem_range.mp hj
    exact ⟨j, Finset.mem_range.mpr (by omega), by simp [ht, hjlarge]⟩

/-- Cardinality cover obtained from the literal prefix partition. -/
theorem card_heathBrownAtkinson_le_sum_prefixLargeSet
    {W : Finset ℝ} {K : ℕ} {V : ℝ}
    (hK : 0 < K) (hV : 0 < V)
    (hsource : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
        (K : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(K : ℝ),
            ‖heathBrownAtkinsonSum x K t‖)) :
    W.card ≤ ∑ j ∈ Finset.range (K + 1),
      (heathBrownAtkinsonPrefixLargeSet W K j V).card := by
  exact (Finset.card_le_card
    (subset_biUnion_heathBrownAtkinsonPrefixLargeSet hK hV hsource)).trans
      Finset.card_biUnion_le

/-- Ivić's absorbed Lemma 7.1 after the exact terminal/prefix selection.
The loss from selecting among the terminal sum and the `K` averaged prefixes
is the displayed factor `K + 1`. -/
theorem heathBrownAtkinson_family_bound_of_averaged_large
    {K : ℕ} {T V : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K) (hV : 0 < V)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hsource : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
        (K : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(K : ℝ),
            ‖heathBrownAtkinsonSum x K t‖))
    (hAbsorb :
      2 * heathBrownAtkinsonEnergy K *
          heathBrownAtkinsonEquation719FirstCoefficient T K ≤
        (V / 2) ^ (2 : ℕ)) :
    (W.card : ℝ) ≤
      ((K + 1 : ℕ) : ℝ) *
        (4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
          heathBrownAtkinsonLemma71FreeMajorant T K /
            (V / 2) ^ (2 : ℕ)) := by
  have hcardNat :=
    card_heathBrownAtkinson_le_sum_prefixLargeSet hK hV hsource
  have hcardReal :
      (W.card : ℝ) ≤ ∑ j ∈ Finset.range (K + 1),
        ((heathBrownAtkinsonPrefixLargeSet W K j V).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (W.card : ℝ) ≤ ∑ j ∈ Finset.range (K + 1),
        ((heathBrownAtkinsonPrefixLargeSet W K j V).card : ℝ) := hcardReal
    _ ≤ ∑ _j ∈ Finset.range (K + 1),
        (4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
          heathBrownAtkinsonLemma71FreeMajorant T K /
            (V / 2) ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ K := by simpa using hj
      apply heathBrownAtkinson_prefix_lemma71_logarithmic
        hjle hT hK (by positivity) hblock
      · intro x hx y hy hxy
        exact hSep x (Finset.filter_subset _ _ hx)
          y (Finset.filter_subset _ _ hy) hxy
      · intro t ht
        exact hRange t (Finset.filter_subset _ _ ht)
      · intro t ht
        exact (mem_heathBrownAtkinsonPrefixLargeSet.mp ht).2
      · exact hAbsorb
    _ = ((K + 1 : ℕ) : ℝ) *
        (4 * (K : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ) *
          heathBrownAtkinsonLemma71FreeMajorant T K /
            (V / 2) ^ (2 : ℕ)) := by
      simp


end

end GafniTao
