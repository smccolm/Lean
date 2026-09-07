import GafniTao.HeathBrownAtkinsonPrefixIntegral

/-!
# Selecting a literal Atkinson prefix

The local mean-square input in Ivić's proof contains the terminal sum
`S(K,K,t)` plus the average of all shorter sums `S(x,K,t)`.  The exact
unit-cell integration formula proved previously turns this into a finite
average.  This file proves the resulting source dichotomy: either the
terminal sum has size at least `V/2`, or one of the literal integer prefixes
does.  No maximum function or sampled surrogate is introduced.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Exact terminal-or-prefix selection from the averaged Atkinson inequality
appearing in the local mean-square argument. -/
theorem heathBrownAtkinson_terminal_or_prefix
    {K : ℕ} {t V : ℝ} (hK : 0 < K) (hV : 0 < V)
    (hsource :
      V ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
        (K : ℝ)⁻¹ *
          (∫ x in (0 : ℝ)..(K : ℝ),
            ‖heathBrownAtkinsonSum x K t‖)) :
    V / 2 ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖ ∨
      ∃ j ∈ Finset.range K,
        V / 2 ≤ ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
  rw [intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixSum] at hsource
  by_cases hterminal :
      V / 2 ≤ ‖heathBrownAtkinsonSum (K : ℝ) K t‖
  · exact Or.inl hterminal
  · right
    by_contra hprefix
    push Not at hprefix
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
    have hrange : (Finset.range K).Nonempty := ⟨0, by simpa using hK⟩
    have hsum :
        (∑ j ∈ Finset.range K,
            ‖heathBrownAtkinsonSum (j : ℝ) K t‖) <
          ∑ _j ∈ Finset.range K, V / 2 := by
      exact Finset.sum_lt_sum_of_nonempty hrange fun j hj => hprefix j hj
    have hsum' :
        (∑ j ∈ Finset.range K,
            ‖heathBrownAtkinsonSum (j : ℝ) K t‖) <
          (K : ℝ) * (V / 2) := by
      simpa using hsum
    have havg :
        (K : ℝ)⁻¹ *
            (∑ j ∈ Finset.range K,
              ‖heathBrownAtkinsonSum (j : ℝ) K t‖) <
          V / 2 := by
      calc
        (K : ℝ)⁻¹ *
            (∑ j ∈ Finset.range K,
              ‖heathBrownAtkinsonSum (j : ℝ) K t‖) <
            (K : ℝ)⁻¹ * ((K : ℝ) * (V / 2)) :=
              mul_lt_mul_of_pos_left hsum' (inv_pos.mpr hKreal)
        _ = V / 2 := by field_simp
    have hterminal' :
        ‖heathBrownAtkinsonSum (K : ℝ) K t‖ < V / 2 :=
      lt_of_not_ge hterminal
    linarith


end

end GafniTao
