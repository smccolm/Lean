import GafniTao.HeathBrownAtkinsonLemma71Logarithmic
import GafniTao.HeathBrownAtkinsonPrefixIntegral

/-!
# The averaged-prefix form used after Ivić Theorem 6.2

The local mean-square theorem contains

`|S(K,K,t)| + K⁻¹ ∫₀ᴷ |S(x,K,t)| dx`.

The integral is a sum of the literal integer prefixes.  Applying the
source-shaped aggregate Lemma 7.1 separately to each prefix costs exactly
`K`; the displayed `K⁻¹` cancels this cost.  Thus this step does not make the
invalid per-ordinate prefix selection used in an earlier exploratory route.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators Interval

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Sum-integral interchange for the exact step-function Atkinson prefix. -/
theorem sum_intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixAggregate
    (W : Finset ℝ) (K : ℕ) :
    (∑ t ∈ W, ∫ x in (0 : ℝ)..(K : ℝ),
        ‖heathBrownAtkinsonSum x K t‖) =
      ∑ j ∈ Finset.range K,
        ∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
  simp_rw [intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixSum]
  rw [Finset.sum_comm]

/-- The complete integral of all prefixes is at most `K` copies of the
three-radical logarithmic majorant. -/
theorem sum_intervalIntegral_norm_heathBrownAtkinsonSum_le
    {K : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 1 ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W, ∫ x in (0 : ℝ)..(K : ℝ),
        ‖heathBrownAtkinsonSum x K t‖) ≤
      (K : ℝ) * heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
  rw [sum_intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixAggregate]
  calc
    (∑ j ∈ Finset.range K,
        ∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ≤
        ∑ _j ∈ Finset.range K,
          heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
      apply Finset.sum_le_sum
      intro j hj
      exact heathBrownAtkinson_lemma71_source_logarithmic
        hT hG hK (Nat.le_of_lt (Finset.mem_range.mp hj))
        hblock hSep hRange hDiameter
    _ = (K : ℝ) *
        heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by simp

/-- Exact aggregate estimate for the terminal-plus-averaged-prefix
expression appearing in Ivić Theorem 6.2.  The factor two is the complete
cost of retaining both terms. -/
theorem heathBrownAtkinson_lemma71_source_average
    {K : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 1 ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W,
        (‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
          (K : ℝ)⁻¹ *
            (∫ x in (0 : ℝ)..(K : ℝ),
              ‖heathBrownAtkinsonSum x K t‖))) ≤
      2 * heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
  have hterminal := heathBrownAtkinson_lemma71_source_logarithmic
    hT hG hK (le_refl K) hblock hSep hRange hDiameter
  have hintegral := sum_intervalIntegral_norm_heathBrownAtkinsonSum_le
    hT hG hK hblock hSep hRange hDiameter
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  calc
    (∑ t ∈ W,
        (‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
          (K : ℝ)⁻¹ *
            (∫ x in (0 : ℝ)..(K : ℝ),
              ‖heathBrownAtkinsonSum x K t‖))) =
        (∑ t ∈ W, ‖heathBrownAtkinsonSum (K : ℝ) K t‖) +
          (K : ℝ)⁻¹ *
            (∑ t ∈ W, ∫ x in (0 : ℝ)..(K : ℝ),
              ‖heathBrownAtkinsonSum x K t‖) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ heathBrownAtkinsonLemma71LogMajorant T G J K W.card +
          (K : ℝ)⁻¹ *
            ((K : ℝ) *
              heathBrownAtkinsonLemma71LogMajorant T G J K W.card) := by
      exact add_le_add hterminal
        (mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr hKreal.le))
    _ = 2 * heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
      field_simp [hKreal.ne']
      ring


end

end GafniTao
