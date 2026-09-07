import GafniTao.HeathBrownAtkinsonPrefixGram

/-!
# Aggregate Bombieri--Halász inequality for an Atkinson prefix

Ivić's Lemma 7.1 is applied after summing the absolute values of the
transformed divisor sums over the ordinate family.  This is the exact finite
duality inequality for that aggregate; it is stronger and more source-faithful
than selecting one large prefix for each ordinate.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Halász duality applied directly to the sum of norms of a common literal
Atkinson prefix.  The coefficient energy is enlarged only to the full dyadic
block energy; the Gram kernel remains the exact equation-(7.19) kernel. -/
theorem heathBrownAtkinson_prefix_aggregate_halasz_gram
    {K j : ℕ} {W : Finset ℝ} (hj : j ≤ K) :
    (∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ^ (2 : ℕ) ≤
      heathBrownAtkinsonEnergy K *
        ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ := by
  let d : ℕ → ℂ := heathBrownAtkinsonPrefixCoefficient K j
  let e : ℝ → ℕ → ℂ := heathBrownAtkinsonVector
  let D : ℝ → ℂ := fun t => ∑ n ∈ Finset.Ioc K (2 * K), d n * e t n
  let c : ℝ → ℂ := fun t => phaseAlign (D t)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := by
    intro t ht
    exact norm_phaseAlign_le_one (D t)
  have hsource : ∀ t, D t = heathBrownAtkinsonSum (j : ℝ) K t := by
    intro t
    dsimp only [D, d, e]
    exact (heathBrownAtkinsonSum_prefix_eq_coefficient_vector hj t).symm
  have halign : ‖∑ t ∈ W, c t * D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have heq :
        (∑ t ∈ W, c t * D t) = (((∑ t ∈ W, ‖D t‖) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro t ht
      exact phaseAlign_mul (D t)
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hexpand :
      (∑ t ∈ W, c t * D t) =
        ∑ n ∈ Finset.Ioc K (2 * K), d n * (∑ t ∈ W, c t * e t n) := by
    simp only [D, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hcs := norm_sum_mul_sq_le (Finset.Ioc K (2 * K)) d
    (fun n => ∑ t ∈ W, c t * e t n)
  rw [← hexpand] at hcs
  have hgram := sum_norm_sq_sum_le_gram
    (Finset.Ioc K (2 * K)) W c e hc
  have hcorr : ∀ t ∈ W, ∀ u ∈ W,
      (∑ n ∈ Finset.Ioc K (2 * K), conj (e t n) * e u n) =
        heathBrownAtkinsonGram K t u := by
    intro t ht u hu
    exact (heathBrownAtkinsonGram_eq_vector_gram K t u).symm
  have hgram' :
      (∑ n ∈ Finset.Ioc K (2 * K), ‖∑ t ∈ W, c t * e t n‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ := by
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          ‖∑ n ∈ Finset.Ioc K (2 * K), conj (e t n) * e u n‖ := hgram
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro u hu
        rw [hcorr t ht u hu]
  have henergyNonneg :
      0 ≤ ∑ n ∈ Finset.Ioc K (2 * K), ‖d n‖ ^ 2 := by positivity
  have hraw :
      (∑ t ∈ W, ‖D t‖) ^ (2 : ℕ) ≤
        (∑ n ∈ Finset.Ioc K (2 * K), ‖d n‖ ^ 2) *
          ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ := by
    calc
      (∑ t ∈ W, ‖D t‖) ^ (2 : ℕ) =
          ‖∑ t ∈ W, c t * D t‖ ^ (2 : ℕ) := by rw [halign]
      _ ≤ (∑ n ∈ Finset.Ioc K (2 * K), ‖d n‖ ^ 2) *
          (∑ n ∈ Finset.Ioc K (2 * K),
            ‖∑ t ∈ W, c t * e t n‖ ^ 2) := hcs
      _ ≤ (∑ n ∈ Finset.Ioc K (2 * K), ‖d n‖ ^ 2) *
          ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖ :=
        mul_le_mul_of_nonneg_left hgram' henergyNonneg
  rw [show (∑ t ∈ W, ‖D t‖) =
      ∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖ by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hsource t]] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (heathBrownAtkinsonPrefixEnergy_le K j) (by positivity))


end

end GafniTao
