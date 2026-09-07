import GafniTao.HeathBrownAtkinsonGramBound

/-!
# Finite large-value consequence of the Atkinson Gram estimate

This is the cancellation-and-absorption part of Ivić's Lemma 7.1.  It is
kept separate from the analytic estimate of an off-diagonal Gram entry so
that the exact loss and the self-pair contribution remain visible.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exact coefficient energy on Heath--Brown's dyadic Atkinson block. -/
def heathBrownAtkinsonEnergy (K : Nat) : Real :=
  ∑ n ∈ Finset.Ioc K (2 * K),
    (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat)

theorem heathBrownAtkinsonEnergy_nonneg (K : Nat) :
    0 ≤ heathBrownAtkinsonEnergy K := by
  unfold heathBrownAtkinsonEnergy
  positivity

/-- If every off-diagonal Gram entry has norm at most `B`, then the complete
double Gram sum is bounded by the diagonal plus `B` for each ordered pair.
The slightly redundant diagonal `B` makes the finite identity independent of
subtraction at `W.card = 0`. -/
theorem sum_norm_heathBrownAtkinsonGram_le
    (K : Nat) (W : Finset Real) (B : Real) (hB : 0 ≤ B)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖heathBrownAtkinsonGram K t u‖ ≤ B) :
    (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
      (W.card : Real) *
        ((K : Real) + (W.card : Real) * B) := by
  have hrow : ∀ t ∈ W,
      (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        (K : Real) + (W.card : Real) * B := by
    intro t ht
    calc
      (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
          ∑ u ∈ W, ((if u = t then (K : Real) else 0) + B) := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases hut : u = t
        · subst u
          rw [norm_heathBrownAtkinsonGram_self, if_pos rfl]
          exact le_add_of_nonneg_right hB
        · rw [if_neg hut]
          simpa only [zero_add] using hoff t ht u hu (Ne.symm hut)
      _ = (K : Real) + (W.card : Real) * B := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos ht]
        simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        ∑ _t ∈ W, ((K : Real) + (W.card : Real) * B) :=
      Finset.sum_le_sum hrow
    _ = (W.card : Real) *
        ((K : Real) + (W.card : Real) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Bombieri--Halász with the self-pair separated before absorption. -/
theorem heathBrownAtkinson_largeValues_preabsorption
    {K : Nat} {V B : Real} {W : Finset Real}
    (hV : 0 < V) (hB : 0 ≤ B)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : Real) K t‖)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖heathBrownAtkinsonGram K t u‖ ≤ B) :
    (W.card : Real) * V ^ (2 : Nat) ≤
      heathBrownAtkinsonEnergy K *
        ((K : Real) + (W.card : Real) * B) := by
  by_cases hW : W = ∅
  · subst W
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    simpa only [add_zero] using
      mul_nonneg (heathBrownAtkinsonEnergy_nonneg K) (Nat.cast_nonneg K)
  · have hR : 0 < (W.card : Real) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
    have hGram := heathBrownAtkinson_halasz_gram hV.le hLarge
    have hDouble := sum_norm_heathBrownAtkinsonGram_le K W B hB hoff
    have hE := heathBrownAtkinsonEnergy_nonneg K
    unfold heathBrownAtkinsonEnergy at hGram ⊢
    have hmul := mul_le_mul_of_nonneg_left hDouble hE
    calc
      (W.card : Real) * V ^ (2 : Nat) =
          (((W.card : Real) * V) ^ (2 : Nat)) / (W.card : Real) := by
        field_simp [hR.ne']
      _ ≤ ((∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat)) *
            ∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) /
          (W.card : Real) := by
        exact div_le_div_of_nonneg_right hGram hR.le
      _ ≤ ((∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat)) *
            ((W.card : Real) *
              ((K : Real) + (W.card : Real) * B))) /
          (W.card : Real) := by
        exact div_le_div_of_nonneg_right hmul hR.le
      _ = (∑ n ∈ Finset.Ioc K (2 * K),
              (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat)) *
            ((K : Real) + (W.card : Real) * B) := by
        field_simp [hR.ne']

/-- The absorbed large-value estimate.  This is the exact finite algebra
behind the choice of the spacing parameter in the source proof. -/
theorem heathBrownAtkinson_largeValues_of_absorption
    {K : Nat} {V B : Real} {W : Finset Real}
    (hV : 0 < V) (hB : 0 ≤ B)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : Real) K t‖)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖heathBrownAtkinsonGram K t u‖ ≤ B)
    (hAbsorb : 2 * heathBrownAtkinsonEnergy K * B ≤ V ^ (2 : Nat)) :
    (W.card : Real) ≤
      2 * heathBrownAtkinsonEnergy K * (K : Real) / V ^ (2 : Nat) := by
  have hpre := heathBrownAtkinson_largeValues_preabsorption
    hV hB hLarge hoff
  have hE := heathBrownAtkinsonEnergy_nonneg K
  have hR : 0 ≤ (W.card : Real) := by positivity
  have hV2 : 0 < V ^ (2 : Nat) := by positivity
  have hcross :
      2 * ((W.card : Real) * heathBrownAtkinsonEnergy K * B) ≤
        (W.card : Real) * V ^ (2 : Nat) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hAbsorb)]
  have hRV :
      (W.card : Real) * V ^ (2 : Nat) ≤
        2 * heathBrownAtkinsonEnergy K * (K : Real) := by
    nlinarith
  exact (le_div_iff₀ hV2).2 (by
    nlinarith)


end

end GafniTao
