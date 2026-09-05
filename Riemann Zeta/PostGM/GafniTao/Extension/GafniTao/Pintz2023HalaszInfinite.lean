import GafniTao.Pintz2023MellinResidue

/-!
# Pintz (2023), equation (4.19): infinite ambient Gram bound

The source extends the selected coefficient sequence by zero and then sends
the positive-integer ambient cutoff to infinity.  This file performs that
limit explicitly and replaces each finite Gram entry by the exact smoothed
zeta series from Lemma 3.4.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Infinite-ambient form of Pintz (4.19).  No supremum or unspecified
off-diagonal weight replaces the literal smoothed zeta Gram entry. -/
theorem pintz2023_halasz_gram_infinite
    {N : ℕ} (Iset : Finset ℕ) (W : Finset ℝ) (b : ℕ → ℂ)
    (eta lambda A : ℝ) (etaAt gammaAt : ℝ → ℝ)
    (hN : 0 < N) (hA : 0 ≤ A)
    (hpositive : ∀ n ∈ Iset, 0 < n)
    (hReal : ∀ t ∈ W, ∀ u ∈ W,
      0 ≤ 1 - etaAt t - etaAt u - 4 * eta)
    (hLarge : ∀ t ∈ W,
      A ≤ ‖∑ n ∈ Iset,
        b n * (n : ℂ) ^
          (-(((1 - etaAt t + 1 / lambda : ℝ) : ℂ) +
            I * ((gammaAt t : ℝ) : ℂ)))‖) :
    ((W.card : ℝ) * A) ^ 2 ≤
      (∑ n ∈ Iset,
        ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) *
      ∑ t ∈ W, ∑ u ∈ W,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖ := by
  obtain ⟨M₀, hM₀⟩ := Finset.exists_nat_subset_range Iset
  let E : ℝ := ∑ n ∈ Iset,
    ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
      (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)
  let G : ℕ → ℝ := fun M =>
    ∑ t ∈ W, ∑ u ∈ W,
      ‖pintz2023HalaszFiniteGram N (M₀ + M)
        eta (etaAt t) (etaAt u) (gammaAt t) (gammaAt u)‖
  let Ginf : ℝ := ∑ t ∈ W, ∑ u ∈ W,
    ‖pintz2023SmoothedZetaSum N
      (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
        I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖
  have hGramLimit : Tendsto G atTop (nhds Ginf) := by
    dsimp only [G, Ginf]
    apply tendsto_finsetSum
    intro t ht
    apply tendsto_finsetSum
    intro u hu
    simpa [Function.comp_def, Nat.add_comm] using
      ((tendsto_pintz2023HalaszFiniteGram
      eta (etaAt t) (etaAt u) (gammaAt t) (gammaAt u) hN
      (hReal t ht u hu)).comp (tendsto_add_atTop_nat M₀)).norm
  have hRightLimit : Tendsto (fun M => E * G M) atTop (nhds (E * Ginf)) :=
    hGramLimit.const_mul E
  have hLimitIneq : ((W.card : ℝ) * A) ^ 2 ≤ E * Ginf := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hRightLimit
    intro M
    let ambient : Finset ℕ := Finset.Icc 1 (M₀ + M)
    have hIambient : Iset ⊆ ambient := by
      intro n hn
      have hnRange := Finset.mem_range.mp (hM₀ hn)
      exact Finset.mem_Icc.mpr ⟨hpositive n hn, by omega⟩
    have hAmbientPositive : ∀ n ∈ ambient, 0 < n := by
      intro n hn
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    have hFinite := pintz2023_halasz_gram_ambient
      ambient Iset W b eta lambda A etaAt gammaAt hN hA
      hIambient hAmbientPositive hLarge
    rw [sum_norm_pintz2023HalaszDSupported_sq ambient Iset b eta lambda
      hN hIambient hAmbientPositive] at hFinite
    simpa only [E, G, pintz2023HalaszFiniteGram] using hFinite
  simpa only [E, Ginf] using hLimitIneq

#print axioms pintz2023_halasz_gram_infinite

end

end GafniTao
