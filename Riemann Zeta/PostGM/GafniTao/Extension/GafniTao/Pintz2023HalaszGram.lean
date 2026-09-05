import GafniTao.Pintz2023FullMHH

/-!
# Pintz (2023), equation (4.19): finite Halász Gram inequality

This file records the coefficient/vector form of Halász duality used after
Pintz's second dyadic subdivision.  It deliberately keeps the source vector
`e t n` arbitrary: the following modules instantiate it with the literal
exponential smoothing factor and the individual zero parameters.  Thus the
off-diagonal Gram entry is not replaced by the coefficient-one logarithmic
kernel used by the generic Montgomery--Halász--Huxley theorem.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Finite coefficient/vector Halász inequality.  This is the abstract
linear-algebra step in the first two lines of Pintz (4.19). -/
theorem pintz2023_finite_halasz_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (A : ℝ)
    (d : ι → ℂ) (e : κ → ι → ℂ)
    (hA : 0 ≤ A)
    (hLarge : ∀ t ∈ W, A ≤ ‖∑ n ∈ s, d n * e t n‖) :
    ((W.card : ℝ) * A) ^ 2 ≤
      (∑ n ∈ s, ‖d n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W,
          ‖∑ n ∈ s, conj (e t n) * e u n‖ := by
  let D : κ → ℂ := fun t => ∑ n ∈ s, d n * e t n
  let c : κ → ℂ := fun t => phaseAlign (D t)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := by
    intro t ht
    exact norm_phaseAlign_le_one (D t)
  have hsumNorm : (W.card : ℝ) * A ≤ ∑ t ∈ W, ‖D t‖ := by
    calc
      (W.card : ℝ) * A = ∑ _t ∈ W, A := by simp
      _ ≤ ∑ t ∈ W, ‖D t‖ := Finset.sum_le_sum fun t ht => hLarge t ht
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
        ∑ n ∈ s, d n * (∑ t ∈ W, c t * e t n) := by
    simp only [D, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hcs := norm_sum_mul_sq_le s d
    (fun n => ∑ t ∈ W, c t * e t n)
  rw [← hexpand] at hcs
  have hgram := sum_norm_sq_sum_le_gram s W c e hc
  have henergy : 0 ≤ ∑ n ∈ s, ‖d n‖ ^ 2 := by positivity
  have hleft : 0 ≤ (W.card : ℝ) * A := mul_nonneg (by positivity) hA
  have hsumNonneg : 0 ≤ ∑ t ∈ W, ‖D t‖ := by positivity
  calc
    ((W.card : ℝ) * A) ^ 2 ≤ (∑ t ∈ W, ‖D t‖) ^ 2 := by
      nlinarith
    _ = ‖∑ t ∈ W, c t * D t‖ ^ 2 := by rw [halign]
    _ ≤ (∑ n ∈ s, ‖d n‖ ^ 2) *
        (∑ n ∈ s, ‖∑ t ∈ W, c t * e t n‖ ^ 2) := hcs
    _ ≤ (∑ n ∈ s, ‖d n‖ ^ 2) *
        (∑ t ∈ W, ∑ u ∈ W,
          ‖∑ n ∈ s, conj (e t n) * e u n‖) :=
      mul_le_mul_of_nonneg_left hgram henergy

#print axioms pintz2023_finite_halasz_gram

end

end GafniTao
