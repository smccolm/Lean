import GafniTao.Pintz2023HalaszKernelBounds

/-!
# Pintz (2023), equation (4.19): zero extension to an ambient sum

Pintz applies Cauchy--Schwarz after extending `d_n` by zero away from the
selected interval.  The zero extension is what permits the Gram factor to
be summed over a much larger range, and ultimately over all positive
integers.  These exact finite identities prevent that step from being
silently replaced by a restricted interval Gram sum.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

noncomputable def pintz2023HalaszDSupported
    (Iset : Finset ℕ) (b : ℕ → ℂ) (N : ℕ)
    (eta lambda : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Iset then pintz2023HalaszD b N eta lambda n else 0

theorem pintz2023HalaszDSupported_mul_E
    {N n : ℕ} (Iset : Finset ℕ) (b : ℕ → ℂ)
    (eta etaJ gamma lambda : ℝ) (hN : 0 < N) (hn : 0 < n) :
    pintz2023HalaszDSupported Iset b N eta lambda n *
        pintz2023HalaszE N eta etaJ gamma n =
      if n ∈ Iset then
        b n * (n : ℂ) ^
          (-(((1 - etaJ + 1 / lambda : ℝ) : ℂ) + I * (gamma : ℂ)))
      else 0 := by
  by_cases hmem : n ∈ Iset
  · simp only [pintz2023HalaszDSupported, hmem, if_true]
    exact pintz2023HalaszD_mul_E b eta etaJ gamma lambda hN hn
  · simp [pintz2023HalaszDSupported, hmem]

/-- The source polynomial is unchanged when `d_n` is extended by zero to
any finite positive ambient set containing the selected interval. -/
theorem sum_pintz2023HalaszDSupported_mul_E
    {N : ℕ} (ambient Iset : Finset ℕ) (b : ℕ → ℂ)
    (eta etaJ gamma lambda : ℝ) (hN : 0 < N)
    (hI : Iset ⊆ ambient) (hpositive : ∀ n ∈ ambient, 0 < n) :
    (∑ n ∈ ambient,
        pintz2023HalaszDSupported Iset b N eta lambda n *
          pintz2023HalaszE N eta etaJ gamma n) =
      ∑ n ∈ Iset,
        b n * (n : ℂ) ^
          (-(((1 - etaJ + 1 / lambda : ℝ) : ℂ) + I * (gamma : ℂ))) := by
  rw [← Finset.sum_subset hI]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [pintz2023HalaszDSupported_mul_E Iset b eta etaJ gamma lambda
      hN (hpositive n (hI hn)), if_pos hn]
  · intro n hnAmbient hnI
    rw [pintz2023HalaszDSupported_mul_E Iset b eta etaJ gamma lambda
      hN (hpositive n hnAmbient), if_neg hnI]

/-- Exact finite ambient Gram identity. -/
theorem sum_conj_pintz2023HalaszE_mul
    {N : ℕ} (ambient : Finset ℕ)
    (eta etaJ etaK gamma delta : ℝ) (hN : 0 < N)
    (hpositive : ∀ n ∈ ambient, 0 < n) :
    (∑ n ∈ ambient,
        conj (pintz2023HalaszE N eta etaJ gamma n) *
          pintz2023HalaszE N eta etaK delta n) =
      ∑ n ∈ ambient,
        ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
          (n : ℂ) ^
            (-(((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * ((delta - gamma : ℝ) : ℂ))) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact conj_pintz2023HalaszE_mul eta etaJ etaK gamma delta
    hN (hpositive n hn)

/-- The finite form of Pintz (4.19), retaining the ambient cutoff and the
literal diagonal/off-diagonal Gram entries. -/
theorem pintz2023_halasz_gram_ambient
    {N : ℕ} (ambient Iset : Finset ℕ) (W : Finset ℝ)
    (b : ℕ → ℂ) (eta lambda A : ℝ)
    (etaAt gammaAt : ℝ → ℝ)
    (hN : 0 < N) (hA : 0 ≤ A)
    (hI : Iset ⊆ ambient) (hpositive : ∀ n ∈ ambient, 0 < n)
    (hLarge : ∀ t ∈ W,
      A ≤ ‖∑ n ∈ Iset,
        b n * (n : ℂ) ^
          (-(((1 - etaAt t + 1 / lambda : ℝ) : ℂ) +
            I * ((gammaAt t : ℝ) : ℂ)))‖) :
    ((W.card : ℝ) * A) ^ 2 ≤
      (∑ n ∈ ambient,
        ‖pintz2023HalaszDSupported Iset b N eta lambda n‖ ^ 2) *
      ∑ t ∈ W, ∑ u ∈ W,
        ‖∑ n ∈ ambient,
          ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
            (n : ℂ) ^
              (-(((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
                I * (((gammaAt u) - gammaAt t : ℝ) : ℂ)))‖ := by
  have hLarge' : ∀ t ∈ W,
      A ≤ ‖∑ n ∈ ambient,
        pintz2023HalaszDSupported Iset b N eta lambda n *
          pintz2023HalaszE N eta (etaAt t) (gammaAt t) n‖ := by
    intro t ht
    rw [sum_pintz2023HalaszDSupported_mul_E ambient Iset b eta
      (etaAt t) (gammaAt t) lambda hN hI hpositive]
    exact hLarge t ht
  have hGram := pintz2023_finite_halasz_gram ambient W A
    (pintz2023HalaszDSupported Iset b N eta lambda)
    (fun t => pintz2023HalaszE N eta (etaAt t) (gammaAt t)) hA hLarge'
  convert hGram using 1
  apply congrArg (fun z : ℝ =>
    (∑ n ∈ ambient,
      ‖pintz2023HalaszDSupported Iset b N eta lambda n‖ ^ 2) * z)
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  exact (sum_conj_pintz2023HalaszE_mul ambient eta (etaAt t) (etaAt u)
    (gammaAt t) (gammaAt u) hN hpositive).symm

#print axioms sum_pintz2023HalaszDSupported_mul_E
#print axioms sum_conj_pintz2023HalaszE_mul
#print axioms pintz2023_halasz_gram_ambient

end

end GafniTao
