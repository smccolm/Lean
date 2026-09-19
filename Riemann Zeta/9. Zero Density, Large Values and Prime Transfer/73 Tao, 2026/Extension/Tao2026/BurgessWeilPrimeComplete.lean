import Tao2026.BurgessWeilPrimeSimpleRoot

/-!
# The unconditional complete Weil input to Burgess

The uniquely occurring numerator root is simple. Swapping the two tagged
blocks and inverting the character handles a uniquely occurring denominator
root without changing the correlation. The established prime-square and CRT
consumers then give the full cubefree complete-sum estimates.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem norm_primeLinearQuotientCorrelation_le_of_unique_left
    (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    ‖primeLinearQuotientCorrelation p r χ b‖ ≤ (4 * r : ℕ) * Real.sqrt p := by
  have hp : p.Prime := Fact.out
  have hmonic : (primeLinearOrderPolynomial p r χ b).Monic :=
    (monic_primeLinearNumeratorPolynomial p r b).mul
      ((monic_primeLinearDenominatorPolynomial p r b).pow (orderOf χ - 1))
  have hroot := rootMultiplicity_primeLinearOrderPolynomial_unique_left p r hp χ b j hunique
  have h := norm_primePolynomialCharacterCorrelation_le_of_monic_split_simple_root p χ hχ
    (primeLinearOrderPolynomial p r χ b) (primeLinearOrderPolynomial_splits p r χ b)
    hmonic (-b (Sum.inl j)) hroot
  rw [primeLinearQuotientCorrelation_eq_polynomial p r χ b hχ]
  apply h.trans
  have hcard := card_roots_primeLinearOrderPolynomial_le p r hp χ b hχ
  have hnat : (primeLinearOrderPolynomial p r χ b).roots.toFinset.card - 1 ≤ 4 * r := by omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (Real.sqrt_nonneg p)

theorem primeLinearQuotientCorrelation_swap_inv
    (p r : ℕ) [NeZero p] (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p) :
    primeLinearQuotientCorrelation p r χ⁻¹ (fun i => b i.swap) =
      primeLinearQuotientCorrelation p r χ b := by
  simp only [primeLinearQuotientCorrelation, Sum.swap_inl, Sum.swap_inr, inv_inv]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem taoPrimeLinearQuotientWeilBound_unconditional : TaoPrimeLinearQuotientWeilBound := by
  intro p r _ χ b j hp _hr hχ hunique
  letI : Fact p.Prime := ⟨hp⟩
  cases j with
  | inl j => exact norm_primeLinearQuotientCorrelation_le_of_unique_left p r χ hχ b j hunique
  | inr j =>
      have hswap : ∀ i : Fin r ⊕ Fin r, b i.swap = b (Sum.inr j) → i = Sum.inl j := by
        intro i hi
        have heq := congrArg Sum.swap (hunique i.swap hi)
        simpa only [Sum.swap_swap, Sum.swap_inr] using heq
      have h := norm_primeLinearQuotientCorrelation_le_of_unique_left p r χ⁻¹
        (inv_ne_one.mpr hχ) (fun i => b i.swap) j hswap
      rwa [primeLinearQuotientCorrelation_swap_inv] at h

theorem taoPrimeLinearQuotientWeilBoundRSeven_unconditional : TaoPrimeLinearQuotientWeilBoundRSeven := by
  intro p _ χ b j hp hχ hunique
  exact taoPrimeLinearQuotientWeilBound_unconditional p 7 χ b j hp (by decide) hχ hunique

theorem taoPrimitiveCubefreeBurgessCompleteWeilBound_unconditional :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  taoPrimeLinearQuotientWeilBound_unconditional.toComposite

theorem taoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven_unconditional :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  taoPrimeLinearQuotientWeilBoundRSeven_unconditional.toComposite

end
end Tao2026
