import GafniTao.WooleyPadicSetup

/-!
# Wooley's monomial p-adic concentration statement

`WooleyMonomialPadicConcentration` is the coefficient-one, monomial
specialization of Wooley Corollary 3.2 used in Section 12 of the source.  It
is deliberately a modular theorem, uniform in the box length and in every
sufficiently deep modulus.  It is not postulated: subsequent files prove its
source chain.  This file only fixes the exact target and proves elementary
consequences of its quantifiers.
-/

namespace GafniTao

noncomputable section

/-- The coefficient-one monomial specialization of Wooley Corollary 3.2.
The depth is restricted to multiples `B = k*h`, for which the source choice
`H = ceil(B/k)` is exactly `h`. -/
def WooleyMonomialPadicConcentration : Prop :=
  ∀ (k p : ℕ), Nat.Prime p → k < p →
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
        ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ k * h → Q < p ^ h →
          (wooleyPadicCount (fordVinogradovKappa k) k Q p (k * h) : ℝ) ≤
            C * (p ^ (k * h) : ℝ) ^ delta *
              (Q : ℝ) ^ fordVinogradovKappa k

theorem WooleyMonomialPadicConcentration.specialize
    (hconc : WooleyMonomialPadicConcentration)
    {k p : ℕ} (hp : Nat.Prime p) (hkp : k < p)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ k * h → Q < p ^ h →
        (wooleyPadicCount (fordVinogradovKappa k) k Q p (k * h) : ℝ) ≤
          C * (p ^ (k * h) : ℝ) ^ delta *
            (Q : ℝ) ^ fordVinogradovKappa k :=
  hconc k p hp hkp delta hdelta

theorem exists_prime_strictly_above (k : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ k < p := by
  obtain ⟨p, hkp, hp⟩ := Nat.exists_infinite_primes (k + 1)
  exact ⟨p, hp, by omega⟩

#print axioms WooleyMonomialPadicConcentration.specialize
#print axioms exists_prime_strictly_above

end

end GafniTao
