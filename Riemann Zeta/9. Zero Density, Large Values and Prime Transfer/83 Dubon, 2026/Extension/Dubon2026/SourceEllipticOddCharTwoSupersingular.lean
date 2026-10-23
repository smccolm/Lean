import Dubon2026.SourceEllipticOddSummingStructure

/-! Characteristic-two algebra for the actual odd quotient discriminant.
The ordinary case uses the squared-coordinate norm polynomial and its two
required coefficients. The supersingular case uses the actual unchanged
a3 coefficient. These cases are required by odd quotient ellipticity,
cyclic quotient products, inertia census and modular-curve good reduction
for DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2; characteristic two is not excluded.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native root bounds and the
already proved denominator degree replace duplicate general foundations. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve Polynomial Finset
noncomputable section
section CharTwo


variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in

theorem Δ_of_char_two (W : WeierstrassCurve F) (h2 : (2 : F) = 0) (ha₁ : W.a₁ = 0) :
    W.Δ = W.a₃ ^ 4 := by
  rw [Δ, b₂, b₄, b₆, b₈, ha₁]
  linear_combination (-216 * W.a₆ ^ 2 - 32 * W.a₄ ^ 3 - 108 * W.a₃ ^ 2 * W.a₆ - 14 * W.a₃ ^ 4
    + 144 * W.a₂ * W.a₄ * W.a₆ + 36 * W.a₂ * W.a₃ ^ 2 * W.a₄ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2
    - 32 * W.a₂ ^ 3 * W.a₆ - 8 * W.a₂ ^ 3 * W.a₃ ^ 2) * h2

theorem char_two_a₁_zero (W : WeierstrassCurve F) (h2 : (2 : F) = 0) (ha₁ : W.a₁ = 0) {n : ℕ}
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).Δ *
        (∏ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  have hcard := card_oddOrderSummingSet hQ
  have hU : ∀ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2 = W.a₃ ^ 2 := by
    intro P _
    simp only [veluU, veluGy, ha₁, zero_mul, add_zero]
    rw [show (2 : F) * P.2 = 0 by rw [h2, zero_mul], zero_add]
    ring
  have hprod : ∏ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2 = (W.a₃ ^ 2) ^ n := by
    rw [Finset.prod_congr rfl hU, Finset.prod_const, hcard]
  have hΔ := Δ_of_char_two W h2 ha₁
  have hΔ' := Δ_of_char_two (veluQuotient W (oddOrderSummingSet W Q n)) h2
    (by rw [veluQuotient_a₁, ha₁])
  rw [hprod, hΔ', veluQuotient_a₃, hΔ]
  ring


end CharTwo

theorem odd_quotient_isElliptic_supersingular {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : F) = 0) (ha₁ : W.a₁ = 0)
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  have h := char_two_a₁_zero W h2 ha₁ Q hQ
  rw [hΔ, zero_mul] at h
  exact pow_ne_zero _ W.isUnit_Δ.ne_zero h.symm

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
