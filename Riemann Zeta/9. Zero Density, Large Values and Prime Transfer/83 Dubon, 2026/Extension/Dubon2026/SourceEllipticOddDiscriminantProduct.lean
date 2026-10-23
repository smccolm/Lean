import Dubon2026.SourceEllipticOddNormCoordinates

/-! Finite polynomial factorization for the explicit odd cyclic
quotient. Translated roots determine the cleared numerator; the three
two-torsion fibers then identify the quotient cubic and its discriminant.
This is the necessary algebraic step before actual-curve assembly in the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain through quotient products,
cyclic-subgroup roots, inertia census, reverse genus and good reduction.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native monic polynomial root
comparison is reused. The actual-curve hypotheses are not asserted here. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)
theorem delta_identity (ξ₁ ξ₂ : ι → K) (e₁ e₂ e₃ X₁ X₂ X₃ Δ Δ' : K)
    (hA₂ : (AP S x t u).eval e₂ = (hP S x).eval e₂ ^ 2 * X₂)
    (hA₃ : (AP S x t u).eval e₃ = (hP S x).eval e₃ ^ 2 * X₃)
    (hF₁₂ : (AP S x t u).eval e₂ - X₁ * (hP S x).eval e₂ ^ 2
      = (e₂ - e₁) * (∏ q ∈ S, (e₂ - ξ₁ q)) ^ 2)
    (hF₁₃ : (AP S x t u).eval e₃ - X₁ * (hP S x).eval e₃ ^ 2
      = (e₃ - e₁) * (∏ q ∈ S, (e₃ - ξ₁ q)) ^ 2)
    (hF₂₃ : (AP S x t u).eval e₃ - X₂ * (hP S x).eval e₃ ^ 2
      = (e₃ - e₂) * (∏ q ∈ S, (e₃ - ξ₂ q)) ^ 2)
    (hL₁₂ : ∀ q ∈ S, (e₂ - ξ₁ q) * (x q - e₁) = -((e₁ - e₂) * (x q - e₃)))
    (hL₁₃ : ∀ q ∈ S, (e₃ - ξ₁ q) * (x q - e₁) = -((e₁ - e₃) * (x q - e₂)))
    (hL₂₃ : ∀ q ∈ S, (e₃ - ξ₂ q) * (x q - e₂) = -((e₂ - e₃) * (x q - e₁)))
    (he₁ : ∀ q ∈ S, e₁ ≠ x q) (he₂ : ∀ q ∈ S, e₂ ≠ x q) (he₃ : ∀ q ∈ S, e₃ ≠ x q)
    (hu : ∀ q ∈ S, u q = 4 * ((x q - e₁) * (x q - e₂) * (x q - e₃)))
    (hΔ : Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2)
    (hΔ' : Δ' = 16 * ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2) :
    Δ' * (∏ q ∈ S, u q) ^ 4 = Δ ^ (2 * S.card + 1) := by
  set n := S.card with hn
  set H₁ := ∏ q ∈ S, (x q - e₁) with hH₁
  set H₂ := ∏ q ∈ S, (x q - e₂) with hH₂
  set H₃ := ∏ q ∈ S, (x q - e₃) with hH₃
  have hH₁0 : H₁ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₁ q hq).symm
  have hH₂0 : H₂ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₂ q hq).symm
  have hH₃0 : H₃ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₃ q hq).symm

  have hsq : ∀ e : K, (hP S x).eval e ^ 2 = (∏ q ∈ S, (x q - e)) ^ 2 := fun e => by
    rw [hP_eval, ← prod_pow, ← prod_pow]
    exact prod_congr rfl fun q _ => by ring

  have hG : ∀ (ξ : ι → K) (ej ek el : K),
      (∀ q ∈ S, (ek - ξ q) * (x q - ej) = -((ej - ek) * (x q - el))) →
      (∏ q ∈ S, (ek - ξ q)) * (∏ q ∈ S, (x q - ej)) = (ek - ej) ^ n * ∏ q ∈ S, (x q - el) := by
    intro ξ ej ek el hL
    rw [← prod_mul_distrib, prod_congr rfl fun q hq => (hL q hq).trans
      (show -((ej - ek) * (x q - el)) = (ek - ej) * (x q - el) by ring), prod_mul_distrib,
      prod_const, hn]
  have G₁₂ := hG ξ₁ e₁ e₂ e₃ hL₁₂
  have G₁₃ := hG ξ₁ e₁ e₃ e₂ hL₁₃
  have G₂₃ := hG ξ₂ e₂ e₃ e₁ hL₂₃
  simp only [← hH₁, ← hH₂, ← hH₃] at G₁₂ G₁₃ G₂₃
  simp only [hsq] at hA₂ hA₃ hF₁₂ hF₁₃ hF₂₃
  simp only [← hH₂, ← hH₃] at hA₂ hA₃ hF₁₂ hF₁₃ hF₂₃

  have pair : ∀ (G Hj Hk Hl Xj Xk ej ek Ae : K),
      Ae = Hk ^ 2 * Xk → Ae - Xj * Hk ^ 2 = (ek - ej) * G ^ 2 → G * Hj = (ek - ej) ^ n * Hl →
      (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 = (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by
    intro G Hj Hk Hl Xj Xk ej ek Ae hA hF hGH
    have e1 : (Xk - Xj) * Hk ^ 2 * Hj ^ 2 = (ek - ej) * (G * Hj) ^ 2 := by
      linear_combination Hj ^ 2 * (hF - hA)
    rw [hGH] at e1
    calc (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 = ((Xk - Xj) * Hk ^ 2 * Hj ^ 2) ^ 2 := by ring
      _ = ((ek - ej) * ((ek - ej) ^ n * Hl) ^ 2) ^ 2 := by rw [e1]
      _ = (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by ring
  have P₁₂ := pair _ H₁ H₂ H₃ X₁ X₂ e₁ e₂ _ hA₂ hF₁₂ G₁₂
  have P₁₃ := pair _ H₁ H₃ H₂ X₁ X₃ e₁ e₃ _ hA₃ hF₁₃ G₁₃
  have P₂₃ := pair _ H₂ H₃ H₁ X₂ X₃ e₂ e₃ _ hA₃ hF₂₃ G₂₃
  have hΔ2 : Δ = 16 * ((e₂ - e₁) * (e₃ - e₁) * (e₃ - e₂)) ^ 2 := by rw [hΔ]; ring

  have hU : ∏ q ∈ S, u q = 4 ^ n * (H₁ * H₂ * H₃) := by
    rw [prod_congr rfl hu, prod_mul_distrib, prod_const, prod_mul_distrib, prod_mul_distrib, hn]
  have h16 : (16 : K) ^ (2 * n + 1) = 16 * ((4 : K) ^ n) ^ 4 := by
    rw [pow_succ, pow_mul, ← pow_mul (4 : K) n 4, mul_comm n 4, pow_mul,
      show ((16 : K)) ^ 2 = 4 ^ 4 by norm_num]
    ring
  clear_value H₁ H₂ H₃
  generalize e₂ - e₁ = a at P₁₂ hΔ2
  generalize e₃ - e₁ = b at P₁₃ hΔ2
  generalize e₃ - e₂ = c at P₂₃ hΔ2

  have hP0 : (H₁ * H₂ * H₃) ^ 4 ≠ 0 := pow_ne_zero 4 (mul_ne_zero (mul_ne_zero hH₁0 hH₂0) hH₃0)
  have key : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4
      = a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1))
        * (H₁ * H₂ * H₃) ^ 4 := by
    have e3 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4
        = ((X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4) * ((X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4)
          * ((X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4) := by ring
    rw [e3, P₁₂, P₁₃, P₂₃]
    ring
  have key2 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4
      = a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1)) :=
    mul_right_cancel₀ hP0 key
  calc Δ' * (∏ q ∈ S, u q) ^ 4
      = 16 * (4 ^ n) ^ 4 * (((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4) := by
        rw [hΔ', hU]; ring
    _ = 16 * (4 ^ n) ^ 4 * (a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1))
        * c ^ (2 * (2 * n + 1))) := by rw [key2]
    _ = Δ ^ (2 * n + 1) := by rw [hΔ2, mul_pow, h16]; ring


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
