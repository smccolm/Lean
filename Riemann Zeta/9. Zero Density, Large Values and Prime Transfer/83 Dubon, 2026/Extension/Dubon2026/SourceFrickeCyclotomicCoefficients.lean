import Dubon2026.SourceWeierstrassTorsionFourierExpansion

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> cyclotomic conjugation.
The actual finite Fourier coefficient model is transported by the given
cyclotomic embedding. No preservation of analytic modularity is assumed.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0). -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

lemma isPrimitiveRoot_zetaN {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaN N) N := by
  simpa [zetaN] using Complex.isPrimitiveRoot_exp N hN

/-- The actual generating root of unity viewed in its cyclotomic field. -/
def zetaK (N : ℕ) : kN N := ⟨zetaN N, zetaN_mem_kN N⟩

@[simp] lemma coe_zetaK (N : ℕ) : (zetaK N : ℂ) = zetaN N := rfl

lemma zetaN_pow_N {N : ℕ} (hN : N ≠ 0) : zetaN N ^ N = 1 :=
  (isPrimitiveRoot_zetaN hN).pow_eq_one

lemma pow_mul_eq_pow_mod_mul {M : Type*} [Monoid M] {x : M} {N : ℕ} (hx : x ^ N = 1)
    (k m : ℕ) : x ^ (k * m) = x ^ (k % N * m) := by
  rw [pow_eq_pow_mod (k * m) hx, pow_eq_pow_mod (k % N * m) hx, Nat.mod_mul_mod]

/-- The explicit monomial coefficient as an element of its actual coefficient field. -/
def wpMonCoeffK (N a₁ a₂ : ℕ) (i : WpIdx) : kN N := ⟨wpMonCoeff N a₁ a₂ i, wpMonCoeff_mem_kN N a₁ a₂ i⟩

/-- The actual finite exponent-fiber Fourier coefficient in the cyclotomic field. -/
def wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) : kN N :=
  ⟨wpQCoeff N a₁ a₂ n, wpQCoeff_mem_kN ha₁ a₂ n⟩

@[simp] lemma coe_wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) :
    (wpQCoeffK ha₁ a₂ n : ℂ) = wpQCoeff N a₁ a₂ n := rfl


end
end Dubon2026.SourceFricke
