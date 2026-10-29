import Dubon2026.SourceSiegelProductCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> exact finite Siegel product.
The literal phases and the actual Bernoulli exponent sum combine to give
the source product normalization. The source multiplier is proved to have
Nth power one, rather than supplied as a phase certificate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
noncomputable section
open Complex Filter Finset Topology
open scoped Real

/-- The finite product of the literal constant phases. -/
def phase (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, rho N r s ^ exponent N e r s

/-- The actual integer Bernoulli order sum of the finite product at infinity. -/
def orderSum (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) : ℤ :=
  ∑ r : ZMod N, ∑ s : ZMod N,
    (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)

theorem phase_pow (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) : phase N e ^ N = 1 := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [phase, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun r _ => Finset.prod_eq_one fun s _ => ?_
  rw [← pow_mul]
  have heven : Even (exponent N e r s * N) := ⟨6 * N * e r s * N, by simp [exponent]; ring⟩
  simp only [rho]
  rw [Even.neg_pow heven, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨6 * (e r s : ℤ) * (s.val : ℤ) * ((r.val : ℤ) - N), ?_⟩
  simp only [exponent]
  push_cast
  field_simp
  ring

theorem expo_pow (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ)
    (r s : ZMod N) (τ : UpperHalfPlane) :
    expo N r τ ^ exponent N e r s =
      cexp (2 * π * I * ((e r s : ℂ) *
        (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * (N : ℂ) * ((r.val : ℤ) : ℂ) + (N : ℂ) ^ 2)) *
        (τ : ℂ) / (N : ℂ)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [expo, exponent, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem exp_orderSum_eq (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) (τ : UpperHalfPlane) :
    cexp (2 * π * I * (orderSum N e : ℂ) * (τ : ℂ) / (N : ℂ)) =
      ∏ r : ZMod N, ∏ s : ZMod N, expo N r τ ^ exponent N e r s := by
  simp only [expo_pow, ← Complex.exp_sum]
  congr 1
  unfold orderSum
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]

theorem normalized_product_eq (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) (τ : UpperHalfPlane) :
    (∏ r : ZMod N, ∏ s : ZMod N,
      siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
      (phase N e * cexp (2 * π * I * (orderSum N e : ℂ) * (τ : ℂ) / (N : ℂ))) =
      ∏ r : ZMod N, ∏ s : ZMod N, normalized N r s τ ^ exponent N e r s := by
  rw [exp_orderSum_eq]
  simp only [normalized, div_pow, mul_pow, phase, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
