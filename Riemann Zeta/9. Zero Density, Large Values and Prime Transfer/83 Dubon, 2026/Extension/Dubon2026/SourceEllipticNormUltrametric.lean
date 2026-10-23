import Dubon2026.SourceEllipticFunctionNorm

/-! The actual norm degree satisfies the ultrametric inequality. Adapted from
TauCeti InfinityPlace/Basic.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba. The native coordinate-ring norm
degree formula and a common polynomial denominator supply the inequality,
without new place or divisor infrastructure. It is the remaining valuation
inequality needed to identify the explicit odd quotient equation coefficients. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate RatFunc

namespace Dubon2026.SourceEllipticFunctionField

attribute [local instance] faithfulSMul_polynomial finiteDimensional_functionField
  finite_polynomial_coordinateRing faithful_polynomial_coordinateRing

variable {F : Type*} [Field F] (W : Affine F)

/-- The polynomial norm degree of a sum is at most the larger norm degree. -/
theorem degree_norm_add_le (a₁ b₁ a₂ b₂ : F[X]) :
    (Algebra.norm F[X] ((a₁ + a₂) • (1 : W.CoordinateRing) +
        (b₁ + b₂) • CoordinateRing.mk W Y)).degree ≤
      max (Algebra.norm F[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).degree
        (Algebra.norm F[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).degree := by
  rw [CoordinateRing.degree_norm_smul_basis, CoordinateRing.degree_norm_smul_basis,
    CoordinateRing.degree_norm_smul_basis, max_max_max_comm, max_add_add_right,
    ← smul_max_of_nonneg (Nat.zero_le 2), ← smul_max_of_nonneg (Nat.zero_le 2)]
  gcongr <;> exact degree_add_le _ _

/-- The same norm-degree bound in natural degrees, including zero numerators. -/
theorem natDegree_norm_add_le (a₁ b₁ a₂ b₂ : F[X]) :
    (Algebra.norm F[X] ((a₁ + a₂) • (1 : W.CoordinateRing) +
        (b₁ + b₂) • CoordinateRing.mk W Y)).natDegree ≤
      max (Algebra.norm F[X] (a₁ • 1 + b₁ • CoordinateRing.mk W Y)).natDegree
        (Algebra.norm F[X] (a₂ • 1 + b₂ • CoordinateRing.mk W Y)).natDegree :=
  le_max_iff.2 ((le_max_iff.1 (degree_norm_add_le W a₁ b₁ a₂ b₂)).imp
    natDegree_le_natDegree natDegree_le_natDegree)

/-- Two actual functions have coordinate-basis numerators over a common polynomial denominator. -/
theorem exists_common_polynomial_denominator (f g : W.FunctionField) :
    ∃ a₁ b₁ a₂ b₂ p : F[X], p ≠ 0 ∧
      f * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₁ • 1 + b₁ • CoordinateRing.mk W Y) ∧
      g * algebraMap F[X] W.FunctionField p =
        algebraMap W.CoordinateRing W.FunctionField (a₂ • 1 + b₂ • CoordinateRing.mk W Y) := by
  obtain ⟨u₁, u₂, ⟨_, p, hp, rfl⟩, h₁, h₂⟩ := IsLocalization.surj₂
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) W.FunctionField f g
  obtain ⟨a₁, b₁, rfl⟩ := CoordinateRing.exists_smul_basis_eq u₁
  obtain ⟨a₂, b₂, rfl⟩ := CoordinateRing.exists_smul_basis_eq u₂
  rw [← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField] at h₁ h₂
  exact ⟨a₁, b₁, a₂, b₂, p, nonZeroDivisors.ne_zero hp, h₁, h₂⟩

/-- The native field norm has ultrametric integer degree on the actual elliptic function field. -/
theorem intDegree_norm_add_le {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    (Algebra.norm (RatFunc F) (f + g)).intDegree ≤
      max (Algebra.norm (RatFunc F) f).intDegree (Algebra.norm (RatFunc F) g).intDegree := by
  obtain ⟨a₁, b₁, a₂, b₂, p, hp, h₁, h₂⟩ := exists_common_polynomial_denominator W f g
  have h₃ : (f + g) * algebraMap F[X] W.FunctionField p =
      algebraMap W.CoordinateRing W.FunctionField
        ((a₁ + a₂) • 1 + (b₁ + b₂) • CoordinateRing.mk W Y) := by
    rw [add_mul, h₁, h₂, ← map_add]
    congr 1
    simp only [add_smul]
    abel
  rw [intDegree_norm_of_mul_eq W hf hp h₁, intDegree_norm_of_mul_eq W hg hp h₂,
    intDegree_norm_of_mul_eq W hfg hp h₃]
  have h := natDegree_norm_add_le W a₁ b₁ a₂ b₂
  rw [max_sub_sub_right]
  exact sub_le_sub_right (by exact_mod_cast h) _

end Dubon2026.SourceEllipticFunctionField
