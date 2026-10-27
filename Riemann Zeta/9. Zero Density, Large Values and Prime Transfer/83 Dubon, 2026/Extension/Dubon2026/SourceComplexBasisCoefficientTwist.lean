import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Analysis.Complex.Basic

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient twists. On a complex basis induced from the original constant
field, apply an automorphism only to the coefficients. Native basis
coordinates and Finsupp equivalences construct the map and its inverse. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Module
variable {K V ι : Type*} [Field K] [Algebra K ℂ]
  [AddCommGroup V] [Module ℂ V] [Module K V] [IsScalarTower K ℂ V]

/-- Apply an automorphism of the complex coefficient field in the specified basis. -/
def basisCoefficientTwist (b : Basis ι ℂ V) (σ : ℂ ≃ₐ[K] ℂ) : V ≃ₗ[K] V :=
  (b.repr.restrictScalars K).trans
    ((Finsupp.mapRange.linearEquiv σ.toLinearEquiv).trans (b.repr.symm.restrictScalars K))

theorem basisCoefficientTwist_repr (b : Basis ι ℂ V) (σ : ℂ ≃ₐ[K] ℂ) (v : V) (i : ι) :
    b.repr (basisCoefficientTwist b σ v) i = σ (b.repr v i) := by
  simp [basisCoefficientTwist]

theorem basisCoefficientTwist_basis (b : Basis ι ℂ V) (σ : ℂ ≃ₐ[K] ℂ) (i : ι) :
    basisCoefficientTwist b σ (b i) = b i := by
  classical
  apply b.repr.injective
  ext j
  rw [basisCoefficientTwist_repr]
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem basisCoefficientTwist_smul (b : Basis ι ℂ V) (σ : ℂ ≃ₐ[K] ℂ) (c : ℂ) (v : V) :
    basisCoefficientTwist b σ (c • v) = σ c • basisCoefficientTwist b σ v := by
  apply b.repr.injective
  ext i
  simp only [basisCoefficientTwist_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]

end
end Dubon2026.SourceFricke