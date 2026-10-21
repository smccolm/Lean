import Dubon2026.SourceJPolynomialDescent
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex


/-! DUB-17/18 -> original differential realization -> finite function-field
extension -> monic relations. Identify each literal formal prime conjugate with
the actual analytic translate, using the already proved native Hecke matrices.
This retains the full upper-half-plane convergence and coefficient embeddings.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean, chosen analytic cyclotomic embedding.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

section Sigma

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

/-- The actual analytic primitive root used by the q-parameter translates. -/
def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

/-- The cyclotomic embedding taking the chosen algebraic root to the analytic root. -/
def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

variable (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

lemma sigma_zeta : sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ := ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit hℓ in
lemma sigma_ratCast' (σ : CyclotomicField ℓ ℚ →+* ℂ) (q : ℚ) : σ (q : CyclotomicField ℓ ℚ) = (q : ℂ) :=
  map_ratCast σ q

end Sigma

end
end Dubon2026.SourceFunctionField
