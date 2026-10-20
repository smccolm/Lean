import Dubon2026.SourceIntegralModularSymbols
import Dubon2026.HeckePrimeOrbits

/-! Integral Hecke actions on the original modular-symbol coefficient module.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power continuation
-> modular Galois association -> finite integral original Hecke algebra.
This supplies the raw integral action and transports the existing original
Gamma0 factorization proofs to coinvariants. SourceIntegralHeckePrime descends
the prime sum; SourceHeckePrimeAdjoint proves original analytic adjointness.
-/

namespace Dubon2026
namespace SourceModularSymbols

open Matrix Matrix.SpecialLinearGroup MvPolynomial Representation TensorProduct
open scoped MatrixGroups
noncomputable section

variable (R : Type*) [CommRing R] (w : ℕ)

/-- The actual rational cusp action tensored with integral adjugate substitution. -/
def integralRawAction (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Module.End R (degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :=
  TensorProduct.map (degreeZeroGLRep R g) (sourceModularBinaryFormAdjugateRep R w A)

variable {R w}

/-- Raw actions compose by multiplying the cusp and integral coefficient matrices. -/
theorem integralRawAction_mul (g h : GL (Fin 2) ℚ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    integralRawAction R w (g * h) (A * B) =
      integralRawAction R w g A ∘ₗ integralRawAction R w h B := by
  apply TensorProduct.ext
  ext D P
  simp [integralRawAction, map_mul]

/-- On the modular group the raw action is the previously constructed symbol action. -/
theorem integralRawAction_SL (γ : SL(2, ℤ)) :
    integralRawAction R w (mapGL ℚ γ) (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      symbolRep R w γ := by
  rw [integralRawAction, sourceModularBinaryFormAdjugateRep_SL]
  rfl

variable (R w) in
/-- The native quotient map with the original integral symbol space as its codomain. -/
def symbolQuotientMap (Γ : Subgroup SL(2, ℤ)) :
    degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w := by
  unfold SourceModularSymbols Coinvariants
  exact Submodule.mkQ _

/-- The original quotient map identifies every Gamma translate with its input. -/
theorem symbolQuotientMap_self (Γ : Subgroup SL(2, ℤ)) (γ : Γ)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    symbolQuotientMap R w Γ (symbolRep R w γ.val x) = symbolQuotientMap R w Γ x := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  apply (Submodule.Quotient.eq _).mpr
  apply Submodule.subset_span
  exact ⟨(γ, x), rfl⟩

/-- Integral matrix factorization gives the same transition after quotienting by Gamma. -/
theorem integralRawAction_factor (Γ : Subgroup SL(2, ℤ))
    {g h : GL (Fin 2) ℚ} {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (σ δ : SL(2, ℤ)) (hδ : δ ∈ Γ)
    (hg : g * mapGL ℚ σ = mapGL ℚ δ * h)
    (hA : A * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * B) :
    symbolQuotientMap R w Γ ∘ₗ integralRawAction R w g A ∘ₗ symbolRep R w σ =
      symbolQuotientMap R w Γ ∘ₗ integralRawAction R w h B := by
  rw [← integralRawAction_SL, ← integralRawAction_mul,
    hg, hA, integralRawAction_mul, integralRawAction_SL]
  apply LinearMap.ext
  intro x
  exact symbolQuotientMap_self Γ (⟨δ, hδ⟩ : Γ) (integralRawAction R w h B x)

/-- The exact integral triangular matrix underlying the original Hecke representative. -/
def integralTriangularMatrix (a d b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(a : ℤ), b; 0, d]

/-- The original rational triangular representative is the cast of its integral matrix. -/
theorem heckeTriangularRat_val (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) :
    (heckeTriangularRat a d b : Matrix (Fin 2) (Fin 2) ℚ) =
      (integralTriangularMatrix a d b).map (Int.cast : ℤ → ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeTriangularRat, integralTriangularMatrix, GeneralLinearGroup.mkOfDetNeZero]

/-- The original real Hecke factorization gives both its rational and integral equalities. -/
theorem integralTriangular_factor {a d a' d' : ℕ}
    [NeZero a] [NeZero d] [NeZero a'] [NeZero d'] (b b' : ℕ)
    (σ δ : SL(2, ℤ))
    (h : heckeTriangularMatrix a d b * mapGL ℝ σ =
      mapGL ℝ δ * heckeTriangularMatrix a' d' b') :
    heckeTriangularRat a d b * mapGL ℚ σ =
        mapGL ℚ δ * heckeTriangularRat a' d' b' ∧
      integralTriangularMatrix a d b * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ : Matrix (Fin 2) (Fin 2) ℤ) * integralTriangularMatrix a' d' b' := by
  have hi : integralTriangularMatrix a d b * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * integralTriangularMatrix a' d' b' := by
    ext i j
    have he := congrArg (fun g : GL (Fin 2) ℝ => g.val i j) h
    simp only [GeneralLinearGroup.coe_mul, heckeTriangularMatrix_val,
      mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two] at he
    fin_cases i <;> fin_cases j <;>
      simp [integralTriangularMatrix, Matrix.mul_apply, Fin.sum_univ_two] at he ⊢ <;>
      exact_mod_cast he
  refine ⟨?_, hi⟩
  apply Units.ext
  change (heckeTriangularRat a d b).val * (mapGL ℚ σ).val =
    (mapGL ℚ δ).val * (heckeTriangularRat a' d' b').val
  rw [heckeTriangularRat_val, heckeTriangularRat_val, mapGL_coe_matrix, mapGL_coe_matrix]
  simpa only [Matrix.map_mul] using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    M.map (Int.castRingHom ℚ)) hi

variable (R w)

/-- The original integral triangular action followed by the actual coinvariant quotient. -/
def triangularSymbolMap (Γ : Subgroup SL(2, ℤ))
    (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) :
    degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w :=
  (symbolQuotientMap R w Γ).comp
    (integralRawAction R w (heckeTriangularRat a d b) (integralTriangularMatrix a d b))

variable {R w}

/-- Existing real Gamma0 transitions act identically on the integral symbol quotient. -/
theorem triangularSymbolMap_factor (Γ : Subgroup SL(2, ℤ))
    {a d a' d' : ℕ} [NeZero a] [NeZero d] [NeZero a'] [NeZero d']
    (b b' : ℕ) (σ : SL(2, ℤ))
    (h : ∃ δ : SL(2, ℤ), δ ∈ Γ ∧
      heckeTriangularMatrix a d b * mapGL ℝ σ =
        mapGL ℝ δ * heckeTriangularMatrix a' d' b') :
    triangularSymbolMap R w Γ a d b ∘ₗ symbolRep R w σ =
      triangularSymbolMap R w Γ a' d' b' := by
  obtain ⟨δ, hδ, he⟩ := h
  obtain ⟨hq, hi⟩ := integralTriangular_factor b b' σ δ he
  unfold triangularSymbolMap
  rw [LinearMap.comp_assoc]
  exact integralRawAction_factor (R := R) (w := w) Γ σ δ hδ hq hi

end
end SourceModularSymbols
end Dubon2026
