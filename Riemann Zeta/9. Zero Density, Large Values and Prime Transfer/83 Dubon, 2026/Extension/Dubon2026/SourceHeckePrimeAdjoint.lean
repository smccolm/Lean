/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceIntegralHeckePrime
import Dubon2026.SourceHeckePeriodSum

/-! Adjointness of the actual original prime Hecke operator and its integral symbol action.
This supplies the prime input to `SourcePrimeHeckeGeneration`, hence finite integral
original Hecke algebra on the DUB-17/DUB-18 modular Galois association route.
-/

namespace Dubon2026.SourceModularSymbols
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane OnePoint
open MvPolynomial Representation TensorProduct MulOpposite
open scoped MatrixGroups ModularForm
noncomputable section

variable {R : Type*} [CommRing R] [Algebra R ℂ] {w Q : ℕ} [NeZero Q] {k : ℤ}

/-- A literal original triangular symbol map is adjoint to the same analytic slash translate. -/
theorem periodMap_triangularSymbolMap
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ)
    (α β : OnePoint ℚ) :
    periodMap R (Gamma0 Q) hk f
      (triangularSymbolMap R w (Gamma0 Q) a d b
        (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ P)) =
      sourceCuspIntegral (periodIntegrand (⇑f ∣[k] heckeTriangularMatrix a d b) P) β α := by
  change periodMap R (Gamma0 Q) hk f
    (Coinvariants.mk _
      (TensorProduct.map (degreeZeroGLRep R (heckeTriangularRat a d b))
        (sourceModularBinaryFormAdjugateRep R w (integralTriangularMatrix a d b))
        (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ P))) = _
  rw [TensorProduct.map_tmul, degreeZeroGLRep_single_sub_single, periodMap_mk,
    rawPairing_single_sub_single_tmul, sourceModularBinaryFormAdjugateRep_apply]
  change _ = sourceCuspIntegral
    (periodIntegrand (⇑f ∣[k] GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (heckeTriangularRat a d b)) P) β α
  rw [← sourceRat_slash, sourceCuspIntegral_periodIntegrand_slash hk f P
    (heckeTriangularRat_val a d b) (sourceHeckeTriangularRat_det_pos a d b)]

/-- The actual period map intertwines the original prime operator with the integral symbol action. -/
theorem periodMap_integralHeckePrime {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2) :
    periodMap R (Gamma0 Q) hk (cuspHeckePrime hp f) =
      periodMap R (Gamma0 Q) hk f ∘ₗ integralHeckePrime R w Q hp := by
  refine Coinvariants.hom_ext (hom_ext_unimodular fun γ P => ?_)
  have hγ : 0 < ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  simp only [LinearMap.comp_apply, periodMap_mk, rawPairing_single_sub_single_tmul,
    integralHeckePrime_mk, primeSymbolPreMap, LinearMap.add_apply, map_add,
    LinearMap.sum_apply, map_sum]
  rw [sourceCuspIntegral_prime hp f hk P hγ]
  congr 1
  · apply Finset.sum_congr rfl
    intro b _
    exact (periodMap_triangularSymbolMap f hk P 1 p b.val _ _).symm
  · split_ifs with h
    · exact (periodMap_triangularSymbolMap f hk P p 1 0 _ _).symm
    · simp

end
end Dubon2026.SourceModularSymbols
