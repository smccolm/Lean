/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourcePeriodCoefficientAction
import Dubon2026.SourceIntegralModularSymbols

/-! The actual raw period pairing of cusp forms and integral cusp-divisor tensors.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
injective period pairing. This construction uses convergent actual cusp integrals
on the already proved divisor and homogeneous-polynomial modules. Descent,
injectivity and Hecke adjointness are proved in the later period and integral-Hecke modules.
-/

namespace Dubon2026.SourceModularSymbols
noncomputable section
open Matrix Matrix.SpecialLinearGroup MonoidAlgebra MvPolynomial OnePoint TensorProduct
open scoped MatrixGroups ModularForm

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} {w : ℕ}
variable {F : Type*} [hF : FunLike F UpperHalfPlane ℂ]

variable (R) in
/-- The period of `f(z) P(z, 1) dz` from `∞` to the cusp `α`, as an `R`-linear functional in
the binary form `P` with coefficients in `R`. -/
private def periodAtCusp [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ where
  toFun P := sourceCuspIntegral (periodIntegrand f P) ∞ α
  map_add' P Q := by
    rw [periodIntegrand_add_right]
    rcases eq_or_ne (∞ : OnePoint ℚ) α with hα | hα
    · subst α
      simp
    · obtain ⟨g, hg, hzero, hinf⟩ := exists_smul_zero_smul_infty hα
      rw [← hzero, ← hinf]
      exact sourceCuspIntegral_add hg
        (integrableOn_sourceResToImagAxis_periodIntegrand_slash f hk P hg)
        (integrableOn_sourceResToImagAxis_periodIntegrand_slash f hk Q hg)
  map_smul' c P := by
    rw [periodIntegrand_smul_right, ← algebraMap_smul ℂ, sourceCuspIntegral_smul, RingHom.id_apply,
      Algebra.smul_def]

/-- Evaluating `periodAtCusp` gives the integral from `∞` to the chosen cusp. -/
@[simp]
private theorem periodAtCusp_apply [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (α : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAtCusp R f hk α P = sourceCuspIntegral (periodIntegrand f P) ∞ α :=
  (rfl)

variable (R) in
/-- Pair a degree-zero divisor with a binary form by taking the coefficient-weighted sum of the
periods from `∞` to its cusps. -/
private def periodDivisorPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero R →ₗ[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ :=
  (Finsupp.linearCombination R (periodAtCusp R f hk)).comp (degreeZero R).subtype

variable (R) in
/-- The **raw period pairing** of a cusp form of weight `w + 2`. It is the `R`-linear
functional on `Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)` induced by integrating against binary forms. -/
def rawPairing [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2) :
    degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] ℂ :=
  TensorProduct.lift (periodDivisorPairing R f hk)

/-- On a pure tensor, the raw pairing is the coefficient-weighted sum of periods from `∞` to
the cusps in the divisor. -/
theorem rawPairing_tmul [CuspFormClass F 𝒢 k] (f : F) (hk : k = w + 2)
    (D : degreeZero R)
    (P : homogeneousSubmodule (Fin 2) R w) :
    rawPairing R f hk (D ⊗ₜ[R] P) =
      Finsupp.linearCombination R
        (fun α ↦ sourceCuspIntegral (periodIntegrand f P) ∞ α)
        D.val := by
  simp [rawPairing, periodDivisorPairing, Finsupp.linearCombination_apply, periodAtCusp_apply]
  rfl

/-- The raw pairing sends `([α] - [β]) ⊗ P` to the period from `β` to `α`. This is the
characteristic formula relating the analytic pairing to the generators of modular symbols. -/
@[simp]
theorem rawPairing_single_sub_single_tmul [CuspFormClass F 𝒢 k] (f : F)
    (hk : k = w + 2)
    (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    rawPairing R f hk
        (⟨single α (1 : R) - single β 1, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ[R] P) =
      sourceCuspIntegral (periodIntegrand f P) β α := by
  rw [rawPairing_tmul]
  change (Finsupp.linearCombination R
    (fun a ↦ sourceCuspIntegral (periodIntegrand f P) ∞ a))
    (Finsupp.single α 1 - Finsupp.single β 1) = _
  have hsub := (Finsupp.linearCombination R
    (fun a ↦ sourceCuspIntegral (periodIntegrand f P) ∞ a)).map_sub
    (Finsupp.single α 1) (Finsupp.single β 1)
  refine hsub.trans ?_
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
    one_smul, one_smul]
  have hadd := sourceCuspIntegral_periodIntegrand_add_adjacent f hk P ∞ β α
  rw [sub_eq_iff_eq_add]
  simpa only [add_comm] using hadd.symm

/-- The raw pairing is additive in the cusp form. -/
theorem rawPairing_add (f g : CuspForm 𝒢 k) (hk : k = w + 2) :
    rawPairing R (f + g) hk = rawPairing R f hk + rawPairing R g hk := by
  refine hom_ext_unimodular fun γ P ↦ ?_
  have hγ : 0 < ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  rw [LinearMap.add_apply, rawPairing_single_sub_single_tmul, rawPairing_single_sub_single_tmul,
    rawPairing_single_sub_single_tmul, CuspForm.coe_add, periodIntegrand_add_left]
  exact sourceCuspIntegral_add hγ (integrableOn_sourceResToImagAxis_periodIntegrand_slash f hk P hγ)
    (integrableOn_sourceResToImagAxis_periodIntegrand_slash g hk P hγ)

/-- The raw pairing is `ℂ`-homogeneous in the cusp form. -/
theorem rawPairing_smul [𝒢.HasDetOne] (c : ℂ) (f : CuspForm 𝒢 k) (hk : k = w + 2) :
    rawPairing R (c • f) hk = c • rawPairing R f hk := by
  refine hom_ext_unimodular fun γ P ↦ ?_
  rw [LinearMap.smul_apply, rawPairing_single_sub_single_tmul, rawPairing_single_sub_single_tmul,
    CuspForm.IsGLPos.coe_smul, periodIntegrand_smul_left, sourceCuspIntegral_smul, smul_eq_mul]

end
end Dubon2026.SourceModularSymbols
