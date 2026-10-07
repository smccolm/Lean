/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selected port from LeanModularForms revision 7c41b9b1747d47298f76bdb51f07031087702198.
Frozen source and license are retained in Dependencies/ModularFormsSource.
-/
import Dubon2026.ModularNormOrder
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-! # Actual finite-dimensional modular and cusp spaces at arbitrary finite index -/

namespace Dubon2026.ModularDimension

open ModularForm UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

open Dubon2026.ModularDimension.NormReduction in
private lemma dim_gen_cong_levels_eq_of_coeff_eq_zero {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    [Γ.FiniteIndex] {N : ℕ}
    (hNinj : Function.Injective fun (f : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))
      (n : Fin N) ↦ (qExpansion (cuspWidth (Γ := Γ)) f).coeff n) (f g : ModularForm (G Γ) k)
    (hcoeff : ∀ m < N, (qExpansion (cuspWidth (Γ := Γ)) (⇑(f - g))).coeff m = 0) : f = g := by
  have hcoeff_norm : ∀ m < N,
      (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff m = 0 := fun m hm ↦
    Dubon2026.ModularDimension.NormReduction.qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero
      (Γ := Γ) (k := k) (f := (f - g)) (N := N) (n := m) hm hcoeff
  have hfun :
      (fun n : Fin N ↦ (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff n) =
        fun n : Fin N ↦
          (qExpansion (cuspWidth (Γ := Γ)) (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))).coeff n := by
    ext n
    simpa [qExpansion_zero (cuspWidth (Γ := Γ))] using hcoeff_norm (n : ℕ) n.isLt
  have hnorm : ModularForm.norm 𝒮ℒ (f - g) = (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ))) :=
    hNinj hfun
  have hsub : (f - g : ModularForm (G Γ) k) = 0 :=
    (coe_eq_zero_iff (f - g)).mp <|
      (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := (f - g)) (k := k)).1 (by simpa using hnorm)
  simpa [sub_eq_zero] using hsub

open Dubon2026.ModularDimension.NormReduction in
/-- Every finite-index integral modular-form space is finite dimensional via its actual norm and finite Fourier jet. -/
theorem dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  haveI : Γ.FiniteIndex := ⟨hΓ⟩
  let GΓ : Subgroup (GL (Fin 2) ℝ) := Dubon2026.ModularDimension.NormReduction.G Γ
  let h : ℝ := Dubon2026.ModularDimension.NormReduction.cuspWidth (Γ := Γ)
  have hh : 0 < h := Dubon2026.ModularDimension.NormReduction.cuspWidth_pos (Γ := Γ) hΓ
  have hperΓ : h ∈ GΓ.strictPeriods :=
    Dubon2026.ModularDimension.NormReduction.cuspWidth_mem_strictPeriods (Γ := Γ)
  have hperSL : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa [h] using
      Dubon2026.ModularDimension.NormReduction.cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
  haveI : GΓ.IsArithmetic :=
    Dubon2026.ModularDimension.NormReduction.instIsArithmetic (Γ := Γ) hΓ
  haveI : GΓ.IsFiniteRelIndex 𝒮ℒ := Subgroup.IsArithmetic.isFiniteRelIndexSL (𝒢 := GΓ)
  let w : ℤ := k * Nat.card (Dubon2026.ModularDimension.NormReduction.Q Γ)
  haveI : FiniteDimensional ℂ (ModularForm 𝒮ℒ w) := inferInstance
  obtain ⟨N, hNinj⟩ :=
    Dubon2026.ModularDimension.exists_qCoeff_injective
      (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (k := w) (h := h) hh hperSL
  let trunc : ModularForm GΓ k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun f n ↦ (qExpansion h f).coeff n
      map_add' f g := by ext n; simp [ModularForm.qExpansion_add hh hperΓ f g]
      map_smul' a f := by ext n; simp [ModularForm.qExpansion_smul hh hperΓ a f] }
  have htrunc_inj : Function.Injective trunc := by
    intro f g hfg
    refine dim_gen_cong_levels_eq_of_coeff_eq_zero hNinj f g fun m hm ↦ ?_
    have hsub : trunc (f - g) = 0 := by
      rw [trunc.map_sub, hfg, sub_self]
    have := congrArg (fun t : Fin N → ℂ ↦ t ⟨m, hm⟩) hsub
    simpa [trunc] using this
  haveI : FiniteDimensional ℂ (Fin N → ℂ) := by infer_instance
  simpa using (FiniteDimensional.of_injective trunc htrunc_inj)


/-- The actual cusp-form inclusion transfers finite dimensionality at every finite-index integral level. -/
theorem cuspForm_finiteDimensional (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Γ.map (mapGL ℝ)) k) := by
  letI := dim_gen_cong_levels k Γ (Subgroup.FiniteIndex.index_ne_zero (H := Γ))
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end
end Dubon2026.ModularDimension
