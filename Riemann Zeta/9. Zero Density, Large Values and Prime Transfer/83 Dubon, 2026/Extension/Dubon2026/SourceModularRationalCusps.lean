/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.NumberTheory.ModularForms.Cusps

/-! Selected rational-cusp action lemmas for Manin's finite integral modular symbols.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
Exact chain: DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> modular Galois
association -> integral Hecke finiteness through periods -> finite integral
modular symbols. The original cusp-form period map is constructed in SourceOriginalPeriodMap.
-/

open Matrix Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups

namespace Dubon2026

/-- Any two distinct rational cusps are the images of `0` and `∞` under a rational matrix of
positive determinant. -/
theorem exists_smul_zero_smul_infty {a b : OnePoint ℚ} (h : a ≠ b) :
    ∃ g : GL (Fin 2) ℚ, 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det ∧
      g • ((0 : ℚ) : OnePoint ℚ) = a ∧ g • (∞ : OnePoint ℚ) = b := by
  obtain ⟨γ, hγ⟩ := OnePoint.exists_mem_SL2 ℤ b
  -- `γ⁻¹ a` is a finite cusp `q`, reached from `0` by the translation by `q`
  obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : OnePoint ℚ) = (mapGL ℚ γ)⁻¹ • a :=
    OnePoint.ne_infty_iff_exists.mp fun h₀ ↦ h (by rw [← hγ, ← h₀, smul_inv_smul])
  refine ⟨mapGL ℚ γ * upperRightHom q, ?_, ?_, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, ← Matrix.GeneralLinearGroup.val_det_apply (mapGL ℚ γ),
      det_mapGL]
    simp [upperRightHom_apply]
  · rw [mul_smul, ← smul_inv_smul (mapGL ℚ γ) a, ← hq]
    simp [upperRightHom_apply, smul_some_eq_ite]
  · rw [mul_smul, ← hγ]
    simp [upperRightHom_apply, smul_infty_eq_ite]

/-- `S` sends `∞` to `0` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_infty : mapGL ℚ S • (∞ : OnePoint ℚ) = (0 : ℚ) := by
  simp [OnePoint.smul_infty_eq_ite, ModularGroup.S]

/-- `S` sends `0` to `∞` under the Möbius action. -/
@[simp]
theorem mapGL_S_smul_zero : mapGL ℚ S • ((0 : ℚ) : OnePoint ℚ) = ∞ := by
  simp [OnePoint.smul_some_eq_ite, ModularGroup.S]

/-- `T` fixes `∞` under the Möbius action. -/
@[simp]
theorem mapGL_T_smul_infty : mapGL ℚ T • (∞ : OnePoint ℚ) = ∞ := by
  simp [OnePoint.smul_infty_eq_ite, ModularGroup.T]


end Dubon2026
