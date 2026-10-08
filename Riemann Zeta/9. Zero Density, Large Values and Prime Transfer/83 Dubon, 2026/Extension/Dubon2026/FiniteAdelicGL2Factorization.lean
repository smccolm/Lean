import Dubon2026.RationalFiniteIdeleFactorization
import Dubon2026.FiniteAdelicGL2Level

/-! # Actual positive-rational strong approximation for finite adelic GL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped MatrixGroups

/-- Every actual finite adelic invertible matrix factors through a positive-determinant rational matrix and the genuine level subgroup. -/
theorem rationalGL2_finiteAdeles_gamma0_factorization (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∃ γ : GL(2, ℚ)⁺, ∃ u : finiteAdeleGL2Gamma0 N,
      g = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ.val * u.val := by
  let f := algebraMap ℚ (FiniteAdeleRing ℤ ℚ)
  let ρ := Matrix.GeneralLinearGroup.map (n := Fin 2) f
  obtain ⟨q, hq, u, hu⟩ := finiteIdele_positive_rational_integral_unit
    (Matrix.GeneralLinearGroup.det g)
  let qU : ℚˣ := Units.mk0 q (ne_of_gt hq)
  let uA : (FiniteAdeleRing ℤ ℚ)ˣ := Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u
  let D := gl2UnitFirstDiagonal qU
  let U := gl2UnitFirstDiagonal uA
  have hdet : Matrix.GeneralLinearGroup.det g = Units.map f.toMonoidHom qU * uA := by
    apply Units.ext
    exact hu
  have hD : Matrix.GeneralLinearGroup.det (ρ D) = Units.map f.toMonoidHom qU := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f (gl2UnitFirstDiagonal qU)) = _
    rw [gl2UnitFirstDiagonal_map, gl2UnitFirstDiagonal_det]
  let r := (ρ D)⁻¹ * g * U⁻¹
  have hr : Matrix.GeneralLinearGroup.det r = 1 := by
    dsimp only [r]
    rw [map_mul, map_mul, map_inv, map_inv, hD, gl2UnitFirstDiagonal_det, hdet]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
  let s : SL(2, FiniteAdeleRing ℤ ℚ) := ⟨r.val, congrArg Units.val hr⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = r := by apply Units.ext; rfl
  obtain ⟨δ, v, hv⟩ := rationalSL2_finiteAdeles_gamma0_factorization N s
  have hr' : r = ρ (Matrix.SpecialLinearGroup.toGL δ) * Matrix.SpecialLinearGroup.toGL v.val := by
    rw [← hs, hv, map_mul, ← generalLinear_map_toGL]
  let γ : GL(2, ℚ)⁺ := ⟨D * Matrix.SpecialLinearGroup.toGL δ, by
    change 0 < (Matrix.GeneralLinearGroup.det (D * Matrix.SpecialLinearGroup.toGL δ)).val
    rw [map_mul, gl2UnitFirstDiagonal_det, Matrix.SpecialLinearGroup.coeToGL_det, mul_one]
    exact hq⟩
  let w : finiteAdeleGL2Gamma0 N :=
    ⟨Matrix.SpecialLinearGroup.toGL v.val * U,
      (finiteAdeleGL2Gamma0 N).mul_mem
        (finiteAdeleGamma0_toGL_mem N v.val v.property)
        (finiteAdele_integral_unit_diagonal_mem N u)⟩
  refine ⟨γ, w, ?_⟩
  change g = ρ (D * Matrix.SpecialLinearGroup.toGL δ) *
    (Matrix.SpecialLinearGroup.toGL v.val * U)
  calc
    g = ρ D * r * U := by dsimp only [r]; group
    _ = ρ (D * Matrix.SpecialLinearGroup.toGL δ) *
        (Matrix.SpecialLinearGroup.toGL v.val * U) := by
      rw [hr', map_mul]
      simp only [mul_assoc]

end
end Dubon2026
