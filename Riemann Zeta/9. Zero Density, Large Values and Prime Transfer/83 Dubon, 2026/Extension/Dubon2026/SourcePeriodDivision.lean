import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> auxiliary point division -> Abel vector division.
Scale the proved Jacobi-inversion error by the required positive integer;
the actual integer period submodule absorbs that error. -/
namespace Dubon2026.SourceFunctionField.PeriodDivision
noncomputable section

theorem integer_multiple_mem_of_scaled_difference {ι : Type*}
    (Λ : Submodule ℤ (ι → ℂ)) (n : ℕ) (hn : n ≠ 0) (u v : ι → ℂ)
    (h : u - (n : ℂ)⁻¹ • v ∈ Λ) : n • u - v ∈ Λ := by
  have hm := Λ.smul_mem (n : ℤ) h
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  convert hm using 1
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, zsmul_eq_mul,
    smul_eq_mul, Int.cast_natCast, Pi.mul_apply, Pi.natCast_apply]
  field_simp [hnC]

end
end Dubon2026.SourceFunctionField.PeriodDivision
