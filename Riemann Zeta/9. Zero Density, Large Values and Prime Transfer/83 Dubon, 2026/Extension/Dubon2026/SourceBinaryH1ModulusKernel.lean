import Dubon2026.SourceBinaryH1ModulusOperatorAlgebra
import Dubon2026.SourceBinaryH1PrimePowerKernel

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-precision Hecke realization -> compare actual permutation Hecke
relations with the finite original H1 operator image. The exact integral
H1 reduction kernel proves that zero on original coefficient reductions
is already zero on the literal tensor module. No surjectivity onto all
residual H1 classes is needed. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- Vanishing on the literal reductions of original integral H1 classes
implies zero in the actual coefficient-reduced tensor operator algebra. -/
theorem sourceBinaryH1ModulusOperatorMap_zero_of_coefficients
    (Q w N : ℕ) (hN : N ≠ 0)
    (T : sourceBinaryH1HeckeAlgebra Q w)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
      sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w (T.val x) = 0) :
    sourceBinaryH1ModulusOperatorMap Q w N T = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x =>
    change a ⊗ₜ[ℤ] (T.val x) = 0
    obtain ⟨u, hu⟩ := (sourceBinaryH1Change_zmod_nonzero_eq_zero_iff Q w N hN (T.val x)).mp (hT x)
    rw [hu]
    have hbalance := (TensorProduct.CompatibleSMul.int (R := ℤ) (M := ZMod N)
      (P := groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w))).smul_tmul
        (N : ℤ) a u
    rw [← hbalance]
    have hn : (N : ℤ) • a = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hn, TensorProduct.zero_tmul]

/-- The actual finite operator kernel is exactly its vanishing on the
original integral classes after literal coefficient reduction. -/
theorem sourceBinaryH1ModulusOperatorMap_zero_iff_coefficients
    (Q w N : ℕ) (hN : N ≠ 0) (T : sourceBinaryH1HeckeAlgebra Q w) :
    sourceBinaryH1ModulusOperatorMap Q w N T = 0 ↔
      ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
        sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w (T.val x) = 0 :=
  ⟨sourceBinaryH1ModulusOperatorMap_zero_coefficients Q w N T,
    sourceBinaryH1ModulusOperatorMap_zero_of_coefficients Q w N hN T⟩

end
end Dubon2026
