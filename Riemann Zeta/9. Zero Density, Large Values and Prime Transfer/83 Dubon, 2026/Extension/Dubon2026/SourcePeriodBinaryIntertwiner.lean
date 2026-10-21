import Dubon2026.SourceModularBinaryForms
import Dubon2026.SymmetricDualityIntertwining
import Mathlib.LinearAlgebra.Matrix.Dual

/-! Comparing original dual period coefficients with column binary forms.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual modular Galois
association -> the original nonzero H1 Hecke eigensystem in binary
coefficients. The original binomial duality matrix already proves the
symmetric-power duality. Conjugation by the genuine modular matrix S
converts inverse row substitution into the required column convention.
This is a coefficient adapter; the H1 Hecke correspondence remains open.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {K : Type*} [Field K]

/-- On the genuine modular group, inverse transpose is conjugation by S. -/
theorem sourceModular_inverseTranspose_conjugate (g : SL(2, ℤ)) :
    polarizedContragredient (mapGL K g) =
      mapGL K ModularGroup.S * mapGL K g * (mapGL K ModularGroup.S)⁻¹ := by
  have hg : (g⁻¹).transpose = ModularGroup.S * g * ModularGroup.S⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, adjugate_fin_two,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  calc
    polarizedContragredient (mapGL K g) = mapGL K (g⁻¹).transpose := by
      apply Units.ext
      rw [polarizedContragredient_val]
      have hinv : (mapGL K g).inv = (mapGL K g⁻¹).val :=
        congrArg Units.val (map_inv (mapGL K) g).symm
      rw [hinv]
      ext i j
      rfl
    _ = _ := by rw [hg, map_mul, map_mul, map_inv]

/-- The existing symmetric duality and the actual modular matrix S give the
invertible change from dual period coordinates to column binary coordinates. -/
def sourcePeriodBinaryIntertwiner (n : ℕ) (hn : (n.factorial : K) ≠ 0) :
    GeneralLinearGroup (Fin (n + 1)) K :=
  (homogeneousSymmetricGL n (mapGL K ModularGroup.S))⁻¹ * symmetricDualityGL n hn

/-- The coordinate change intertwines the actual column action with the dual
of inverse-row substitution, using the already proved binomial duality. -/
theorem sourcePeriodBinaryIntertwiner_intertwine
    (n : ℕ) (hn : (n.factorial : K) ≠ 0) (g : SL(2, ℤ)) :
    homogeneousSymmetricGL n (mapGL K g) * sourcePeriodBinaryIntertwiner n hn =
      sourcePeriodBinaryIntertwiner n hn *
        polarizedContragredient
          (homogeneousSymmetricGL n (polarizedContragredient (mapGL K g))) := by
  have hd : GeneralLinearGroup.det (polarizedContragredient (mapGL K g)) = 1 := by
    rw [sourceModular_inverseTranspose_conjugate]
    simp
  have h := symmetricDualityGL_intertwine n hn (polarizedContragredient (mapGL K g))
  rw [hd, one_pow] at h
  simp only [map_one, one_mul] at h
  rw [sourceModular_inverseTranspose_conjugate, map_mul, map_mul, map_inv] at h
  have h' := congrArg
    (fun x => (homogeneousSymmetricGL n (mapGL K ModularGroup.S))⁻¹ * x) h
  simpa only [sourcePeriodBinaryIntertwiner, sourceModular_inverseTranspose_conjugate,
    map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using h'

end
end Dubon2026
