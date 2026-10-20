import Dubon2026.FiniteBaseCMPolarizedExtension
import Dubon2026.SymmetricRealPolarization
import Dubon2026.HomogeneousSymmetricContinuity

/-! The original rank-two arithmetic representation supplies the exact
CM symmetric-power matrices and determinant multiplier. The actual
arithmetic conjugation and the proved symmetric-power duality discharge
the CM conjugate-duality identity required by DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra for the symmetric CM residual matrices. -/
local instance finiteBaseCMSymmetricUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The source kernel action is literal conjugation by the actual original real-place involution. -/
theorem finiteBaseCMKernel_conjugate (g : FiniteBaseCMKernel a F K) :
    (((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g) :
      finiteBaseArithmeticGaloisGroup a F) =
        finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹ := by
  have he : finiteBaseCMComponentSection a F (Multiplicative.ofAdd (1 : ZMod 2)) =
      finiteBaseRealConjugation a F := by
    change (if (1 : ZMod 2) = 0 then 1 else finiteBaseRealConjugation a F) = finiteBaseRealConjugation a F
    norm_num
  calc
    _ = finiteBaseCMComponentSection a F (Multiplicative.ofAdd (1 : ZMod 2)) * g.val *
        (finiteBaseCMComponentSection a F (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹ :=
      (finiteBaseCMGroupExtension a F K).inl_conjAct_comm
    _ = _ := by rw [he]

variable {L : Type*} [Field L] [TopologicalSpace L] [DiscreteTopology L]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)

/-- The original continuous rank-two representation supplies its actual CM symmetric power and determinant multiplier. -/
def finiteBaseCMSymmetricMatrices :
    FiniteBaseCMKernel a F K →ₜ* (GeneralLinearGroup (Fin (n + 1)) L × Lˣ) where
  toFun g := (homogeneousSymmetricGL n (ρ g.val), (GeneralLinearGroup.det (ρ g.val)) ^ n)
  map_one' := by simp
  map_mul' g h := by simp only [Subgroup.coe_mul, map_mul, mul_pow, Prod.mk_mul_mk]
  continuous_toFun := by
    exact (continuous_of_discreteTopology : Continuous (fun x : GeneralLinearGroup (Fin 2) L =>
      (homogeneousSymmetricGL n x, (GeneralLinearGroup.det x) ^ n))).comp
        (ρ.continuous.comp continuous_subtype_val)

omit [DiscreteTopology L] in
/-- The original odd real-place matrix supplies a symmetric invertible polarization of these exact CM matrices. -/
theorem finiteBaseCMSymmetricPolarization_symmetric (hn : (n.factorial : L) ≠ 0)
    (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1) :
    (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))).val.transpose =
      (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))).val := by
  apply symmetricRealPolarization_symmetric n hn _ _ hodd
  rw [← map_pow, pow_two, finiteBaseRealConjugation_mul_self, map_one]

/-- The constructed original CM matrices satisfy the exact source conjugate-duality equation. -/
theorem finiteBaseCMSymmetricMatrices_polarization (hn : (n.factorial : L) ≠ 0)
    (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMSymmetricMatrices a F K n ρ
        ((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2)) g) =
      (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)), 1) *
        polarizedSwitch (finiteBaseCMSymmetricMatrices a F K n ρ g) *
          (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)), 1)⁻¹ := by
  have he : ρ ((((finiteBaseCMGroupSplitting a F K).conjAct
      (Multiplicative.ofAdd (1 : ZMod 2))) g).val) =
      ρ (finiteBaseRealConjugation a F) * ρ g.val * (ρ (finiteBaseRealConjugation a F))⁻¹ := by
    rw [finiteBaseCMKernel_conjugate]
    simp only [map_mul ρ, map_inv ρ]
  apply Prod.ext
  · change homogeneousSymmetricGL n (ρ _) = _
    rw [he]
    exact symmetricRealPolarization_conjugate n hn (ρ (finiteBaseRealConjugation a F)) (ρ g.val)
  · change (GeneralLinearGroup.det (ρ _)) ^ n = 1 * (GeneralLinearGroup.det (ρ g.val)) ^ n * 1⁻¹
    rw [he, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det (ρ (finiteBaseRealConjugation a F))),
      mul_assoc, mul_inv_cancel, mul_one, one_mul, inv_one, mul_one]

end
end Dubon2026
