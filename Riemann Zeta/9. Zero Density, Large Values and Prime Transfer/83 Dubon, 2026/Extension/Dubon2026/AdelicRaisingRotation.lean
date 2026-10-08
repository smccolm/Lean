import Dubon2026.RealOneParameterEigenvector
import Dubon2026.RealRotationGroup
import Dubon2026.AdelicLowestWeightJets

/-! # The exact original rotation character on every actual raising derivative -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem compact_eigen_from_Cartan {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Module.End ℂ V) (v : V) (a : ℂ) (h : ((-Complex.I) • K) v = a • v) :
    K v = (Complex.I * a) • v := by
  have he := congrArg (fun w : V => Complex.I • w) h
  simpa only [LinearMap.smul_apply, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] using he

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original rotation derivative has weight i(k+2n) on the literal nth raising vector. -/
theorem adelicRaisingJet_rotation_infinitesimal (hf : f ≠ 0) (n : ℕ) :
    adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff (adelicRaisingJet f n) =
      (Complex.I * ((k : ℂ) + 2 * n)) • adelicRaisingJet f n := by
  have hH : adelicComplexSl2Action f compactSl2H =
      (-Complex.I) • adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff := by
    simp only [compactSl2H, map_smul, adelicComplexSl2Action_compact_tangent]
  apply compact_eigen_from_Cartan
  exact (congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) => T (adelicRaisingJet f n)) hH).symm.trans
    (adelicRaisingJet_weight f hf n)

/-- Every original rotation acts on the actual nth raising derivative by its exact exponential character. -/
theorem adelicRaisingJet_rotation (hf : f ≠ 0) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
      (adelicRaisingJet f n).val =
        Complex.exp ((t : ℂ) * (Complex.I * ((k : ℂ) + 2 * n))) • (adelicRaisingJet f n).val := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realSmoothInfinitesimal_eigen_orbit (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) realRotationCurve realRotationCurve_entries_contDiff realRotationCurve_add
    realRotationCurve_zero (adelicRaisingJet f n) _ (adelicRaisingJet_rotation_infinitesimal f hf n) t

end
end Dubon2026
