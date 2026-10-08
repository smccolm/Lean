import Dubon2026.RealSmoothUnitaryInfinitesimal
import Dubon2026.SkewLadderInnerProducts
import Dubon2026.AdelicInfinitesimalCharacter

/-! # Genuine Hilbert adjoint identities for the original matrix infinitesimals -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The smooth domain carries precisely the inner product induced by its original Hilbert inclusion. -/
instance adelicRealSmoothInnerProductSpace : InnerProductSpace ℂ (adelicRealSmoothSubmodule f) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRealSmoothSubmodule f)

/-- Every original real smooth-curve infinitesimal is skew symmetric in the actual inherited Hilbert inner product. -/
theorem adelicSmoothInfinitesimal_skew (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (hc0 : c 0 = 1)
    (v w : adelicRealSmoothSubmodule f) :
    inner ℂ (adelicSmoothInfinitesimal f c hc v) w +
      inner ℂ v (adelicSmoothInfinitesimal f c hc w) = 0 := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal_skew (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl)
    (fun g v w => adelicCyclicHilbertRepresentation_inner f (adelicRealSL2Embedding g) v w)
    c hc hc0 v w

/-- The actual compact Cartan is symmetric for the genuine smooth-domain Hilbert inner product. -/
theorem adelicCompactSl2H_symmetric :
    @LinearMap.IsSymmetric ℂ (adelicRealSmoothSubmodule f) inferInstance inferInstance inferInstance
      (adelicComplexSl2Action f compactSl2H) :=
  @compactSl2Action_Cartan_symmetric (adelicRealSmoothSubmodule f) inferInstance inferInstance
    (adelicComplexSl2Action f).toLinearMap
    (adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff)
    (adelicComplexSl2Action_compact_tangent f)
    (adelicSmoothInfinitesimal_skew f realRotationCurve realRotationCurve_entries_contDiff
      realRotationCurve_zero)

/-- The actual raising and lowering matrices are negative adjoints on the original genuine smooth Hilbert domain. -/
theorem adelicCompactSl2E_F_inner (v w : adelicRealSmoothSubmodule f) :
    inner ℂ (adelicComplexSl2Action f compactSl2E v) w =
      -inner ℂ v (adelicComplexSl2Action f compactSl2F w) :=
  @compactSl2Action_raising_lowering_inner (adelicRealSmoothSubmodule f) inferInstance inferInstance
    (adelicComplexSl2Action f).toLinearMap
    (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff)
    (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff)
    (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff)
    (adelicComplexSl2Action_A f) (adelicComplexSl2Action_U f) (adelicComplexSl2Action_F f)
    (adelicSmoothInfinitesimal_skew f realGeodesicCurve realGeodesicCurve_entries_contDiff
      realGeodesicCurve_zero)
    (adelicSmoothInfinitesimal_skew f realUpperUnipotent realUpperUnipotent_entries_contDiff
      realUpperUnipotent_zero)
    (adelicSmoothInfinitesimal_skew f realLowerUnipotent realLowerUnipotent_entries_contDiff
      realLowerUnipotent_zero) v w

end
end Dubon2026
