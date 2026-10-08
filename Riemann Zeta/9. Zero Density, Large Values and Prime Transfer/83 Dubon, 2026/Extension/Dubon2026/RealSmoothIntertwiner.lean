import Dubon2026.RealSmoothInfinitesimalOperator
import Dubon2026.LinearMapSmoothJets

/-! # Original bounded intertwiners preserve the actual smooth domain and its derivatives -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- An actual bounded intertwiner preserves every original smooth matrix-family orbit. -/
theorem realMatrixSmoothSubmodule_intertwiner (ρ : Representation ℂ SL(2, ℝ) V)
    (T : V →L[ℂ] V) (hT : ∀ g v, T (ρ g v) = ρ g (T v))
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) : T v ∈ realMatrixSmoothSubmodule ρ := by
  intro E _ _ c hc
  have he : (fun t => ρ (c t) (T v)) = (fun t => T (ρ (c t) v)) :=
    funext (fun t => (hT (c t) v).symm)
  rw [he]
  exact (T.restrictScalars ℝ).contDiff.comp (hv E c hc)

/-- The original bounded intertwiner restricted to its genuine invariant smooth domain. -/
def realMatrixSmoothIntertwiner (ρ : Representation ℂ SL(2, ℝ) V)
    (T : V →L[ℂ] V) (hT : ∀ g v, T (ρ g v) = ρ g (T v)) :
    Module.End ℂ (realMatrixSmoothSubmodule ρ) :=
  T.toLinearMap.restrict (fun v hv => realMatrixSmoothSubmodule_intertwiner ρ T hT v hv)

/-- The original restricted intertwiner commutes with every original real smooth-curve derivative. -/
theorem realMatrixSmoothIntertwiner_infinitesimal (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (T : V →L[ℂ] V) (hT : ∀ g v, T (ρ g v) = ρ g (T v))
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) :
    Commute (realMatrixSmoothIntertwiner ρ T hT) (realMatrixSmoothInfinitesimal ρ L hL c hc) := by
  ext v
  change T (deriv (fun t : ℝ => ρ (c t) v.val) 0) =
    deriv (fun t : ℝ => ρ (c t) (T v.val)) 0
  have hd : DifferentiableAt ℝ (fun t : ℝ => ρ (c t) v.val) 0 :=
    ((contDiff_infty.mp (v.property ℝ c hc) 1).differentiable (by norm_num)) 0
  have he : (fun t : ℝ => ρ (c t) (T v.val)) = (fun t => T (ρ (c t) v.val)) :=
    funext (fun t => (hT (c t) v.val).symm)
  rw [he]
  exact (deriv_continuousLinearMap (T.restrictScalars ℝ) _ 0 hd).symm

end
end Dubon2026
