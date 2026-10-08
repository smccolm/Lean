import Dubon2026.RealSmoothOneParameterJets
import Dubon2026.AdelicClosedWeightLines

/-! # Exact all-order original adelic norm jets and genuine infinitesimal powers -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every original smooth-vector norm jet along an actual smooth one-parameter subgroup is the corresponding original infinitesimal power, translated by the same original subgroup. -/
theorem adelicSmoothInfinitesimal_iteratedDeriv (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (v : adelicRealSmoothSubmodule f) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun s : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c s)) v.val) t =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t))
        (((adelicSmoothInfinitesimal f c hc) ^ n) v).val := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact congrFun (@realMatrixSmoothInfinitesimal_iteratedDeriv (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) c hc hadd v n) t

/-- At the genuine identity, every original Hilbert norm jet is exactly the original infinitesimal power itself. -/
theorem adelicSmoothInfinitesimal_iteratedDeriv_zero (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (hc0 : c 0 = 1)
    (v : adelicRealSmoothSubmodule f) (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c s)) v.val) 0 =
      (((adelicSmoothInfinitesimal f c hc) ^ n) v).val := by
  have he := adelicSmoothInfinitesimal_iteratedDeriv f c hc hadd v n 0
  simpa only [hc0, map_one, Module.End.one_apply] using he

end
end Dubon2026
