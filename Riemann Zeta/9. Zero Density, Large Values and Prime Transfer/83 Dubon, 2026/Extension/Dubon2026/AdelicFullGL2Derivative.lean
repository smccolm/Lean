import Dubon2026.AdelicGL2NormDerivative
import Dubon2026.RealGL2CurvePositive

/-! # Norm derivatives along every genuine real general-linear curve -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter
open scoped MatrixGroups Topology

/-- The original completed adelic action has the genuine full complexified matrix Lie derivative along every real general-linear curve through the identity. -/
theorem adelicComplexGL2Action_hasDerivAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : adelicRealSmoothSubmodule f)
    (c : ℝ → GeneralLinearGroup (Fin 2) ℝ) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val i j) (a i j) 0) :
    HasDerivAt (fun t => adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (c t)) v.val)
      (adelicComplexGL2Action f (a.map Complex.ofReal) v).val 0 := by
  have he := realGL2Curve_positivePart_eventually c hc a hd
  have h₀ : realGL2PositivePart (c 0) = 1 := by
    rw [hc]
    exact realGL2PositivePart_of_positive 1
  have hP (i j : Fin 2) : HasDerivAt (fun t => (realGL2PositivePart (c t)).val.val i j) (a i j) 0 := by
    apply (hd i j).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    rw [ht]
  have hD := adelicComplexGL2Action_positive_hasDerivAt f v (fun t => realGL2PositivePart (c t)) h₀ a hP
  have heO : (fun t => adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (c t)) v.val) =ᶠ[𝓝 0]
      (fun t => adelicCyclicHilbertRepresentation f
        (adelicRealGL2Embedding (realGL2PositivePart (c t)).val) v.val) := by
    filter_upwards [he] with t ht
    rw [ht]
  exact @HasDerivAt.congr_of_eventuallyEq ℝ inferInstance (AdelicCyclicHilbert f)
    inferInstance inferInstance _ _ _ _ hD heO

end
end Dubon2026
