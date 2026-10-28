import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk

theorem AlgebraicCurve.isIntegral_adjoin_intermediateField_mk {L F : Type*} [Field L] [Field F] [Algebra L F] (E : IntermediateField L F) {j x : F} (hj : j ∈ E) (hx : x ∈ E) (h : IsIntegral (Algebra.adjoin L {j}) x) : IsIntegral (Algebra.adjoin L {(⟨j, hj⟩ : E)}) (⟨x, hx⟩ : E) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk.solution
