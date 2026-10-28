import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar
attribute [-simp] ModularCurve.jqNModC_one

theorem ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeBetaBar
    {N : ℕ} [NeZero N] (ℓ : ℕ) [NeZero ℓ] (D : ModularCurve.ComplexPlaceDictionary N)
    (D' : ModularCurve.ComplexPlaceDictionary (N * ℓ))
    (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong (ModularCurve.heckeBetaBar ℂ N ℓ) hβ =
        D.pt (ModularForm.heckeDiagMatrix ℓ • τ) ∧
      D'.ramification τ *
          (D'.pt τ).ramificationIndexAlong (ModularCurve.heckeBetaBar ℂ N ℓ) =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.solution
