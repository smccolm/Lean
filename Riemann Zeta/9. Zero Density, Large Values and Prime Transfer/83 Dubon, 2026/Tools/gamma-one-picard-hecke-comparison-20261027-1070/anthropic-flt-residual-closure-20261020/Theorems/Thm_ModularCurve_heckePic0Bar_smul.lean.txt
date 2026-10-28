import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_heckePic0Bar_smul

theorem ModularCurve.heckePic0Bar_smul {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : ModularCurve.HeckeAlphaBarIntegral L N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral L N ℓ) [AlgebraicCurve.HasPrincipalDivisors L (ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (N * ℓ)))] (hFI : AlgebraicCurve.FundamentalIdentityAlong L (ModularCurve.heckeBetaBar L N ℓ) hβ) (hfin : AlgebraicCurve.FiniteAlong L (ModularCurve.heckeAlphaBar L N ℓ)) (hN : AlgebraicCurve.NormFormulaAlong L (ModularCurve.heckeAlphaBar L N ℓ) hfin) (σ : L ≃ₐ[ℚ] L) (c : AlgebraicCurve.Pic0 L (ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N))) : ModularCurve.heckePic0Bar hα hβ hFI hfin hN (σ • c) = σ • ModularCurve.heckePic0Bar hα hβ hFI hfin hN c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckePic0Bar_smul.solution
