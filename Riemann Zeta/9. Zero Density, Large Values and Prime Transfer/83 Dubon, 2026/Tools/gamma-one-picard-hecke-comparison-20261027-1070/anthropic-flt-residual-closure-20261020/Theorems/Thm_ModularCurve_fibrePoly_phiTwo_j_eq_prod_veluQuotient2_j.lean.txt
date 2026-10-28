import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
attribute [-instance] WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] WeierstrassCurve.veluX_empty

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine
theorem ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.solution
