import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_charInvolution_heckeOperatorHom

theorem ModularCurve.Period.charInvolution_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A] (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A) :
    ModularCurve.Period.charInvolution N ℤ A (HeckeEis.heckeOperatorHom N ℓ A φ)
      = HeckeEis.heckeOperatorHom N ℓ A (ModularCurve.Period.charInvolution N ℤ A φ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_charInvolution_heckeOperatorHom.solution
