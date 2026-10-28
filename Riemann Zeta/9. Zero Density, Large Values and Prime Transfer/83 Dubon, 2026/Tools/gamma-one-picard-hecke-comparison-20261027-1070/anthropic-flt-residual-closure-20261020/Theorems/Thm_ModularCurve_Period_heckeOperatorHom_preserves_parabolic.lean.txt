import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic

open CongruenceSubgroup
theorem ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A)
    (hφ : ModularCurve.Period.IsParabolicHom (Gamma0 N) φ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 N) (HeckeEis.heckeOperatorHom N ℓ A φ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.solution
