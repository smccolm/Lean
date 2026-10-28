import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_ModularCurve_index_heckeUpper

theorem ModularCurve.index_heckeUpper {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (HeckeEis.heckeUpper N ℓ).index = ℓ + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_index_heckeUpper.solution
