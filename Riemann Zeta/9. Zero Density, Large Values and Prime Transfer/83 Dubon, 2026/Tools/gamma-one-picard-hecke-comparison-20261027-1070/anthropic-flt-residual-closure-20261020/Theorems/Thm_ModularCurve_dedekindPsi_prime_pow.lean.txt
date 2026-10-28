import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_prime_pow

open ModularCurve
theorem ModularCurve.dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_prime_pow.solution
