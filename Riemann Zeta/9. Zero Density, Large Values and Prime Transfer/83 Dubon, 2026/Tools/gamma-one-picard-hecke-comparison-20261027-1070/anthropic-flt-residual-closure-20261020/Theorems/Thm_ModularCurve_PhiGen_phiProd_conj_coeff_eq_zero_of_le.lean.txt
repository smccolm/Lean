import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ * ℓ + ℓ ≤ m) : ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (-(m : ℤ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.solution
