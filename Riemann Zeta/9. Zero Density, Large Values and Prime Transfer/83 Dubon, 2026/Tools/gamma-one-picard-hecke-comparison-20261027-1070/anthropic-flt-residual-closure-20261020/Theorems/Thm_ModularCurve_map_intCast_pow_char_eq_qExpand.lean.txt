import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_map_intCast_pow_char_eq_qExpand

open ModularCurve
theorem ModularCurve.map_intCast_pow_char_eq_qExpand {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (s : LaurentSeries ℤ) :
    (s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.solution
