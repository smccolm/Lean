import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one

theorem IsLocalRing.exists_dvd_pow_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.solution
