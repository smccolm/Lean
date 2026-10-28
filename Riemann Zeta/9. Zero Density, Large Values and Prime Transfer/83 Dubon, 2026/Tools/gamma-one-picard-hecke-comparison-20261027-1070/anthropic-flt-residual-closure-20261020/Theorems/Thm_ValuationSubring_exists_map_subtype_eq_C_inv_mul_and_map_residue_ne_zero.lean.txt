import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero

theorem ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    (q₁ : Polynomial L) (hq₁ : q₁ ≠ 0) :
    ∃ q : Polynomial A, ∃ c : L, c ≠ 0 ∧
      (q.map A.subtype = Polynomial.C c⁻¹ * q₁) ∧ q.map (IsLocalRing.residue A) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.solution
