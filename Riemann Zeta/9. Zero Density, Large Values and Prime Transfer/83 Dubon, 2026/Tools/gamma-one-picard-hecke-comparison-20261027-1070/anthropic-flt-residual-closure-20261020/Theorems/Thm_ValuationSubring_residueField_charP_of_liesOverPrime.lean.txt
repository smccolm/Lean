import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_residueField_charP_of_liesOverPrime

theorem ValuationSubring.residueField_charP_of_liesOverPrime {L : Type*} [Field L]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) :
    CharP (IsLocalRing.ResidueField A) ℓ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residueField_charP_of_liesOverPrime.solution
