import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
namespace P2MW.S_ValuationSubring_residueField_charP_of_liesOverPrime

theorem solution {L : Type*} [Field L]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) :
    CharP (IsLocalRing.ResidueField A) ℓ := by
  refine (CharP.charP_iff_prime_eq_zero hℓ).mpr ?_
  rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have : (((ℓ : ℕ) : A) : L) = (ℓ : L) := by simp
  rw [this]
  exact hA
