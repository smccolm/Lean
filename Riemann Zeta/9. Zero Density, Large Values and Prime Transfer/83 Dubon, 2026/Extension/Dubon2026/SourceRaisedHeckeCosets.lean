import Dubon2026.SourceRaisedLevelConjugation
import Dubon2026.SourceHeckeSubgroupConjugation

/-! Original good-prime Hecke cosets under the actual raised-level conjugation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> Hecke compatibility of original raised-level evaluation.
The existing actual transversal supplies both finite cardinalities, so
surjectivity follows from exact subgroup membership and coset injectivity.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (Q p ell : ℕ) [NeZero p] (hellQp : Nat.Coprime ell (Q * p))

include hellQp

/-- Actual conjugation preserves good-prime upper-Hecke membership because
the additional factor p is a unit modulo the original Hecke prime. -/
theorem sourceRaisedLevel_mem_upper (g : Gamma0 (Q * p)) :
    sourceRaisedLevelConjugation Q p g ∈ heckeUpperSubgroup Q ell ↔
      g ∈ heckeUpperSubgroup (Q * p) ell := by
  change ((((p : ℤ) * g.val 0 1 : ℤ) : ZMod ell) = 0) ↔
    (((g.val 0 1 : ℤ) : ZMod ell) = 0)
  rw [Int.cast_mul, Int.cast_natCast]
  have hp : IsUnit (p : ZMod ell) :=
    (ZMod.isUnit_iff_coprime p ell).mpr (hellQp.of_dvd_right (dvd_mul_left p Q)).symm
  exact hp.mul_right_eq_zero

/-- The actual raised-level conjugation induces its original Hecke coset map. -/
def sourceRaisedHeckeCosetMap :
    Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell →
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  Quotient.map' (sourceRaisedLevelConjugation Q p) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact (sourceRaisedLevel_mem_upper Q p ell hellQp _).mpr hab)

/-- An actual matrix class maps to its actual integral conjugate class. -/
theorem sourceRaisedHeckeCosetMap_mk (g : Gamma0 (Q * p)) :
    sourceRaisedHeckeCosetMap Q p ell hellQp
        (g : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) =
      (sourceRaisedLevelConjugation Q p g : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := rfl

/-- The original raised-level coset map respects the literal group action. -/
theorem sourceRaisedHeckeCosetMap_smul (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceRaisedHeckeCosetMap Q p ell hellQp (g • x) =
      sourceRaisedLevelConjugation Q p g • sourceRaisedHeckeCosetMap Q p ell hellQp x := by
  induction x using QuotientGroup.induction_on with
  | H x => exact congrArg QuotientGroup.mk (map_mul (sourceRaisedLevelConjugation Q p) g x)

/-- The actual conjugation induces an injective map of the original Hecke cosets. -/
theorem sourceRaisedHeckeCosetMap_injective :
    Function.Injective (sourceRaisedHeckeCosetMap Q p ell hellQp) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      intro h
      rw [sourceRaisedHeckeCosetMap_mk, sourceRaisedHeckeCosetMap_mk, QuotientGroup.eq,
        ← map_inv, ← map_mul, sourceRaisedLevel_mem_upper Q p ell hellQp] at h
      exact QuotientGroup.eq.mpr h

/-- The existing two original Hecke transversals make the exact coset map bijective. -/
theorem sourceRaisedHeckeCosetMap_bijective (hell : ell.Prime) :
    Function.Bijective (sourceRaisedHeckeCosetMap Q p ell hellQp) := by
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell
  have hellQ : Nat.Coprime ell Q := hellQp.of_dvd_right (dvd_mul_right Q p)
  apply (sourceRaisedHeckeCosetMap_injective Q p ell hellQp).bijective_of_nat_card_le
  exact le_of_eq ((Nat.card_congr (heckeUpperCosetEquiv hell hellQ)).symm.trans
    (Nat.card_congr (heckeUpperCosetEquiv hell hellQp)))

/-- The exact original Hecke coset equivalence induced by the raised-level conjugation. -/
def sourceRaisedHeckeCosetEquiv (hell : ell.Prime) :
    (Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) ≃
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell :=
  Equiv.ofBijective _ (sourceRaisedHeckeCosetMap_bijective Q p ell hellQp hell)

end
end Dubon2026
