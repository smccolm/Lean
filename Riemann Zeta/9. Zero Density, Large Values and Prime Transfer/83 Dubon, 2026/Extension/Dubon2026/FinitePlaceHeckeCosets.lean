import Dubon2026.FinitePlaceHeckeUpper
import Dubon2026.SurjectiveCosetEquiv

/-! # The actual p+1 Hecke cosets of the genuine local level group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine full adelic Hecke quotient is equivalent to the intrinsic local conjugation-stabilizer quotient at its original prime. -/
def finiteAdelicHeckeQuotientLocalEquiv (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] :
    finiteAdeleGL2Gamma0 N ⧸ finiteAdelicHeckeUpper N p ≃
      finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) ⧸
        finitePlaceHeckeUpper N p (Fact.out : p.Prime) :=
  (Quotient.congrRight (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    exact finiteAdelicHeckeUpper_local_iff N p (a⁻¹ * b))).trans
    (subgroupComapCosetEquiv (finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicLevelAt_surjective N _) (finitePlaceHeckeUpper N p (Fact.out : p.Prime)))

/-- The actual quotient equivalence sends every original adelic level representative to precisely its genuine local coordinate. -/
theorem finiteAdelicHeckeQuotientLocalEquiv_mk (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (g : finiteAdeleGL2Gamma0 N) :
    finiteAdelicHeckeQuotientLocalEquiv N p (QuotientGroup.mk g) =
      QuotientGroup.mk (finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime)) g) := rfl

/-- The original p+1 classical representatives give exactly all intrinsic local Hecke cosets, with no repetition. -/
def finitePlaceHeckeCosetEquiv (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) : Option (ZMod p) ≃
      finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) ⧸
        finitePlaceHeckeUpper N p (Fact.out : p.Prime) :=
  (finiteAdelicHeckeUpperCosetEquiv N p hpN).trans (finiteAdelicHeckeQuotientLocalEquiv N p)

/-- The actual local coset transversal uses precisely the original inverse classical Gamma0 representatives evaluated at p. -/
theorem finitePlaceHeckeCosetEquiv_apply (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (i : Option (ZMod p)) :
    finitePlaceHeckeCosetEquiv N p hpN i = QuotientGroup.mk
      (finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime))
        (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i))⁻¹) := rfl

/-- The genuine intrinsic local Hecke quotient has exactly p+1 cosets. -/
theorem finitePlaceHeckeCosets_card (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) :
    Nat.card (finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) ⧸
      finitePlaceHeckeUpper N p (Fact.out : p.Prime)) = p + 1 := by
  rw [← Nat.card_congr (finitePlaceHeckeCosetEquiv N p hpN)]
  simp [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

end
end Dubon2026
