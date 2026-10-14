import Dubon2026.WittCyclotomicDiagonalFrobenius
import Dubon2026.WittCyclotomicChangedNorm

/-! # The actual diagonal Frobenius on the cyclotomic fraction field

Construct the inverse natural exponent modulo the exact prime-power
level, extend the actual ring automorphism to fractions, and prove its
coefficient action and fixed changed point. This removes inverse-action
existence from the hypotheses of DUB-17's finite auxiliary-field descent.
-/
namespace Dubon2026
noncomputable section
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite

/-- A natural unit has a constructed inverse exponent at every required prime-power level. -/
theorem primePowerNaturalUnit_exists_inverse (p : ℕ) [Fact p.Prime] (n a : ℕ) (ha : ¬p ∣ a) :
    ∃ b : ℕ, b.Coprime (p ^ (n + 1)) ∧ a * b ≡ 1 [MOD p ^ (n + 1)] := by
  let N := p ^ (n + 1)
  haveI : NeZero N := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hac : a.Coprime N := (Fact.out : p.Prime).coprime_pow_of_not_dvd ha
  let z := ZMod.unitOfCoprime a hac
  let b := ((z⁻¹ : (ZMod N)ˣ) : ZMod N).val
  have hb : b.Coprime N := (ZMod.isUnit_iff_coprime b N).mp (by
    change IsUnit (((((z⁻¹ : (ZMod N)ˣ) : ZMod N).val) : ℕ) : ZMod N)
    rw [ZMod.natCast_zmod_val]
    exact (z⁻¹).isUnit)
  refine ⟨b, hb, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  rw [Nat.cast_mul, Nat.cast_one]
  change (a : ZMod N) * (b : ZMod N) = 1
  rw [show (a : ZMod N) = z.val from (ZMod.coe_unitOfCoprime a hac).symm]
  change z.val * (((z⁻¹ : (ZMod N)ˣ) : ZMod N).val : ZMod N) = 1
  rw [ZMod.natCast_zmod_val]
  simp

/-- The original diagonal ring automorphism extends canonically to its actual fraction field. -/
def wittCyclotomicDiagonalFieldFrobenius (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    wittCyclotomicField p n ≃+* wittCyclotomicField p n :=
  IsFractionRing.ringEquivOfRingEquiv (wittCyclotomicDiagonalFrobenius p n a b ha hb hab)

/-- Its action on the actual integral root algebra is the already constructed diagonal Frobenius. -/
theorem wittCyclotomicDiagonalFieldFrobenius_integer (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) (x : wittCyclotomicRootAlgebra p n) :
    wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab
      (algebraMap _ (wittCyclotomicField p n) x) =
      algebraMap _ (wittCyclotomicField p n) (wittCyclotomicDiagonalFrobenius p n a b ha hb hab x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

/-- The actual changed field point is fixed by the inverse-unit diagonal field Frobenius. -/
theorem wittCyclotomicDiagonalFieldFrobenius_changedPoint (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    wittCyclotomicDiagonalFieldFrobenius p n a b ha hb hab (wittCyclotomicChangedFieldPoint p u n) =
      wittCyclotomicChangedFieldPoint p u n := by
  rw [wittCyclotomicChangedFieldPoint, wittCyclotomicDiagonalFieldFrobenius_integer,
    wittCyclotomicDiagonalFrobenius_changedPoint p n a b ha hb hab u hu]

end
end Dubon2026
