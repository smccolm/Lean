import Dubon2026.FiniteIdeleCharacterLocalUnits
import Dubon2026.FinitePlaceHeckeDiagonalPowers

/-! # Principal prime ideles with their original prime coordinate removed -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The principal rational prime idele divided by its actual local prime insertion. -/
def finiteIdelePrimeAway (p : ℕ) [NeZero p] (hp : p.Prime) : (FiniteAdeleRing ℤ ℚ)ˣ :=
  Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom
    (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne p))) *
      (finiteAdeleLocalUnit (rationalPrimePlace p hp) (finitePlacePrimeUnit p _))⁻¹

/-- Removing the original prime coordinate leaves precisely one at that place. -/
theorem finiteIdelePrimeAway_same (p : ℕ) [NeZero p] (hp : p.Prime) :
    Units.map (finiteAdelePlace (rationalPrimePlace p hp)).toMonoidHom
      (finiteIdelePrimeAway p hp) = 1 := by
  rw [finiteIdelePrimeAway, map_mul, map_inv, finiteAdeleLocalUnit_same]
  have he : Units.map (finiteAdelePlace (rationalPrimePlace p hp)).toMonoidHom
      (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom
        (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne p)))) =
      finitePlacePrimeUnit p (rationalPrimePlace p hp) := Units.ext rfl
  rw [he, mul_inv_cancel]

/-- At every other original place the same idele retains the actual rational prime value. -/
theorem finiteIdelePrimeAway_ne (p : ℕ) [NeZero p] (hp : p.Prime)
    (v : HeightOneSpectrum ℤ) (hv : v ≠ rationalPrimePlace p hp) :
    Units.map (finiteAdelePlace v).toMonoidHom (finiteIdelePrimeAway p hp) =
      finitePlacePrimeUnit p v := by
  rw [finiteIdelePrimeAway, map_mul, map_inv, finiteAdeleLocalUnit_ne _ _ hv, inv_one, mul_one]
  exact Units.ext rfl

/-- The original prime-removed idele has integral value at every actual place. -/
theorem finiteIdelePrimeAway_integral (p : ℕ) [NeZero p] (hp : p.Prime) :
    (finiteIdelePrimeAway p hp).val ∈ finiteAdeleIntegerSubring := by
  intro v
  change finiteAdelePlace v (finiteIdelePrimeAway p hp).val ∈ v.adicCompletionIntegers ℚ
  by_cases hv : v = rationalPrimePlace p hp
  · subst v
    have he := congrArg Units.val (finiteIdelePrimeAway_same p hp)
    change finiteAdelePlace (rationalPrimePlace p hp) (finiteIdelePrimeAway p hp).val = 1 at he
    rw [he]
    exact ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).one_mem
  · have he := congrArg Units.val (finiteIdelePrimeAway_ne p hp v hv)
    change finiteAdelePlace v (finiteIdelePrimeAway p hp).val = (finitePlacePrimeUnit p v).val at he
    rw [he, finitePlacePrimeUnit_val]
    simp

/-- Its actual inverse is also integral at every original place. -/
theorem finiteIdelePrimeAway_inverse_integral (p : ℕ) [NeZero p] (hp : p.Prime) :
    (finiteIdelePrimeAway p hp).inv ∈ finiteAdeleIntegerSubring := by
  intro v
  change (Units.map (finiteAdelePlace v).toMonoidHom (finiteIdelePrimeAway p hp)).inv ∈
    v.adicCompletionIntegers ℚ
  by_cases hv : v = rationalPrimePlace p hp
  · subst v
    rw [finiteIdelePrimeAway_same]
    exact ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).one_mem
  · rw [finiteIdelePrimeAway_ne p hp v hv]
    exact finitePlace_inverse_level_integral p v (rationalPrimePlace_prime_not_mem p hp v hv)

/-- The original prime-removed idele defines a genuine unit in the original integral finite adele ring. -/
def finiteIdelePrimeAwayIntegerUnit (p : ℕ) [NeZero p] (hp : p.Prime) :
    finiteAdeleIntegerSubringˣ where
  val := ⟨(finiteIdelePrimeAway p hp).val, finiteIdelePrimeAway_integral p hp⟩
  inv := ⟨(finiteIdelePrimeAway p hp).inv, finiteIdelePrimeAway_inverse_integral p hp⟩
  val_inv := Subtype.ext (finiteIdelePrimeAway p hp).val_inv
  inv_val := Subtype.ext (finiteIdelePrimeAway p hp).inv_val

/-- Its actual residue away from the removed prime is the original prime residue. -/
theorem finiteIdelePrimeAway_residue (D p : ℕ) [NeZero D] [NeZero p] (hp : p.Prime)
    (hpD : p.Coprime D) :
    finiteAdeleResidue D (finiteIdelePrimeAwayIntegerUnit p hp).val = (p : ZMod D) := by
  have hD : (D : ℤ) ∉ (rationalPrimePlace p hp).asIdeal := by
    rw [rationalPrimePlace_nat_mem_iff]
    exact hp.coprime_iff_not_dvd.mp hpD
  have hs : finiteAdeleLevelMultiple D ((finiteIdelePrimeAway p hp).val - (p : ℤ)) := by
    apply (finiteAdeleLevelMultiple_iff D _).mpr
    intro v
    change algebraMap ℚ (v.adicCompletion ℚ) ((D : ℚ)⁻¹) *
      (finiteAdelePlace v (finiteIdelePrimeAway p hp).val - ((p : ℤ) : v.adicCompletion ℚ)) ∈
        v.adicCompletionIntegers ℚ
    by_cases hv : v = rationalPrimePlace p hp
    · subst v
      have he := congrArg Units.val (finiteIdelePrimeAway_same p hp)
      change finiteAdelePlace (rationalPrimePlace p hp) (finiteIdelePrimeAway p hp).val = 1 at he
      rw [he]
      exact ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).toSubring.mul_mem
        (finitePlace_inverse_level_integral D _ hD)
        (((rationalPrimePlace p hp).adicCompletionIntegers ℚ).toSubring.sub_mem (by simp) (by simp))
    · have he := congrArg Units.val (finiteIdelePrimeAway_ne p hp v hv)
      change finiteAdelePlace v (finiteIdelePrimeAway p hp).val = (finitePlacePrimeUnit p v).val at he
      rw [he, finitePlacePrimeUnit_val, Int.cast_natCast, sub_self, mul_zero]
      exact (v.adicCompletionIntegers ℚ).zero_mem
  simpa only [Int.cast_natCast] using
    (finiteAdeleResidue_eq_intCast_iff D (finiteIdelePrimeAwayIntegerUnit p hp).val (p : ℤ)).mpr hs

end
end Dubon2026
