/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The fixed-field proof is adapted to the original rational valuation integers
from Nyll/ClassFieldTheory/LubinTate/Padic/CompletedUnramifiedFrobeniusFixed.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/
import Dubon2026.RationalPrimeWittFractionField

/-! # The actual original local field is the Witt Frobenius fixed field

Clearing a genuine Witt denominator by a power of the original prime puts
any fixed fraction in the proved original integer fixed ring. Thus the
actual fraction-field fixed set equals the image of the original rational
prime completion. This discharges the coefficient-field descent needed
for DUB-17's auxiliary finite field, norm and ramified reciprocity formula.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime

/-- The fixed field of actual Witt Frobenius is exactly the image of the original rational prime local field. -/
theorem rationalPrimeWittFieldFrobenius_fixed_iff
    (p : ℕ) (hp : p.Prime) (x : rationalPrimeWittField p hp) :
    rationalPrimeWittFieldFrobenius p hp x = x ↔
      ∃ z : rationalPrimeLocalField p hp, rationalPrimeWittFieldMap p hp z = x := by
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let W := WittVector q (AlgebraicClosure (ZMod q))
  let E := rationalPrimeWittField p hp
  let φ := rationalPrimeWittFieldFrobenius p hp
  constructor
  · intro hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨m, u, hbu⟩ := WittVector.exists_eq_pow_p_mul' b hb0
    let c : W := a * (u⁻¹ : Wˣ)
    have hqW : (q : W) ≠ 0 := WittVector.p_nonzero q (AlgebraicClosure (ZMod q))
    have hqE : algebraMap W E ((q : W) ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective W E)).mpr (pow_ne_zero m hqW)
    have huE : algebraMap W E (u : W) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective W E)).mpr u.ne_zero
    have hbE : algebraMap W E b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective W E)).mpr hb0
    have hclear : algebraMap W E c = algebraMap W E ((q : W) ^ m) * x := by
      rw [show algebraMap W E c = algebraMap W E a * (algebraMap W E (u : W))⁻¹ by
        simp only [c, map_mul, map_units_inv]]
      rw [← div_eq_mul_inv]
      apply (div_eq_iff huE).2
      have habMul : algebraMap W E a = x * algebraMap W E b := (div_eq_iff hbE).1 hab
      rw [hbu, map_mul] at habMul
      exact habMul.trans (by ac_rfl)
    have hqMap : algebraMap W E (q : W) = (q : E) := map_natCast (algebraMap W E) q
    have hqPow : algebraMap W E ((q : W) ^ m) = (q : E) ^ m := by
      rw [map_pow, hqMap]
    have hφq : φ (q : E) = (q : E) := map_natCast φ q
    have hcFieldFixed : φ (algebraMap W E c) = algebraMap W E c := by
      rw [hclear, map_mul, show φ (algebraMap W E ((q : W) ^ m)) =
        algebraMap W E ((q : W) ^ m) by rw [hqPow, map_pow, hφq], hx]
    have hcFixed : WittVector.frobenius c = c := by
      apply IsFractionRing.injective W E
      rw [← rationalPrimeWittFieldFrobenius_integer p hp c]
      exact hcFieldFixed
    obtain ⟨z, hz⟩ := (rationalPrimeIntegerWittMap_frobenius_fixed_iff p hp c).mp hcFixed
    refine ⟨algebraMap 𝒪[rationalPrimeLocalField p hp] (rationalPrimeLocalField p hp) z /
      (q : rationalPrimeLocalField p hp) ^ m, ?_⟩
    rw [map_div₀, rationalPrimeWittFieldMap_integer, map_pow, map_natCast, hz]
    have hqE' : (q : E) ^ m ≠ 0 := by rwa [hqPow] at hqE
    apply (div_eq_iff hqE').2
    rw [hqPow] at hclear
    exact hclear.trans (mul_comm _ _)
  · rintro ⟨z, rfl⟩
    exact rationalPrimeWittFieldFrobenius_base p hp z

end
end Dubon2026
