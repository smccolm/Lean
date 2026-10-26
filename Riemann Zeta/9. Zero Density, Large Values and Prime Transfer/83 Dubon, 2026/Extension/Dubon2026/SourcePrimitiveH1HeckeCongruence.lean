import Dubon2026.SourceFaithfulCharacterDivisibility
import Dubon2026.SourceBinaryH1PrimePowerKernel
import Dubon2026.SourcePrimitiveLocalH1Character
import Dubon2026.SourceBinaryH1HeckeCommute

/-! DUB-17/18 -> original all-weight adic association -> actual geometric
finite-precision Hecke realization. An original integral H1 operator that
vanishes after coefficient reduction has a divisible original Hecke
character value. The actual Fourier-field embedding is retained.
This discharges a necessary congruence condition for finite-level
specialization; it does not itself construct the geometric Galois action.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E]

open scoped IsMulCommutative in
/-- Vanishing of an actual original H1 operator modulo a nonzero modulus
makes its original field-valued character divided by that modulus integral. -/
theorem sourcePrimitiveH1Hecke_operator_congruence_integral
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (N : ℕ) (hN : N ≠ 0)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q (k - 2).toNat (T.val x) = 0) :
    IsIntegral ℤ (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) / (N : E)) := by
  let w := (k - 2).toNat
  let A := sourceBinaryH1HeckeAlgebra Q w
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (sourceBinaryH1PrimeOperators_commute ℤ Q w p q).eq)
  letI : CommRing A := inferInstance
  letI := sourceIntegralBinaryH1Finite Q w
  have hn : ((N : ℤ) : E) ≠ 0 := by exact_mod_cast hN
  have h := sourceFaithfulCharacter_div_isIntegral
    (M := groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w))
    (τ.toRingHom.comp (sourcePrimitiveFieldH1HeckeCharacter f hk).toRingHom)
    T (N : ℤ) hn (fun x =>
      (sourceBinaryH1Change_zmod_nonzero_eq_zero_iff Q w N hN (T.val x)).mp (hT x))
  simpa only [RingHom.comp_apply, Int.cast_natCast] using h

variable [ValuativeRel E]

/-- Original operator congruences give the same valuation bound on the
original Fourier-field H1 character, without a supplied eigenvector lift. -/
theorem sourcePrimitiveH1Hecke_operator_congruence_valuation
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (N : ℕ) (hN : N ≠ 0)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q (k - 2).toNat (T.val x) = 0) :
    ValuativeRel.valuation E (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T)) ≤
      ValuativeRel.valuation E (N : E) := by
  have hi := sourcePrimitiveH1Hecke_operator_congruence_integral f hk τ N hN T hT
  have hv := (Valuation.integer.integers (ValuativeRel.valuation E)).isIntegral_iff_v_le_one.mp
    hi.tower_top
  have hn : (N : E) ≠ 0 := by exact_mod_cast hN
  have hpos : 0 < ValuativeRel.valuation E (N : E) :=
    pos_iff_ne_zero.mpr (by simpa using hn)
  rw [map_div₀] at hv
  simpa only [one_mul] using (div_le_iff₀ hpos).mp hv

/-- At every positive power of every original prime, vanishing of the
original coefficient-reduced H1 operator forces the matching precision
bound on the same original primitive character. -/
theorem sourcePrimitiveH1Hecke_primePower_congruence_valuation
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1))))
        Q (k - 2).toNat (T.val x) = 0) :
    ValuativeRel.valuation E (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T)) ≤
      ValuativeRel.valuation E (p : E) ^ (n + 1) := by
  simpa only [Nat.cast_pow, map_pow] using
    sourcePrimitiveH1Hecke_operator_congruence_valuation f hk τ
      (p ^ (n + 1)) (pow_ne_zero _ hp.ne_zero) T hT

end
end Dubon2026
