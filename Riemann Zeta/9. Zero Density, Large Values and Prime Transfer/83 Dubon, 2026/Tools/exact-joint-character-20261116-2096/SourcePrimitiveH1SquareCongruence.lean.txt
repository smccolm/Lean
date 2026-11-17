import Dubon2026.SourcePrimitiveH1AdicOperatorKernel
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
finite joint geometric/boundary character. Vanishing of the square of
the actual original H1 operator at twice the precision suffices for the
original character at the requested precision. Integrality of a power
is descended by the pinned Mathlib theorem; no discrete valuation or
unit boundary separator is assumed. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E]

/-- A squared original operator congruence at the squared modulus gives
integrality of the original character divided by the unsquared modulus. -/
theorem sourcePrimitiveH1Hecke_square_congruence_integral
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (N : ℕ) (hN : N ≠ 0)
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod (N ^ 2))) Q (k - 2).toNat
        ((T ^ 2).val x) = 0) :
    IsIntegral ℤ (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) / (N : E)) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  have hi := sourcePrimitiveH1Hecke_operator_congruence_integral f hk τ
    (N ^ 2) (pow_ne_zero _ hN) (T ^ 2) hT
  simpa only [map_pow, Nat.cast_pow, div_pow] using hi

variable [ValuativeRel E]

/-- The original adic character kills a word whose original H1 square
vanishes modulo the square of the requested prime-power modulus. -/
theorem sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator_square
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p]
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod ((p ^ (n + 1)) ^ 2)))
        Q (k - 2).toNat ((T ^ 2).val x) = 0) :
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n T = 0 := by
  let B := 𝒪[E]
  let I := IsLocalRing.maximalIdeal B
  have hi := sourcePrimitiveH1Hecke_square_congruence_integral f hk τ
    (p ^ (n + 1)) (pow_ne_zero _ hp.ne_zero) T hT
  have hv := (Valuation.integer.integers (ValuativeRel.valuation E)).isIntegral_iff_v_le_one.mp
    hi.tower_top
  let b : B := ⟨τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) /
    ((p ^ (n + 1) : ℕ) : E), hv⟩
  have heq : sourcePrimitiveLocalH1HeckeCharacter f hk τ T = (p : B) ^ (n + 1) * b := by
    apply Subtype.ext
    rw [sourcePrimitiveLocalH1HeckeCharacter_coe]
    change τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) =
      (p : E) ^ (n + 1) * (τ (sourcePrimitiveFieldH1HeckeCharacter f hk T) /
        ((p ^ (n + 1) : ℕ) : E))
    have hpn : (p : E) ^ (n + 1) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [Nat.cast_pow, mul_comm, div_mul_cancel₀ _ hpn]
  have hpI : (p : B) ∈ I := by
    apply (IsLocalRing.residue_eq_zero_iff (p : B)).mp
    rw [map_natCast, CharP.cast_eq_zero]
  change Ideal.Quotient.mk (I ^ (n + 1)) (sourcePrimitiveLocalH1HeckeCharacter f hk τ T) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [heq]
  exact (I ^ (n + 1)).mul_mem_right b (Ideal.pow_mem_pow hpI (n + 1))

end
end Dubon2026
