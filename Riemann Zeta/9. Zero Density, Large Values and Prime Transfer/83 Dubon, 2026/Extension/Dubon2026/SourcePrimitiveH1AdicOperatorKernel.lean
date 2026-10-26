import Dubon2026.SourcePrimitiveH1HeckeCongruence
import Dubon2026.SourcePrimitiveAdicH1Quotients

/-! DUB-17/18 -> original all-weight adic association -> actual finite-level
Hecke specialization. The exact original H1 character kills every operator
that vanishes modulo the corresponding positive prime power. Integrality
of the divided character value and the actual residue characteristic put
it in the required maximal-ideal power. No eigenvector lift is assumed. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- A zero original H1 operator modulo a positive prime power has zero
value under the matching original finite adic Hecke character. -/
theorem sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) (hp : p.Prime) [CharP 𝓀[E] p]
    (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1))))
        Q (k - 2).toNat (T.val x) = 0) :
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n T = 0 := by
  let B := 𝒪[E]
  let I := IsLocalRing.maximalIdeal B
  have hi := sourcePrimitiveH1Hecke_operator_congruence_integral f hk τ
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
