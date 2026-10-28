import Dubon2026.SourceParabolicHeckeCongruence
import Dubon2026.SourcePrimitiveAdicH1Quotients

/-! DUB17/18 -> original all-weight association -> finite parabolic
character descent. The original compatible adic character kills every
operator whose coefficient reduction vanishes on integral parabolic H1,
at every positive power of every prime away from one fixed nonzero
integer. The finite Gamma1 parabolic transfer and exceptional primes
remain separate obligations. Reuse the native full-H1 ideal-power proof. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped ValuativeRel

theorem sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away
    {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ {E : Type} [Field E] [CharZero E] [ValuativeRel E]
      (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
      (p : ℕ), p.Prime → IsCoprime (p : ℤ) d → ∀ [CharP 𝓀[E] p] (n : ℕ)
      (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat),
      (∀ x : H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
        x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) →
        sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1))))
          Q (k - 2).toNat (T.val x) = 0) →
      sourcePrimitiveH1AdicQuotientCharacter f hk τ n T = 0 := by
  obtain ⟨d, hd, hint⟩ := sourcePrimitiveParabolicHecke_congruence_integral_away f hk
  refine ⟨d, hd, ?_⟩
  intro E _ _ _ τ p hp hcop _ n T hT
  have hc : IsCoprime ((p ^ (n + 1) : ℕ) : ℤ) d := by
    simpa only [Nat.cast_pow] using hcop.pow_left (m := n + 1)
  have hi := hint τ (p ^ (n + 1)) (pow_ne_zero _ hp.ne_zero) hc T hT
  let B := 𝒪[E]
  let I := IsLocalRing.maximalIdeal B
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
