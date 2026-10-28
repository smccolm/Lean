import Dubon2026.SourceParabolicAdicOperatorKernel

/-! DUB17/18 -> original all-weight association -> finite parabolic
character descent. Name the actual fixed exceptional integer already
proved to exist, retaining uniformity in every field, embedding, prime
and precision. This avoids repeatedly elaborating a large existential
statement during geometric operator descent; no bound is assumed. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)

/-- A fixed nonzero saturation bound supplied by the proved original parabolic congruence. -/
def sourcePrimitiveParabolicExceptionalInteger : ℤ :=
  (sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away f hk).choose

theorem sourcePrimitiveParabolicExceptionalInteger_ne_zero :
    sourcePrimitiveParabolicExceptionalInteger f hk ≠ 0 :=
  (sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away f hk).choose_spec.1

theorem sourcePrimitiveParabolicH1AdicQuotientCharacter_zero
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (p : ℕ) (hp : p.Prime)
    (hcop : IsCoprime (p : ℤ) (sourcePrimitiveParabolicExceptionalInteger f hk))
    [CharP 𝓀[E] p] (n : ℕ) (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat)
    (hT : ∀ x : H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
      x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat) →
      sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1))))
        Q (k - 2).toNat (T.val x) = 0) :
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n T = 0 :=
  (sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away f hk).choose_spec.2
    τ p hp hcop n T hT

end
end Dubon2026
