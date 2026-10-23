import Dubon2026.SourceEllipticOddActualDiscriminant

/-! The explicit odd quotient of an actual short model is elliptic.
Algebraic closedness supplies the cubic roots; the actual discriminant
identity proves nonvanishing. No root enumeration or target ellipticity
is assumed. General-model descent and characteristic two remain required
before the full quotient theorem and the DUB-17 / DUB-18 inertia chain. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem odd_quotient_discriminant_of_short_model (h2 : (2 : K) ≠ 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) [V.IsElliptic]
    {n : ℕ} (Q : V.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient V (oddOrderSummingSet V Q n)).Δ *
        (∏ P ∈ oddOrderSummingSet V Q n, veluU V P.1 P.2) ^ 4 = V.Δ ^ (2 * n + 1) := by
  have h4 : V.twoTorsionPolynomial.a ≠ 0 := by
    change (4 : K) ≠ 0
    simpa only [show (2 : K) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  obtain ⟨r₁, r₂, r₃, hr⟩ := (Cubic.splits_iff_roots_eq_three h4).mp
    (show (V.twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits from IsAlgClosed.splits _)
  exact odd_quotient_discriminant_of_split_short_model h2 V ha₁ ha₃ r₁ r₂ r₃ hr Q hQ

theorem odd_quotient_isElliptic_of_short_model (h2 : (2 : K) ≠ 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) [V.IsElliptic]
    {n : ℕ} (Q : V.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient V (oddOrderSummingSet V Q n)).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  have h := odd_quotient_discriminant_of_short_model h2 V ha₁ ha₃ Q hQ
  rw [hΔ, zero_mul] at h
  exact pow_ne_zero _ V.isUnit_Δ.ne_zero h.symm

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
