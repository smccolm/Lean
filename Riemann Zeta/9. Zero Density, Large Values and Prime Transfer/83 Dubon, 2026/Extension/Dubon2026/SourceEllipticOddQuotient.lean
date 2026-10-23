import Dubon2026.SourceEllipticOddNormalizedDiscriminant
import Dubon2026.SourceEllipticOddBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The actual odd quotient is elliptic over the original field.
Base change to the algebraic closure preserves the actual point's order,
the exact finite kernel-coordinate set, the quotient coefficients and its
discriminant identity. Injectivity descends the identity. All characteristics,
including two and three, are retained. This discharges odd quotient
ellipticity before quotient maps and modular-polynomial products, cyclic
subgroup roots, inertia census and good reduction in DUB-17 / DUB-18. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]

theorem odd_quotient_discriminant (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).Δ *
      (∏ P ∈ oddOrderSummingSet W Q n, veluU W P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  classical
  let K := AlgebraicClosure F
  let f : F →+* K := algebraMap F K
  have hQK : addOrderOf (pointMapHom f W Q) = 2 * n + 1 := by
    rw [addOrderOf_injective (pointMapHom f W) (pointMapHom_injective f W), hQ]
  have hK := odd_quotient_discriminant_of_isAlgClosed (W.map f) (pointMapHom f W Q) hQK
  rw [map_oddOrderSummingSet] at hK
  exact (identity_map_iff f W (oddOrderSummingSet W Q n) n).mp hK

theorem odd_quotient_isElliptic (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (veluQuotient W (oddOrderSummingSet W Q n)).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  have h := odd_quotient_discriminant W Q hQ
  rw [hΔ, zero_mul] at h
  exact pow_ne_zero _ W.isUnit_Δ.ne_zero h.symm

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
