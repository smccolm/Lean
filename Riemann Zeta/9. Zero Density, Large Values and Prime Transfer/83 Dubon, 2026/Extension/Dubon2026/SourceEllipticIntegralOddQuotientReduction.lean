import Dubon2026.SourceEllipticTorsionReductionCoordinates
import Dubon2026.SourceEllipticOddQuotientJ

/-! The constructed integral odd quotient reduces to the literal quotient
of the reduced cyclic generator. The half-orbit map is injective because
reduction preserves exact order. Good reduction of the quotient follows
from the already proved odd quotient discriminant theorem, in every residue
characteristic prime to the order. This discharges the integral model input
to the DUB-17/18 modular-polynomial specialization argument. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVelu SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
variable [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

/-- Reduction is injective on the integral half-orbit set of the actual odd kernel. -/
theorem integralOddSummingSet_residue_injOn (hΔ : (W.map (residue A)).Δ ≠ 0)
    {n : ℕ} (hN : IsUnit ((2 * n + 1 : ℕ) : A))
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (Prod.map (residue A) (residue A))
      (integralOddSummingSet A W hN Q (hQ ▸ addOrderOf_nsmul_eq_zero Q) n) := by
  have hkill : (2 * n + 1) • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hredorder : addOrderOf (reducePoint hΔ Q) = 2 * n + 1 :=
    (addOrderOf_reducePoint hΔ hN Q hkill).trans hQ
  intro u hu v hv he
  simp only [integralOddSummingSet, Finset.mem_coe, Finset.mem_image] at hu hv
  obtain ⟨i, hi, rfl⟩ := hu
  obtain ⟨j, hj, rfl⟩ := hv
  rw [integralTorsionCoordinates_residue hΔ, integralTorsionCoordinates_residue hΔ,
    reducePoint_nsmul_of_torsion hΔ hN Q hkill,
    reducePoint_nsmul_of_torsion hΔ hN Q hkill] at he
  have hij : i = j := coordsOrZero_odd_nsmul_injOn hredorder hi hj he
  subst j
  rfl

/-- The literal integral odd quotient reduces to the actual quotient of the reduced generator. -/
theorem integralOddQuotientModel_residue (hΔ : (W.map (residue A)).Δ ≠ 0)
    {n : ℕ} (hN : IsUnit ((2 * n + 1 : ℕ) : A))
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (integralOddQuotientModel A W hN Q (hQ ▸ addOrderOf_nsmul_eq_zero Q) n).map (residue A) =
      veluQuotient (W.map (residue A))
        (oddOrderSummingSet (W.map (residue A)) (reducePoint hΔ Q) n) := by
  rw [integralOddQuotientModel, veluQuotient_map _ _ _
    (integralOddSummingSet_residue_injOn hΔ hN Q hQ), integralOddSummingSet_residue hΔ]

/-- The constructed integral quotient has unit discriminant, derived from its actual reduction. -/
theorem integralOddQuotientModel_isElliptic (hΔ : (W.map (residue A)).Δ ≠ 0)
    {n : ℕ} (hN : IsUnit ((2 * n + 1 : ℕ) : A))
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (integralOddQuotientModel A W hN Q (hQ ▸ addOrderOf_nsmul_eq_zero Q) n).IsElliptic := by
  letI : (W.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hredorder : addOrderOf (reducePoint hΔ Q) = 2 * n + 1 :=
    (addOrderOf_reducePoint hΔ hN Q (hQ ▸ addOrderOf_nsmul_eq_zero Q)).trans hQ
  letI := odd_quotient_isElliptic (W.map (residue A)) (reducePoint hΔ Q) hredorder
  rw [WeierstrassCurve.isElliptic_iff, ← map_residue_Δ_ne_zero_iff,
    integralOddQuotientModel_residue hΔ hN Q hQ]
  exact (WeierstrassCurve.isUnit_Δ _).ne_zero

end
end Dubon2026.SourceEllipticReduction
