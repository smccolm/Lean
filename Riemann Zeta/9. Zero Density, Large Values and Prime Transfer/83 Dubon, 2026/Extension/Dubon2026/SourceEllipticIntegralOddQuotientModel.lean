import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Dubon2026.SourceEllipticOddBaseChange

/-! Construct the literal integral odd quotient from actual torsion coordinates.
The exact generic curve is derived, not supplied. Compatibility with the
reduced cyclic subgroup and invertibility of the quotient discriminant still
need the reduction argument before modular-polynomial specialization applies. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticFunctionField
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

/-- Both actual coordinates of a point killed by a unit integer are integral. -/
theorem torsion_coords_mem (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) : (coordsOrZero P).1 ∈ A ∧ (coordsOrZero P).2 ∈ A := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨A.zero_mem, A.zero_mem⟩
  · have hx := torsion_x_mem_valuationSubring A W h N hN hP
    exact ⟨hx, equation_y_mem_valuationSubring A W h.1 hx⟩

/-- The original torsion coordinates regarded as elements of the valuation ring. -/
def integralTorsionCoordinates (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (P : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) : A × A :=
  (⟨(coordsOrZero P).1, (torsion_coords_mem A W hN P hP).1⟩,
    ⟨(coordsOrZero P).2, (torsion_coords_mem A W hN P hP).2⟩)

/-- The integral half-orbit coordinate set of the actual odd cyclic kernel. -/
def integralOddSummingSet (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (Q : (W.map A.subtype).toAffine.Point)
    (hQ : N • Q = 0) (n : ℕ) : Finset (A × A) :=
  (Finset.Icc 1 n).image fun m => integralTorsionCoordinates A W hN (m • Q)
    (by rw [smul_comm N m, hQ, smul_zero])

/-- The constructed integral half-orbit maps to the actual original half-orbit. -/
theorem integralOddSummingSet_map (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (Q : (W.map A.subtype).toAffine.Point)
    (hQ : N • Q = 0) (n : ℕ) :
    (integralOddSummingSet A W hN Q hQ n).image (Prod.map A.subtype A.subtype) =
      oddOrderSummingSet (W.map A.subtype) Q n := by
  simp only [integralOddSummingSet, oddOrderSummingSet, Finset.image_image,
    Function.comp_def]
  rfl

/-- The literal finite Velu formulas produce an integral model of the actual odd quotient. -/
def integralOddQuotientModel (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (Q : (W.map A.subtype).toAffine.Point)
    (hQ : N • Q = 0) (n : ℕ) : WeierstrassCurve A :=
  veluQuotient W (integralOddSummingSet A W hN Q hQ n)

/-- Inclusion gives precisely the original Velu quotient, with no model hypothesis. -/
theorem integralOddQuotientModel_map (A : ValuationSubring L) (W : WeierstrassCurve A)
    {N : ℕ} (hN : IsUnit (N : A)) (Q : (W.map A.subtype).toAffine.Point)
    (hQ : N • Q = 0) (n : ℕ) :
    (integralOddQuotientModel A W hN Q hQ n).map A.subtype =
      veluQuotient (W.map A.subtype) (oddOrderSummingSet (W.map A.subtype) Q n) := by
  rw [integralOddQuotientModel, veluQuotient_map _ _ _
    ((A.subtype_injective.prodMap A.subtype_injective).injOn), integralOddSummingSet_map]

end
end Dubon2026.SourceEllipticVelu
