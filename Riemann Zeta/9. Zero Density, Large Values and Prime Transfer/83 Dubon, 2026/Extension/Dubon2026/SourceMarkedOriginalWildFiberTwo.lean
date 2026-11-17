import Dubon2026.SourceMarkedOriginalResidueFiberTwo
import Dubon2026.SourceMarkedCharTwoSignAction
import Dubon2026.SourceMarkedSignFiberSymmetries
import Dubon2026.SourceMarkedOrderTwelveFiberBound

/-! DUB-17/18 -> reverse original genus -> characteristic-two fiber.
The actual exceptional sign quotient has order twelve and its quartic
and cubic elements have no fixed primitive sign classes for N greater
than three. Native orbit marks and the constructed original residue chart
give the required factor twelve, without a new group classification. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup SourceCurve SourceEllipticStabilizer
open SourceEllipticCharTwo MarkedTorsion GammaOne GammaOne.ToricCoordinates IntegralDiamond
open scoped MarkedTorsion
attribute [local instance] charTwoSignSubgroup_normal
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
    [CharP (IsLocalRing.ResidueField A) 2]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem original_twelve_mul_card_j_zero_fiber_le_of_char_two
    (h2N : ¬ 2 ∣ N) (hN : 3 < N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk) :
    12 * Nat.card {v : Place kk F // 0 < v.ord x} ≤ (plusMinus (Gamma1 N)).index := by
  classical
  letI := valuation_residue_isAlgClosed A
  letI : Fact (IsUnit (3 : kk)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
  have hNK : (N : kk) ≠ 0 := fun h => h2N ((CharP.cast_eq_zero_iff kk 2 N).mp h)
  obtain ⟨ω, hω⟩ := exists_omega (K := kk)
  obtain ⟨g, hg, hneg, hcurve⟩ := exists_original_residue_marked_fiber_of_char_two
    A N h2N (by omega) x hx
  let α := stabilizerPointHom (ofJ0 kk) (quarticStabilizer ω hω)
  obtain ⟨f, hf, hpair, _⟩ := exists_signClass_fiber_factor N g hg hneg α
    (hcurve (quarticStabilizer ω hω).val
      (MulAction.mem_stabilizer_iff.mp (quarticStabilizer ω hω).property))
  let G := (MulAction.stabilizer (VariableChange kk) (ofJ0 kk)) ⧸ charTwoSignSubgroup
  have hG : Nat.card G = 12 := charTwoSignQuotient_card
  letI : Finite G := Nat.finite_of_card_ne_zero (hG.trans_ne (by decide))
  have hinv (σ : G) (s : SignClasses (ofJ0 kk).toAffine.Point N) : f (σ • s) = f s := by
    induction σ using QuotientGroup.induction_on with
    | H σ =>
      change f (charTwoSignProjection σ • s) = f s
      rw [charTwo_signProjection_marked_smul]
      exact signClass_fiber_factor_invariant N g f hpair (stabilizerPointHom (ofJ0 kk) σ)
        (hcurve σ.val (MulAction.mem_stabilizer_iff.mp σ.property)) s
  have hc : Nat.card (SignClasses (ofJ0 kk).toAffine.Point N) =
      (plusMinus (Gamma1 N)).index := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      using actual_point_signClasses_card (ofJ0 kk) N hNK
  letI : Finite (SignClasses (ofJ0 kk).toAffine.Point N) :=
    Nat.finite_of_card_ne_zero (hc.trans_ne Subgroup.FiniteIndex.index_ne_zero)
  have hbound := twelve_mul_card_fiber_le_of_free_marks hG charTwoSignQuotient_square_or_cube
    (charTwoSignProjection (quarticStabilizer ω hω))
    (charTwoSignProjection (cubicStabilizer ω hω))
    (signProjection_quartic_ne_one ω hω) (signProjection_quartic_square ω hω)
    (signProjection_cubic_ne_one ω hω) (signProjection_cubic_cube ω hω)
    (charTwo_quartic_marked_ne_self N hN ω hω) (charTwo_cubic_marked_ne_self N hN ω hω)
    f hf hinv
  rwa [hc] at hbound

end
end Dubon2026.SourceFunctionField.MarkedChart
