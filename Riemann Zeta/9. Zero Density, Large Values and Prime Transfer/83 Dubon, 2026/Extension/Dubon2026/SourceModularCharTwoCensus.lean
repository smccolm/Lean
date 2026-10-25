import Dubon2026.SourceEllipticCharTwoWeightedCensus
import Dubon2026.SourceEllipticCharTwoPlaceClassification

/-! The exact characteristic-two weighted census on actual coefficient
modular places. The full-inertia place classifier, actual sign-quotient action,
orbit marks, native torsion counts and finite-fiber sums discharge all
geometric and counting inputs. This is required for the DUB-17/18 wild
differential contribution and characteristic-two genus/Picard argument. -/
namespace Dubon2026.SourceFunctionField
open WeierstrassCurve SourceCurve SourceEllipticCharTwo SourceEllipticDivisionField
open SourceEllipticStabilizer SourceLevelProjective
noncomputable section

theorem coeff_char_two_order_census_with_closure
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    (∀ v ∈ S, v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3 ∨
      v.ord (jCoeff N K) = 4 ∨ v.ord (jCoeff N K) = 6 ∨ v.ord (jCoeff N K) = 12) ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      3 * (S.filter fun v => v.ord (jCoeff N K) = 3).card +
      2 * (S.filter fun v => v.ord (jCoeff N K) = 6).card = nuTwo N ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      (S.filter fun v => v.ord (jCoeff N K) = 4).card = nuThree N := by
  classical
  letI := charTwoSignSubgroup_normal (K := K)
  obtain ⟨ω, hω⟩ := exists_omega (K := K)
  obtain ⟨f, hsurj, hrel, hord⟩ := exists_char_two_cyclic_modular_place_classification K Ω N hNK
  let c : CyclicSubgroup K N → Place K (modularFunctionFieldCoeff N K) := fun H => (f H).val
  have hc (H T : CyclicSubgroup K N) : c H = c T ↔
      T ∈ MulAction.orbit ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H := by
    change (f H).val = (f T).val ↔ _
    rw [← Subtype.ext_iff, hrel H T]
    exact cyclicStabilizerRelated_iff_sign_orbit (NeZero.ne N) H T
  apply cyclic_order_census ω hω N hNK c S (fun v => v.ord (jCoeff N K))
  · intro H
    exact (hS _).mpr (f H).property
  · intro v hv
    obtain ⟨H, hH⟩ := hsurj ⟨v, (hS v).mp hv⟩
    exact ⟨H, congrArg Subtype.val hH⟩
  · exact hc
  · intro H
    change (f H).val.ord (jCoeff N K) = _
    rw [hord H]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun T =>
      cyclicStabilizerRelated_iff_sign_orbit (NeZero.ne N) H T)

theorem coeff_char_two_order_census
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    [CharP K 2] (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    (∀ v ∈ S, v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3 ∨
      v.ord (jCoeff N K) = 4 ∨ v.ord (jCoeff N K) = 6 ∨ v.ord (jCoeff N K) = 12) ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      3 * (S.filter fun v => v.ord (jCoeff N K) = 3).card +
      2 * (S.filter fun v => v.ord (jCoeff N K) = 6).card = nuTwo N ∧
    (S.filter fun v => v.ord (jCoeff N K) = 1).card +
      (S.filter fun v => v.ord (jCoeff N K) = 4).card = nuThree N := by
  classical
  exact coeff_char_two_order_census_with_closure K (AlgebraicClosure (RatFunc K)) N hNK S hS

end
end Dubon2026.SourceFunctionField
