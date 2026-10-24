import Dubon2026.SourceEllipticCyclicPlaceFiberClassification
import Dubon2026.SourceEllipticExceptionalCyclicRelation
import Dubon2026.SourceEllipticExceptionalOrbitCounts
import Dubon2026.SourceEllipticExceptionalJValues
import Dubon2026.SourceCyclicOrbitClassification

/-! DUB-17/18 -> modular good reduction -> reverse genus. The actual
modular coefficient-field place fibers at j=1728 and j=0 have the source
Dedekind-psi/nuTwo/nuThree cardinalities in characteristic at least five.
The actual specialization classifier, full stabilizer relation, orbit
counts and elliptic fixed-subgroup census are consumed without a census
or orbit-comparison hypothesis. The wild characteristics remain separate. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceCurve SourceFunctionField SourceLevelProjective
open SourceFunctionField.CoefficientPresentation SourceEllipticStabilizer SourceManin
noncomputable section
variable (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
variable [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
variable [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
variable (p : ℕ) [CharP K p] (hp : 5 ≤ p)
variable (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
include Ω p hp hNK

theorem quartic_modular_place_fiber_count :
    2 * Nat.card {v : Place K (modularFunctionFieldCoeff N K) //
      0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 1728)} =
      dedekindPsi N + nuTwo N := by
  obtain ⟨h2u, h3u⟩ := SourceEllipticReduction.isUnit_two_three_of_five_le K K p hp
  have h2 : (2 : K) ≠ 0 := h2u.ne_zero
  have h3 : (3 : K) ≠ 0 := h3u.ne_zero
  haveI : (EA (1 : K)).IsElliptic := isElliptic_EA 1 one_ne_zero h2
  obtain ⟨u, hu⟩ := exists_quartic_scaling (K := K)
  let τ := cyclicSubgroupEquiv N
    (stabilizerPointEquiv (EA (1 : K)) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu 1))
  obtain ⟨f, hf, hrel, _horder⟩ :=
    SourceEllipticDivisionField.exists_cyclic_modular_place_fiber_classification
      K Ω p hp N hNK (EA (1 : K))
  have he (S T) : f S = f T ↔ orbQ τ S = orbQ τ T :=
    (hrel S T).trans ((quartic_cyclic_relation 1 one_ne_zero h2 h3 u hu N
      (NeZero.ne N) S T).trans (orbQ_eq_iff_two τ
        (cyclicSubgroupEquiv_square N _ (quartic_action_square 1 u hu)) S T).symm)
  have hc := quartic_cyclic_orbit_count 1 one_ne_zero u hu h2 N hNK
  change 2 * Nat.card (Orb τ) = _ at hc
  rw [← classifier_card_eq_orbits τ f hf he] at hc
  simpa only [quartic_j] using hc

theorem cubic_modular_place_fiber_count :
    3 * Nat.card {v : Place K (modularFunctionFieldCoeff N K) //
      0 < v.ord (jCoeff N K)} = dedekindPsi N + 2 * nuThree N := by
  obtain ⟨h2u, h3u⟩ := SourceEllipticReduction.isUnit_two_three_of_five_le K K p hp
  have h2 : (2 : K) ≠ 0 := h2u.ne_zero
  have h3 : (3 : K) ≠ 0 := h3u.ne_zero
  haveI : (EB (1 : K)).IsElliptic := isElliptic_EB 1 one_ne_zero h2 h3
  obtain ⟨u, hu, hu1⟩ := exists_cubic_scaling h3
  let τ := cyclicSubgroupEquiv N
    (stabilizerPointEquiv (EB (1 : K)) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu 1))
  obtain ⟨f, hf, hrel, _horder⟩ :=
    SourceEllipticDivisionField.exists_cyclic_modular_place_fiber_classification
      K Ω p hp N hNK (EB (1 : K))
  have he (S T) : f S = f T ↔ orbQ τ S = orbQ τ T :=
    (hrel S T).trans ((cubic_cyclic_relation 1 one_ne_zero h2 h3 u hu hu1 N
      (NeZero.ne N) S T).trans (orbQ_eq_iff_three τ
        (cyclicSubgroupEquiv_cube N _ (cubic_action_relation 1 one_ne_zero u hu hu1 h2)) S T).symm)
  have hc := cubic_cyclic_orbit_count 1 one_ne_zero u hu hu1 h2 N hNK
  change 3 * Nat.card (Orb τ) = _ at hc
  rw [← classifier_card_eq_orbits τ f hf he] at hc
  simpa only [cubic_j, map_zero, sub_zero] using hc

end
end Dubon2026.SourceEllipticExceptional
