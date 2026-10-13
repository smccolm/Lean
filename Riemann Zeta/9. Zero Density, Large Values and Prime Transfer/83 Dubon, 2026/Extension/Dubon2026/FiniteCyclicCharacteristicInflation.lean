import Dubon2026.FiniteCyclicPeriodDetection
import Dubon2026.RepresentationPeriodInflation
import Dubon2026.ContinuousCohomologyRestriction
import Mathlib.Algebra.Module.ZMod
import Mathlib.Topology.Instances.ZMod

/-! # Characteristic-fold cyclic inflation kills original finite-coefficient H2

The exact original cocycle period repeats q times after enlarging the cyclic
stage by q. Its coefficients have characteristic q, so the proved period
detection kills the original H2 class. The next arithmetic edge is to realize
this enlargement in the unramified local quotient, for finite support in
DUB-17's sum-of-local-invariants and global Selmer duality argument.
-/

namespace Dubon2026
noncomputable section

variable (q : ℕ) [Fact q.Prime]
  {G H : Type} [Group G] [CommGroup H] [Fintype H]
  [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace H] [DiscreteTopology H]
  (A : Rep (ZMod q) G) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (φ : H →* G) (g : G) (h : H) (hh : ∀ x, x ∈ Subgroup.zpowers h)
  (hφ : φ h = g) (n : ℕ) (hn : g ^ n = 1) (hnpos : 0 < n)
  (horder : orderOf h = n * q)

include hh hφ hn hnpos horder in
/-- Pulling the actual finite-coefficient H2 class to a cyclic stage whose
generator period is q times longer gives zero, with its original cocycles
and continuous coboundary quotient retained. -/
theorem finiteCyclicCharacteristicH2Inflation_eq_zero
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA φ continuous_of_discreteTopology x = 0 := by
  let B := restrictedCoefficientRep A φ
  have hB := restrictedCoefficientAction_continuous A φ continuous_of_discreteTopology hA
  haveI : Finite B := inferInstanceAs (Finite A)
  have hhsize : 1 < orderOf h := by
    rw [horder]
    exact lt_of_lt_of_le (Fact.out : q.Prime).one_lt (Nat.le_mul_of_pos_left q hnpos)
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    exact finiteCyclicH2_eq_zero_of_period_zero B hB h hh hhsize
      (continuousRepresentationCocycleTwoRestriction A φ continuous_of_discreteTopology c) (by
        change representationCyclicTwoCochainPeriodSum B h (orderOf h)
          (fun z => c.val (φ z.1, φ z.2)) = 0
        rw [horder]
        have he := representationCyclicPeriod_inflation A B φ (LinearMap.id : A →ₗ[ZMod q] B)
          g h hφ n hn q c.val
        refine he.trans ?_
        change q • representationCyclicTwoCochainPeriodSum A g n c.val = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul])

end
end Dubon2026
