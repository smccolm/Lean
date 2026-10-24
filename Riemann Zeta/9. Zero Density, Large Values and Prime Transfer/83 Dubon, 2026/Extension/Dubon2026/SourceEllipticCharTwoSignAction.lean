import Dubon2026.SourceEllipticCharTwoSignQuotient
import Dubon2026.SourceEllipticTrivialInertiaTorsion

/-! The actual order-twelve quotient and its uniform point-action kernel.
Every kernel element acts as identity or elliptic negation on all points.
These are the exact group and action inputs for the DUB-17/18 modular
fixing-field construction; the actual good model and inertia map remain
to be supplied in characteristic two. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal

/-- The quotient of the actual exceptional stabilizer by elliptic negation. -/
def charTwoSignProjection : MulAction.stabilizer (VariableChange K) (ofJ0 K) →*
    (MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup :=
  QuotientGroup.mk' charTwoSignSubgroup

theorem charTwoSignProjection_kernel_point [DecidableEq K]
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K))
    (hg : charTwoSignProjection g = 1) :
    (∀ P, stabilizerPointEquiv (ofJ0 K) g.val
      (MulAction.mem_stabilizer_iff.mp g.property) P = P) ∨
    (∀ P, stabilizerPointEquiv (ofJ0 K) g.val
      (MulAction.mem_stabilizer_iff.mp g.property) P = -P) := by
  have hm : g ∈ charTwoSignSubgroup := (QuotientGroup.eq_one_iff g).mp hg
  rcases (mem_charTwoSignSubgroup_iff g).mp hm with h | h
  · subst g
    left
    intro P
    apply (stabilizerPointEquiv_eq_iff_heq _ _ _ _ _).mpr
    exact SourceEllipticReduction.vcInvFun_one_heq _ P
  · subst g
    exact Or.inr charTwoNegation_point

theorem char_two_sign_quotient_data [DecidableEq K] [IsAlgClosed K] :
    Nat.card ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) = 12 ∧
    ∀ g : MulAction.stabilizer (VariableChange K) (ofJ0 K), charTwoSignProjection g = 1 →
      (∀ P, stabilizerPointEquiv (ofJ0 K) g.val
        (MulAction.mem_stabilizer_iff.mp g.property) P = P) ∨
      (∀ P, stabilizerPointEquiv (ofJ0 K) g.val
        (MulAction.mem_stabilizer_iff.mp g.property) P = -P) :=
  ⟨charTwoSignQuotient_card, charTwoSignProjection_kernel_point⟩

end
end Dubon2026.SourceEllipticCharTwo
