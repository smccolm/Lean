import Dubon2026.SourceEllipticDeuringPrescribedInertiaAction
import Dubon2026.SourceEllipticCharTwoSignAction

/-! DUB-17/18 -> characteristic-two genus/Picard -> wild modular orders.
Apply the actual order-twelve sign quotient directly to the constructed
Deuring inertia action. Its kernel fixes every torsion point up to one
uniform sign. Full inertia-image and cyclic-orbit counts are deferred to
their separate census consumers; they are not needed for this order bound. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceEllipticReduction SourceEllipticVariableChange
open SourceEllipticCharTwo SourceEllipticStabilizer
noncomputable section
attribute [local instance] charTwoSignSubgroup_normal

theorem exists_char_two_exceptional_inertia_sign
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) (hNK : (N : K) ≠ 0) :
    let E := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M)
        (π : v.toValuationSubring.inertiaSubgroup (RatFunc K) →*
          (MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) ∧
        Nat.card ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸
          charTwoSignSubgroup) = 12 ∧
        ∀ σ, π σ = 1 →
          (∀ P, galoisTorsionMap E N σ.val.val P = P) ∨
          (∀ P, galoisTorsionMap E N σ.val.val P = -P) := by
  have h3 : (3 : K) ≠ 0 := by rw [three_eq_one]; exact one_ne_zero
  letI : Fact (IsUnit (3 : K)) := ⟨h3.isUnit⟩
  let E := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, _, _, hfix, heq, _⟩ :=
    exists_prescribed_ofJ_inertia_action_of_three_ne_zero K Ω h3 N hNK (ofJ0 K)
  letI := decResidue
  let ρs : v.toValuationSubring.inertiaSubgroup (RatFunc K) →*
      MulAction.stabilizer (VariableChange K) (ofJ0 K) :=
    ρ.codRestrict _ (fun σ => MulAction.mem_stabilizer_iff.mpr (hfix σ))
  let π := charTwoSignProjection.comp ρs
  have hv0 : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
    simpa only [ofJ0_j, map_zero, sub_zero] using hv
  refine ⟨M, hfd, hgal, hcard, v, π, hv0, charTwoSignQuotient_card, ?_⟩
  intro σ hσ
  rcases charTwoSignProjection_kernel_point (ρs σ) hσ with hi | hn
  · left
    intro P
    apply hinj
    have ha := (stabilizerPointEquiv_eq_iff_heq _ _ _ _ _).mp (hi (θ P))
    exact eq_of_heq ((heq σ P).symm.trans ha)
  · right
    intro P
    apply hinj
    rw [map_neg]
    have ha := (stabilizerPointEquiv_eq_iff_heq _ _ _ _ _).mp (hn (θ P))
    exact eq_of_heq ((heq σ P).symm.trans ha)

end
end Dubon2026.SourceEllipticDivisionField
