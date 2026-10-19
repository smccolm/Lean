import Dubon2026.ContinuousUnramifiedFiniteInflation

/-! The reverse comparison needed for DUB-17's unramified local dimension:
the literal inflation image of an open quotient consists of original
continuous classes trivial on every subgroup killed by that quotient.
This retains the original representation and its topology. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [TopologicalSpace R] [IsTopologicalAddGroup A] [ContinuousSMul R A] in
/-- An original cocycle inflated from an open quotient is continuous,
even when its coefficients are the full subgroup-invariant space. -/
theorem firstInflation_cocycle_continuous (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) (c : groupCohomology.cocycles₁ (A.quotientToInvariants N)) :
    Continuous (fun g => groupCohomology.mapCocycles₁ (QuotientGroup.mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) c g) := by
  letI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  change Continuous (fun g => (c (QuotientGroup.mk g)).val)
  exact (continuous_subtype_val.comp (continuous_of_discreteTopology
    (f := fun q => c q))).comp continuous_quot_mk

/-- Every literal open-quotient inflation class is the image of an
original continuous class whose original inertia restriction is zero. -/
theorem firstInflation_range_le_continuous_unramified_image
    (I N : Subgroup G) [N.Normal] (hIN : I ≤ N) (hN : IsOpen (N : Set G)) :
    (groupCohomology.H1InfRes A N).f.hom.range ≤
      ((continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker.map
        (continuousH1ToAlgebraic A hA)) := by
  rintro _ ⟨z, rfl⟩
  change groupCohomology.H1 (A.quotientToInvariants N) at z
  induction z using groupCohomology.H1_induction_on with
  | h c =>
    have hc := firstInflation_cocycle_continuous A N hN c
    let d₀ : groupCohomology.cocycles₁ A :=
      groupCohomology.mapCocycles₁ (QuotientGroup.mk' N)
        (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) c
    let d : continuousRepresentationCocyclesOne A :=
      ⟨d₀, hc⟩
    refine ⟨Submodule.Quotient.mk d, ?_, ?_⟩
    · change continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val
        (Submodule.Quotient.mk d) = 0
      rw [continuousRepresentationH1Restriction_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext i
      change A.ρ i.val 0 - 0 = (c (QuotientGroup.mk i.val)).val
      rw [map_zero, sub_zero, (QuotientGroup.eq_one_iff _).mpr (hIN i.property),
        groupCohomology.cocycles₁_map_one]
      rfl
    · change groupCohomology.H1π A d.val =
        groupCohomology.map (QuotientGroup.mk' N)
          (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) 1
            (groupCohomology.H1π (A.quotientToInvariants N) c)
      exact (groupCohomology.H1π_comp_map_apply _ _ c).symm

end
end Dubon2026
