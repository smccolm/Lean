import Dubon2026.ContinuousCosetOrbitCocycles

/-! # The continuous Mackey formula for original degree-two transfer

The proof reindexes the original finite cosets and uses an explicit
continuous coboundary. This removes the cohomological transfer identity
premise from DUB-17's proposed global-to-local invariant comparison;
identification of the orbit terms with arithmetic completions remains.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R D G : Type} [CommRing R] [Group D] [Group G]
  [TopologicalSpace R] [TopologicalSpace D] [TopologicalSpace G]
  [IsTopologicalGroup D] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (φ : D →* G) (hφ : Continuous φ) (S : Subgroup G) (hS : IsOpen (S : Set G))
  [Fintype (G ⧸ S)] [Fintype (cosetOrbitIndex φ S)]
  [∀ ω : cosetOrbitIndex φ S, Fintype (D ⧸ cosetOrbitStabilizer φ S ω.out)]

/-- Restriction of the actual continuous corestriction equals the sum of
the actual stabilizer corestrictions of the original conjugated cocycles. -/
theorem continuousRepresentationH2Corestriction_mackey
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationH2Restriction A hA φ hφ
        (continuousRepresentationH2Corestriction A hA S hS (Submodule.Quotient.mk c)) =
      ∑ ω : cosetOrbitIndex φ S,
        continuousRepresentationH2Corestriction (restrictedCoefficientRep A φ)
          (restrictedCoefficientAction_continuous A φ hφ hA)
          (cosetOrbitStabilizer φ S ω.out) (cosetOrbitStabilizer_isOpen φ hφ S hS ω.out)
          (Submodule.Quotient.mk (continuousCosetOrbitCocycle A hA φ hφ S ω.out c)) := by
  rw [continuousRepresentationH2Corestriction_mk, continuousRepresentationH2Restriction_mk]
  simp_rw [continuousRepresentationH2Corestriction_mk]
  let t (ω : cosetOrbitIndex φ S) :=
    continuousCosetTraceTwo (restrictedCoefficientRep A φ)
      (restrictedCoefficientAction_continuous A φ hφ hA)
      (cosetOrbitStabilizer φ S ω.out) (cosetOrbitStabilizer_isOpen φ hφ S hS ω.out)
      (continuousCosetOrbitCocycle A hA φ hφ S ω.out c)
  have hs : (∑ ω : cosetOrbitIndex φ S, (Submodule.Quotient.mk (t ω) :
      ContinuousRepresentationH2 (restrictedCoefficientRep A φ)
        (restrictedCoefficientAction_continuous A φ hφ hA))) =
        Submodule.Quotient.mk (∑ ω : cosetOrbitIndex φ S, t ω) :=
    (map_sum (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A φ)
      (restrictedCoefficientAction_continuous A φ hφ hA)).mkQ t Finset.univ).symm
  change _ = ∑ ω : cosetOrbitIndex φ S, Submodule.Quotient.mk (t ω)
  rw [hs]
  symm
  apply (continuousRepresentationH2_eq_iff (restrictedCoefficientRep A φ)
    (restrictedCoefficientAction_continuous A φ hφ hA) _ _).mpr
  refine ⟨⟨fun d => cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c.val (φ d),
    (cosetRepresentativeHomotopy_continuous A hA S hS (cosetOrbitRepresentativeChange φ S) c).comp hφ⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have ht := (cosetOrbit_trace_restriction_coboundary A φ S c.val).symm
  simp only [Submodule.coe_sub, Submodule.coe_sum]
  funext z
  rw [Pi.sub_apply, Finset.sum_apply]
  exact congrFun ht z

end
end Dubon2026
