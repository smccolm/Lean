import Dubon2026.CosetTraceDifferential

/-! # Continuous original cochains and cocycles under the genuine finite coset trace -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

include hA hS

/-- The actual finite coset sum preserves continuity of original one-cochains. -/
theorem cosetTraceOne_continuous (f : S → A) (hf : Continuous f) :
    Continuous (cosetTraceOne A S f) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  exact hA.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk
    (hf.comp ((cosetTransition_continuous S hS).comp (continuous_id.prodMk continuous_const))))

/-- Jointly continuous two-cochains retain their actual continuity after
the genuine finite coset trace. -/
theorem cosetTraceTwo_continuous (c : S × S → A) (hc : Continuous c) :
    Continuous (cosetTraceTwo A S c) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  exact hA.comp ((hout.comp (continuous_fst.smul (continuous_snd.smul continuous_const))).prodMk
    (hc.comp (((cosetTransition_continuous S hS).comp
      (continuous_fst.prodMk (continuous_snd.smul continuous_const))).prodMk
      ((cosetTransition_continuous S hS).comp (continuous_snd.prodMk continuous_const)))))

variable [TopologicalSpace R] [ContinuousSMul R A]

/-- Genuine finite coset trace on the original continuous one-cochains. -/
def continuousCosetTraceOne : C(S, A) →ₗ[R] C(G, A) where
  toFun f := ⟨cosetTraceOne A S f, cosetTraceOne_continuous A hA S hS f f.continuous⟩
  map_add' f j := by
    apply ContinuousMap.coe_injective
    exact map_add (cosetTraceOne A S) (f : S → A) (j : S → A)
  map_smul' r f := by
    apply ContinuousMap.coe_injective
    exact map_smul (cosetTraceOne A S) r (f : S → A)

/-- Genuine finite coset trace on the original continuous two-cocycles. -/
def continuousCosetTraceTwo :
    continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype) →ₗ[R]
      continuousRepresentationCocyclesTwo A where
  toFun c := ⟨⟨cosetTraceTwo A S c.val, cosetTraceTwo_mem_cocycles A S c.val⟩,
    cosetTraceTwo_continuous A hA S hS c.val c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (cosetTraceTwo A S) (c.val : S × S → A) (d.val : S × S → A)
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (cosetTraceTwo A S) r (c.val : S × S → A)

/-- Every original continuous coboundary is sent to the coboundary of its
actual continuous traced cochain. -/
theorem continuousCosetTraceTwo_coboundary (f : C(S, A)) :
    continuousCosetTraceTwo A hA S hS
      (continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) f) =
      continuousRepresentationCoboundaryTwo A hA (continuousCosetTraceOne A hA S hS f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact cosetTraceTwo_differential A S (f : S → A)

end
end Dubon2026
