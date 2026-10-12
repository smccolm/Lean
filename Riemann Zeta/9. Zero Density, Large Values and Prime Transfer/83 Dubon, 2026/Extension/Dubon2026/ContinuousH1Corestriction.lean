import Dubon2026.CosetTraceOneCocycles
import Dubon2026.ContinuousCosetTrace

/-! # Actual continuous H1 corestriction through the original finite coset trace

This is required for the cyclotomic descent of the Kummer pairing. Both original
cocycle continuity and the original coboundary relation are preserved explicitly.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

/-- The existing literal coset trace sends actual continuous subgroup
one-cocycles linearly to actual continuous original group one-cocycles. -/
def continuousCosetTraceOneCocycle :
    continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype) →ₗ[R]
      continuousRepresentationCocyclesOne A where
  toFun c := ⟨⟨cosetTraceOne A S c.val, cosetTraceOne_mem_cocycles A S c.val⟩,
    cosetTraceOne_continuous A hA S hS c.val c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (cosetTraceOne A S) (c.val : S → A) (d.val : S → A)
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (cosetTraceOne A S) r (c.val : S → A)

/-- The actual continuous degree-one trace preserves the original
coboundary, with the explicit original zero-cochain trace witness. -/
theorem continuousCosetTraceOneCocycle_coboundary (a : A) :
    continuousCosetTraceOneCocycle A hA S hS
      (continuousRepresentationCoboundaryOne (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) a) =
      continuousRepresentationCoboundaryOne A hA (cosetTraceZero A S a) := by
  apply Subtype.ext
  apply Subtype.ext
  exact cosetTraceOne_coboundary A S a

/-- Corestriction on the original continuous H1 quotients, induced by the
same original finite coset sum and proved preservation of coboundaries. -/
def continuousRepresentationH1Corestriction :
    ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) →ₗ[R]
      ContinuousRepresentationH1 A hA := by
  have hb : continuousRepresentationCoboundariesOne (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≤
      (continuousRepresentationCoboundariesOne A hA).comap
        (continuousCosetTraceOneCocycle A hA S hS) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨cosetTraceZero A S a, (continuousCosetTraceOneCocycle_coboundary A hA S hS a).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype))
    (M₂ := continuousRepresentationCocyclesOne A) (τ₁₂ := RingHom.id R)
    (continuousRepresentationCoboundariesOne (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (continuousRepresentationCoboundariesOne A hA) (continuousCosetTraceOneCocycle A hA S hS) hb

/-- The genuine H1 corestriction has the literal original finite trace
cocycle as its representative. -/
theorem continuousRepresentationH1Corestriction_mk
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationH1Corestriction A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCosetTraceOneCocycle A hA S hS c) := by
  rfl

end
end Dubon2026
