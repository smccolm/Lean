import Dubon2026.ContinuousRepresentationRestriction

/-! # Genuine restriction on the actual continuous H1 and H2 quotients -/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

/-- Restrict genuine continuous H1 classes by the actual cocycle map and its
proved preservation of original continuous coboundaries. -/
def continuousRepresentationH1Restriction :
    ContinuousRepresentationH1 A hA →ₗ[R]
      ContinuousRepresentationH1 (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) := by
  have hb : continuousRepresentationCoboundariesOne A hA ≤
      (continuousRepresentationCoboundariesOne (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA)).comap
          (continuousRepresentationCocycleOneRestriction A j hj) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (continuousRepresentationCocycleOneRestriction_coboundary A j hj hA a).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesOne A)
    (M₂ := continuousRepresentationCocyclesOne (restrictedCoefficientRep A j))
    (τ₁₂ := RingHom.id R) (continuousRepresentationCoboundariesOne A hA)
    (continuousRepresentationCoboundariesOne (restrictedCoefficientRep A j)
      (restrictedCoefficientAction_continuous A j hj hA))
    (continuousRepresentationCocycleOneRestriction A j hj) hb

/-- Restrict genuine continuous H2 classes, preserving an actual continuous
one-cochain witness for every original coboundary. -/
def continuousRepresentationH2Restriction :
    ContinuousRepresentationH2 A hA →ₗ[R]
      ContinuousRepresentationH2 (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) := by
  have hb : continuousRepresentationCoboundariesTwo A hA ≤
      (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA)).comap
          (continuousRepresentationCocycleTwoRestriction A j hj) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f.comp ⟨j, hj⟩,
      (continuousRepresentationCocycleTwoRestriction_coboundary A j hj hA f).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesTwo A)
    (M₂ := continuousRepresentationCocyclesTwo (restrictedCoefficientRep A j))
    (τ₁₂ := RingHom.id R) (continuousRepresentationCoboundariesTwo A hA)
    (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A j)
      (restrictedCoefficientAction_continuous A j hj hA))
    (continuousRepresentationCocycleTwoRestriction A j hj) hb

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The actual H1 restriction retains the same original restricted cocycle. -/
theorem continuousRepresentationH1Restriction_mk
    (c : continuousRepresentationCocyclesOne A) :
    continuousRepresentationH1Restriction A hA j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleOneRestriction A j hj c) := by
  rfl

/-- The actual H2 restriction retains the same original restricted two-cocycle. -/
theorem continuousRepresentationH2Restriction_mk
    (c : continuousRepresentationCocyclesTwo A) :
    continuousRepresentationH2Restriction A hA j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction A j hj c) := by
  rfl

end
end Dubon2026
