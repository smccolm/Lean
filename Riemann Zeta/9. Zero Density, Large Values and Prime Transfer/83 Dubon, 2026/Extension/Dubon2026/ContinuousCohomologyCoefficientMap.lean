import Dubon2026.ContinuousEquivariantCoefficientMap

/-! # Actual continuous H1 and H2 maps induced by genuine coefficient homomorphisms -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The genuine continuous equivariant coefficient map induces a map on the
original continuous H1 quotients by preserving the same coboundary witnesses. -/
def continuousCoefficientH1Map :
    ContinuousRepresentationH1 A hA →ₗ[R] ContinuousRepresentationH1 B hB := by
  have hb : continuousRepresentationCoboundariesOne A hA ≤
      (continuousRepresentationCoboundariesOne B hB).comap
        (continuousCoefficientCocycleOneMap A B φ hφ hφρ) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, (continuousCoefficientCocycleOneMap_coboundary A B φ hφ hφρ hA hB a).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesOne A)
    (M₂ := continuousRepresentationCocyclesOne B) (τ₁₂ := RingHom.id R)
    (continuousRepresentationCoboundariesOne A hA)
    (continuousRepresentationCoboundariesOne B hB)
    (continuousCoefficientCocycleOneMap A B φ hφ hφρ) hb

/-- The same coefficient map induces a map on actual continuous H2; every
continuous original one-cochain witness is sent to its genuine coefficient image. -/
def continuousCoefficientH2Map :
    ContinuousRepresentationH2 A hA →ₗ[R] ContinuousRepresentationH2 B hB := by
  have hb : continuousRepresentationCoboundariesTwo A hA ≤
      (continuousRepresentationCoboundariesTwo B hB).comap
        (continuousCoefficientCocycleTwoMap A B φ hφ hφρ) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨fun g => φ (f g), hφ.comp f.continuous⟩,
      (continuousCoefficientCocycleTwoMap_coboundary A B φ hφ hφρ hA hB f).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesTwo A)
    (M₂ := continuousRepresentationCocyclesTwo B) (τ₁₂ := RingHom.id R)
    (continuousRepresentationCoboundariesTwo A hA)
    (continuousRepresentationCoboundariesTwo B hB)
    (continuousCoefficientCocycleTwoMap A B φ hφ hφρ) hb

omit [IsTopologicalGroup G] in
/-- The original H1 coefficient map uses the exact pointwise image cocycle. -/
theorem continuousCoefficientH1Map_mk (c : continuousRepresentationCocyclesOne A) :
    continuousCoefficientH1Map A B φ hφ hφρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleOneMap A B φ hφ hφρ c) := by
  rfl

/-- The original H2 coefficient map uses the same jointly continuous image cocycle. -/
theorem continuousCoefficientH2Map_mk (c : continuousRepresentationCocyclesTwo A) :
    continuousCoefficientH2Map A B φ hφ hφρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap A B φ hφ hφρ c) := by
  rfl

end
end Dubon2026
