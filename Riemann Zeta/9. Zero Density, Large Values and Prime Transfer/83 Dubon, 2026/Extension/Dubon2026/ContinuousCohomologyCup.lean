import Dubon2026.ContinuousEquivariantCup
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # The genuine continuous degree-one cup product descends to cohomology -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- The class of the original continuous cup cocycle in the actual continuous
H2 quotient, still viewed as bilinear in original cocycle representatives. -/
def continuousCocycleCupClass :
    continuousRepresentationCocyclesOne A →ₗ[R]
      continuousRepresentationCocyclesOne B →ₗ[R] ContinuousRepresentationH2 C hC :=
  (continuousOneCocycleCupBilinear A B C β hβ hcβ hB).compr₂
    (continuousRepresentationCoboundariesTwo C hC).mkQ

/-- An original left coboundary has zero cup class, witnessed by the actual
continuous cochain `g ↦ β(a, u(g))`. -/
theorem continuousCocycleCupClass_coboundary_left
    (a : A) (u : continuousRepresentationCocyclesOne B) :
    continuousCocycleCupClass A B C β hβ hcβ hB hC
        (continuousRepresentationCoboundaryOne A hA a) u = 0 := by
  change (Submodule.Quotient.mk
    (continuousOneCocycleCup A B C β hβ hcβ hB
      (continuousRepresentationCoboundaryOne A hA a) u) : ContinuousRepresentationH2 C hC) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let w : C(G, C) := ⟨fun g => β a (u.val g),
    hcβ.comp (continuous_const.prodMk u.property)⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (equivariantOneCocycleCup_coboundary_left A B C β hβ a u.val).symm

/-- An original right coboundary has zero cup class, with the negative explicit
cochain proved continuous in the same original topology. -/
theorem continuousCocycleCupClass_coboundary_right
    (f : continuousRepresentationCocyclesOne A) (b : B) :
    continuousCocycleCupClass A B C β hβ hcβ hB hC f
        (continuousRepresentationCoboundaryOne B hB b) = 0 := by
  change (Submodule.Quotient.mk
    (continuousOneCocycleCup A B C β hβ hcβ hB f
      (continuousRepresentationCoboundaryOne B hB b)) : ContinuousRepresentationH2 C hC) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let w : C(G, C) := ⟨fun g => -β (f.val g) (B.ρ g b),
    (hcβ.comp (f.property.prodMk
      (hB.comp (continuous_id.prodMk continuous_const)))).neg⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (equivariantOneCocycleCup_coboundary_right A B C β hβ f.val b).symm

/-- The actual bilinear cup product on continuous H1 classes, obtained by proving
both genuine continuous coboundary submodules vanish in the original H2 quotient. -/
def continuousH1Cup :
    ContinuousRepresentationH1 A hA →ₗ[R]
      ContinuousRepresentationH1 B hB →ₗ[R] ContinuousRepresentationH2 C hC :=
  LinearMap.liftQ₂ (continuousRepresentationCoboundariesOne A hA)
    (continuousRepresentationCoboundariesOne B hB)
    (continuousCocycleCupClass A B C β hβ hcβ hB hC)
    (by
      rintro _ ⟨a, rfl⟩
      apply LinearMap.ext
      intro u
      exact continuousCocycleCupClass_coboundary_left A B C β hβ hcβ hA hB hC a u)
    (by
      rintro _ ⟨b, rfl⟩
      apply LinearMap.ext
      intro f
      exact continuousCocycleCupClass_coboundary_right A B C β hβ hcβ hB hC f b)

/-- The descended pairing evaluates to the actual original continuous cup
cocycle class on every pair of original continuous representatives. -/
theorem continuousH1Cup_mk
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousH1Cup A B C β hβ hcβ hA hB hC
        (Submodule.Quotient.mk f) (Submodule.Quotient.mk u) =
      (Submodule.Quotient.mk (continuousOneCocycleCup A B C β hβ hcβ hB f u) :
        ContinuousRepresentationH2 C hC) := by
  rfl

end
end Dubon2026
