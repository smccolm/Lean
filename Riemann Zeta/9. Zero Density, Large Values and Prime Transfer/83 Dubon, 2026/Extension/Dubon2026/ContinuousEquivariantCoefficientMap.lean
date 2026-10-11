import Dubon2026.ContinuousRepresentationCohomology

/-! # Genuine coefficient maps on the original continuous cocycles and coboundaries -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (φ : A →ₗ[R] B) (hφ : Continuous φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

/-- Compose the original continuous one-cocycle with the actual continuous
equivariant coefficient map, retaining its original pointwise function. -/
def continuousCoefficientCocycleOneMap :
    continuousRepresentationCocyclesOne A →ₗ[R] continuousRepresentationCocyclesOne B where
  toFun c := ⟨⟨fun g => φ (c.val g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have hc : c.val (g * h) = A.ρ g (c.val h) + c.val g :=
      (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h
    change φ (c.val (g * h)) = B.ρ g (φ (c.val h)) + φ (c.val g)
    rw [hc, map_add, hφρ]⟩, hφ.comp c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact map_add φ (c.val g) (d.val g)
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact map_smul φ r (c.val g)

/-- Compose the original jointly continuous two-cocycle with the same actual
coefficient map. Its original three-variable cocycle identity is preserved. -/
def continuousCoefficientCocycleTwoMap :
    continuousRepresentationCocyclesTwo A →ₗ[R] continuousRepresentationCocyclesTwo B where
  toFun c := ⟨⟨fun z => φ (c.val z), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h t
    have hc : c.val (g * h, t) + c.val (g, h) =
        A.ρ g (c.val (h, t)) + c.val (g, h * t) :=
      (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g h t
    change φ (c.val (g * h, t)) + φ (c.val (g, h)) =
      B.ρ g (φ (c.val (h, t))) + φ (c.val (g, h * t))
    simpa only [map_add, hφρ] using congrArg φ hc⟩, hφ.comp c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact map_add φ (c.val z) (d.val z)
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact map_smul φ r (c.val z)

omit [IsTopologicalGroup G] in
/-- The actual coefficient map preserves the literal one-cocycle evaluation. -/
theorem continuousCoefficientCocycleOneMap_apply
    (c : continuousRepresentationCocyclesOne A) (g : G) :
    (continuousCoefficientCocycleOneMap A B φ hφ hφρ c).val g = φ (c.val g) := by
  rfl

omit [IsTopologicalGroup G] in
/-- The actual coefficient map preserves the literal two-cocycle evaluation. -/
theorem continuousCoefficientCocycleTwoMap_apply
    (c : continuousRepresentationCocyclesTwo A) (g : G × G) :
    (continuousCoefficientCocycleTwoMap A B φ hφ hφρ c).val g = φ (c.val g) := by
  rfl

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- A genuine degree-zero coboundary maps to the coboundary of the actual
image coefficient, using the original differential and action equivariance. -/
theorem continuousCoefficientCocycleOneMap_coboundary (a : A) :
    continuousCoefficientCocycleOneMap A B φ hφ hφρ
      (continuousRepresentationCoboundaryOne A hA a) =
        continuousRepresentationCoboundaryOne B hB (φ a) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change φ (A.ρ g a - a) = B.ρ g (φ a) - φ a
  rw [map_sub, hφρ]

/-- A genuine continuous one-cochain witness maps to its actual continuous
coefficient image, preserving the original degree-one coboundary exactly. -/
theorem continuousCoefficientCocycleTwoMap_coboundary (f : C(G, A)) :
    continuousCoefficientCocycleTwoMap A B φ hφ hφρ
      (continuousRepresentationCoboundaryTwo A hA f) =
        continuousRepresentationCoboundaryTwo B hB
          ⟨fun g => φ (f g), hφ.comp f.continuous⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change φ (A.ρ z.1 (f z.2) - f (z.1 * z.2) + f z.1) =
    B.ρ z.1 (φ (f z.2)) - φ (f (z.1 * z.2)) + φ (f z.1)
  rw [map_add, map_sub, hφρ]

end
end Dubon2026
