import Dubon2026.ContinuousRepresentationCohomology

/-! # The original continuous H1 under an additive coefficient identification

This is the degree-one counterpart of the existing H2 bridge. It connects the
integer-linear root/character Kummer inputs to the actual prime-field modules
in DUB-17's local duality argument, retaining original cocycles and boundaries.
-/

namespace Dubon2026
noncomputable section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G]
  (A : Rep.{0} R G) (B : Rep.{0} S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (e : A ≃+ B) (he : Continuous e) (hei : Continuous e.symm)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

/-- The actual additive coefficient identification preserves original
continuous one-cocycles bijectively, even across different coefficient rings. -/
def continuousCocycleOneAdditiveEquiv :
    continuousRepresentationCocyclesOne A ≃+ continuousRepresentationCocyclesOne B where
  toFun c := ⟨⟨fun g => e (c.val g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    simpa only [map_add, heρ] using congrArg e
      ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h)⟩, he.comp c.property⟩
  invFun c := ⟨⟨fun g => e.symm (c.val g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    apply e.injective
    simpa only [map_add, heρ, e.apply_symm_apply] using
      (groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h⟩, hei.comp c.property⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.symm_apply_apply (c.val g)
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.apply_symm_apply (c.val g)
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.map_add (c.val g) (d.val g)

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Original one-coboundaries correspond exactly, with the same original
zero-cochain transported by the actual additive coefficient equivalence. -/
theorem continuousCocycleOneAdditiveEquiv_map_coboundaries :
    (continuousRepresentationCoboundariesOne A hA).toAddSubgroup.map
      (continuousCocycleOneAdditiveEquiv A B e he hei heρ).toAddMonoidHom =
        (continuousRepresentationCoboundariesOne B hB).toAddSubgroup := by
  ext c
  constructor
  · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
    refine ⟨e a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change B.ρ g (e a) - e a = e (A.ρ g a - a)
    rw [map_sub, heρ]
  · rintro ⟨b, rfl⟩
    refine ⟨continuousRepresentationCoboundaryOne A hA (e.symm b), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change e (A.ρ g (e.symm b) - e.symm b) = B.ρ g b - b
    rw [map_sub, heρ, e.apply_symm_apply]

/-- The actual continuous H1 quotients are additively equivalent through
their original coefficient identification, without a common scalar-ring premise. -/
def continuousH1AdditiveCoefficientEquiv :
    ContinuousRepresentationH1 A hA ≃+ ContinuousRepresentationH1 B hB :=
  QuotientAddGroup.congr
    (continuousRepresentationCoboundariesOne A hA).toAddSubgroup
    (continuousRepresentationCoboundariesOne B hB).toAddSubgroup
    (continuousCocycleOneAdditiveEquiv A B e he hei heρ)
    (continuousCocycleOneAdditiveEquiv_map_coboundaries A B e he hei heρ hA hB)

/-- Every actual H1 representative is sent to its literal pointwise coefficient image. -/
theorem continuousH1AdditiveCoefficientEquiv_mk (c : continuousRepresentationCocyclesOne A) :
    continuousH1AdditiveCoefficientEquiv A B e he hei heρ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv A B e he hei heρ c) := rfl

end
end Dubon2026
