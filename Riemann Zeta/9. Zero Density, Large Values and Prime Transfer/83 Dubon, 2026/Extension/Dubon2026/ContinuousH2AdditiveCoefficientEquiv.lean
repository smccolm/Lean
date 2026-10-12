import Dubon2026.ContinuousRepresentationCohomology

/-! # Actual H2 under an additive equivariant coefficient identification

This is the coefficient-ring bridge needed to identify the cyclotomic prime-field
cup target with the original integer-linear root-of-unity cohomology. It retains
the same continuous cocycles and continuous coboundary witnesses.
-/

namespace Dubon2026
noncomputable section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) (B : Rep S G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (e : A ≃+ B) (he : Continuous e) (hei : Continuous e.symm)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

/-- An actual continuous additive coefficient identification carries the literal
two-cocycles bijectively, even when their coefficient rings differ. -/
def continuousCocycleTwoAdditiveEquiv :
    continuousRepresentationCocyclesTwo A ≃+ continuousRepresentationCocyclesTwo B where
  toFun c := ⟨⟨fun z => e (c.val z), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h t
    have hc := (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g h t
    change e (c.val (g * h, t)) + e (c.val (g, h)) =
      B.ρ g (e (c.val (h, t))) + e (c.val (g, h * t))
    simpa only [map_add, heρ] using congrArg e hc⟩, he.comp c.property⟩
  invFun c := ⟨⟨fun z => e.symm (c.val z), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h t
    apply e.injective
    simpa only [map_add, heρ, e.apply_symm_apply] using
      (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g h t⟩,
        hei.comp c.property⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact e.symm_apply_apply (c.val z)
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact e.apply_symm_apply (c.val z)
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact e.map_add (c.val z) (d.val z)

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The additive coefficient identification maps precisely the actual continuous
coboundaries; the reverse direction transports the original continuous witness. -/
theorem continuousCocycleTwoAdditiveEquiv_map_coboundaries :
    (continuousRepresentationCoboundariesTwo A hA).toAddSubgroup.map
      (continuousCocycleTwoAdditiveEquiv A B e he hei heρ).toAddMonoidHom =
        (continuousRepresentationCoboundariesTwo B hB).toAddSubgroup := by
  ext c
  constructor
  · rintro ⟨d, ⟨f, rfl⟩, rfl⟩
    refine ⟨⟨fun g => e (f g), he.comp f.continuous⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change B.ρ z.1 (e (f z.2)) - e (f (z.1 * z.2)) + e (f z.1) =
      e (A.ρ z.1 (f z.2) - f (z.1 * z.2) + f z.1)
    rw [map_add, map_sub, heρ]
  · rintro ⟨f, rfl⟩
    refine ⟨continuousRepresentationCoboundaryTwo A hA
      ⟨fun g => e.symm (f g), hei.comp f.continuous⟩, ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change e (A.ρ z.1 (e.symm (f z.2)) - e.symm (f (z.1 * z.2)) +
      e.symm (f z.1)) = B.ρ z.1 (f z.2) - f (z.1 * z.2) + f z.1
    rw [map_add, map_sub, heρ, e.apply_symm_apply, e.apply_symm_apply,
      e.apply_symm_apply]

/-- The original continuous H2 groups are additively identified by the actual
coefficient map, without an artificial common coefficient-ring assumption. -/
def continuousH2AdditiveCoefficientEquiv :
    ContinuousRepresentationH2 A hA ≃+ ContinuousRepresentationH2 B hB :=
  QuotientAddGroup.congr
    (continuousRepresentationCoboundariesTwo A hA).toAddSubgroup
    (continuousRepresentationCoboundariesTwo B hB).toAddSubgroup
    (continuousCocycleTwoAdditiveEquiv A B e he hei heρ)
    (continuousCocycleTwoAdditiveEquiv_map_coboundaries A B e he hei heρ hA hB)

/-- The H2 identification sends every original cocycle to its literal pointwise
coefficient image. -/
theorem continuousH2AdditiveCoefficientEquiv_mk (c : continuousRepresentationCocyclesTwo A) :
    continuousH2AdditiveCoefficientEquiv A B e he hei heρ hA hB
      (Submodule.Quotient.mk c) =
        Submodule.Quotient.mk (continuousCocycleTwoAdditiveEquiv A B e he hei heρ c) := by
  rfl

end
end Dubon2026
