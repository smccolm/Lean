import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual continuous H1 under a topological group identification

This transports the original root coefficients between the genuine cyclotomic
field Galois group and its fixing subgroup, as needed for Kummer pairing descent.
Both directions retain actual continuous cocycles and original boundaries.
-/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)

/-- Pullback along the actual group identification is bijective on the original
continuous one-cocycles, with inverse given by literal inverse pullback. -/
def continuousCocycleOneGroupEquiv :
    continuousRepresentationCocyclesOne A ≃+
      continuousRepresentationCocyclesOne (restrictedCoefficientRep A e.toMonoidHom) where
  toFun := continuousRepresentationCocycleOneRestriction A e.toMonoidHom he
  invFun c := ⟨⟨fun g => c.val (e.symm g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.val.property
      (e.symm g) (e.symm h)
    change c.val (e.symm g * e.symm h) =
      A.ρ (e (e.symm g)) (c.val (e.symm h)) + c.val (e.symm g) at hc
    simpa only [map_mul, e.apply_symm_apply] using hc⟩, c.property.comp hei⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact congrArg c.val (e.apply_symm_apply g)
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext h
    exact congrArg c.val (e.symm_apply_apply h)
  map_add' _ _ := rfl

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The actual one-cocycle identification maps precisely the original
coboundaries, with the same degree-zero coefficient witness. -/
theorem continuousCocycleOneGroupEquiv_map_coboundaries :
    (continuousRepresentationCoboundariesOne A hA).toAddSubgroup.map
      (continuousCocycleOneGroupEquiv A e he hei).toAddMonoidHom =
        (continuousRepresentationCoboundariesOne (restrictedCoefficientRep A e.toMonoidHom)
          (restrictedCoefficientAction_continuous A e.toMonoidHom he hA)).toAddSubgroup := by
  ext c
  constructor
  · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (continuousRepresentationCocycleOneRestriction_coboundary
      A e.toMonoidHom he hA a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨continuousRepresentationCoboundaryOne A hA a, ⟨a, rfl⟩,
      continuousRepresentationCocycleOneRestriction_coboundary A e.toMonoidHom he hA a⟩

/-- Original continuous H1 is identified by the actual group isomorphism,
preserving the original coefficient module and its restricted action. -/
def continuousH1GroupEquiv :
    ContinuousRepresentationH1 A hA ≃+
      ContinuousRepresentationH1 (restrictedCoefficientRep A e.toMonoidHom)
        (restrictedCoefficientAction_continuous A e.toMonoidHom he hA) :=
  QuotientAddGroup.congr
    (continuousRepresentationCoboundariesOne A hA).toAddSubgroup
    (continuousRepresentationCoboundariesOne (restrictedCoefficientRep A e.toMonoidHom)
      (restrictedCoefficientAction_continuous A e.toMonoidHom he hA)).toAddSubgroup
    (continuousCocycleOneGroupEquiv A e he hei)
    (continuousCocycleOneGroupEquiv_map_coboundaries A e he hei hA)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The actual H1 equivalence is precisely the existing continuous restriction
map on original classes, so its inverse introduces no replacement cohomology. -/
theorem continuousH1GroupEquiv_apply (x : ContinuousRepresentationH1 A hA) :
    continuousH1GroupEquiv A e he hei hA x =
      continuousRepresentationH1Restriction A hA e.toMonoidHom he x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
