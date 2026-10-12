import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual continuous H2 under a topological group identification

This supplies the group identification needed for the original unit and root H2
corestriction square in cyclotomic descent of the Kummer pairing.
-/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)

/-- Actual continuous two-cocycles are identified by literal pullback along the
given group isomorphism and its continuous inverse. -/
def continuousCocycleTwoGroupEquiv :
    continuousRepresentationCocyclesTwo A ≃+
      continuousRepresentationCocyclesTwo (restrictedCoefficientRep A e.toMonoidHom) where
  toFun := continuousRepresentationCocycleTwoRestriction A e.toMonoidHom he
  invFun c := ⟨⟨fun z => c.val (e.symm z.1, e.symm z.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h t
    have hc := (groupCohomology.mem_cocycles₂_iff _).mp c.val.property
      (e.symm g) (e.symm h) (e.symm t)
    change c.val (e.symm g * e.symm h, e.symm t) + c.val (e.symm g, e.symm h) =
      A.ρ (e (e.symm g)) (c.val (e.symm h, e.symm t)) +
        c.val (e.symm g, e.symm h * e.symm t) at hc
    simpa only [map_mul, e.apply_symm_apply] using hc⟩,
      c.property.comp ((hei.comp continuous_fst).prodMk (hei.comp continuous_snd))⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change c.val (e (e.symm z.1), e (e.symm z.2)) = c.val z
    simp only [e.apply_symm_apply]
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change c.val (e.symm (e z.1), e.symm (e z.2)) = c.val z
    simp only [e.symm_apply_apply]
  map_add' _ _ := rfl

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The actual group pullback maps exactly the original continuous H2
coboundaries, transporting each original one-cochain witness continuously. -/
theorem continuousCocycleTwoGroupEquiv_map_coboundaries :
    (continuousRepresentationCoboundariesTwo A hA).toAddSubgroup.map
      (continuousCocycleTwoGroupEquiv A e he hei).toAddMonoidHom =
        (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A e.toMonoidHom)
          (restrictedCoefficientAction_continuous A e.toMonoidHom he hA)).toAddSubgroup := by
  ext c
  constructor
  · rintro ⟨d, ⟨f, rfl⟩, rfl⟩
    exact ⟨f.comp ⟨e, he⟩, (continuousRepresentationCocycleTwoRestriction_coboundary
      A e.toMonoidHom he hA f).symm⟩
  · rintro ⟨f, rfl⟩
    refine ⟨continuousRepresentationCoboundaryTwo A hA (f.comp ⟨e.symm, hei⟩),
      ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change A.ρ (e z.1) (f (e.symm (e z.2))) - f (e.symm (e z.1 * e z.2)) +
      f (e.symm (e z.1)) = A.ρ (e z.1) (f z.2) - f (z.1 * z.2) + f z.1
    rw [← e.map_mul, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]

/-- Identify the original continuous H2 by its actual group isomorphism,
without changing its coefficient module or quotient relation. -/
def continuousH2GroupEquiv :
    ContinuousRepresentationH2 A hA ≃+
      ContinuousRepresentationH2 (restrictedCoefficientRep A e.toMonoidHom)
        (restrictedCoefficientAction_continuous A e.toMonoidHom he hA) :=
  QuotientAddGroup.congr
    (continuousRepresentationCoboundariesTwo A hA).toAddSubgroup
    (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A e.toMonoidHom)
      (restrictedCoefficientAction_continuous A e.toMonoidHom he hA)).toAddSubgroup
    (continuousCocycleTwoGroupEquiv A e he hei)
    (continuousCocycleTwoGroupEquiv_map_coboundaries A e he hei hA)

/-- The H2 identification is the existing genuine continuous restriction map. -/
theorem continuousH2GroupEquiv_apply (x : ContinuousRepresentationH2 A hA) :
    continuousH2GroupEquiv A e he hei hA x =
      continuousRepresentationH2Restriction A hA e.toMonoidHom he x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
