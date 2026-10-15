import Dubon2026.OriginalClassesModOutsideH1

/-! # Original cyclic class H2 survives quotienting outside units

The finite-stage class-formation coefficient has the same original H2
through the literal quotient map. Existing cyclic periodicity and local
outside-unit vanishing suffice; no general infinite-product theorem is
introduced. The exact field-degree cardinality is inherited from the
already proved original cyclic class theorem.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)

include hu

omit [NumberField K] [IsGalois K L] in
/-- The original outside units have zero H1 for every actual cyclic extension unramified outside S. -/
theorem originalOutsideUnit_cyclic_first_zero :
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) 1) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  apply supportedOutsideUnit_cohomology_zero_of_local K L S hS 1 (by decide)
  intro ω
  exact (supportedOutsideOrbitPoint_first_second_zero_of_unramified K L S hS ω
    (hu ω.out.val ω.out.property)).1

/-- The literal full-class quotient map is an isomorphism on original cyclic H2. -/
theorem originalClassesModOutside_cyclic_H2_isIso :
    IsIso ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have hu1 := originalOutsideUnit_cyclic_first_zero K L S hS hu
  have hu2 := originalOutsideUnit_second_zero_of_unramified K L S hS hu
  have hu3 := cyclic_oddCohomology_zero_of_first (supportedOutsideUnitRep K L S hS)
    g hg hu1 3 (by decide)
  let hX := originalOutsideClassShortComplex_shortExact K L S hS
  haveI : Mono ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) :=
    (groupCohomology.mapShortComplex₂_exact hX 2).mono_g (hu2.eq_zero_of_src _)
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := 2) rfl).epi_f (hu3.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The original cyclic class H2 comparison, with the actual quotient as its forward map. -/
def originalClassesModOutsideCyclicH2Iso :
    groupCohomology (originalIdeleClassRep K L) 2 ≅
      groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2 := by
  let f : groupCohomology (originalIdeleClassRep K L) 2 ⟶
      groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2 :=
    (groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)
  haveI : IsIso f :=
    originalClassesModOutside_cyclic_H2_isIso K L S hS hu
  exact asIso f

/-- The class quotient's actual cyclic H2 is finite and has order equal to the field degree. -/
theorem originalClassesModOutside_cyclic_second_card :
    Finite (groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) =
        Module.finrank K L := by
  let e := (originalClassesModOutsideCyclicH2Iso K L S hS hu).toLinearEquiv.toEquiv
  haveI := (originalIdeleClass_finiteGalois_second_card_dvd K L).1
  exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm.trans
    (original_ideleClass_second_card K L)⟩

end
end Dubon2026
