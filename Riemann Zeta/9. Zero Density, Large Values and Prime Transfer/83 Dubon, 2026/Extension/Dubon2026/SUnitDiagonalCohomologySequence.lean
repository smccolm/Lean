import Dubon2026.SUnitExtendedLatticeRepresentation

/-! # The original split logarithmic-lattice and integer-diagonal sequence

The actual product representation gives a split short exact sequence
with the original logarithmic lattice and trivial integer diagonal.
The literal projection is a retraction, so original lattice cohomology
injects into original product cohomology. This is the required finiteness
descent from the extended lattice for DUB-17's diagonal Herbrand factor.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual logarithmic-lattice inclusion and integer projection form the original diagonal sequence. -/
def sUnitDiagonalShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := sUnitLogLatticeRep K L S hS
  X₂ := sUnitLogProductRep K L S hS
  X₃ := Rep.trivial ℤ Gal(L/K) ℤ
  f := Rep.ofHom ⟨LinearMap.inl ℤ _ ℤ, by intro σ; rfl⟩
  g := Rep.ofHom ⟨LinearMap.snd ℤ _ ℤ, by intro σ; rfl⟩
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl

/-- The original diagonal representation sequence is short exact. -/
theorem sUnitDiagonalShortComplex_shortExact : (sUnitDiagonalShortComplex K L S hS).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun _ _ h => congrArg Prod.fst h)
    epi_g := (Rep.epi_iff_surjective _).mpr (fun n => ⟨(0, n), rfl⟩) }
  apply ((sUnitDiagonalShortComplex K L S hS).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  change (∃ y, (y, (0 : ℤ)) = x) ↔ x.2 = 0
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩

/-- The actual first-coordinate projection to the original logarithmic-lattice representation. -/
def sUnitDiagonalRetraction : sUnitLogProductRep K L S hS ⟶ sUnitLogLatticeRep K L S hS :=
  Rep.ofHom ⟨LinearMap.fst ℤ (sUnitFullLogLattice L S) ℤ, by intro σ; rfl⟩

/-- The actual original logarithmic-lattice inclusion has the literal first projection as retraction. -/
theorem sUnitDiagonal_inclusion_retraction :
    (sUnitDiagonalShortComplex K L S hS).f ≫ sUnitDiagonalRetraction K L S hS =
      𝟙 (sUnitLogLatticeRep K L S hS) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The actual original logarithmic-lattice cohomology injects into the original diagonal product cohomology. -/
theorem sUnitDiagonal_cohomology_injective (n : ℕ) :
    Function.Injective
      ((groupCohomology.functor ℤ Gal(L/K) n).map (sUnitDiagonalShortComplex K L S hS).f).hom := by
  let F := groupCohomology.functor ℤ Gal(L/K) n
  have hs : F.map (sUnitDiagonalShortComplex K L S hS).f ≫
      F.map (sUnitDiagonalRetraction K L S hS) = 𝟙 (F.obj (sUnitLogLatticeRep K L S hS)) := by
    rw [← F.map_comp, sUnitDiagonal_inclusion_retraction]
    exact F.map_id _
  have hl : Function.LeftInverse (F.map (sUnitDiagonalRetraction K L S hS)).hom
      (F.map (sUnitDiagonalShortComplex K L S hS).f).hom := by
    intro x
    exact congrArg (fun f : F.obj (sUnitLogLatticeRep K L S hS) ⟶
      F.obj (sUnitLogLatticeRep K L S hS) => f.hom x) hs
  exact hl.injective

/-- Finiteness of original extended-lattice cohomology implies finiteness for the original logarithmic lattice. -/
theorem sUnitLogLattice_cohomology_finite_of_extended (n : ℕ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) n)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) n) := by
  letI : Finite (groupCohomology (sUnitLogProductRep K L S hS) n) :=
    Finite.of_equiv (groupCohomology (sUnitExtendedLogRep K L S hS) n)
      (sUnitExtendedProductCohomologyIso K L S hS n).symm.toLinearEquiv.toEquiv
  exact Finite.of_injective (β := groupCohomology (sUnitLogProductRep K L S hS) n)
    ((groupCohomology.functor ℤ Gal(L/K) n).map (sUnitDiagonalShortComplex K L S hS).f).hom
    (sUnitDiagonal_cohomology_injective K L S hS n)

end
end Dubon2026
