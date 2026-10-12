import Dubon2026.OriginalCoinducedSubgroupAcyclicity
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The original coinduced quotient and subgroup dimension shift -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- The original restriction-coinduction unit embeds each coefficient as
the function given by its genuine group orbit. -/
def originalCoinducedUnit : A ⟶ originalCoinducedFunctionRep A :=
  Rep.resCoindToHom (⊥ : Subgroup G).subtype A (Rep.res (⊥ : Subgroup G).subtype A) (𝟙 _)

/-- Evaluation at the original identity recovers the original coefficient. -/
theorem originalCoinducedUnit_injective : Function.Injective (originalCoinducedUnit A).hom := by
  intro x y h
  have he := congrArg (fun f : originalCoinducedFunctionRep A => f.val 1) h
  change A.ρ 1 x = A.ρ 1 y at he
  simpa only [map_one, Module.End.one_apply] using he

/-- The original orbit-function image is invariant under the actual coinduced action. -/
theorem originalCoinducedUnit_range_stable (g : G) :
    (originalCoinducedUnit A).hom.toLinearMap.range ≤
      (originalCoinducedUnit A).hom.toLinearMap.range.comap ((originalCoinducedFunctionRep A).ρ g) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨A.ρ g x, Rep.hom_comm_apply (originalCoinducedUnit A) g x⟩

/-- The actual quotient of original coinduced functions by the actual
image of the original coefficient module. -/
def originalCoinducedQuotient : Rep k G :=
  (originalCoinducedFunctionRep A).quotient (originalCoinducedUnit A).hom.toLinearMap.range
    (originalCoinducedUnit_range_stable A)

/-- The literal original embedding and quotient projection. -/
def originalCoinducedShortComplex : ShortComplex (Rep k G) where
  X₁ := A
  X₂ := originalCoinducedFunctionRep A
  X₃ := originalCoinducedQuotient A
  f := originalCoinducedUnit A
  g := (originalCoinducedFunctionRep A).mkQ (originalCoinducedUnit A).hom.toLinearMap.range
    (originalCoinducedUnit_range_stable A)
  zero := by
    apply Rep.hom_ext
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The same original sequence is short exact after restriction to any
actual subgroup; the quotient, kernel and embedding are unchanged. -/
theorem originalCoinducedShortComplex_restrict_shortExact (S : Subgroup G) :
    ((originalCoinducedShortComplex A).map (Rep.resFunctor S.subtype)).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (originalCoinducedUnit_injective A)
    epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
  apply (((originalCoinducedShortComplex A).map (Rep.resFunctor S.subtype)).exact_map_iff_of_faithful
    (forget₂ (Rep k S) (ModuleCat k))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (originalCoinducedUnit A).hom.toLinearMap.range =
    (originalCoinducedUnit A).hom.toLinearMap.range.mkQ.ker
  rw [Submodule.ker_mkQ]

/-- The actual connecting morphism identifies first cohomology of the
original quotient with second cohomology of the original coefficients on
every subgroup. Both intervening cohomology groups vanish by explicit
original coboundaries. -/
theorem originalCoinducedDimensionShift_isIso (S : Subgroup G) :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl) := by
  exact groupCohomology.isIso_δ_of_isZero
    (originalCoinducedShortComplex_restrict_shortExact A S) 1
      (originalCoinducedSubgroup_first_zero A S) (originalCoinducedSubgroup_second_zero A S)

end
end Dubon2026
