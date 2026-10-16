import Dubon2026.OriginalFullIdeleCohomologySequence
import Dubon2026.CyclicPositiveCohomologyVanishing
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Original cyclic class H2 is the quotient of full-idele H2

The existing exact principal-idele sequence gives the kernel. Hilbert90
and the proved native cyclic periodicity make global unit H3 vanish,
so the genuine full-idele-to-class map is surjective on H2. The resulting
literal quotient equivalence is the descent needed for DUB-17's total
invariant and auxiliary full-order cyclic class.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Submodule.Quotient.module

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The actual class-map kernel on H2 is exactly the range of original principal inclusion. -/
theorem originalFullClassH2_ker_eq_principal_range :
    LinearMap.ker ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom =
      LinearMap.range ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom := by
  have h := groupCohomology.mapShortComplex₂_exact (originalFullIdeleShortComplex_shortExact K L) 2
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact h.symm

variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]

omit [NumberField L] in
/-- Hilbert90 and native cyclic periodicity kill H3 of the actual original global unit coefficient. -/
theorem originalCyclicGlobalUnit_third_zero :
    Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 3) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have h1 : Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact cyclic_oddCohomology_zero_of_first (Rep.ofAlgebraAutOnUnits K L) g hg h1 3 (by decide)

/-- Every actual cyclic idele-class H2 class is the image of an original full-idele H2 class. -/
theorem originalFullClassH2_surjective :
    Function.Surjective ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)) := by
  let hX := originalFullIdeleShortComplex_shortExact K L
  have hz := originalCyclicGlobalUnit_third_zero K L
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := 2) rfl).epi_f (hz.eq_zero_of_tgt _)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The literal quotient of original full-idele H2 by principal H2 is the original cyclic idele-class H2. -/
def originalCyclicClassH2QuotientEquiv :
    (groupCohomology (originalFullIdeleRep K L) 2 ⧸
      LinearMap.range ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom) ≃ₗ[ℤ]
      groupCohomology (originalIdeleClassRep K L) 2 :=
  (Submodule.quotEquivOfEq _ _ (originalFullClassH2_ker_eq_principal_range K L).symm).trans
    (((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom.quotKerEquivOfSurjective
      (originalFullClassH2_surjective K L))

/-- The quotient equivalence retains the actual full-idele-to-class cohomology map. -/
theorem originalCyclicClassH2QuotientEquiv_mk
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalCyclicClassH2QuotientEquiv K L (Submodule.Quotient.mk x) =
      (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x := rfl

end
end Dubon2026
