import Dubon2026.SUnitLogarithmicRepresentation
import Dubon2026.FiniteCyclicCohomologyCardinality

/-! # The actual logarithmic short exact sequence for original cohomology

The proved logarithmic representation morphism supplies an actual short
exact sequence in the project's existing representation category. Its
first term is the original finite logarithmic kernel, already identified
with S-unit torsion. The existing cochain argument proves finite kernel
cohomology. These are the precise original inputs to DUB-17's logarithmic
Herbrand comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual logarithmic kernel, original S-units and original logarithmic lattice form this representation complex. -/
def sUnitLogarithmicShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := Rep.subrepresentation (sUnitOriginalRep K L S hS)
    (sUnitLogRepHom K L S hS).hom.toLinearMap.ker (sUnitLogRepHom_kernel_stable K L S hS)
  X₂ := sUnitOriginalRep K L S hS
  X₃ := sUnitLogLatticeRep K L S hS
  f := Rep.subtype _ _ (sUnitLogRepHom_kernel_stable K L S hS)
  g := sUnitLogRepHom K L S hS
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact x.property

/-- The original logarithmic representation sequence is short exact without an exactness hypothesis. -/
theorem sUnitLogarithmicShortComplex_shortExact :
    (sUnitLogarithmicShortComplex K L S hS).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr Subtype.val_injective
    epi_g := (Rep.epi_iff_surjective _).mpr (sUnitLogRepHom_surjective K L S hS) }
  apply ((sUnitLogarithmicShortComplex K L S hS).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change ((sUnitLogRepHom K L S hS).hom.toLinearMap.ker).subtype.range =
    (sUnitLogRepHom K L S hS).hom.toLinearMap.ker
  exact Submodule.range_subtype _

/-- The first term of the actual original logarithmic representation sequence is finite. -/
theorem sUnitLogarithmicShortComplex_finite_kernel :
    Finite (sUnitLogarithmicShortComplex K L S hS).X₁ :=
  sUnitLogRepHom_finite_kernel K L S hS

/-- Every original cohomology group of the actual logarithmic kernel is finite. -/
theorem sUnitLogarithmicKernel_cohomology_finite [FiniteDimensional K L] (n : ℕ) :
    Finite (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ n) := by
  letI := sUnitLogarithmicShortComplex_finite_kernel K L S hS
  exact finite_groupCohomology_of_finite_coefficients _ n

end
end Dubon2026
