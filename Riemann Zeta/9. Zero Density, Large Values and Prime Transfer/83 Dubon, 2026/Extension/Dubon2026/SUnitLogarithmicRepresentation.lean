import Dubon2026.SUnitLogarithmicExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The original S-unit logarithm in the existing representation category

The proved original Galois actions define actual integer representations.
The original logarithmic surjection is an intertwining representation
morphism. Its actual kernel is stable and finite. These objects connect
the proved logarithmic sequence to the existing original group-cohomology
long exact sequence for DUB-17's Herbrand comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual original S-unit Galois representation over the integers. -/
def sUnitOriginalRep : Rep ℤ Gal(L/K) := by
  letI := sUnitAdditiveGaloisAction K L S hS
  exact Rep.ofDistribMulAction ℤ Gal(L/K) (Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L))

/-- The actual original complete logarithmic lattice as an integer Galois representation. -/
def sUnitLogLatticeRep : Rep ℤ Gal(L/K) := by
  letI := sUnitFullLogLatticeAction L S K hS
  exact Rep.ofDistribMulAction ℤ Gal(L/K) (sUnitFullLogLattice L S)

/-- The original logarithmic surjection as a morphism of the actual Galois representations. -/
def sUnitLogRepHom : sUnitOriginalRep K L S hS ⟶ sUnitLogLatticeRep K L S hS :=
  Rep.ofHom ⟨(sUnitLogToLattice L S).toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact sUnitLogToLattice_galois L S K hS σ x⟩

/-- The representation morphism evaluates to the same original logarithmic lattice vector. -/
theorem sUnitLogRepHom_apply (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    (sUnitLogRepHom K L S hS).hom x = sUnitLogToLattice L S x := rfl

/-- The actual original logarithmic representation morphism is surjective. -/
theorem sUnitLogRepHom_surjective : Function.Surjective (sUnitLogRepHom K L S hS).hom :=
  sUnitLogToLattice_surjective L S

/-- The actual kernel of the original logarithmic representation morphism is finite. -/
theorem sUnitLogRepHom_finite_kernel : Finite (sUnitLogRepHom K L S hS).hom.ker := by
  change Finite (sUnitLogToLattice L S).ker
  rw [sUnitLogToLattice_ker, ← sUnitFullLog_ker_eq_torsion]
  exact sUnitFullLog_finite_kernel L S

/-- The actual logarithmic kernel is invariant under the original S-unit Galois representation. -/
theorem sUnitLogRepHom_kernel_stable (σ : Gal(L/K)) :
    (sUnitLogRepHom K L S hS).hom.toLinearMap.ker ≤
      ((sUnitLogRepHom K L S hS).hom.toLinearMap.ker).comap ((sUnitOriginalRep K L S hS).ρ σ) := by
  letI := sUnitAdditiveGaloisAction K L S hS
  letI := sUnitFullLogLatticeAction L S K hS
  intro x hx
  change Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) at x
  change sUnitLogToLattice L S x = 0 at hx
  change sUnitLogToLattice L S (σ • x) = 0
  rw [sUnitLogToLattice_galois, hx, smul_zero]

end
end Dubon2026
