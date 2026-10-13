import Dubon2026.SupportedIdeleCohomologySequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # The exact original full principal-idele sequence

The full field-unit coefficient has vanishing H1 by existing Hilbert90.
Its original short exact sequence therefore supplies the invariant-class
lifting step needed to compare the cohomological norm quotient with the
actual base-field class norm quotient in DUB-17. Supported S-units cannot
replace this coefficient because their H1 need not vanish.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original full idele group with its actual original Galois action. -/
def originalFullIdeleRep : Rep ℤ Gal(L/K) := by
  letI := numberFieldIdeleGaloisAction K L
  exact Rep.ofMulDistribMulAction Gal(L/K) (AdeleRing (𝓞 L) L)ˣ

/-- The actual full principal-idele embedding as an original coefficient morphism. -/
def originalFullPrincipalRepHom : Rep.ofAlgebraAutOnUnits K L ⟶ originalFullIdeleRep K L :=
  Rep.ofHom ⟨(numberFieldPrincipalIdele L).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (numberFieldPrincipalIdele_galois K L σ x.toMul).symm⟩

/-- The actual original full class quotient as an original coefficient morphism. -/
def originalFullClassRepHom : originalFullIdeleRep K L ⟶ originalIdeleClassRep K L :=
  Rep.ofHom ⟨(QuotientGroup.mk' (numberFieldPrincipalIdele L).range).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (numberFieldIdeleClassGaloisMap_mk K L σ x.toMul).symm⟩

/-- The original global field units, full ideles and idele classes form the actual coefficient sequence. -/
def originalFullIdeleShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := Rep.ofAlgebraAutOnUnits K L
  X₂ := originalFullIdeleRep K L
  X₃ := originalIdeleClassRep K L
  f := originalFullPrincipalRepHom K L
  g := originalFullClassRepHom K L
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change QuotientGroup.mk' (numberFieldPrincipalIdele L).range
      (numberFieldPrincipalIdele L x.toMul) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x.toMul, rfl⟩

/-- The original full principal-idele representation sequence is short exact without a support hypothesis. -/
theorem originalFullIdeleShortComplex_shortExact :
    (originalFullIdeleShortComplex K L).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr ?_
    epi_g := (Rep.epi_iff_surjective _).mpr ?_ }
  · apply ((originalFullIdeleShortComplex K L).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext x
    change Additive (AdeleRing (𝓞 L) L)ˣ at x
    change (∃ y : Additive Lˣ, Additive.ofMul (numberFieldPrincipalIdele L y.toMul) = x) ↔
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range x.toMul = 1
    constructor
    · rintro ⟨y, hy⟩
      exact (QuotientGroup.eq_one_iff x.toMul).mpr ⟨y.toMul, congrArg Additive.toMul hy⟩
    · intro hx
      obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff x.toMul).mp hx
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  · intro x y h
    apply Additive.toMul.injective
    exact numberFieldPrincipalIdele_injective L (congrArg Additive.toMul h)
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (numberFieldPrincipalIdele L).range x.toMul
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

/-- Actual Hilbert90 makes the original full idele-to-class map surjective on original H0. -/
theorem originalFullClassH0_surjective [FiniteDimensional K L] :
    Function.Surjective ((groupCohomology.functor ℤ Gal(L/K) 0).map (originalFullClassRepHom K L)) := by
  let X := originalFullIdeleShortComplex K L
  let hX := originalFullIdeleShortComplex_shortExact K L
  have hz : Limits.IsZero (groupCohomology X.X₁ 1) := by
    change Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1)
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have he := groupCohomology.mapShortComplex₃_exact hX (i := 0) rfl
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 0).map (originalFullClassRepHom K L)) :=
    he.epi_f (hz.eq_of_tgt _ _)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end
end Dubon2026
