import Dubon2026.ArithmeticGlobalSourceMaps
import Dubon2026.ArithmeticSPlaceColimitExactness
import Dubon2026.ArithmeticSUnitCoefficientColimitIso

/-! # The original arithmetic S-unit, source idele and source class sequence

Actual finite-stage exactness and the original equivariant coefficient
colimit identify a short exact sequence beginning with the arithmetic ES
representation. The JS and CS terms are the source fixed-support colimits,
with their proved continuous arithmetic actions. This constructs the source
sequence required by Milne I.4.10 on DUB-17's global-duality route; it does
not assert the remaining class-formation or continuous Ext comparisons.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The original source coefficient-colimit sequence with its actual arithmetic Galois maps. -/
def arithmeticSourceColimitShortComplex :
    ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) where
  X₁ := arithmeticSUnitCoefficientColimitRep K Ω a ha
  X₂ := arithmeticSPlaceColimitRep K Ω a ha
  X₃ := arithmeticSPlaceClassColimitRep K Ω a ha
  f := arithmeticSPlaceColimitPrincipalRepHom K Ω a ha
  g := arithmeticSPlaceColimitQuotientRepHom K Ω a ha
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact arithmeticSPlaceColimitQuotient_principal K Ω a ha x

/-- The actual equivariant source coefficient-colimit sequence is short exact. -/
theorem arithmeticSourceColimitShortComplex_shortExact :
    (arithmeticSourceColimitShortComplex K Ω a ha).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (arithmeticSPlaceColimitPrincipal_injective K Ω a ha)
    epi_g := (Rep.epi_iff_surjective _).mpr (arithmeticSPlaceColimitQuotient_surjective K Ω a ha) }
  apply ((arithmeticSourceColimitShortComplex K Ω a ha).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact arithmeticSPlaceColimit_range_eq_ker K Ω a ha

/-- The original arithmetic S-unit diagonal, identified through its literal finite-stage inclusions. -/
def arithmeticSourcePrincipalRepHom :
    originalArithmeticSUnitRepresentation K Ω a ha ⟶ arithmeticSPlaceColimitRep K Ω a ha :=
  (arithmeticSUnitCoefficientColimitIso K Ω a ha).inv ≫ arithmeticSPlaceColimitPrincipalRepHom K Ω a ha

/-- The source arithmetic sequence beginning with the actual original localized S-units. -/
def arithmeticSourceIdeleShortComplex :
    ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) where
  X₁ := originalArithmeticSUnitRepresentation K Ω a ha
  X₂ := arithmeticSPlaceColimitRep K Ω a ha
  X₃ := arithmeticSPlaceClassColimitRep K Ω a ha
  f := arithmeticSourcePrincipalRepHom K Ω a ha
  g := arithmeticSPlaceColimitQuotientRepHom K Ω a ha
  zero := by
    change ((arithmeticSUnitCoefficientColimitIso K Ω a ha).inv ≫
      (arithmeticSourceColimitShortComplex K Ω a ha).f) ≫
      (arithmeticSourceColimitShortComplex K Ω a ha).g = 0
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => (arithmeticSUnitCoefficientColimitIso K Ω a ha).inv ≫ q)
        (arithmeticSourceColimitShortComplex K Ω a ha).zero).trans (comp_zero))

/-- The actual arithmetic S-unit comparison preserves the original source diagonal. -/
theorem arithmeticSourcePrincipal_from_colimit :
    (arithmeticSUnitCoefficientColimitIso K Ω a ha).hom ≫ arithmeticSourcePrincipalRepHom K Ω a ha =
      arithmeticSPlaceColimitPrincipalRepHom K Ω a ha := by
  change (arithmeticSUnitCoefficientColimitIso K Ω a ha).hom ≫
    (arithmeticSUnitCoefficientColimitIso K Ω a ha).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

/-- The original arithmetic ES, JS and CS sequence is short exact for the same fixed exceptional support. -/
theorem arithmeticSourceIdeleShortComplex_shortExact :
    (arithmeticSourceIdeleShortComplex K Ω a ha).ShortExact := by
  let e : arithmeticSourceColimitShortComplex K Ω a ha ≅ arithmeticSourceIdeleShortComplex K Ω a ha :=
    ShortComplex.isoMk (arithmeticSUnitCoefficientColimitIso K Ω a ha) (Iso.refl _) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using arithmeticSourcePrincipal_from_colimit K Ω a ha)
      (by
        change 𝟙 _ ≫ arithmeticSPlaceColimitQuotientRepHom K Ω a ha =
          arithmeticSPlaceColimitQuotientRepHom K Ω a ha ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id])
  exact ShortComplex.shortExact_of_iso e (arithmeticSourceColimitShortComplex_shortExact K Ω a ha)

/-- The global source diagonal retains the literal finite-stage arithmetic S-unit embedding and original local diagonal. -/
theorem arithmeticSourcePrincipal_finiteStage
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticSUnitFiniteStageRep K Ω a ha F) :
    (arithmeticSourcePrincipalRepHom K Ω a ha).hom
      ((arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom x) =
        Module.DirectLimit.of ℤ
          (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
          (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
          (arithmeticSPlaceTransitionMap K Ω a ha) F
            ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom x) := by
  let y : ArithmeticSUnitCoefficientColimit K Ω a ha :=
    Module.DirectLimit.of ℤ
      (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
      (arithmeticSUnitCoefficientTransition K Ω a ha) F x
  have h := congrArg (fun v : arithmeticSUnitCoefficientColimitRep K Ω a ha ⟶
      arithmeticSPlaceColimitRep K Ω a ha => v.hom y)
    (arithmeticSourcePrincipal_from_colimit K Ω a ha)
  change (arithmeticSourcePrincipalRepHom K Ω a ha).hom
      (arithmeticSUnitCoefficientColimitToGlobal K Ω a ha y) =
        arithmeticSPlaceColimitPrincipal K Ω a ha y at h
  exact (congrArg (arithmeticSourcePrincipalRepHom K Ω a ha).hom
    (arithmeticSUnitCoefficientColimitToGlobal_of K Ω a ha F x).symm).trans
      (h.trans (arithmeticSPlaceColimitPrincipal_of K Ω a ha F x))

end
end Dubon2026
