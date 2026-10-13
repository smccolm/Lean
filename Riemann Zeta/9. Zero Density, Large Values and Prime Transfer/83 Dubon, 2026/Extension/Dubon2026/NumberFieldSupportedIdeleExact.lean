import Dubon2026.NumberFieldIdeleSupport
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Exact original principal S-units in supported ideles

The global idele class group is the quotient of units of the original
adele ring by the original principal image. The kernel of the actual
supported-idele map consists exactly of the actual principal S-units,
and the first isomorphism theorem identifies the quotient with its
actual image. Surjectivity onto the whole class group for sufficiently
large S is a later obligation in DUB-17's global norm-index dependency.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- The class group of the original full ideles modulo their actual principal image. -/
abbrev OriginalNumberFieldIdeleClassGroup :=
  (AdeleRing (𝓞 K) K)ˣ ⧸ (numberFieldPrincipalIdele K).range

/-- The actual map from supported original ideles to the original global idele classes. -/
def numberFieldSupportedIdeleClassMap (S : Set (HeightOneSpectrum (𝓞 K))) :
    numberFieldSupportedIdeles K S →* OriginalNumberFieldIdeleClassGroup K :=
  (QuotientGroup.mk' (numberFieldPrincipalIdele K).range).comp
    (numberFieldSupportedIdeles K S).subtype

/-- The original S-units embed as actual principal supported ideles. -/
def numberFieldSupportedPrincipalIdele (S : Set (HeightOneSpectrum (𝓞 K))) :
    S.unit K →* numberFieldSupportedIdeles K S where
  toFun x := ⟨numberFieldPrincipalIdele K x.val,
    (numberFieldPrincipalIdele_mem_supported_iff K S x.val).mpr x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The original principal S-unit map is injective. -/
theorem numberFieldSupportedPrincipalIdele_injective
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (numberFieldSupportedPrincipalIdele K S) := by
  intro x y h
  apply Subtype.ext
  exact numberFieldPrincipalIdele_injective K (congrArg Subtype.val h)

/-- The exact kernel of the original supported-idele class map is the original principal S-unit image. -/
theorem numberFieldSupportedIdeleClassMap_ker
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (numberFieldSupportedIdeleClassMap K S).ker =
      (numberFieldSupportedPrincipalIdele K S).range := by
  ext a
  change QuotientGroup.mk' (numberFieldPrincipalIdele K).range a.val = 1 ↔
    ∃ x, numberFieldSupportedPrincipalIdele K S x = a
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff a.val).mp ha
    have hxS : x ∈ S.unit K :=
      (numberFieldPrincipalIdele_mem_supported_iff K S x).mp (hx.symm ▸ a.property)
    exact ⟨⟨x, hxS⟩, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact (QuotientGroup.eq_one_iff a.val).mpr ⟨x.val, congrArg Subtype.val hx⟩

/-- Supported ideles modulo the actual principal S-units identify with their actual global class image. -/
def numberFieldSupportedIdeleQuotientEquivImage
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    numberFieldSupportedIdeles K S ⧸ (numberFieldSupportedPrincipalIdele K S).range ≃*
      (numberFieldSupportedIdeleClassMap K S).range :=
  (QuotientGroup.quotientMulEquivOfEq (numberFieldSupportedIdeleClassMap_ker K S).symm).trans
    (QuotientGroup.quotientKerEquivRange (numberFieldSupportedIdeleClassMap K S))

end
end Dubon2026
