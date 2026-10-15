import Dubon2026.ArithmeticSourceIdeleExactSequence
import Dubon2026.ArithmeticSUnitIntegerExt

/-! # Original source Hom lifting from actual arithmetic S-unit Ext vanishing

The source ES-to-JS-to-CS sequence and the proved integer Ext vanishing
remove the obstruction to lifting original prime-field coefficient maps
from CS to JS. This is the actual Hom-coefficient sequence needed before
the continuous/equivariant Ext comparison in Milne I.4.10 for DUB-17.
The lift is integer-linear; equivariant Ext vanishing is not asserted.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Forgetting the actual Galois actions retains the original arithmetic source coefficient sequence. -/
abbrev arithmeticSourceModuleShortComplex :=
  (arithmeticSourceIdeleShortComplex K Ω a ha).map
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))

/-- The same original arithmetic coefficient sequence is short exact over the integers. -/
theorem arithmeticSourceModuleShortComplex_shortExact :
    (arithmeticSourceModuleShortComplex K Ω a ha).ShortExact :=
  (arithmeticSourceIdeleShortComplex_shortExact K Ω a ha).map_of_exact _

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- Every original prime-field linear coefficient map to source classes lifts integer-linearly to source ideles, by the proved arithmetic ES Ext vanishing. -/
theorem arithmeticSourceHom_exists_lift
    (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (f : A →ₗ[ℤ] arithmeticSPlaceClassColimitRep K Ω a ha) :
    ∃ g : A →ₗ[ℤ] arithmeticSPlaceColimitRep K Ω a ha,
      (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom.toLinearMap.comp g = f := by
  let S := arithmeticSourceModuleShortComplex K Ω a ha
  have hS := arithmeticSourceModuleShortComplex_shortExact K Ω a ha
  let X := ModuleCat.of ℤ A
  have hz : (Ext.mk₀ (ModuleCat.ofHom f)).comp hS.extClass (show 0 + 1 = 1 from rfl) = 0 :=
    originalArithmeticSUnit_integerExt_eq_zero K Ω a ha q hqa A 0 _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ X hS
    (Ext.mk₀ (ModuleCat.ofHom f)) (show 0 + 1 = 1 from rfl) hz
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective X S.X₂).surjective y
  rw [Ext.mk₀_comp_mk₀] at hy
  have hg : g ≫ S.g = ModuleCat.ofHom f := (Ext.mk₀_bijective X S.X₃).injective hy
  exact ⟨g.hom, congrArg (fun v : X ⟶ S.X₃ => v.hom) hg⟩

end
end Dubon2026
