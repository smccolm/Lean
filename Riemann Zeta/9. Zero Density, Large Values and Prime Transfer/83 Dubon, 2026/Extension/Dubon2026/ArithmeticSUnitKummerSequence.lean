import Dubon2026.ArithmeticSUnitRepresentation
import Dubon2026.GaloisKummerCoefficientSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The original arithmetic S-unit Kummer coefficient sequence

The original roots of unity embed in the actual integral-closure unit group.
Their image is the kernel of its literal q-power map, and arithmetic S-unit
divisibility proves surjectivity. This is the actual discrete coefficient
sequence needed before the global Ext/cohomology comparison for DUB-17.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance] arithmeticSUnitScalarComm arithmeticSUnitAction
attribute [local instance 1100] Rep.hV2

private theorem rootUnit_integral (R L : Type) [CommRing R] [Field L] [Algebra R L]
    (q : ℕ) (hq : 0 < q) (u : rootsOfUnity q L) : IsIntegral R u.val.val := by
  have h : u.val.val ^ q = 1 := congrArg Units.val u.property
  exact IsIntegral.of_pow hq (h.symm ▸ isIntegral_one)

private def integralRootUnitMap (R L : Type) [CommRing R] [Field L] [Algebra R L]
    (q : ℕ) (hq : 0 < q) : rootsOfUnity q L →* (integralClosure R L)ˣ where
  toFun u := {
    val := ⟨u.val.val, rootUnit_integral R L q hq u⟩
    inv := ⟨u.val.inv, rootUnit_integral R L q hq u⁻¹⟩
    val_inv := Subtype.ext u.val.val_inv
    inv_val := Subtype.ext u.val.inv_val }
  map_one' := Units.ext (Subtype.ext rfl)
  map_mul' _ _ := Units.ext (Subtype.ext rfl)

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]

/-- The same original root unit, now regarded as an actual arithmetic S-unit,
defines a morphism of the original Galois representations. -/
def originalArithmeticSUnitKummerInclusion :
    galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q ⟶
        originalArithmeticSUnitRepresentation K Ω a ha :=
  Rep.ofHom {
    toLinearMap := (integralRootUnitMap (originalLocalizedIntegers K a ha)
      (originalUnramifiedGaloisUnion (Ω := Ω) a) q (Fact.out : q.Prime).pos).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Additive.ofMul.injective
      apply Units.ext
      exact Subtype.ext rfl }

/-- Forgetting S-integrality gives precisely the existing original field-root inclusion. -/
theorem originalArithmeticSUnitKummerInclusion_field_comparison :
    (originalArithmeticSUnitInclusion K Ω a ha).hom.toLinearMap.comp
      (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap =
        (galoisKummerInclusion (K := K)
          (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q).hom.toLinearMap := by
  ext x
  rfl

/-- The actual original root coefficient inclusion into arithmetic S-units is injective. -/
theorem originalArithmeticSUnitKummerInclusion_injective :
    Function.Injective (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap := by
  intro x y h
  apply galoisKummerInclusion_injective (K := K)
    (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q
  have hh := congrArg (originalArithmeticSUnitInclusion K Ω a ha).hom.toLinearMap h
  exact hh

/-- The original root image is exactly the kernel of the actual arithmetic S-unit q-power map. -/
theorem originalArithmeticSUnitKummerCoefficient_exact :
    LinearMap.range (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap =
      LinearMap.ker (originalArithmeticSUnitPower K Ω a ha q).hom.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    apply (originalArithmeticSUnitInclusion_injective K Ω a ha)
    change ((Additive.toMul (Rep.toAdditive u) : rootsOfUnity q
      (originalUnramifiedGaloisUnion (Ω := Ω) a)).val) ^ q = 1
    exact (Additive.toMul (Rep.toAdditive u)).property
  · intro hx
    let u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ := Additive.toMul (Rep.toAdditive x)
    change u ^ q = 1 at hx
    let f := Units.map (OriginalArithmeticSUnitRing K Ω a ha).val.toMonoidHom
    have hv : (f u) ^ q = 1 := by rw [← map_pow, hx, map_one]
    refine ⟨Rep.toAdditive.symm (Additive.ofMul
      (⟨f u, hv⟩ : rootsOfUnity q (originalUnramifiedGaloisUnion (Ω := Ω) a))), ?_⟩
    apply Rep.toAdditive.injective
    apply Additive.toMul.injective
    apply Units.ext
    exact Subtype.ext rfl

/-- The original arithmetic root inclusion and literal S-unit q-power map
form the actual Kummer coefficient complex. -/
def originalArithmeticSUnitKummerShortComplex :
    ShortComplex (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) where
  X₁ := galoisRootOfUnityRepresentation (K := K)
    (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q
  X₂ := originalArithmeticSUnitRepresentation K Ω a ha
  X₃ := originalArithmeticSUnitRepresentation K Ω a ha
  f := originalArithmeticSUnitKummerInclusion K Ω a ha q
  g := originalArithmeticSUnitPower K Ω a ha q
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have h := LinearMap.mem_range_self
      (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap x
    rw [originalArithmeticSUnitKummerCoefficient_exact] at h
    exact h

/-- The actual arithmetic S-unit Kummer sequence is short exact, with the
surjectivity supplied by the constructed unramified roots. -/
theorem originalArithmeticSUnitKummerShortComplex_shortExact [IsAlgClosure K Ω]
    (hqa : (q : 𝓞 K) ∣ a) :
    (originalArithmeticSUnitKummerShortComplex K Ω a ha q).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr
      (originalArithmeticSUnitKummerInclusion_injective K Ω a ha q)
    epi_g := (Rep.epi_iff_surjective _).mpr
      (originalArithmeticSUnitPower_surjective K Ω a ha q hqa) }
  apply ((originalArithmeticSUnitKummerShortComplex K Ω a ha q).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact originalArithmeticSUnitKummerCoefficient_exact K Ω a ha q

end
end Dubon2026
