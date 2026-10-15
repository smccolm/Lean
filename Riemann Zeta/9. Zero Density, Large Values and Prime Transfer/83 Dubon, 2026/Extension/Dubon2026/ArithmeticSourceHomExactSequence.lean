import Dubon2026.ArithmeticSourceHomLifting

/-! # Actual arithmetic Hom-coefficient exactness

The pinned internal Hom functor retains the original conjugate Galois
actions and literal postcomposition maps. Its left exactness and the proved
arithmetic integer Ext vanishing yield the actual short exact Hom sequence
for prime-field coefficients. This removes the Hom-surjectivity input before
the continuous source duality comparison; no equivariant Ext is assumed zero.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))

local instance : (CategoryTheory.ihom A).PreservesZeroMorphisms where
  map_zero X Y := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl

/-- Actual integer-linear Hom coefficients with their original conjugate arithmetic actions and postcomposition maps. -/
abbrev arithmeticSourceHomShortComplex :=
  (arithmeticSourceIdeleShortComplex K Ω a ha).map (CategoryTheory.ihom A)

/-- The original Hom quotient map is literal postcomposition with the same source class quotient. -/
theorem arithmeticSourceHomShortComplex_quotient_apply
    (f : A →ₗ[ℤ] arithmeticSPlaceColimitRep K Ω a ha) :
    (arithmeticSourceHomShortComplex K Ω a ha A).g.hom f =
      (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom.toLinearMap.comp f := rfl

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  [Module (ZMod q) A]

include hqa in
/-- The original source Hom sequence is short exact for actual prime-field coefficients, with surjectivity derived from arithmetic ES Ext vanishing. -/
theorem arithmeticSourceHomShortComplex_shortExact :
    (arithmeticSourceHomShortComplex K Ω a ha A).ShortExact := by
  have hS := arithmeticSourceIdeleShortComplex_shortExact K Ω a ha
  haveI := hS.mono_f
  refine {
    exact := hS.exact.map_of_mono_of_preservesKernel (CategoryTheory.ihom A) hS.mono_f inferInstance
    mono_f := ?_
    epi_g := ?_ }
  · change Mono ((CategoryTheory.ihom A).map (arithmeticSourceIdeleShortComplex K Ω a ha).f)
    infer_instance
  · apply (Rep.epi_iff_surjective _).mpr
    change Function.Surjective (fun f : A →ₗ[ℤ] arithmeticSPlaceColimitRep K Ω a ha =>
      (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom.toLinearMap.comp f)
    rw [show A.hV2 = AddCommGroup.toIntModule A from Subsingleton.elim _ _]
    intro f
    obtain ⟨g, hg⟩ := arithmeticSourceHom_exists_lift K Ω a ha q hqa A f
    exact ⟨g, hg⟩

end
end Dubon2026
