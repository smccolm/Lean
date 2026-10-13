import Dubon2026.NumberFieldIdeleSupport
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Algebra.Group.Prod

/-! # Original supported ideles in their actual local coordinates

The units of the original adele ring are identified with their actual
archimedean units and finite unit coordinates. Finite support is used
only to reconstruct the restricted product. This is the entry bridge
for the local cohomology factors in DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- The actual finite unit coordinates integral outside the specified support. -/
def numberFieldSupportedFiniteCoordinates (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup ((v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ) :=
  ⨅ v : HeightOneSpectrum (𝓞 K), ⨅ (_ : v ∉ S),
    ((v.adicCompletionIntegers K).units).comap (Pi.evalMonoidHom _ v)

/-- The original full-idele archimedean component at an actual infinite place. -/
def numberFieldIdeleInfiniteComponent (v : InfinitePlace K) :
    (AdeleRing (𝓞 K) K)ˣ →* v.Completionˣ :=
  Units.map (((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v).comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).toMonoidHom)

/-- The original supported-idele group is the product of its actual local coordinates. -/
def numberFieldSupportedIdeleCoordinateEquiv
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    numberFieldSupportedIdeles K S ≃*
      ((v : InfinitePlace K) → v.Completionˣ) × numberFieldSupportedFiniteCoordinates K S where
  toFun a := (fun v => numberFieldIdeleInfiniteComponent K v a.val,
    ⟨fun v => numberFieldIdeleFiniteComponent K v a.val, by
      simpa only [numberFieldSupportedFiniteCoordinates, numberFieldSupportedIdeles,
        Subgroup.mem_iInf, Subgroup.mem_comap, Pi.evalMonoidHom_apply] using a.property⟩)
  invFun x := by
    have hx : ∀ v, v ∉ S → x.2.val v ∈ (v.adicCompletionIntegers K).units := by
      simpa only [numberFieldSupportedFiniteCoordinates, Subgroup.mem_iInf,
        Subgroup.mem_comap, Pi.evalMonoidHom_apply] using x.2.property
    have he : ∀ᶠ v in Filter.cofinite,
        x.2.val v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      exact hx v hv
    let a : (FiniteAdeleRing (𝓞 K) K)ˣ := RestrictedProduct.mkUnit x.2.val he
    let b : (InfiniteAdeleRing K)ˣ := MulEquiv.piUnits.symm x.1
    refine ⟨MulEquiv.prodUnits.symm (b, a), ?_⟩
    simpa only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] using hx
  left_inv a := by
    apply Subtype.ext
    apply Units.ext
    apply Prod.ext
    · rfl
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext v
      apply Units.ext
      rfl
    · apply Subtype.ext
      funext v
      apply Units.ext
      rfl
  map_mul' a b := by
    apply Prod.ext
    · funext v
      exact map_mul (numberFieldIdeleInfiniteComponent K v) a.val b.val
    · apply Subtype.ext
      funext v
      exact map_mul (numberFieldIdeleFiniteComponent K v) a.val b.val

/-- The finite coordinate of the equivalence is the actual original evaluation. -/
theorem numberFieldSupportedIdeleCoordinateEquiv_finite
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : numberFieldSupportedIdeles K S)
    (v : HeightOneSpectrum (𝓞 K)) :
    (numberFieldSupportedIdeleCoordinateEquiv K S a).2.val v =
      numberFieldIdeleFiniteComponent K v a.val := rfl

/-- The infinite coordinate of the equivalence is the actual original evaluation. -/
theorem numberFieldSupportedIdeleCoordinateEquiv_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : numberFieldSupportedIdeles K S)
    (v : InfinitePlace K) :
    (numberFieldSupportedIdeleCoordinateEquiv K S a).1 v =
      numberFieldIdeleInfiniteComponent K v a.val := rfl

end
end Dubon2026
