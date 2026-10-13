import Dubon2026.SupportedIdeleCoordinates

/-! # Assembly of original ideles from actual local units

Pinned restricted-product unit construction assembles exactly the original
local units once their actual finite coordinates are integral eventually.
These identities and original component extensionality are the construction
step for DUB-17's reverse local-to-global idele norm-image implication.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- The actual finite components of every original idele are original integer units outside finitely many places. -/
theorem originalIdele_finiteComponent_eventually_integerUnit (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v in Filter.cofinite, numberFieldIdeleFiniteComponent K v a ∈ (v.adicCompletionIntegers K).units := by
  filter_upwards [a.val.2.property, a.inv.2.property] with v hv hi
  exact ⟨hv, hi⟩

/-- The pinned original restricted-product constructor assembles actual local units into an original full idele. -/
def originalIdeleFromLocalUnits
    (aInf : (v : InfinitePlace K) → v.Completionˣ)
    (aFin : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hFin : ∀ᶠ v in Filter.cofinite, aFin v ∈ (v.adicCompletionIntegers K).units) :
    (AdeleRing (𝓞 K) K)ˣ :=
  MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm aInf, RestrictedProduct.mkUnit aFin hFin)

/-- The assembled original idele retains every actual finite unit coordinate. -/
theorem originalIdeleFromLocalUnits_finite
    (aInf : (v : InfinitePlace K) → v.Completionˣ)
    (aFin : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hFin : ∀ᶠ v in Filter.cofinite, aFin v ∈ (v.adicCompletionIntegers K).units)
    (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdeleFiniteComponent K v (originalIdeleFromLocalUnits K aInf aFin hFin) = aFin v := rfl

/-- The assembled original idele retains every actual infinite unit coordinate. -/
theorem originalIdeleFromLocalUnits_infinite
    (aInf : (v : InfinitePlace K) → v.Completionˣ)
    (aFin : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hFin : ∀ᶠ v in Filter.cofinite, aFin v ∈ (v.adicCompletionIntegers K).units)
    (v : InfinitePlace K) :
    numberFieldIdeleInfiniteComponent K v (originalIdeleFromLocalUnits K aInf aFin hFin) = aInf v := rfl

/-- Equality of all actual original finite and infinite unit coordinates is equality of original ideles. -/
theorem originalIdele_eq_of_components (a b : (AdeleRing (𝓞 K) K)ˣ)
    (hFin : ∀ v, numberFieldIdeleFiniteComponent K v a = numberFieldIdeleFiniteComponent K v b)
    (hInf : ∀ v, numberFieldIdeleInfiniteComponent K v a = numberFieldIdeleInfiniteComponent K v b) : a = b := by
  apply Units.ext
  apply Prod.ext
  · funext v
    exact congrArg Units.val (hInf v)
  · apply FiniteAdeleRing.ext
    intro v
    exact congrArg Units.val (hFin v)

end
end Dubon2026
