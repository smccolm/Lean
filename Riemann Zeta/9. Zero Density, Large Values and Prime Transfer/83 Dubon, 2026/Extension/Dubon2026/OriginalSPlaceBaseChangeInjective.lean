import Dubon2026.OriginalSPlaceBaseChange

/-! # Faithful original S-place transition

Every base place has an upper place, and the actual completed-field maps
are injective. Their literal product transition therefore reflects zero.
This is needed to descend outside units, and hence identify the invariants
of the original class-formation coefficient on the DUB-17 duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

/-- The literal original S-place transition is injective at the unchanged pulled-back support. -/
theorem originalSPlaceBaseChange_injective :
    Function.Injective (originalSPlaceBaseChange K L S T hST) := by
  intro x y h
  funext p
  cases p with
  | inl v =>
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
    apply Additive.toMul.injective
    apply Units.ext
    apply (originalInfiniteCompletionBaseChange_isometry K L w).injective
    exact congrArg (fun z => (z (Sum.inl w)).toMul.val) h
  | inr v =>
    obtain ⟨w, hw⟩ := originalFinitePrimeBelow_surjective K L v.val
    have hwt : w ∈ T := (hST w).mpr (hw ▸ v.property)
    have hv : v = ⟨originalFinitePrimeBelow K L w, (hST w).mp hwt⟩ :=
      Subtype.ext hw.symm
    subst v
    apply Additive.toMul.injective
    apply Units.ext
    apply (originalFiniteCompletionBaseChange K L w).injective
    let e := supportedIdeleLocalFactorLinearEquiv K S
    have hx := congrArg Prod.fst (e.apply_symm_apply (x, 0))
    have hy := congrArg Prod.fst (e.apply_symm_apply (y, 0))
    calc
      _ = originalFiniteCompletionBaseChange K L w
          (((e (e.symm (x, 0))).1
            (Sum.inr ⟨originalFinitePrimeBelow K L w, (hST w).mp hwt⟩)).toMul.val) :=
        congrArg (fun z => originalFiniteCompletionBaseChange K L w
          ((z (Sum.inr ⟨originalFinitePrimeBelow K L w, (hST w).mp hwt⟩)).toMul.val)) hx.symm
      _ = originalFiniteCompletionBaseChange K L w
          (((e (e.symm (y, 0))).1
            (Sum.inr ⟨originalFinitePrimeBelow K L w, (hST w).mp hwt⟩)).toMul.val) :=
        congrArg (fun z => (z (Sum.inr ⟨w, hwt⟩)).toMul.val) h
      _ = _ := congrArg (fun z => originalFiniteCompletionBaseChange K L w
          ((z (Sum.inr ⟨originalFinitePrimeBelow K L w, (hST w).mp hwt⟩)).toMul.val)) hy

end
end Dubon2026
