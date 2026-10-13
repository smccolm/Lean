import Dubon2026.SupportedFiniteCoordinateFactors
import Dubon2026.SupportedUnrestrictedUnitTransports
import Dubon2026.SupportedOutsideUnitRepresentation

/-! # The original supported ideles split into their actual local factors

The original adele-unit coordinate equivalence and its finite-support
split identify the supported coefficient group with the unrestricted
local units and the original outside-support integer units. This is the
original-object entry required for DUB-17's local cohomology calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

/-- The actual supported-idele coefficient group in its original unrestricted and integral coordinates. -/
def supportedIdeleLocalFactorLinearEquiv :
    Additive (numberFieldSupportedIdeles L S) ≃ₗ[ℤ]
      (∀ p : SUnitLogPlace L S, supportedUnrestrictedUnitModule L S p) ×
        (∀ v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}, Additive (v.val.adicCompletionIntegers L)ˣ) := by
  let e := (numberFieldSupportedIdeleCoordinateEquiv L S).trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (numberFieldSupportedFiniteFactorEquiv L S))
  let f : Additive (((v : InfinitePlace L) → v.Completionˣ) ×
      (((v : S) → (v.val.adicCompletion L)ˣ) ×
        ((v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}) → (v.val.adicCompletionIntegers L)ˣ))) ≃+
      (∀ p : SUnitLogPlace L S, supportedUnrestrictedUnitModule L S p) ×
        (∀ v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}, Additive (v.val.adicCompletionIntegers L)ˣ) := {
    toFun := fun x => (fun p => match p with
      | Sum.inl v => Additive.ofMul (x.toMul.1 v)
      | Sum.inr v => Additive.ofMul (x.toMul.2.1 v),
      fun v => Additive.ofMul (x.toMul.2.2 v))
    invFun := fun y => Additive.ofMul
      ((fun v => (y.1 (Sum.inl v)).toMul),
        ((fun v => (y.1 (Sum.inr v)).toMul), (fun v => (y.2 v).toMul)))
    left_inv := fun _ => rfl
    right_inv := by
      intro y
      apply Prod.ext
      · funext p
        cases p <;> rfl
      · rfl
    map_add' := by
      intro x y
      apply Prod.ext
      · funext p
        cases p <;> rfl
      · rfl }
  exact (e.toAdditive.trans f).toIntLinearEquiv

/-- The unrestricted infinite coordinate is the original full-idele evaluation. -/
theorem supportedIdeleLocalFactorLinearEquiv_infinite
    (a : Additive (numberFieldSupportedIdeles L S)) (v : InfinitePlace L) :
    (supportedIdeleLocalFactorLinearEquiv L S a).1 (Sum.inl v) =
      Additive.ofMul (numberFieldIdeleInfiniteComponent L v a.toMul.val) := rfl

/-- The unrestricted finite coordinate is the original full-idele evaluation. -/
theorem supportedIdeleLocalFactorLinearEquiv_finite
    (a : Additive (numberFieldSupportedIdeles L S)) (v : S) :
    (supportedIdeleLocalFactorLinearEquiv L S a).1 (Sum.inr v) =
      Additive.ofMul (numberFieldIdeleFiniteComponent L v.val a.toMul.val) := rfl

/-- The outside-support integer coordinate retains the actual original full-idele field value. -/
theorem supportedIdeleLocalFactorLinearEquiv_outside
    (a : Additive (numberFieldSupportedIdeles L S))
    (v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}) :
    (((supportedIdeleLocalFactorLinearEquiv L S a).2 v).toMul.val : v.val.adicCompletion L) =
      (numberFieldIdeleFiniteComponent L v.val a.toMul.val).val := rfl

end
end Dubon2026
