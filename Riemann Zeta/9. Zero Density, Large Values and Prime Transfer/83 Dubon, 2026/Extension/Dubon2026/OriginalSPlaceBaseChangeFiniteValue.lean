import Dubon2026.OriginalSPlaceBaseChange

/-! Retain the exact prime coordinate under the original S-place field
transition. This identifies the local value of the finite correction after
field enlargement in DUB-17's prescribed local-class recovery. -/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

/-- The source S-place transition evaluates through the literal original
completion embedding at the contracted prime. -/
theorem originalSPlaceBaseChange_finite_value
    (x : ∀ p : SUnitLogPlace K S, supportedUnrestrictedUnitModule K S p) (w : T) :
    (originalSPlaceBaseChange K L S T hST x (Sum.inr w)).toMul.val =
      originalFiniteCompletionBaseChange K L w.val
        ((x (Sum.inr ⟨originalFinitePrimeBelow K L w.val,
          (hST w.val).mp w.property⟩)).toMul.val) := by
  let v : S := ⟨originalFinitePrimeBelow K L w.val, (hST w.val).mp w.property⟩
  have h := congrArg (fun z => (z.1 (Sum.inr v)).toMul.val)
    ((supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply (x, 0))
  exact congrArg (originalFiniteCompletionBaseChange K L w.val) h

/-- At identified original primes the same value uses the original
completed field inclusion, with no remaining transport of the coordinate. -/
theorem originalSPlaceBaseChange_finite_value_at
    (x : ∀ p : SUnitLogPlace K S, supportedUnrestrictedUnitModule K S p)
    (v : S) (w : T) [w.val.asIdeal.LiesOver v.val.asIdeal]
    (h : originalFinitePrimeBelow K L w.val = v.val) :
    (originalSPlaceBaseChange K L S T hST x (Sum.inr w)).toMul.val =
      originalAdicBaseChangeMap K L v.val w.val ((x (Sum.inr v)).toMul.val) := by
  rcases v with ⟨v, hv⟩
  dsimp only at h
  subst v
  exact originalSPlaceBaseChange_finite_value K L S T hST x w

end
end Dubon2026
