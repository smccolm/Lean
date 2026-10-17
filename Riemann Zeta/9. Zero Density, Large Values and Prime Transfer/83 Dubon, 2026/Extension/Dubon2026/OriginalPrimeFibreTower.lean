import Dubon2026.OriginalPrimeTowerSelection

/-! # Actual prime fibres in the required nonnormal field tower

This finite reindexing serves the sum of local completion degrees through
the Sylow fixed field. It uses the original primes and contraction maps.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- The actual original prime fibre over a specified lower prime. -/
abbrev OriginalPrimeFibre
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :=
  {w : HeightOneSpectrum (𝓞 L) // originalFinitePrimeBelow K L w = v}

/-- Original prime fibres are finite without a normality assumption. -/
instance originalPrimeFibreFinite
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Finite (OriginalPrimeFibre K L v) := by
  have h : {w : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L w = v}.Finite := by
    simpa only [Set.mem_singleton_iff] using
      originalFinitePrimeBelow_preimage_finite K L {v} (Set.finite_singleton v)
  exact h.to_subtype

/-- Reindex actual upper primes by their intermediate primes in the same
field tower. All field and prime maps remain the original contractions. -/
def originalPrimeFibreTowerEquiv
    (K E M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] (v : HeightOneSpectrum (𝓞 K)) :
    (Σ u : OriginalPrimeFibre K E v, OriginalPrimeFibre E M u.val) ≃
      OriginalPrimeFibre K M v where
  toFun z := ⟨z.2.val, (originalFinitePrimeBelow_tower K E M z.2.val).symm.trans
    ((congrArg (originalFinitePrimeBelow K E) z.2.property).trans z.1.property)⟩
  invFun w := ⟨⟨originalFinitePrimeBelow E M w.val,
    (originalFinitePrimeBelow_tower K E M w.val).trans w.property⟩, ⟨w.val, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
    cases hw
    rfl
  right_inv _ := rfl

end
end Dubon2026
