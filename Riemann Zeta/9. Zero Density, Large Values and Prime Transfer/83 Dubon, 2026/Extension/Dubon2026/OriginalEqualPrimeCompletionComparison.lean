import Dubon2026.NumberFieldGaloisLocalTransport

/-! # Literal comparisons through the same original prime completion

These elementary composition lemmas keep the two actual completion
comparisons opaque when applying them to arithmetic orbit fields. This
is the original-prime fiber calculation required by DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable (L E M : Type) [Field L] [NumberField L] [Field E] [Field M]
  (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : v = w)
  (e : v.adicCompletion L ≃+* E) (e' : w.adicCompletion L ≃+* M)

/-- Compare two fields through the original completed identity at equal primes. -/
def originalEqualPrimeCompletionComparison : E ≃+* M :=
  (e.symm.trans (numberFieldGaloisLocalTransport ℚ L 1 v w
    ((numberFieldGaloisPlaceEquiv_one ℚ L v).trans h))).trans e'

/-- Continuity follows from the actual completion maps and original identity transport. -/
theorem originalEqualPrimeCompletionComparison_continuous
    [TopologicalSpace E] [TopologicalSpace M]
    (he : Continuous e.symm) (he' : Continuous e') :
    Continuous (originalEqualPrimeCompletionComparison L E M v w h e e') :=
  he'.comp ((numberFieldGaloisLocalTransport_continuous ℚ L 1 v w _).comp he)

/-- The literal image of every original global element is preserved by the comparison. -/
theorem originalEqualPrimeCompletionComparison_algebraMap (x : L) :
    originalEqualPrimeCompletionComparison L E M v w h e e'
      (e (algebraMap L (v.adicCompletion L) x)) =
        e' (algebraMap L (w.adicCompletion L) x) := by
  change e' (numberFieldGaloisLocalTransport ℚ L 1 v w _ (e.symm (e _))) = _
  rw [e.symm_apply_apply, numberFieldGaloisLocalTransport_algebraMap]
  rfl

end
end Dubon2026
