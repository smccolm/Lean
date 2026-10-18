import Dubon2026.OriginalLocalCompletionSurjective
import Dubon2026.OriginalLocalCompletionValuation

/-! Compare the genuine number-field completion of Q with the original
prime-local field defined over Z. The existing induced-prime and completed
embedding constructions preserve the literal rational values and valuation.
This is the base-field comparison needed by DUB-17's arithmetic Cartier
specialization of the finite local relation total. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (p : ℕ) (hp : p.Prime)

/-- The actual prime of the ring of integers of Q induced by the original
rational prime-local embedding. -/
def rationalOriginalPrimePlace : HeightOneSpectrum (𝓞 ℚ) :=
  originalLocalEmbeddingPrime ℚ (rationalPrimeLocalField p hp) p hp

/-- Its contraction is exactly the original prime of Z. -/
theorem rationalOriginalPrimePlace_below :
    originalIntegerPrimeBelow ℚ (rationalOriginalPrimePlace p hp) = rationalPrimePlace p hp :=
  originalLocalEmbeddingPrime_below ℚ (rationalPrimeLocalField p hp) p hp

/-- The original local base alone generates itself in the completed
rational embedding, discharging the completion-surjectivity input. -/
private theorem rationalOriginalPrimeCompletion_generation :
    (algebraMap (rationalPrimeLocalField p hp) (rationalPrimeLocalField p hp)).fieldRange ⊔
      (algebraMap ℚ (rationalPrimeLocalField p hp)).fieldRange = ⊤ := by
  have h : (algebraMap (rationalPrimeLocalField p hp) (rationalPrimeLocalField p hp)).fieldRange = ⊤ :=
    RingHom.fieldRange_eq_top_iff.mpr (fun x => ⟨x, rfl⟩)
  rw [h, top_sup_eq]

/-- The ring-of-integers completion and original prime-local field are
identified through their actual dense rational embeddings. -/
def rationalOriginalPrimeCompletionEquiv :
    (rationalOriginalPrimePlace p hp).adicCompletion ℚ ≃+* rationalPrimeLocalField p hp :=
  originalLocalCompletionEquiv ℚ (rationalPrimeLocalField p hp) p hp
    (rationalOriginalPrimeCompletion_generation p hp)

/-- The completion comparison fixes every original rational field value. -/
theorem rationalOriginalPrimeCompletionEquiv_rational (x : ℚ) :
    rationalOriginalPrimeCompletionEquiv p hp
      (algebraMap ℚ ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) x) =
      algebraMap ℚ (rationalPrimeLocalField p hp) x :=
  originalLocalCompletionEquiv_algebraMap ℚ (rationalPrimeLocalField p hp) p hp
    (rationalOriginalPrimeCompletion_generation p hp) x

end
end Dubon2026
