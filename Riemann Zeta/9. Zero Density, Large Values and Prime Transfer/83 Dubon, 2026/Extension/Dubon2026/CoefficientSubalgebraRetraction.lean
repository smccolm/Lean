import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Noetherian descent through an actual coefficient-ring retraction -/

namespace Dubon2026
noncomputable section

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

/-- Corestrict the original coefficient endomorphism to its proved subalgebra image; fixing that same subalgebra makes the actual corestriction surjective. -/
theorem coefficientSubalgebra_corestriction_surjective (S : Subalgebra O R)
    (f : R →ₐ[O] R) (hf : ∀ x, f x ∈ S)
    (hfix : ∀ x : S, f x = (x : R)) :
    Function.Surjective (f.codRestrict S hf) := by
  intro x
  refine ⟨x.val, ?_⟩
  exact Subtype.ext (hfix x)

/-- The actual coefficient subalgebra is Noetherian when the original Noetherian ring admits a genuine retraction onto it. -/
theorem coefficientSubalgebra_isNoetherian_of_retraction [IsNoetherianRing R]
    (S : Subalgebra O R) (f : R →ₐ[O] R) (hf : ∀ x, f x ∈ S)
    (hfix : ∀ x : S, f x = (x : R)) : IsNoetherianRing S := by
  exact isNoetherianRing_of_surjective R S (f.codRestrict S hf).toRingHom
    (coefficientSubalgebra_corestriction_surjective S f hf hfix)

end
end Dubon2026
