import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index
import Dubon2026.Reuse.Imperial.Patching.Algebra

/-! Uniform finite-quotient rank descends when the actual arithmetic
rings are further quotiented by genuine local deformation conditions.
This preserves the established ring bound on the DUB-17 chain; it does
not construct those conditions or prove their required dimensions. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- A surjective map of local rings gives a surjection on every
maximal-adic quotient, preserving the required finite-cardinality bound. -/
theorem localSurjection_cardinality_quotient_pow_le
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) (k : ℕ)
    [Finite (R ⧸ maximalIdeal R ^ k)] :
    Nat.card (S ⧸ maximalIdeal S ^ k) ≤ Nat.card (R ⧸ maximalIdeal R ^ k) := by
  have hmap : Ideal.map f (maximalIdeal R ^ k) = maximalIdeal S ^ k := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective f hf]
  let e := Ideal.quotientMap (maximalIdeal S ^ k) f
    (Ideal.map_le_iff_le_comap.mp hmap.le)
  exact Nat.card_le_card_of_surjective e (Ideal.quotientMap_surjective hf)

/-- The existing uniform-rank bound survives actual surjective local
deformation quotients. Finiteness of the source truncations is derived
from its Noetherianity and finite residue field. -/
theorem localQuotientFamily_uniformlyBoundedRank
    {I : Type*} (R S : I → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, IsNoetherianRing (R i)]
    [∀ i, Finite (ResidueField (R i))]
    [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [Algebra.UniformlyBoundedRank R]
    (f : ∀ i, R i →+* S i) (hf : ∀ i, Function.Surjective (f i)) :
    Algebra.UniformlyBoundedRank S := by
  constructor
  intro k
  obtain ⟨b, hb⟩ := Algebra.UniformlyBoundedRank.cond (R := R) k
  refine ⟨b, fun i => ?_⟩
  letI : Finite (R i ⧸ maximalIdeal (R i)) := inferInstanceAs (Finite (ResidueField (R i)))
  letI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal (R i))) k
  exact (localSurjection_cardinality_quotient_pow_le (f i) (hf i) k).trans_lt (hb i)

end
end Dubon2026
