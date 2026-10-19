import Dubon2026.LocalQuotientGeneratorBound
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Reuse the pinned finite-ideal quotient bound after lifting a fixed
base ring's maximal-ideal generators. The resulting bound depends only
on that base ring and the fixed number of actual character directions,
as required by the existing patching algebra's uniform-rank condition. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped BigOperators

/-- A fixed quotient and a bounded kernel give uniform bounds on
all finite maximal-adic quotients of the original auxiliary ring. -/
theorem localQuotient_cardinality_pow_le
    {R A η : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [Fintype η] [Finite (ResidueField R)]
    (f : R →+* A) (hf : Function.Surjective f)
    (v : η → R) (hker : RingHom.ker f = Ideal.span (Set.range v))
    (s : Finset A) (hs : Ideal.span (s : Set A) = maximalIdeal A) (k : ℕ) :
    Nat.card (R ⧸ maximalIdeal R ^ k) ≤
      Nat.card (ResidueField R) ^
        (∑ i ∈ Finset.range k, (Fintype.card η + s.card) ^ i) := by
  letI : Finite (R ⧸ maximalIdeal R) := inferInstanceAs (Finite (ResidueField R))
  obtain ⟨t, ht, hcard⟩ := localQuotient_exists_bounded_maximal_generators f hf v hker s hs
  have h := Ideal.index_pow_le t ht k
  change Nat.card (R ⧸ maximalIdeal R ^ k) ≤
    Nat.card (ResidueField R) ^ (∑ i ∈ Finset.range k, t.card ^ i) at h
  apply h.trans
  have hpos : 0 < Nat.card (ResidueField R) := Nat.card_pos
  gcongr

end
end Dubon2026
