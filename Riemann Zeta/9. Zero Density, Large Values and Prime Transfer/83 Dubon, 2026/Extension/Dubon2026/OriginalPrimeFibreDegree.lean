import Dubon2026.OriginalAdicDecompositionDegree
import Dubon2026.OriginalFinitePrimeOrbits
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The degree mass over actual primes above an original prime

Reuse the actual Galois orbit theorem and orbit-stabilizer cardinality.
The resulting sum of decomposition orders is the global degree, exactly
the factor needed when summing DUB-17's local invariant base-change
formula over the original prime fibre.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
attribute [local instance] numberFieldGaloisPlaceAction

omit [NumberField L] in
/-- The actual prime fibre is the actual Galois orbit of any of its members. -/
theorem originalFinitePrime_fibre_eq_orbit (w : HeightOneSpectrum (𝓞 L)) :
    {t : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L t = originalFinitePrimeBelow K L w} =
      MulAction.orbit Gal(L/K) w := by
  ext t
  change originalFinitePrimeBelow K L t = originalFinitePrimeBelow K L w ↔ _
  rw [eq_comm, originalFinitePrimeBelow_eq_iff_orbit]
  rfl

omit [NumberField L] in
/-- Summing the actual decomposition orders over all original primes above a base prime gives the global extension degree. -/
theorem originalFinitePrime_finsum_decomposition_card (v : HeightOneSpectrum (𝓞 K)) :
    ∑ᶠ w : {w : HeightOneSpectrum (𝓞 L) // originalFinitePrimeBelow K L w = v},
      Nat.card (OriginalFiniteDecompositionGroup K L w.val) = Module.finrank K L := by
  obtain ⟨w, rfl⟩ := originalFinitePrimeBelow_surjective K L v
  change (∑ᶠ t : ({t : HeightOneSpectrum (𝓞 L) |
      originalFinitePrimeBelow K L t = originalFinitePrimeBelow K L w} : Set _),
    Nat.card (OriginalFiniteDecompositionGroup K L t.val)) = Module.finrank K L
  rw [show {t : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L t = originalFinitePrimeBelow K L w} =
    MulAction.orbit Gal(L/K) w from originalFinitePrime_fibre_eq_orbit K L w]
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit Gal(L/K) w) :=
    (Finite.finite_mulAction_orbit (M := Gal(L/K)) w).fintype
  letI : Fintype (OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  have heq (t : MulAction.orbit Gal(L/K) w) :
      Nat.card (OriginalFiniteDecompositionGroup K L t.val) =
        Nat.card (OriginalFiniteDecompositionGroup K L w) := by
    obtain ⟨σ, hσ⟩ := t.property
    exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer hσ.symm).toEquiv).symm
  simp only [heq, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]
  rw [Nat.card_eq_fintype_card,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group, ← Nat.card_eq_fintype_card]
  exact IsGalois.card_aut_eq_finrank K L

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The sum of actual finite-completion degrees over the original prime fibre is the original global field degree. -/
theorem originalFinitePrime_finsum_completion_degree (v : HeightOneSpectrum (𝓞 K)) :
    (∑ᶠ w : {w : HeightOneSpectrum (𝓞 L) // originalFinitePrimeBelow K L w = v},
      letI : w.val.asIdeal.LiesOver v.asIdeal := by
        simpa only [w.property] using originalFinitePrimeBelow_liesOver K L w.val
      letI : Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
        (originalAdicBaseChangeMap K L v w.val).toAlgebra
      Module.finrank (v.adicCompletion K) (w.val.adicCompletion L)) = Module.finrank K L := by
  calc
    _ = ∑ᶠ w : {w : HeightOneSpectrum (𝓞 L) // originalFinitePrimeBelow K L w = v},
        Nat.card (OriginalFiniteDecompositionGroup K L w.val) := by
      apply finsum_congr
      intro w
      letI : w.val.asIdeal.LiesOver v.asIdeal := by
        simpa only [w.property] using originalFinitePrimeBelow_liesOver K L w.val
      exact originalAdicBaseChange_finrank_eq_decomposition_card K L v w.val
    _ = Module.finrank K L := originalFinitePrime_finsum_decomposition_card K L v

end
end Dubon2026
