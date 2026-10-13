import Dubon2026.OriginalAdicFiniteGalois
import Dubon2026.OriginalUnramifiedDecompositionCyclic
import Mathlib.RingTheory.Ideal.NatInt

/-! # Actual completion degrees from original prime stabilizers

The existing original prime-to-ideal stabilizer map is surjective as
well as injective. Its cardinality computes the original completion
degree, allowing the pinned cyclotomic ramification and inertia formulas
to supply DUB-17's local degree divisibility without a degree premise.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Pointwise
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Every automorphism fixing the original ideal fixes the same original height-one prime. -/
theorem originalFiniteDecompositionIdealMap_surjective (w : HeightOneSpectrum (𝓞 L)) :
    Function.Surjective (originalFiniteDecompositionIdealMap K L w) := by
  intro σ
  refine ⟨⟨σ.val, ?_⟩, rfl⟩
  change numberFieldGaloisPlaceEquiv K L σ.val w = w
  apply HeightOneSpectrum.ext
  rw [numberFieldGaloisPlaceEquiv_asIdeal]
  have h := σ.property
  change σ.val • w.asIdeal = w.asIdeal at h
  rw [Ideal.pointwise_smul_def] at h
  exact h

/-- The original prime stabilizer and its literal ideal stabilizer have equal order. -/
theorem originalFiniteDecomposition_card_ideal (w : HeightOneSpectrum (𝓞 L)) :
    Nat.card (OriginalFiniteDecompositionGroup K L w) =
      Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) :=
  Nat.card_congr (Equiv.ofBijective (originalFiniteDecompositionIdealMap K L w)
    ⟨originalFiniteDecompositionIdealMap_injective K L w,
      originalFiniteDecompositionIdealMap_surjective K L w⟩)

variable [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual original completed extension has degree equal to its original decomposition-group order. -/
theorem originalAdicBaseChange_finrank_eq_decomposition_card
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (OriginalFiniteDecompositionGroup K L w) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI := (originalAdicBaseChange_finite_galois K L v w).1
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (originalAdicDecompositionGaloisEquiv K L v w).toEquiv).symm

omit K in
/-- For a rational number-field extension the actual decomposition order is the original integer-prime ramification index times its residue degree. -/
theorem originalRationalDecomposition_card_eq
    [IsGalois ℚ L] (p : ℕ) [hp : Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (OriginalFiniteDecompositionGroup ℚ L w) =
      (Ideal.span {(p : ℤ)}).ramificationIdx w.asIdeal *
        (Ideal.span {(p : ℤ)}).inertiaDeg w.asIdeal := by
  let v := Ideal.span {(p : ℤ)}
  have hv : v ≠ ⊥ := by simpa [v] using hp.out.ne_zero
  letI : v.IsPrime := Ideal.isPrime_int_iff.mpr (Or.inr ⟨p, hp.out, rfl⟩)
  letI : v.IsMaximal := (show v.IsPrime from inferInstance).isMaximal hv
  letI : Field (ℤ ⧸ v) := Ideal.Quotient.field v
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Finite (ℤ ⧸ v) := Ring.HasFiniteQuotients.finiteQuotient hv
  rw [originalFiniteDecomposition_card_ideal]
  have h := Ideal.card_stabilizer_eq (G := Gal(L/ℚ)) v hv w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v w.asIdeal Gal(L/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg v w.asIdeal Gal(L/ℚ)] at h
  exact h

end
end Dubon2026
