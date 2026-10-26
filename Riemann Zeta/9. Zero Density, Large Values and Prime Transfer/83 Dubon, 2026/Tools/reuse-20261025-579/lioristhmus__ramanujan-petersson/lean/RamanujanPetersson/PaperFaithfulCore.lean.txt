import Mathlib
import RamanujanPetersson.PaperInterfaces
import RamanujanPetersson.Autoformalized
import RamanujanPetersson.Theorem41
import RamanujanPetersson.Theorem21
import RamanujanPetersson.Theorem31
import RamanujanPetersson.Corollary53
import RamanujanPetersson.Corollary53Coprime

open scoped BigOperators

namespace RamanujanPetersson

/--
Paper-facing packaging of the local consequence extracted from Theorem 3.1.

This layer does not construct Deligne's representation; it only repackages the
abstract representation-level hypotheses and the resulting trace/determinant data
into a single existential statement.
-/
theorem theorem31_paperFaithful
    {ℓ N p k : ℕ} {ρ : GQ → RepObj ℓ} {aₚ χp : ℂ}
    (hcont : ContinuousRep ρ)
    (hsemi : SemisimpleRep ρ)
    (hunram : UnramifiedOutside ρ (N * ℓ))
    (hlocal : LocalCharacteristicPolynomial ρ p aₚ χp k)
    (htrace : TraceAtFrob ρ p = aₚ)
    (hdet : DetAtFrob ρ p = χp * (p : ℂ) ^ (k - 1)) :
    ∃ ρ' : GQ → RepObj ℓ,
      ContinuousRep ρ' ∧
      SemisimpleRep ρ' ∧
      UnramifiedOutside ρ' (N * ℓ) ∧
      LocalCharacteristicPolynomial ρ' p aₚ χp k ∧
      TraceAtFrob ρ' p = aₚ ∧
      DetAtFrob ρ' p = χp * (p : ℂ) ^ (k - 1) := by
  refine ⟨ρ, hcont, hsemi, hunram, hlocal, htrace, hdet⟩

/--
Paper-facing form of the purity package used in Theorem 4.1.

The deep arithmetic input is kept abstract: the theorem simply records that once
one has algebraic Hecke roots with the chosen-embedding sum/product identities and
purity for every complex embedding, these data can be packaged as a single
existential paper-facing root pair.
-/
theorem theorem41_paperFaithful
    {αₚ βₚ : Qbar} {aₚ χp : ℂ} {p k : ℕ}
    (hsum : chosenEmbedding αₚ + chosenEmbedding βₚ = aₚ)
    (hprod : chosenEmbedding αₚ * chosenEmbedding βₚ = χp * (p : ℂ) ^ (k - 1))
    (hpurity : ∀ σ : QbarEmbedding,
      ‖embedQbar σ αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
      ‖embedQbar σ βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ∃ α' β' : Qbar,
      chosenEmbedding α' + chosenEmbedding β' = aₚ ∧
      chosenEmbedding α' * chosenEmbedding β' = χp * (p : ℂ) ^ (k - 1) ∧
      ∀ σ : QbarEmbedding,
        ‖embedQbar σ α'‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
        ‖embedQbar σ β'‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  refine ⟨αₚ, βₚ, hsum, hprod, ?_⟩
  intro σ
  exact hpurity σ

/--
Paper-facing deduction of Theorem 2.1 from the abstract purity package.

As in the paper, the proof only uses the chosen-embedding sum formula together
with the purity equalities at the distinguished embedding.
-/
theorem theorem21_paperFaithful
    {αₚ βₚ : Qbar} {aₚ χp : ℂ} {p k N : ℕ}
    (hsum : chosenEmbedding αₚ + chosenEmbedding βₚ = aₚ)
    (hprod : chosenEmbedding αₚ * chosenEmbedding βₚ = χp * (p : ℂ) ^ (k - 1))
    (hpurity : ∀ σ : QbarEmbedding,
      ‖embedQbar σ αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
      ‖embedQbar σ βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖aₚ‖ ≤ 2 * (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  let _ := hprod
  let _ := N
  have hchosen := hpurity chosenEmbeddingIndex
  rcases hchosen with ⟨hα, hβ⟩
  have hα' : ‖chosenEmbedding αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
    simpa [chosenEmbedding_agrees] using hα
  have hβ' : ‖chosenEmbedding βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
    simpa [chosenEmbedding_agrees] using hβ
  have ha : aₚ = chosenEmbedding αₚ + chosenEmbedding βₚ := by
    simpa using hsum.symm
  simpa using witnessSqueeze ha hα' hβ'

/--
Paper-facing prime-power clause of Corollary 5.3.

The proof reuses the existing witness-form estimate after specializing the purity
hypothesis to the distinguished complex embedding.
-/
theorem corollary53_primePowers_paperFaithful
    {a : ℕ → ℂ} {αₚ βₚ : Qbar} {p k N : ℕ}
    (hp : Nat.Prime p)
    (hpnmidN : ¬ p ∣ N)
    (hsum : chosenEmbedding αₚ + chosenEmbedding βₚ = a p)
    (hprod : chosenEmbedding αₚ * chosenEmbedding βₚ = 1 * (p : ℂ) ^ (k - 1))
    (hpurity : ∀ σ : QbarEmbedding,
      ‖embedQbar σ αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
      ‖embedQbar σ βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2))
    (coeffFormula : ∀ m : ℕ,
      a (p ^ m) = ∑ j ∈ Finset.range (m + 1),
        chosenEmbedding αₚ ^ j * chosenEmbedding βₚ ^ (m - j)) :
    ∀ m : ℕ, ‖a (p ^ m)‖ ≤ (m + 1) * ((p : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ m := by
  let _ := hsum
  let _ := hprod
  have hchosen := hpurity chosenEmbeddingIndex
  rcases hchosen with ⟨hα, hβ⟩
  have hα' : ‖chosenEmbedding αₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
    simpa [chosenEmbedding_agrees] using hα
  have hβ' : ‖chosenEmbedding βₚ‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) := by
    simpa [chosenEmbedding_agrees] using hβ
  intro m
  exact corollary53_primePowers_witnessForm hp hpnmidN (coeffFormula m) hα' hβ'

/--
Paper-facing coprime-index clause of Corollary 5.3.

This keeps the factorization and arithmetic identities abstract but packages them in
terms of the actual prime factors of `n`, so the conclusion matches the statement in
the paper-facing layer.
-/
theorem corollary53_coprimeIndices_paperFaithful
    {a : ℕ → ℂ} {n N k : ℕ}
    (hn : n ≠ 0)
    (hnCoprime : Nat.Coprime n N)
    (factorizationFormula :
      a n = ∏ p ∈ n.primeFactors, a (p ^ n.factorization p))
    (primePowerBoundOnSupport :
      ∀ p ∈ n.primeFactors,
        ‖a (p ^ n.factorization p)‖ ≤
          (n.factorization p + 1 : ℝ) *
            (((p : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (n.factorization p)))
    (divisorCountFormula :
      (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (n.factorization p + 1 : ℝ))
    (archimedeanPowerFormula :
      ∏ p ∈ n.primeFactors, (((p : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (n.factorization p)) =
        (n : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖a n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  let _ := hn
  simpa using
    (corollary53_coprimeIndices_witnessForm
      (a := a n) (n := n) (N := N) (k := k) (d := n.divisors.card)
      (s := n.primeFactors)
      (apow := fun p => a (p ^ n.factorization p))
      (p := fun p => p)
      (m := fun p => n.factorization p)
      hnCoprime factorizationFormula primePowerBoundOnSupport
      divisorCountFormula archimedeanPowerFormula)

end RamanujanPetersson
