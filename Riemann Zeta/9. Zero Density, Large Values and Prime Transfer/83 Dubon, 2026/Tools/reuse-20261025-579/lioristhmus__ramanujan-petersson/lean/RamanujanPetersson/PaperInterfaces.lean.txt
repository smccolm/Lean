import Mathlib

namespace RamanujanPetersson

/--
Abstract placeholder for the algebraic closure `\overline{\mathbf{Q}}` appearing in the
paper-facing statements.
-/
axiom Qbar : Type

/--
Abstract placeholder for embeddings `\overline{\mathbf{Q}} \hookrightarrow \mathbf{C}`.
-/
axiom QbarEmbedding : Type

/--
Interpret an abstract algebraic number through a chosen embedding into `ℂ`.
-/
axiom embedQbar : QbarEmbedding → Qbar → ℂ

/--
A distinguished embedding used to present paper-facing complex-valued statements.
-/
axiom chosenEmbedding : Qbar → ℂ

/--
Index of the distinguished embedding `chosenEmbedding`.
-/
axiom chosenEmbeddingIndex : QbarEmbedding

/--
The distinguished embedding agrees with evaluation at `chosenEmbeddingIndex`.
-/
axiom chosenEmbedding_agrees :
    ∀ x : Qbar, embedQbar chosenEmbeddingIndex x = chosenEmbedding x

/--
Abstract placeholder for the absolute Galois group of `ℚ`.
-/
axiom GQ : Type

/--
Abstract target type for an `ℓ`-adic representation.
-/
axiom RepObj : ℕ → Type

/--
Predicate asserting continuity of an abstract Galois representation.
-/
axiom ContinuousRep : {ℓ : ℕ} → (GQ → RepObj ℓ) → Prop

/--
Predicate asserting semisimplicity of an abstract Galois representation.
-/
axiom SemisimpleRep : {ℓ : ℕ} → (GQ → RepObj ℓ) → Prop

/--
`UnramifiedOutside rho N` packages the statement that `rho` is unramified outside the
level parameter `N`.
-/
axiom UnramifiedOutside : {ℓ : ℕ} → (GQ → RepObj ℓ) → ℕ → Prop

/--
Abstract local characteristic-polynomial relation for Frobenius at a prime `p`.
The last natural-number argument is included as a paper-facing arithmetic parameter,
for example a weight or level quantity depending on the application.
-/
axiom LocalCharacteristicPolynomial :
    {ℓ : ℕ} → (GQ → RepObj ℓ) → ℕ → ℂ → ℂ → ℕ → Prop

/--
Abstract Frobenius trace attached to a representation at a prime `p`.
-/
axiom TraceAtFrob : {ℓ : ℕ} → (GQ → RepObj ℓ) → ℕ → ℂ

/--
Abstract Frobenius determinant attached to a representation at a prime `p`.
-/
axiom DetAtFrob : {ℓ : ℕ} → (GQ → RepObj ℓ) → ℕ → ℂ

/--
A paper-facing package for the local Hecke roots above `p`: the roots themselves live in
`Qbar`, and the chosen complex embedding recovers the usual sum/product formulas.
-/
structure HeckeRootPair (aₚ χp : ℂ) (p k : ℕ) where
  /-- First algebraic Hecke root. -/
  alpha : Qbar
  /-- Second algebraic Hecke root. -/
  beta : Qbar
  /-- Chosen-complex realization of the trace relation. -/
  chosen_sum : chosenEmbedding alpha + chosenEmbedding beta = aₚ
  /-- Chosen-complex realization of the determinant relation. -/
  chosen_prod : chosenEmbedding alpha * chosenEmbedding beta = χp * (p : ℂ) ^ (k - 1)

/--
Input package for the purity statement. It records the paper-facing parameters `aₚ`, `χp`,
`p`, `k`, and `N`, together with a chosen algebraic root pair and the purity equalities
for every complex embedding of `Qbar`.
-/
structure PurityInput (aₚ χp : ℂ) (p k N : ℕ) where
  /-- Chosen algebraic Hecke roots with the paper's sum/product identities. -/
  roots : HeckeRootPair aₚ χp p k
  /-- Primality of `p`. -/
  prime_p : Nat.Prime p
  /-- The prime `p` does not divide the level `N`. -/
  p_not_dvd_level : ¬ p ∣ N
  /-- Purity for every embedding, matching the paper's archimedean statement. -/
  purity : ∀ σ : QbarEmbedding,
      ‖embedQbar σ roots.alpha‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2) ∧
      ‖embedQbar σ roots.beta‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)

/--
Abstract paper-facing input for Deligne's Galois-representation package. This packages the
kind of hypotheses supplied by Theorem 3.1 / Appendix A: an `ℓ`-adic representation with
continuity, semisimplicity, unramifiedness, and local Frobenius-polynomial data.
-/
structure DeligneInput where
  /-- Auxiliary prime indexing the representation. -/
  ℓ : ℕ
  /-- Level parameter outside which the representation is unramified. -/
  N : ℕ
  /-- Weight or analogous arithmetic parameter used by the local polynomial package. -/
  weight : ℕ
  /-- The abstract Galois representation. -/
  rho : GQ → RepObj ℓ
  /-- Continuity hypothesis. -/
  continuous : ContinuousRep rho
  /-- Semisimplicity hypothesis. -/
  semisimple : SemisimpleRep rho
  /-- Unramifiedness outside the level. -/
  unramifiedOutside : UnramifiedOutside rho N
  /-- Local characteristic-polynomial package at primes. -/
  localCharacteristicPolynomial :
    ∀ p : ℕ,
      LocalCharacteristicPolynomial rho p (TraceAtFrob rho p) (DetAtFrob rho p) weight

/--
Input package for the prime-power step. This keeps the paper-facing coefficient function,
the parameters `p`, `k`, `N`, and a chosen root package, while also storing enough witness
fields to reconnect with the existing witness-form prime-power theorem in later layers.
-/
structure PrimePowerInput where
  /-- Fourier-coefficient function from the paper-facing statement. -/
  a : ℕ → ℂ
  /-- Prime entering the prime-power term. -/
  p : ℕ
  /-- Weight parameter from the paper. -/
  k : ℕ
  /-- Level parameter from the paper. -/
  N : ℕ
  /-- The paper-facing coefficient `a_p`. -/
  aₚ : ℂ
  /-- The nebentypus value `χ(p)` in complex form. -/
  χp : ℂ
  /-- Chosen algebraic Hecke roots at `p`. -/
  roots : HeckeRootPair aₚ χp p k
  /-- Purity package attached to the same root data. -/
  purityInput : PurityInput aₚ χp p k N
  /-- Compatibility between the local root package and the purity witness package. -/
  roots_eq : roots = purityInput.roots
  /-- Primality of `p`. -/
  prime_p : Nat.Prime p
  /-- The prime `p` does not divide the level `N`. -/
  p_not_dvd_level : ¬ p ∣ N
  /-- Identifies the paper-facing symbol `a_p` with the coefficient function. -/
  coeffAtPrime : a p = aₚ
  /-- Prime-power coefficient formula in the chosen complex embedding. -/
  coeffFormula : ∀ m : ℕ,
      a (p ^ m) = ∑ j ∈ Finset.range (m + 1),
        chosenEmbedding roots.alpha ^ j * chosenEmbedding roots.beta ^ (m - j)

/--
Input package for the coprime-index step. The theorem statement remains the paper's bound
for coefficients at indices coprime to `N`; the helper fields merely package the standard
multiplicativity and divisor-arithmetic ingredients used in Corollary 5.3.
-/
structure CoprimeIndexInput where
  /-- Fourier-coefficient function from the paper-facing statement. -/
  a : ℕ → ℂ
  /-- General index whose coefficient is being estimated. -/
  n : ℕ
  /-- Level parameter. -/
  N : ℕ
  /-- Weight parameter. -/
  k : ℕ
  /-- The index `n` is coprime to the level `N`. -/
  coprime_level : Nat.Coprime n N
  /-- Helper package for the standard multiplicative factorization step. -/
  factorizationFormula : Prop
  /-- Helper package for the prime-power bounds inserted into that factorization. -/
  primePowerBound : Prop
  /-- Helper package for the divisor-count identity used in Corollary 5.3. -/
  divisorCountFormula : Prop
  /-- Helper package for collapsing the archimedean factors to a power of `n`. -/
  archimedeanPowerFormula : Prop

end RamanujanPetersson
