import RiemannZeta.GuthMaynard.FiniteScaleAssembly
import RiemannZeta.GuthMaynard.TypeIFiniteEstimates

open Finset Set

namespace RiemannZeta.GuthMaynard

/-!
# Finite Type-I window resolution

The production dichotomy returns an actual sharp finite Dirichlet block,
not an unbounded Poisson series.  Its coefficients are independent of the
ordinate and have norm at most one.  Consequently the already proved finite
Montgomery--Halasz--Huxley theorem can be applied once the dichotomy consumer
has supplied its physical scale, interval, and terminal-majorant hypotheses.
The theorems below provide the generic MHH step, certificate projections, and
the enlarged-interval normalization.  They do not themselves unpack the
dichotomy or close the Type-I branch.

This module records the finite cardinality theorem and endpoint-scale
certificate separately.  It stops before the actual dichotomy consumer and
the later multiplicity-weighted branch-to-slab reduction.
-/

/-- Every field of an endpoint scale certificate, exposed as the four
exhaustive dispatch rules consumed by the finite density reduction. -/
theorem typeIEndpointScaleDispatch_native
    {σ τ₀ : ℝ} (hcert : EndpointScaleCertificate σ τ₀) :
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₀ + σ - 1 →
      classicalMHHExponent σ τ ≤ 2 - 2 * σ) ∧
    (∀ τ : ℝ, 2 * τ₀ / 3 ≤ τ → τ ≤ τ₀ →
      corollary1110Envelope σ τ₀ τ ≤ (3 - 3 * σ) * τ / τ₀) ∧
    (∀ τ : ℝ, 4 * τ₀ / 3 ≤ τ → τ ≤ 8 * τ₀ / 3 →
      (2 * τ₀ / 3 ≤ τ / 2 ∧ τ / 2 ≤ τ₀) ∨
        (2 * τ₀ / 3 ≤ τ / 3 ∧ τ / 3 ≤ τ₀)) ∧
    (∀ τ : ℝ, 2 ≤ τ → τ < 4 * τ₀ / 3 →
      False ∨ τ < 6 * σ - 3) := by
  exact ⟨hcert.mhh_window, hcert.subdivision_window,
    hcert.raised_scale_window, hcert.zeta_window⟩

/-- A generic Type-I finite-window helper.  For every separately supplied
sharp Type-I witness family, this theorem proves the finite MHH cardinality
bound and separately certifies that a supplied logarithmic scale lies under
the endpoint MHH exponent whenever it is in the basic endpoint window.

No stationary-phase hypothesis occurs in the signature: the coefficient-
uniform MHH theorem is stronger than the zeta-only large-values lemma for
which ANTEDB uses smooth reflection. -/
theorem typeI_finite_window_resolution_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧
        ∀ (C N : ℕ) (σ τ₀ τ T V : ℝ) (W : Finset ℝ),
          EndpointScaleCertificate σ τ₀ →
          0 ≤ τ → τ ≤ τ₀ + σ - 1 →
          0 ≤ σ → 0 < N → N < C → 1 ≤ T → 0 < V →
          W.Nonempty → IsSeparated 1 W → InBaseInterval T W →
          (∀ t ∈ W, 1 ≤ t) →
          (∀ t ∈ W,
            V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
          (∀ t ∈ W,
            (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) →
          (W.card : ℝ) ≤
              K * T ^ ε *
                ((N : ℝ) ^ 2 / V ^ 2 +
                  T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) ∧
            classicalMHHExponent σ τ ≤ 2 - 2 * σ := by
  intro ε hε
  obtain ⟨K, hK, hlarge⟩ := typeIClassicalLargeValues_native ε hε
  refine ⟨K, hK, ?_⟩
  intro C N σ τ₀ τ T V W hcert hτNonneg hτUpper hσ hN hNC hT hV
    hW hSep hBase hOne hLarge hMajorant
  exact ⟨hlarge C N σ T V W hσ hN hNC hT hV hW hSep hBase
      hOne hLarge hMajorant,
    hcert.mhh_window τ hτNonneg hτUpper⟩

/-- The actual interval-normalization and MHH consumer for a Type-I witness
returned by `ClassicalTypeITypeIIDichotomyConclusion`.  Unlike the generic
helper above, its ordinate hypothesis is exactly the enlarged interval in the
dichotomy, and the proof derives the common base interval `[1,3T]`.

The terminal-majorant comparison remains explicit because its discharge is a
separate endpoint-scale obligation; this theorem must not be described as the
complete Type-I branch resolution. -/
theorem typeI_dichotomy_witness_mhh_bound_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧
        ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
          0 ≤ σ → 0 < N → N < C → 2 ≤ T → 0 < V →
          T ^ δ ≤ T / 2 → W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
          (∀ t ∈ W,
            V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
          (∀ t ∈ W,
            (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) →
          (W.card : ℝ) ≤
            K * (3 * T) ^ ε *
              ((N : ℝ) ^ 2 / V ^ 2 +
                (3 * T) * min ((N : ℝ) / V ^ 2)
                  ((N : ℝ) ^ 4 / V ^ 6)) := by
  intro ε hε
  obtain ⟨K, hK, hlarge⟩ := typeIClassicalLargeValues_native ε hε
  refine ⟨K, hK, ?_⟩
  intro C N σ δ T V W hσ hN hNC hT hV hShift hW hSep hInterval
    hLarge hMajorant
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    rw [Set.mem_Icc]
    have htRange := hInterval t ht
    constructor
    · calc
        (0 : ℝ) ≤ T / 2 := by linarith
        _ ≤ T - T ^ δ := by linarith
        _ ≤ t := htRange.1
    · calc
        t ≤ 2 * T + T ^ δ := htRange.2
        _ ≤ 3 * T := by linarith
  have hOne : ∀ t ∈ W, (1 : ℝ) ≤ t := by
    intro t ht
    have htRange := hInterval t ht
    calc
      (1 : ℝ) ≤ T / 2 := by linarith
      _ ≤ T - T ^ δ := by linarith
      _ ≤ t := htRange.1
  exact hlarge C N σ (3 * T) V W hσ hN hNC (by linarith) hV hW
    hSep hBase hOne hLarge hMajorant

/-- Ingham specialization of the endpoint-certificate projection.
This does not consume a Type-I dichotomy witness. -/
theorem ingham_typeI_finite_window_resolution_native
    {σ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1) :
    EndpointScaleCertificate σ (2 - σ) ∧
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ (2 - σ) + σ - 1 →
        classicalMHHExponent σ τ ≤ 2 - 2 * σ) := by
  have hcert := ingham_endpoint_scale_certificate hσLower hσUpper
  exact ⟨hcert, hcert.mhh_window⟩

/-- Huxley specialization of the endpoint-certificate projection.
This does not consume a Type-I dichotomy witness. -/
theorem huxley_typeI_finite_window_resolution_native
    {σ : ℝ} (hσLower : 3 / 4 < σ) (hσUpper : σ < 1) :
    EndpointScaleCertificate σ (3 * σ - 1) ∧
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ (3 * σ - 1) + σ - 1 →
        classicalMHHExponent σ τ ≤ 2 - 2 * σ) := by
  have hcert := huxley_endpoint_scale_certificate hσLower hσUpper
  exact ⟨hcert, hcert.mhh_window⟩

end RiemannZeta.GuthMaynard
