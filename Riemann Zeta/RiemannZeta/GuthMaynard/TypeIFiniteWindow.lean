import RiemannZeta.GuthMaynard.FiniteScaleAssembly
import RiemannZeta.GuthMaynard.TypeIFiniteEstimates
import RiemannZeta.GuthMaynard.FiniteDensityEndpoint

open Finset Set

namespace RiemannZeta.GuthMaynard

/-- The height exponent of `T` relative to a positive finite block `N`.
This is the convention used by `classicalMHHExponent`: `T = N ^ τ`. -/
noncomputable def typeILogarithmicScale (T : ℝ) (N : ℕ) : ℝ :=
  Real.logb N T

/-- Exact conversion from the logarithmic scale back to the physical
height. -/
theorem rpow_typeILogarithmicScale_eq
    {T : ℝ} {N : ℕ} (hT : 0 < T) (hN : 1 < N) :
    (N : ℝ) ^ typeILogarithmicScale T N = T := by
  exact Real.rpow_logb (by exact_mod_cast (show 0 < N by omega))
    (by exact_mod_cast hN.ne') hT

/-- The endpoint MHH certificate applied to the actual physical scale. -/
theorem endpoint_mhh_at_physical_typeI_scale
    {σ τ₀ T : ℝ} {N : ℕ} (hcert : EndpointScaleCertificate σ τ₀)
    (hScaleNonneg : 0 ≤ typeILogarithmicScale T N)
    (hScaleUpper : typeILogarithmicScale T N ≤ τ₀ + σ - 1) :
    classicalMHHExponent σ (typeILogarithmicScale T N) ≤ 2 - 2 * σ :=
  hcert.mhh_window _ hScaleNonneg hScaleUpper

/-- The source normalization for a Type-I block of length `N`.  Multiplying
the coefficients `n⁻σ` by `N^σ` makes them uniformly bounded by one on
`(N,2N]`, while preserving coefficients independent of the ordinate. -/
noncomputable def normalizedClassicalTypeICoeff
    (C N : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (((N : ℝ) ^ σ : ℝ) : ℂ) * classicalZetaLongLineCoeff C σ n

/-- The normalized Type-I coefficients are genuinely unit bounded on the
dyadic block.  This is the normalization needed for the MHH exponent
`classicalMHHExponent σ τ`; applying MHH directly to `n⁻σ` at the unscaled
threshold loses the decisive factor `N^(2σ)`. -/
theorem norm_normalizedClassicalTypeICoeff_le_one
    (C N : ℕ) (σ : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ) :
    ∀ n ∈ dyadicInterval N, ‖normalizedClassicalTypeICoeff C N σ n‖ ≤ 1 := by
  intro n hn
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  unfold normalizedClassicalTypeICoeff classicalZetaLongLineCoeff
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
      Complex.norm_natCast_cpow_of_pos hnPos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.rpow_neg (by exact_mod_cast hnPos.le),
      ← div_eq_mul_inv, ← Real.div_rpow (Nat.cast_nonneg N)
        (by exact_mod_cast hnPos.le)]
    apply Real.rpow_le_one
    · positivity
    · exact (div_le_one (by exact_mod_cast hnPos)).2 (by exact_mod_cast hnData.1.le)
    · exact hσ
  · simp

/-- Normalizing the coefficients scales the whole finite Dirichlet
polynomial by the positive real factor `N^σ`. -/
theorem dirichletPoly_normalizedClassicalTypeICoeff
    (C N : ℕ) (σ t : ℝ) :
    dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t =
      (((N : ℝ) ^ σ : ℝ) : ℂ) *
        dirichletPoly N (classicalZetaLongLineCoeff C σ) t := by
  unfold dirichletPoly normalizedClassicalTypeICoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A large value of the actual sharp Type-I polynomial becomes a large
value at threshold `N^σ V` after source normalization. -/
theorem normalizedClassicalTypeICoeff_large
    (C N : ℕ) (σ t V : ℝ) (hN : 0 < N) (hLarge :
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    (N : ℝ) ^ σ * V ≤
      ‖dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t‖ := by
  rw [dirichletPoly_normalizedClassicalTypeICoeff, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact mul_le_mul_of_nonneg_left hLarge
    (Real.rpow_nonneg (by exact_mod_cast hN.le) _)

/-!
# Finite Type-I window resolution

The production dichotomy returns an actual sharp finite Dirichlet block,
not an unbounded Poisson series.  Its coefficients are independent of the
ordinate.  The source MHH exponent nevertheless requires the additional
normalization by `N^σ`; merely observing that `n⁻σ` is bounded by one gives a
strictly weaker estimate.  This module proves that normalization, the
epsilon-absorbed direct route, exact powered extraction, the weighted Weyl
route, and the endpoint package.  It stops before the later
multiplicity-weighted branch-to-slab reduction.
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

/-- Source-facing finite MHH consumer for the actual Type-I witness returned
by the dichotomy.  Unlike the epsilon-absorbed helper above, this exact form
uses the unrestricted theorem and retains its harmonic factor.  Consequently
it needs neither `N < T` nor a terminal-majorant premise. -/
theorem actual_typeI_dichotomy_witness_mhh_native :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
        0 ≤ σ → 0 < N → N < C → 2 ≤ T → 0 < V →
        T ^ δ ≤ T / 2 → IsSeparated 1 W →
        (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        (W.card : ℝ) ≤
          K * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / V ^ 2 +
              (3 * T) * min ((N : ℝ) / V ^ 2)
                ((N : ℝ) ^ 4 / V ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨K, hK, ?_⟩
  intro C N σ δ T V W hσ hN hNC hT hV hShift hSep hInterval hLarge
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
  exact hMHH N (3 * T) V W (classicalZetaLongLineCoeff C σ)
    hN (by linarith) hV
    (norm_classicalZetaLongLineCoeff_le_one C N σ hσ)
    hSep hBase hLarge

/-- Unrestricted MHH applied after the indispensable `N^σ` source
normalization.  The conclusion retains the harmonic factor, but its
threshold is the correctly normalized `N^σ V`; this is the form consumed
by the endpoint branch-to-slab theorem. -/
theorem actual_typeI_normalized_dichotomy_witness_mhh_native :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
        0 ≤ σ → 0 < N → 2 ≤ T → 0 < V →
        T ^ δ ≤ T / 2 → IsSeparated 1 W →
        (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        (W.card : ℝ) ≤
          K * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / ((N : ℝ) ^ σ * V) ^ 2 +
              (3 * T) * min
                ((N : ℝ) / ((N : ℝ) ^ σ * V) ^ 2)
                ((N : ℝ) ^ 4 / ((N : ℝ) ^ σ * V) ^ 6)) := by
  obtain ⟨K, hK, hMHH⟩ := classical_large_values_with_harmonic_unrestricted
  refine ⟨K, hK, ?_⟩
  intro C N σ δ T V W hσ hN hT hV hShift hSep hInterval hLarge
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
  have hThreshold : 0 < (N : ℝ) ^ σ * V := by positivity
  exact hMHH N (3 * T) ((N : ℝ) ^ σ * V) W
    (normalizedClassicalTypeICoeff C N σ) hN (by linarith) hThreshold
    (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
    hSep hBase (fun t ht =>
      normalizedClassicalTypeICoeff_large C N σ t V hN (hLarge t ht))

/-- The epsilon-absorbed MHH estimate for the actual enlarged-interval
Type-I witness, with the indispensable source normalization included.

The hypothesis `N ≤ 3T` is exactly the scale conclusion supplied by the
terminal Type-I step for a surviving witness.  It lets the proved MHH theorem
absorb the harmonic shell factor into `(3T)^ε`.  The large-value threshold is
`N^σ V`, so the three terms have the classical exponents
`N^(2-2σ)`, `N^(1-2σ)`, and `N^(4-6σ)` after elementary simplification. -/
theorem actual_typeI_dichotomy_witness_mhh_absorbed_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧
        ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
          0 ≤ σ → 0 < N → N < C → 2 ≤ T → 0 < V →
          T ^ δ ≤ T / 2 → (N : ℝ) ≤ 3 * T → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
          (∀ t ∈ W,
            V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
          (W.card : ℝ) ≤
            K * (3 * T) ^ ε *
              ((N : ℝ) ^ 2 / ((N : ℝ) ^ σ * V) ^ 2 +
                (3 * T) * min
                  ((N : ℝ) / ((N : ℝ) ^ σ * V) ^ 2)
                  ((N : ℝ) ^ 4 / ((N : ℝ) ^ σ * V) ^ 6)) := by
  intro ε hε
  obtain ⟨K, hK, hMHH⟩ := classical_montgomery_halasz_huxley_native ε hε
  refine ⟨K, hK, ?_⟩
  intro C N σ δ T V W hσ hN _hNC hT hV hShift hNT hSep hInterval hLarge
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
  have hThreshold : 0 < (N : ℝ) ^ σ * V := by positivity
  exact hMHH N (3 * T) ((N : ℝ) ^ σ * V) W
    (normalizedClassicalTypeICoeff C N σ) hN (by linarith) hNT hThreshold
    (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
    hSep hBase (fun t ht =>
      normalizedClassicalTypeICoeff_large C N σ t V hN (hLarge t ht))

/-- The powered route for the actual Type-I block.  The base polynomial is
first normalized by `N^σ`; exact finite powering and dyadic extraction then
produce a unit-coefficient block at one of the scales `2^r N^k`.  This is the
analytic realization of the two-or-three-fold raised-scale branch in
`EndpointScaleCertificate`, rather than merely its exponent arithmetic. -/
theorem powered_actual_typeI_block_large_values_bound
    (C N k : ℕ) (σ H V : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ) (hH : 1 ≤ H)
    (hV : 0 < V) (hSep : IsSeparated 1 W) (hBase : InBaseInterval H W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    ∀ η : ℝ, 0 < η →
      ∃ D : ℝ, 0 < D ∧
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let L := (((N : ℝ) ^ σ * V) ^ k /
              (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', L ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedClassicalTypeICoeff C N σ) 0 D η) t‖) ∧
          ∃ K : ℝ, 0 < K ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / L ^ 2 +
                  H * min ((Q : ℝ) / L ^ 2) ((Q : ℝ) ^ 4 / L ^ 6)) := by
  intro η hη
  have hLargeNormalized : ∀ t ∈ W,
      (N : ℝ) ^ σ * V ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N),
          normalizedClassicalTypeICoeff C N σ n *
            (n : ℂ) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            normalizedClassicalTypeICoeff C N σ n *
              (n : ℂ) ^ (-(0 + Complex.I * t)) =
          dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      ring
    rw [hEq]
    have hDirichlet := normalizedClassicalTypeICoeff_large
      C N σ t V hN (hLarge t ht)
    exact hDirichlet
  have hPowered := powered_unit_block_large_values_bound
    N k (normalizedClassicalTypeICoeff C N σ) 0 H
      ((N : ℝ) ^ σ * V) W hN hk (by norm_num) hH (by positivity)
      (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
      hSep hBase hLargeNormalized η hη
  simpa only [Real.rpow_zero, one_mul] using hPowered

/-- Uniform-constant powered Type-I estimate.  For fixed `k` and `η`, the
coefficient normalization and MHH constants precede every actual detector
scale and witness family. -/
theorem powered_actual_typeI_block_large_values_bound_uniform
    (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (C N : ℕ) (σ H V : ℝ) (W : Finset ℝ),
        0 < N → 0 < k → 0 ≤ σ → 1 ≤ H → 0 < V →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let L := (((N : ℝ) ^ σ * V) ^ k /
              (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', L ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedClassicalTypeICoeff C N σ) 0 D η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / L ^ 2 +
                H * min ((Q : ℝ) / L ^ 2)
                  ((Q : ℝ) ^ 4 / L ^ 6)) := by
  obtain ⟨D, hD, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_uniform k η hη
  refine ⟨D, hD, K, hK, ?_⟩
  intro C N σ H V W hN hk hσ hH hV hSep hBase hLarge
  have hLargeNormalized : ∀ t ∈ W,
      (N : ℝ) ^ σ * V ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N),
          normalizedClassicalTypeICoeff C N σ n *
            (n : ℂ) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            normalizedClassicalTypeICoeff C N σ n *
              (n : ℂ) ^ (-(0 + Complex.I * t)) =
          dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      ring
    rw [hEq]
    exact normalizedClassicalTypeICoeff_large C N σ t V hN
      (hLarge t ht)
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered N (normalizedClassicalTypeICoeff C N σ) 0 H
      ((N : ℝ) ^ σ * V) W hN hk (by norm_num) hH (by positivity)
      (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
      hSep hBase hLargeNormalized
  refine ⟨r, hr, W', hW', hCard, hSep', hBase', ?_, ?_⟩
  · simpa only [Real.rpow_zero, one_mul] using hLarge'
  · simpa only [Real.rpow_zero, one_mul] using hBound

/-- Bounded-power uniform form of the actual Type-I powered route. -/
theorem powered_actual_typeI_block_large_values_bound_bounded_uniform
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 1 ≤ D ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k C N : ℕ) (σ H V : ℝ) (W : Finset ℝ),
        0 < k → k ≤ B → 0 < N → 0 ≤ σ → 1 ≤ H → 0 < V →
        IsSeparated 1 W → InBaseInterval H W →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let L := (((N : ℝ) ^ σ * V) ^ k /
              (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', L ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedClassicalTypeICoeff C N σ) 0 D η) t‖) ∧
          (W'.card : ℝ) ≤
            K * (1 + (((harmonic Q : ℚ) : ℝ))) *
              ((Q : ℝ) ^ 2 / L ^ 2 +
                H * min ((Q : ℝ) / L ^ 2)
                  ((Q : ℝ) ^ 4 / L ^ 6)) := by
  obtain ⟨D, hD, K, hK, hPowered⟩ :=
    powered_unit_block_large_values_bound_bounded_uniform B η hη
  refine ⟨D, hD, K, hK, ?_⟩
  intro k C N σ H V W hk hkB hN hσ hH hV hSep hBase hLarge
  have hLargeNormalized : ∀ t ∈ W,
      (N : ℝ) ^ σ * V ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N),
          normalizedClassicalTypeICoeff C N σ n *
            (n : ℂ) ^ (-(0 + Complex.I * t))‖ := by
    intro t ht
    have hEq :
        ∑ n ∈ Finset.Ioc N (2 * N),
            normalizedClassicalTypeICoeff C N σ n *
              (n : ℂ) ^ (-(0 + Complex.I * t)) =
          dirichletPoly N (normalizedClassicalTypeICoeff C N σ) t := by
      unfold dirichletPoly dyadicInterval
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      ring
    rw [hEq]
    exact normalizedClassicalTypeICoeff_large C N σ t V hN (hLarge t ht)
  obtain ⟨r, hr, W', hW', hCard, hSep', hBase', hLarge', hBound⟩ :=
    hPowered k N (normalizedClassicalTypeICoeff C N σ) 0 H
      ((N : ℝ) ^ σ * V) W hk hkB hN (by norm_num) hH (by positivity)
      (norm_normalizedClassicalTypeICoeff_le_one C N σ hN hσ)
      hSep hBase hLargeNormalized
  refine ⟨r, hr, W', hW', hCard, hSep', hBase', ?_, ?_⟩
  · simpa only [Real.rpow_zero, one_mul] using hLarge'
  · simpa only [Real.rpow_zero, one_mul] using hBound

/-- The exact direct-route obligation for an actual Type-I dichotomy witness,
after the source normalization and harmonic-loss absorption. -/
def ActualTypeIAbsorbedMHH : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ (C N : ℕ) (σ δ T V : ℝ) (W : Finset ℝ),
        0 ≤ σ → 0 < N → N < C → 2 ≤ T → 0 < V →
        T ^ δ ≤ T / 2 → (N : ℝ) ≤ 3 * T → IsSeparated 1 W →
        (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) →
        (∀ t ∈ W,
          V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
        (W.card : ℝ) ≤
          K * (3 * T) ^ ε *
            ((N : ℝ) ^ 2 / ((N : ℝ) ^ σ * V) ^ 2 +
              (3 * T) * min
                ((N : ℝ) / ((N : ℝ) ^ σ * V) ^ 2)
                ((N : ℝ) ^ 4 / ((N : ℝ) ^ σ * V) ^ 6))

theorem actual_typeI_absorbed_mhh_native : ActualTypeIAbsorbedMHH :=
  actual_typeI_dichotomy_witness_mhh_absorbed_native

/-- The exact powered-route obligation for the normalized actual Type-I
block. -/
def ActualTypeIPoweredRoute : Prop :=
  ∀ (C N k : ℕ) (σ H V : ℝ) (W : Finset ℝ),
    0 < N → 0 < k → 0 ≤ σ → 1 ≤ H → 0 < V →
    IsSeparated 1 W → InBaseInterval H W →
    (∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) →
    ∀ η : ℝ, 0 < η →
      ∃ D : ℝ, 0 < D ∧
        ∃ r ∈ Finset.range k, ∃ W' ⊆ W,
          let Q := 2 ^ r * N ^ k
          let L := (((N : ℝ) ^ σ * V) ^ k /
              (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k
          (W.card : ℝ) ≤ k * (W'.card : ℝ) ∧
          IsSeparated 1 W' ∧ InBaseInterval H W' ∧
          (∀ t ∈ W', L ≤
            ‖dirichletPoly Q
              (normalizedFinitePoweredCoeffs N k
                (normalizedClassicalTypeICoeff C N σ) 0 D η) t‖) ∧
          ∃ K : ℝ, 0 < K ∧
            (W'.card : ℝ) ≤
              K * (1 + (((harmonic Q : ℚ) : ℝ))) *
                ((Q : ℝ) ^ 2 / L ^ 2 +
                  H * min ((Q : ℝ) / L ^ 2) ((Q : ℝ) ^ 4 / L ^ 6))

theorem actual_typeI_powered_route_native : ActualTypeIPoweredRoute := by
  intro C N k σ H V W hN hk hσ hH hV hSep hBase hLarge
  exact powered_actual_typeI_block_large_values_bound
    C N k σ H V W hN hk hσ hH hV hSep hBase hLarge

/-- The exceptional short-polynomial route uses the already proved weighted
Weyl estimate with its genuine `n⁻σ` amplitude. -/
def ActualTypeIWeylRoute : Prop :=
  ∀ (σ Y : ℝ) (A N : ℕ), 0 ≤ σ → 1 ≤ Y → 0 < A → 0 < N →
    Y ≤ A → (A : ℝ) ^ 2 ≤ Y ^ 3 → N ≤ A →
    ‖weightedWeylBlock σ (Y ^ 3) A N‖ ≤
      (A : ℝ) ^ (-σ) * (30 * Real.sqrt ((A : ℝ) * Y))

theorem actual_typeI_weyl_route_native : ActualTypeIWeylRoute := by
  intro σ Y A N hσ hY hA hN hYA hAY hNA
  exact norm_weightedWeylBlock_le σ Y A N hσ hY hA hN hYA hAY hNA

/-- The complete finite Type-I branch package before the later
multiplicity-weighted branch-to-slab reduction.  It contains the corrected
normalization and epsilon-absorbed direct MHH route, the actual powered
two/three-fold route, the weighted Weyl route, and both exhaustive endpoint
scale certificates. -/
def ActualTypeIBranchResolution : Prop :=
  ActualTypeIAbsorbedMHH ∧ ActualTypeIPoweredRoute ∧
    ActualTypeIWeylRoute ∧ ClassicalFiniteScaleExponentAssembly

theorem actual_typeI_branch_resolution_native : ActualTypeIBranchResolution := by
  exact ⟨actual_typeI_absorbed_mhh_native,
    actual_typeI_powered_route_native, actual_typeI_weyl_route_native,
    classical_finite_scale_exponent_assembly_native⟩

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
