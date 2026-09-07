import GafniTao.HeathBrownAtkinsonLemma71Physical

/-!
# Radical extraction in Ivić equation (7.25)

The two non-diagonal radicals in the physical Lemma 7.1 are factored into
the cardinality, coefficient, and logarithmic pieces used by the source.
The statements keep `K + 1` and the exact Atkinson coefficient; replacing
those by dyadic monomials is a later, separately audited scale step.
-/

namespace GafniTao

noncomputable section

/-- The exponent-pair radical is linear in the selected cardinality and
contains the square root of the literal equation-(7.19) coefficient. -/
theorem heathBrownAtkinson_exponentPair_radical_le
    {T J : ℝ} {K R : ℕ} (hT : 0 < T) (hK : 1 ≤ K) :
    Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
          ((R : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K)) ≤
      2 * (R : ℝ) * Real.sqrt (K : ℝ) *
        (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
          Real.sqrt (heathBrownAtkinsonSourceFirstCoefficient T J K) := by
  let L : ℝ := 1 + Real.log (2 * K : ℕ)
  let F : ℝ := heathBrownAtkinsonSourceFirstCoefficient T J K
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hL : 1 ≤ L := by
    dsimp only [L]
    have htwoK : (1 : ℝ) ≤ (2 * K : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * K)
    linarith [Real.log_nonneg htwoK]
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact heathBrownAtkinsonSourceFirstCoefficient_nonneg hT
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hright :
      0 ≤ 2 * (R : ℝ) * Real.sqrt (K : ℝ) * L ^ (2 : ℕ) *
        Real.sqrt F := by positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨hright, ?_⟩
  unfold heathBrownAtkinsonLogEnergy
  change
    ((2 * K : ℕ) : ℝ) * L ^ (3 : ℕ) * (R : ℝ) *
        ((R : ℝ) * F) ≤
      (2 * (R : ℝ) * Real.sqrt (K : ℝ) * L ^ (2 : ℕ) *
        Real.sqrt F) ^ (2 : ℕ)
  have hsqrtK : Real.sqrt (K : ℝ) ^ (2 : ℕ) = (K : ℝ) :=
    Real.sq_sqrt hKreal.le
  have hsqrtF : Real.sqrt F ^ (2 : ℕ) = F := Real.sq_sqrt hF
  rw [mul_pow, mul_pow, mul_pow, hsqrtK, hsqrtF]
  push_cast
  have hL3 : 0 ≤ L ^ (3 : ℕ) := by positivity
  have hfactor : 2 * L ^ (3 : ℕ) ≤ 4 * L ^ (4 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hL hL3
    nlinarith
  have hscale : 0 ≤ (R : ℝ) ^ (2 : ℕ) * (K : ℝ) * F := by positivity
  have := mul_le_mul_of_nonneg_right hfactor hscale
  nlinarith

/-- The reciprocal-spacing radical has the source powers before replacing
`K+1` by its dyadic upper bound.  Its last factor is exactly `sqrt(log T/G)`,
so the sign and the physical spacing denominator remain visible. -/
theorem heathBrownAtkinson_reciprocal_radical_le
    {T G : ℝ} {K R : ℕ} (hT : 2 ≤ T) (hG : 0 < G) (hK : 1 ≤ K) :
    Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
          (224 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) / G *
            Real.log T)) ≤
      32 * Real.sqrt (K : ℝ) * Real.sqrt (R : ℝ) *
        (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
        Real.sqrt (Real.sqrt (T * ((K + 1 : ℕ) : ℝ))) *
        Real.sqrt (Real.log T / G) := by
  let L : ℝ := 1 + Real.log (2 * K : ℕ)
  let S : ℝ := Real.sqrt (T * ((K + 1 : ℕ) : ℝ))
  let A : ℝ := Real.log T / G
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have hL : 1 ≤ L := by
    dsimp only [L]
    have htwoK : (1 : ℝ) ≤ (2 * K : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * K)
    linarith [Real.log_nonneg htwoK]
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hright :
      0 ≤ 32 * Real.sqrt (K : ℝ) * Real.sqrt (R : ℝ) * L ^ (2 : ℕ) *
        Real.sqrt S * Real.sqrt A := by positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨hright, ?_⟩
  unfold heathBrownAtkinsonLogEnergy
  change
    ((2 * K : ℕ) : ℝ) * L ^ (3 : ℕ) * (R : ℝ) *
        (224 * S / G * Real.log T) ≤
      (32 * Real.sqrt (K : ℝ) * Real.sqrt (R : ℝ) * L ^ (2 : ℕ) *
        Real.sqrt S * Real.sqrt A) ^ (2 : ℕ)
  have hsource : 224 * S / G * Real.log T = 224 * S * A := by
    dsimp only [A]
    ring
  rw [hsource]
  have hsqrtK : Real.sqrt (K : ℝ) ^ (2 : ℕ) = (K : ℝ) :=
    Real.sq_sqrt hKreal.le
  have hsqrtR : Real.sqrt (R : ℝ) ^ (2 : ℕ) = (R : ℝ) :=
    Real.sq_sqrt hR
  have hsqrtS : Real.sqrt S ^ (2 : ℕ) = S := Real.sq_sqrt hS
  have hsqrtA : Real.sqrt A ^ (2 : ℕ) = A := Real.sq_sqrt hA
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hsqrtK, hsqrtR, hsqrtS,
    hsqrtA]
  push_cast
  have hL3 : 0 ≤ L ^ (3 : ℕ) := by positivity
  have hfactor : 448 * L ^ (3 : ℕ) ≤ 1024 * L ^ (4 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hL hL3
    nlinarith
  have hscale : 0 ≤ (K : ℝ) * (R : ℝ) * S * A := by positivity
  have := mul_le_mul_of_nonneg_right hfactor hscale
  nlinarith


end

end GafniTao
