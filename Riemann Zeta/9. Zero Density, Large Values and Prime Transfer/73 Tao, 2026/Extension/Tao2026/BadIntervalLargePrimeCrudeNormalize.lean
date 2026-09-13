import Tao2026.BadIntervalPrimeTupleMultiFiber

/-!
# Source-scale normalization of the large-prime crude bounds

The exact two- and three-coordinate counts have numerators involving the
coordinate scales and denominators involving exact prime-band cardinalities.
This module cancels those scales under one common normalization hypothesis
`P_j ≤ L · #band(P_j)`.  It produces the source-shaped bounds `16 L² / p`
and `96 L³ / (pp')`; the later PNT specialization takes `L = log(z)^{1+o(1)}`.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- If `q ≤ U`, replacing the integer quotient by the real quotient costs at
most the factor two needed to absorb the terminal `+1`. -/
theorem natCast_floor_div_add_one_mul_le_two_mul
    (U q R : ℕ) (hq : 0 < q) (hqU : q ≤ U) :
    ((((U / q + 1) * R : ℕ) : ℝ)) ≤
      2 * (R : ℝ) * (U : ℝ) / (q : ℝ) := by
  have hone : 1 ≤ U / q := (Nat.one_le_div_iff hq).2 hqU
  have hnat : (U / q + 1) * R ≤ 2 * (U / q) * R := by
    gcongr
    omega
  have hcast : ((((U / q + 1) * R : ℕ) : ℝ)) ≤
      2 * ((U / q : ℕ) : ℝ) * R := by
    exact_mod_cast hnat
  calc
    ((((U / q + 1) * R : ℕ) : ℝ)) ≤
        2 * ((U / q : ℕ) : ℝ) * R := hcast
    _ ≤ 2 * ((U : ℝ) / (q : ℝ)) * R := by
      gcongr
      exact Nat.cast_div_le
    _ = 2 * (R : ℝ) * (U : ℝ) / (q : ℝ) := by ring

/-- Two band-normalization inequalities cancel both coordinate scales from
the source pair-fiber ratio. -/
theorem ratio_normalize_two_bands
    (P₁ P₂ C₁ C₂ q L : ℝ)
    (hL : 0 ≤ L) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hq : 0 < q)
    (h₁ : P₁ ≤ L * C₁) (h₂ : P₂ ≤ L * C₂)
    (hP₂ : 0 ≤ P₂) :
    (16 * P₁ * P₂ / q) / (C₁ * C₂) ≤ 16 * L ^ 2 / q := by
  have hprod : P₁ * P₂ ≤ L ^ 2 * (C₁ * C₂) := by
    calc
      P₁ * P₂ ≤ (L * C₁) * (L * C₂) :=
        mul_le_mul h₁ h₂ hP₂ (mul_nonneg hL hC₁.le)
      _ = L ^ 2 * (C₁ * C₂) := by ring
  have hden : 0 < q * (C₁ * C₂) := mul_pos hq (mul_pos hC₁ hC₂)
  rw [div_div]
  apply (div_le_iff₀ hden).2
  field_simp [hq.ne', hC₁.ne', hC₂.ne']
  nlinarith

/-- Source-shaped crude form of Proposition 6.7(i).  A common band loss `L`
turns the exact two-coordinate count into `16 L² / p`. -/
theorem taoLargePrimeProbability_le_crude_logScale_pair
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) (j₁ j₂ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj : j₁ ≠ j₂)
    (hp : Nat.Prime a.2) (hpl : ¬a.2 ∣ a.1)
    (L : ℝ) (hL : 0 ≤ L)
    (hband₁ : (P j₁ : ℝ) ≤
      L * ((taoDyadicPrimeBand (P j₁)).card : ℝ))
    (hband₂ : (P j₂ : ℝ) ≤
      L * ((taoDyadicPrimeBand (P j₂)).card : ℝ))
    (hqU : a.2 ≤ (2 * P j₁) * (2 * P j₂)) :
    taoLargePrimeProbability P hP m' a ≤ 16 * L ^ 2 / (a.2 : ℝ) := by
  have hexact := taoLargePrimeProbability_le_crude_pair_of_not_dvd_shift
    P hP m' a j₁ j₂ hj₁ hj₂ hj hp hpl
  have hnum := natCast_floor_div_add_one_mul_le_two_mul
    ((2 * P j₁) * (2 * P j₂)) a.2 2 hp.pos hqU
  have hnum' :
      (((((2 * P j₁) * (2 * P j₂)) / a.2 + 1) * 2 : ℕ) : ℝ) ≤
        16 * (P j₁ : ℝ) * (P j₂ : ℝ) / (a.2 : ℝ) := by
    convert hnum using 1
    · push_cast
      ring
  let C₁ : ℝ := ((taoDyadicPrimeBand (P j₁)).card : ℝ)
  let C₂ : ℝ := ((taoDyadicPrimeBand (P j₂)).card : ℝ)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact_mod_cast Finset.card_pos.mpr (hP j₁)
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    exact_mod_cast Finset.card_pos.mpr (hP j₂)
  calc
    taoLargePrimeProbability P hP m' a ≤
        ((((((2 * P j₁) * (2 * P j₂)) / a.2 + 1) * 2 : ℕ) : ℝ) /
          (C₁ * C₂)) := by simpa [C₁, C₂] using hexact
    _ ≤ (16 * (P j₁ : ℝ) * (P j₂ : ℝ) / (a.2 : ℝ)) /
        (C₁ * C₂) := div_le_div_of_nonneg_right hnum' (mul_nonneg hC₁.le hC₂.le)
    _ ≤ 16 * L ^ 2 / (a.2 : ℝ) := by
      apply ratio_normalize_two_bands _ _ _ _ _ _ hL hC₁ hC₂
        (by exact_mod_cast hp.pos) hband₁ hband₂
      exact_mod_cast Nat.zero_le (P j₂)

/-- Three band-normalization inequalities cancel all coordinate scales from
the source triple-fiber ratio. -/
theorem ratio_normalize_three_bands
    (P₁ P₂ P₃ C₁ C₂ C₃ q L : ℝ)
    (hL : 0 ≤ L) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hq : 0 < q) (h₁ : P₁ ≤ L * C₁) (h₂ : P₂ ≤ L * C₂)
    (h₃ : P₃ ≤ L * C₃) (hP₂ : 0 ≤ P₂) (hP₃ : 0 ≤ P₃) :
    (96 * P₁ * P₂ * P₃ / q) / (C₁ * C₂ * C₃) ≤
      96 * L ^ 3 / q := by
  have hpair : P₁ * P₂ ≤ L ^ 2 * (C₁ * C₂) := by
    calc
      P₁ * P₂ ≤ (L * C₁) * (L * C₂) :=
        mul_le_mul h₁ h₂ hP₂ (mul_nonneg hL hC₁.le)
      _ = L ^ 2 * (C₁ * C₂) := by ring
  have hprod : P₁ * P₂ * P₃ ≤ L ^ 3 * (C₁ * C₂ * C₃) := by
    calc
      P₁ * P₂ * P₃ ≤ (L ^ 2 * (C₁ * C₂)) * (L * C₃) :=
        mul_le_mul hpair h₃ hP₃
          (mul_nonneg (sq_nonneg L) (mul_nonneg hC₁.le hC₂.le))
      _ = L ^ 3 * (C₁ * C₂ * C₃) := by ring
  have hden : 0 < q * (C₁ * C₂ * C₃) :=
    mul_pos hq (mul_pos (mul_pos hC₁ hC₂) hC₃)
  rw [div_div]
  apply (div_le_iff₀ hden).2
  field_simp [hq.ne', hC₁.ne', hC₂.ne', hC₃.ne']
  nlinarith

/-- Source-shaped crude form of Proposition 6.8(i).  A common band loss `L`
turns the exact three-coordinate count into `96 L³ / (pp')`. -/
theorem taoLargePrimeJointProbability_le_crude_logScale_triple
    (P : Fin 1001 → ℕ) (hP : ∀ k, (taoDyadicPrimeBand (P k)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) (j₁ j₂ j₃ : Fin 1001)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hj₃ : j₃ ≠ 0)
    (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃) (h₂₃ : j₂ ≠ j₃)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (L : ℝ) (hL : 0 ≤ L)
    (hband₁ : (P j₁ : ℝ) ≤
      L * ((taoDyadicPrimeBand (P j₁)).card : ℝ))
    (hband₂ : (P j₂ : ℝ) ≤
      L * ((taoDyadicPrimeBand (P j₂)).card : ℝ))
    (hband₃ : (P j₃ : ℝ) ≤
      L * ((taoDyadicPrimeBand (P j₃)).card : ℝ))
    (hqU : a.2 * b.2 ≤
      ((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) :
    taoLargePrimeJointProbability P hP m' a b ≤
      96 * L ^ 3 / ((a.2 : ℝ) * (b.2 : ℝ)) := by
  have hexact :=
    taoLargePrimeJointProbability_le_crude_triple_of_not_dvd_shifts
      P hP m' a b j₁ j₂ j₃ hj₁ hj₂ hj₃ h₁₂ h₁₃ h₂₃
        hp hq hpq hpa hqb
  have hmodPos : 0 < a.2 * b.2 := Nat.mul_pos hp.pos hq.pos
  have hnum := natCast_floor_div_add_one_mul_le_two_mul
    (((2 * P j₁) * (2 * P j₂)) * (2 * P j₃))
      (a.2 * b.2) 6 hmodPos hqU
  have hnum' :
      ((((((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) /
        (a.2 * b.2) + 1) * 6 : ℕ) : ℝ) ≤
        96 * (P j₁ : ℝ) * (P j₂ : ℝ) * (P j₃ : ℝ) /
          ((a.2 : ℝ) * (b.2 : ℝ)) := by
    convert hnum using 1
    · push_cast
      ring
  let C₁ : ℝ := ((taoDyadicPrimeBand (P j₁)).card : ℝ)
  let C₂ : ℝ := ((taoDyadicPrimeBand (P j₂)).card : ℝ)
  let C₃ : ℝ := ((taoDyadicPrimeBand (P j₃)).card : ℝ)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact_mod_cast Finset.card_pos.mpr (hP j₁)
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    exact_mod_cast Finset.card_pos.mpr (hP j₂)
  have hC₃ : 0 < C₃ := by
    dsimp [C₃]
    exact_mod_cast Finset.card_pos.mpr (hP j₃)
  calc
    taoLargePrimeJointProbability P hP m' a b ≤
        (((((((2 * P j₁) * (2 * P j₂)) * (2 * P j₃)) /
          (a.2 * b.2) + 1) * 6 : ℕ) : ℝ) / (C₁ * C₂ * C₃)) := by
            simpa [C₁, C₂, C₃] using hexact
    _ ≤ (96 * (P j₁ : ℝ) * (P j₂ : ℝ) * (P j₃ : ℝ) /
          ((a.2 : ℝ) * (b.2 : ℝ))) / (C₁ * C₂ * C₃) :=
      div_le_div_of_nonneg_right hnum'
        (mul_nonneg (mul_nonneg hC₁.le hC₂.le) hC₃.le)
    _ ≤ 96 * L ^ 3 / ((a.2 : ℝ) * (b.2 : ℝ)) := by
      apply ratio_normalize_three_bands _ _ _ _ _ _ _ _ hL hC₁ hC₂ hC₃
        (mul_pos (by exact_mod_cast hp.pos) (by exact_mod_cast hq.pos))
          hband₁ hband₂ hband₃
      · exact_mod_cast Nat.zero_le (P j₂)
      · exact_mod_cast Nat.zero_le (P j₃)

end

end Tao2026
