import GafniTao.FordLemma51Normalize

/-!
# Ford Lemma 5.1: literal real parameters

Ford states `M₁` and `M₂` as real numbers.  The proof sums over integral
cutoffs, so this file supplies the missing floor bridges and retains a real
`M₂` in every displayed `W_j`.  The branch `M₁ M₂ > N`, omitted from the
Taylor discussion in the paper, is discharged by the trivial length bound.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal real-`M₂` version of the displayed `W_j` in Ford's Lemma
5.1. -/
def fordLemma51WReal
    {k : ℕ} (s : ℕ) (M₂ : ℝ) (r M : ℕ) (N t : ℝ) (j : Fin k) : ℝ :=
  let d : ℕ := (j : ℕ) + 1
  min (2 * (s : ℝ) * M₂ ^ d)
    (2 * (s : ℝ) * M₂ ^ d /
        ((r : ℝ) * (M : ℝ) ^ d) +
      (s : ℝ) * t * M₂ ^ d /
        (Real.pi * d * N ^ d) +
      4 * Real.pi * d * (2 * N) ^ d /
        ((r : ℝ) * t * (M : ℝ) ^ d) + 2)

theorem fordLemma51WReal_nonneg
    {k s r M : ℕ} {M₂ N t : ℝ}
    (hs : 0 < s) (hM₂ : 0 ≤ M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t) (j : Fin k) :
    0 ≤ fordLemma51WReal s M₂ r M N t j := by
  unfold fordLemma51WReal
  apply le_min <;> positivity

theorem fordLemma51W_le_real
    {k s Q r M : ℕ} {M₂ N t : ℝ}
    (hQ : (Q : ℝ) ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) (hN : 0 < N) (ht : 0 < t)
    (j : Fin k) :
    fordLemma51W s Q r M N t j ≤
      fordLemma51WReal s M₂ r M N t j := by
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hpow : (Q : ℝ) ^ ((j : ℕ) + 1) ≤
      M₂ ^ ((j : ℕ) + 1) := by
    exact pow_le_pow_left₀ hQ0 hQ _
  unfold fordLemma51W fordLemma51WReal
  apply min_le_min
  · gcongr
  · have hdenM : 0 < (r : ℝ) * (M : ℝ) ^ ((j : ℕ) + 1) := by
      positivity
    have hdenN : 0 < Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) *
        N ^ ((j : ℕ) + 1) := by positivity
    gcongr

/-- Ford's literal displayed core with real `M₂` and `⌊M₁⌋` in the places
where the proof actually uses the first cutoff. -/
def fordLemma51SourceCore
    (k h g r s : ℕ) (M₁ M₂ : ℝ) (N : ℕ) (B : Finset ℕ) (t : ℝ) : ℝ :=
  (5 * (r : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
    (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ) + fordVinogradovKappa k) *
    (fordVinogradovMomentNat r k ⌊M₁⌋₊ : ℝ) *
    (fordLemma51WindowMoment k h g s B : ℝ) *
    ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51WReal s M₂ r ⌊M₁⌋₊ N t j.1

/-- The nonnegative analytic core after replacing the integral second cutoff
by Ford's literal real `M₂` in the `W_j`. -/
def fordLemma51AnalyticCoreRealW
    (k h g r s M : ℕ) (M₂ : ℝ) (N : ℕ)
    (B : Finset ℕ) (t : ℝ) : ℝ :=
  (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
    (fordVinogradovMomentNat r k M : ℝ) *
    (fordLemma51WindowMoment k h g s B : ℝ) *
    ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51WReal s M₂ r M N t j.1

theorem fordLemma51AnalyticCoreRealW_nonneg
    {k h g r s M N : ℕ} {M₂ t : ℝ}
    (hs : 0 < s) (hM₂ : 0 ≤ M₂) (hr : 0 < r) (hM : 0 < M)
    (hN : (0 : ℝ) < N) (ht : 0 < t) (B : Finset ℕ) :
    0 ≤ fordLemma51AnalyticCoreRealW k h g r s M M₂ N B t := by
  have hprod : 0 ≤ ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51WReal s M₂ r M N t j.1 := by
    exact Finset.prod_nonneg fun j _ =>
      fordLemma51WReal_nonneg hs hM₂ hr hM hN ht j.1
  unfold fordLemma51AnalyticCoreRealW
  positivity

theorem fordLemma51AnalyticCore_le_realW
    {k h g r s M Q N : ℕ} {M₂ t : ℝ}
    (hs : 0 < s) (hQ : (Q : ℝ) ≤ M₂) (hr : 0 < r)
    (hM : 0 < M) (hN : (0 : ℝ) < N) (ht : 0 < t)
    (B : Finset ℕ) :
    fordLemma51AnalyticCore k h g r s M Q N B t ≤
      fordLemma51AnalyticCoreRealW k h g r s M M₂ N B t := by
  have hprod :
      (∏ j : FordLemma51DegreeWindow k h g,
        fordLemma51W s Q r M N t j.1) ≤
      ∏ j : FordLemma51DegreeWindow k h g,
        fordLemma51WReal s M₂ r M N t j.1 := by
    apply Finset.prod_le_prod
    · intro j _
      exact fordLemma51W_nonneg hs hr hM hN ht j.1
    · intro j _
      exact fordLemma51W_le_real hQ hr hM hN ht j.1
  unfold fordLemma51AnalyticCore fordLemma51AnalyticCoreRealW
  gcongr

theorem fordLemma51SourceCore_eq_separated
    {k h g r s N : ℕ} {M₁ M₂ : ℝ}
    (hM₁ : 1 ≤ M₁) (B : Finset ℕ) (t : ℝ) :
    fordLemma51SourceCore k h g r s M₁ M₂ N B t =
      M₂ ^ (-(2 * s : ℝ)) *
        (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ)) *
        fordLemma51AnalyticCoreRealW
          k h g r s ⌊M₁⌋₊ M₂ N B t := by
  have hfloor : 0 < ⌊M₁⌋₊ := Nat.floor_pos.mpr hM₁
  have hfloorReal : (0 : ℝ) < ⌊M₁⌋₊ := by exact_mod_cast hfloor
  unfold fordLemma51SourceCore fordLemma51AnalyticCoreRealW
  rw [Real.rpow_add hfloorReal, Real.rpow_natCast]
  ring

/-- The raw moment prefactor, normalized using the paper's real `M₂` rather
than the integral cutoff used to enumerate `B`. -/
theorem fordLemma51_centralTerm_eq_real_second_scale
    {k h g r s M Q N : ℕ} {M₂ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hM : 0 < M) (hM₂ : 0 < M₂)
    {B : Finset ℕ} (hBne : B.Nonempty) {t : ℝ}
    (hN : 0 < N) (ht : 0 < t) :
    (N : ℝ) / ((M : ℝ) * B.card) *
        (fordLemma51MomentMajorant k h g r s M Q N B t) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) =
      (N : ℝ) * (M₂ / B.card) ^ (1 / (r : ℝ)) *
        (M₂ ^ (-(2 * s : ℝ)) * (M : ℝ) ^ (-(2 * r : ℝ)) *
          fordLemma51AnalyticCore k h g r s M Q N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hBcard : 0 < B.card := Finset.card_pos.mpr hBne
  have hBreal : (0 : ℝ) < B.card := by exact_mod_cast hBcard
  have hcore := fordLemma51AnalyticCore_nonneg
    (k := k) (h := h) (g := g) (M₂ := Q) hs hr hM hNreal ht B
  rw [fordLemma51MomentMajorant_eq_prefactors]
  exact fordLemma51_prefactor_normalization
    hMreal (by exact_mod_cast hBcard) hM₂ hcore hNreal hr hs

theorem fordLemma51SourceCore_nonneg
    {k h g r s N : ℕ} {M₁ M₂ t : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 0 ≤ M₂) (hr : 0 < r) (hs : 0 < s)
    (hN : (0 : ℝ) < N) (ht : 0 < t) (B : Finset ℕ) :
    0 ≤ fordLemma51SourceCore k h g r s M₁ M₂ N B t := by
  rw [fordLemma51SourceCore_eq_separated hM₁]
  have hfloor : 0 < ⌊M₁⌋₊ := Nat.floor_pos.mpr hM₁
  have hcore := fordLemma51AnalyticCoreRealW_nonneg
    (k := k) (h := h) (g := g) hs hM₂ hr hfloor hN ht B
  positivity

theorem fordLemma51_centralTerm_le_sourceCore
    {k h g r s Q N : ℕ} {M₁ M₂ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hQ : (Q : ℝ) ≤ M₂) {B : Finset ℕ} (hBne : B.Nonempty)
    {t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    (N : ℝ) / ((⌊M₁⌋₊ : ℝ) * B.card) *
        (fordLemma51MomentMajorant
          k h g r s ⌊M₁⌋₊ Q N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) ≤
      (N : ℝ) * (M₂ / B.card) ^ (1 / (r : ℝ)) *
        (fordLemma51SourceCore k h g r s M₁ M₂ N B t) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hfloor : 0 < ⌊M₁⌋₊ := Nat.floor_pos.mpr hM₁
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hEq := fordLemma51_centralTerm_eq_real_second_scale
    (k := k) (h := h) (g := g) (r := r) (s := s)
    (M := ⌊M₁⌋₊) (Q := Q) (N := N)
    hr hs hfloor (zero_lt_one.trans_le hM₂) hBne hN ht
  rw [hEq]
  rw [fordLemma51SourceCore_eq_separated hM₁]
  have hcore := fordLemma51AnalyticCore_le_realW
    (k := k) (h := h) (g := g) (r := r) (s := s)
    (M := ⌊M₁⌋₊) (Q := Q) (N := N)
    hs hQ hr hfloor hNreal ht B
  have hleftCore : 0 ≤
      M₂ ^ (-(2 * s : ℝ)) * (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ)) *
        fordLemma51AnalyticCore k h g r s ⌊M₁⌋₊ Q N B t := by
    have := fordLemma51AnalyticCore_nonneg
      (k := k) (h := h) (g := g) (M₂ := Q)
      hs hr hfloor hNreal ht B
    positivity
  have hrightCore : 0 ≤
      M₂ ^ (-(2 * s : ℝ)) * (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ)) *
        fordLemma51AnalyticCoreRealW
          k h g r s ⌊M₁⌋₊ M₂ N B t := by
    have := fordLemma51AnalyticCoreRealW_nonneg
      (k := k) (h := h) (g := g)
      hs (zero_le_one.trans hM₂) hr hfloor hNreal ht B
    positivity
  have hscaled :
      M₂ ^ (-(2 * s : ℝ)) * (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ)) *
          fordLemma51AnalyticCore k h g r s ⌊M₁⌋₊ Q N B t ≤
        M₂ ^ (-(2 * s : ℝ)) * (⌊M₁⌋₊ : ℝ) ^ (-(2 * r : ℝ)) *
          fordLemma51AnalyticCoreRealW
            k h g r s ⌊M₁⌋₊ M₂ N B t := by
    gcongr
  have hq : 0 ≤ 1 / ((2 * r * s : ℕ) : ℝ) := by positivity
  have hrpow := Real.rpow_le_rpow hleftCore hscaled hq
  have houter : 0 ≤ (N : ℝ) * (M₂ / B.card) ^ (1 / (r : ℝ)) := by
    positivity
  exact mul_le_mul_of_nonneg_left hrpow houter

/-- Ford's Lemma 5.1 with the real parameters and the literal displayed
right-hand side from the source.  The proof uses the Taylor argument when
`M₁ M₂ ≤ N`; when that condition fails, the first displayed term already
dominates the trivial length bound for the exponential sum. -/
theorem ford_exponential_lemma_5_1
    {k h g r s N R : ℕ}
    (hk : 2 ≤ k) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (_hh : 1 ≤ h) (_hhg : h ≤ g) (_hgk : g ≤ k)
    {M₁ M₂ : ℝ} (hM₁ : 1 ≤ M₁) (hM₁N : M₁ ≤ N)
    (hM₂ : 1 ≤ M₂) (hM₂N : M₂ ≤ N)
    {B : Finset ℕ} (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hBtop : ∀ b ∈ B, (b : ℝ) ≤ M₂)
    (hR : R ≤ 2 * N) {u t : ℝ}
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      2 * M₁ * M₂ +
        t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) +
        (N : ℝ) * (M₂ / B.card) ^ (1 / (r : ℝ)) *
          (fordLemma51SourceCore k h g r s M₁ M₂ N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hN : 0 < N := by
    by_contra hNzero
    have : N = 0 := Nat.eq_zero_of_not_pos hNzero
    subst N
    norm_num at hM₁N
    linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans hM₁
  have hM₂0 : 0 ≤ M₂ := zero_le_one.trans hM₂
  have hsource :
      0 ≤ fordLemma51SourceCore k h g r s M₁ M₂ N B t :=
    fordLemma51SourceCore_nonneg hM₁ hM₂0 (lt_of_lt_of_le Nat.zero_lt_two hr)
      (lt_of_lt_of_le Nat.zero_lt_two hs) hNreal ht B
  by_cases hprod : M₁ * M₂ ≤ N
  · have hfloor₁ : 0 < ⌊M₁⌋₊ := Nat.floor_pos.mpr hM₁
    have hfloor₂ : 1 ≤ ⌊M₂⌋₊ := Nat.floor_pos.mpr hM₂
    have hfloor₁_le : (⌊M₁⌋₊ : ℝ) ≤ M₁ := Nat.floor_le hM₁0
    have hfloor₂_le : (⌊M₂⌋₊ : ℝ) ≤ M₂ := Nat.floor_le hM₂0
    have hfloorProd : ((⌊M₁⌋₊ * ⌊M₂⌋₊ : ℕ) : ℝ) ≤ M₁ * M₂ := by
      norm_num only [Nat.cast_mul]
      exact mul_le_mul hfloor₁_le hfloor₂_le (by positivity) hM₁0
    have hMN : ⌊M₁⌋₊ * ⌊M₂⌋₊ ≤ N := by
      exact_mod_cast hfloorProd.trans hprod
    have hBtopFloor : ∀ b ∈ B, b ≤ ⌊M₂⌋₊ := by
      intro b hb
      exact (Nat.le_floor_iff hM₂0).2 (hBtop b hb)
    have hraw := ford_exponential_lemma_5_1_raw
      (k := k) (h := h) (g := g) (r := r) (s := s)
      (M := ⌊M₁⌋₊) (M₂ := ⌊M₂⌋₊) (N := N) (R := R)
      hr hs hfloor₁ hfloor₂ hBne hBpos hBtopFloor hMN hR hu huOne ht
    have hcentral := fordLemma51_centralTerm_le_sourceCore
      (k := k) (h := h) (g := g) (r := r) (s := s)
      (Q := ⌊M₂⌋₊) (N := N) (lt_of_lt_of_le Nat.zero_lt_two hr)
      (lt_of_lt_of_le Nat.zero_lt_two hs) hM₁ hM₂ hfloor₂_le hBne hN ht
    have hboundary :
        2 * (⌊M₁⌋₊ : ℝ) * (⌊M₂⌋₊ : ℝ) ≤ 2 * M₁ * M₂ := by
      norm_cast at hfloorProd
      nlinarith
    have hpower :
        (((⌊M₁⌋₊ * ⌊M₂⌋₊ : ℕ) : ℝ) ^ (k + 1)) ≤
          (M₁ * M₂) ^ (k + 1) := by
      exact pow_le_pow_left₀ (by positivity) hfloorProd _
    have herror :
        t * (((⌊M₁⌋₊ * ⌊M₂⌋₊ : ℕ) : ℝ) ^ (k + 1)) /
              (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) ≤
          t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) := by
      calc
        t * (((⌊M₁⌋₊ * ⌊M₂⌋₊ : ℕ) : ℝ) ^ (k + 1)) /
              (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) ≤
            t * (M₁ * M₂) ^ (k + 1) /
              (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) := by
                gcongr
        _ ≤ t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) := by
          apply div_le_div_of_nonneg_left
          · positivity
          · positivity
          · gcongr
            exact Nat.le_succ k
    linarith
  · have hprodStrict : (N : ℝ) < M₁ * M₂ := lt_of_not_ge hprod
    have htrivial := norm_fordShiftedExponentialSum_le_N hR u t
    have hmain : (N : ℝ) ≤ 2 * M₁ * M₂ := by linarith
    have herror :
        0 ≤ t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) := by
      positivity
    have hcentral :
        0 ≤ (N : ℝ) * (M₂ / B.card) ^ (1 / (r : ℝ)) *
          (fordLemma51SourceCore k h g r s M₁ M₂ N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) := by
      positivity
    exact htrivial.trans (by linarith)

#print axioms fordLemma51WReal_nonneg
#print axioms fordLemma51W_le_real
#print axioms fordLemma51AnalyticCoreRealW_nonneg
#print axioms fordLemma51AnalyticCore_le_realW
#print axioms fordLemma51SourceCore_eq_separated
#print axioms fordLemma51_centralTerm_eq_real_second_scale
#print axioms fordLemma51SourceCore_nonneg
#print axioms fordLemma51_centralTerm_le_sourceCore
#print axioms ford_exponential_lemma_5_1

end

end GafniTao
