import GafniTao.HeathBrownKthDerivativeSetup
import Mathlib.Algebra.Order.Round

/-!
# Heath-Brown's one-dimensional spacing count

This is the finite core of the elementary spacing lemma used twice in
Heath-Brown's proof of the refined count `mathcal N`.  The definition uses
the literal distance to the nearest integer.  The lemmas below establish
the two quantitative facts needed for the cardinality argument: points in
one nearest-integer fiber occupy an interval of length `2 theta / mu`, and
the full nearest-integer image has length controlled by the upper derivative.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The source notation `||x|| = min_{z in Z} |x-z|`, represented by the
canonical nearest integer supplied by `Int.round`. -/
def heathBrownDistanceToInteger (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

theorem heathBrownDistanceToInteger_eq_min_fract (x : ℝ) :
    heathBrownDistanceToInteger x =
      min (Int.fract x) (1 - Int.fract x) := by
  unfold heathBrownDistanceToInteger
  exact abs_sub_round_eq_min x

theorem heathBrownDistanceToInteger_nonneg (x : ℝ) :
    0 ≤ heathBrownDistanceToInteger x := by
  exact abs_nonneg _

theorem heathBrownDistanceToInteger_add_intCast (x : ℝ) (q : ℤ) :
    heathBrownDistanceToInteger (x + q) =
      heathBrownDistanceToInteger x := by
  unfold heathBrownDistanceToInteger
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

/-- On the centered fundamental interval, distance to the nearest integer
is the ordinary absolute value.  The right endpoint is handled separately
because `Int.round (1/2) = 1`. -/
theorem heathBrownDistanceToInteger_eq_abs_of_abs_le_half
    {x : ℝ} (hx : |x| ≤ 1 / 2) :
    heathBrownDistanceToInteger x = |x| := by
  rcases lt_or_eq_of_le (le_trans (le_abs_self x) hx) with hlt | heq
  · have hlo : -(1 / 2 : ℝ) ≤ x := by
      exact (neg_le_of_abs_le hx)
    have hround : round x = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨hlo, hlt⟩
    simp [heathBrownDistanceToInteger, hround]
  · have hxhalf : x = (1 : ℝ) / 2 := heq
    subst x
    norm_num [heathBrownDistanceToInteger]

theorem abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half
    {x delta : ℝ}
    (hdelta : heathBrownDistanceToInteger x ≤ delta)
    (hx : |x| ≤ 1 / 2) :
    |x| ≤ delta := by
  rwa [heathBrownDistanceToInteger_eq_abs_of_abs_le_half hx] at hdelta

/-- Integers counted in Heath-Brown's elementary spacing lemma. -/
def heathBrownSpacingSet (N : ℕ) (g : ℝ → ℝ) (theta : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n => heathBrownDistanceToInteger (g n) ≤ theta)

theorem mem_heathBrownSpacingSet
    {N : ℕ} {g : ℝ → ℝ} {theta : ℝ} {n : ℕ} :
    n ∈ heathBrownSpacingSet N g theta ↔
      1 ≤ n ∧ n ≤ N ∧
        |g n - (round (g n) : ℝ)| ≤ theta := by
  simp [heathBrownSpacingSet, heathBrownDistanceToInteger, and_assoc]

theorem heathBrown_same_round_upper_difference
    {g : ℝ → ℝ} {theta : ℝ} {m n : ℕ}
    (hm : |g m - (round (g m) : ℝ)| ≤ theta)
    (hn : |g n - (round (g n) : ℝ)| ≤ theta)
    (hround : round (g m) = round (g n)) :
    |g m - g n| ≤ 2 * theta := by
  have htriangle := abs_sub_le (g m) (round (g m) : ℝ) (g n)
  have hmiddle :
      |(round (g m) : ℝ) - g n| =
        |g n - (round (g n) : ℝ)| := by
    rw [hround]
    exact abs_sub_comm _ _
  rw [hmiddle] at htriangle
  linarith

/-- Two counted points in one nearest-integer fiber have source-index
separation at most `2 theta / mu`.  This is the exact finite packing input
to Heath-Brown's Lemma `space`. -/
theorem heathBrown_same_round_index_separation
    {N : ℕ} {g : ℝ → ℝ} {mu theta : ℝ}
    (hmuPos : 0 < mu)
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv g x)
    {m n : ℕ} (hm : m ∈ heathBrownSpacingSet N g theta)
    (hn : n ∈ heathBrownSpacingSet N g theta)
    (hmn : m ≤ n) (hround : round (g m) = round (g n)) :
    (n : ℝ) - m ≤ 2 * theta / mu := by
  rw [mem_heathBrownSpacingSet] at hm hn
  have hmI : (m : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by positivity, by exact_mod_cast hm.2.1⟩
  have hnI : (n : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    constructor
    · positivity
    · exact_mod_cast hn.2.1
  have hslope := heathBrown_lower_slope hg hgd hderivLower hmI hnI
    (by exact_mod_cast hmn)
  have hupperAbs := heathBrown_same_round_upper_difference hm.2.2 hn.2.2 hround
  have horder : g m ≤ g n := by
    have hnonneg : 0 ≤ mu * ((n : ℝ) - m) :=
      mul_nonneg hmuPos.le (sub_nonneg.mpr (by exact_mod_cast hmn))
    linarith
  have hupper : g n - g m ≤ 2 * theta := by
    have habs : |g n - g m| ≤ 2 * theta := by
      simpa only [abs_sub_comm] using hupperAbs
    rw [abs_of_nonneg (sub_nonneg.mpr horder)] at habs
    exact habs
  rw [le_div_iff₀ hmuPos]
  linarith

/-- The upper derivative bounds the spread in `g` across any two source
indices. -/
theorem heathBrown_index_upper_difference
    {N : ℕ} {g : ℝ → ℝ} {M : ℝ}
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivUpper : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), deriv g x ≤ M)
    {m n : ℕ} (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≤ n) :
    g n - g m ≤ M * ((n : ℝ) - m) := by
  have hmI : (m : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by positivity, by exact_mod_cast hm⟩
  have hnI : (n : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by positivity, by exact_mod_cast hn⟩
  exact heathBrown_upper_slope hg hgd hderivUpper hmI hnI
    (by exact_mod_cast hmn)

/-- Exact nearest-integer fiber bound.  The `max 0` makes the statement
total; a nonempty fiber itself forces `theta >= 0`. -/
theorem heathBrown_spacing_fiber_card_le
    {N : ℕ} {g : ℝ → ℝ} {mu theta : ℝ}
    (hmuPos : 0 < mu)
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv g x)
    (q : ℤ) :
    ((heathBrownSpacingSet N g theta).filter
      (fun n : ℕ => round (g (n : ℝ)) = q)).card ≤
      ⌊max 0 (2 * theta / mu)⌋₊ + 1 := by
  classical
  let F : Finset ℕ := (heathBrownSpacingSet N g theta).filter
    (fun n : ℕ => round (g (n : ℝ)) = q)
  change F.card ≤ ⌊max 0 (2 * theta / mu)⌋₊ + 1
  by_cases hF : F.Nonempty
  · let n₀ := F.min' hF
    have hn₀F : n₀ ∈ F := Finset.min'_mem F hF
    have hn₀S : n₀ ∈ heathBrownSpacingSet N g theta :=
      (Finset.mem_filter.mp hn₀F).1
    have hn₀Round : round (g n₀) = q :=
      (Finset.mem_filter.mp hn₀F).2
    have htheta : 0 ≤ theta := by
      rw [mem_heathBrownSpacingSet] at hn₀S
      exact (abs_nonneg _).trans hn₀S.2.2
    have hRnonneg : 0 ≤ 2 * theta / mu := by positivity
    have hsubset : F ⊆ Finset.Icc n₀ (n₀ + ⌊2 * theta / mu⌋₊) := by
      intro n hnF
      have hnS : n ∈ heathBrownSpacingSet N g theta :=
        (Finset.mem_filter.mp hnF).1
      have hnRound : round (g n) = q := (Finset.mem_filter.mp hnF).2
      have hn₀n : n₀ ≤ n := Finset.min'_le F n hnF
      have hsep := heathBrown_same_round_index_separation hmuPos hg hgd
        hderivLower hn₀S hnS hn₀n (hn₀Round.trans hnRound.symm)
      have hsubNat : n - n₀ ≤ ⌊2 * theta / mu⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub hn₀n]
        exact hsep
      exact Finset.mem_Icc.mpr ⟨hn₀n, by omega⟩
    calc
      F.card ≤ (Finset.Icc n₀ (n₀ + ⌊2 * theta / mu⌋₊)).card :=
        Finset.card_le_card hsubset
      _ = ⌊2 * theta / mu⌋₊ + 1 := by
        rw [Nat.card_Icc]
        omega
      _ = ⌊max 0 (2 * theta / mu)⌋₊ + 1 := by
        rw [max_eq_right hRnonneg]
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [this, Finset.card_empty, Nat.zero_le]

/-- Every nearest integer arising from a counted source point lies in the
explicit floor/ceiling interval determined by the two endpoint values. -/
theorem heathBrown_spacing_round_mem_endpoint_interval
    {N : ℕ} {g : ℝ → ℝ} {mu theta : ℝ}
    (hN : 1 ≤ N) (hmuPos : 0 < mu)
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv g x)
    {n : ℕ} (hn : n ∈ heathBrownSpacingSet N g theta) :
    round (g n) ∈
      Finset.Icc ⌊g 1 - theta⌋ ⌈g N + theta⌉ := by
  rw [mem_heathBrownSpacingSet] at hn
  have htheta : 0 ≤ theta := (abs_nonneg _).trans hn.2.2
  have h1n : (1 : ℕ) ≤ n := hn.1
  have hnN : n ≤ N := hn.2.1
  have hOneI : (1 : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by norm_num, by exact_mod_cast hN⟩
  have hnI : (n : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by positivity, by exact_mod_cast hnN⟩
  have hNI : (N : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by positivity, le_rfl⟩
  have hmonoOne := heathBrown_lower_slope hg hgd hderivLower hOneI hnI
    (by exact_mod_cast h1n)
  have hmonoN := heathBrown_lower_slope hg hgd hderivLower hnI hNI
    (by exact_mod_cast hnN)
  have hmuOne : 0 ≤ mu * ((n : ℝ) - 1) := by
    exact mul_nonneg hmuPos.le (sub_nonneg.mpr (by exact_mod_cast h1n))
  have hmuN : 0 ≤ mu * ((N : ℝ) - n) := by
    exact mul_nonneg hmuPos.le (sub_nonneg.mpr (by exact_mod_cast hnN))
  have hgOne : g 1 ≤ g n := by linarith
  have hgN : g n ≤ g N := by linarith
  have hroundLower : g n - theta ≤ (round (g n) : ℝ) := by
    have := le_of_abs_le hn.2.2
    linarith
  have hroundUpper : (round (g n) : ℝ) ≤ g n + theta := by
    have := neg_le_of_abs_le hn.2.2
    linarith
  rw [Finset.mem_Icc]
  constructor
  · have hreal : (⌊g 1 - theta⌋ : ℝ) ≤ (round (g n) : ℝ) :=
      (Int.floor_le (g 1 - theta)).trans (by linarith)
    exact_mod_cast hreal
  · have hreal : (round (g n) : ℝ) ≤ (⌈g N + theta⌉ : ℝ) := by
      have hceil := Int.le_ceil (g N + theta)
      linarith
    exact_mod_cast hreal

/-- Fully finite form of Heath-Brown's elementary spacing lemma before
simplifying the floor/ceiling factors into Vinogradov notation. -/
theorem heathBrown_spacing_card_le_exact
    {N : ℕ} {g : ℝ → ℝ} {mu theta : ℝ}
    (hN : 1 ≤ N) (hmuPos : 0 < mu)
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv g x) :
    (heathBrownSpacingSet N g theta).card ≤
      (⌊max 0 (2 * theta / mu)⌋₊ + 1) *
        (Finset.Icc ⌊g 1 - theta⌋ ⌈g N + theta⌉).card := by
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun n : ℕ => round (g (n : ℝ)))
    (s := heathBrownSpacingSet N g theta)
    (t := Finset.Icc ⌊g 1 - theta⌋ ⌈g N + theta⌉)
  · intro n hn
    exact heathBrown_spacing_round_mem_endpoint_interval hN hmuPos hg hgd
      hderivLower hn
  · intro q hq
    exact heathBrown_spacing_fiber_card_le hmuPos hg hgd hderivLower q

#print axioms heathBrownDistanceToInteger_eq_min_fract
#print axioms heathBrownDistanceToInteger_eq_abs_of_abs_le_half
#print axioms abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half
#print axioms mem_heathBrownSpacingSet
#print axioms heathBrown_same_round_upper_difference
#print axioms heathBrown_same_round_index_separation
#print axioms heathBrown_index_upper_difference
#print axioms heathBrown_spacing_fiber_card_le
#print axioms heathBrown_spacing_round_mem_endpoint_interval
#print axioms heathBrown_spacing_card_le_exact

end

end GafniTao
