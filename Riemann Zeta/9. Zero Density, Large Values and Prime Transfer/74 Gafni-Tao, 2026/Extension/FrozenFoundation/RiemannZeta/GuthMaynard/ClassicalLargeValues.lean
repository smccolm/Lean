import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannZeta.GuthMaynard.HalaszMontgomery
import RiemannZeta.GuthMaynard.LogarithmicKernel

open Complex Finset Set
open scoped BigOperators ComplexConjugate

namespace RiemannZeta.GuthMaynard

/-!
# Classical Montgomery--Halász--Huxley large values

This file proves the finite large-values estimate used by the classical
zero-density argument.  Its analytic input is the pair of kernel estimates in
`LogarithmicKernel`; all remaining arguments here are finite duality,
separated-set counting, localization, and subdivision.
-/

/-- A unit complex number which rotates `z` onto the nonnegative real axis. -/
noncomputable def phaseAlign (z : ℂ) : ℂ := if z = 0 then 1 else conj z / ‖z‖

private theorem norm_conj_eq (z : ℂ) : ‖conj z‖ = ‖z‖ := by
  change ‖star z‖ = ‖z‖
  exact norm_star z

theorem norm_phaseAlign_le_one (z : ℂ) : ‖phaseAlign z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · rw [phaseAlign, if_neg hz, norm_div]
    rw [norm_conj_eq, norm_real]
    have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [hzNorm]

theorem phaseAlign_mul (z : ℂ) : phaseAlign z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseAlign, hz]
  · rw [phaseAlign, if_neg hz]
    calc
      conj z / ‖z‖ * z = (conj z * z) / ‖z‖ := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / ‖z‖ := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      _ = (‖z‖ : ℂ) := by
        push_cast
        have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        field_simp

/-- Coordinate Cauchy--Schwarz for a finite complex sum. -/
theorem norm_sum_mul_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => by rw [norm_mul])
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) :=
      sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

/-- The finite Gram-matrix bound underlying Halász--Montgomery duality. -/
theorem sum_norm_sq_sum_le_gram {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (c : κ → ℂ) (y : κ → ι → ℂ)
    (hc : ∀ t ∈ W, ‖c t‖ ≤ 1) :
    (∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
  have hexpand :
      ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
        ∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n) := by
    have hpoint (n : ι) :
        ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          conj (∑ t ∈ W, c t * y t n) * (∑ t ∈ W, c t * y t n) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    have hcast :
        ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ s, ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp_rw [hpoint]
    simp only [map_sum, map_mul]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hre := congrArg Complex.re hexpand
  simp only [ofReal_re] at hre
  rw [hre]
  calc
    Complex.re (∑ t ∈ W, ∑ u ∈ W,
        conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)) ≤
        ‖∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => norm_sum_le _ _)
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, norm_mul]
      rw [norm_conj_eq]
      have hct := hc t ht
      have hcu := hc u hu
      have hprod : ‖c t‖ * ‖c u‖ ≤ 1 := by
        calc
          ‖c t‖ * ‖c u‖ ≤ 1 * 1 :=
            mul_le_mul hct hcu (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      exact (mul_le_mul_of_nonneg_right hprod
        (norm_nonneg (∑ n ∈ s, conj (y t n) * y u n))).trans_eq (one_mul _)

private theorem dirichletPoly_eq_logarithmicPhase
    (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPoly N a t =
      ∑ n ∈ dyadicInterval N, a n * unitaryPhase (logarithmicPhase t n) := by
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  exact (unitaryPhase_logarithmicPhase_eq_cpow t n hnPos).symm

private theorem logarithmicPhase_sub (t u : ℝ) (n : ℕ) :
    logarithmicPhase u n - logarithmicPhase t n = logarithmicPhase (u - t) n := by
  simp only [logarithmicPhase]
  ring

theorem logarithmicPhase_gram_eq_kernel (N : ℕ) (t u : ℝ) :
    (∑ n ∈ dyadicInterval N,
        conj (unitaryPhase (logarithmicPhase t n)) *
          unitaryPhase (logarithmicPhase u n)) =
      logarithmicKernel N (u - t) := by
  unfold logarithmicKernel
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, ← unitaryPhase_sub, logarithmicPhase_sub]
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  exact unitaryPhase_logarithmicPhase_eq_cpow (u - t) n hnPos

/-- Phase-aligned finite Halász--Montgomery duality, specialized to the
project's dyadic Dirichlet polynomials. -/
theorem halasz_montgomery_duality
    (N : ℕ) (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    ((W.card : ℝ) * V) ^ 2 ≤
      (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ := by
  let D : ℝ → ℂ := fun t => dirichletPoly N a t
  let c : ℝ → ℂ := fun t => phaseAlign (D t)
  let y : ℝ → ℕ → ℂ := fun t n => unitaryPhase (logarithmicPhase t n)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := by
    intro t ht
    exact norm_phaseAlign_le_one (D t)
  have hsumNorm : (W.card : ℝ) * V ≤ ∑ t ∈ W, ‖D t‖ := by
    calc
      (W.card : ℝ) * V = ∑ t ∈ W, V := by simp
      _ ≤ ∑ t ∈ W, ‖D t‖ := Finset.sum_le_sum fun t ht => hLarge t ht
  have halign :
      ‖∑ t ∈ W, c t * D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have heq : (∑ t ∈ W, c t * D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro t ht
      exact phaseAlign_mul (D t)
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hexpand :
      (∑ t ∈ W, c t * D t) =
        ∑ n ∈ dyadicInterval N, a n * (∑ t ∈ W, c t * y t n) := by
    simp only [D, dirichletPoly_eq_logarithmicPhase, y, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hcs := norm_sum_mul_sq_le (dyadicInterval N) a
    (fun n => ∑ t ∈ W, c t * y t n)
  rw [← hexpand] at hcs
  have hgram := sum_norm_sq_sum_le_gram (dyadicInterval N) W c y hc
  have hcorr : ∀ t ∈ W, ∀ u ∈ W,
      (∑ n ∈ dyadicInterval N, conj (y t n) * y u n) =
        logarithmicKernel N (u - t) := by
    intro t ht u hu
    exact logarithmicPhase_gram_eq_kernel N t u
  have hgram' :
      (∑ n ∈ dyadicInterval N, ‖∑ t ∈ W, c t * y t n‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ := by
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          ‖∑ n ∈ dyadicInterval N, conj (y t n) * y u n‖ := hgram
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro u hu
        rw [hcorr t ht u hu]
  have henergy : 0 ≤ ∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2 := by positivity
  calc
    ((W.card : ℝ) * V) ^ 2 ≤ ‖∑ t ∈ W, c t * D t‖ ^ 2 := by
      rw [halign]
      have hleft : 0 ≤ (W.card : ℝ) * V := mul_nonneg (by positivity) hV
      have hright : 0 ≤ ∑ t ∈ W, ‖D t‖ := by positivity
      nlinarith
    _ ≤ (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        (∑ n ∈ dyadicInterval N, ‖∑ t ∈ W, c t * y t n‖ ^ 2) := hcs
    _ ≤ (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖ :=
      mul_le_mul_of_nonneg_left hgram' henergy

private theorem separated_subset_card_le_one_of_diameter
    (W S : Finset ℝ) (hSep : IsSeparated 1 W) (hSW : S ⊆ W)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < 1) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  have hlarge := hSep x (hSW hx) y (hSW hy) hxy
  exact (not_lt_of_ge hlarge) (hdiam x hx y hy)

/-- A unit-width annulus about a point contains at most one separated point on
each side. -/
theorem separated_annulus_card_le_two
    (W : Finset ℝ) (t : ℝ) (k : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}).card ≤ 2 := by
  let S := {u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧ |u - t| < (k : ℝ) + 1}
  let P : ℝ → Prop := fun u => t ≤ u
  have hpos : (S.filter P).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter P) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      rw [abs_of_nonneg (sub_nonneg.mpr hxData.2)] at hxS
      rw [abs_of_nonneg (sub_nonneg.mpr hyData.2)] at hyS
      rw [abs_lt]
      constructor <;> linarith [hxS.2.2, hyS.2.2]
  have hneg : (S.filter (fun u => ¬ P u)).card ≤ 1 := by
    apply separated_subset_card_le_one_of_diameter W (S.filter (fun u => ¬ P u)) hSep
    · intro u hu
      exact (Finset.mem_filter.mp hu).1 |> Finset.mem_filter.mp |>.1
    · intro x hx y hy
      have hxData := Finset.mem_filter.mp hx
      have hyData := Finset.mem_filter.mp hy
      have hxS := Finset.mem_filter.mp hxData.1
      have hyS := Finset.mem_filter.mp hyData.1
      have hxt : x - t ≤ 0 := by linarith
      have hyt : y - t ≤ 0 := by linarith
      rw [abs_of_nonpos hxt] at hxS
      rw [abs_of_nonpos hyt] at hyS
      rw [abs_lt]
      constructor <;> linarith [hxS.2.2, hyS.2.2]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) P
  change S.card ≤ 2
  omega

/-- The reciprocal distances from one point to the other separated points in
its `N`-neighborhood have harmonic, rather than linear, total mass. -/
theorem sum_inv_distance_near_le_harmonic
    (N : ℕ) (W : Finset ℝ) (t : ℝ) (hSep : IsSeparated 1 W) (ht : t ∈ W) :
    (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) ≤
      2 * (((harmonic N : ℚ) : ℝ)) := by
  let S := {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}
  let shell : ℝ → ℕ := fun u => Nat.floor |u - t|
  have hmaps : ∀ u ∈ S, shell u ∈ Finset.Icc 1 N := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have hu := huData.1
    have hne := huData.2.1
    have hsep := hSep t ht u hu (Ne.symm hne)
    have hqOne : 1 ≤ |u - t| := by simpa only [abs_sub_comm] using hsep
    have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
    have hfloorPos : 0 < shell u := by
      exact Nat.floor_pos.mpr hqOne
    have hfloorLeReal : ((shell u : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact (Nat.floor_le hqNonneg).trans huData.2.2
    have hfloorLe : shell u ≤ N := by exact_mod_cast hfloorLeReal
    exact Finset.mem_Icc.mpr ⟨hfloorPos, hfloorLe⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun u => 1 / |u - t|)]
  calc
    (∑ k ∈ Finset.Icc 1 N, ∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
        ∑ k ∈ Finset.Icc 1 N, 2 * (1 / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkPos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hfiberCard : ({u ∈ S | shell u = k}).card ≤ 2 := by
        calc
          ({u ∈ S | shell u = k}).card ≤
              ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧
                |u - t| < (k : ℝ) + 1}).card := by
            apply Finset.card_le_card
            intro u hu
            have huData := Finset.mem_filter.mp hu
            have huS := Finset.mem_filter.mp huData.1
            have hfloor := huData.2
            have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
            have hlow : (k : ℝ) ≤ |u - t| := by
              rw [← hfloor]
              exact Nat.floor_le hqNonneg
            have hhigh : |u - t| < (k : ℝ) + 1 := by
              rw [← hfloor]
              exact Nat.lt_floor_add_one _
            exact Finset.mem_filter.mpr ⟨huS.1, huS.2.1, hlow, hhigh⟩
          _ ≤ 2 := separated_annulus_card_le_two W t k hSep
      calc
        (∑ u ∈ S with shell u = k, 1 / |u - t|) ≤
            ∑ u ∈ S with shell u = k, 1 / (k : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          have huData := Finset.mem_filter.mp hu
          have huS := Finset.mem_filter.mp huData.1
          have hfloor := huData.2
          have hqNonneg : 0 ≤ |u - t| := abs_nonneg _
          have hkq : (k : ℝ) ≤ |u - t| := by
            rw [← hfloor]
            exact Nat.floor_le hqNonneg
          exact one_div_le_one_div_of_le (by exact_mod_cast hkPos) hkq
        _ = (({u ∈ S | shell u = k}).card : ℝ) * (1 / (k : ℝ)) := by simp
        _ ≤ 2 * (1 / (k : ℝ)) := by
          gcongr
          exact_mod_cast hfiberCard
    _ = 2 * (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [inv_eq_one_div]
      rw [Finset.mul_sum]

/-- Row-sum bound for the logarithmic Gram kernel on a localized interval.
The near terms contribute a harmonic loss; the far terms are controlled by
the B-process and are small enough to be absorbed after choosing the interval
length. -/
theorem logarithmicKernel_row_sum_le
    (N : ℕ) (W : Finset ℝ) (t A L : ℝ) (hN : 0 < N)
    (hSep : IsSeparated 1 W) (ht : t ∈ W)
    (hInterval : ∀ u ∈ W, u ∈ Set.Icc A (A + L))
    (hLN : L ≤ (N : ℝ) ^ 2) :
    (∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
      (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
        100 * (W.card : ℝ) * Real.sqrt L := by
  have hpoint : ∀ u ∈ W,
      ‖logarithmicKernel N (u - t)‖ ≤
        (if u = t then (N : ℝ) else 0) +
          6 * Real.pi * (N : ℝ) *
            (if u ≠ t ∧ |u - t| ≤ (N : ℝ) then 1 / |u - t| else 0) +
          100 * Real.sqrt L := by
    intro u hu
    by_cases hut : u = t
    · subst u
      rw [sub_self, norm_logarithmicKernel_zero]
      simp only [ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
      nlinarith [Real.sqrt_nonneg L]
    · have hsep := hSep u hu t ht hut
      have hqOne : 1 ≤ |u - t| := hsep
      by_cases hqN : |u - t| ≤ (N : ℝ)
      · simp [hut, hqN]
        exact (norm_logarithmicKernel_le_div N (u - t) hN (by simpa using hqOne) (by simpa using hqN)).trans
          (le_add_of_nonneg_right (by positivity : 0 ≤ 100 * Real.sqrt L))
      · have hNt : (N : ℝ) ≤ |u - t| := le_of_not_ge hqN
        have huI := hInterval u hu
        have htI := hInterval t ht
        have hqL : |u - t| ≤ L := by
          rw [abs_le]
          constructor <;> linarith [huI.1, huI.2, htI.1, htI.2]
        have hqN2 : |u - t| ≤ (N : ℝ) ^ 2 := hqL.trans hLN
        have hfar := norm_logarithmicKernel_le_sqrt N (u - t) hN
          (by simpa using hNt) (by simpa using hqN2)
        have hsqrt : Real.sqrt |u - t| ≤ Real.sqrt L := Real.sqrt_le_sqrt hqL
        simp only [hut, if_false, hqN, and_false, zero_add, mul_zero]
        exact hfar.trans (by gcongr)
  calc
    (∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
        ∑ u ∈ W, ((if u = t then (N : ℝ) else 0) +
          6 * Real.pi * (N : ℝ) *
            (if u ≠ t ∧ |u - t| ≤ (N : ℝ) then 1 / |u - t| else 0) +
          100 * Real.sqrt L) := Finset.sum_le_sum hpoint
    _ = (N : ℝ) + 6 * Real.pi * (N : ℝ) *
          (∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ (N : ℝ)}, 1 / |u - t|) +
          100 * (W.card : ℝ) * Real.sqrt L := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', if_pos ht]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      rw [← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ (N : ℝ) + 6 * Real.pi * (N : ℝ) *
          (2 * (((harmonic N : ℚ) : ℝ))) +
          100 * (W.card : ℝ) * Real.sqrt L := by
      gcongr
      exact sum_inv_distance_near_le_harmonic N W t hSep ht
    _ = (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) +
          100 * (W.card : ℝ) * Real.sqrt L := by ring

/-- Localized large-value count after absorption of the B-process term. -/
theorem local_classical_large_values
    (N : ℕ) (V A L : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hV : 0 < V)
    (hSep : IsSeparated 1 W)
    (hInterval : ∀ t ∈ W, t ∈ Set.Icc A (A + L))
    (hLN : L ≤ (N : ℝ) ^ 2)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖)
    (hAbsorb : 200 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) * Real.sqrt L ≤ V ^ 2) :
    (W.card : ℝ) ≤
      2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
        ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2 := by
  by_cases hW : W = ∅
  · subst W
    have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let R : ℝ := W.card
  let G : ℝ := ∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2
  let B : ℝ := (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW))
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    positivity
  have hdual := halasz_montgomery_duality N V W a hV.le hLarge
  have hrows :
      (∑ t ∈ W, ∑ u ∈ W, ‖logarithmicKernel N (u - t)‖) ≤
        R * (B + 100 * R * Real.sqrt L) := by
    calc
      _ ≤ ∑ t ∈ W, (B + 100 * R * Real.sqrt L) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa only [B, R] using
          logarithmicKernel_row_sum_le N W t A L hN hSep ht hInterval hLN
      _ = R * (B + 100 * R * Real.sqrt L) := by
        simp only [sum_const, nsmul_eq_mul, R]
  have hmain : (R * V) ^ 2 ≤ G * (R * (B + 100 * R * Real.sqrt L)) := by
    exact hdual.trans (mul_le_mul_of_nonneg_left hrows hG)
  have hhalf :
      100 * G * R ^ 2 * Real.sqrt L ≤ (V ^ 2 / 2) * R ^ 2 := by
    have habs : 100 * G * Real.sqrt L ≤ V ^ 2 / 2 := by
      change 200 * G * Real.sqrt L ≤ V ^ 2 at hAbsorb
      nlinarith
    calc
      100 * G * R ^ 2 * Real.sqrt L =
          (100 * G * Real.sqrt L) * R ^ 2 := by ring
      _ ≤ (V ^ 2 / 2) * R ^ 2 :=
        mul_le_mul_of_nonneg_right habs (sq_nonneg R)
  have hcancel : R * V ^ 2 ≤ 2 * G * B := by
    have hquad : R ^ 2 * V ^ 2 ≤ 2 * G * R * B := by
      nlinarith [hmain, hhalf]
    have hfactored : R * (R * V ^ 2) ≤ R * (2 * G * B) := by
      nlinarith
    exact le_of_mul_le_mul_left hfactored hR
  change R ≤ 2 * G * B / V ^ 2
  rw [le_div_iff₀ (sq_pos_of_pos hV)]
  simpa only [mul_assoc] using hcancel

/-- Subdivision of `[0,T]` into equal real intervals transfers the local
absorbed estimate to the full separated set. -/
theorem classical_large_values_of_local_scale
    (N : ℕ) (T V L : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hV : 0 < V) (hL : 0 < L)
    (hLN : L ≤ (N : ℝ) ^ 2)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖)
    (hAbsorb : 200 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) * Real.sqrt L ≤ V ^ 2) :
    (W.card : ℝ) ≤
      ((Nat.floor (T / L) + 1 : ℕ) : ℝ) *
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
  let bin : ℝ → ℕ := fun t => Nat.floor (t / L)
  let K : ℕ := Nat.floor (T / L) + 1
  have hmaps : ∀ t ∈ W, bin t ∈ Finset.range K := by
    intro t ht
    have htBase := hBase t ht
    have hquot : t / L ≤ T / L := (div_le_div_iff_of_pos_right hL).2 htBase.2
    have hfloor := Nat.floor_mono hquot
    dsimp only [bin, K]
    rw [Finset.mem_range]
    omega
  have hfiber (k : ℕ) (hk : k ∈ Finset.range K) :
      (({t ∈ W | bin t = k}).card : ℝ) ≤
        2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2 := by
    let Wk := {t ∈ W | bin t = k}
    have hWkSep : IsSeparated 1 Wk := by
      intro x hx y hy hxy
      exact hSep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    have hWkInterval : ∀ t ∈ Wk, t ∈ Set.Icc ((k : ℝ) * L) ((k : ℝ) * L + L) := by
      intro t ht
      have htData := Finset.mem_filter.mp ht
      have htBase := hBase t htData.1
      have hbin := htData.2
      have hquotNonneg : 0 ≤ t / L := div_nonneg htBase.1 hL.le
      have hlowFloor : ((bin t : ℕ) : ℝ) ≤ t / L := Nat.floor_le hquotNonneg
      have hhighFloor : t / L < ((bin t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      constructor
      · rw [hbin] at hlowFloor
        exact (le_div_iff₀ hL).mp hlowFloor
      · rw [hbin] at hhighFloor
        have := (div_lt_iff₀ hL).mp hhighFloor
        nlinarith
    have hWkLarge : ∀ t ∈ Wk, V ≤ ‖dirichletPoly N a t‖ := by
      intro t ht
      exact hLarge t (Finset.mem_filter.mp ht).1
    change (Wk.card : ℝ) ≤ _
    exact local_classical_large_values N V ((k : ℝ) * L) L Wk a hN hV hWkSep
      hWkInterval hLN hWkLarge hAbsorb
  have hcard : W.card = ∑ k ∈ Finset.range K, ({t ∈ W | bin t = k}).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (W.card : ℝ) = ∑ k ∈ Finset.range K, (({t ∈ W | bin t = k}).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ k ∈ Finset.range K,
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
      exact Finset.sum_le_sum hfiber
    _ = ((Nat.floor (T / L) + 1 : ℕ) : ℝ) *
        (2 * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) *
          ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) / V ^ 2) := by
      simp only [sum_const, card_range, nsmul_eq_mul, K]

theorem dyadic_energy_le_length
    (N : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) :
    (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) ≤ (N : ℝ) := by
  calc
    (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) ≤
        ∑ n ∈ dyadicInterval N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [ha n hn, norm_nonneg (a n)]
    _ = (N : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, mul_one, dyadicInterval,
        Nat.card_Ioc]
      have hle : N ≤ 2 * N := by omega
      norm_num
      omega

/-- A nonempty set of values of height at least `V` forces the coefficient
energy to be at least `V²/N`. -/
theorem threshold_sq_le_length_mul_energy
    (N : ℕ) (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hV : 0 ≤ V) (hW : W.Nonempty)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    V ^ 2 ≤ (N : ℝ) * (∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2) := by
  obtain ⟨t, ht⟩ := hW
  have hcs := norm_sum_mul_sq_le (dyadicInterval N) a
    (fun n => unitaryPhase (logarithmicPhase t n))
  rw [← dirichletPoly_eq_logarithmicPhase] at hcs
  have hphase :
      (∑ n ∈ dyadicInterval N, ‖unitaryPhase (logarithmicPhase t n)‖ ^ 2) =
        (N : ℝ) := by
    simp only [norm_unitaryPhase, one_pow, sum_const, nsmul_eq_mul, mul_one,
      dyadicInterval, Nat.card_Ioc]
    have hle : N ≤ 2 * N := by omega
    norm_num
    omega
  rw [hphase] at hcs
  have hlarge := hLarge t ht
  have hnorm : 0 ≤ ‖dirichletPoly N a t‖ := norm_nonneg _
  nlinarith

/-- The Huxley (`V⁻⁶`) branch for bounded coefficients. -/
theorem classical_large_values_sixth_branch
    (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 0 ≤ T) (hV : 0 < V)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) :
    (W.card : ℝ) ≤
      4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
        ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) := by
  by_cases hW : W = ∅
  · subst W
    have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let G : ℝ := ∑ n ∈ dyadicInterval N, ‖a n‖ ^ 2
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hGleN : G ≤ (N : ℝ) := by
    dsimp only [G]
    exact dyadic_energy_le_length N a ha
  have hthreshold : V ^ 2 ≤ (N : ℝ) * G := by
    dsimp only [G]
    exact threshold_sq_le_length_mul_energy N V W a hV.le
      (Finset.nonempty_iff_ne_empty.mpr hW) hLarge
  have hGpos : 0 < G := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_pos_of_pos hV]
  let x : ℝ := V ^ 2 / (200 * G)
  let L : ℝ := x ^ 2
  have hx : 0 < x := by dsimp only [x]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hsqrtL : Real.sqrt L = x := by
    dsimp only [L]
    rw [Real.sqrt_sq hx.le]
  have hxN : x ≤ (N : ℝ) := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity : 0 < 200 * G)]
    nlinarith
  have hLN : L ≤ (N : ℝ) ^ 2 := by
    dsimp only [L]
    exact pow_le_pow_left₀ (by positivity) hxN 2
  have hAbsorb : 200 * G * Real.sqrt L ≤ V ^ 2 := by
    rw [hsqrtL]
    dsimp only [x]
    field_simp [hGpos.ne']
    norm_num
  have hlocal := classical_large_values_of_local_scale N T V L W a hN hV hL hLN
    hSep hBase hLarge (by simpa only [G] using hAbsorb)
  have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hB :
      (N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ)) ≤
        49 * (N : ℝ) * (1 + (((harmonic N : ℚ) : ℝ))) := by
    have hNreal : 0 ≤ (N : ℝ) := by positivity
    have hpi : 12 * Real.pi ≤ 48 := by nlinarith [Real.pi_lt_four]
    have hpiMul := mul_le_mul_of_nonneg_right hpi (mul_nonneg hNreal hH)
    nlinarith
  have hlocalFactor :
      2 * G * ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (((harmonic N : ℚ) : ℝ))) /
          V ^ 2 ≤
        98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2 := by
    have htwoG : 0 ≤ 2 * G := by positivity
    have hmul := mul_le_mul_of_nonneg_left hB htwoG
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hV)).2
    nlinarith
  have hqNonneg : 0 ≤ T / L := div_nonneg hT hL.le
  have hK : ((Nat.floor (T / L) + 1 : ℕ) : ℝ) ≤ T / L + 1 := by
    have hf := Nat.floor_le hqNonneg
    push_cast
    linarith
  have hrough :
      (W.card : ℝ) ≤ (T / L + 1) *
        (98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2) := by
    exact hlocal.trans (mul_le_mul hK hlocalFactor (by positivity) (by positivity))
  have hqIdentity : T / L = 40000 * T * G ^ 2 / V ^ 4 := by
    dsimp only [L, x]
    field_simp [hV.ne', hGpos.ne']
    ring
  rw [hqIdentity] at hrough
  have hGN : G * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hGleN (by positivity : 0 ≤ (N : ℝ))]
  have hG3 : G ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hG hGleN 3
  have hG3N : G ^ 3 * (N : ℝ) ≤ (N : ℝ) ^ 4 := by
    calc
      G ^ 3 * (N : ℝ) ≤ (N : ℝ) ^ 3 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hG3 (by positivity)
      _ = (N : ℝ) ^ 4 := by ring
  have htarget :
      (40000 * T * G ^ 2 / V ^ 4 + 1) *
          (98 * (1 + (((harmonic N : ℚ) : ℝ))) * G * (N : ℝ) / V ^ 2) ≤
        4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) ^ 4 / V ^ 6) := by
    have hfirst : 98 * G * V ^ 4 ≤ 4000000 * (N : ℝ) * V ^ 4 := by
      have hc : (98 : ℝ) * G ≤ 4000000 * (N : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hsecond : 3920000 * T * G ^ 3 ≤ 4000000 * T * (N : ℝ) ^ 3 := by
      have hc : (3920000 : ℝ) * G ^ 3 ≤ 4000000 * (N : ℝ) ^ 3 := by nlinarith
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hc hT
    field_simp [hV.ne']
    nlinarith [hfirst, hsecond]
  exact hrough.trans htarget

/-- The basic Montgomery mean-value branch, normalized to bounded
coefficients and the same algebraic shape as the sixth-power branch. -/
theorem classical_large_values_second_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
  rcases halasz_montgomery_lemma_native with ⟨C, hC, hHM⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hRawLarge : ∀ t ∈ W,
      V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ := by
    intro t ht
    simpa only [dirichletPoly, dyadicInterval, ofReal_neg, ofReal_mul] using hLarge t ht
  have hbound := hHM N T V W a hN hT hV hSep hBase hRawLarge
  have henergy := dyadic_energy_le_length N a ha
  have henergy' : (∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2) ≤ (N : ℝ) := by
    simpa only [dyadicInterval] using henergy
  have hTNonneg : 0 ≤ T := zero_le_one.trans hT
  have hTN : T + (N : ℝ) ≤ 2 * T := by linarith
  have hInv : V ^ (-2 : ℝ) = 1 / V ^ 2 := by
    rw [Real.rpow_neg hV.le, Real.rpow_two, inv_eq_one_div]
  rw [hInv] at hbound
  calc
    (W.card : ℝ) ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) *
        ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := hbound
    _ ≤ C * (2 * T) * (1 / V ^ 2) * (N : ℝ) := by
      gcongr
    _ ≤ (2 * C) * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
      have hNreal : 0 ≤ (N : ℝ) := by positivity
      have hV2 : 0 < V ^ 2 := sq_pos_of_pos hV
      field_simp [hV.ne']
      nlinarith [sq_nonneg (N : ℝ)]

/-- The mean-value branch does not intrinsically require `N ≤ T`. Keeping the
`N²/V²` diagonal term separately absorbs the additional `N` in `T+N`. This is
the form needed by the finite classical zero detector, whose convolution has
polynomially long support. -/
theorem classical_large_values_second_branch_unrestricted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by
  rcases halasz_montgomery_lemma_native with ⟨C, hC, hHM⟩
  refine ⟨C, hC, ?_⟩
  intro N T V W a hN hT hV ha hSep hBase hLarge
  have hRawLarge : ∀ t ∈ W,
      V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖ := by
    intro t ht
    simpa only [dirichletPoly, dyadicInterval, ofReal_neg, ofReal_mul] using hLarge t ht
  have hbound := hHM N T V W a hN hT hV hSep hBase hRawLarge
  have henergy := dyadic_energy_le_length N a ha
  have henergy' : (∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2) ≤ (N : ℝ) := by
    simpa only [dyadicInterval] using henergy
  have hInv : V ^ (-2 : ℝ) = 1 / V ^ 2 := by
    rw [Real.rpow_neg hV.le, Real.rpow_two, inv_eq_one_div]
  rw [hInv] at hbound
  calc
    (W.card : ℝ) ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) *
        ∑ n ∈ Ioc N (2 * N), ‖a n‖ ^ 2 := hbound
    _ ≤ C * (T + (N : ℝ)) * (1 / V ^ 2) * (N : ℝ) := by
      gcongr
    _ = C * ((N : ℝ) ^ 2 / V ^ 2 + T * (N : ℝ) / V ^ 2) := by ring

/-- The complete second/sixth-power classical estimate before logarithmic
absorption, valid for arbitrary positive polynomial length. -/
theorem classical_large_values_with_harmonic_unrestricted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  rcases classical_large_values_second_branch_unrestricted with ⟨C₂, hC₂, hSecond⟩
  let C := max C₂ 4000000
  refine ⟨C, lt_of_lt_of_le hC₂ (le_max_left _ _), ?_⟩
  intro N T V W a hN hT hV ha hSep hBase hLarge
  have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  by_cases hBD : (N : ℝ) / V ^ 2 ≤ (N : ℝ) ^ 4 / V ^ 6
  · rw [min_eq_left hBD]
    have hbasic := hSecond N T V W a hN hT hV ha hSep hBase hLarge
    have hbasic' : (W.card : ℝ) ≤
        C₂ * ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) := by
      simpa only [mul_div_assoc] using hbasic
    have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2) := by
      positivity
    have hCscale : C₂ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) := by
      have hCnonneg : 0 ≤ C := (lt_of_lt_of_le hC₂ (le_max_left _ _)).le
      exact (le_max_left C₂ 4000000).trans <| by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (by linarith : 1 ≤ 1 + (((harmonic N : ℚ) : ℝ))) hCnonneg
    exact hbasic'.trans (mul_le_mul_of_nonneg_right hCscale hinner)
  · rw [min_eq_right (le_of_not_ge hBD)]
    have hsixth := classical_large_values_sixth_branch N T V W a hN
      (zero_le_one.trans hT) hV ha hSep hBase hLarge
    have hsixth' : (W.card : ℝ) ≤
        4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := by
      simpa only [mul_div_assoc] using hsixth
    have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6) := by
      positivity
    have hcoef : 4000000 * (1 + (((harmonic N : ℚ) : ℝ))) ≤
        C * (1 + (((harmonic N : ℚ) : ℝ))) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    exact hsixth'.trans (mul_le_mul_of_nonneg_right hcoef hinner)

/-- The two classical branches combined before absorbing the harmonic loss. -/
theorem classical_large_values_with_harmonic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * (1 + (((harmonic N : ℚ) : ℝ))) *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
  rcases classical_large_values_second_branch with ⟨C₂, hC₂, hSecond⟩
  let C := max C₂ 4000000
  refine ⟨C, lt_of_lt_of_le hC₂ (le_max_left _ _), ?_⟩
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hH : 0 ≤ (((harmonic N : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hA : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 := by positivity
  have hB : 0 ≤ (N : ℝ) / V ^ 2 := by positivity
  have hD : 0 ≤ (N : ℝ) ^ 4 / V ^ 6 := by positivity
  by_cases hBD : (N : ℝ) / V ^ 2 ≤ (N : ℝ) ^ 4 / V ^ 6
  · rw [min_eq_left hBD]
    have hbasic := hSecond N T V W a hN hT hNT hV ha hSep hBase hLarge
    have hbasic' : (W.card : ℝ) ≤
        C₂ * ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) := by
      simpa only [mul_div_assoc] using hbasic
    calc
      (W.card : ℝ) ≤ C₂ * ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) :=
        hbasic'
      _ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2)) := by
        have hC₂C : C₂ ≤ C := le_max_left _ _
        have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) / V ^ 2) := by
          positivity
        have hC : 0 ≤ C := (lt_of_lt_of_le hC₂ hC₂C).le
        have hCscale : C ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              (by linarith : 1 ≤ 1 + (((harmonic N : ℚ) : ℝ))) hC
        exact mul_le_mul_of_nonneg_right (hC₂C.trans hCscale) hinner
  · rw [min_eq_right (le_of_not_ge hBD)]
    have hsixth := classical_large_values_sixth_branch N T V W a hN
      (zero_le_one.trans hT) hV ha hSep hBase hLarge
    have hsixth' : (W.card : ℝ) ≤
        4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := by
      simpa only [mul_div_assoc] using hsixth
    calc
      (W.card : ℝ) ≤ 4000000 * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := hsixth'
      _ ≤ C * (1 + (((harmonic N : ℚ) : ℝ))) *
          ((N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6)) := by
        have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 + T * ((N : ℝ) ^ 4 / V ^ 6) := by
          positivity
        have hcoef : 4000000 * (1 + (((harmonic N : ℚ) : ℝ))) ≤
            C * (1 + (((harmonic N : ℚ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
        exact mul_le_mul_of_nonneg_right hcoef hinner

/-- The full finite Montgomery--Halász--Huxley estimate required by Package C
of Shitlist #15. -/
def ClassicalMontgomeryHalaszHuxley : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 1 ≤ T → (N : ℝ) ≤ T → 0 < V →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∀ t ∈ W, V ≤ ‖dirichletPoly N a t‖) →
        (W.card : ℝ) ≤
          C * T ^ ε *
            ((N : ℝ) ^ 2 / V ^ 2 +
              T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6))

theorem classical_montgomery_halasz_huxley_native :
    ClassicalMontgomeryHalaszHuxley := by
  intro ε hε
  rcases classical_large_values_with_harmonic with ⟨C₀, hC₀, hBound⟩
  refine ⟨C₀ * (2 + 1 / ε), by positivity, ?_⟩
  intro N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hraw := hBound N T V W a hN hT hNT hV ha hSep hBase hLarge
  have hHlog : (((harmonic N : ℚ) : ℝ)) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  have hlogPow : Real.log N ≤ (N : ℝ) ^ ε / ε :=
    Real.log_natCast_le_rpow_div N hε
  have hpowMono : (N : ℝ) ^ ε ≤ T ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNT hε.le
  have hpowOne : 1 ≤ T ^ ε := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hε.le
  have hfactor : 1 + (((harmonic N : ℚ) : ℝ)) ≤ (2 + 1 / ε) * T ^ ε := by
    have hdivMono : (N : ℝ) ^ ε / ε ≤ T ^ ε / ε :=
      div_le_div_of_nonneg_right hpowMono hε.le
    calc
      1 + (((harmonic N : ℚ) : ℝ)) ≤ 2 + Real.log N := by linarith
      _ ≤ 2 + (N : ℝ) ^ ε / ε := add_le_add_right hlogPow 2
      _ ≤ 2 + T ^ ε / ε := add_le_add_right hdivMono 2
      _ ≤ 2 * T ^ ε + T ^ ε / ε := by
        simpa only [add_comm] using
          add_le_add_right (by nlinarith [hpowOne] : (2 : ℝ) ≤ 2 * T ^ ε)
            (T ^ ε / ε)
      _ = (2 + 1 / ε) * T ^ ε := by ring
  have hinner : 0 ≤ (N : ℝ) ^ 2 / V ^ 2 +
      T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) := by
    have hmin : 0 ≤ min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6) := by positivity
    positivity
  calc
    (W.card : ℝ) ≤ C₀ * (1 + (((harmonic N : ℚ) : ℝ))) *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := hraw
    _ ≤ (C₀ * (2 + 1 / ε)) * T ^ ε *
        ((N : ℝ) ^ 2 / V ^ 2 +
          T * min ((N : ℝ) / V ^ 2) ((N : ℝ) ^ 4 / V ^ 6)) := by
      have hscale := mul_le_mul_of_nonneg_left hfactor hC₀.le
      have hmul := mul_le_mul_of_nonneg_right hscale hinner
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

end RiemannZeta.GuthMaynard
