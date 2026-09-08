import RiemannZeta.GuthMaynard.ClassicalDichotomy
import RiemannZeta.GuthMaynard.WeylZeta

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Terminal Type-I blocks

At the terminal end of the ordinary-zeta Type-I range the logarithmic
phase has first derivative bounded away from a full period.  The finite
Kusmin--Landau estimate therefore controls every prefix, and Abel summation
transfers that cancellation to the decreasing weight `n^(-sigma)`.
-/

/-- Uniform first-derivative cancellation for every prefix beginning just
to the right of `A`.  The deliberately generous constant is uniform in the
prefix length. -/
theorem norm_logarithmicPhase_prefix_le_div
    (A L : ℕ) (t : ℝ) (hA : 0 < A) (hL : L ≤ A)
    (htOne : 1 ≤ t) (htA : t ≤ (A : ℝ)) :
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      6 * Real.pi * (A : ℝ) / t := by
  by_cases hL0 : L = 0
  · subst L
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  let δ : ℝ := t / (3 * (A : ℝ))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hinc (n : ℕ) (hn : n ≤ L - 1) :
      let m := A + 1 + n
      δ ≤ logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ∧
        logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ≤
          2 * Real.pi - δ := by
    dsimp only
    let m := A + 1 + n
    have hm : 0 < m := by dsimp only [m]; omega
    have hmLower : A ≤ m := by dsimp only [m]; omega
    have hmUpper : m + 1 ≤ 3 * A := by
      dsimp only [m]
      omega
    have hlogs :
        1 / ((m : ℝ) + 1) ≤
            Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ∧
          Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
            1 / (m : ℝ) := by
      have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
      have hsuccReal : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hratio : 0 < (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by positivity
      have hlog :
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
            Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
        Real.log_div hsuccReal.ne' hmReal.ne'
      constructor
      · calc
          1 / ((m : ℝ) + 1) =
              1 - ((((m + 1 : ℕ) : ℝ) / (m : ℝ))⁻¹) := by
                push_cast
                field_simp [hmReal.ne']
                ring
          _ ≤ Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos hratio
          _ = Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := hlog
      · rw [← hlog]
        calc
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
              ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos hratio
          _ = 1 / (m : ℝ) := by
            push_cast
            field_simp [hmReal.ne']
            ring
    have hphase :
        logarithmicPhase t (m + 1) - logarithmicPhase t m =
          -t * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_one]
      ring
    rw [hphase]
    have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmLowerReal : (A : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmLower
    have hmUpperReal : ((m : ℝ) + 1) ≤ 3 * (A : ℝ) := by
      exact_mod_cast hmUpper
    have htOverM : t / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmReal]
      exact htA.trans hmLowerReal
    have hdeltaLeThird : δ ≤ 1 / 3 := by
      dsimp only [δ]
      rw [div_le_iff₀ (by positivity : 0 < 3 * (A : ℝ))]
      nlinarith
    have hdeltaLog : δ ≤ t *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      have hrecip : 1 / (3 * (A : ℝ)) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmUpperReal
      dsimp only [δ]
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left hrecip (zero_le_one.trans htOne)).trans
          (mul_le_mul_of_nonneg_left hlogs.1 (zero_le_one.trans htOne))
    constructor
    · have hlogUpper : t *
          (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left hlogs.2 (zero_le_one.trans htOne)).trans (by
          simpa only [div_eq_mul_inv, one_mul] using htOverM)
      nlinarith [Real.pi_gt_three]
    · linarith
  have hmono : ∀ n < L - 1,
      logarithmicPhase t (A + 1 + n + 1) - logarithmicPhase t (A + 1 + n) ≤
        logarithmicPhase t (A + 1 + n + 2) -
          logarithmicPhase t (A + 1 + n + 1) := by
    intro n hn
    let m := A + 1 + n
    have hm : 0 < m := by dsimp only [m]; omega
    have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmOneReal : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hratioLe :
        ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
          ((m + 1 : ℕ) : ℝ) / (m : ℝ) := by
      rw [div_le_div_iff₀ hmOneReal hmReal]
      push_cast
      nlinarith
    have hlogLe := Real.strictMonoOn_log.monotoneOn
      (by show 0 < ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ); positivity)
      (by show 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ); positivity) hratioLe
    have hphaseOne :
        logarithmicPhase t (m + 1) - logarithmicPhase t m =
          -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
      rw [Real.log_div (by positivity) hmReal.ne']
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_one]
      ring
    have hphaseTwo :
        logarithmicPhase t (m + 2) - logarithmicPhase t (m + 1) =
          -t * Real.log (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
      rw [Real.log_div (by positivity) hmOneReal.ne']
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_ofNat]
      ring_nf
    have hfinal := mul_le_mul_of_nonpos_left hlogLe (by linarith : -t ≤ 0)
    rw [← hphaseOne, ← hphaseTwo] at hfinal
    simpa only [m, Nat.cast_add, Nat.cast_one, add_assoc] using hfinal
  have hKL := kusminLandau_interval (fun n : ℕ => logarithmicPhase t n)
    (A + 1) (L - 1) (-1) δ hδ
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, add_assoc] using (hinc n hn).1)
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, add_assoc] using (hinc n hn).2)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hmono n hn)
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred] at hKL
  calc
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
        2 * Real.pi / δ := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hKL
    _ = 6 * Real.pi * (A : ℝ) / t := by
      dsimp only [δ]
      field_simp [show t ≠ 0 by linarith, hAReal.ne']
      ring

/-- Abel-summed terminal estimate for a sharp ordinary-zeta block. -/
theorem norm_terminalWeightedBlock_le
    (σ t : ℝ) (A L : ℕ) (hσ : 0 ≤ σ) (hA : 0 < A)
    (hL : 0 < L) (hLA : L ≤ A) (htOne : 1 ≤ t) (htA : t ≤ (A : ℝ)) :
    ‖∑ n ∈ Finset.range L,
        ((A + 1 + n : ℝ) ^ (-σ) : ℝ) •
          unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      (A + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (A : ℝ) / t) := by
  let f : ℕ → ℝ := fun n => (A + 1 + n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n =>
    unitaryPhase (logarithmicPhase t (A + 1 + n))
  have hBound := norm_weighted_sum_le_of_antitone f g L
    (6 * Real.pi * (A : ℝ) / t) hL
    (by
      intro i _
      dsimp only [f]
      positivity)
    (by
      intro i _
      dsimp only [f]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show A + 1 + i ≤ A + 1 + (i + 1) by omega)
      · linarith)
    (by
      intro j hj
      dsimp only [g]
      exact norm_logarithmicPhase_prefix_le_div A j t hA (hj.trans hLA) htOne htA)
  simpa only [f, g, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using hBound

/-- The sharp-cutoff Type-I coefficients on a dyadic block are exactly a
decreasing real weight, followed (if necessary) by zeros. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_terminal
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      ∑ i ∈ Finset.range N,
        (if N + 1 + i ≤ C then
          ((N + 1 + i : ℝ) ^ (-σ) : ℝ) •
            unitaryPhase (logarithmicPhase t (N + 1 + i))
        else 0) := by
  unfold dirichletPoly
  rw [dyadicInterval_eq_Ico_succ, Finset.sum_Ico_eq_sum_range]
  have hLength : 2 * N + 1 - (N + 1) = N := by omega
  rw [hLength]
  apply Finset.sum_congr rfl
  intro i hi
  have hm : 0 < N + 1 + i := by omega
  by_cases hmC : N + 1 + i ≤ C
  · rw [if_pos hmC, classicalZetaLongLineCoeff_term C (N + 1 + i) σ t hm hmC]
    have hcastReal : ((N + 1 + i : ℕ) : ℝ) = (N : ℝ) + 1 + (i : ℝ) := by
      push_cast
      ring
    rw [← hcastReal]
    rw [Complex.real_smul,
      unitaryPhase_logarithmicPhase_eq_cpow t (N + 1 + i) hm]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (N + 1 + i))]
    simp only [Complex.ofReal_natCast]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hm.ne')]
    congr 2
    push_cast
    ring
  · rw [if_neg hmC, classicalZetaLongLineCoeff, if_neg hmC, zero_mul]

/-- Concrete terminal estimate for the actual sharp Type-I dyadic block.
It remains valid when the sharp upper cutoff stops inside the block. -/
theorem norm_terminal_classicalZetaLongLineCoeff_le
    (C N : ℕ) (σ t : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (htOne : 1 ≤ t) (htN : t ≤ (N : ℝ)) :
    ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖ ≤
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) := by
  let f : ℕ → ℝ := fun i =>
    if N + 1 + i ≤ C then (N + 1 + i : ℝ) ^ (-σ) else 0
  let g : ℕ → ℂ := fun i =>
    unitaryPhase (logarithmicPhase t (N + 1 + i))
  have hanti : ∀ i, i + 1 < N → f (i + 1) ≤ f i := by
    intro i hi
    dsimp only [f]
    by_cases hnext : N + 1 + (i + 1) ≤ C
    · have hcurrent : N + 1 + i ≤ C := by omega
      rw [if_pos hnext, if_pos hcurrent]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show N + 1 + i ≤ N + 1 + (i + 1) by omega)
      · linarith
    · rw [if_neg hnext]
      positivity
  have hBound := norm_weighted_sum_le_of_antitone f g N
    (6 * Real.pi * (N : ℝ) / t) hN
    (by
      intro i hi
      dsimp only [f]
      split_ifs
      · positivity
      · exact le_rfl)
    hanti
    (by
      intro j hj
      dsimp only [g]
      exact norm_logarithmicPhase_prefix_le_div N j t hN hj htOne htN)
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_terminal C N σ t hN]
  have hStart : N + 1 ≤ C := by omega
  simpa only [f, g, if_pos hStart, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, add_zero, ite_smul, zero_smul] using hBound

/-- A block whose asserted detector threshold exceeds the terminal
Kusmin--Landau majorant must lie strictly below the height.  This is the
case-splitting form consumed by the finite density reduction. -/
theorem typeI_scale_lt_height_of_large
    (C N : ℕ) (σ t V : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N)
    (hNC : N < C) (htOne : 1 ≤ t)
    (hLarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖)
    (hMajorant :
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) < V) :
    (N : ℝ) < t := by
  by_contra hNot
  have htN : t ≤ (N : ℝ) := le_of_not_gt hNot
  have hUpper := norm_terminal_classicalZetaLongLineCoeff_le
    C N σ t hσ hN hNC htOne htN
  linarith

end RiemannZeta.GuthMaynard
