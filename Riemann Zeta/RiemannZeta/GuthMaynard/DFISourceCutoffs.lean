import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import RiemannZeta.GuthMaynard.DFIDelta
import RiemannZeta.GuthMaynard.DFIEquation21

open Complex Set
open scoped ContDiff Topology

namespace RiemannZeta.GuthMaynard

/-!
# Source cutoffs for DFI equations (9) and (21)

The structures used earlier in the DFI chain record the exact source
hypotheses, but those hypotheses also have to be inhabited.  This file
constructs the two smooth cutoffs from ordinary `ContDiffBump`s.  The
derivative constants are obtained from compact support, so no analytic
existence assumption is introduced.
-/

/-- Every iterated derivative of a compactly supported smooth function is
again compactly supported. -/
theorem hasCompactSupport_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Compact support supplies precisely the derivative constants required by
the source cutoff interfaces, at every positive physical scale. -/
theorem exists_scaled_iteratedDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) {A : ℝ} (hA : 0 < A) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedDeriv k f x‖ ≤ C * A⁻¹ ^ k := by
  obtain ⟨B, hB⟩ :=
    (hf.continuous_iteratedDeriv k
      (show (k : ℕ∞ω) ≤ ∞ from mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv f hcompact k)
  let C : ℝ := (max B 0 + 1) * A ^ k
  have hbase : 0 < max B 0 + 1 := by
    have : 0 ≤ max B 0 := le_max_right _ _
    linarith
  have hC : 0 < C := mul_pos hbase (pow_pos hA _)
  refine ⟨C, hC, fun x => ?_⟩
  calc
    ‖iteratedDeriv k f x‖ ≤ B := hB x
    _ ≤ max B 0 + 1 := by exact (le_max_left _ _).trans (by linarith)
    _ = C * A⁻¹ ^ k := by
      dsimp [C]
      rw [inv_pow]
      field_simp [hA.ne']

/-- Equation (9) writes the scale factor as `Q^(-k-1)` rather than
`Q^(-k)`.  Since its implicit constant may depend on the chosen cutoff,
the additional factor of `Q` is absorbed explicitly here. -/
theorem exists_delta_iteratedDeriv_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {Q : ℝ} (hQ : 0 < Q) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedDeriv k f x‖ ≤ C * (Q ^ (k + 1))⁻¹ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_scaled_iteratedDeriv_bound hf hcompact hQ k
  refine ⟨C * Q, mul_pos hC hQ, fun x => (hbound x).trans_eq ?_⟩
  rw [pow_succ, inv_pow]
  field_simp [hQ.ne']

/-- The centered bump used for the redundant factor before DFI equation
(21). -/
noncomputable def dfiStandardRedundantBump (U : ℝ) (hU : 0 < U) :
    ContDiffBump (0 : ℝ) :=
  ⟨U / 2, U, by positivity, by linarith⟩

/-- A concrete complex-valued redundant cutoff at scale `U`. -/
noncomputable def dfiStandardRedundantCutoff (U : ℝ) (hU : 0 < U) : ℝ → ℂ :=
  Complex.ofRealCLM ∘ dfiStandardRedundantBump U hU

/-- The standard centered bump satisfies the complete source interface used
in DFI equation (21). -/
theorem dfiStandardRedundantCutoff_spec (U : ℝ) (hU : 0 < U) :
    DFIRedundantCutoff (dfiStandardRedundantCutoff U hU) U := by
  let b := dfiStandardRedundantBump U hU
  have hbSmooth : ContDiff ℝ ∞ (b : ℝ → ℝ) := b.contDiff
  have hbCompact : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hφSmooth : ContDiff ℝ ∞ (dfiStandardRedundantCutoff U hU) := by
    exact Complex.ofRealCLM.contDiff.comp hbSmooth
  have hφCompact : HasCompactSupport (dfiStandardRedundantCutoff U hU) := by
    exact hbCompact.comp_left (by simp [Complex.ofRealCLM_apply])
  refine
    { U_pos := hU
      smooth := hφSmooth
      compactSupport := hφCompact
      support_subset := ?_
      value_zero := ?_
      derivativeBound := fun k =>
        exists_scaled_iteratedDeriv_bound hφSmooth hφCompact hU k }
  · intro x hx
    have hbx : b x ≠ 0 := by
      intro hz
      apply hx
      simp [dfiStandardRedundantCutoff, b, hz]
    have hxball : x ∈ Metric.ball (0 : ℝ) U := by
      rw [← show b.rOut = U by rfl, ← b.support_eq]
      exact hbx
    have habs : |x| < U := by
      simpa [Metric.mem_ball, Real.dist_eq] using hxball
    exact (abs_lt.mp habs)
  · have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (U / 2) := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using div_nonneg hU.le (by norm_num : (0 : ℝ) ≤ 2)
    simp [dfiStandardRedundantCutoff, b, b.one_of_mem_closedBall hzero]

/-- The positive integer at which the equation-(9) weight is normalized. -/
noncomputable def dfiDeltaCenter (Q : ℝ) : ℕ := Nat.ceil Q + 1

theorem dfiDeltaCenter_pos (Q : ℝ) : 0 < dfiDeltaCenter Q := by
  unfold dfiDeltaCenter
  omega

theorem dfiDeltaCenter_left {Q : ℝ} (_hQ : 0 ≤ Q) :
    Q < (dfiDeltaCenter Q : ℝ) := by
  unfold dfiDeltaCenter
  push_cast
  exact lt_of_le_of_lt (Nat.le_ceil Q) (lt_add_one _)

theorem dfiDeltaCenter_right {Q : ℝ} (hQ : 2 ≤ Q) :
    (dfiDeltaCenter Q : ℝ) < 2 * Q := by
  rw [dfiDeltaCenter, Nat.cast_add, Nat.cast_one]
  have hQ0 : 0 ≤ Q := by linarith
  have hc := Nat.ceil_lt_add_one hQ0
  nlinarith

/-- A radius strictly inside the source annulus and below one quarter. -/
noncomputable def dfiDeltaBumpRadius (Q : ℝ) : ℝ :=
  min ((min ((dfiDeltaCenter Q : ℝ) - Q)
    (2 * Q - (dfiDeltaCenter Q : ℝ))) / 2) (1 / 4)

theorem dfiDeltaBumpRadius_pos {Q : ℝ} (hQ : 2 ≤ Q) :
    0 < dfiDeltaBumpRadius Q := by
  unfold dfiDeltaBumpRadius
  have hQ0 : 0 ≤ Q := by linarith
  have hl := sub_pos.mpr (dfiDeltaCenter_left hQ0)
  have hr := sub_pos.mpr (dfiDeltaCenter_right hQ)
  positivity

theorem dfiDeltaBumpRadius_le_quarter (Q : ℝ) :
    dfiDeltaBumpRadius Q ≤ 1 / 4 := by
  exact min_le_right _ _

theorem dfiDeltaBumpRadius_lt_left {Q : ℝ} (hQ : 2 ≤ Q) :
    dfiDeltaBumpRadius Q < (dfiDeltaCenter Q : ℝ) - Q := by
  have hr := dfiDeltaBumpRadius_pos hQ
  have hle : dfiDeltaBumpRadius Q ≤
      ((dfiDeltaCenter Q : ℝ) - Q) / 2 := by
    refine (min_le_left _ _).trans ?_
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hQ0 : 0 ≤ Q := by linarith
  nlinarith [dfiDeltaCenter_left hQ0]

theorem dfiDeltaBumpRadius_lt_right {Q : ℝ} (hQ : 2 ≤ Q) :
    dfiDeltaBumpRadius Q < 2 * Q - (dfiDeltaCenter Q : ℝ) := by
  have hr := dfiDeltaBumpRadius_pos hQ
  have hle : dfiDeltaBumpRadius Q ≤
      (2 * Q - (dfiDeltaCenter Q : ℝ)) / 2 := by
    refine (min_le_left _ _).trans ?_
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  nlinarith [dfiDeltaCenter_right hQ]

/-- One half of the even equation-(9) cutoff. -/
noncomputable def dfiDeltaPositiveBump (Q : ℝ) (hQ : 2 ≤ Q) :
    ContDiffBump (dfiDeltaCenter Q : ℝ) :=
  ⟨dfiDeltaBumpRadius Q / 2, dfiDeltaBumpRadius Q,
    div_pos (dfiDeltaBumpRadius_pos hQ) (by norm_num),
    by nlinarith [dfiDeltaBumpRadius_pos hQ]⟩

/-- The explicit even annular function used in DFI equation (9). -/
noncomputable def dfiStandardDeltaWeightFun (Q : ℝ) (hQ : 2 ≤ Q) : ℝ → ℝ :=
  fun u => dfiDeltaPositiveBump Q hQ u + dfiDeltaPositiveBump Q hQ (-u)

theorem dfiStandardDeltaWeightFun_smooth (Q : ℝ) (hQ : 2 ≤ Q) :
    ContDiff ℝ ∞ (dfiStandardDeltaWeightFun Q hQ) := by
  exact (dfiDeltaPositiveBump Q hQ).contDiff.add
    ((dfiDeltaPositiveBump Q hQ).contDiff.comp contDiff_neg)

theorem dfiStandardDeltaWeightFun_even (Q : ℝ) (hQ : 2 ≤ Q) (u : ℝ) :
    dfiStandardDeltaWeightFun Q hQ (-u) = dfiStandardDeltaWeightFun Q hQ u := by
  simp only [dfiStandardDeltaWeightFun, neg_neg]
  ring

/-- The positive half-bump vanishes outside its radius. -/
theorem dfiDeltaPositiveBump_eq_zero_of_radius_le {Q x : ℝ} (hQ : 2 ≤ Q)
    (hx : dfiDeltaBumpRadius Q ≤ dist x (dfiDeltaCenter Q : ℝ)) :
    dfiDeltaPositiveBump Q hQ x = 0 := by
  exact (dfiDeltaPositiveBump Q hQ).zero_of_le_dist hx

/-- At positive integer arguments the even cutoff has exactly one nonzero
sample, at `⌈Q⌉+1`. -/
theorem dfiStandardDeltaWeightFun_natCast (Q : ℝ) (hQ : 2 ≤ Q) (m : ℕ)
    (hm : 0 < m) :
    dfiStandardDeltaWeightFun Q hQ (m : ℝ) =
      if m = dfiDeltaCenter Q then 1 else 0 := by
  by_cases hmc : m = dfiDeltaCenter Q
  · subst m
    have hcenter : (dfiDeltaCenter Q : ℝ) ∈
        Metric.closedBall (dfiDeltaCenter Q : ℝ) (dfiDeltaBumpRadius Q / 2) := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using
        div_nonneg (dfiDeltaBumpRadius_pos hQ).le (by norm_num : (0 : ℝ) ≤ 2)
    have hnegdist : dfiDeltaBumpRadius Q ≤
        dist (-(dfiDeltaCenter Q : ℝ)) (dfiDeltaCenter Q : ℝ) := by
      rw [Real.dist_eq]
      have hc : (1 : ℝ) ≤ dfiDeltaCenter Q := by
        exact_mod_cast (dfiDeltaCenter_pos Q)
      have hr := dfiDeltaBumpRadius_le_quarter Q
      rw [abs_of_nonpos (by linarith : -(dfiDeltaCenter Q : ℝ) -
        (dfiDeltaCenter Q : ℝ) ≤ 0)]
      nlinarith
    simp only [dfiStandardDeltaWeightFun]
    rw [(dfiDeltaPositiveBump Q hQ).one_of_mem_closedBall hcenter,
      dfiDeltaPositiveBump_eq_zero_of_radius_le hQ hnegdist]
    norm_num
  · have hdist : dfiDeltaBumpRadius Q ≤
        dist (m : ℝ) (dfiDeltaCenter Q : ℝ) := by
      rw [Real.dist_eq]
      have hcast : (m : ℝ) ≠ (dfiDeltaCenter Q : ℝ) := by exact_mod_cast hmc
      have hone : (1 : ℝ) ≤ |(m : ℝ) - (dfiDeltaCenter Q : ℝ)| := by
        rcases lt_or_gt_of_ne hmc with hlt | hgt
        · have hstep : (m : ℝ) + 1 ≤ (dfiDeltaCenter Q : ℝ) := by
            exact_mod_cast (Nat.add_one_le_iff.mpr hlt)
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hstep : (dfiDeltaCenter Q : ℝ) + 1 ≤ m := by
            exact_mod_cast (Nat.add_one_le_iff.mpr hgt)
          rw [abs_of_nonneg (by linarith)]
          linarith
      exact (dfiDeltaBumpRadius_le_quarter Q).trans (by linarith)
    have hnegdist : dfiDeltaBumpRadius Q ≤
        dist (-(m : ℝ)) (dfiDeltaCenter Q : ℝ) := by
      rw [Real.dist_eq]
      have hc : (1 : ℝ) ≤ dfiDeltaCenter Q := by
        exact_mod_cast (dfiDeltaCenter_pos Q)
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hr := dfiDeltaBumpRadius_le_quarter Q
      rw [abs_of_nonpos (by linarith : -(m : ℝ) -
        (dfiDeltaCenter Q : ℝ) ≤ 0)]
      nlinarith
    simp only [dfiStandardDeltaWeightFun, if_neg hmc]
    rw [dfiDeltaPositiveBump_eq_zero_of_radius_le hQ hdist,
      dfiDeltaPositiveBump_eq_zero_of_radius_le hQ hnegdist]
    norm_num

/-- Exact equation-(9) normalization of the concrete annular weight. -/
theorem dfiStandardDeltaWeightFun_normalized (Q : ℝ) (hQ : 2 ≤ Q) :
    ∑' r : ℕ, dfiStandardDeltaWeightFun Q hQ (r + 1 : ℕ) = 1 := by
  let c := dfiDeltaCenter Q
  have hc : 0 < c := dfiDeltaCenter_pos Q
  rw [tsum_eq_single (c - 1)]
  · have hindex : c - 1 + 1 = c := by omega
    have hcast : ((c - 1 + 1 : ℕ) : ℝ) = (c : ℝ) := by norm_cast
    rw [hcast]
    simpa [c] using dfiStandardDeltaWeightFun_natCast Q hQ c hc
  · intro r hre
    have hrp : 0 < r + 1 := by omega
    have hrne : r + 1 ≠ c := by
      intro h
      apply hre
      omega
    simpa [c, hrne] using dfiStandardDeltaWeightFun_natCast Q hQ (r + 1) hrp

theorem dfiStandardDeltaWeightFun_support_annulus (Q : ℝ) (hQ : 2 ≤ Q) :
    Function.support (dfiStandardDeltaWeightFun Q hQ) ⊆
      {u : ℝ | Q ≤ |u| ∧ |u| ≤ 2 * Q} := by
  intro u hu
  have hor : dfiDeltaPositiveBump Q hQ u ≠ 0 ∨
      dfiDeltaPositiveBump Q hQ (-u) ≠ 0 := by
    contrapose! hu
    simp [dfiStandardDeltaWeightFun, hu]
  rcases hor with hplus | hminus
  · have hball : u ∈ Metric.ball (dfiDeltaCenter Q : ℝ)
        (dfiDeltaBumpRadius Q) := by
      rw [← show (dfiDeltaPositiveBump Q hQ).rOut =
        dfiDeltaBumpRadius Q by rfl, ← (dfiDeltaPositiveBump Q hQ).support_eq]
      exact hplus
    have hdist : |u - (dfiDeltaCenter Q : ℝ)| < dfiDeltaBumpRadius Q := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have hcpos : 0 < (dfiDeltaCenter Q : ℝ) := by
      exact_mod_cast dfiDeltaCenter_pos Q
    have hl := dfiDeltaBumpRadius_lt_left hQ
    have hr := dfiDeltaBumpRadius_lt_right hQ
    have huQ : Q < u := by
      rw [abs_lt] at hdist
      linarith
    have hu2Q : u < 2 * Q := by
      rw [abs_lt] at hdist
      linarith
    change Q ≤ |u| ∧ |u| ≤ 2 * Q
    rw [abs_of_pos (lt_of_lt_of_le (by linarith : 0 < Q) huQ.le)]
    exact ⟨huQ.le, hu2Q.le⟩
  · have hball : -u ∈ Metric.ball (dfiDeltaCenter Q : ℝ)
        (dfiDeltaBumpRadius Q) := by
      rw [← show (dfiDeltaPositiveBump Q hQ).rOut =
        dfiDeltaBumpRadius Q by rfl, ← (dfiDeltaPositiveBump Q hQ).support_eq]
      exact hminus
    have hdist : |-u - (dfiDeltaCenter Q : ℝ)| < dfiDeltaBumpRadius Q := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have hl := dfiDeltaBumpRadius_lt_left hQ
    have hr := dfiDeltaBumpRadius_lt_right hQ
    have huQ : Q < -u := by
      rw [abs_lt] at hdist
      linarith
    have hu2Q : -u < 2 * Q := by
      rw [abs_lt] at hdist
      linarith
    have huneg : u < 0 := by linarith [show 0 < Q by linarith]
    change Q ≤ |u| ∧ |u| ≤ 2 * Q
    rw [abs_of_neg huneg]
    exact ⟨huQ.le, hu2Q.le⟩

/-- A concrete inhabitant of the DFI equation-(9) weight interface. -/
noncomputable def dfiStandardDeltaWeight (Q : ℝ) (hQ : 2 ≤ Q) :
    DFIDeltaWeight Q where
  toFun := dfiStandardDeltaWeightFun Q hQ
  one_le_Q := le_trans (by norm_num) hQ
  smooth := dfiStandardDeltaWeightFun_smooth Q hQ
  even := dfiStandardDeltaWeightFun_even Q hQ
  support_annulus := dfiStandardDeltaWeightFun_support_annulus Q hQ
  normalized := dfiStandardDeltaWeightFun_normalized Q hQ
  derivativeBound := fun k =>
    exists_delta_iteratedDeriv_bound
      (dfiStandardDeltaWeightFun_smooth Q hQ)
      (by
        have hp : HasCompactSupport
            (dfiDeltaPositiveBump Q hQ : ℝ → ℝ) :=
          (dfiDeltaPositiveBump Q hQ).hasCompactSupport
        have hn : HasCompactSupport (fun x : ℝ =>
            dfiDeltaPositiveBump Q hQ (-x)) := by
          convert hp.comp_smul (c := (-1 : ℝ)) (by norm_num) using 1
          funext x
          simp only [neg_one_smul]
        simpa only [dfiStandardDeltaWeightFun] using hp.add hn)
      (by linarith) k

end RiemannZeta.GuthMaynard
