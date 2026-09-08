import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import RiemannZeta.GuthMaynard.DFIDelta
import RiemannZeta.GuthMaynard.DFIEstimates
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

/-! ## A genuinely scale-uniform redundant-cutoff family -/

/-- One fixed unit-scale bump.  Rescaling this function, rather than choosing
a new bump at every physical scale, preserves one family of derivative
constants. -/
noncomputable def dfiUnitRedundantBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fixed complex-valued unit cutoff. -/
noncomputable def dfiUnitRedundantCutoff : ℝ → ℂ :=
  Complex.ofRealCLM ∘ dfiUnitRedundantBump

/-- Scale the fixed unit cutoff to physical radius `U`. -/
noncomputable def dfiUniformRedundantCutoff (U : ℝ) : ℝ → ℂ :=
  fun x ↦ dfiUnitRedundantCutoff (U⁻¹ * x)

theorem dfiUniformRedundantCutoff_spec (U : ℝ) (hU : 0 < U) :
    DFIRedundantCutoff (dfiUniformRedundantCutoff U) U := by
  have hunitSmooth : ContDiff ℝ ∞ dfiUnitRedundantCutoff := by
    exact Complex.ofRealCLM.contDiff.comp dfiUnitRedundantBump.contDiff
  have hsmooth : ContDiff ℝ ∞ (dfiUniformRedundantCutoff U) := by
    simpa only [dfiUniformRedundantCutoff] using
      hunitSmooth.comp (contDiff_const.mul contDiff_id)
  have hcompactReal : HasCompactSupport
      (fun x : ℝ ↦ dfiUnitRedundantBump (U⁻¹ * x)) := by
    simpa only [smul_eq_mul] using
      dfiUnitRedundantBump.hasCompactSupport.comp_smul
        (inv_ne_zero hU.ne')
  have hcompact : HasCompactSupport (dfiUniformRedundantCutoff U) := by
    exact hcompactReal.comp_left (by simp)
  refine
    { U_pos := hU
      smooth := hsmooth
      compactSupport := hcompact
      support_subset := ?_
      value_zero := ?_
      derivativeBound := fun k ↦ ?_ }
  · intro x hx
    have hbne : dfiUnitRedundantBump (U⁻¹ * x) ≠ 0 := by
      intro hz
      apply hx
      simp [dfiUniformRedundantCutoff, dfiUnitRedundantCutoff, hz]
    have hball : U⁻¹ * x ∈ Metric.ball (0 : ℝ) 1 := by
      rw [← show dfiUnitRedundantBump.rOut = (1 : ℝ) by rfl,
        ← dfiUnitRedundantBump.support_eq]
      exact hbne
    have habs : |U⁻¹ * x| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have hrewrite : |U⁻¹ * x| = |x| / U := by
      rw [abs_mul, abs_inv, abs_of_pos hU]
      field_simp [hU.ne']
    rw [hrewrite] at habs
    exact (abs_lt.mp ((div_lt_one hU).mp habs))
  · have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (1 / 2) := by
      simp [Metric.mem_closedBall]
    simp [dfiUniformRedundantCutoff, dfiUnitRedundantCutoff,
      dfiUnitRedundantBump.one_of_mem_closedBall hzero]
  · obtain ⟨B, hB⟩ :=
      (hunitSmooth.continuous_iteratedDeriv k
        (show (k : ℕ∞ω) ≤ ∞ from mod_cast le_top)).bounded_above_of_compact_support
        (hasCompactSupport_iteratedDeriv dfiUnitRedundantCutoff
          (dfiUnitRedundantBump.hasCompactSupport.comp_left (by simp)) k)
    let C : ℝ := max B 0 + 1
    have hC : 0 < C := by
      dsimp [C]
      linarith [le_max_right B 0]
    refine ⟨C, hC, ?_⟩
    intro x
    have hkSmooth : ContDiff ℝ k dfiUnitRedundantCutoff :=
      hunitSmooth.of_le (by exact_mod_cast le_top)
    have hscale := congrFun
      (iteratedDeriv_comp_const_smul hkSmooth U⁻¹) x
    rw [show dfiUniformRedundantCutoff U =
      fun x ↦ dfiUnitRedundantCutoff (U⁻¹ * x) by rfl,
      hscale, norm_smul, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hU]
    calc
      U⁻¹ ^ k * ‖iteratedDeriv k dfiUnitRedundantCutoff (U⁻¹ * x)‖ ≤
          U⁻¹ ^ k * C := by
        apply mul_le_mul_of_nonneg_left
        · exact (hB _).trans (by dsimp [C]; exact le_max_left B 0 |>.trans (by linarith))
        · positivity
      _ = C * U⁻¹ ^ k := by ring

/-- A single derivative profile works for the rescaled redundant cutoff at
every positive physical scale. -/
theorem exists_dfiUniformRedundantCutoff_profile :
    ∃ D : ℕ → ℝ, ∀ (U : ℝ) (hU : 0 < U),
      DFIRedundantCutoffProfile (dfiUniformRedundantCutoff_spec U hU) D := by
  have hunitSmooth : ContDiff ℝ ∞ dfiUnitRedundantCutoff := by
    exact Complex.ofRealCLM.contDiff.comp dfiUnitRedundantBump.contDiff
  have hunitCompact : HasCompactSupport dfiUnitRedundantCutoff :=
    dfiUnitRedundantBump.hasCompactSupport.comp_left (by simp)
  choose B hB using fun k ↦
    (hunitSmooth.continuous_iteratedDeriv k
      (show (k : ℕ∞ω) ≤ ∞ from mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv dfiUnitRedundantCutoff hunitCompact k)
  let D : ℕ → ℝ := fun k ↦ max (B k) 0 + 1
  have hD : ∀ k, 0 < D k := by
    intro k
    dsimp [D]
    linarith [le_max_right (B k) 0]
  refine ⟨D, ?_⟩
  intro U hU
  refine ⟨hD, ?_⟩
  intro k x
  have hkSmooth : ContDiff ℝ k dfiUnitRedundantCutoff :=
    hunitSmooth.of_le (by exact_mod_cast le_top)
  have hscale := congrFun
    (iteratedDeriv_comp_const_smul hkSmooth U⁻¹) x
  rw [show dfiUniformRedundantCutoff U =
      fun x ↦ dfiUnitRedundantCutoff (U⁻¹ * x) by rfl,
    hscale, norm_smul, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hU]
  calc
    U⁻¹ ^ k * ‖iteratedDeriv k dfiUnitRedundantCutoff (U⁻¹ * x)‖ ≤
        U⁻¹ ^ k * D k := by
      apply mul_le_mul_of_nonneg_left
      · exact (hB k _).trans (by
          dsimp [D]
          exact (le_max_left (B k) 0).trans (by linarith))
      · positivity
    _ = D k * U⁻¹ ^ k := by ring

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

/-! ## A genuinely scale-uniform equation-(9) family -/

/-- A fixed bump supported in `(1,2)` and equal to one on
`[5/4,7/4]`. -/
noncomputable def dfiUnitDeltaBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The even unit-scale annular profile. -/
noncomputable def dfiUnitDeltaProfile (u : ℝ) : ℝ :=
  dfiUnitDeltaBump u + dfiUnitDeltaBump (-u)

theorem dfiUnitDeltaProfile_smooth : ContDiff ℝ ∞ dfiUnitDeltaProfile := by
  exact dfiUnitDeltaBump.contDiff.add
    (dfiUnitDeltaBump.contDiff.comp contDiff_neg)

theorem dfiUnitDeltaProfile_even (u : ℝ) :
    dfiUnitDeltaProfile (-u) = dfiUnitDeltaProfile u := by
  simp only [dfiUnitDeltaProfile, neg_neg]
  ring

theorem dfiUnitDeltaProfile_nonneg (u : ℝ) :
    0 ≤ dfiUnitDeltaProfile u := by
  exact add_nonneg
    (show 0 ≤ dfiUnitDeltaBump u from dfiUnitDeltaBump.nonneg)
    (show 0 ≤ dfiUnitDeltaBump (-u) from dfiUnitDeltaBump.nonneg)

theorem dfiUnitDeltaProfile_support_annulus :
    Function.support dfiUnitDeltaProfile ⊆
      {u : ℝ | 1 ≤ |u| ∧ |u| ≤ 2} := by
  intro u hu
  by_cases hu0 : 0 ≤ u
  · have hpos : dfiUnitDeltaBump u ≠ 0 := by
      intro hz
      have hnegzero : dfiUnitDeltaBump (-u) = 0 := by
        apply dfiUnitDeltaBump.zero_of_le_dist
        change (1 / 2 : ℝ) ≤ dist (-u) (3 / 2)
        rw [Real.dist_eq, abs_of_nonpos (by linarith : -u - 3 / 2 ≤ 0)]
        linarith
      exact hu (by simp [dfiUnitDeltaProfile, hz, hnegzero])
    have hball : u ∈ Metric.ball (3 / 2 : ℝ) (1 / 2) := by
      rw [← show dfiUnitDeltaBump.rOut = (1 / 2 : ℝ) by rfl,
        ← dfiUnitDeltaBump.support_eq]
      exact hpos
    have hdist : |u - 3 / 2| < 1 / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have hdist' := (abs_lt.mp hdist)
    change 1 ≤ |u| ∧ |u| ≤ 2
    rw [abs_of_nonneg hu0]
    constructor <;> linarith [hdist'.1, hdist'.2]
  · have huneg : u < 0 := lt_of_not_ge hu0
    have hneg : dfiUnitDeltaBump (-u) ≠ 0 := by
      intro hz
      have hposzero : dfiUnitDeltaBump u = 0 := by
        apply dfiUnitDeltaBump.zero_of_le_dist
        change (1 / 2 : ℝ) ≤ dist u (3 / 2)
        rw [Real.dist_eq, abs_of_nonpos (by linarith : u - 3 / 2 ≤ 0)]
        linarith
      exact hu (by simp [dfiUnitDeltaProfile, hz, hposzero])
    have hball : -u ∈ Metric.ball (3 / 2 : ℝ) (1 / 2) := by
      rw [← show dfiUnitDeltaBump.rOut = (1 / 2 : ℝ) by rfl,
        ← dfiUnitDeltaBump.support_eq]
      exact hneg
    have hdist : |-u - 3 / 2| < 1 / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    have hdist' := (abs_lt.mp hdist)
    change 1 ≤ |u| ∧ |u| ≤ 2
    rw [abs_of_neg huneg]
    constructor <;> linarith [hdist'.1, hdist'.2]

theorem dfiUnitDeltaProfile_eq_one_of_mem_plateau
    {u : ℝ} (hu₁ : 5 / 4 ≤ u) (hu₂ : u ≤ 7 / 4) :
    dfiUnitDeltaProfile u = 1 := by
  have hclosed : u ∈ Metric.closedBall (3 / 2 : ℝ) (1 / 4) := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith
  have hnegzero : dfiUnitDeltaBump (-u) = 0 := by
    apply dfiUnitDeltaBump.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist (-u) (3 / 2)
    rw [Real.dist_eq, abs_of_nonpos (by linarith : -u - 3 / 2 ≤ 0)]
    linarith
  rw [dfiUnitDeltaProfile, dfiUnitDeltaBump.one_of_mem_closedBall hclosed,
    hnegzero, add_zero]

/-- The unnormalized equation-(9) profile at physical scale `Q`. -/
noncomputable def dfiUniformDeltaRaw (Q u : ℝ) : ℝ :=
  dfiUnitDeltaProfile (Q⁻¹ * u)

theorem dfiUniformDeltaRaw_smooth {Q : ℝ} :
    ContDiff ℝ ∞ (dfiUniformDeltaRaw Q) := by
  change ContDiff ℝ ∞ (fun u ↦ dfiUnitDeltaProfile (Q⁻¹ * u))
  exact dfiUnitDeltaProfile_smooth.comp (contDiff_const.mul contDiff_id)

theorem dfiUniformDeltaRaw_even (Q u : ℝ) :
    dfiUniformDeltaRaw Q (-u) = dfiUniformDeltaRaw Q u := by
  change dfiUnitDeltaProfile (Q⁻¹ * -u) = dfiUnitDeltaProfile (Q⁻¹ * u)
  rw [show Q⁻¹ * -u = -(Q⁻¹ * u) by ring,
    dfiUnitDeltaProfile_even]

theorem dfiUniformDeltaRaw_nonneg (Q u : ℝ) :
    0 ≤ dfiUniformDeltaRaw Q u := dfiUnitDeltaProfile_nonneg _

theorem dfiUniformDeltaRaw_support_annulus {Q u : ℝ} (hQ : 0 < Q)
    (hu : dfiUniformDeltaRaw Q u ≠ 0) :
    Q ≤ |u| ∧ |u| ≤ 2 * Q := by
  have hs := dfiUnitDeltaProfile_support_annulus hu
  have habs : |Q⁻¹ * u| = |u| / Q := by
    rw [abs_mul, abs_inv, abs_of_pos hQ]
    field_simp [hQ.ne']
  change 1 ≤ |Q⁻¹ * u| ∧ |Q⁻¹ * u| ≤ 2 at hs
  rw [habs] at hs
  constructor
  · exact (one_le_div hQ).mp hs.1
  · exact (div_le_iff₀ hQ).mp hs.2

/-- A finite expression for the positive-integer normalization factor. -/
noncomputable def dfiUniformDeltaNormalizer (Q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range ⌈2 * Q⌉₊,
    dfiUniformDeltaRaw Q (r + 1 : ℕ)

theorem dfiUniformDeltaRaw_eq_zero_nat_of_ceiling_lt
    {Q : ℝ} (hQ : 0 < Q) {r : ℕ} (hr : ⌈2 * Q⌉₊ < r) :
    dfiUniformDeltaRaw Q r = 0 := by
  by_contra hne
  have hs := (dfiUniformDeltaRaw_support_annulus hQ hne).2
  have hceil : 2 * Q ≤ (⌈2 * Q⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : (⌈2 * Q⌉₊ : ℝ) < r := by exact_mod_cast hr
  rw [abs_of_nonneg (Nat.cast_nonneg r)] at hs
  linarith

theorem dfiUniformDeltaRaw_tsum_eq_normalizer {Q : ℝ} (hQ : 0 < Q) :
    ∑' r : ℕ, dfiUniformDeltaRaw Q (r + 1 : ℕ) =
      dfiUniformDeltaNormalizer Q := by
  rw [tsum_eq_sum (s := Finset.range ⌈2 * Q⌉₊)]
  · rfl
  · intro r hr
    apply dfiUniformDeltaRaw_eq_zero_nat_of_ceiling_lt hQ
    simpa using hr

theorem dfiUniformDeltaRaw_plateau_nat {Q : ℝ} (hQ : 0 < Q)
    {r : ℕ} (hr₁ : 5 * Q / 4 ≤ r) (hr₂ : (r : ℝ) ≤ 7 * Q / 4) :
    dfiUniformDeltaRaw Q r = 1 := by
  unfold dfiUniformDeltaRaw
  apply dfiUnitDeltaProfile_eq_one_of_mem_plateau
  · rw [inv_mul_eq_div]
    apply (le_div_iff₀ hQ).2
    convert hr₁ using 1
    ring
  · rw [inv_mul_eq_div]
    apply (div_le_iff₀ hQ).2
    convert hr₂ using 1
    ring

/-- The positive-integer normalization mass is comparable from below to
the physical scale.  This is the quantitative fact missing from the
single-sample cutoff. -/
theorem dfiUniformDeltaNormalizer_lower {Q : ℝ} (hQ : 8 ≤ Q) :
    Q / 8 ≤ dfiUniformDeltaNormalizer Q := by
  let L : ℕ := ⌈5 * Q / 4⌉₊
  let N : ℕ := ⌊Q / 4⌋₊
  let R : ℕ := ⌈2 * Q⌉₊
  let S : Finset ℕ := Finset.Ico (L - 1) (L - 1 + N)
  have hQpos : 0 < Q := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.ceil_pos.mpr (by positivity)
  have hLlower : 5 * Q / 4 ≤ (L : ℝ) := by
    dsimp [L]
    exact Nat.le_ceil _
  have hLupper : (L : ℝ) < 5 * Q / 4 + 1 := by
    dsimp [L]
    exact Nat.ceil_lt_add_one (by positivity)
  have hNupper : (N : ℝ) ≤ Q / 4 := by
    dsimp [N]
    exact Nat.floor_le (by positivity)
  have hNlower : Q / 8 ≤ (N : ℝ) := by
    have hfloor : Q / 4 < (N : ℝ) + 1 := by
      simpa only [N] using Nat.lt_floor_add_one (Q / 4)
    linarith
  have hLNupper : ((L + N : ℕ) : ℝ) ≤ 7 * Q / 4 := by
    push_cast
    linarith
  have hLNR : L + N ≤ R := by
    have hRlower : 2 * Q ≤ (R : ℝ) := by
      dsimp [R]
      exact Nat.le_ceil _
    exact_mod_cast (show ((L + N : ℕ) : ℝ) ≤ (R : ℝ) by linarith)
  have hSsub : S ⊆ Finset.range R := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    apply Finset.mem_range.mpr
    omega
  have hsample : ∀ i ∈ S, dfiUniformDeltaRaw Q (i + 1 : ℕ) = 1 := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hmLower : L ≤ i + 1 := by omega
    have hmUpperNat : i + 1 ≤ L + N := by omega
    have hmLowerR : 5 * Q / 4 ≤ ((i + 1 : ℕ) : ℝ) := by
      exact hLlower.trans (by exact_mod_cast hmLower)
    have hmUpperR : (((i + 1 : ℕ) : ℝ)) ≤ 7 * Q / 4 := by
      exact (by exact_mod_cast hmUpperNat : ((i + 1 : ℕ) : ℝ) ≤ (L + N : ℕ)) |>.trans
        hLNupper
    exact dfiUniformDeltaRaw_plateau_nat hQpos hmLowerR hmUpperR
  have hcard : S.card = N := by
    dsimp [S]
    rw [Nat.card_Ico]
    omega
  have hsumS : (∑ i ∈ S, dfiUniformDeltaRaw Q (i + 1 : ℕ)) = (N : ℝ) := by
    calc
      _ = ∑ _i ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsample i hi
      _ = (S.card : ℝ) := by simp
      _ = (N : ℝ) := by rw [hcard]
  calc
    Q / 8 ≤ (N : ℝ) := hNlower
    _ = ∑ i ∈ S, dfiUniformDeltaRaw Q (i + 1 : ℕ) := hsumS.symm
    _ ≤ dfiUniformDeltaNormalizer Q := by
      unfold dfiUniformDeltaNormalizer
      exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun i _hi _hnot ↦ dfiUniformDeltaRaw_nonneg Q (i + 1 : ℕ))

theorem dfiUniformDeltaNormalizer_pos {Q : ℝ} (hQ : 8 ≤ Q) :
    0 < dfiUniformDeltaNormalizer Q := by
  have := dfiUniformDeltaNormalizer_lower hQ
  have hQpos : 0 < Q := by linarith
  linarith

/-- The normalized scale-uniform equation-(9) function. -/
noncomputable def dfiUniformDeltaWeightFun (Q u : ℝ) : ℝ :=
  (dfiUniformDeltaNormalizer Q)⁻¹ * dfiUniformDeltaRaw Q u

theorem dfiUniformDeltaWeightFun_smooth {Q : ℝ} :
    ContDiff ℝ ∞ (dfiUniformDeltaWeightFun Q) := by
  exact contDiff_const.mul dfiUniformDeltaRaw_smooth

theorem dfiUniformDeltaWeightFun_even (Q u : ℝ) :
    dfiUniformDeltaWeightFun Q (-u) = dfiUniformDeltaWeightFun Q u := by
  simp only [dfiUniformDeltaWeightFun, dfiUniformDeltaRaw_even]

theorem dfiUniformDeltaWeightFun_support_annulus {Q : ℝ} (hQ : 8 ≤ Q) :
    Function.support (dfiUniformDeltaWeightFun Q) ⊆
      {u : ℝ | Q ≤ |u| ∧ |u| ≤ 2 * Q} := by
  intro u hu
  apply dfiUniformDeltaRaw_support_annulus (by linarith)
  intro hz
  exact hu (by simp [dfiUniformDeltaWeightFun, hz])

theorem dfiUniformDeltaWeightFun_normalized {Q : ℝ} (hQ : 8 ≤ Q) :
    ∑' r : ℕ, dfiUniformDeltaWeightFun Q (r + 1 : ℕ) = 1 := by
  have hQpos : 0 < Q := by linarith
  have hnormPos := dfiUniformDeltaNormalizer_pos hQ
  rw [tsum_eq_sum (s := Finset.range ⌈2 * Q⌉₊)]
  · unfold dfiUniformDeltaWeightFun
    rw [← Finset.mul_sum]
    change (dfiUniformDeltaNormalizer Q)⁻¹ *
      dfiUniformDeltaNormalizer Q = 1
    exact inv_mul_cancel₀ hnormPos.ne'
  · intro r hr
    unfold dfiUniformDeltaWeightFun
    rw [dfiUniformDeltaRaw_eq_zero_nat_of_ceiling_lt hQpos (by simpa using hr),
      mul_zero]

/-- A concrete equation-(9) weight whose whole family has uniform
derivative constants. -/
noncomputable def dfiUniformDeltaWeight (Q : ℝ) (hQ : 8 ≤ Q) :
    DFIDeltaWeight Q where
  toFun := dfiUniformDeltaWeightFun Q
  one_le_Q := by linarith
  smooth := dfiUniformDeltaWeightFun_smooth
  even := dfiUniformDeltaWeightFun_even Q
  support_annulus := dfiUniformDeltaWeightFun_support_annulus hQ
  normalized := dfiUniformDeltaWeightFun_normalized hQ
  derivativeBound := fun k ↦
    exists_delta_iteratedDeriv_bound
      dfiUniformDeltaWeightFun_smooth
      (by
        have hrawCompact : HasCompactSupport (dfiUniformDeltaRaw Q) := by
          have hunitCompact : HasCompactSupport dfiUnitDeltaProfile := by
            have hp : HasCompactSupport (dfiUnitDeltaBump : ℝ → ℝ) :=
              dfiUnitDeltaBump.hasCompactSupport
            have hn : HasCompactSupport (fun x : ℝ ↦ dfiUnitDeltaBump (-x)) := by
              convert hp.comp_smul (c := (-1 : ℝ)) (by norm_num) using 1
              funext x
              simp only [neg_one_smul]
            simpa only [dfiUnitDeltaProfile] using hp.add hn
          simpa only [dfiUniformDeltaRaw] using
            hunitCompact.comp_smul (inv_ne_zero (by linarith : Q ≠ 0))
        have hmul := hrawCompact.mul_left
          (f := fun _ : ℝ ↦ (dfiUniformDeltaNormalizer Q)⁻¹)
        simpa only [dfiUniformDeltaWeightFun, Pi.mul_apply] using hmul)
      (by linarith) k

theorem iteratedDeriv_dfiUniformDeltaRaw (Q : ℝ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (dfiUniformDeltaRaw Q) u =
      Q⁻¹ ^ j * iteratedDeriv j dfiUnitDeltaProfile (Q⁻¹ * u) := by
  have hs := congrFun
    (iteratedDeriv_comp_const_smul
      (dfiUnitDeltaProfile_smooth.of_le
        (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)) Q⁻¹) u
  simpa only [dfiUniformDeltaRaw, smul_eq_mul] using hs

theorem iteratedDeriv_dfiUniformDeltaWeightFun
    {Q : ℝ} (j : ℕ) (u : ℝ) :
    iteratedDeriv j (dfiUniformDeltaWeightFun Q) u =
      (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ ^ j *
        iteratedDeriv j dfiUnitDeltaProfile (Q⁻¹ * u) := by
  have hraw : ContDiffAt ℝ j (dfiUniformDeltaRaw Q) u :=
    dfiUniformDeltaRaw_smooth.contDiffAt.of_le
      (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)
  rw [show dfiUniformDeltaWeightFun Q = fun x ↦
      (dfiUniformDeltaNormalizer Q)⁻¹ * dfiUniformDeltaRaw Q x by rfl,
    iteratedDeriv_const_mul (dfiUniformDeltaNormalizer Q)⁻¹ hraw,
    iteratedDeriv_dfiUniformDeltaRaw]
  ring

/-- One equation-(9) derivative profile works simultaneously for every
`Q ≥ 8`. -/
theorem exists_dfiUniformDeltaWeight_profile :
    ∃ D : ℕ → ℝ, ∀ (Q : ℝ) (hQ : 8 ≤ Q),
      DFIDeltaWeightProfile (dfiUniformDeltaWeight Q hQ) D := by
  have hunitCompact : HasCompactSupport dfiUnitDeltaProfile := by
    have hp : HasCompactSupport (dfiUnitDeltaBump : ℝ → ℝ) :=
      dfiUnitDeltaBump.hasCompactSupport
    have hn : HasCompactSupport (fun x : ℝ ↦ dfiUnitDeltaBump (-x)) := by
      convert hp.comp_smul (c := (-1 : ℝ)) (by norm_num) using 1
      funext x
      simp only [neg_one_smul]
    simpa only [dfiUnitDeltaProfile] using hp.add hn
  choose B hB using fun j ↦
    (dfiUnitDeltaProfile_smooth.continuous_iteratedDeriv j
      (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv dfiUnitDeltaProfile hunitCompact j)
  let D : ℕ → ℝ := fun j ↦ 8 * (max (B j) 0 + 1)
  have hD : ∀ j, 0 < D j := by
    intro j
    dsimp [D]
    have := le_max_right (B j) 0
    positivity
  refine ⟨D, ?_⟩
  intro Q hQ
  refine ⟨hD, ?_⟩
  intro j u
  have hQpos : 0 < Q := by linarith
  have hNormPos := dfiUniformDeltaNormalizer_pos hQ
  have hNormLower := dfiUniformDeltaNormalizer_lower hQ
  have hNormInv : (dfiUniformDeltaNormalizer Q)⁻¹ ≤ 8 * Q⁻¹ := by
    calc
      (dfiUniformDeltaNormalizer Q)⁻¹ ≤ (Q / 8)⁻¹ :=
        (inv_le_inv₀ hNormPos (by positivity : 0 < Q / 8)).2 hNormLower
      _ = 8 * Q⁻¹ := by field_simp [hQpos.ne']
  have hB' : ‖iteratedDeriv j dfiUnitDeltaProfile (Q⁻¹ * u)‖ ≤
      max (B j) 0 + 1 :=
    (hB j _).trans ((le_max_left (B j) 0).trans (by linarith))
  change ‖iteratedDeriv j (dfiUniformDeltaWeightFun Q) u‖ ≤
    D j * (Q ^ (j + 1))⁻¹
  rw [iteratedDeriv_dfiUniformDeltaWeightFun]
  have hQinv : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQpos.le
  have hNormInvNonneg : 0 ≤ (dfiUniformDeltaNormalizer Q)⁻¹ :=
    inv_nonneg.mpr hNormPos.le
  calc
    ‖(dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ ^ j *
        iteratedDeriv j dfiUnitDeltaProfile (Q⁻¹ * u)‖ =
      (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ ^ j *
        ‖iteratedDeriv j dfiUnitDeltaProfile (Q⁻¹ * u)‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hNormInvNonneg, abs_of_nonneg (pow_nonneg hQinv j)]
    _ ≤ (8 * Q⁻¹) * Q⁻¹ ^ j * (max (B j) 0 + 1) := by
      gcongr
    _ = D j * (Q ^ (j + 1))⁻¹ := by
      dsimp [D]
      rw [pow_succ, mul_inv_rev, inv_pow]
      ring

/-! ## Uniform quotient profile for the canonical equation-(9) family -/

/-- The fixed unit-scale removable quotient underlying every scaled
`dfiUniformDeltaWeight`. -/
noncomputable def dfiUnitDeltaQuotient (u : ℝ) : ℝ :=
  dfiUnitDeltaProfile u / u

theorem dfiUnitDeltaQuotient_eventuallyEq_zero_at_zero :
    dfiUnitDeltaQuotient =ᶠ[𝓝 (0 : ℝ)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)]
    with u hu
  have habs : |u| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hu
  have hprofile : dfiUnitDeltaProfile u = 0 := by
    by_contra hne
    have hs := dfiUnitDeltaProfile_support_annulus hne
    change 1 ≤ |u| ∧ |u| ≤ 2 at hs
    exact (not_lt_of_ge hs.1) habs
  simp [dfiUnitDeltaQuotient, hprofile]

theorem dfiUnitDeltaQuotient_smooth :
    ContDiff ℝ ∞ dfiUnitDeltaQuotient := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    exact (contDiffAt_const (𝕜 := ℝ) (x := (0 : ℝ)) (c := (0 : ℝ))
      (n := (∞ : WithTop ℕ∞))).congr_of_eventuallyEq
        dfiUnitDeltaQuotient_eventuallyEq_zero_at_zero
  · exact dfiUnitDeltaProfile_smooth.contDiffAt.div contDiffAt_id hu

theorem dfiUnitDeltaQuotient_hasCompactSupport :
    HasCompactSupport dfiUnitDeltaQuotient := by
  have hunitCompact : HasCompactSupport dfiUnitDeltaProfile := by
    have hp : HasCompactSupport (dfiUnitDeltaBump : ℝ → ℝ) :=
      dfiUnitDeltaBump.hasCompactSupport
    have hn : HasCompactSupport (fun x : ℝ ↦ dfiUnitDeltaBump (-x)) := by
      convert hp.comp_smul (c := (-1 : ℝ)) (by norm_num) using 1
      funext x
      simp only [neg_one_smul]
    simpa only [dfiUnitDeltaProfile] using hp.add hn
  apply HasCompactSupport.mono hunitCompact
  intro u hu
  by_contra hprofile
  have hz : dfiUnitDeltaProfile u = 0 := by
    simpa [Function.mem_support] using hprofile
  exact hu (by simp [dfiUnitDeltaQuotient, hz])

/-- Exact scaling identity for the quotient in DFI equation (12). -/
theorem dfiWeightQuotient_dfiUniformDeltaWeight
    {Q : ℝ} (hQ : 8 ≤ Q) (u : ℝ) :
    dfiWeightQuotient (dfiUniformDeltaWeight Q hQ) u =
      (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ *
        dfiUnitDeltaQuotient (Q⁻¹ * u) := by
  have hQ0 : Q ≠ 0 := by linarith
  by_cases hu : u = 0
  · subst u
    simp [dfiWeightQuotient, dfiUnitDeltaQuotient]
  · unfold dfiWeightQuotient dfiUnitDeltaQuotient
    change ((dfiUniformDeltaNormalizer Q)⁻¹ *
        dfiUnitDeltaProfile (Q⁻¹ * u)) / u = _
    field_simp [hQ0, hu]

theorem iteratedDeriv_dfiWeightQuotient_dfiUniformDeltaWeight
    {Q : ℝ} (hQ : 8 ≤ Q) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (dfiWeightQuotient (dfiUniformDeltaWeight Q hQ)) u =
      (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ * Q⁻¹ ^ j *
        iteratedDeriv j dfiUnitDeltaQuotient (Q⁻¹ * u) := by
  let A : ℝ := (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹
  have hfun : dfiWeightQuotient (dfiUniformDeltaWeight Q hQ) =
      fun x : ℝ ↦ A * dfiUnitDeltaQuotient (Q⁻¹ * x) := by
    funext x
    simpa only [A] using dfiWeightQuotient_dfiUniformDeltaWeight hQ x
  have hcomp : ContDiffAt ℝ j
      (fun x : ℝ ↦ dfiUnitDeltaQuotient (Q⁻¹ * x)) u :=
    (dfiUnitDeltaQuotient_smooth.comp
      (contDiff_const.mul contDiff_id)).contDiffAt.of_le
        (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)
  rw [hfun, iteratedDeriv_const_mul A hcomp]
  have hchain := congrFun
    (iteratedDeriv_comp_const_mul
      (dfiUnitDeltaQuotient_smooth.of_le
        (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)) Q⁻¹) u
  rw [hchain]
  dsimp [A]
  ring

/-- One quotient-derivative profile works simultaneously for the canonical
equation-(9) weights at every `Q ≥ 8`. -/
theorem exists_dfiUniformDeltaWeight_quotient_profile :
    ∃ E : ℕ → ℝ, ∀ (Q : ℝ) (hQ : 8 ≤ Q),
      DFIWeightQuotientProfile (dfiUniformDeltaWeight Q hQ) E := by
  choose B hB using fun j ↦
    (dfiUnitDeltaQuotient_smooth.continuous_iteratedDeriv j
      (show (j : ℕ∞ω) ≤ ∞ from mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv dfiUnitDeltaQuotient
        dfiUnitDeltaQuotient_hasCompactSupport j)
  let E : ℕ → ℝ := fun j ↦ 8 * (max (B j) 0 + 1)
  have hE : ∀ j, 0 < E j := by
    intro j
    dsimp [E]
    have := le_max_right (B j) 0
    positivity
  refine ⟨E, ?_⟩
  intro Q hQ
  refine ⟨hE, ?_⟩
  intro j u
  have hQpos : 0 < Q := by linarith
  have hNormPos := dfiUniformDeltaNormalizer_pos hQ
  have hNormLower := dfiUniformDeltaNormalizer_lower hQ
  have hNormInv : (dfiUniformDeltaNormalizer Q)⁻¹ ≤ 8 * Q⁻¹ := by
    calc
      (dfiUniformDeltaNormalizer Q)⁻¹ ≤ (Q / 8)⁻¹ :=
        (inv_le_inv₀ hNormPos (by positivity : 0 < Q / 8)).2 hNormLower
      _ = 8 * Q⁻¹ := by field_simp [hQpos.ne']
  have hB' : ‖iteratedDeriv j dfiUnitDeltaQuotient (Q⁻¹ * u)‖ ≤
      max (B j) 0 + 1 :=
    (hB j _).trans ((le_max_left (B j) 0).trans (by linarith))
  rw [iteratedDeriv_dfiWeightQuotient_dfiUniformDeltaWeight hQ]
  have hQinv : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQpos.le
  have hNormInvNonneg : 0 ≤ (dfiUniformDeltaNormalizer Q)⁻¹ :=
    inv_nonneg.mpr hNormPos.le
  calc
    ‖(dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ * Q⁻¹ ^ j *
        iteratedDeriv j dfiUnitDeltaQuotient (Q⁻¹ * u)‖ =
      (dfiUniformDeltaNormalizer Q)⁻¹ * Q⁻¹ * Q⁻¹ ^ j *
        ‖iteratedDeriv j dfiUnitDeltaQuotient (Q⁻¹ * u)‖ := by
          rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs,
            Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hNormInvNonneg, abs_of_nonneg hQinv,
            abs_of_nonneg (pow_nonneg hQinv j)]
    _ ≤ (8 * Q⁻¹) * Q⁻¹ * Q⁻¹ ^ j * (max (B j) 0 + 1) := by
      gcongr
    _ = E j * (Q ^ (j + 2))⁻¹ := by
      dsimp [E]
      rw [show Q ^ (j + 2) = Q ^ j * Q * Q by
        rw [show j + 2 = j + 1 + 1 by omega, pow_succ, pow_succ]]
      rw [inv_pow]
      field_simp [hQpos.ne']

end RiemannZeta.GuthMaynard
