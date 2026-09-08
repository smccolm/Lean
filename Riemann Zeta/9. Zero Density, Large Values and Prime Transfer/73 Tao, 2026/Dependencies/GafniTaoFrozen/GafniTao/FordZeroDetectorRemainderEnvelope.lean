import GafniTao.FordZeroDetectorSelectedAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform envelope for Ford's selected horizontal remainders

The differentiated cotangent expression simplifies exactly to a logarithmic
factor times exponential decay.  This file records that identity and a
uniform comparison valid while the nearby good shift varies in a fixed
compact positive interval.
-/

open Complex Filter Set Topology
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordDetectorHorizontalRemainderMajorant_eq
    {eta M y : ℝ} (heta : 0 < eta) :
    fordDetectorHorizontalRemainderMajorant eta M y =
      8 * Real.pi * M *
        Real.exp (-Real.pi * |y| / eta) := by
  unfold fordDetectorHorizontalRemainderMajorant
  field_simp [heta.ne', Real.pi_ne_zero]
  ring

/-- A single exponential envelope controls every good shift
`eta' ∈ [eta,etaMax]`. -/
theorem fordDetectorHorizontalRemainderMajorant_le_uniform
    {eta' etaMax M y D : ℝ}
    (heta' : 0 < eta') (hetaMax : eta' ≤ etaMax)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hy : D ≤ |y|) :
    fordDetectorHorizontalRemainderMajorant eta' M y ≤
      8 * Real.pi * M *
        Real.exp (-Real.pi * D / etaMax) := by
  have hetaMaxPos : 0 < etaMax := heta'.trans_le hetaMax
  have hcross : D * eta' ≤ |y| * etaMax := by
    calc
      D * eta' ≤ D * etaMax :=
        mul_le_mul_of_nonneg_left hetaMax hD
      _ ≤ |y| * etaMax :=
        mul_le_mul_of_nonneg_right hy hetaMaxPos.le
  have hquot : D / etaMax ≤ |y| / eta' := by
    exact (div_le_div_iff₀ hetaMaxPos heta').2 (by
      simpa [mul_comm] using hcross)
  have hexp :
      Real.exp (-Real.pi * |y| / eta') ≤
        Real.exp (-Real.pi * D / etaMax) := by
    apply Real.exp_le_exp.mpr
    calc
      -Real.pi * |y| / eta' =
          -(Real.pi * (|y| / eta')) := by ring
      _ ≤ -(Real.pi * (D / etaMax)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hquot Real.pi_pos.le)
      _ = -Real.pi * D / etaMax := by ring
  rw [fordDetectorHorizontalRemainderMajorant_eq heta']
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hM)

theorem log_sq_le_sq {T : ℝ} (hT : 1 ≤ T) :
    Real.log T ^ 2 ≤ T ^ 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogT : Real.log T ≤ T := by
    have := Real.log_le_sub_one_of_pos hTpos
    linarith
  nlinarith [sq_nonneg (T - Real.log T)]

/-- The elementary envelope used for the final squeeze: logarithmic growth is
bounded by a quadratic, while the exponential rate is kept literal. -/
theorem fordDetectorHorizontalRemainderMajorant_le_poly_exp
    {eta' etaMax C t T y : ℝ}
    (heta' : 0 < eta') (hetaMax : eta' ≤ etaMax)
    (hC : 0 ≤ C) (hT : 1 ≤ T) (htT : t ≤ T)
    (hy : T - t ≤ |y|) :
    fordDetectorHorizontalRemainderMajorant eta'
        (C * Real.log T ^ 2) y ≤
      8 * Real.pi * C * T ^ 2 *
        Real.exp (-Real.pi * (T - t) / etaMax) := by
  have hM : 0 ≤ C * Real.log T ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  have hbase := fordDetectorHorizontalRemainderMajorant_le_uniform
    heta' hetaMax hM (sub_nonneg.mpr htT) hy
  calc
    fordDetectorHorizontalRemainderMajorant eta'
        (C * Real.log T ^ 2) y ≤
      8 * Real.pi * (C * Real.log T ^ 2) *
        Real.exp (-Real.pi * (T - t) / etaMax) := hbase
    _ ≤ 8 * Real.pi * C * T ^ 2 *
        Real.exp (-Real.pi * (T - t) / etaMax) := by
      have hexp : 0 ≤ Real.exp (-Real.pi * (T - t) / etaMax) :=
        Real.exp_pos _ |>.le
      have hcoef : 0 ≤ 8 * Real.pi * C := by positivity
      have hsquare := log_sq_le_sq hT
      have hlogCoeff :
          (8 * Real.pi * C) * Real.log T ^ 2 ≤
            (8 * Real.pi * C) * T ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hcoef
      have hmul := mul_le_mul_of_nonneg_right hlogCoeff hexp
      calc
        8 * Real.pi * (C * Real.log T ^ 2) *
            Real.exp (-Real.pi * (T - t) / etaMax) =
          ((8 * Real.pi * C) * Real.log T ^ 2) *
            Real.exp (-Real.pi * (T - t) / etaMax) := by ring
        _ ≤ ((8 * Real.pi * C) * T ^ 2) *
            Real.exp (-Real.pi * (T - t) / etaMax) := hmul
        _ = 8 * Real.pi * C * T ^ 2 *
            Real.exp (-Real.pi * (T - t) / etaMax) := by ring

theorem tendsto_fordDetector_poly_exp_envelope
    {etaMax C t : ℝ} (hetaMax : 0 < etaMax) :
    Tendsto (fun T : ℝ =>
      8 * Real.pi * C * T ^ 2 *
        Real.exp (-Real.pi * (T - t) / etaMax))
      atTop (𝓝 0) := by
  let b : ℝ := Real.pi / etaMax
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hbase :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) b hb
  have hconst : Tendsto
      (fun _x : ℝ => 8 * Real.pi * C * Real.exp (b * t))
      atTop (𝓝 (8 * Real.pi * C * Real.exp (b * t))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hbase
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards with T
  rw [Real.rpow_two]
  have hexp :
      -Real.pi * (T - t) / etaMax = b * t + (-b * T) := by
    dsimp [b]
    field_simp [hetaMax.ne']
    ring
  rw [hexp, Real.exp_add]
  ring

/-- Uniform epsilon form of the horizontal-tail limit.  It applies to any
choice of nearby good shift and physical edge satisfying the literal
majorant, so no noncanonical choice function enters later arguments. -/
theorem eventually_fordDetector_horizontal_remainder_small
    {eta etaMax C t : ℝ} (heta : 0 < eta)
    (hetaMax : eta ≤ etaMax) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T eta' y : ℝ}, T0 ≤ T →
        1 ≤ T → t ≤ T → eta ≤ eta' → eta' ≤ etaMax →
        T - t ≤ |y| →
        ‖fordDetectorHorizontalRemainder eta' t y‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) y →
        ‖fordDetectorHorizontalRemainder eta' t y‖ < ε := by
  have hetaMaxPos : 0 < etaMax := heta.trans_le hetaMax
  intro ε hε
  have htend := tendsto_fordDetector_poly_exp_envelope
    (C := C) (t := t) hetaMaxPos
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨T0, hT0⟩ := htend ε hε
  refine ⟨T0, ?_⟩
  intro T eta' y hT0T hT htT hetaLow hetaHigh hy hrem
  have heta' : 0 < eta' := heta.trans_le hetaLow
  have henv := fordDetectorHorizontalRemainderMajorant_le_poly_exp
    heta' hetaHigh hC hT htT hy
  have hsmall := hT0 T hT0T
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hsmall
  · exact lt_of_le_of_lt (hrem.trans henv) hsmall
  · positivity

end

end GafniTao
