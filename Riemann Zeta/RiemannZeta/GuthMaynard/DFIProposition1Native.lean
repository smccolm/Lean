import RiemannZeta.GuthMaynard.DFIVoronoiDual

/-! The source-form DFI Proposition 1, obtained from the unconditional
Mellin--Barnes continuation and the exact additive-character dual split. -/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- The `u`-independent norm of the two non-Gamma factors on the reflected
line `Re s = 3/2`. -/
noncomputable def dfiArchimedeanScale (q : ℕ) [NeZero q] : ℝ :=
  ‖(q : ℂ) ^ (1 / 2 : ℂ)‖ *
    ‖(2 * Real.pi : ℂ) ^ (-(3 / 2 : ℂ))‖

theorem dfiArchimedeanScale_nonneg (q : ℕ) [NeZero q] :
    0 ≤ dfiArchimedeanScale q := mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_dfiPeriodicArchimedeanFactor_mul_exp (q : ℕ) [NeZero q]
    (u sign : ℝ) :
    ‖dfiPeriodicArchimedeanFactor q ((3 / 2 : ℂ) - (u : ℂ) * I) *
        cexp ((sign : ℂ) * Real.pi * I *
          ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ =
      dfiArchimedeanScale q *
        ‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
          cexp ((sign : ℂ) * Real.pi * I *
            ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
  let r : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
  unfold dfiPeriodicArchimedeanFactor dfiArchimedeanScale
  repeat' rw [norm_mul]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqnorm : ‖(q : ℂ) ^ (r - 1)‖ = ‖(q : ℂ) ^ (1 / 2 : ℂ)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    dsimp [r]
    norm_num
  have hpinorm : ‖(2 * Real.pi : ℂ) ^ (-r)‖ =
      ‖(2 * Real.pi : ℂ) ^ (-(3 / 2 : ℂ))‖ := by
    have hbase : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by norm_num
    rw [hbase]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
        (by positivity : (0 : ℝ) < 2 * Real.pi),
      Complex.norm_cpow_eq_rpow_re_of_pos
        (by positivity : (0 : ℝ) < 2 * Real.pi)]
    dsimp [r]
    norm_num
  change ‖(q : ℂ) ^ (r - 1)‖ * ‖(2 * Real.pi : ℂ) ^ (-r)‖ *
      ‖Gamma r‖ * ‖cexp ((sign : ℂ) * Real.pi * I * r / 2)‖ = _
  rw [hqnorm, hpinorm]
  dsimp [r]
  ring

theorem norm_dfiPeriodicArchimedeanFactor_mul_exp_pos_le
    (q : ℕ) [NeZero q] (u : ℝ) :
    ‖dfiPeriodicArchimedeanFactor q ((3 / 2 : ℂ) - (u : ℂ) * I) *
        cexp (Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * dfiArchimedeanScale q * (1 + |u|) := by
  have hnorm := norm_dfiPeriodicArchimedeanFactor_mul_exp q u 1
  norm_num at hnorm
  rw [norm_mul, hnorm]
  calc
    dfiArchimedeanScale q *
        (‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
          ‖cexp (Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖) =
      dfiArchimedeanScale q *
        ‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
          cexp (Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
            rw [norm_mul]
    _ ≤
      dfiArchimedeanScale q * (4 * (1 + |u|)) := by
        exact mul_le_mul_of_nonneg_left
          (norm_Gamma_mul_voronoiExp_pos_le u)
          (dfiArchimedeanScale_nonneg q)
    _ = 4 * dfiArchimedeanScale q * (1 + |u|) := by ring

theorem norm_dfiPeriodicArchimedeanFactor_mul_exp_neg_le
    (q : ℕ) [NeZero q] (u : ℝ) :
    ‖dfiPeriodicArchimedeanFactor q ((3 / 2 : ℂ) - (u : ℂ) * I) *
        cexp (-Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * dfiArchimedeanScale q * (1 + |u|) := by
  have hnorm := norm_dfiPeriodicArchimedeanFactor_mul_exp q u (-1)
  norm_num at hnorm
  have hnorm' :
      ‖dfiPeriodicArchimedeanFactor q ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
          ‖cexp (-Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ =
        dfiArchimedeanScale q *
          (‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
            ‖cexp (-Real.pi * I *
              ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖) := by
    convert hnorm using 1 <;> ring_nf
  rw [norm_mul, hnorm']
  calc
    dfiArchimedeanScale q *
        (‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
          ‖cexp (-Real.pi * I *
            ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖) =
      dfiArchimedeanScale q *
        ‖Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
          cexp (-Real.pi * I * ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
            rw [norm_mul]
    _ ≤
      dfiArchimedeanScale q * (4 * (1 + |u|)) := by
        exact mul_le_mul_of_nonneg_left
          (norm_Gamma_mul_voronoiExp_neg_le u)
          (dfiArchimedeanScale_nonneg q)
    _ = 4 * dfiArchimedeanScale q * (1 + |u|) := by ring

theorem norm_dfiVoronoiMinusMultiplier_le (q : ℕ) [NeZero q]
    (u : ℝ) :
    ‖dfiVoronoiMinusMultiplier q
        (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2 := by
  let r : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
  have hr : 1 - (-(1 / 2 : ℂ) + (u : ℂ) * I) = r := by
    dsimp [r]
    ring
  have hp := norm_dfiPeriodicArchimedeanFactor_mul_exp_pos_le q u
  have hm := norm_dfiPeriodicArchimedeanFactor_mul_exp_neg_le q u
  unfold dfiVoronoiMinusMultiplier
  rw [hr]
  have hrewrite :
      dfiPeriodicArchimedeanFactor q r ^ 2 *
          (cexp (Real.pi * I * r) + cexp (-Real.pi * I * r)) =
        (dfiPeriodicArchimedeanFactor q r *
            cexp (Real.pi * I * r / 2)) ^ 2 +
          (dfiPeriodicArchimedeanFactor q r *
            cexp (-Real.pi * I * r / 2)) ^ 2 := by
    rw [show cexp (Real.pi * I * r) =
        cexp (Real.pi * I * r / 2) * cexp (Real.pi * I * r / 2) by
          rw [← Complex.exp_add]
          congr 1
          ring]
    rw [show cexp (-Real.pi * I * r) =
        cexp (-Real.pi * I * r / 2) * cexp (-Real.pi * I * r / 2) by
          rw [← Complex.exp_add]
          congr 1
          ring]
    ring
  have hfull :
      (q : ℂ) * dfiPeriodicArchimedeanFactor q r ^ 2 *
          (cexp (Real.pi * I * r) + cexp (-Real.pi * I * r)) =
        (q : ℂ) *
          ((dfiPeriodicArchimedeanFactor q r *
              cexp (Real.pi * I * r / 2)) ^ 2 +
            (dfiPeriodicArchimedeanFactor q r *
              cexp (-Real.pi * I * r / 2)) ^ 2) := by
    calc
      (q : ℂ) * dfiPeriodicArchimedeanFactor q r ^ 2 *
            (cexp (Real.pi * I * r) + cexp (-Real.pi * I * r)) =
          (q : ℂ) * (dfiPeriodicArchimedeanFactor q r ^ 2 *
            (cexp (Real.pi * I * r) + cexp (-Real.pi * I * r))) := by ring
      _ = _ := by rw [hrewrite]
  have hq : (0 : ℝ) ≤ q := by positivity
  rw [hfull, norm_mul, Complex.norm_natCast]
  calc
    q * ‖(dfiPeriodicArchimedeanFactor q r *
              cexp (Real.pi * I * r / 2)) ^ 2 +
            (dfiPeriodicArchimedeanFactor q r *
              cexp (-Real.pi * I * r / 2)) ^ 2‖ ≤
      q *
        (‖dfiPeriodicArchimedeanFactor q r *
              cexp (Real.pi * I * r / 2)‖ ^ 2 +
          ‖dfiPeriodicArchimedeanFactor q r *
              cexp (-Real.pi * I * r / 2)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by
          have hadd := norm_add_le
            ((dfiPeriodicArchimedeanFactor q r *
              cexp (Real.pi * I * r / 2)) ^ 2)
            ((dfiPeriodicArchimedeanFactor q r *
              cexp (-Real.pi * I * r / 2)) ^ 2)
          simp only [norm_pow] at hadd
          exact hadd) hq
    _ ≤
      q * ((4 * dfiArchimedeanScale q * (1 + |u|)) ^ 2 +
        (4 * dfiArchimedeanScale q * (1 + |u|)) ^ 2) := by
          gcongr
    _ = 32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2 := by ring

theorem norm_dfiVoronoiPlusMultiplier_le (q : ℕ) [NeZero q]
    (u : ℝ) :
    ‖dfiVoronoiPlusMultiplier q
        (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2 := by
  let r : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
  have hr : 1 - (-(1 / 2 : ℂ) + (u : ℂ) * I) = r := by
    dsimp [r]
    ring
  have hp := norm_dfiPeriodicArchimedeanFactor_mul_exp_pos_le q u
  have hm := norm_dfiPeriodicArchimedeanFactor_mul_exp_neg_le q u
  unfold dfiVoronoiPlusMultiplier
  rw [hr]
  have hcancel :
      cexp (Real.pi * I * r / 2) * cexp (-Real.pi * I * r / 2) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hrewrite : dfiPeriodicArchimedeanFactor q r ^ 2 =
      (dfiPeriodicArchimedeanFactor q r * cexp (Real.pi * I * r / 2)) *
        (dfiPeriodicArchimedeanFactor q r * cexp (-Real.pi * I * r / 2)) := by
    rw [show (dfiPeriodicArchimedeanFactor q r * cexp (Real.pi * I * r / 2)) *
        (dfiPeriodicArchimedeanFactor q r * cexp (-Real.pi * I * r / 2)) =
      dfiPeriodicArchimedeanFactor q r ^ 2 *
        (cexp (Real.pi * I * r / 2) * cexp (-Real.pi * I * r / 2)) by ring,
      hcancel, mul_one]
  have hfull :
      2 * (q : ℂ) * dfiPeriodicArchimedeanFactor q r ^ 2 =
        2 * (q : ℂ) *
          ((dfiPeriodicArchimedeanFactor q r * cexp (Real.pi * I * r / 2)) *
            (dfiPeriodicArchimedeanFactor q r *
              cexp (-Real.pi * I * r / 2))) := by rw [hrewrite]
  let X := dfiPeriodicArchimedeanFactor q r * cexp (Real.pi * I * r / 2)
  let Y := dfiPeriodicArchimedeanFactor q r * cexp (-Real.pi * I * r / 2)
  have hnorm : ‖(2 : ℂ) * (q : ℂ) * (X * Y)‖ =
      2 * q * (‖X‖ * ‖Y‖) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
    norm_num
  rw [hfull]
  change ‖(2 : ℂ) * (q : ℂ) * (X * Y)‖ ≤ _
  rw [hnorm]
  have hq : (0 : ℝ) ≤ q := by positivity
  have hB : 0 ≤ 4 * dfiArchimedeanScale q * (1 + |u|) :=
    mul_nonneg (mul_nonneg (by norm_num) (dfiArchimedeanScale_nonneg q))
      (by positivity)
  calc
    2 * q *
        (‖X‖ * ‖Y‖) ≤
      2 * q * ((4 * dfiArchimedeanScale q * (1 + |u|)) *
        (4 * dfiArchimedeanScale q * (1 + |u|))) := by
          dsimp [X, Y]
          gcongr
    _ = 32 * q * dfiArchimedeanScale q ^ 2 * (1 + |u|) ^ 2 := by ring

theorem continuous_dfiVoronoiMinusMultiplier_leftLine
    (q : ℕ) [NeZero q] :
    Continuous (fun u : ℝ =>
      dfiVoronoiMinusMultiplier q
        (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  let r : ℝ → ℂ := fun v => 1 - (-(1 / 2 : ℂ) + (v : ℂ) * I)
  have hr : ContinuousAt r u := by
    dsimp [r]
    fun_prop
  have hGamma : ContinuousAt (fun v : ℝ =>
      Gamma (1 - (-(1 / 2 : ℂ) + (v : ℂ) * I))) u := by
    apply (Complex.continuousAt_Gamma (r u) ?_).comp_of_eq hr rfl
    intro m hm
    dsimp [r] at hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hqpow : ContinuousAt (fun v : ℝ => (q : ℂ) ^ (r v - 1)) u :=
    (hr.sub continuousAt_const).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hpipow : ContinuousAt (fun v : ℝ =>
      (2 * Real.pi : ℂ) ^ (-(r v))) u :=
    hr.neg.const_cpow (Or.inl (by
      exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_ne_zero))
  have hArch : ContinuousAt (fun v : ℝ =>
      dfiPeriodicArchimedeanFactor q (r v)) u := by
    unfold dfiPeriodicArchimedeanFactor
    exact (hqpow.mul hpipow).mul hGamma
  have hExpPos : ContinuousAt (fun v : ℝ =>
      cexp (Real.pi * I * r v)) u :=
    Complex.continuous_exp.continuousAt.comp (by fun_prop)
  have hExpNeg : ContinuousAt (fun v : ℝ =>
      cexp (-Real.pi * I * r v)) u :=
    Complex.continuous_exp.continuousAt.comp (by fun_prop)
  unfold dfiVoronoiMinusMultiplier
  exact (continuousAt_const.mul (hArch.pow 2)).mul (hExpPos.add hExpNeg)

theorem continuous_dfiVoronoiPlusMultiplier_leftLine
    (q : ℕ) [NeZero q] :
    Continuous (fun u : ℝ =>
      dfiVoronoiPlusMultiplier q
        (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  let r : ℝ → ℂ := fun v => 1 - (-(1 / 2 : ℂ) + (v : ℂ) * I)
  have hr : ContinuousAt r u := by
    dsimp [r]
    fun_prop
  have hGamma : ContinuousAt (fun v : ℝ =>
      Gamma (1 - (-(1 / 2 : ℂ) + (v : ℂ) * I))) u := by
    apply (Complex.continuousAt_Gamma (r u) ?_).comp_of_eq hr rfl
    intro m hm
    dsimp [r] at hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hqpow : ContinuousAt (fun v : ℝ => (q : ℂ) ^ (r v - 1)) u :=
    (hr.sub continuousAt_const).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hpipow : ContinuousAt (fun v : ℝ =>
      (2 * Real.pi : ℂ) ^ (-(r v))) u :=
    hr.neg.const_cpow (Or.inl (by
      exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_ne_zero))
  have hArch : ContinuousAt (fun v : ℝ =>
      dfiPeriodicArchimedeanFactor q (r v)) u := by
    unfold dfiPeriodicArchimedeanFactor
    exact (hqpow.mul hpipow).mul hGamma
  unfold dfiVoronoiPlusMultiplier
  exact (continuousAt_const.mul continuousAt_const).mul (hArch.pow 2)

theorem DFIVoronoiTestFunction.integrable_minusMultiplier_mul_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] :
    Integrable (fun u : ℝ =>
      dfiVoronoiMinusMultiplier q
          (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  let C : ℝ := 32 * q * dfiArchimedeanScale q ^ 2
  have hWeighted := hg.integrable_sqWeight_norm_mellin (-(1 / 2 : ℝ))
  have hDom : Integrable (fun u : ℝ =>
      C * ((1 + |u|) ^ 2 *
        ‖mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖)) :=
    by
      simpa only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one] using hWeighted.const_mul C
  have hMellinCont : Continuous (fun u : ℝ =>
      mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) :=
    hg.differentiable_mellin.continuous.comp (by fun_prop)
  apply hDom.mono'
    ((continuous_dfiVoronoiMinusMultiplier_leftLine q).mul
      hMellinCont).aestronglyMeasurable
  filter_upwards with u
  change ‖dfiVoronoiMinusMultiplier q
      (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ _
  rw [norm_mul]
  simpa [C, mul_assoc] using mul_le_mul_of_nonneg_right
    (norm_dfiVoronoiMinusMultiplier_le q u)
    (norm_nonneg (mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)))

theorem DFIVoronoiTestFunction.integrable_plusMultiplier_mul_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] :
    Integrable (fun u : ℝ =>
      dfiVoronoiPlusMultiplier q
          (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  let C : ℝ := 32 * q * dfiArchimedeanScale q ^ 2
  have hWeighted := hg.integrable_sqWeight_norm_mellin (-(1 / 2 : ℝ))
  have hDom : Integrable (fun u : ℝ =>
      C * ((1 + |u|) ^ 2 *
        ‖mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖)) :=
    by
      simpa only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one] using hWeighted.const_mul C
  have hMellinCont : Continuous (fun u : ℝ =>
      mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) :=
    hg.differentiable_mellin.continuous.comp (by fun_prop)
  apply hDom.mono'
    ((continuous_dfiVoronoiPlusMultiplier_leftLine q).mul
      hMellinCont).aestronglyMeasurable
  filter_upwards with u
  change ‖dfiVoronoiPlusMultiplier q
      (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ _
  rw [norm_mul]
  simpa [C, mul_assoc] using mul_le_mul_of_nonneg_right
    (norm_dfiVoronoiPlusMultiplier_le q u)
    (norm_nonneg (mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)))

/-- One Dirichlet-series summand on DFI's reflected contour, before the
normalizing vertical integral is taken. -/
noncomputable def dfiVoronoiMellinTerm (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (M : ℂ → ℂ) (g : ℝ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (periodicDivisorCoeff q Φ)
      (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) n *
    (M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
      mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))

theorem integrable_dfiVoronoiMellinTerm
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ) (n : ℕ)
    (hInt : Integrable (fun u : ℝ =>
      M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))) :
    Integrable (dfiVoronoiMellinTerm q Φ M g n) := by
  unfold dfiVoronoiMellinTerm
  apply hInt.bdd_mul
      (c := ‖LSeries.term (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) n‖)
  · by_cases hn : n = 0
    · subst n
      simpa [LSeries.term_zero] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _u : ℝ => (0 : ℂ)))
    · simp_rw [LSeries.term_of_ne_zero hn]
      have hBase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hExponent : Continuous (fun u : ℝ =>
          1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by fun_prop
      have hPow : Continuous (fun u : ℝ =>
          (n : ℂ) ^ (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I))) :=
        hExponent.const_cpow (Or.inl hBase)
      exact (continuous_const.div hPow (fun _u =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hBase))).aestronglyMeasurable
  · filter_upwards with u
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    norm_num

theorem integral_norm_dfiVoronoiMellinTerm
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ) (n : ℕ) :
    (∫ u : ℝ, ‖dfiVoronoiMellinTerm q Φ M g n u‖) =
      ‖LSeries.term (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) n‖ *
        ∫ u : ℝ,
          ‖M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
            mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  unfold dfiVoronoiMellinTerm
  rw [norm_mul]
  congr 1
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  norm_num

theorem summable_integral_norm_dfiVoronoiMellinTerm
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ) :
    Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖dfiVoronoiMellinTerm q Φ M g n u‖) := by
  have hCoeff : LSeriesSummable (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) :=
    periodicDivisorCoeff_LSeriesSummable q Φ (by norm_num)
  have hNorm : Summable (fun n : ℕ =>
      ‖LSeries.term (periodicDivisorCoeff q Φ) (3 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr hCoeff
  have hMul := hNorm.mul_right
    (∫ u : ℝ,
      ‖M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)‖)
  apply hMul.congr
  intro n
  exact (integral_norm_dfiVoronoiMellinTerm q Φ M g n).symm

theorem integrable_tsum_of_summable_integral_norm_dfi
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, Integrable (F n) measure)
    (hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂measure)) :
    Integrable (fun x => ∑' n, F n x) measure := by
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) measure := (hFint n).1
  have hNormMeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) measure :=
    (hMeas n).enorm
  have hLIntegral : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂measure ≠ ⊤ := by
    have hEach (n : ℕ) : ∫⁻ x, ‖F n x‖ₑ ∂measure =
        ‖∫ x, ‖F n x‖ ∂measure‖₊ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hFint n).norm,
        ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
      simp only [coe_nnnorm]
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  have hPointwise : ∀ᵐ x ∂measure,
      Summable (fun n => (‖F n x‖₊ : ℝ)) := by
    rw [← lintegral_tsum hNormMeas] at hLIntegral
    refine (ae_lt_top' (AEMeasurable.tsum hNormMeas) hLIntegral).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hBoundInt : Integrable (fun x => ∑' n, ‖F n x‖) measure := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hFint n).norm.1), ?_⟩
    dsimp [HasFiniteIntegral]
    have hFinite : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂measure < ⊤ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hLIntegral
    convert hFinite using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm,
      NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  refine hBoundInt.mono' (AEStronglyMeasurable.tsum hMeas) ?_
  filter_upwards [hPointwise] with x hx
  exact norm_tsum_le_tsum_norm hx

theorem integrable_periodicEstermann_one_sub_mul
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ)
    (hInt : Integrable (fun u : ℝ =>
      M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))) :
    Integrable (fun u : ℝ =>
      periodicEstermann q Φ
          (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) *
        M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
  have hTermInt : ∀ n : ℕ, Integrable (dfiVoronoiMellinTerm q Φ M g n) :=
    fun n => integrable_dfiVoronoiMellinTerm q Φ M g n hInt
  have hTermSum : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖dfiVoronoiMellinTerm q Φ M g n u‖) :=
    summable_integral_norm_dfiVoronoiMellinTerm q Φ M g
  have hSeries := integrable_tsum_of_summable_integral_norm_dfi
    hTermInt hTermSum
  apply hSeries.congr
  filter_upwards with u
  have hs : 1 < (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)).re := by norm_num
  rw [periodicEstermann_eq_LSeries q Φ hs]
  unfold LSeries dfiVoronoiMellinTerm
  rw [tsum_mul_right]
  ring

theorem verticalIntegral_periodicEstermann_one_sub_mul
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ)
    (hInt : Integrable (fun u : ℝ =>
      M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))) :
    VerticalIntegral' (fun z : ℂ =>
        periodicEstermann q Φ (1 - z) * M z * mellin g z)
      (-(1 / 2 : ℝ)) =
      ∑' n : ℕ, VerticalIntegral' (fun z : ℂ =>
        LSeries.term (periodicDivisorCoeff q Φ) (1 - z) n *
          (M z * mellin g z)) (-(1 / 2 : ℝ)) := by
  have hTermInt : ∀ n : ℕ, Integrable (dfiVoronoiMellinTerm q Φ M g n) :=
    fun n => integrable_dfiVoronoiMellinTerm q Φ M g n hInt
  have hTermSum : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖dfiVoronoiMellinTerm q Φ M g n u‖) :=
    summable_integral_norm_dfiVoronoiMellinTerm q Φ M g
  have hIntegral :
      (∫ u : ℝ,
        periodicEstermann q Φ
            (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) *
          M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
          mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) =
        ∑' n : ℕ, ∫ u : ℝ, dfiVoronoiMellinTerm q Φ M g n u := by
    rw [MeasureTheory.integral_tsum_of_summable_integral_norm
      hTermInt hTermSum]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    have hs : 1 <
        (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)).re := by norm_num
    rw [periodicEstermann_eq_LSeries q Φ hs]
    unfold LSeries dfiVoronoiMellinTerm
    rw [tsum_mul_right]
    ring
  unfold dfiVoronoiMellinTerm at hIntegral
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  calc
    _ = (1 / (2 * Real.pi * I)) *
          (I * ∫ u : ℝ,
            periodicEstermann q Φ
                (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) *
              M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
              mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
      congr 3
      funext u
      norm_num
    _ = (1 / (2 * Real.pi * I)) *
          (I * (∑' n : ℕ, ∫ u : ℝ,
            LSeries.term (periodicDivisorCoeff q Φ)
                (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) n *
              (M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
                mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I)))) :=
      congrArg (fun w : ℂ => (1 / (2 * Real.pi * I)) * (I * w)) hIntegral
    _ = ∑' n : ℕ, (1 / (2 * Real.pi * I)) *
          (I * ∫ u : ℝ,
            LSeries.term (periodicDivisorCoeff q Φ)
                (1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)) n *
              (M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
                mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro n
      congr 3
      funext u
      norm_num

theorem verticalIntegral'_const_mul (c : ℂ) (f : ℂ → ℂ) (σ : ℝ) :
    VerticalIntegral' (fun z : ℂ => c * f z) σ =
      c * VerticalIntegral' f σ := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

theorem verticalIntegral_dfiVoronoiMellinTerm
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ) (n : ℕ) :
    VerticalIntegral' (fun z : ℂ =>
        LSeries.term (periodicDivisorCoeff q Φ) (1 - z) n *
          (M z * mellin g z)) (-(1 / 2 : ℝ)) =
      periodicDivisorCoeff q Φ n *
        VerticalIntegral' (fun z : ℂ =>
          (n : ℂ) ^ (-(1 - z)) * M z * mellin g z)
          (-(1 / 2 : ℝ)) := by
  have hCoeffZero : periodicDivisorCoeff q Φ 0 = 0 := by
    simp [periodicDivisorCoeff]
  rw [← verticalIntegral'_const_mul
    (periodicDivisorCoeff q Φ n)
    (fun z : ℂ => (n : ℂ) ^ (-(1 - z)) * M z * mellin g z)
    (-(1 / 2 : ℝ))]
  congr 1
  funext z
  rw [LSeries.term_def₀ hCoeffZero]
  ring

theorem verticalIntegral_periodicEstermann_one_sub_mul_eq_transforms
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (M : ℂ → ℂ)
    (g : ℝ → ℂ)
    (hInt : Integrable (fun u : ℝ =>
      M (-(1 / 2 : ℂ) + (u : ℂ) * I) *
        mellin g (-(1 / 2 : ℂ) + (u : ℂ) * I))) :
    VerticalIntegral' (fun z : ℂ =>
        periodicEstermann q Φ (1 - z) * M z * mellin g z)
      (-(1 / 2 : ℝ)) =
      ∑' n : ℕ, periodicDivisorCoeff q Φ n *
        VerticalIntegral' (fun z : ℂ =>
          (n : ℂ) ^ (-(1 - z)) * M z * mellin g z)
          (-(1 / 2 : ℝ)) := by
  rw [verticalIntegral_periodicEstermann_one_sub_mul q Φ M g hInt]
  apply tsum_congr
  intro n
  exact verticalIntegral_dfiVoronoiMellinTerm q Φ M g n

theorem verticalIntegral'_add {f h : ℂ → ℂ} (σ : ℝ)
    (hf : Integrable (fun u : ℝ => f ((σ : ℂ) + (u : ℂ) * I)))
    (hh : Integrable (fun u : ℝ => h ((σ : ℂ) + (u : ℂ) * I))) :
    VerticalIntegral' (fun z : ℂ => f z + h z) σ =
      VerticalIntegral' f σ + VerticalIntegral' h σ := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [MeasureTheory.integral_add hf hh]
  ring

noncomputable def dfiMinusBranchIntegrand (q : ℕ) [NeZero q]
    (d : ZMod q) (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹)) (1 - z) *
    dfiVoronoiMinusMultiplier q z * mellin g z

noncomputable def dfiPlusBranchIntegrand (q : ℕ) [NeZero q]
    (d : ZMod q) (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  periodicEstermann q (dfiVoronoiCharacter q d⁻¹) (1 - z) *
    dfiVoronoiPlusMultiplier q z * mellin g z

theorem DFIVoronoiTestFunction.integrable_minusBranch
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) :
    Integrable (fun u : ℝ =>
      dfiMinusBranchIntegrand q d g
        (((-(1 / 2 : ℝ) : ℂ)) + (u : ℂ) * I)) := by
  unfold dfiMinusBranchIntegrand
  simpa only [Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one] using
    (integrable_periodicEstermann_one_sub_mul q
      (dfiVoronoiCharacter q (-d⁻¹)) (dfiVoronoiMinusMultiplier q) g
      (hg.integrable_minusMultiplier_mul_mellin q))

theorem DFIVoronoiTestFunction.integrable_plusBranch
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) :
    Integrable (fun u : ℝ =>
      dfiPlusBranchIntegrand q d g
        (((-(1 / 2 : ℝ) : ℂ)) + (u : ℂ) * I)) := by
  unfold dfiPlusBranchIntegrand
  simpa only [Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one] using
    (integrable_periodicEstermann_one_sub_mul q
      (dfiVoronoiCharacter q d⁻¹) (dfiVoronoiPlusMultiplier q) g
      (hg.integrable_plusMultiplier_mul_mellin q))

theorem DFIVoronoiTestFunction.minusIntegral_voronoiCharacter
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) :
    VerticalIntegral' (dfiMinusBranchIntegrand q d g) (-(1 / 2 : ℝ)) =
      ∑' n : ℕ, periodicDivisorCoeff q
          (dfiVoronoiCharacter q (-d⁻¹)) n *
        dfiVoronoiMinusTransform q (mellin g) n := by
  have hMinus := verticalIntegral_periodicEstermann_one_sub_mul_eq_transforms
    q (dfiVoronoiCharacter q (-d⁻¹)) (dfiVoronoiMinusMultiplier q) g
    (hg.integrable_minusMultiplier_mul_mellin q)
  unfold dfiMinusBranchIntegrand
  simpa only [dfiVoronoiMinusTransform, mul_assoc] using hMinus

theorem DFIVoronoiTestFunction.plusIntegral_voronoiCharacter
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) :
    VerticalIntegral' (dfiPlusBranchIntegrand q d g) (-(1 / 2 : ℝ)) =
      ∑' n : ℕ, periodicDivisorCoeff q
          (dfiVoronoiCharacter q d⁻¹) n *
        dfiVoronoiPlusTransform q (mellin g) n := by
  have hPlus := verticalIntegral_periodicEstermann_one_sub_mul_eq_transforms
    q (dfiVoronoiCharacter q d⁻¹) (dfiVoronoiPlusMultiplier q) g
    (hg.integrable_plusMultiplier_mul_mellin q)
  unfold dfiPlusBranchIntegrand
  simpa only [dfiVoronoiPlusTransform, mul_assoc] using hPlus

set_option maxHeartbeats 800000 in
theorem DFIVoronoiTestFunction.reflectedIntegral_voronoiCharacter
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    VerticalIntegral'
        (periodicEstermannReflectedIntegrand q
          (dfiVoronoiCharacter q d) (mellin g))
        (-(1 / 2 : ℝ)) =
      (∑' n : ℕ, periodicDivisorCoeff q
          (dfiVoronoiCharacter q (-d⁻¹)) n *
        dfiVoronoiMinusTransform q (mellin g) n) +
      ∑' n : ℕ, periodicDivisorCoeff q
          (dfiVoronoiCharacter q d⁻¹) n *
        dfiVoronoiPlusTransform q (mellin g) n := by
  have hSplit : periodicEstermannReflectedIntegrand q
      (dfiVoronoiCharacter q d) (mellin g) =
      fun z => dfiMinusBranchIntegrand q d g z +
        dfiPlusBranchIntegrand q d g z := by
    funext z
    unfold dfiMinusBranchIntegrand dfiPlusBranchIntegrand
    exact periodicEstermannReflectedIntegrand_voronoiCharacter
      q d hd (mellin g) z
  have hMinusInt : Integrable (fun u : ℝ =>
      dfiMinusBranchIntegrand q d g
        (((-(1 / 2 : ℝ) : ℂ)) + (u : ℂ) * I)) := by
    exact hg.integrable_minusBranch q d
  have hPlusInt : Integrable (fun u : ℝ =>
      dfiPlusBranchIntegrand q d g
        (((-(1 / 2 : ℝ) : ℂ)) + (u : ℂ) * I)) := by
    exact hg.integrable_plusBranch q d
  calc
    VerticalIntegral'
          (periodicEstermannReflectedIntegrand q
            (dfiVoronoiCharacter q d) (mellin g)) (-(1 / 2 : ℝ)) =
        VerticalIntegral' (fun z => dfiMinusBranchIntegrand q d g z +
          dfiPlusBranchIntegrand q d g z) (-(1 / 2 : ℝ)) :=
      congrArg (fun F : ℂ → ℂ => VerticalIntegral' F (-(1 / 2 : ℝ))) hSplit
    _ = VerticalIntegral' (dfiMinusBranchIntegrand q d g) (-(1 / 2 : ℝ)) +
        VerticalIntegral' (dfiPlusBranchIntegrand q d g) (-(1 / 2 : ℝ)) :=
      verticalIntegral'_add (-(1 / 2 : ℝ))
        (by simpa only [Complex.ofReal_neg] using hMinusInt)
        (by simpa only [Complex.ofReal_neg] using hPlusInt)
    _ = _ := congrArg₂ (· + ·)
      (hg.minusIntegral_voronoiCharacter q d)
      (hg.plusIntegral_voronoiCharacter q d)

/-- DFI Proposition 1 in its source additive-character specialization.
The two canonical Mellin--Barnes transforms have exactly the source
normalizations `-(2π/q)Y₀` and `(4/q)K₀`. -/
theorem DFIVoronoiTestFunction.dfiProposition1_native
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    periodicDivisorWeightedSum q (dfiVoronoiCharacter q d) g =
      dfiVoronoiMainTerm q g +
        (∑' n : ℕ, divisorWeight n *
          ZMod.stdAddChar ((-d⁻¹) * (n : ZMod q)) *
            dfiVoronoiMinusTransform q (mellin g) n) +
        ∑' n : ℕ, divisorWeight n *
          ZMod.stdAddChar (d⁻¹ * (n : ZMod q)) *
            dfiVoronoiPlusTransform q (mellin g) n := by
  rw [hg.periodicDivisorVoronoi_mellinBarnes_native q
    (dfiVoronoiCharacter q d)]
  rw [dfiVoronoi_laurent_mainTerm q d hd hg]
  rw [hg.reflectedIntegral_voronoiCharacter q d hd]
  simp_rw [periodicDivisorCoeff_voronoiCharacter]
  ring

end RiemannZeta.GuthMaynard
