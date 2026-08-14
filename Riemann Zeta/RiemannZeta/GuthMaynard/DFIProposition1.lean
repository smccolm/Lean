import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import RiemannZeta.GuthMaynard.DivisorVoronoi

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# DFI Proposition 1: divisor Voronoi summation

This file develops the Poisson--Voronoi formula used between DFI equations
(22) and (23).  The first layer below connects the literal additive divisor
coefficient to the repository's periodic Estermann continuation and computes
its double-pole coefficient.  The Bessel-transform expansion is built on this
source entry, rather than accepted as a hypothesis.
-/

/-- Exact half-line Gamma norm identity obtained from Euler's reflection
formula.  It supplies the exponential decay needed for the DFI left
contour without assuming a Stirling estimate. -/
theorem Gamma_half_add_mul_I_norm_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hConj : 1 - z = (starRingEnd ℂ) z := by
    dsimp [z]
    apply Complex.ext
    · simp
      norm_num
    · simp
  rw [hConj, Complex.Gamma_conj, Complex.mul_conj] at h
  have hSin : Complex.sin ((Real.pi : ℂ) * z) =
      (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * z =
        (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * I by
      dsimp [z]
      push_cast
      ring]
    rw [Complex.sin_add, Complex.sin_pi_div_two,
      Complex.cos_pi_div_two, Complex.cos_mul_I]
    simp
  rw [hSin] at h
  rw [Complex.sq_norm]
  change Complex.normSq (Complex.Gamma z) = _
  exact_mod_cast h

theorem Gamma_three_half_add_mul_I_norm_sq (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ((1 / 4 : ℝ) + t ^ 2) *
        (Real.pi / Real.cosh (Real.pi * t)) := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
  have hRec := Complex.Gamma_add_one z hz
  have hArg : z + 1 = (3 / 2 : ℂ) + (t : ℂ) * I := by
    dsimp [z]
    ring
  rw [hArg] at hRec
  rw [hRec, norm_mul, mul_pow, Gamma_half_add_mul_I_norm_sq]
  have hNorm : ‖z‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
    rw [Complex.sq_norm]
    dsimp [z]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hNorm]

theorem exp_le_two_mul_cosh (x : ℝ) :
    Real.exp x ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  have h := Real.exp_pos (-x)
  linarith

theorem exp_neg_le_two_mul_cosh (x : ℝ) :
    Real.exp (-x) ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  have h := Real.exp_pos x
  linarith

theorem norm_voronoiExp_pos_sq (u : ℝ) :
    ‖Complex.exp (Real.pi * I *
      ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ^ 2 =
      Real.exp (Real.pi * u) := by
  rw [Complex.norm_exp]
  norm_num
  rw [← Real.exp_nat_mul]
  congr 1
  ring_nf

theorem norm_voronoiExp_neg_sq (u : ℝ) :
    ‖Complex.exp (-Real.pi * I *
      ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ^ 2 =
      Real.exp (-Real.pi * u) := by
  rw [Complex.norm_exp]
  norm_num
  rw [← Real.exp_nat_mul]
  congr 1
  ring_nf

private theorem norm_Gamma_mul_voronoiExp_le_aux (u : ℝ) (sign : ℝ)
    (hSign : sign = 1 ∨ sign = -1) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
      Complex.exp (sign * Real.pi * I *
        ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * (1 + |u|) := by
  rcases hSign with rfl | rfl
  · let s : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
    have hGamma : ‖Complex.Gamma s‖ ^ 2 =
        ((1 / 4 : ℝ) + u ^ 2) *
          (Real.pi / Real.cosh (Real.pi * u)) := by
      simpa [s] using Gamma_three_half_add_mul_I_norm_sq (-u)
    have hExp : ‖Complex.exp (Real.pi * I * s / 2)‖ ^ 2 =
        Real.exp (Real.pi * u) := by
      simpa [s] using norm_voronoiExp_pos_sq u
    have hCosh : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
    have hRatio :
        (Real.pi / Real.cosh (Real.pi * u)) * Real.exp (Real.pi * u) ≤
          2 * Real.pi := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCosh]
      have h := exp_le_two_mul_cosh (Real.pi * u)
      nlinarith [Real.pi_pos]
    have hSq : ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2)‖ ^ 2 ≤
        (4 * (1 + |u|)) ^ 2 := by
      rw [norm_mul, mul_pow, hGamma, hExp]
      have hA : 0 ≤ (1 / 4 : ℝ) + u ^ 2 := by positivity
      have hPi : Real.pi ≤ 4 := Real.pi_lt_four.le
      calc
        ((1 / 4 : ℝ) + u ^ 2) *
            (Real.pi / Real.cosh (Real.pi * u)) * Real.exp (Real.pi * u) =
            ((1 / 4 : ℝ) + u ^ 2) *
              ((Real.pi / Real.cosh (Real.pi * u)) * Real.exp (Real.pi * u)) := by ring
        _ ≤ ((1 / 4 : ℝ) + u ^ 2) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left hRatio hA
        _ ≤ ((1 / 4 : ℝ) + u ^ 2) * 8 := by nlinarith
        _ ≤ (4 * (1 + |u|)) ^ 2 := by
          have huSq : |u| ^ 2 = u ^ 2 := sq_abs u
          nlinarith [abs_nonneg u]
    have hNorm : 0 ≤ ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2)‖ :=
      norm_nonneg _
    have hRight : 0 ≤ 4 * (1 + |u|) := by positivity
    simpa [s] using (show
      ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2)‖ ≤
        4 * (1 + |u|) by nlinarith)
  · let s : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
    have hGamma : ‖Complex.Gamma s‖ ^ 2 =
        ((1 / 4 : ℝ) + u ^ 2) *
          (Real.pi / Real.cosh (Real.pi * u)) := by
      simpa [s] using Gamma_three_half_add_mul_I_norm_sq (-u)
    have hExp : ‖Complex.exp (-Real.pi * I * s / 2)‖ ^ 2 =
        Real.exp (-Real.pi * u) := by
      simpa [s] using norm_voronoiExp_neg_sq u
    have hCosh : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
    have hRatio :
        (Real.pi / Real.cosh (Real.pi * u)) * Real.exp (-Real.pi * u) ≤
          2 * Real.pi := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCosh]
      have h := exp_neg_le_two_mul_cosh (Real.pi * u)
      have h' : Real.exp (-Real.pi * u) ≤
          2 * Real.cosh (Real.pi * u) := by
        simpa only [neg_mul] using h
      nlinarith [Real.pi_pos]
    have hSq : ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2)‖ ^ 2 ≤
        (4 * (1 + |u|)) ^ 2 := by
      rw [norm_mul, mul_pow, hGamma, hExp]
      have hA : 0 ≤ (1 / 4 : ℝ) + u ^ 2 := by positivity
      have hPi : Real.pi ≤ 4 := Real.pi_lt_four.le
      calc
        ((1 / 4 : ℝ) + u ^ 2) *
            (Real.pi / Real.cosh (Real.pi * u)) * Real.exp (-Real.pi * u) =
            ((1 / 4 : ℝ) + u ^ 2) *
              ((Real.pi / Real.cosh (Real.pi * u)) * Real.exp (-Real.pi * u)) := by ring
        _ ≤ ((1 / 4 : ℝ) + u ^ 2) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left hRatio hA
        _ ≤ ((1 / 4 : ℝ) + u ^ 2) * 8 := by nlinarith
        _ ≤ (4 * (1 + |u|)) ^ 2 := by
          have huSq : |u| ^ 2 = u ^ 2 := sq_abs u
          nlinarith [abs_nonneg u]
    have hNorm : 0 ≤ ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2)‖ :=
      norm_nonneg _
    have hRight : 0 ≤ 4 * (1 + |u|) := by positivity
    simpa [s] using (show
      ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2)‖ ≤
        4 * (1 + |u|) by nlinarith)

theorem norm_Gamma_mul_voronoiExp_pos_le (u : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
      Complex.exp (Real.pi * I *
        ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * (1 + |u|) := by
  simpa using norm_Gamma_mul_voronoiExp_le_aux u 1 (Or.inl rfl)

theorem norm_Gamma_mul_voronoiExp_neg_le (u : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
      Complex.exp (-Real.pi * I *
        ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * (1 + |u|) := by
  simpa using norm_Gamma_mul_voronoiExp_le_aux u (-1) (Or.inr rfl)

/-- The absolute Dirichlet-series majorant for a periodic coefficient on the
fixed reflected line `Re s = 3/2`. -/
noncomputable def dfiPeriodicLSeriesNorm (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun m : ℕ => Ψ m) (3 / 2 : ℂ) n‖

theorem norm_periodicLFunction_three_half_sub_mul_I_le
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) (u : ℝ) :
    ‖ZMod.LFunction Ψ ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤
      dfiPeriodicLSeriesNorm q Ψ := by
  have hs : 1 < (((3 / 2 : ℂ) - (u : ℂ) * I).re) := by norm_num
  rw [ZMod.LFunction_eq_LSeries Ψ hs]
  have hSummable : LSeriesSummable (fun m : ℕ => Ψ m)
      ((3 / 2 : ℂ) - (u : ℂ) * I) :=
    ZMod.LSeriesSummable_of_one_lt_re Ψ hs
  unfold LSeries dfiPeriodicLSeriesNorm
  calc
    ‖∑' n : ℕ, LSeries.term (fun m : ℕ => Ψ m)
        ((3 / 2 : ℂ) - (u : ℂ) * I) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term (fun m : ℕ => Ψ m)
          ((3 / 2 : ℂ) - (u : ℂ) * I) n‖ :=
      norm_tsum_le_tsum_norm hSummable.norm
    _ = ∑' n : ℕ,
        ‖LSeries.term (fun m : ℕ => Ψ m) (3 / 2 : ℂ) n‖ := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      norm_num

/-- Each reflected periodic L-function has only linear growth on the DFI
line `Re s = 3/2`.  The two exponentially unbalanced Fourier signs are
controlled separately before their sum is formed. -/
theorem periodicLFunctionDual_three_half_sub_mul_I_bound
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖periodicLFunctionDual q Ψ
        ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤ C * (1 + |u|) := by
  let B₁ : ℝ := dfiPeriodicLSeriesNorm q (ZMod.dft Ψ)
  let B₂ : ℝ := dfiPeriodicLSeriesNorm q (ZMod.dft fun x => Ψ (-x))
  let A : ℝ := ‖(q : ℂ) ^ (1 / 2 : ℂ)‖ *
    ‖(2 * Real.pi : ℂ) ^ (-(3 / 2 : ℂ))‖
  refine ⟨A * 4 * (B₁ + B₂), ?_, ?_⟩
  · have hB₁ : 0 ≤ B₁ := by
      exact tsum_nonneg (fun _ => norm_nonneg _)
    have hB₂ : 0 ≤ B₂ := by
      exact tsum_nonneg (fun _ => norm_nonneg _)
    dsimp [A]
    positivity
  · intro u
    let s : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
    have hq : 0 < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
    have hTwoPi : 0 < 2 * Real.pi := by positivity
    have hqNorm : ‖(q : ℂ) ^ (s - 1)‖ = ‖(q : ℂ) ^ (1 / 2 : ℂ)‖ := by
      rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
        Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
      congr 1
      norm_num [s]
    have hTwoPiNorm : ‖(2 * Real.pi : ℂ) ^ (-s)‖ =
        ‖(2 * Real.pi : ℂ) ^ (-(3 / 2 : ℂ))‖ := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by
        norm_cast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hTwoPi,
        Complex.norm_cpow_eq_rpow_re_of_pos hTwoPi]
      congr 1
      norm_num [s]
    have hL₁ : ‖ZMod.LFunction (ZMod.dft Ψ) s‖ ≤ B₁ := by
      simpa [s, B₁] using
        norm_periodicLFunction_three_half_sub_mul_I_le q (ZMod.dft Ψ) u
    have hL₂ : ‖ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ ≤ B₂ := by
      simpa [s, B₂] using
        norm_periodicLFunction_three_half_sub_mul_I_le q
          (ZMod.dft fun x => Ψ (-x)) u
    have hB₁ : 0 ≤ B₁ := by exact tsum_nonneg (fun _ => norm_nonneg _)
    have hB₂ : 0 ≤ B₂ := by exact tsum_nonneg (fun _ => norm_nonneg _)
    let D : ℂ :=
      Complex.exp (Real.pi * I * s / 2) *
          ZMod.LFunction (ZMod.dft Ψ) s +
        Complex.exp (-Real.pi * I * s / 2) *
          ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s
    have hPlus : ‖Complex.Gamma s *
        Complex.exp (Real.pi * I * s / 2) *
          ZMod.LFunction (ZMod.dft Ψ) s‖ ≤
        4 * (1 + |u|) * B₁ := by
      rw [norm_mul]
      exact mul_le_mul (by
        simpa [s] using norm_Gamma_mul_voronoiExp_pos_le u) hL₁
        (norm_nonneg _) (by positivity)
    have hMinus : ‖Complex.Gamma s *
        Complex.exp (-Real.pi * I * s / 2) *
          ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ ≤
        4 * (1 + |u|) * B₂ := by
      rw [norm_mul]
      exact mul_le_mul (by
        simpa [s] using norm_Gamma_mul_voronoiExp_neg_le u) hL₂
        (norm_nonneg _) (by positivity)
    have hInside : ‖Complex.Gamma s * D‖ ≤
        4 * (1 + |u|) * (B₁ + B₂) := by
      dsimp [D]
      rw [mul_add]
      calc
        ‖Complex.Gamma s *
              (Complex.exp (Real.pi * I * s / 2) *
                ZMod.LFunction (ZMod.dft Ψ) s) +
            Complex.Gamma s *
              (Complex.exp (-Real.pi * I * s / 2) *
                ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ ≤
            ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2) *
                ZMod.LFunction (ZMod.dft Ψ) s‖ +
              ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2) *
                ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ := by
          simpa [mul_assoc] using norm_add_le
            (Complex.Gamma s * Complex.exp (Real.pi * I * s / 2) *
              ZMod.LFunction (ZMod.dft Ψ) s)
            (Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2) *
              ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)
        _ ≤ 4 * (1 + |u|) * B₁ + 4 * (1 + |u|) * B₂ :=
          add_le_add hPlus hMinus
        _ = 4 * (1 + |u|) * (B₁ + B₂) := by ring
    have hA : 0 ≤ A := by dsimp [A]; positivity
    unfold periodicLFunctionDual
    change ‖(q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) *
        Complex.Gamma s * D‖ ≤ _
    calc
      ‖(q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) *
          Complex.Gamma s * D‖ =
          ‖(q : ℂ) ^ (1 / 2 : ℂ)‖ *
            ‖(2 * Real.pi : ℂ) ^ (-(3 / 2 : ℂ))‖ *
            ‖Complex.Gamma s * D‖ := by
        rw [show (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) *
              Complex.Gamma s * D =
            ((q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s)) *
              (Complex.Gamma s * D) by ring]
        rw [norm_mul, norm_mul, hqNorm, hTwoPiNorm]
      _ ≤
          A * (4 * (1 + |u|) * (B₁ + B₂)) := by
        exact mul_le_mul_of_nonneg_left hInside hA
      _ = (A * 4 * (B₁ + B₂)) * (1 + |u|) := by ring

noncomputable def dfiPeriodicDualGrowthConstant (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) : ℝ :=
  Classical.choose (periodicLFunctionDual_three_half_sub_mul_I_bound q Ψ)

theorem dfiPeriodicDualGrowthConstant_nonneg (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    0 ≤ dfiPeriodicDualGrowthConstant q Ψ :=
  (Classical.choose_spec
    (periodicLFunctionDual_three_half_sub_mul_I_bound q Ψ)).1

theorem norm_periodicLFunctionDual_three_half_sub_mul_I_le
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) (u : ℝ) :
    ‖periodicLFunctionDual q Ψ
      ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤
      dfiPeriodicDualGrowthConstant q Ψ * (1 + |u|) :=
  (Classical.choose_spec
    (periodicLFunctionDual_three_half_sub_mul_I_bound q Ψ)).2 u

/-- The complete reflected Estermann function has quadratic growth on the
fixed DFI line.  This is a finite consequence of the two periodic
L-function bounds, not an assumed convexity estimate. -/
theorem periodicEstermannDual_three_half_sub_mul_I_bound
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖periodicEstermannDual q Φ
        ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  let C : ℝ := ∑ a : ZMod q, ∑ b : ZMod q,
    ‖Φ (a * b)‖ *
      dfiPeriodicDualGrowthConstant q (fun x => if x = a then 1 else 0) *
      dfiPeriodicDualGrowthConstant q (fun x => if x = b then 1 else 0)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    apply Finset.sum_nonneg
    intro a _ha
    apply Finset.sum_nonneg
    intro b _hb
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _)
        (dfiPeriodicDualGrowthConstant_nonneg q _))
      (dfiPeriodicDualGrowthConstant_nonneg q _)
  · intro u
    unfold periodicEstermannDual
    calc
      ‖∑ a : ZMod q, ∑ b : ZMod q,
          Φ (a * b) *
            periodicLFunctionDual q (fun x => if x = a then 1 else 0)
              ((3 / 2 : ℂ) - (u : ℂ) * I) *
            periodicLFunctionDual q (fun x => if x = b then 1 else 0)
              ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤
          ∑ a : ZMod q, ∑ b : ZMod q,
            ‖Φ (a * b) *
              periodicLFunctionDual q (fun x => if x = a then 1 else 0)
                ((3 / 2 : ℂ) - (u : ℂ) * I) *
              periodicLFunctionDual q (fun x => if x = b then 1 else 0)
                ((3 / 2 : ℂ) - (u : ℂ) * I)‖ := by
        calc
          ‖∑ a : ZMod q, ∑ b : ZMod q,
              Φ (a * b) *
                periodicLFunctionDual q (fun x => if x = a then 1 else 0)
                  ((3 / 2 : ℂ) - (u : ℂ) * I) *
                periodicLFunctionDual q (fun x => if x = b then 1 else 0)
                  ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤
              ∑ a : ZMod q, ‖∑ b : ZMod q,
                Φ (a * b) *
                  periodicLFunctionDual q (fun x => if x = a then 1 else 0)
                    ((3 / 2 : ℂ) - (u : ℂ) * I) *
                  periodicLFunctionDual q (fun x => if x = b then 1 else 0)
                    ((3 / 2 : ℂ) - (u : ℂ) * I)‖ := by
            exact norm_sum_le _ _
          _ ≤ ∑ a : ZMod q, ∑ b : ZMod q,
                ‖Φ (a * b) *
                  periodicLFunctionDual q (fun x => if x = a then 1 else 0)
                    ((3 / 2 : ℂ) - (u : ℂ) * I) *
                  periodicLFunctionDual q (fun x => if x = b then 1 else 0)
                    ((3 / 2 : ℂ) - (u : ℂ) * I)‖ := by
            apply Finset.sum_le_sum
            intro a _ha
            exact norm_sum_le _ _
      _ ≤ ∑ a : ZMod q, ∑ b : ZMod q,
          (‖Φ (a * b)‖ *
            dfiPeriodicDualGrowthConstant q (fun x => if x = a then 1 else 0) *
            dfiPeriodicDualGrowthConstant q (fun x => if x = b then 1 else 0)) *
              (1 + |u|) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _ha
        apply Finset.sum_le_sum
        intro b _hb
        rw [norm_mul, norm_mul]
        have hA := norm_periodicLFunctionDual_three_half_sub_mul_I_le q
          (fun x => if x = a then 1 else 0) u
        have hB := norm_periodicLFunctionDual_three_half_sub_mul_I_le q
          (fun x => if x = b then 1 else 0) u
        have hΦ : 0 ≤ ‖Φ (a * b)‖ := norm_nonneg _
        have hCA : 0 ≤ dfiPeriodicDualGrowthConstant q
            (fun x => if x = a then 1 else 0) :=
          dfiPeriodicDualGrowthConstant_nonneg q _
        have hCB : 0 ≤ dfiPeriodicDualGrowthConstant q
            (fun x => if x = b then 1 else 0) :=
          dfiPeriodicDualGrowthConstant_nonneg q _
        have hOne : 0 ≤ 1 + |u| := by positivity
        calc
          ‖Φ (a * b)‖ *
              ‖periodicLFunctionDual q (fun x => if x = a then 1 else 0)
                ((3 / 2 : ℂ) - (u : ℂ) * I)‖ *
              ‖periodicLFunctionDual q (fun x => if x = b then 1 else 0)
                ((3 / 2 : ℂ) - (u : ℂ) * I)‖ ≤
              ‖Φ (a * b)‖ *
                (dfiPeriodicDualGrowthConstant q
                    (fun x => if x = a then 1 else 0) * (1 + |u|)) *
                (dfiPeriodicDualGrowthConstant q
                    (fun x => if x = b then 1 else 0) * (1 + |u|)) := by
            gcongr
          _ = (‖Φ (a * b)‖ *
              dfiPeriodicDualGrowthConstant q (fun x => if x = a then 1 else 0) *
              dfiPeriodicDualGrowthConstant q (fun x => if x = b then 1 else 0)) *
                (1 + |u|) ^ 2 := by ring
      _ = C * (1 + |u|) ^ 2 := by
        dsimp [C]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_mul]

/-- The periodic additive character `n ↦ e(dn/q)` in Proposition 1. -/
noncomputable def dfiVoronoiCharacter (q : ℕ) [NeZero q]
    (d : ZMod q) (n : ZMod q) : ℂ :=
  ZMod.stdAddChar (d * n)

@[simp]
theorem dfiVoronoiCharacter_apply (q : ℕ) [NeZero q]
    (d n : ZMod q) :
    dfiVoronoiCharacter q d n = ZMod.stdAddChar (d * n) := rfl

/-- The periodic divisor coefficient is literally
`τ(n)e(dn/q)` for the source additive character. -/
theorem periodicDivisorCoeff_voronoiCharacter (q : ℕ) [NeZero q]
    (d : ZMod q) (n : ℕ) :
    periodicDivisorCoeff q (dfiVoronoiCharacter q d) n =
      divisorWeight n * ZMod.stdAddChar (d * (n : ZMod q)) := by
  rfl

private theorem isUnit_mul_eq_zero_iff {R : Type*} [MonoidWithZero R]
    {a b : R} (ha : IsUnit a) : a * b = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply ha.mul_left_cancel
    simpa using h
  · rintro rfl
    exact mul_zero a

/-- The elementary two-variable character orthogonality calculation behind
the leading `q⁻¹` coefficient of the Voronoi main term. -/
theorem sum_voronoiCharacter_mul (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) :
    ∑ a : ZMod q, ∑ b : ZMod q, dfiVoronoiCharacter q d (a * b) = (q : ℂ) := by
  calc
    ∑ a : ZMod q, ∑ b : ZMod q, dfiVoronoiCharacter q d (a * b) =
        ∑ b : ZMod q, ∑ a : ZMod q, ZMod.stdAddChar (a * (d * b)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      unfold dfiVoronoiCharacter
      congr 1
      ring
    _ = ∑ b : ZMod q, (if d * b = 0 then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      simpa using AddChar.sum_mulShift (d * b) (ZMod.isPrimitive_stdAddChar q)
    _ = ∑ b : ZMod q, (if b = 0 then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [isUnit_mul_eq_zero_iff hd]
    _ = (q : ℂ) := by simp

/-- Exact coefficient of the double pole of the additive Estermann series.
For `(d,q)=1` it is `1/q`, as in DFI Proposition 1. -/
theorem periodicEstermannLeadingCoeff_voronoiCharacter
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    periodicEstermannLeadingCoeff q (dfiVoronoiCharacter q d) =
      ((q : ℂ) : ℂ)⁻¹ := by
  unfold periodicEstermannLeadingCoeff
  rw [sum_voronoiCharacter_mul q d hd]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp

/-- At residue zero, the regularized periodic L-function is the scaled
regularized Riemann zeta function. -/
theorem periodicLFunctionRegularized_zeroIndicator (q : ℕ) [NeZero q]
    (s : ℂ) :
    periodicLFunctionRegularized q
        (fun x : ZMod q => if x = 0 then 1 else 0) s =
      (q : ℂ) ^ (-s) * hurwitzZetaRegularized 0 s := by
  unfold periodicLFunctionRegularized
  simp

/-- Exact entire continuation of `(s-1) q⁻s ζ(s)` used to compute the
simple-pole coefficient in Proposition 1. -/
theorem periodicLFunctionPoleCleared_zeroIndicator (q : ℕ) [NeZero q]
    (s : ℂ) :
    periodicLFunctionPoleCleared q
        (fun x : ZMod q => if x = 0 then 1 else 0) s =
      (s - 1) * ((q : ℂ) ^ (-s) * hurwitzZetaRegularized 0 s) +
        (q : ℂ) ^ (-s) * (Complex.Gammaℝ s)⁻¹ := by
  unfold periodicLFunctionPoleCleared
  rw [periodicLFunctionRegularized_zeroIndicator]
  simp

theorem periodicLFunctionPoleCleared_zeroIndicator_one
    (q : ℕ) [NeZero q] :
    periodicLFunctionPoleCleared q
        (fun x : ZMod q => if x = 0 then 1 else 0) 1 = (q : ℂ)⁻¹ := by
  rw [periodicLFunctionPoleCleared_zeroIndicator]
  simp [Complex.Gammaℝ_one, Complex.cpow_neg_one]

private theorem deriv_q_cpow_neg_at_one (q : ℕ) [NeZero q] :
    deriv (fun s : ℂ => (q : ℂ) ^ (-s)) 1 =
      -(q : ℂ)⁻¹ * Complex.log (q : ℂ) := by
  have h := ((hasDerivAt_neg (1 : ℂ)).const_cpow
    (c := (q : ℂ)) (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
  convert h.deriv using 1
  rw [Complex.cpow_neg_one]
  ring

private theorem deriv_Gammaℝ_inv_at_one :
    deriv (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 1 =
      (Real.eulerMascheroniConstant : ℂ) / 2 +
        Complex.log (4 * (Real.pi : ℂ)) / 2 := by
  have h := Complex.hasDerivAt_Gammaℝ_one.inv
    (Complex.Gammaℝ_one.trans_ne one_ne_zero)
  rw [Complex.Gammaℝ_one] at h
  convert h.deriv using 1
  ring_nf

/-- The derivative of the zero-class pole-cleared periodic L-function is
`q⁻¹(γ-log q)`.  This is the local Laurent calculation which supplies
the `2γ-2log q` term in DFI Proposition 1. -/
theorem deriv_periodicLFunctionPoleCleared_zeroIndicator
    (q : ℕ) [NeZero q] :
    deriv (periodicLFunctionPoleCleared q
      (fun x : ZMod q => if x = 0 then 1 else 0)) 1 =
      (q : ℂ)⁻¹ *
        ((Real.eulerMascheroniConstant : ℂ) - Complex.log (q : ℂ)) := by
  rw [show periodicLFunctionPoleCleared q
      (fun x : ZMod q => if x = 0 then 1 else 0) =
      fun s : ℂ =>
        (s - 1) * ((q : ℂ) ^ (-s) * hurwitzZetaRegularized 0 s) +
          (q : ℂ) ^ (-s) * (Complex.Gammaℝ s)⁻¹ by
    funext s
    exact periodicLFunctionPoleCleared_zeroIndicator q s]
  have hreg : hurwitzZetaRegularized 0 1 =
      ((Real.eulerMascheroniConstant : ℂ) -
        Complex.log (4 * (Real.pi : ℂ))) / 2 := by
    unfold hurwitzZetaRegularized
    rw [HurwitzZeta.hurwitzZeta_zero, riemannZeta_one]
    simp
  have hqhas : HasDerivAt (fun s : ℂ => (q : ℂ) ^ (-s))
      (-(q : ℂ)⁻¹ * Complex.log (q : ℂ)) 1 := by
    exact (deriv_q_cpow_neg_at_one q).symm ▸
      (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (-s)) 1).hasDerivAt
  have hregHas := (differentiable_hurwitzZetaRegularized 0 1).hasDerivAt
  have hGhas : HasDerivAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      ((Real.eulerMascheroniConstant : ℂ) / 2 +
        Complex.log (4 * (Real.pi : ℂ)) / 2) 1 := by
    exact (deriv_Gammaℝ_inv_at_one).symm ▸
      (Complex.hasDerivAt_Gammaℝ_one.differentiableAt.inv
        (Complex.Gammaℝ_one.trans_ne one_ne_zero)).hasDerivAt
  have htotal := ((hasDerivAt_id (x := (1 : ℂ))).sub_const 1).mul
      (hqhas.mul hregHas) |>.add (hqhas.mul hGhas)
  have heq := htotal.deriv
  simp only [Pi.mul_apply, id_eq, sub_self, zero_mul,
    one_mul, add_zero] at heq
  rw [hreg, Complex.cpow_neg_one, Complex.Gammaℝ_one, inv_one] at heq
  convert heq using 1
  ring

/-- Every residue-class L-function has residue `1/q` at one. -/
theorem periodicLFunctionPoleCleared_indicator_one
    (q : ℕ) [NeZero q] (a : ZMod q) :
    periodicLFunctionPoleCleared q
        (fun x : ZMod q => if x = a then 1 else 0) 1 = (q : ℂ)⁻¹ := by
  unfold periodicLFunctionPoleCleared
  simp [Complex.Gammaℝ_one, Complex.cpow_neg_one]

/-- One complete character sum in either variable.  Coprimality of `d`
turns the exceptional frequency into the single residue zero. -/
theorem sum_voronoiCharacter_mul_right (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (a : ZMod q) :
    ∑ b : ZMod q, dfiVoronoiCharacter q d (a * b) =
      if a = 0 then (q : ℂ) else 0 := by
  calc
    ∑ b : ZMod q, dfiVoronoiCharacter q d (a * b) =
        ∑ b : ZMod q, ZMod.stdAddChar (b * (d * a)) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold dfiVoronoiCharacter
      congr 1
      ring
    _ = if d * a = 0 then (q : ℂ) else 0 := by
      simpa using AddChar.sum_mulShift (d * a) (ZMod.isPrimitive_stdAddChar q)
    _ = if a = 0 then (q : ℂ) else 0 := by
      simp only [isUnit_mul_eq_zero_iff hd]

theorem sum_voronoiCharacter_mul_left (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (b : ZMod q) :
    ∑ a : ZMod q, dfiVoronoiCharacter q d (a * b) =
      if b = 0 then (q : ℂ) else 0 := by
  simpa only [mul_comm] using sum_voronoiCharacter_mul_right q d hd b

/-- Orthogonality with an arbitrary weight depending on the first residue. -/
theorem sum_voronoiCharacter_mul_weight_left (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (A : ZMod q → ℂ) :
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * A a = (q : ℂ) * A 0 := by
  calc
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * A a =
      ∑ a : ZMod q,
        (∑ b : ZMod q, dfiVoronoiCharacter q d (a * b)) * A a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
    _ = ∑ a : ZMod q, (if a = 0 then (q : ℂ) else 0) * A a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_voronoiCharacter_mul_right q d hd]
    _ = (q : ℂ) * A 0 := by simp

/-- Orthogonality with an arbitrary weight depending on the second residue. -/
theorem sum_voronoiCharacter_mul_weight_right (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (B : ZMod q → ℂ) :
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * B b = (q : ℂ) * B 0 := by
  rw [Finset.sum_comm]
  simpa only [mul_comm] using sum_voronoiCharacter_mul_weight_left q d hd B

/-- The pole-cleared additive Estermann function has value `1/q` at one. -/
theorem periodicEstermannPoleCleared_voronoiCharacter_one
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    periodicEstermannPoleCleared q (dfiVoronoiCharacter q d) 1 =
      (q : ℂ)⁻¹ := by
  unfold periodicEstermannPoleCleared
  simp_rw [periodicLFunctionPoleCleared_indicator_one]
  have hfactor : (∑ a : ZMod q, ∑ b : ZMod q,
      dfiVoronoiCharacter q d (a * b) * (q : ℂ)⁻¹ * (q : ℂ)⁻¹) =
      (q : ℂ)⁻¹ * (q : ℂ)⁻¹ *
        (∑ a : ZMod q, ∑ b : ZMod q,
          dfiVoronoiCharacter q d (a * b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfactor]
  rw [sum_voronoiCharacter_mul q d hd]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp

/-- Exact simple-pole coefficient of the additive Estermann function.
This is `2q⁻¹(γ-log q)`, with no Laurent coefficient left abstract. -/
theorem periodicEstermannResidueCoeff_voronoiCharacter
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    periodicEstermannResidueCoeff q (dfiVoronoiCharacter q d) =
      2 * (q : ℂ)⁻¹ *
        ((Real.eulerMascheroniConstant : ℂ) - Complex.log (q : ℂ)) := by
  let P : ZMod q → ℂ → ℂ := fun a =>
    periodicLFunctionPoleCleared q (fun x : ZMod q => if x = a then 1 else 0)
  have hPdiff (a : ZMod q) : DifferentiableAt ℂ (P a) 1 :=
    differentiable_periodicLFunctionPoleCleared q _ 1
  have hderiv : HasDerivAt
      (periodicEstermannPoleCleared q (dfiVoronoiCharacter q d))
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          (deriv (P a) 1 * P b 1 + P a 1 * deriv (P b) 1)) 1 := by
    unfold periodicEstermannPoleCleared
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro b _
    convert (((hPdiff a).hasDerivAt.const_mul
      (dfiVoronoiCharacter q d (a * b))).mul (hPdiff b).hasDerivAt) using 1
    ring
  rw [periodicEstermannResidueCoeff, dslope_same, hderiv.deriv]
  have hPone (a : ZMod q) : P a 1 = (q : ℂ)⁻¹ := by
    exact periodicLFunctionPoleCleared_indicator_one q a
  simp_rw [hPone]
  have hsplit :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          (deriv (P a) 1 * (q : ℂ)⁻¹ +
            (q : ℂ)⁻¹ * deriv (P b) 1)) =
        (q : ℂ)⁻¹ *
            (∑ a : ZMod q, ∑ b : ZMod q,
              dfiVoronoiCharacter q d (a * b) * deriv (P a) 1) +
          (q : ℂ)⁻¹ *
            (∑ a : ZMod q, ∑ b : ZMod q,
              dfiVoronoiCharacter q d (a * b) * deriv (P b) 1) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    apply congrArg₂ (fun x y : ℂ => x + y)
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
  rw [hsplit, sum_voronoiCharacter_mul_weight_left q d hd,
    sum_voronoiCharacter_mul_weight_right q d hd]
  have hPzero : deriv (P 0) 1 = (q : ℂ)⁻¹ *
      ((Real.eulerMascheroniConstant : ℂ) - Complex.log (q : ℂ)) := by
    exact deriv_periodicLFunctionPoleCleared_zeroIndicator q
  rw [hPzero]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp
  ring

/-- A literal smooth compactly supported test function on the positive
half-line, as required by DFI Proposition 1.  Explicit support endpoints
make every Mellin convergence and tail assertion derivable. -/
structure DFIVoronoiTestFunction (g : ℝ → ℂ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  smooth : ContDiff ℝ ∞ g
  support_subset : Function.support g ⊆ Set.Icc lower upper

theorem DFIVoronoiTestFunction.continuous
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) : Continuous g :=
  hg.smooth.continuous

theorem DFIVoronoiTestFunction.hasCompactSupport
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) : HasCompactSupport g := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hg.support_subset

/-- Multiplication by `x⁻¹` on the positive support of a DFI test function.
The value at zero is harmless because every DFI test function vanishes on a
neighbourhood of zero.  This weight translates Mellin contours by one unit. -/
noncomputable def dfiVoronoiInvWeight (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * g x

noncomputable def DFIVoronoiTestFunction.invWeight
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    DFIVoronoiTestFunction (dfiVoronoiInvWeight g) := by
  refine ⟨hg.lower, hg.upper, hg.lower_pos, hg.lower_le_upper, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      have hEventually : dfiVoronoiInvWeight g =ᶠ[nhds (0 : ℝ)] 0 := by
        filter_upwards [Iio_mem_nhds hg.lower_pos] with y hy
        have hgy : g y = 0 := by
          by_contra hne
          exact (not_le_of_gt hy) (hg.support_subset hne).1
        simp [dfiVoronoiInvWeight, hgy]
      exact contDiffAt_const.congr_of_eventuallyEq hEventually
    · have hCast : ContDiffAt ℝ ∞ (fun y : ℝ ↦ (y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt
      have hCastNe : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      exact (hCast.inv hCastNe).mul hg.smooth.contDiffAt
  · intro x hx
    apply hg.support_subset
    intro hgx
    exact hx (by simp [dfiVoronoiInvWeight, hgx])

/-- The inverse source weight translates the Mellin transform exactly one
unit to the right. -/
theorem DFIVoronoiTestFunction.mellin_invWeight_add_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (z : ℂ) :
    mellin (dfiVoronoiInvWeight g) (z + 1) = mellin g z := by
  unfold mellin
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show z + 1 - 1 = z by ring]
    rw [show z - 1 = z + (-1 : ℂ) by ring]
    rw [Complex.cpow_add _ _ hxC, Complex.cpow_neg_one]
    simp only [dfiVoronoiInvWeight]
    ring
  · have hgx : g x = 0 := by
      by_contra hne
      have hs := hg.support_subset hne
      exact hx (hg.lower_pos.trans_le hs.1)
    simp [dfiVoronoiInvWeight, hgx]

/-- Repeated multiplication by the inverse source variable.  This is the
Mellin-coordinate implementation of the repeated integration by parts used
to truncate the Bessel transforms in DFI equation (29). -/
noncomputable def dfiVoronoiInvWeightIterate :
    ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g)

@[simp]
theorem dfiVoronoiInvWeightIterate_zero (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate 0 g = g := rfl

@[simp]
theorem dfiVoronoiInvWeightIterate_succ (k : ℕ) (g : ℝ → ℂ) :
    dfiVoronoiInvWeightIterate (k + 1) g =
      dfiVoronoiInvWeight (dfiVoronoiInvWeightIterate k g) := rfl

/-- Every repeated inverse weight remains a smooth positive compactly
supported Voronoi test function with the original support endpoints. -/
noncomputable def DFIVoronoiTestFunction.invWeightIterate
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    DFIVoronoiTestFunction (dfiVoronoiInvWeightIterate k g) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      simpa [dfiVoronoiInvWeightIterate] using ih.invWeight

/-- `k` repeated inverse weights translate the Mellin transform exactly
`k` units to the right. -/
theorem DFIVoronoiTestFunction.mellin_invWeightIterate_add_nat
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) (z : ℂ) :
    mellin (dfiVoronoiInvWeightIterate k g) (z + k) = mellin g z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := (hg.invWeightIterate k).mellin_invWeight_add_one (z + k)
      rw [show z + (k + 1 : ℕ) = (z + k) + 1 by push_cast; ring]
      rw [dfiVoronoiInvWeightIterate_succ, hstep, ih]

/-- The logarithmic-coordinate Mellin kernel attached to a DFI test
function on the vertical line `Re s = σ`. -/
noncomputable def dfiVoronoiMellinKernel
    (σ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * g (Real.exp (-u))

theorem DFIVoronoiTestFunction.contDiff_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    ContDiff ℝ ∞ (dfiVoronoiMellinKernel σ g) := by
  have hWeight : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp (-σ * u) : ℂ)) := by
    have hInner : ContDiff ℝ ∞ (fun u : ℝ => -σ * u) :=
      contDiff_const.mul contDiff_id
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp hInner)
  have hArg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := by
    fun_prop
  exact hWeight.mul (hg.smooth.comp hArg)

theorem DFIVoronoiTestFunction.hasCompactSupport_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    HasCompactSupport (dfiVoronoiMellinKernel σ g) := by
  have hUpperPos : 0 < hg.upper := hg.lower_pos.trans_le hg.lower_le_upper
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log hg.upper) (-Real.log hg.lower)))
  intro u hu
  have hgZero : g (Real.exp (-u)) = 0 := by
    by_contra hne
    have hs := hg.support_subset hne
    apply hu
    rw [Set.mem_Icc]
    constructor
    · have hlog : -u ≤ Real.log hg.upper := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hUpperPos]
        exact hs.2
      linarith
    · have hlog : Real.log hg.lower ≤ -u := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hg.lower_pos]
        exact hs.1
      linarith
  simp [dfiVoronoiMellinKernel, hgZero]

/-- The DFI logarithmic Mellin kernel as a Schwartz function. -/
noncomputable def dfiVoronoiMellinKernelSchwartz
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hg.hasCompactSupport_mellinKernel σ).toSchwartzMap
    (hg.contDiff_mellinKernel σ)

@[simp]
theorem DFIVoronoiTestFunction.mellinKernelSchwartz_apply
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    dfiVoronoiMellinKernelSchwartz hg σ u =
      dfiVoronoiMellinKernel σ g u := rfl

theorem DFIVoronoiTestFunction.mellin_eq_fourier_mellinKernel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    mellin g ((σ : ℂ) + (u : ℂ) * I) =
      𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
        (u / (2 * Real.pi)) := by
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, zero_add, mul_one, neg_mul]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (u / (2 * Real.pi)))
  funext v
  simp [dfiVoronoiMellinKernel]

/-- A compactly supported smooth DFI test function has an integrable Mellin
transform on every complete vertical line.  This is the exact analytic
hypothesis needed by Mathlib's Mellin inversion theorem. -/
theorem DFIVoronoiTestFunction.verticalIntegrable_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    VerticalIntegrable (mellin g) σ := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
  have hFourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hScaled : Integrable
      (fun u : ℝ =>
        𝓕 (dfiVoronoiMellinKernelSchwartz hg σ) (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right' (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  exact (hg.mellin_eq_fourier_mellinKernel σ u).symm

/-- Quadratic polynomial growth is integrable against the Mellin transform
of a DFI test function on every vertical line. -/
theorem DFIVoronoiTestFunction.integrable_sqWeight_norm_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    Integrable (fun u : ℝ =>
      (1 + |u|) ^ 2 * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (dfiVoronoiMellinKernelSchwartz hg σ)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hcOne : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have h0 : Integrable (fun ξ : ℝ => ‖F ξ‖) := F.integrable.norm
  have h1 : Integrable (fun ξ : ℝ => |ξ| * ‖F ξ‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul volume 1
  have h2 : Integrable (fun ξ : ℝ => |ξ| ^ 2 * ‖F ξ‖) := by
    simpa [Real.norm_eq_abs] using F.integrable_pow_mul volume 2
  have hPoly : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ 2 * ‖F ξ‖) := by
    have hSum := h0.add ((h1.const_mul 2).add h2)
    convert hSum using 1
    funext ξ
    simp only [Pi.add_apply]
    ring
  have hScaled : Integrable (fun u : ℝ =>
      (1 + |u / c|) ^ 2 * ‖F (u / c)‖) := by
    simpa [div_eq_mul_inv] using
      hPoly.comp_mul_right' (show c⁻¹ ≠ 0 by positivity)
  have hDom : Integrable (fun u : ℝ =>
      c ^ 2 * ((1 + |u / c|) ^ 2 * ‖F (u / c)‖)) :=
    hScaled.const_mul (c ^ 2)
  have hTargetMeas : AEStronglyMeasurable (fun u : ℝ =>
      (1 + |u|) ^ 2 * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by
    have hCont : Continuous (fun u : ℝ =>
        (1 + |u|) ^ 2 * ‖F (u / c)‖) := by
      fun_prop
    apply hCont.aestronglyMeasurable.congr
    filter_upwards with u
    rw [hg.mellin_eq_fourier_mellinKernel σ u]
  apply hDom.mono' hTargetMeas
  filter_upwards with u
  have hAbsDiv : |u / c| = |u| / c := by
    rw [abs_div, abs_of_pos hc]
  have hLinear : 1 + |u| ≤ c * (1 + |u / c|) := by
    rw [hAbsDiv]
    field_simp
    simpa [add_comm] using add_le_add_right hcOne |u|
  have hSq : (1 + |u|) ^ 2 ≤ c ^ 2 * (1 + |u / c|) ^ 2 := by
    simpa [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hLinear 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  simpa [F, c, mul_assoc] using
    mul_le_mul_of_nonneg_right hSq (norm_nonneg (F (u / c)))

theorem DFIVoronoiTestFunction.eventuallyEq_zero_atTop
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    g =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop hg.upper] with x hx
  by_contra hne
  have hs := hg.support_subset hne
  exact (not_lt_of_ge hs.2) hx

theorem DFIVoronoiTestFunction.eventuallyEq_zero_atZero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0)) g 0 := by
  have hnear : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < hg.lower :=
    isOpen_Iio.mem_nhds hg.lower_pos
  have hnear' : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < hg.lower :=
    hnear.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear'] with x hx
  by_contra hne
  have hs := hg.support_subset hne
  exact (not_lt_of_ge hs.1) hx

theorem DFIVoronoiTestFunction.isBigO_atTop
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (a : ℝ) :
    g =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-a)) atTop).congr'
    hg.eventuallyEq_zero_atTop.symm EventuallyEq.rfl

theorem DFIVoronoiTestFunction.isBigO_atZero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (b : ℝ) :
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0)) g
      (fun x : ℝ => x ^ (-b)) := by
  exact (Asymptotics.isBigO_zero (fun x : ℝ => x ^ (-b))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr'
    hg.eventuallyEq_zero_atZero.symm EventuallyEq.rfl

theorem DFIVoronoiTestFunction.mellinConvergent
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    MellinConvergent g (σ : ℂ) := by
  exact mellinConvergent_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (σ + 1)) (by simp)
    (hg.isBigO_atZero (σ - 1)) (by simp)

/-- Pointwise Mellin inversion for the exact DFI source test class, with
all convergence and vertical-integrability hypotheses discharged. -/
theorem DFIVoronoiTestFunction.mellinInversion
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin g) x = g x := by
  exact mellinInv_mellin_eq σ g hx (hg.mellinConvergent σ)
    (hg.verticalIntegrable_mellin σ) hg.continuous.continuousAt

/-- Every individual term in the right-line Mellin expansion is integrable;
the oscillatory Dirichlet factor has constant norm on a vertical line. -/
theorem DFIVoronoiTestFunction.integrable_periodicDivisorMellinTerm
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) (Φ : ZMod q → ℂ) (c : ℝ) (n : ℕ) :
    Integrable (periodicDivisorMellinTerm q Φ g c n) := by
  unfold periodicDivisorMellinTerm
  apply (hg.verticalIntegrable_mellin c).bdd_mul
      (c := ‖LSeries.term (periodicDivisorCoeff q Φ) (c : ℂ) n‖)
  · by_cases hn : n = 0
    · subst n
      simpa [LSeries.term_zero] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _u : ℝ => (0 : ℂ)))
    · simp_rw [LSeries.term_of_ne_zero hn]
      have hBase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hExponent : Continuous (fun u : ℝ =>
          (c : ℂ) + (u : ℂ) * I) := by fun_prop
      have hPow : Continuous (fun u : ℝ =>
          (n : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)) :=
        hExponent.const_cpow (Or.inl hBase)
      exact (continuous_const.div hPow (fun _u =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hBase))).aestronglyMeasurable
  · filter_upwards with u
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

theorem DFIVoronoiTestFunction.integral_norm_periodicDivisorMellinTerm
    (g : ℝ → ℂ)
    (q : ℕ) (Φ : ZMod q → ℂ) (c : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖periodicDivisorMellinTerm q Φ g c n u‖) =
      ‖LSeries.term (periodicDivisorCoeff q Φ) (c : ℂ) n‖ *
        ∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  unfold periodicDivisorMellinTerm
  rw [norm_mul]
  congr 1
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

/-- Absolute summability of the norms of all right-line Mellin terms.  This
is the complete Tonelli/Fubini condition used by the Voronoi entry theorem. -/
theorem DFIVoronoiTestFunction.summable_integral_norm_periodicDivisorMellinTerm
    (g : ℝ → ℂ)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖periodicDivisorMellinTerm q Φ g c n u‖) := by
  have hCoeff : LSeriesSummable (periodicDivisorCoeff q Φ) (c : ℂ) :=
    periodicDivisorCoeff_LSeriesSummable q Φ (by simpa using hc)
  have hNorm : Summable (fun n : ℕ =>
      ‖LSeries.term (periodicDivisorCoeff q Φ) (c : ℂ) n‖) :=
    summable_norm_iff.mpr hCoeff
  have hMul := hNorm.mul_right
    (∫ u : ℝ, ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖)
  apply hMul.congr
  intro n
  exact (integral_norm_periodicDivisorMellinTerm g q Φ c n).symm

/-- Absolute integrability of the full Estermann--Mellin integrand on the
right contour.  Absolute convergence of the periodic divisor series gives
a bound uniform in the ordinate. -/
theorem DFIVoronoiTestFunction.integrable_periodicEstermann_mul_mellin_right
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) {c : ℝ} (hc : 1 < c) :
    Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((c : ℂ) + (u : ℂ) * I) *
        mellin g ((c : ℂ) + (u : ℂ) * I)) := by
  let B : ℝ := ∑' n : ℕ,
    ‖LSeries.term (periodicDivisorCoeff q Φ) (c : ℂ) n‖
  apply (hg.verticalIntegrable_mellin c).bdd_mul (c := B)
  · have hCont : Continuous (fun u : ℝ =>
        periodicEstermann q Φ ((c : ℂ) + (u : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hne : ((c : ℂ) + (u : ℂ) * I) ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          mul_one, sub_zero, add_zero, one_re] at hre
        linarith
      exact (differentiableAt_periodicEstermann q Φ hne).continuousAt.comp_of_eq
        (by fun_prop) rfl
    exact hCont.aestronglyMeasurable
  · filter_upwards with u
    have hsu : 1 < (((c : ℂ) + (u : ℂ) * I).re) := by
      simpa using hc
    rw [periodicEstermann_eq_LSeries q Φ hsu]
    have hCoeff : LSeriesSummable (periodicDivisorCoeff q Φ) (c : ℂ) :=
      periodicDivisorCoeff_LSeriesSummable q Φ (by simpa using hc)
    have hCoeffU : LSeriesSummable (periodicDivisorCoeff q Φ)
        ((c : ℂ) + (u : ℂ) * I) :=
      hCoeff.of_re_le_re (by simp)
    unfold LSeries B
    calc
      ‖∑' n : ℕ, LSeries.term (periodicDivisorCoeff q Φ)
          ((c : ℂ) + (u : ℂ) * I) n‖ ≤
          ∑' n : ℕ, ‖LSeries.term (periodicDivisorCoeff q Φ)
            ((c : ℂ) + (u : ℂ) * I) n‖ :=
        norm_tsum_le_tsum_norm hCoeffU.norm
      _ = ∑' n : ℕ,
          ‖LSeries.term (periodicDivisorCoeff q Φ) (c : ℂ) n‖ := by
        apply tsum_congr
        intro n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
        simp

/-- Absolute integrability of the source left contour `Re s = -1/2`.
The Estermann functional equation gives quadratic growth on the reflected
line, while compact support gives arbitrary polynomial Mellin decay. -/
theorem DFIVoronoiTestFunction.integrable_periodicEstermann_mul_mellin_left
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        mellin g ((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
  let d : ℝ := -(1 / 2 : ℝ)
  suffices hResult : Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) *
        mellin g ((d : ℂ) + (u : ℂ) * I)) by
    simpa [d] using hResult
  obtain ⟨C, hC, hDual⟩ :=
    periodicEstermannDual_three_half_sub_mul_I_bound q Φ
  have hWeighted := hg.integrable_sqWeight_norm_mellin d
  have hDom : Integrable (fun u : ℝ =>
      C * ((1 + |u|) ^ 2 *
        ‖mellin g ((d : ℂ) + (u : ℂ) * I)‖)) :=
    hWeighted.const_mul C
  have hMellinCont : Continuous (fun u : ℝ =>
      mellin g ((d : ℂ) + (u : ℂ) * I)) := by
    have hFourier : Continuous (fun u : ℝ =>
        𝓕 (dfiVoronoiMellinKernelSchwartz hg d)
          (u / (2 * Real.pi))) := by
      fun_prop
    apply hFourier.congr
    intro u
    exact (hg.mellin_eq_fourier_mellinKernel d u).symm
  have hEstCont : Continuous (fun u : ℝ =>
      periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hne : ((d : ℂ) + (u : ℂ) * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [d] at hre
    exact (differentiableAt_periodicEstermann q Φ hne).continuousAt.comp_of_eq
      (by fun_prop) rfl
  apply hDom.mono' (hEstCont.mul hMellinCont).aestronglyMeasurable
  filter_upwards with u
  have hReflect := periodicEstermann_leftLine_reflection q Φ
    (d := d) (u := u) (by norm_num [d])
  have hBound : ‖periodicEstermann q Φ
      ((d : ℂ) + (u : ℂ) * I)‖ ≤
      C * (1 + |u|) ^ 2 := by
    rw [hReflect]
    convert hDual u using 1
    norm_num [d]
  change ‖periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) *
      mellin g ((d : ℂ) + (u : ℂ) * I)‖ ≤ _
  rw [norm_mul]
  calc
    ‖periodicEstermann q Φ
          ((d : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((d : ℂ) + (u : ℂ) * I)‖ ≤
        (C * (1 + |u|) ^ 2) *
          ‖mellin g ((d : ℂ) + (u : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hBound (norm_nonneg _)
    _ = C * ((1 + |u|) ^ 2 *
        ‖mellin g ((d : ℂ) + (u : ℂ) * I)‖) := by ring

/-- For the source test class, Mellin differentiation at one has no
remaining convergence premise. -/
theorem DFIVoronoiTestFunction.mellin_hasDerivAt_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    HasDerivAt (mellin g) (mellin (fun x : ℝ => Real.log x • g x) 1) 1 := by
  exact (mellin_hasDerivAt_of_isBigO_rpow (s := (1 : ℂ)) (a := (2 : ℝ))
    (b := (0 : ℝ))
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (2 : ℝ)) (by norm_num)
    (hg.isBigO_atZero (0 : ℝ)) (by norm_num)).2

theorem mellin_apply_one (g : ℝ → ℂ) :
    mellin g 1 = ∫ x : ℝ in Set.Ioi 0, g x := by
  simp [mellin]

theorem mellin_log_smul_apply_one (g : ℝ → ℂ) :
    mellin (fun x : ℝ => Real.log x • g x) 1 =
      ∫ x : ℝ in Set.Ioi 0, (Real.log x : ℂ) * g x := by
  simp [mellin, smul_eq_mul]

/-- The complete logarithmic main term in DFI Proposition 1. -/
noncomputable def dfiVoronoiMainTerm (q : ℕ) (g : ℝ → ℂ) : ℂ :=
  (q : ℂ)⁻¹ * ∫ x : ℝ in Set.Ioi 0,
    ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)) * g x

/-- The two Laurent coefficients assemble to the literal logarithmic
integral in Proposition 1. -/
theorem dfiVoronoi_laurent_mainTerm
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d)
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    periodicEstermannPoleCleared q (dfiVoronoiCharacter q d) 1 *
          deriv (mellin g) 1 +
        periodicEstermannResidueCoeff q (dfiVoronoiCharacter q d) *
          mellin g 1 = dfiVoronoiMainTerm q g := by
  rw [periodicEstermannPoleCleared_voronoiCharacter_one q d hd,
    periodicEstermannResidueCoeff_voronoiCharacter q d hd,
    hg.mellin_hasDerivAt_one.deriv]
  rw [mellin_log_smul_apply_one g, mellin_apply_one g]
  unfold dfiVoronoiMainTerm
  have hlog : IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * g x) (Set.Ioi 0) := by
    have hc := (mellin_hasDerivAt_of_isBigO_rpow (s := (1 : ℂ)) (a := (2 : ℝ))
      (b := (0 : ℝ))
      (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
      (hg.isBigO_atTop (2 : ℝ)) (by norm_num)
      (hg.isBigO_atZero (0 : ℝ)) (by norm_num)).1
    simpa [MellinConvergent, smul_eq_mul] using hc
  have hgInt : IntegrableOn g (Set.Ioi 0) :=
    (hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport).integrableOn
  rw [show (∫ x : ℝ in Set.Ioi 0,
      ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * g x) =
      (∫ x : ℝ in Set.Ioi 0, (Real.log x : ℂ) * g x) +
        (2 * (Real.eulerMascheroniConstant : ℂ) -
          2 * Complex.log (q : ℂ)) *
          (∫ x : ℝ in Set.Ioi 0, g x) by
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_add hlog
      (hgInt.const_mul (2 * (Real.eulerMascheroniConstant : ℂ) -
        2 * Complex.log (q : ℂ)))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring]
  ring

end RiemannZeta.GuthMaynard
