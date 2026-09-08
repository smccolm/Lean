import RiemannZeta.GuthMaynard.HeathBrown
import RiemannZeta.GuthMaynard.QuantitativeSmoothReflection
import RiemannZeta.GuthMaynard.ClassicalLargeValues
import RiemannZeta.GuthMaynard.TerminalTypeI
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.Order.Floor.Div

open Complex Finset Filter MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace RiemannZeta.GuthMaynard

/-- A fixed Guth--Maynard cutoff has a global Lipschitz constant.  Compact
support is essential here: it turns the local `C¹` control supplied by the
cutoff structure into one constant that is independent of every analytic
scale used in the Heath--Brown recurrence. -/
theorem GMSmoothCutoff.exists_lipschitzWith
    (cutoff : GMSmoothCutoff) :
    ∃ K : NNReal, LipschitzWith K cutoff.toFun := by
  have hcompact : HasCompactSupport cutoff.toFun :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc cutoff.support
  exact cutoff.smooth.lipschitzWith_of_hasCompactSupport hcompact (by simp)

/-- The cutoff-squared weights on a dyadic lattice have uniformly bounded
discrete total variation.  The bound is independent of the lattice scale;
this is the finite Abel input for the nonstationary displacement bins. -/
theorem GMSmoothCutoff.exists_traceWeight_variation_bound
    (cutoff : GMSmoothCutoff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℕ), 0 < Q →
      (∑ m ∈ Finset.range Q,
        |cutoff (((Q + 1 + (m + 1) : ℕ) : ℝ) / Q) ^ 2 -
          cutoff (((Q + 1 + m : ℕ) : ℝ) / Q) ^ 2|) ≤ K := by
  obtain ⟨K₀, hLip⟩ := cutoff.exists_lipschitzWith
  refine ⟨2 * ((K₀ : ℝ) + 1), by positivity, ?_⟩
  intro Q hQ
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hstep (m : ℕ) :
      |cutoff (((Q + 1 + (m + 1) : ℕ) : ℝ) / Q) ^ 2 -
          cutoff (((Q + 1 + m : ℕ) : ℝ) / Q) ^ 2| ≤
        2 * (K₀ : ℝ) / Q := by
    let x : ℝ := (((Q + 1 + (m + 1) : ℕ) : ℝ) / Q)
    let y : ℝ := (((Q + 1 + m : ℕ) : ℝ) / Q)
    have hxy : |cutoff x - cutoff y| ≤ (K₀ : ℝ) * |x - y| := by
      simpa only [Real.dist_eq] using hLip.dist_le_mul x y
    have hx0 : 0 ≤ cutoff x := cutoff.nonneg x
    have hy0 : 0 ≤ cutoff y := cutoff.nonneg y
    have hx1 : cutoff x ≤ 1 := cutoff.bounded x
    have hy1 : cutoff y ≤ 1 := cutoff.bounded y
    have hsum : |cutoff x + cutoff y| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hx0 hy0)]
      linarith
    have hfactor :
        |cutoff x ^ 2 - cutoff y ^ 2| =
          |cutoff x - cutoff y| * |cutoff x + cutoff y| := by
      rw [sq_sub_sq, abs_mul]
      ring
    have hdist : |x - y| = 1 / Q := by
      dsimp only [x, y]
      rw [abs_of_nonneg]
      · push_cast
        field_simp
        ring
      · rw [sub_nonneg]
        gcongr
        omega
    rw [hfactor]
    calc
      |cutoff x - cutoff y| * |cutoff x + cutoff y| ≤
          ((K₀ : ℝ) * |x - y|) * 2 := by gcongr
      _ = 2 * (K₀ : ℝ) / Q := by rw [hdist]; ring
  calc
    (∑ m ∈ Finset.range Q,
        |cutoff (((Q + 1 + (m + 1) : ℕ) : ℝ) / Q) ^ 2 -
          cutoff (((Q + 1 + m : ℕ) : ℝ) / Q) ^ 2|) ≤
        ∑ _m ∈ Finset.range Q, 2 * (K₀ : ℝ) / Q := by
      apply Finset.sum_le_sum
      intro m hm
      exact hstep m
    _ = (Q : ℝ) * (2 * (K₀ : ℝ) / Q) := by simp
    _ = 2 * (K₀ : ℝ) := by field_simp
    _ ≤ 2 * ((K₀ : ℝ) + 1) := by linarith

/-- Finite Abel summation on an initial range, with the terminal weight
placed one step beyond the summation interval. -/
theorem heathBrown_weighted_range_eq_endpoint_sub_differences
    (w a : ℕ → ℂ) (L : ℕ) :
    (∑ m ∈ Finset.range L, w m * a m) =
      w L * (∑ m ∈ Finset.range L, a m) -
        ∑ j ∈ Finset.range L,
          (w (j + 1) - w j) * (∑ m ∈ Finset.range (j + 1), a m) := by
  induction L with
  | zero => simp
  | succ L ih =>
      simp only [Finset.sum_range_succ, ih]
      ring

/-- Norm form of the preceding finite Abel identity. -/
theorem heathBrown_norm_weighted_range_le_of_partial_sum
    (w a : ℕ → ℂ) (L : ℕ) (R W D : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j < L, ‖∑ m ∈ Finset.range (j + 1), a m‖ ≤ R)
    (hendpoint : ‖w L‖ ≤ W)
    (hdifference :
      (∑ j ∈ Finset.range L, ‖w (j + 1) - w j‖) ≤ D) :
    ‖∑ m ∈ Finset.range L, w m * a m‖ ≤ (W + D) * R := by
  have hpartialL : ‖∑ m ∈ Finset.range L, a m‖ ≤ R := by
    by_cases hL : L = 0
    · subst L
      simpa using hR
    · have hpred : L = (L - 1) + 1 := by omega
      rw [hpred]
      exact hpartial (L - 1) (by omega)
  have hW : 0 ≤ W := (norm_nonneg (w L)).trans hendpoint
  rw [heathBrown_weighted_range_eq_endpoint_sub_differences]
  calc
    ‖w L * (∑ m ∈ Finset.range L, a m) -
        ∑ j ∈ Finset.range L,
          (w (j + 1) - w j) * (∑ m ∈ Finset.range (j + 1), a m)‖ ≤
      ‖w L * (∑ m ∈ Finset.range L, a m)‖ +
        ‖∑ j ∈ Finset.range L,
          (w (j + 1) - w j) * (∑ m ∈ Finset.range (j + 1), a m)‖ :=
      norm_sub_le _ _
    _ ≤ W * R +
        ∑ j ∈ Finset.range L, ‖w (j + 1) - w j‖ * R := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hendpoint hpartialL (norm_nonneg _) hW
      · calc
          ‖∑ j ∈ Finset.range L,
              (w (j + 1) - w j) *
                (∑ m ∈ Finset.range (j + 1), a m)‖ ≤
            ∑ j ∈ Finset.range L,
              ‖(w (j + 1) - w j) *
                (∑ m ∈ Finset.range (j + 1), a m)‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range L, ‖w (j + 1) - w j‖ * R := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left
              (hpartial j (Finset.mem_range.mp hj)) (norm_nonneg _)
    _ = W * R +
        (∑ j ∈ Finset.range L, ‖w (j + 1) - w j‖) * R := by
      rw [Finset.sum_mul]
    _ ≤ W * R + D * R := by gcongr
    _ = (W + D) * R := by ring

/-!
# Smooth reflection entry for the Heath--Brown moment

This file connects the sharp coefficient-one blocks in Heath--Brown's
difference-set moment to the exact cutoff-squared Poisson kernel used in the
Guth--Maynard trace argument.  The passage is a genuine positive-kernel
majorant: the three source pieces lie in cutoff plateaux, while the enlarged
smooth polynomial retains every additional coefficient.  No sharp block is
identified with a smooth block outside that proved majorant.
-/

/-- The unrestricted cutoff-squared polynomial at scale `Q`.  Writing it as
a `gmSmoothDirichletPoly` makes its coefficient sequence explicit; its
continuous interpolation is exactly `gmTraceKernel`. -/
noncomputable def heathBrownTracePolynomial
    (cutoff : GMSmoothCutoff) (Q : ℕ) (t : ℝ) : ℂ :=
  gmSmoothDirichletPoly cutoff Q
    (fun n => (cutoff ((n : ℝ) / Q) : ℂ)) t

/-- Ordered-difference second moment of the unrestricted cutoff-squared
polynomial. -/
noncomputable def heathBrownTraceMoment
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖heathBrownTracePolynomial cutoff Q (t - u)‖ ^ 2

/-- A full cutoff-squared polynomial is the source polynomial with the
literal nonnegative coefficient `w(n/Q)^2`. -/
theorem heathBrownTracePolynomial_eq_source
    (cutoff : GMSmoothCutoff) (Q : ℕ) (t : ℝ) :
    heathBrownTracePolynomial cutoff Q t =
      sourceDirichletPoly Q
        (fun n => ((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) t := by
  unfold heathBrownTracePolynomial gmSmoothDirichletPoly sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- Exact finite Abel form of the cutoff-squared trace polynomial. -/
theorem heathBrownTracePolynomial_eq_weighted_range
    (cutoff : GMSmoothCutoff) (Q : ℕ) (t : ℝ) (hQ : 0 < Q) :
    heathBrownTracePolynomial cutoff Q t =
      ∑ m ∈ Finset.range Q,
        ((cutoff (((Q + 1 + m : ℕ) : ℝ) / Q) ^ 2 : ℝ) : ℂ) *
          unitaryPhase (logarithmicPhase (-t) (Q + 1 + m)) := by
  rw [heathBrownTracePolynomial_eq_source]
  unfold sourceDirichletPoly
  rw [dyadicInterval_eq_Ico_succ, Finset.sum_Ico_eq_sum_range]
  have hlength : 2 * Q + 1 - (Q + 1) = Q := by omega
  rw [hlength]
  apply Finset.sum_congr rfl
  intro m hm
  have hn : 0 < Q + 1 + m := by omega
  have hexp : ((t : ℂ) * I) = -((-t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexp, ← unitaryPhase_logarithmicPhase_eq_cpow (-t) (Q + 1 + m) hn]
  congr 2
  all_goals push_cast
  all_goals ring

/-- Reversing the logarithmic frequency conjugates every finite prefix, so
its norm depends only on the absolute frequency. -/
theorem norm_logarithmicPhase_prefix_neg_eq_abs
    (A L : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.range L,
        unitaryPhase (logarithmicPhase (-t) (A + 1 + m))‖ =
      ‖∑ m ∈ Finset.range L,
        unitaryPhase (logarithmicPhase |t| (A + 1 + m))‖ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have hconj :
        (∑ m ∈ Finset.range L,
            unitaryPhase (logarithmicPhase (-t) (A + 1 + m))) =
          star (∑ m ∈ Finset.range L,
            unitaryPhase (logarithmicPhase t (A + 1 + m))) := by
      change (∑ m ∈ Finset.range L,
          unitaryPhase (logarithmicPhase (-t) (A + 1 + m))) =
        starRingEnd ℂ (∑ m ∈ Finset.range L,
          unitaryPhase (logarithmicPhase t (A + 1 + m)))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m hm
      unfold unitaryPhase logarithmicPhase
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal,
        Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    rw [hconj, norm_star]
  · rw [abs_of_nonpos ht]

/-- The terminal Abel weight lies just to the right of the cutoff support. -/
theorem gmSmoothCutoff_terminal_traceWeight_zero
    (cutoff : GMSmoothCutoff) (Q : ℕ) (hQ : 0 < Q) :
    cutoff (((Q + 1 + Q : ℕ) : ℝ) / Q) ^ 2 = 0 := by
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx : 2 < (((Q + 1 + Q : ℕ) : ℝ) / Q) := by
    rw [lt_div_iff₀ hQReal]
    push_cast
    linarith
  have hcutoff : cutoff (((Q + 1 + Q : ℕ) : ℝ) / Q) = 0 := by
    by_contra hne
    have hsupp : (((Q + 1 + Q : ℕ) : ℝ) / Q) ∈
        Function.support cutoff.toFun := hne
    have hIcc := cutoff.support hsupp
    exact (not_lt_of_ge hIcc.2) hx
  rw [hcutoff, zero_pow]
  norm_num

/-- Uniform nonstationary estimate for the actual cutoff-squared trace
polynomial.  This is the missing near-bin input in the source recurrence:
the constant depends only on the fixed cutoff, while the decay is `Q/|t|`.
-/
theorem exists_norm_heathBrownTracePolynomial_le_div
    (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (t : ℝ), 0 < Q →
      1 ≤ |t| → |t| ≤ (Q : ℝ) →
      ‖heathBrownTracePolynomial cutoff Q t‖ ≤
        C * (Q : ℝ) / |t| := by
  obtain ⟨K, hK, hvariation⟩ :=
    cutoff.exists_traceWeight_variation_bound
  refine ⟨(K + 1) * (6 * Real.pi), by positivity, ?_⟩
  intro Q t hQ htOne htQ
  let w : ℕ → ℂ := fun m =>
    ((cutoff (((Q + 1 + m : ℕ) : ℝ) / Q) ^ 2 : ℝ) : ℂ)
  let a : ℕ → ℂ := fun m =>
    unitaryPhase (logarithmicPhase (-t) (Q + 1 + m))
  have hR : 0 ≤ 6 * Real.pi * (Q : ℝ) / |t| := by positivity
  have hpartial : ∀ j < Q,
      ‖∑ m ∈ Finset.range (j + 1), a m‖ ≤
        6 * Real.pi * (Q : ℝ) / |t| := by
    intro j hj
    rw [norm_logarithmicPhase_prefix_neg_eq_abs Q (j + 1) t]
    exact norm_logarithmicPhase_prefix_le_div Q (j + 1) |t| hQ
      (by omega) htOne htQ
  have hendpoint : ‖w Q‖ ≤ 0 := by
    have hz := gmSmoothCutoff_terminal_traceWeight_zero cutoff Q hQ
    dsimp only [w]
    rw [hz]
    simp
  have hdifference :
      (∑ j ∈ Finset.range Q, ‖w (j + 1) - w j‖) ≤ K := by
    simpa only [w, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hvariation Q hQ
  have hAbel := heathBrown_norm_weighted_range_le_of_partial_sum
    w a Q (6 * Real.pi * (Q : ℝ) / |t|) 0 K
    hR hpartial hendpoint hdifference
  rw [heathBrownTracePolynomial_eq_weighted_range cutoff Q t hQ]
  change ‖∑ m ∈ Finset.range Q, w m * a m‖ ≤ _
  calc
    ‖∑ m ∈ Finset.range Q, w m * a m‖ ≤
        (0 + K) * (6 * Real.pi * (Q : ℝ) / |t|) := hAbel
    _ = K * (6 * Real.pi * (Q : ℝ) / |t|) := by ring
    _ ≤ (K + 1) * (6 * Real.pi * (Q : ℝ) / |t|) :=
      mul_le_mul_of_nonneg_right (by linarith) hR
    _ = (K + 1) * (6 * Real.pi) * (Q : ℝ) / |t| := by ring

/-- On a cutoff plateau, the restricted smooth polynomial is exactly the
corresponding sharp finite piece written on its ambient dyadic interval. -/
theorem gmSmoothRestrictedOne_eq_sourceRestrictedOne
    (cutoff : GMSmoothCutoff) (Q : ℕ) (S : Finset ℕ) (t : ℝ)
    (_hS : S ⊆ dyadicInterval Q)
    (hcore : ∀ n ∈ S,
      ((n : ℝ) / Q) ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) :
    gmSmoothDirichletPoly cutoff Q
        (gmRestrictedCoeffs S (fun _ => (1 : ℂ))) t =
      sourceDirichletPoly Q
        (gmRestrictedCoeffs S (fun _ => (1 : ℂ))) t := by
  unfold gmSmoothDirichletPoly sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnS : n ∈ S
  · rw [cutoff.equals_one _ (hcore n hnS)]
    simp [gmRestrictedCoeffs, hnS]
  · simp [gmRestrictedCoeffs, hnS]

/-- Positive-kernel enlargement of one sharp source piece to the complete
cutoff-squared trace polynomial.  This is the exact Jutila majorant entry
needed before applying smooth reflection. -/
theorem gmSmoothRestrictedOne_differenceMoment_le_trace
    (cutoff : GMSmoothCutoff) (Q : ℕ) (S : Finset ℕ) (W : Finset ℝ)
    (hS : S ⊆ dyadicInterval Q)
    (hcore : ∀ n ∈ S,
      ((n : ℝ) / Q) ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖gmSmoothDirichletPoly cutoff Q
          (gmRestrictedCoeffs S (fun _ => (1 : ℂ))) (t - u)‖ ^ 2) ≤
      heathBrownTraceMoment cutoff Q W := by
  let b : ℕ → ℝ := fun n => cutoff ((n : ℝ) / Q) ^ 2
  have hbNonneg : ∀ n ∈ dyadicInterval Q, 0 ≤ b n := by
    intro n hn
    exact sq_nonneg _
  have hcoeff : ∀ n ∈ dyadicInterval Q,
      ‖gmRestrictedCoeffs S (fun _ => (1 : ℂ)) n‖ ≤ b n := by
    intro n hn
    by_cases hnS : n ∈ S
    · have hOne := cutoff.equals_one _ (hcore n hnS)
      simp [gmRestrictedCoeffs, hnS, b, hOne]
    · simp [gmRestrictedCoeffs, hnS, b, sq_nonneg]
  have hMajorant := sourceDirichletPoly_differenceMoment_le_of_norm_le
    Q W (gmRestrictedCoeffs S (fun _ => (1 : ℂ))) b hbNonneg hcoeff
  unfold heathBrownTraceMoment
  simpa only [gmSmoothRestrictedOne_eq_sourceRestrictedOne cutoff Q S _ hS hcore,
    heathBrownTracePolynomial_eq_source, b] using hMajorant

/-- The literal sharp coefficient-one Heath--Brown moment is bounded by
three unrestricted trace moments.  The only loss is the exact factor three
from the source partition and Cauchy--Schwarz. -/
theorem sourceCoefficientOne_differenceMoment_le_three_trace
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (hN : 30 ≤ N) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
      3 * (heathBrownTraceMoment cutoff (gmSourceLeftScale N) W +
        heathBrownTraceMoment cutoff N W +
        heathBrownTraceMoment cutoff (gmSourceRightScale N) W) := by
  have hLeft := gmSmoothRestrictedOne_differenceMoment_le_trace
    cutoff (gmSourceLeftScale N) (gmSourceLeftPiece N) W
    (fun _ hn => gmSourceLeftPiece_mem_dyadic hN hn)
    (fun _ hn => gmSourceLeftPiece_mem_core hN hn)
  have hMiddle := gmSmoothRestrictedOne_differenceMoment_le_trace
    cutoff N (gmSourceMiddlePiece N) W
    (fun _ hn => gmSourceMiddlePiece_mem_dyadic hn)
    (fun _ hn => gmSourceMiddlePiece_mem_core hN hn)
  have hRight := gmSmoothRestrictedOne_differenceMoment_le_trace
    cutoff (gmSourceRightScale N) (gmSourceRightPiece N) W
    (fun _ hn => gmSourceRightPiece_mem_dyadic hN hn)
    (fun _ hn => gmSourceRightPiece_mem_core hN hn)
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W, 3 *
        (‖gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
            (gmRestrictedCoeffs (gmSourceLeftPiece N) (fun _ => (1 : ℂ)))
              (t - u)‖ ^ 2 +
          ‖gmSmoothDirichletPoly cutoff N
            (gmRestrictedCoeffs (gmSourceMiddlePiece N) (fun _ => (1 : ℂ)))
              (t - u)‖ ^ 2 +
          ‖gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
            (gmRestrictedCoeffs (gmSourceRightPiece N) (fun _ => (1 : ℂ)))
              (t - u)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        rw [sourceDirichletPoly_eq_three_gmSmooth cutoff hN
          (fun _ => (1 : ℂ)) (t - u)]
        exact norm_add_add_sq_le_three _ _ _
    _ = 3 *
        ((∑ t ∈ W, ∑ u ∈ W,
            ‖gmSmoothDirichletPoly cutoff (gmSourceLeftScale N)
              (gmRestrictedCoeffs (gmSourceLeftPiece N) (fun _ => (1 : ℂ)))
                (t - u)‖ ^ 2) +
          (∑ t ∈ W, ∑ u ∈ W,
            ‖gmSmoothDirichletPoly cutoff N
              (gmRestrictedCoeffs (gmSourceMiddlePiece N) (fun _ => (1 : ℂ)))
                (t - u)‖ ^ 2) +
          (∑ t ∈ W, ∑ u ∈ W,
            ‖gmSmoothDirichletPoly cutoff (gmSourceRightScale N)
              (gmRestrictedCoeffs (gmSourceRightPiece N) (fun _ => (1 : ℂ)))
                (t - u)‖ ^ 2)) := by
          ring_nf
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ 3 * (heathBrownTraceMoment cutoff (gmSourceLeftScale N) W +
        heathBrownTraceMoment cutoff N W +
        heathBrownTraceMoment cutoff (gmSourceRightScale N) W) := by
      gcongr

/-- Pointwise scale extraction for the cutoff-squared kernel. -/
theorem heathBrown_traceKernel_eq_scaled_phase
    (cutoff : GMSmoothCutoff) (Q n : ℕ) (hQ : 0 < Q) (hn : 0 < n)
    (t : ℝ) :
    (((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) *
        (n : ℂ) ^ ((t : ℂ) * I) =
      (Q : ℂ) ^ ((t : ℂ) * I) *
        gmTraceKernel cutoff t ((n : ℝ) / Q) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : 0 < (n : ℝ) / Q := div_pos hnr hQr
  have hcast : (n : ℂ) = (Q : ℂ) * (((n : ℝ) / Q : ℝ) : ℂ) := by
    have hreal : (n : ℝ) = (Q : ℝ) * ((n : ℝ) / Q) :=
      (mul_div_cancel₀ (n : ℝ) hQr.ne').symm
    calc
      (n : ℂ) = (((n : ℝ) : ℂ)) := by norm_num
      _ = ((((Q : ℝ) * ((n : ℝ) / Q) : ℝ)) : ℂ) :=
        congrArg Complex.ofReal hreal
      _ = (Q : ℂ) * (((n : ℝ) / Q : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  change (((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) *
      ((((Q : ℝ) : ℂ) * (((n : ℝ) / Q : ℝ) : ℂ)) ^
        ((t : ℂ) * I)) = _
  rw [Complex.mul_cpow_ofReal_nonneg hQr.le hratio.le]
  unfold gmTraceKernel
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have harg :
      ((Real.log ((n : ℝ) / Q) : ℝ) : ℂ) * ((t : ℂ) * I) =
        (((t * Real.log ((n : ℝ) / Q) : ℝ)) : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  push_cast
  ring

/-- Exact complete-frequency Poisson formula for the unrestricted smooth
Heath--Brown block.  The unitary physical-scale phase is kept explicit, and
the complete integer series is decomposed into the actual zero mode and the
actual nonzero tail consumed by quantitative smooth reflection. -/
theorem heathBrownTracePolynomial_eq_phase_mul_zero_add_tail
    (cutoff : GMSmoothCutoff) (Q : ℕ) (hQ : 0 < Q) (t : ℝ) :
    heathBrownTracePolynomial cutoff Q t =
      (Q : ℂ) ^ ((t : ℂ) * I) *
        (gmTraceZeroMode cutoff Q t + gmTraceNonzeroTailAt cutoff Q t) := by
  rw [heathBrownTracePolynomial_eq_source]
  unfold sourceDirichletPoly
  calc
    (∑ n ∈ dyadicInterval Q,
        (((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) *
          (n : ℂ) ^ ((t : ℂ) * I)) =
      (Q : ℂ) ^ ((t : ℂ) * I) *
        ∑ n ∈ dyadicInterval Q,
          gmTraceKernel cutoff t ((n : ℝ) / Q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        exact heathBrown_traceKernel_eq_scaled_phase cutoff Q n hQ
          (by rw [dyadicInterval, Finset.mem_Ioc] at hn; omega) t
    _ = (Q : ℂ) ^ ((t : ℂ) * I) *
        ∑' n : ℤ, gmTraceKernel cutoff t ((n : ℝ) / Q) := by
          have hColumn :
              (∑ n : GMColumn Q,
                  gmTraceKernel cutoff t ((n : ℝ) / Q)) =
                ∑ n ∈ dyadicInterval Q,
                  gmTraceKernel cutoff t ((n : ℝ) / Q) := by
            conv_rhs => rw [← Finset.sum_attach]
            rw [Finset.univ_eq_attach (dyadicInterval Q)]
          rw [gmTraceKernel_tsum_eq_column_sum cutoff Q hQ t, hColumn]
    _ = (Q : ℂ) ^ ((t : ℂ) * I) *
        ∑' m : ℤ, gmScaledTraceMode cutoff Q t m := by
          rw [gmTraceKernel_poisson cutoff t (Q : ℝ) (by exact_mod_cast hQ)]
          congr 2
    _ = _ := by
      rw [gmScaledTraceMode_tsum_decompose cutoff Q hQ t]

/-- Norm form of the exact Poisson entry.  The physical-scale phase is
unitary, so only the genuine zero and nonzero Fourier contributions remain. -/
theorem norm_heathBrownTracePolynomial_le_zero_add_tail
    (cutoff : GMSmoothCutoff) (Q : ℕ) (hQ : 0 < Q) (t : ℝ) :
    ‖heathBrownTracePolynomial cutoff Q t‖ ≤
      ‖gmTraceZeroMode cutoff Q t‖ +
        ‖gmTraceNonzeroTailAt cutoff Q t‖ := by
  have hPhase : ‖(Q : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hQ]
    simp
  rw [heathBrownTracePolynomial_eq_phase_mul_zero_add_tail cutoff Q hQ t,
    norm_mul, hPhase, one_mul]
  exact norm_add_le (gmTraceZeroMode cutoff Q t)
    (gmTraceNonzeroTailAt cutoff Q t)

/-- Quantitative reflected bound for the actual smooth polynomial introduced
above.  It composes the complete-frequency Lemma 6.2 theorem with the
separated zero-mode estimate; neither Fourier contribution is omitted. -/
theorem heathBrownTracePolynomial_quantitative_reflection
    (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
        ∀ {T T₀ t : ℝ} {Q : ℕ},
          T_min ≤ T → 0 < Q → (Q : ℝ) ≤ T →
          T ^ ε ≤ T₀ → T₀ ≤ |t| → |t| ≤ 2 * T₀ → |t| ≤ T →
          ‖heathBrownTracePolynomial cutoff Q t‖ ≤
            (Q : ℝ) * C / Real.sqrt T₀ *
                (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
                  ‖gmReflectionDirichletPoly t
                    (gmReflectionLength T ε Q t) u‖) +
              C / T ^ A + (Q : ℝ) * C / T₀ ^ q := by
  intro A ε hA hε
  obtain ⟨C₁, T_min, hC₁, hT_min, hTail⟩ :=
    gmScaledQuantitativeSmoothReflection_native cutoff A ε hA hε
  obtain ⟨C₀, hC₀, hZero⟩ := gmTraceZeroMode_separated_bound cutoff q
  let C : ℝ := max C₁ C₀
  refine ⟨C, T_min, hC₁.trans_le (le_max_left _ _), hT_min, ?_⟩
  intro T T₀ t Q hT hQ hQT hT₀ htLower htDouble htUpper
  have hTrace := norm_heathBrownTracePolynomial_le_zero_add_tail cutoff Q hQ t
  have hZeroAt := hZero Q (show 0 < T₀ by
      have hTOne : 1 ≤ T := hT_min.trans hT
      have hTPow : 0 < T ^ ε := Real.rpow_pos_of_pos (zero_lt_one.trans_le hTOne) ε
      exact hTPow.trans_le hT₀) htLower
  have hTailAt := hTail hT hQ hQT hT₀ htLower htDouble htUpper
  calc
    ‖heathBrownTracePolynomial cutoff Q t‖ ≤
        ‖gmTraceZeroMode cutoff Q t‖ +
          ‖gmTraceNonzeroTailAt cutoff Q t‖ := hTrace
    _ ≤ ((Q : ℝ) * C₀ / T₀ ^ q) +
        ((Q : ℝ) * C₁ / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε Q t) u‖) +
          C₁ / T ^ A) := add_le_add hZeroAt hTailAt
    _ ≤ (Q : ℝ) * C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε Q t) u‖) +
          C / T ^ A + (Q : ℝ) * C / T₀ ^ q := by
      have hTOne : 1 ≤ T := hT_min.trans hT
      have hTPos : 0 < T := zero_lt_one.trans_le hTOne
      have hT₀Pos : 0 < T₀ := by
        exact (Real.rpow_pos_of_pos hTPos ε).trans_le hT₀
      have hIntegral : 0 ≤
          ∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
            ‖gmReflectionDirichletPoly t
              (gmReflectionLength T ε Q t) u‖ := by
        have hH : 0 ≤ gmReflectionHeight T ε :=
          Real.rpow_nonneg hTPos.le _
        exact intervalIntegral.integral_nonneg (by linarith)
          (fun u hu => norm_nonneg _)
      have hCore :
          (Q : ℝ) * C₁ / Real.sqrt T₀ *
              (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
                ‖gmReflectionDirichletPoly t
                  (gmReflectionLength T ε Q t) u‖) ≤
            (Q : ℝ) * C / Real.sqrt T₀ *
              (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
                ‖gmReflectionDirichletPoly t
                  (gmReflectionLength T ε Q t) u‖) := by
        gcongr
        exact le_max_left _ _
      have hErr : C₁ / T ^ A ≤ C / T ^ A := by
        exact div_le_div_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hTPos.le A)
      have hZeroC : (Q : ℝ) * C₀ / T₀ ^ q ≤
          (Q : ℝ) * C / T₀ ^ q := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
          (pow_nonneg hT₀Pos.le q)
      linarith

/-! ## Dyadic resolution of the reflected prefix

The reflected polynomial in Lemma 6.2 is a prefix rather than one of the
project's dyadic polynomials.  The following coefficient sequence keeps the
translation parameter in the coefficients and kills the artificial tail up
to the next power of two.  Its norm is at most one, so every resulting block
is covered by the already proved coefficient-one difference moment.
-/

/-- Unit-bounded coefficients of the translated reflected prefix. -/
noncomputable def heathBrownReflectedPrefixCoeff
    (M : ℕ) (u : ℝ) (n : ℕ) : ℂ :=
  if 0 < n ∧ n ≤ M then (n : ℂ) ^ (-(u : ℂ) * I) else 0

theorem norm_heathBrownReflectedPrefixCoeff_le_one
    (M : ℕ) (u : ℝ) (n : ℕ) :
    ‖heathBrownReflectedPrefixCoeff M u n‖ ≤ 1 := by
  by_cases hn : 0 < n ∧ n ≤ M
  · rw [heathBrownReflectedPrefixCoeff, if_pos hn]
    rw [Complex.norm_natCast_cpow_of_pos hn.1]
    simp
  · simp [heathBrownReflectedPrefixCoeff, hn]

/-- Exact prefix-to-wide-polynomial identity.  The isolated `1` is the
literal `m = 1` term; all indices between `M + 1` and the next power of two
vanish by definition. -/
theorem gmReflectionDirichletPoly_eq_one_add_wide
    (t u : ℝ) {M : ℕ} (hM : 0 < M) :
    gmReflectionDirichletPoly t M u =
      1 + wideDirichletPoly 1 (Nat.clog 2 M)
        (heathBrownReflectedPrefixCoeff M u) t := by
  classical
  let k := Nat.clog 2 M
  let term : ℕ → ℂ := fun n =>
    (n : ℂ) ^ (-((((t + u : ℝ) : ℂ) * I)))
  have hOneMem : 1 ∈ Finset.Icc 1 M := by
    simp only [Finset.mem_Icc]
    omega
  have hSplit :
      (∑ n ∈ Finset.Icc 1 M, term n) =
        term 1 + ∑ n ∈ Finset.Ioc 1 M, term n := by
    rw [Finset.Icc_eq_cons_Ioc]
    · rfl
    · omega
  have hCover : M ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by omega) M
  have hSubset : Finset.Ioc 1 M ⊆ Finset.Ioc 1 (2 ^ k) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hCover⟩
  have hTailZero : ∀ n ∈ Finset.Ioc 1 (2 ^ k),
      n ∉ Finset.Ioc 1 M →
      heathBrownReflectedPrefixCoeff M u n *
          (n : ℂ) ^ (-(t : ℂ) * I) = 0 := by
    intro n hn hnM
    have hnAbove : M < n := by
      have hnData := Finset.mem_Ioc.mp hn
      simp only [Finset.mem_Ioc, not_and_or] at hnM
      omega
    simp [heathBrownReflectedPrefixCoeff, Nat.not_le.mpr hnAbove]
  have hTerm : ∀ n ∈ Finset.Ioc 1 M,
      heathBrownReflectedPrefixCoeff M u n *
          (n : ℂ) ^ (-(t : ℂ) * I) = term n := by
    intro n hn
    have hnPos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
    have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
    rw [heathBrownReflectedPrefixCoeff,
      if_pos ⟨hnPos, (Finset.mem_Ioc.mp hn).2⟩,
      mul_comm, ← Complex.cpow_add _ _ hnNe]
    dsimp only [term]
    congr 2
    push_cast
    ring
  have hWide :
      wideDirichletPoly 1 k (heathBrownReflectedPrefixCoeff M u) t =
        ∑ n ∈ Finset.Ioc 1 M, term n := by
    unfold wideDirichletPoly
    simp only [mul_one]
    calc
      (∑ n ∈ Finset.Ioc 1 (2 ^ k),
          heathBrownReflectedPrefixCoeff M u n *
            (n : ℂ) ^ (-(t : ℂ) * I)) =
          ∑ n ∈ Finset.Ioc 1 M,
            heathBrownReflectedPrefixCoeff M u n *
              (n : ℂ) ^ (-(t : ℂ) * I) :=
        (Finset.sum_subset hSubset hTailZero).symm
      _ = ∑ n ∈ Finset.Ioc 1 M, term n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hTerm n hn
  unfold gmReflectionDirichletPoly
  rw [hSplit]
  have hTermOne : term 1 = 1 := by simp [term]
  rw [hTermOne]
  exact congrArg (fun z : ℂ => 1 + z) hWide.symm

/-- Pointwise Cauchy--Schwarz for the exact prefix decomposition.  The
displayed `2 (k+1)` is an explicit harmless logarithmic loss, not asymptotic
notation. -/
theorem norm_gmReflectionDirichletPoly_sq_le_dyadic
    (t u : ℝ) {M : ℕ} (hM : 0 < M) :
    ‖gmReflectionDirichletPoly t M u‖ ^ 2 ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        (1 + ∑ r ∈ Finset.range (Nat.clog 2 M),
          ‖dirichletPoly (2 ^ r)
            (heathBrownReflectedPrefixCoeff M u) t‖ ^ 2) := by
  let k := Nat.clog 2 M
  let P : ℂ := wideDirichletPoly 1 k
    (heathBrownReflectedPrefixCoeff M u) t
  have hIdentity : gmReflectionDirichletPoly t M u = 1 + P := by
    simpa only [P, k] using gmReflectionDirichletPoly_eq_one_add_wide t u hM
  have hTriangle : ‖gmReflectionDirichletPoly t M u‖ ≤ 1 + ‖P‖ := by
    rw [hIdentity]
    simpa using norm_add_le (1 : ℂ) P
  have hNormNonneg : 0 ≤ ‖gmReflectionDirichletPoly t M u‖ := norm_nonneg _
  have hPNonneg : 0 ≤ ‖P‖ := norm_nonneg _
  have hSquare : ‖gmReflectionDirichletPoly t M u‖ ^ 2 ≤
      2 * (1 + ‖P‖ ^ 2) := by
    have hMono : ‖gmReflectionDirichletPoly t M u‖ ^ 2 ≤
        (1 + ‖P‖) ^ 2 := by nlinarith
    calc
      ‖gmReflectionDirichletPoly t M u‖ ^ 2 ≤
          (1 + ‖P‖) ^ 2 := hMono
      _ ≤ 2 * (1 + ‖P‖ ^ 2) := by nlinarith [sq_nonneg (‖P‖ - 1)]
  have hBlocks : ‖P‖ ^ 2 ≤
      (k : ℝ) * ∑ r ∈ Finset.range k,
        ‖dirichletPoly (2 ^ r)
          (heathBrownReflectedPrefixCoeff M u) t‖ ^ 2 := by
    dsimp only [P]
    rw [wideDirichletPoly_eq_sum_blocks]
    simpa only [one_mul, Nat.mul_one, Finset.card_range, Nat.cast_id] using
      complex_sum_sq_le_card_mul_sum_sq (Finset.range k)
        (fun r => dirichletPoly (2 ^ r)
          (heathBrownReflectedPrefixCoeff M u) t)
  have hSumNonneg : 0 ≤ ∑ r ∈ Finset.range k,
      ‖dirichletPoly (2 ^ r)
        (heathBrownReflectedPrefixCoeff M u) t‖ ^ 2 := by positivity
  calc
    ‖gmReflectionDirichletPoly t M u‖ ^ 2 ≤
        2 * (1 + ‖P‖ ^ 2) := hSquare
    _ ≤ 2 * (1 + (k : ℝ) * ∑ r ∈ Finset.range k,
        ‖dirichletPoly (2 ^ r)
          (heathBrownReflectedPrefixCoeff M u) t‖ ^ 2) := by gcongr
    _ ≤ 2 * ((k : ℝ) + 1) *
        (1 + ∑ r ∈ Finset.range k,
          ‖dirichletPoly (2 ^ r)
            (heathBrownReflectedPrefixCoeff M u) t‖ ^ 2) := by
      nlinarith [show 0 ≤ (k : ℝ) by positivity]

/-- Fixed-displacement ordered-pair moment of a reflected prefix.  The
translation is absorbed into unit coefficients and then eliminated by the
positive-kernel coefficient majorant, leaving only the literal
coefficient-one Heath--Brown moments at dyadic scales. -/
theorem gmReflectionDirichletPoly_differenceMoment_le_dyadic
    (W : Finset ℝ) (u : ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ t ∈ W, ∑ v ∈ W,
        ‖gmReflectionDirichletPoly (t - v) M u‖ ^ 2) ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          ∑ r ∈ Finset.range (Nat.clog 2 M),
            ∑ t ∈ W, ∑ v ∈ W,
              ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ)) (t - v)‖ ^ 2) := by
  let k := Nat.clog 2 M
  have hPoint : ∀ t ∈ W, ∀ v ∈ W,
      ‖gmReflectionDirichletPoly (t - v) M u‖ ^ 2 ≤
        2 * ((k : ℝ) + 1) *
          (1 + ∑ r ∈ Finset.range k,
            ‖dirichletPoly (2 ^ r)
              (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2) := by
    intro t ht v hv
    simpa only [k] using
      norm_gmReflectionDirichletPoly_sq_le_dyadic (t - v) u hM
  calc
    (∑ t ∈ W, ∑ v ∈ W,
        ‖gmReflectionDirichletPoly (t - v) M u‖ ^ 2) ≤
      ∑ t ∈ W, ∑ v ∈ W,
        2 * ((k : ℝ) + 1) *
          (1 + ∑ r ∈ Finset.range k,
            ‖dirichletPoly (2 ^ r)
              (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro v hv
        exact hPoint t ht v hv
    _ = 2 * ((k : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          ∑ r ∈ Finset.range k,
            ∑ t ∈ W, ∑ v ∈ W,
              ‖dirichletPoly (2 ^ r)
                (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      ring_nf
      congr 1
      calc
        (∑ t ∈ W, ∑ v ∈ W, ∑ r ∈ Finset.range k,
            ((k : ℝ) *
                ‖dirichletPoly (2 ^ r)
                  (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2 +
              ‖dirichletPoly (2 ^ r)
                (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2)) =
          ∑ t ∈ W, ∑ r ∈ Finset.range k, ∑ v ∈ W,
            ((k : ℝ) *
                ‖dirichletPoly (2 ^ r)
                  (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2 +
              ‖dirichletPoly (2 ^ r)
                (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact Finset.sum_comm
        _ = ∑ r ∈ Finset.range k, ∑ t ∈ W, ∑ v ∈ W,
            ((k : ℝ) *
                ‖dirichletPoly (2 ^ r)
                  (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2 +
              ‖dirichletPoly (2 ^ r)
                (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2 * 2) :=
          Finset.sum_comm
    _ ≤ 2 * ((k : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          ∑ r ∈ Finset.range k,
            ∑ t ∈ W, ∑ v ∈ W,
              ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ)) (t - v)‖ ^ 2) := by
      have hMoments :
          (∑ r ∈ Finset.range k,
              ∑ t ∈ W, ∑ v ∈ W,
                ‖dirichletPoly (2 ^ r)
                  (heathBrownReflectedPrefixCoeff M u) (t - v)‖ ^ 2) ≤
            ∑ r ∈ Finset.range k,
              ∑ t ∈ W, ∑ v ∈ W,
                ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ))
                  (t - v)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        exact dirichletPoly_differenceMoment_le_one (2 ^ r) W
          (heathBrownReflectedPrefixCoeff M u)
          (fun n hn => norm_heathBrownReflectedPrefixCoeff_le_one M u n)
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hMoments) (by positivity)

/-! ## Cauchy--Schwarz across the reflection integral -/

/-- Interval Cauchy--Schwarz in the exact real, nonnegative form used by
the reflected Heath--Brown recurrence. -/
theorem sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (f : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u in -H..H, f u) ^ 2 ≤
      (2 * H) * ∫ u in -H..H, f u ^ 2 := by
  let s : Set ℝ := Set.Ioc (-H) H
  let μ : Measure ℝ := volume.restrict s
  have horder : -H ≤ H := by linarith
  have hf2Int : Integrable (fun u => f u ^ 2) μ := by
    change IntegrableOn (fun u => f u ^ 2) s
    exact (hf.pow 2).continuousOn.integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hOneInt : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) μ := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ) ^ 2) s
    exact (continuous_const.pow 2).continuousOn.integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hfMem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2Int
  have hOneMem : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq continuous_const.aestronglyMeasurable).2
      hOneInt
  have hfMem' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hfMem
  have hOneMem' : MemLp (fun _ : ℝ => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hOneMem
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hf0) (Eventually.of_forall fun _ => zero_le_one)
    hfMem' hOneMem'
  have hIntNonneg : 0 ≤ ∫ u in -H..H, f u :=
    intervalIntegral.integral_nonneg horder (fun u hu => hf0 u)
  have hSqIntNonneg : 0 ≤ ∫ u in -H..H, f u ^ 2 :=
    intervalIntegral.integral_nonneg horder (fun u hu => sq_nonneg _)
  have hMeasure : ∫ _u : ℝ in -H..H, (1 : ℝ) = 2 * H := by
    simp
    ring
  have hHolder' :
      (∫ u in -H..H, f u) ≤
        Real.sqrt (∫ u in -H..H, f u ^ 2) * Real.sqrt (2 * H) := by
    dsimp only [μ, s] at hHolder
    simp only [mul_one, one_rpow] at hHolder
    rw [← intervalIntegral.integral_of_le horder,
      ← intervalIntegral.integral_of_le horder,
      ← intervalIntegral.integral_of_le horder] at hHolder
    rw [hMeasure] at hHolder
    simpa only [Real.sqrt_eq_rpow, one_div, Real.rpow_two] using hHolder
  have hLengthNonneg : 0 ≤ 2 * H := by positivity
  have hSqrtSq :
      (Real.sqrt (∫ u in -H..H, f u ^ 2) * Real.sqrt (2 * H)) ^ 2 =
        (2 * H) * ∫ u in -H..H, f u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hSqIntNonneg, Real.sq_sqrt hLengthNonneg]
    ring
  calc
    (∫ u in -H..H, f u) ^ 2 ≤
        (Real.sqrt (∫ u in -H..H, f u ^ 2) * Real.sqrt (2 * H)) ^ 2 := by
      exact pow_le_pow_left₀ hIntNonneg hHolder' 2
    _ = (2 * H) * ∫ u in -H..H, f u ^ 2 := hSqrtSq

/-- Cauchy--Schwarz for the literal reflected prefix appearing in Lemma
6.2. -/
theorem sq_integral_norm_gmReflectionDirichletPoly_le
    (t : ℝ) (M : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) ^ 2 ≤
      (2 * H) *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ ^ 2 := by
  exact sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    (fun u => ‖gmReflectionDirichletPoly t M u‖) H hH
    (continuous_gmReflectionDirichletPoly t M).norm
    (fun u => norm_nonneg _)

/-! ## Fixed-length reflection for dyadic displacement bins -/

/-- Complete trace reflection with an arbitrary common dual cutoff `M`.
This is the form required for a difference bin: every pair in the bin uses
the same coefficient sequence, so the positive-kernel moment majorant is
legitimate.  All Mellin, omitted-frequency, and zero-mode errors remain
explicit. -/
theorem heathBrownTracePolynomial_reflection_with_length
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {t T₀ H : ℝ} {Q M : ℕ},
        4 ≤ T₀ → T₀ ≤ |t| → 1 ≤ H → H ≤ T₀ / 2 →
        0 < Q → 0 < M →
        ‖heathBrownTracePolynomial cutoff Q t‖ ≤
          (Q : ℝ) * C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            (Q : ℝ) * K * (M : ℝ) ^ 2 *
              H ^ (1 - (q : ℝ)) +
            (Q : ℝ) * L * (1 + |t|) ^ (q + 2) /
              ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) +
            (Q : ℝ) * D / T₀ ^ q := by
  obtain ⟨C, K, L, hC, hK, hL, hComplete⟩ :=
    gmCompleteSmoothReflection_bound_order cutoff q hq
  obtain ⟨D, hD, hZero⟩ := gmTraceZeroMode_separated_bound cutoff q
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro t T₀ H Q M hT₀ ht hH hHT hQ hM
  have hTrace := norm_heathBrownTracePolynomial_le_zero_add_tail
    cutoff Q hQ t
  have hZeroAt := hZero Q (show 0 < T₀ by linarith) ht
  have hTailAt := hComplete hT₀ ht hH hHT hQ hM
  rw [norm_gmTraceNonzeroTailAt_eq] at hTrace
  calc
    ‖heathBrownTracePolynomial cutoff Q t‖ ≤
        ‖gmTraceZeroMode cutoff Q t‖ +
          (Q : ℝ) * ‖gmTraceNonzeroFourierSum cutoff Q t‖ := hTrace
    _ ≤ (Q : ℝ) * D / T₀ ^ q +
        (Q : ℝ) *
          (C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            L * (1 + |t|) ^ (q + 2) /
              ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q)) := by
      exact add_le_add hZeroAt
        (mul_le_mul_of_nonneg_left hTailAt (by positivity))
    _ = (Q : ℝ) * C / Real.sqrt T₀ *
            (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
          (Q : ℝ) * K * (M : ℝ) ^ 2 *
            H ^ (1 - (q : ℝ)) +
          (Q : ℝ) * L * (1 + |t|) ^ (q + 2) /
            ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) +
          (Q : ℝ) * D / T₀ ^ q := by ring

/-! ## Exact dyadic decomposition of the difference set -/

/-- The dyadic scale of a nonzero ordinate difference. -/
noncomputable def heathBrownDifferenceScale (t u : ℝ) : ℕ :=
  Nat.log 2 (Nat.floor |t - u|)

/-- Ordered off-diagonal pairs from a finite ordinate set. -/
noncomputable def heathBrownOffDiagonalPairs (W : Finset ℝ) : Finset (ℝ × ℝ) :=
  (W ×ˢ W).filter (fun p => p.1 ≠ p.2)

/-- One exact fiber of the dyadic difference-scale map. -/
noncomputable def heathBrownDifferenceBin
    (W : Finset ℝ) (j : ℕ) : Finset (ℝ × ℝ) :=
  (heathBrownOffDiagonalPairs W).filter
    (fun p => heathBrownDifferenceScale p.1 p.2 = j)

/-- Ordered distinct pairs at distance below the integral radius `K`. -/
noncomputable def heathBrownNearPairs
    (W : Finset ℝ) (K : ℕ) : Finset (ℝ × ℝ) :=
  (W ×ˢ W).filter
    (fun p => p.1 ≠ p.2 ∧ |p.1 - p.2| < (K : ℝ))

/-- A one-separated set has at most two points in every unit annulus, hence
at most `2K` distinct neighbours of any centre at distance below `K`. -/
theorem separated_near_card_le_two_mul
    (W : Finset ℝ) (t : ℝ) (K : ℕ) (hSep : IsSeparated 1 W) :
    ({u ∈ W | u ≠ t ∧ |u - t| < (K : ℝ)}).card ≤ 2 * K := by
  let S := {u ∈ W | u ≠ t ∧ |u - t| < (K : ℝ)}
  let shell : ℝ → ℕ := fun u => Nat.floor |u - t|
  have hMaps : ∀ u ∈ S, shell u ∈ Finset.range K := by
    intro u hu
    rw [Finset.mem_range]
    exact (Nat.floor_lt (abs_nonneg _)).2 (Finset.mem_filter.mp hu).2.2
  have hFiber : ∀ k ∈ Finset.range K,
      ({u ∈ S | shell u = k}).card ≤ 2 := by
    intro k hk
    calc
      ({u ∈ S | shell u = k}).card ≤
          ({u ∈ W | u ≠ t ∧ (k : ℝ) ≤ |u - t| ∧
            |u - t| < (k : ℝ) + 1}).card := by
        apply Finset.card_le_card
        intro u hu
        have huFilter := Finset.mem_filter.mp hu
        have huS := Finset.mem_filter.mp huFilter.1
        have hFloor := huFilter.2
        have hNonneg : 0 ≤ |u - t| := abs_nonneg _
        have hLow : (k : ℝ) ≤ |u - t| := by
          rw [← hFloor]
          exact Nat.floor_le hNonneg
        have hHigh : |u - t| < (k : ℝ) + 1 := by
          rw [← hFloor]
          exact Nat.lt_floor_add_one _
        exact Finset.mem_filter.mpr ⟨huS.1, huS.2.1, hLow, hHigh⟩
      _ ≤ 2 := separated_annulus_card_le_two W t k hSep
  change S.card ≤ 2 * K
  rw [Finset.card_eq_sum_ones]
  rw [← Finset.sum_fiberwise_of_maps_to hMaps (fun _ => 1)]
  calc
    (∑ k ∈ Finset.range K, ∑ _u ∈ S with shell _u = k, 1) ≤
        ∑ _k ∈ Finset.range K, 2 := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [sum_const, nsmul_eq_mul, mul_one] using hFiber k hk
    _ = 2 * K := by simp; ring

/-- The complete ordered near-pair set has the corresponding `2K|W|`
cardinality bound. -/
theorem heathBrownNearPairs_card_le
    (W : Finset ℝ) (K : ℕ) (hSep : IsSeparated 1 W) :
    (heathBrownNearPairs W K).card ≤ W.card * (2 * K) := by
  have hEq : (heathBrownNearPairs W K).card =
      ∑ t ∈ W, ({u ∈ W | u ≠ t ∧ |u - t| < (K : ℝ)}).card := by
    unfold heathBrownNearPairs
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    rw [abs_sub_comm t u]
    by_cases htu : t = u
    · simp [htu]
    · simp [htu, Ne.symm htu]
  rw [hEq]
  calc
    (∑ t ∈ W, ({u ∈ W | u ≠ t ∧ |u - t| < (K : ℝ)}).card) ≤
        ∑ _t ∈ W, 2 * K := by
      apply Finset.sum_le_sum
      intro t ht
      exact separated_near_card_le_two_mul W t K hSep
    _ = W.card * (2 * K) := by simp

/-- The floor-log definition gives the literal dyadic inequalities needed
to use a single reflection scale throughout one bin. -/
theorem heathBrownDifferenceScale_bounds
    {t u : ℝ} (hLower : 1 ≤ |t - u|) :
    ((2 ^ heathBrownDifferenceScale t u : ℕ) : ℝ) ≤ |t - u| ∧
      |t - u| < ((2 ^ (heathBrownDifferenceScale t u + 1) : ℕ) : ℝ) := by
  let n := Nat.floor |t - u|
  have hAbsNonneg : 0 ≤ |t - u| := abs_nonneg _
  have hnPos : 0 < n := by
    dsimp only [n]
    exact Nat.floor_pos.mpr hLower
  have hnNe : n ≠ 0 := hnPos.ne'
  have hPowLowerNat : 2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hnNe
  have hFloorLower : (n : ℝ) ≤ |t - u| := by
    dsimp only [n]
    exact Nat.floor_le hAbsNonneg
  have hAbsFloorSucc : |t - u| < (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one |t - u|
  have hFloorUpperNat : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
    Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two n)
  constructor
  · dsimp only [heathBrownDifferenceScale, n]
    exact (by exact_mod_cast hPowLowerNat :
      ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ)).trans hFloorLower
  · dsimp only [heathBrownDifferenceScale, n]
    exact hAbsFloorSucc.trans_le (by exact_mod_cast hFloorUpperNat)

/-- Membership in the `j`th exact difference fiber supplies the common
dyadic lower and upper displacement bounds used by the reflection theorem. -/
theorem heathBrownDifferenceBin_bounds
    {W : Finset ℝ} {j : ℕ} {p : ℝ × ℝ} (hSep : IsSeparated 1 W)
    (hp : p ∈ heathBrownDifferenceBin W j) :
    (((2 ^ j : ℕ) : ℝ) ≤ |p.1 - p.2| ∧
      |p.1 - p.2| < ((2 ^ (j + 1) : ℕ) : ℝ)) := by
  have hpFilter := Finset.mem_filter.mp hp
  have hpOff := Finset.mem_filter.mp hpFilter.1
  have hpW := Finset.mem_product.mp hpOff.1
  have hLower : 1 ≤ |p.1 - p.2| := by
    simpa [Real.dist_eq] using
      hSep p.1 hpW.1 p.2 hpW.2 hpOff.2
  have hBounds := heathBrownDifferenceScale_bounds hLower
  simpa [hpFilter.2] using hBounds

/-- A dyadic displacement fiber is a subset of the near-pair set at its
upper endpoint, giving a source-faithful local cardinality estimate. -/
theorem heathBrownDifferenceBin_card_le
    (W : Finset ℝ) (j : ℕ) (hSep : IsSeparated 1 W) :
    (heathBrownDifferenceBin W j).card ≤ W.card * (2 * 2 ^ (j + 1)) := by
  apply le_trans (Finset.card_le_card ?_)
    (heathBrownNearPairs_card_le W (2 ^ (j + 1)) hSep)
  intro p hp
  have hpFilter := Finset.mem_filter.mp hp
  have hpOff := Finset.mem_filter.mp hpFilter.1
  have hBounds := heathBrownDifferenceBin_bounds hSep hp
  exact Finset.mem_filter.mpr ⟨hpOff.1, hpOff.2, hBounds.2⟩

/-- Every off-diagonal pair in a separated base interval belongs to one of
the finitely many dyadic fibers up to the physical height. -/
theorem heathBrownDifferenceScale_mem_range
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) {p : ℝ × ℝ}
    (hp : p ∈ heathBrownOffDiagonalPairs W) :
    heathBrownDifferenceScale p.1 p.2 ∈
      Finset.range (Nat.log 2 (Nat.floor T) + 1) := by
  have hpData := Finset.mem_filter.mp hp
  have hpW := Finset.mem_product.mp hpData.1
  have hLower : 1 ≤ |p.1 - p.2| := by
    simpa [Real.dist_eq] using hSep p.1 hpW.1 p.2 hpW.2 hpData.2
  have hUpper : |p.1 - p.2| ≤ T :=
    abs_sub_le_height_of_mem_baseInterval hInterval hpW.1 hpW.2
  have hTNonneg : 0 ≤ T := (abs_nonneg _).trans hUpper
  have hFloorMono : Nat.floor |p.1 - p.2| ≤ Nat.floor T :=
    Nat.floor_mono hUpper
  have hLogMono : Nat.log 2 (Nat.floor |p.1 - p.2|) ≤
      Nat.log 2 (Nat.floor T) := Nat.log_monotone hFloorMono
  rw [Finset.mem_range]
  dsimp only [heathBrownDifferenceScale]
  omega

/-- Exact fiberwise partition of an arbitrary off-diagonal pair sum. -/
theorem sum_heathBrownOffDiagonalPairs_eq_sum_differenceBins
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) (F : (ℝ × ℝ) → ℝ) :
    (∑ p ∈ heathBrownOffDiagonalPairs W, F p) =
      ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        ∑ p ∈ heathBrownDifferenceBin W j, F p := by
  have hMaps : ∀ p ∈ heathBrownOffDiagonalPairs W,
      heathBrownDifferenceScale p.1 p.2 ∈
        Finset.range (Nat.log 2 (Nat.floor T) + 1) :=
    fun p hp => heathBrownDifferenceScale_mem_range hSep hInterval hp
  have hFiber := Finset.sum_fiberwise_of_maps_to hMaps F
  simpa only [heathBrownDifferenceBin] using hFiber.symm

/-! ## Trace-moment diagonal and bin assembly -/

/-- The unrestricted cutoff-squared trace polynomial has the elementary
pointwise bound by the exact dyadic interval length. -/
theorem norm_heathBrownTracePolynomial_le
    (cutoff : GMSmoothCutoff) (Q : ℕ) (t : ℝ) :
    ‖heathBrownTracePolynomial cutoff Q t‖ ≤ Q := by
  rw [heathBrownTracePolynomial_eq_source]
  unfold sourceDirichletPoly
  calc
    ‖∑ n ∈ dyadicInterval Q,
        (((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) *
          (n : ℂ) ^ ((t : ℂ) * I)‖ ≤
      ∑ n ∈ dyadicInterval Q,
        ‖(((cutoff ((n : ℝ) / Q) ^ 2 : ℝ) : ℂ)) *
          (n : ℂ) ^ ((t : ℂ) * I)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ dyadicInterval Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnPos : 0 < n := by
        rw [dyadicInterval, Finset.mem_Ioc] at hn
        omega
      have hPhase : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hnPos]
        simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _), hPhase, mul_one]
      have hCutNonneg := cutoff.nonneg ((n : ℝ) / Q)
      have hCutLe := cutoff.bounded ((n : ℝ) / Q)
      nlinarith [sq_nonneg (cutoff ((n : ℝ) / Q) - 1)]
    _ = Q := by
      simp [dyadicInterval]
      omega

/-- Off-diagonal part of one smooth trace moment. -/
noncomputable def heathBrownTraceOffDiagonalMoment
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ p ∈ heathBrownOffDiagonalPairs W,
    ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2

/-- The trace diagonal is bounded by the exact cardinality times `Q²`. -/
theorem heathBrownTraceDiagonal_le
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ‖heathBrownTracePolynomial cutoff Q (t - t)‖ ^ 2) ≤
      (W.card : ℝ) * Q ^ 2 := by
  calc
    (∑ t ∈ W, ‖heathBrownTracePolynomial cutoff Q (t - t)‖ ^ 2) ≤
        ∑ _t ∈ W, (Q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have hNorm := norm_heathBrownTracePolynomial_le cutoff Q (t - t)
      exact pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    _ = (W.card : ℝ) * Q ^ 2 := by simp

/-- The product-filter representation is exactly the traditional nested
off-diagonal sum. -/
theorem heathBrownTraceOffDiagonalMoment_eq_nested
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) :
    heathBrownTraceOffDiagonalMoment cutoff Q W =
      ∑ t ∈ W, ∑ u ∈ W.erase t,
        ‖heathBrownTracePolynomial cutoff Q (t - u)‖ ^ 2 := by
  classical
  unfold heathBrownTraceOffDiagonalMoment heathBrownOffDiagonalPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ u ∈ W, if t ≠ u then
        ‖heathBrownTracePolynomial cutoff Q (t - u)‖ ^ 2 else 0) =
      ∑ u ∈ W.erase t, if t ≠ u then
        ‖heathBrownTracePolynomial cutoff Q (t - u)‖ ^ 2 else 0 := by
        rw [← Finset.sum_erase_add W _ ht]
        simp
    _ = ∑ u ∈ W.erase t,
        ‖heathBrownTracePolynomial cutoff Q (t - u)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [(Finset.ne_of_mem_erase hu).symm]

/-- Exact diagonal/off-diagonal decomposition of the smooth trace moment. -/
theorem heathBrownTraceMoment_eq_diagonal_add_offDiagonal
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) :
    heathBrownTraceMoment cutoff Q W =
      (∑ t ∈ W, ‖heathBrownTracePolynomial cutoff Q (t - t)‖ ^ 2) +
        heathBrownTraceOffDiagonalMoment cutoff Q W := by
  unfold heathBrownTraceMoment
  rw [orderedPairSum_eq_diagonal_add_offDiagonal,
    heathBrownTraceOffDiagonalMoment_eq_nested]

/-- Exact dyadic-bin expansion of the smooth off-diagonal trace moment. -/
theorem heathBrownTraceOffDiagonalMoment_eq_sum_bins
    {T : ℝ} {W : Finset ℝ} (hSep : IsSeparated 1 W)
    (hInterval : InBaseInterval T W) (cutoff : GMSmoothCutoff) (Q : ℕ) :
    heathBrownTraceOffDiagonalMoment cutoff Q W =
      ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        ∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2 := by
  unfold heathBrownTraceOffDiagonalMoment
  exact sum_heathBrownOffDiagonalPairs_eq_sum_differenceBins hSep hInterval _

/-- One smooth-trace dyadic-bin moment. -/
noncomputable def heathBrownTraceBinMoment
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ heathBrownDifferenceBin W j,
    ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2

/-- A bin-restricted reflected-prefix moment is bounded by the complete
ordered-pair moment, hence by the exact dyadic coefficient-one expression.
-/
theorem gmReflectionDirichletPoly_binMoment_le_dyadic
    (W : Finset ℝ) (j : ℕ) (u : ℝ) {M : ℕ} (hM : 0 < M) :
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2) ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          ∑ r ∈ Finset.range (Nat.clog 2 M),
            ∑ t ∈ W, ∑ v ∈ W,
              ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ)) (t - v)‖ ^ 2) := by
  have hSubset : heathBrownDifferenceBin W j ⊆ W ×ˢ W := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2) ≤
      ∑ p ∈ W ×ˢ W,
        ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun p hp hnot => sq_nonneg _)
    _ = ∑ t ∈ W, ∑ v ∈ W,
        ‖gmReflectionDirichletPoly (t - v) M u‖ ^ 2 := by
      rw [Finset.sum_product]
    _ ≤ _ := gmReflectionDirichletPoly_differenceMoment_le_dyadic W u hM

/-- Sum of the squared reflection integrals over one difference bin.  Two
applications of interval length are visible: one from Cauchy--Schwarz and
one from integrating the uniform dyadic moment bound. -/
theorem sum_bin_sq_integral_norm_gmReflectionDirichletPoly_le
    (W : Finset ℝ) (j : ℕ) {M : ℕ} (hM : 0 < M)
    (H : ℝ) (hH : 0 ≤ H) :
    (∑ p ∈ heathBrownDifferenceBin W j,
        (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2) ≤
      (2 * H) ^ 2 *
        (2 * ((Nat.clog 2 M : ℝ) + 1) *
          (((W.card : ℝ) ^ 2) +
            ∑ r ∈ Finset.range (Nat.clog 2 M),
              ∑ t ∈ W, ∑ v ∈ W,
                ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ))
                  (t - v)‖ ^ 2)) := by
  let B : ℝ := 2 * ((Nat.clog 2 M : ℝ) + 1) *
    (((W.card : ℝ) ^ 2) +
      ∑ r ∈ Finset.range (Nat.clog 2 M),
        ∑ t ∈ W, ∑ v ∈ W,
          ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ)) (t - v)‖ ^ 2)
  have hLength : 0 ≤ 2 * H := by positivity
  have hPoint : ∀ p ∈ heathBrownDifferenceBin W j,
      (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 ≤
        (2 * H) * ∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2 := by
    intro p hp
    exact sq_integral_norm_gmReflectionDirichletPoly_le
      (p.1 - p.2) M H hH
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2) ≤
      ∑ p ∈ heathBrownDifferenceBin W j,
        (2 * H) * ∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact hPoint p hp
    _ = (2 * H) * ∫ u in -H..H,
        ∑ p ∈ heathBrownDifferenceBin W j,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply intervalIntegral.integral_finsetSum
      intro p hp
      exact ((continuous_gmReflectionDirichletPoly (p.1 - p.2) M).norm.pow 2)
        |>.intervalIntegrable _ _
    _ ≤ (2 * H) * ∫ _u in -H..H, B := by
      apply mul_le_mul_of_nonneg_left _ hLength
      apply intervalIntegral.integral_mono_on
      · linarith
      · exact (continuous_finsetSum (heathBrownDifferenceBin W j) (fun p hp =>
          (continuous_gmReflectionDirichletPoly (p.1 - p.2) M).norm.pow 2))
          |>.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u hu
        dsimp only [B]
        exact gmReflectionDirichletPoly_binMoment_le_dyadic W j u hM
    _ = (2 * H) ^ 2 * B := by
      simp
      ring

/-! ## Binwise reflected trace estimate -/

/-- The coefficient-one ordered-difference moment at one physical scale.
This names the quantity recursively reappearing after smooth reflection. -/
noncomputable def heathBrownCoefficientOneMoment
    (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2

/-- Reversing both ordinate indices converts the negative-sign polynomial
moment exactly into the source positive-sign convention. -/
theorem dirichletPoly_one_differenceMoment_eq_coefficientOneMoment
    (N : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖dirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) =
      heathBrownCoefficientOneMoment N W := by
  unfold heathBrownCoefficientOneMoment
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖dirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2) =
      ∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (u - t)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro u hu
          rw [← dirichletPoly_neg_eq_sourceDirichletPoly]
          congr 3
          ring
    _ = ∑ u ∈ W, ∑ t ∈ W,
        ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (u - t)‖ ^ 2 :=
      Finset.sum_comm
    _ = _ := rfl

/-- The coefficient-one moment which controls every reflected prefix of
length `M`.  Keeping this expression named prevents the later recurrence
from hiding its actual dyadic Dirichlet-polynomial input. -/
noncomputable def heathBrownReflectionDyadicMoment
    (W : Finset ℝ) (M : ℕ) : ℝ :=
  2 * ((Nat.clog 2 M : ℝ) + 1) *
    (((W.card : ℝ) ^ 2) +
      ∑ r ∈ Finset.range (Nat.clog 2 M),
        ∑ t ∈ W, ∑ v ∈ W,
          ‖dirichletPoly (2 ^ r) (fun _ => (1 : ℂ)) (t - v)‖ ^ 2)

/-- The reflected-prefix majorant is literally a logarithmic sum of the
same coefficient-one moments at smaller dyadic scales. -/
theorem heathBrownReflectionDyadicMoment_eq
    (W : Finset ℝ) (M : ℕ) :
    heathBrownReflectionDyadicMoment W M =
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          ∑ r ∈ Finset.range (Nat.clog 2 M),
            heathBrownCoefficientOneMoment (2 ^ r) W) := by
  unfold heathBrownReflectionDyadicMoment
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  exact dirichletPoly_one_differenceMoment_eq_coefficientOneMoment (2 ^ r) W

/-- The three uniform error terms in the fixed-length reflection theorem.
The displacement-dependent numerator has been replaced by its bin endpoint
`U`; the corresponding comparison is proved in the consumer below. -/
noncomputable def heathBrownReflectionBinError
    (q Q M : ℕ) (H U T₀ K L D : ℝ) : ℝ :=
  (Q : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
    (Q : ℝ) * L * (1 + U) ^ (q + 2) /
      ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) +
    (Q : ℝ) * D / T₀ ^ q

/-- The square of four real summands is at most four times the sum of their
squares.  This elementary loss is the exact finite device used to square the
reflection formula without introducing a hidden asymptotic constant. -/
theorem add_add_add_sq_le_four_mul_sum_sq (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ + x₂ + x₃ + x₄) ^ 2 ≤
      4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃),
    sq_nonneg (x₁ - x₄), sq_nonneg (x₂ - x₃),
    sq_nonneg (x₂ - x₄), sq_nonneg (x₃ - x₄)]

/-- One exact dyadic displacement bin of the smooth trace moment is bounded
by a common reflected coefficient-one moment plus the complete uniform
Mellin, omitted-frequency, and zero-mode errors.  This is the quantitative
bin consumer needed for the Heath--Brown recurrence; it invokes the actual
complete reflection theorem for every pair in the bin. -/
theorem heathBrownTraceBinMoment_le_reflection
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {W : Finset ℝ} {j Q M : ℕ} {H : ℝ},
        IsSeparated 1 W → 2 ≤ j → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 → 0 < Q → 0 < M →
        heathBrownTraceBinMoment cutoff Q W j ≤
          2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (heathBrownReflectionBinError q Q M H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hReflect⟩ :=
    heathBrownTracePolynomial_reflection_with_length cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro W j Q M H hSep hj hH hHupper hQ hM
  let T₀ : ℝ := ((2 ^ j : ℕ) : ℝ)
  let U : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
  let A : ℝ := (Q : ℝ) * C / Real.sqrt T₀
  let E : ℝ := heathBrownReflectionBinError q Q M H U T₀ K L D
  have hT₀ : 4 ≤ T₀ := by
    have hNat : 4 ≤ 2 ^ j := by
      change 2 ^ 2 ≤ 2 ^ j
      exact Nat.pow_le_pow_right (by omega) hj
    dsimp only [T₀]
    exact_mod_cast hNat
  have hPoint : ∀ p ∈ heathBrownDifferenceBin W j,
      ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ≤
        A * (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E := by
    intro p hp
    have hBin := heathBrownDifferenceBin_bounds hSep hp
    have hRaw := hReflect hT₀ hBin.1 hH (by simpa [T₀] using hHupper) hQ hM
    have hBase : 1 + |p.1 - p.2| ≤ 1 + U := by
      dsimp only [U]
      linarith
    have hPow : (1 + |p.1 - p.2|) ^ (q + 2) ≤
        (1 + U) ^ (q + 2) :=
      pow_le_pow_left₀ (by positivity) hBase (q + 2)
    have hDenom : 0 < (Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q := by
      positivity
    have hFrequency :
        (Q : ℝ) * L * (1 + |p.1 - p.2|) ^ (q + 2) /
            ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) ≤
          (Q : ℝ) * L * (1 + U) ^ (q + 2) /
            ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
      apply div_le_div_of_nonneg_right _ hDenom.le
      exact mul_le_mul_of_nonneg_left hPow (by positivity)
    dsimp only [A, E, heathBrownReflectionBinError, T₀, U]
    calc
      ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ≤
          (Q : ℝ) * C / Real.sqrt (((2 ^ j : ℕ) : ℝ)) *
              (∫ u in -H..H,
                ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) +
            (Q : ℝ) * K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            (Q : ℝ) * L * (1 + |p.1 - p.2|) ^ (q + 2) /
              ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) +
            (Q : ℝ) * D / (((2 ^ j : ℕ) : ℝ)) ^ q := hRaw
      _ ≤ _ := by linarith
  have hPointSq : ∀ p ∈ heathBrownDifferenceBin W j,
      ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2 ≤
        2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2 := by
    intro p hp
    have hpBound := hPoint p hp
    have hRhsNonneg : 0 ≤
        A * (∫ u in -H..H,
          ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E :=
      (norm_nonneg _).trans hpBound
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hpBound 2
    calc
      ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2 ≤
          (A * (∫ u in -H..H,
            ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) + E) ^ 2 := hSq
      _ ≤ 2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2 := by
        nlinarith [sq_nonneg
          (A * (∫ u in -H..H,
            ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) - E)]
  have hIntegral := sum_bin_sq_integral_norm_gmReflectionDirichletPoly_le
    W j hM H ((by norm_num : (0 : ℝ) ≤ 1).trans hH)
  unfold heathBrownTraceBinMoment
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2) ≤
      ∑ p ∈ heathBrownDifferenceBin W j,
        (2 * A ^ 2 *
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2 +
          2 * E ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hPointSq p hp
    _ = 2 * A ^ 2 *
          (∑ p ∈ heathBrownDifferenceBin W j,
            (∫ u in -H..H,
              ‖gmReflectionDirichletPoly (p.1 - p.2) M u‖) ^ 2) +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) * E ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ 2 * A ^ 2 *
          ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) * E ^ 2 := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left
        · simpa only [heathBrownReflectionDyadicMoment] using hIntegral
        · positivity
      · exact le_rfl
    _ = 2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * H) ^ 2 * heathBrownReflectionDyadicMoment W M) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (heathBrownReflectionBinError q Q M H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 := by
      rfl

/-- The elementary estimate for the two displacement fibers below the
stationary-reflection threshold. -/
theorem heathBrownTraceBinMoment_le_card_mul
    (cutoff : GMSmoothCutoff) (Q : ℕ) (W : Finset ℝ) (j : ℕ) :
    heathBrownTraceBinMoment cutoff Q W j ≤
      ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2 := by
  unfold heathBrownTraceBinMoment
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2) ≤
      ∑ _p ∈ heathBrownDifferenceBin W j, (Q : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_heathBrownTracePolynomial_le cutoff Q (p.1 - p.2)) 2
    _ = ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2 := by simp

/-- Source-sharp estimate for a nonstationary dyadic displacement bin.  The
upper endpoint hypothesis places the whole bin below the polynomial scale;
the lower endpoint then retains the decisive inverse dyadic factor. -/
theorem exists_heathBrownTraceBinMoment_near_bound
    (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) (W : Finset ℝ) (j : ℕ),
        0 < Q → IsSeparated 1 W → 2 ^ (j + 1) ≤ Q →
        heathBrownTraceBinMoment cutoff Q W j ≤
          ((heathBrownDifferenceBin W j).card : ℝ) *
            (C * (Q : ℝ) / (2 ^ j : ℕ)) ^ 2 := by
  obtain ⟨C, hC, hTrace⟩ :=
    exists_norm_heathBrownTracePolynomial_le_div cutoff
  refine ⟨C, hC, ?_⟩
  intro Q W j hQ hSep hjQ
  unfold heathBrownTraceBinMoment
  calc
    (∑ p ∈ heathBrownDifferenceBin W j,
        ‖heathBrownTracePolynomial cutoff Q (p.1 - p.2)‖ ^ 2) ≤
      ∑ _p ∈ heathBrownDifferenceBin W j,
        (C * (Q : ℝ) / (2 ^ j : ℕ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hbounds := heathBrownDifferenceBin_bounds hSep hp
      have hupper : |p.1 - p.2| ≤ (Q : ℝ) := by
        have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hjQ
        exact hbounds.2.le.trans hcast
      have honePow : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.one_le_pow j 2 (by omega))
      have hpoint := hTrace Q (p.1 - p.2) hQ
        (honePow.trans hbounds.1)
        hupper
      have hpowPos : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
      have habsPos : 0 < |p.1 - p.2| :=
        lt_of_lt_of_le hpowPos hbounds.1
      have hdenom :
          C * (Q : ℝ) / |p.1 - p.2| ≤
            C * (Q : ℝ) / (2 ^ j : ℕ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hpowPos
        · exact hbounds.1
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hpoint.trans hdenom) 2
    _ = ((heathBrownDifferenceBin W j).card : ℝ) *
        (C * (Q : ℝ) / (2 ^ j : ℕ)) ^ 2 := by simp

/-- Cardinality-summed form of the nonstationary bin estimate.  One power
of the dyadic displacement is spent counting separated neighbours and the
remaining inverse power is kept for the geometric bin sum. -/
theorem exists_heathBrownTraceBinMoment_near_card_bound
    (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) (W : Finset ℝ) (j : ℕ),
        0 < Q → IsSeparated 1 W → 2 ^ (j + 1) ≤ Q →
        heathBrownTraceBinMoment cutoff Q W j ≤
          4 * (W.card : ℝ) * C ^ 2 * (Q : ℝ) ^ 2 /
            ((2 ^ j : ℕ) : ℝ) := by
  obtain ⟨C, hC, hnear⟩ :=
    exists_heathBrownTraceBinMoment_near_bound cutoff
  refine ⟨C, hC, ?_⟩
  intro Q W j hQ hSep hjQ
  have hcardNat := heathBrownDifferenceBin_card_le W j hSep
  have hcard : ((heathBrownDifferenceBin W j).card : ℝ) ≤
      (W.card : ℝ) * (2 * 2 ^ (j + 1) : ℕ) := by
    exact_mod_cast hcardNat
  have hpowPos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  calc
    heathBrownTraceBinMoment cutoff Q W j ≤
        ((heathBrownDifferenceBin W j).card : ℝ) *
          (C * (Q : ℝ) / (2 ^ j : ℕ)) ^ 2 :=
      hnear Q W j hQ hSep hjQ
    _ ≤ ((W.card : ℝ) * (2 * 2 ^ (j + 1) : ℕ)) *
          (C * (Q : ℝ) / (2 ^ j : ℕ)) ^ 2 := by
      gcongr
    _ = 4 * (W.card : ℝ) * C ^ 2 * (Q : ℝ) ^ 2 /
          ((2 ^ j : ℕ) : ℝ) := by
      rw [pow_succ]
      push_cast
      field_simp
      ring

/-- Fixed-height dual length `ceil(2^j H / Q)`, with a nonempty fallback.
This is the literal reflected length in Montgomery--Vaughan (29.41). -/
def heathBrownFixedReflectionLength (Q H j : ℕ) : ℕ :=
  max 1 ((2 ^ j * H + Q - 1) / Q)

theorem heathBrownFixedReflectionLength_pos (Q H j : ℕ) :
    0 < heathBrownFixedReflectionLength Q H j := by
  unfold heathBrownFixedReflectionLength
  omega

/-- The corrected source schedule.  Bins below the polynomial scale retain
the Abel `2⁻ʲ` gain; genuinely stationary bins are reflected with their own
dual length; only the short transition between these regimes is estimated
trivially. -/
noncomputable def heathBrownTraceSourceBound
    (Cnear C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  (W.card : ℝ) * Q ^ 2 +
    ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ^ (j + 1) ≤ Q then
        4 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 /
          ((2 ^ j : ℕ) : ℝ)
      else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
        2 * (((Q : ℝ) * C /
            Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * (H : ℝ)) ^ 2 *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j)) +
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
            (heathBrownReflectionBinError q Q
              (heathBrownFixedReflectionLength Q H j) H
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
      else
        ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2

/-- The `heathBrownSourceNearSum` definition used by the source-facing construction in `HeathBrownReflection`. -/
noncomputable def heathBrownSourceNearSum
    (Cnear T : ℝ) (W : Finset ℝ) (Q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
    if 2 ^ (j + 1) ≤ Q then
      4 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 /
        ((2 ^ j : ℕ) : ℝ)
    else 0

/-- The `heathBrownSourceTransitionSum` definition used by the source-facing construction in `HeathBrownReflection`. -/
noncomputable def heathBrownSourceTransitionSum
    (T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
    if 2 ^ (j + 1) ≤ Q then 0
    else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then 0
    else ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2

/-- The `heathBrownSourceReflectedMainSum` definition used by the source-facing construction in `HeathBrownReflection`. -/
noncomputable def heathBrownSourceReflectedMainSum
    (C T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
    if 2 ^ (j + 1) ≤ Q then 0
    else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
      2 * (((Q : ℝ) * C /
          Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
          ((2 * (H : ℝ)) ^ 2 *
            heathBrownReflectionDyadicMoment W
              (heathBrownFixedReflectionLength Q H j))
    else 0

/-- The `heathBrownSourceReflectedErrorSum` definition used by the source-facing construction in `HeathBrownReflection`. -/
noncomputable def heathBrownSourceReflectedErrorSum
    (K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
    if 2 ^ (j + 1) ≤ Q then 0
    else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
      2 * ((heathBrownDifferenceBin W j).card : ℝ) *
        (heathBrownReflectionBinError q Q
          (heathBrownFixedReflectionLength Q H j) H
          (((2 ^ (j + 1) : ℕ) : ℝ))
          (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
    else 0

/-- Exact four-component decomposition of the corrected source schedule. -/
theorem heathBrownTraceSourceBound_eq_components
    (Cnear C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) :
    heathBrownTraceSourceBound Cnear C K L D q T W Q H =
      (W.card : ℝ) * Q ^ 2 +
        heathBrownSourceNearSum Cnear T W Q +
        heathBrownSourceTransitionSum T W Q H +
        heathBrownSourceReflectedMainSum C T W Q H +
        heathBrownSourceReflectedErrorSum K L D q T W Q H := by
  let f : ℕ → ℝ := fun j =>
    if 2 ^ (j + 1) ≤ Q then
      4 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 /
        ((2 ^ j : ℕ) : ℝ)
    else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
      2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
          ((2 * (H : ℝ)) ^ 2 * heathBrownReflectionDyadicMoment W
            (heathBrownFixedReflectionLength Q H j)) +
        2 * ((heathBrownDifferenceBin W j).card : ℝ) *
          (heathBrownReflectionBinError q Q
            (heathBrownFixedReflectionLength Q H j) H
            (((2 ^ (j + 1) : ℕ) : ℝ)) (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
    else ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2
  change (W.card : ℝ) * Q ^ 2 +
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), f j) = _
  have hsum :
      (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), f j) =
        heathBrownSourceNearSum Cnear T W Q +
        heathBrownSourceTransitionSum T W Q H +
        heathBrownSourceReflectedMainSum C T W Q H +
        heathBrownSourceReflectedErrorSum K L D q T W Q H := by
    unfold heathBrownSourceNearSum heathBrownSourceTransitionSum
      heathBrownSourceReflectedMainSum heathBrownSourceReflectedErrorSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f]
    by_cases hNear : 2 ^ (j + 1) ≤ Q
    · simp [hNear]
    · simp only [hNear, if_false]
      by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
      · simp [hStationary]
      · simp [hStationary]
  rw [hsum]
  ring

/-- The unrestricted trace moment satisfies the corrected three-way source
schedule.  Both analytic inputs are consumed here: finite Abel cancellation
for near bins and the complete quantitative smooth reflection for far bins.
-/
theorem heathBrownTraceMoment_le_source_bound
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ Cnear C K L D : ℝ,
      0 < Cnear ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {T : ℝ} {W : Finset ℝ} {Q H : ℕ},
        IsSeparated 1 W → InBaseInterval T W →
        0 < Q → 0 < H →
        heathBrownTraceMoment cutoff Q W ≤
          heathBrownTraceSourceBound Cnear C K L D q T W Q H := by
  obtain ⟨Cnear, hCnear, hNear⟩ :=
    exists_heathBrownTraceBinMoment_near_card_bound cutoff
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hReflect⟩ :=
    heathBrownTraceBinMoment_le_reflection cutoff q hq
  refine ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, ?_⟩
  intro T W Q H hSep hInterval hQ hH
  unfold heathBrownTraceSourceBound
  rw [heathBrownTraceMoment_eq_diagonal_add_offDiagonal,
    heathBrownTraceOffDiagonalMoment_eq_sum_bins hSep hInterval]
  apply add_le_add
  · exact heathBrownTraceDiagonal_le cutoff Q W
  · apply Finset.sum_le_sum
    intro j hj
    by_cases hNearScale : 2 ^ (j + 1) ≤ Q
    · rw [if_pos hNearScale]
      exact hNear Q W j hQ hSep hNearScale
    · rw [if_neg hNearScale]
      by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
      · rw [if_pos hStationary]
        have hHeightLower : (1 : ℝ) ≤ H := by exact_mod_cast hH
        have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
          have hCast : (2 : ℝ) * H ≤ ((2 ^ j : ℕ) : ℝ) := by
            exact_mod_cast hStationary.2
          linarith
        exact hReflect hSep hStationary.1 hHeightLower hHeightUpper hQ
          (heathBrownFixedReflectionLength_pos Q H j)
      · rw [if_neg hStationary]
        exact heathBrownTraceBinMoment_le_card_mul cutoff Q W j

/-- The transition branch of the corrected schedule contains only
`O(H)` neighbours per ordinate. -/
theorem heathBrownDifferenceBin_card_le_transition
    (W : Finset ℝ) (Q H j : ℕ) (hQ : 4 ≤ Q)
    (hSep : IsSeparated 1 W) (hNotNear : ¬ 2 ^ (j + 1) ≤ Q)
    (hNotStationary : ¬ (2 ≤ j ∧ 2 * H ≤ 2 ^ j)) :
    (heathBrownDifferenceBin W j).card ≤ 8 * W.card * H := by
  have hj : 2 ≤ j := by
    by_contra hj
    have hjle : j ≤ 1 := by omega
    interval_cases j <;> norm_num at hNotNear ⊢ <;> omega
  have hpow : 2 ^ j ≤ 2 * H := by
    have hnot : ¬ 2 * H ≤ 2 ^ j := by
      intro h
      exact hNotStationary ⟨hj, h⟩
    omega
  calc
    (heathBrownDifferenceBin W j).card ≤
        W.card * (2 * 2 ^ (j + 1)) :=
      heathBrownDifferenceBin_card_le W j hSep
    _ = W.card * (4 * 2 ^ j) := by rw [pow_succ]; ring
    _ ≤ W.card * (4 * (2 * H)) := by gcongr
    _ = 8 * W.card * H := by ring

/-- Any subfamily of the inverse dyadic series has total mass at most two.
-/
theorem sum_if_div_two_pow_le_two_mul
    (A : ℝ) (hA : 0 ≤ A) (P : ℕ → Prop) [DecidablePred P] (L : ℕ) :
    (∑ j ∈ Finset.range L,
      if P j then A / ((2 ^ j : ℕ) : ℝ) else 0) ≤ 2 * A := by
  calc
    (∑ j ∈ Finset.range L,
        if P j then A / ((2 ^ j : ℕ) : ℝ) else 0) ≤
      ∑ j ∈ Finset.range L, A * ((1 / 2 : ℝ) ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hP : P j
        · rw [if_pos hP]
          have hinv : (((2 ^ j : ℕ) : ℝ))⁻¹ = (1 / 2 : ℝ) ^ j := by
            push_cast
            rw [← inv_pow]
            norm_num [one_div]
          rw [div_eq_mul_inv, hinv]
        · rw [if_neg hP]
          positivity
    _ = A * (∑ j ∈ Finset.range L, (1 / 2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ A * 2 := by
      gcongr
      exact sum_geometric_two_le L
    _ = 2 * A := by ring

theorem heathBrownSourceNearSum_le
    (Cnear T : ℝ) (W : Finset ℝ) (Q : ℕ) :
    heathBrownSourceNearSum Cnear T W Q ≤
      8 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 := by
  unfold heathBrownSourceNearSum
  let A : ℝ := 4 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hgeom := sum_if_div_two_pow_le_two_mul A hA
    (fun j => 2 ^ (j + 1) ≤ Q)
    (Nat.log 2 (Nat.floor T) + 1)
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        if 2 ^ (j + 1) ≤ Q then
          4 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 /
            ((2 ^ j : ℕ) : ℝ)
        else 0) ≤ 2 * A := hgeom
    _ = 8 * (W.card : ℝ) * Cnear ^ 2 * (Q : ℝ) ^ 2 := by
      dsimp only [A]
      ring

theorem heathBrownSourceTransitionSum_le
    (T : ℝ) (W : Finset ℝ) (Q H : ℕ) (hQ : 4 ≤ Q)
    (hSep : IsSeparated 1 W) :
    heathBrownSourceTransitionSum T W Q H ≤
      ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        (8 * (W.card : ℝ) * H * (Q : ℝ) ^ 2) := by
  unfold heathBrownSourceTransitionSum
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        if 2 ^ (j + 1) ≤ Q then 0
        else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then 0
        else ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2) ≤
      ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        8 * (W.card : ℝ) * H * (Q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hNear : 2 ^ (j + 1) ≤ Q
      · simp [hNear]
        positivity
      · simp only [hNear, if_false]
        by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
        · simp [hStationary]
          positivity
        · rw [if_neg hStationary]
          have hcardNat := heathBrownDifferenceBin_card_le_transition
            W Q H j hQ hSep hNear hStationary
          have hcard : ((heathBrownDifferenceBin W j).card : ℝ) ≤
              8 * (W.card : ℝ) * H := by exact_mod_cast hcardNat
          exact mul_le_mul_of_nonneg_right hcard (sq_nonneg (Q : ℝ))
    _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
        (8 * (W.card : ℝ) * H * (Q : ℝ) ^ 2) := by simp

/-- Source-facing insertion of the corrected trace schedule into all three
exact localization pieces. -/
theorem heathBrownCoefficientOneMoment_le_source_bound
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ Cnear C K L D : ℝ,
      0 < Cnear ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownCoefficientOneMoment N W ≤
          3 * (heathBrownTraceSourceBound Cnear C K L D q T W
                (gmSourceLeftScale N) H +
            heathBrownTraceSourceBound Cnear C K L D q T W N H +
            heathBrownTraceSourceBound Cnear C K L D q T W
              (gmSourceRightScale N) H) := by
  obtain ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, hTrace⟩ :=
    heathBrownTraceMoment_le_source_bound cutoff q hq
  refine ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, ?_⟩
  intro N H T W hN hH hSep hInterval
  have hLeftPos : 0 < gmSourceLeftScale N := by
    unfold gmSourceLeftScale
    omega
  have hMiddlePos : 0 < N := by omega
  have hRightPos : 0 < gmSourceRightScale N := by
    unfold gmSourceRightScale
    omega
  have hLeft := hTrace hSep hInterval hLeftPos hH
  have hMiddle := hTrace hSep hInterval hMiddlePos hH
  have hRight := hTrace hSep hInterval hRightPos hH
  have hEntry := sourceCoefficientOne_differenceMoment_le_three_trace
    cutoff N W hN
  calc
    heathBrownCoefficientOneMoment N W ≤
        3 * (heathBrownTraceMoment cutoff (gmSourceLeftScale N) W +
          heathBrownTraceMoment cutoff N W +
          heathBrownTraceMoment cutoff (gmSourceRightScale N) W) := by
      simpa only [heathBrownCoefficientOneMoment] using hEntry
    _ ≤ 3 * (heathBrownTraceSourceBound Cnear C K L D q T W
            (gmSourceLeftScale N) H +
          heathBrownTraceSourceBound Cnear C K L D q T W N H +
          heathBrownTraceSourceBound Cnear C K L D q T W
            (gmSourceRightScale N) H) := by
      gcongr

/-- The fully explicit right side of the reflected trace recurrence for one
choice of binwise heights and dual cutoffs. -/
noncomputable def heathBrownTraceScheduleBound
    (C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q : ℕ)
    (H : ℕ → ℝ) (M : ℕ → ℕ) : ℝ :=
  (W.card : ℝ) * Q ^ 2 +
    ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ≤ j then
        2 * (((Q : ℝ) * C /
            Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * H j) ^ 2 * heathBrownReflectionDyadicMoment W (M j)) +
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
            (heathBrownReflectionBinError q Q (M j) (H j)
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
      else
        ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2

/-- Exact finite reflected recurrence for one unrestricted smooth trace
moment.  The schedule supplies a common integration height and reflected
cutoff for each genuine dyadic displacement bin.  The two tiny bins are
retained with their elementary bounds; every other bin invokes the actual
complete smooth-reflection theorem and its coefficient-one recursive
moments. -/
theorem heathBrownTraceMoment_le_reflection_schedule
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {T : ℝ} {W : Finset ℝ} {Q : ℕ}
          (H : ℕ → ℝ) (M : ℕ → ℕ),
        IsSeparated 1 W → InBaseInterval T W → 0 < Q →
        (∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          2 ≤ j →
            1 ≤ H j ∧ H j ≤ ((2 ^ j : ℕ) : ℝ) / 2 ∧ 0 < M j) →
        heathBrownTraceMoment cutoff Q W ≤
          heathBrownTraceScheduleBound C K L D q T W Q H M := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hBin⟩ :=
    heathBrownTraceBinMoment_le_reflection cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro T W Q H M hSep hInterval hQ hSchedule
  unfold heathBrownTraceScheduleBound
  have hBins := heathBrownTraceOffDiagonalMoment_eq_sum_bins
    hSep hInterval cutoff Q
  rw [heathBrownTraceMoment_eq_diagonal_add_offDiagonal, hBins]
  apply add_le_add
  · exact heathBrownTraceDiagonal_le cutoff Q W
  · apply Finset.sum_le_sum
    intro j hj
    by_cases hjLarge : 2 ≤ j
    · rw [if_pos hjLarge]
      have hData := hSchedule j hj hjLarge
      exact hBin hSep hjLarge hData.1 hData.2.1 hQ hData.2.2
    · rw [if_neg hjLarge]
      exact heathBrownTraceBinMoment_le_card_mul cutoff Q W j

/-- Source-facing reflected recurrence for the literal coefficient-one block
`(N,2N]`.  The exact three-piece localization is consumed first, and each of
its unrestricted trace moments is then estimated by the same complete
Poisson/reflection constants.  Thus this theorem starts with the original
Heath--Brown moment rather than an independently supplied trace quantity. -/
theorem heathBrownCoefficientOneMoment_le_reflection_schedule
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N : ℕ} {T : ℝ} {W : Finset ℝ}
          (H : ℕ → ℝ) (MLeft MMiddle MRight : ℕ → ℕ),
        30 ≤ N → IsSeparated 1 W → InBaseInterval T W →
        (∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          2 ≤ j →
            1 ≤ H j ∧ H j ≤ ((2 ^ j : ℕ) : ℝ) / 2 ∧
              0 < MLeft j ∧ 0 < MMiddle j ∧ 0 < MRight j) →
        heathBrownCoefficientOneMoment N W ≤
          3 *
            (heathBrownTraceScheduleBound C K L D q T W
                (gmSourceLeftScale N) H MLeft +
              heathBrownTraceScheduleBound C K L D q T W
                N H MMiddle +
              heathBrownTraceScheduleBound C K L D q T W
                (gmSourceRightScale N) H MRight) := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hTrace⟩ :=
    heathBrownTraceMoment_le_reflection_schedule cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro N T W H MLeft MMiddle MRight hN hSep hInterval hSchedule
  have hLeftPos : 0 < gmSourceLeftScale N := by
    unfold gmSourceLeftScale
    omega
  have hMiddlePos : 0 < N := by omega
  have hRightPos : 0 < gmSourceRightScale N := by
    unfold gmSourceRightScale
    omega
  have hLeftSchedule : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      2 ≤ j →
        1 ≤ H j ∧ H j ≤ ((2 ^ j : ℕ) : ℝ) / 2 ∧
          0 < MLeft j := by
    intro j hj hj2
    have h := hSchedule j hj hj2
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hMiddleSchedule : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      2 ≤ j →
        1 ≤ H j ∧ H j ≤ ((2 ^ j : ℕ) : ℝ) / 2 ∧
          0 < MMiddle j := by
    intro j hj hj2
    have h := hSchedule j hj hj2
    exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  have hRightSchedule : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      2 ≤ j →
        1 ≤ H j ∧ H j ≤ ((2 ^ j : ℕ) : ℝ) / 2 ∧
          0 < MRight j := by
    intro j hj hj2
    have h := hSchedule j hj hj2
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩
  have hLeft := hTrace H MLeft hSep hInterval hLeftPos hLeftSchedule
  have hMiddle := hTrace H MMiddle hSep hInterval hMiddlePos hMiddleSchedule
  have hRight := hTrace H MRight hSep hInterval hRightPos hRightSchedule
  have hEntry := sourceCoefficientOne_differenceMoment_le_three_trace
    cutoff N W hN
  calc
    heathBrownCoefficientOneMoment N W ≤
        3 * (heathBrownTraceMoment cutoff (gmSourceLeftScale N) W +
          heathBrownTraceMoment cutoff N W +
          heathBrownTraceMoment cutoff (gmSourceRightScale N) W) := by
      simpa only [heathBrownCoefficientOneMoment] using hEntry
    _ ≤ 3 *
          (heathBrownTraceScheduleBound C K L D q T W
              (gmSourceLeftScale N) H MLeft +
            heathBrownTraceScheduleBound C K L D q T W
              N H MMiddle +
            heathBrownTraceScheduleBound C K L D q T W
              (gmSourceRightScale N) H MRight) := by
      gcongr

/-! ## Source hybrid reflection schedule -/

/-- Common terminal dual length for all bins below height `T`. -/
noncomputable def heathBrownCommonReflectionLength (Q H : ℕ) (T : ℝ) : ℕ :=
  max 1 ((Nat.floor T * H + Q - 1) / Q)

/-- Dyadic terminal scale which contains every reflected prefix. -/
noncomputable def heathBrownReflectionTargetScale (Q H : ℕ) (T : ℝ) : ℕ :=
  2 ^ Nat.clog 2 (heathBrownCommonReflectionLength Q H T)

theorem heathBrownFixedReflectionLength_lower
    (Q H j : ℕ) (hQ : 0 < Q) :
    2 ^ j * H ≤ Q * heathBrownFixedReflectionLength Q H j := by
  let A : ℕ := 2 ^ j * H
  have hCeil : A ≤ Q * CeilDiv.ceilDiv A Q := by
    simpa only [nsmul_eq_mul] using
      (le_smul_ceilDiv (b := A) (a := Q) hQ)
  have hCeilLe : CeilDiv.ceilDiv A Q ≤
      max 1 (CeilDiv.ceilDiv A Q) := le_max_right _ _
  have hMul := Nat.mul_le_mul_left Q hCeilLe
  unfold heathBrownFixedReflectionLength
  rw [← Nat.ceilDiv_eq_add_pred_div]
  exact hCeil.trans hMul

theorem heathBrownFixedReflectionLength_upper
    (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H) :
    Q * heathBrownFixedReflectionLength Q H j ≤ 2 ^ j * H + Q := by
  let A : ℕ := 2 ^ j * H
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCeilPos : 0 < CeilDiv.ceilDiv A Q := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos
    · omega
    · exact hQ
  have hMax : max 1 (CeilDiv.ceilDiv A Q) =
      CeilDiv.ceilDiv A Q := max_eq_right hCeilPos
  have hDiv : Q * ((A + Q - 1) / Q) ≤ A + Q - 1 :=
    Nat.mul_div_le _ _
  unfold heathBrownFixedReflectionLength
  change Q * max 1 ((A + Q - 1) / Q) ≤ A + Q
  rw [← Nat.ceilDiv_eq_add_pred_div, hMax,
    Nat.ceilDiv_eq_add_pred_div]
  exact hDiv.trans (Nat.sub_le _ _)

/-- Real form of the two ceiling inequalities for the fixed reflection
length.  Keeping the product `Q*M` intact is the convenient source form for
the omitted-frequency denominator. -/
theorem heathBrownFixedReflectionLength_bounds_real
    (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H) :
    (((2 ^ j : ℕ) : ℝ) * H ≤
        (Q : ℝ) * heathBrownFixedReflectionLength Q H j) ∧
      (Q : ℝ) * heathBrownFixedReflectionLength Q H j ≤
        ((2 ^ j : ℕ) : ℝ) * H + Q := by
  constructor
  · exact_mod_cast heathBrownFixedReflectionLength_lower Q H j hQ
  · exact_mod_cast heathBrownFixedReflectionLength_upper Q H j hQ hH

/-- The ceiling length itself is bounded by the physical dual length plus
one. -/
theorem heathBrownFixedReflectionLength_cast_le
    (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H) :
    (heathBrownFixedReflectionLength Q H j : ℝ) ≤
      (((2 ^ j : ℕ) : ℝ) * H) / Q + 1 := by
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hUpper := (heathBrownFixedReflectionLength_bounds_real Q H j hQ hH).2
  calc
    (heathBrownFixedReflectionLength Q H j : ℝ) =
        ((Q : ℝ) * heathBrownFixedReflectionLength Q H j) / Q := by
      field_simp
    _ ≤ ((((2 ^ j : ℕ) : ℝ) * H) + Q) / Q := by
      exact div_le_div_of_nonneg_right hUpper hQReal.le
    _ = (((2 ^ j : ℕ) : ℝ) * H) / Q + 1 := by
      field_simp

/-- The common terminal ceiling overshoots `floor(T) H / Q` by at most one
source block. -/
theorem heathBrownCommonReflectionLength_upper
    (Q H : ℕ) (T : ℝ) (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T) :
    Q * heathBrownCommonReflectionLength Q H T ≤
      Nat.floor T * H + Q := by
  let A : ℕ := Nat.floor T * H
  have hFloor : 0 < Nat.floor T := Nat.floor_pos.mpr hT
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCeilPos : 0 < CeilDiv.ceilDiv A Q := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos
    · omega
    · exact hQ
  have hMax : max 1 (CeilDiv.ceilDiv A Q) = CeilDiv.ceilDiv A Q :=
    max_eq_right hCeilPos
  have hDiv : Q * ((A + Q - 1) / Q) ≤ A + Q - 1 := Nat.mul_div_le _ _
  unfold heathBrownCommonReflectionLength
  change Q * max 1 ((A + Q - 1) / Q) ≤ A + Q
  rw [← Nat.ceilDiv_eq_add_pred_div, hMax, Nat.ceilDiv_eq_add_pred_div]
  exact hDiv.trans (Nat.sub_le _ _)

/-- Matching lower bound for the common terminal ceiling. -/
theorem heathBrownCommonReflectionLength_lower
    (Q H : ℕ) (T : ℝ) (hQ : 0 < Q) :
    Nat.floor T * H ≤ Q * heathBrownCommonReflectionLength Q H T := by
  let A : ℕ := Nat.floor T * H
  have hCeil : A ≤ Q * CeilDiv.ceilDiv A Q := by
    simpa only [nsmul_eq_mul] using
      (le_smul_ceilDiv (b := A) (a := Q) hQ)
  have hCeilLe : CeilDiv.ceilDiv A Q ≤ max 1 (CeilDiv.ceilDiv A Q) :=
    le_max_right _ _
  have hMul := Nat.mul_le_mul_left Q hCeilLe
  unfold heathBrownCommonReflectionLength
  rw [← Nat.ceilDiv_eq_add_pred_div]
  exact hCeil.trans hMul

/-- Source-scale majorant for all three errors in one reflected displacement
bin.  The first term uses the ceiling upper bound, while the
omitted-frequency term uses the matching lower bound on `Q*M`. -/
theorem heathBrownReflectionBinError_fixed_le
    (K L D : ℝ) (q Q H j : ℕ)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hQ : 0 < Q) (hH : 0 < H) :
    heathBrownReflectionBinError q Q
        (heathBrownFixedReflectionLength Q H j) H
        (((2 ^ (j + 1) : ℕ) : ℝ)) (((2 ^ j : ℕ) : ℝ)) K L D ≤
      K / Q * ((((2 ^ j : ℕ) : ℝ) * H) + Q) ^ 2 *
          (H : ℝ) ^ (1 - (q : ℝ)) +
        L / Q * (1 + 2 * ((2 ^ j : ℕ) : ℝ)) ^ (q + 2) /
          ((((2 ^ j : ℕ) : ℝ) * H) ^ q) +
        (Q : ℝ) * D / (((2 ^ j : ℕ) : ℝ) ^ q) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  let M : ℕ := heathBrownFixedReflectionLength Q H j
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  have hX : 0 < X := by dsimp only [X]; positivity
  have hM : 0 < M := by
    dsimp only [M]
    exact heathBrownFixedReflectionLength_pos Q H j
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hBounds := heathBrownFixedReflectionLength_bounds_real Q H j hQ hH
  have hQMNonneg : 0 ≤ (Q : ℝ) * M := by positivity
  have hXHNonneg : 0 ≤ X * H := by positivity
  have hQMsq : ((Q : ℝ) * M) ^ 2 ≤ (X * H + Q) ^ 2 := by
    exact pow_le_pow_left₀ hQMNonneg hBounds.2 2
  have hFirst :
      (Q : ℝ) * K * (M : ℝ) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) ≤
        K / Q * (X * H + Q) ^ 2 *
          (H : ℝ) ^ (1 - (q : ℝ)) := by
    have hPowH : 0 ≤ (H : ℝ) ^ (1 - (q : ℝ)) :=
      Real.rpow_nonneg hHReal.le _
    have hCore : (Q : ℝ) * K * (M : ℝ) ^ 2 ≤
        K / Q * (X * H + Q) ^ 2 := by
      rw [show K / (Q : ℝ) * (X * H + Q) ^ 2 =
          (K * (X * H + Q) ^ 2) / Q by
        field_simp]
      apply (le_div_iff₀ hQReal).2
      calc
        (Q : ℝ) * K * (M : ℝ) ^ 2 * Q =
            K * (((Q : ℝ) * M) ^ 2) := by ring
        _ ≤ K * (X * H + Q) ^ 2 := by gcongr
    exact mul_le_mul_of_nonneg_right hCore hPowH
  have hProductPow : (X * H) ^ q ≤ ((Q : ℝ) * M) ^ q :=
    pow_le_pow_left₀ hXHNonneg hBounds.1 q
  have hSecond :
      (Q : ℝ) * L * (1 + ((2 ^ (j + 1) : ℕ) : ℝ)) ^ (q + 2) /
          ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) ≤
        L / Q * (1 + 2 * X) ^ (q + 2) / ((X * H) ^ q) := by
    have hDenLeft : 0 < (Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q := by positivity
    have hDenRight : 0 < (X * H) ^ q := by positivity
    have hNumerNonneg : 0 ≤ L * (1 + 2 * X) ^ (q + 2) := by positivity
    have hRewritePow : (((2 ^ (j + 1) : ℕ) : ℝ)) = 2 * X := by
      dsimp only [X]
      rw [pow_succ]
      norm_num
      ring
    rw [hRewritePow]
    have hExact :
        (Q : ℝ) * L * (1 + 2 * X) ^ (q + 2) /
            ((Q : ℝ) ^ (q + 2) * (M : ℝ) ^ q) =
          (L / Q * (1 + 2 * X) ^ (q + 2)) /
            (((Q : ℝ) * M) ^ q) := by
      rw [mul_pow]
      field_simp
      ring
    rw [hExact]
    exact div_le_div_of_nonneg_left (by positivity) hDenRight hProductPow
  dsimp only [heathBrownReflectionBinError, X, M]
  exact add_le_add (add_le_add hFirst hSecond) le_rfl

/-- Uniform version of the preceding bin majorant on the physical range.
All displacement dependence is replaced by the slab height `T`, while the
stationary condition supplies the common denominator `H^q`. -/
theorem heathBrownReflectionBinError_fixed_le_uniform
    (K L D : ℝ) (q Q H j : ℕ) (T : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hQ : 0 < Q) (hH : 0 < H)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hReflect : 2 ≤ j ∧ 2 * H ≤ 2 ^ j) :
    heathBrownReflectionBinError q Q
        (heathBrownFixedReflectionLength Q H j) H
        (((2 ^ (j + 1) : ℕ) : ℝ)) (((2 ^ j : ℕ) : ℝ)) K L D ≤
      K / Q * (T * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) +
        L / Q * (1 + 2 * T) ^ (q + 2) / ((H : ℝ) ^ q) +
        (Q : ℝ) * D / ((H : ℝ) ^ q) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  have hFloorNe : Nat.floor T ≠ 0 := by
    intro hZero
    rw [hZero] at hj
    norm_num at hj
    omega
  have hFloorPos : 0 < Nat.floor T := Nat.pos_of_ne_zero hFloorNe
  have hTOne : 1 ≤ T := Nat.floor_pos.mp hFloorPos
  have hTNonneg : 0 ≤ T := zero_le_one.trans hTOne
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hjLe : j ≤ Nat.log 2 (Nat.floor T) := by
    rw [Finset.mem_range] at hj
    omega
  have hXLeFloor : 2 ^ j ≤ Nat.floor T := by
    calc
      2 ^ j ≤ 2 ^ Nat.log 2 (Nat.floor T) :=
        Nat.pow_le_pow_right (by omega) hjLe
      _ ≤ Nat.floor T := Nat.pow_log_le_self 2 hFloorNe
  have hXLeT : X ≤ T := by
    calc
      X ≤ (Nat.floor T : ℝ) := by
        dsimp only [X]
        exact_mod_cast hXLeFloor
      _ ≤ T := Nat.floor_le hTNonneg
  have hHLeXNat : H ≤ 2 ^ j := by omega
  have hHLeX : (H : ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast hHLeXNat
  have hXHLower : (H : ℝ) ≤ X * H := by
    have hOneLeX : (1 : ℝ) ≤ X := by
      dsimp only [X]
      exact_mod_cast (Nat.one_le_pow j 2 (by omega))
    nlinarith
  have hFirstBase : X * H + Q ≤ T * H + Q := by
    gcongr
  have hFirstSq : (X * H + Q) ^ 2 ≤ (T * H + Q) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hFirstBase 2
  have hNumerBase : 1 + 2 * X ≤ 1 + 2 * T := by linarith
  have hNumerPow : (1 + 2 * X) ^ (q + 2) ≤
      (1 + 2 * T) ^ (q + 2) := by
    exact pow_le_pow_left₀ (by positivity) hNumerBase (q + 2)
  have hDenPow : (H : ℝ) ^ q ≤ (X * H) ^ q :=
    pow_le_pow_left₀ hHReal.le hXHLower q
  have hXDenPow : (H : ℝ) ^ q ≤ X ^ q :=
    pow_le_pow_left₀ hHReal.le hHLeX q
  have hRaw := heathBrownReflectionBinError_fixed_le K L D q Q H j
    hK hL hQ hH
  have hPowH : 0 ≤ (H : ℝ) ^ (1 - (q : ℝ)) :=
    Real.rpow_nonneg hHReal.le _
  have hFirst :
      K / Q * (X * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) ≤
        K / Q * (T * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) := by
    gcongr
  have hSecond :
      L / Q * (1 + 2 * X) ^ (q + 2) / ((X * H) ^ q) ≤
        L / Q * (1 + 2 * T) ^ (q + 2) / ((H : ℝ) ^ q) := by
    calc
      _ ≤ L / Q * (1 + 2 * T) ^ (q + 2) / ((X * H) ^ q) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hDenPow
  have hThird :
      (Q : ℝ) * D / X ^ q ≤ (Q : ℝ) * D / (H : ℝ) ^ q := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hXDenPow
  dsimp only [X] at hRaw hFirst hSecond hThird
  exact hRaw.trans (add_le_add (add_le_add hFirst hSecond) hThird)

/-- Common physical-range majorant for one reflected-bin error. -/
noncomputable def heathBrownUniformReflectionError
    (K L D : ℝ) (q Q H : ℕ) (T : ℝ) : ℝ :=
  K / Q * (T * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) +
    L / Q * (1 + 2 * T) ^ (q + 2) / ((H : ℝ) ^ q) +
    (Q : ℝ) * D / ((H : ℝ) ^ q)

/-- The complete three-family analytic remainder retained by the hybrid
schedule. -/
noncomputable def heathBrownHybridErrorSum
    (K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
    if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
      2 * ((heathBrownDifferenceBin W j).card : ℝ) *
        (heathBrownReflectionBinError q Q
          (heathBrownFixedReflectionLength Q H j) H
          (((2 ^ (j + 1) : ℕ) : ℝ))
          (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
    else 0

/-- A displacement bin occurring in the exact finite partition has dyadic
endpoint at most `floor T`. -/
theorem two_pow_le_floor_of_mem_difference_range
    {T : ℝ} {j : ℕ}
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    2 ^ j ≤ Nat.floor T := by
  have hFloor : Nat.floor T ≠ 0 := by
    intro hZero
    rw [hZero] at hj
    norm_num at hj
    omega
  have hjLe : j ≤ Nat.log 2 (Nat.floor T) := by
    rw [Finset.mem_range] at hj
    omega
  calc
    2 ^ j ≤ 2 ^ Nat.log 2 (Nat.floor T) :=
      Nat.pow_le_pow_right (by omega) hjLe
    _ ≤ Nat.floor T := Nat.pow_log_le_self 2 hFloor

/-- Summing the complete reflection remainder over the exact dyadic
partition costs one logarithm and the separated-pair factor `8 |W| T`.
No error family is omitted. -/
theorem heathBrownHybridErrorSum_le_uniform
    (K L D : ℝ) (q Q H : ℕ) (T : ℝ) (W : Finset ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) :
    heathBrownHybridErrorSum K L D q T W Q H ≤
      (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
        (8 * (W.card : ℝ) * T *
          (heathBrownUniformReflectionError K L D q Q H T) ^ 2) := by
  have hTNonneg : 0 ≤ T := zero_le_one.trans hT
  have hErrNonneg : 0 ≤ heathBrownUniformReflectionError K L D q Q H T := by
    unfold heathBrownUniformReflectionError
    positivity
  unfold heathBrownHybridErrorSum
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
            (heathBrownReflectionBinError q Q
              (heathBrownFixedReflectionLength Q H j) H
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
        else 0) ≤
      ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
        8 * (W.card : ℝ) * T *
          (heathBrownUniformReflectionError K L D q Q H T) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hReflect : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
      · rw [if_pos hReflect]
        have hErr := heathBrownReflectionBinError_fixed_le_uniform
          K L D q Q H j T hK hL hD hQ hH hj hReflect
        have hRawNonneg : 0 ≤
            heathBrownReflectionBinError q Q
              (heathBrownFixedReflectionLength Q H j) H
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D := by
          unfold heathBrownReflectionBinError
          positivity
        have hErrSq :
            (heathBrownReflectionBinError q Q
              (heathBrownFixedReflectionLength Q H j) H
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 ≤
              (heathBrownUniformReflectionError K L D q Q H T) ^ 2 := by
          apply pow_le_pow_left₀ hRawNonneg
          simpa only [heathBrownUniformReflectionError] using hErr
        have hCardNat := heathBrownDifferenceBin_card_le W j hSep
        have hPowFloor := two_pow_le_floor_of_mem_difference_range hj hReflect.1
        have hPowT : (((2 ^ j : ℕ) : ℝ)) ≤ T := by
          calc
            (((2 ^ j : ℕ) : ℝ)) ≤ (Nat.floor T : ℝ) := by
              exact_mod_cast hPowFloor
            _ ≤ T := Nat.floor_le hTNonneg
        have hCardReal : ((heathBrownDifferenceBin W j).card : ℝ) ≤
            (W.card : ℝ) * (4 * T) := by
          calc
            ((heathBrownDifferenceBin W j).card : ℝ) ≤
                (W.card : ℝ) * (2 * (((2 ^ (j + 1) : ℕ) : ℝ))) := by
              exact_mod_cast hCardNat
            _ = (W.card : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ))) := by
              have hPowCast :
                  2 * (((2 ^ (j + 1) : ℕ) : ℝ)) =
                    4 * (((2 ^ j : ℕ) : ℝ)) := by
                rw [pow_succ]
                norm_num
                ring
              rw [hPowCast]
            _ ≤ (W.card : ℝ) * (4 * T) := by gcongr
        calc
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (heathBrownReflectionBinError q Q
                (heathBrownFixedReflectionLength Q H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 ≤
            2 * ((W.card : ℝ) * (4 * T)) *
              (heathBrownUniformReflectionError K L D q Q H T) ^ 2 := by
                gcongr
          _ = 8 * (W.card : ℝ) * T *
              (heathBrownUniformReflectionError K L D q Q H T) ^ 2 := by ring
      · rw [if_neg hReflect]
        positivity
    _ = (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
        (8 * (W.card : ℝ) * T *
          (heathBrownUniformReflectionError K L D q Q H T) ^ 2) := by
      simp

/-- Every reflected bin length is bounded by the common terminal length. -/
theorem heathBrownFixedReflectionLength_le_common
    {T : ℝ} {j Q H : ℕ}
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hjTwo : 2 ≤ j) :
    heathBrownFixedReflectionLength Q H j ≤
      heathBrownCommonReflectionLength Q H T := by
  have hPow := two_pow_le_floor_of_mem_difference_range hj hjTwo
  unfold heathBrownFixedReflectionLength heathBrownCommonReflectionLength
  apply max_le_max_left
  apply Nat.div_le_div_right
  gcongr

/-- The stationary main coefficient loses only one power of the fixed
height after using `2H ≤ 2^j`. -/
theorem heathBrown_reflection_main_coefficient_le
    (C : ℝ) (Q H j : ℕ) (hH : 0 < H) (hReflect : 2 * H ≤ 2 ^ j) :
    2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
        (2 * (H : ℝ)) ^ 2 ≤
      4 * (Q : ℝ) ^ 2 * C ^ 2 * H := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hHeight : 2 * (H : ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast hReflect
  have hRatio : (H : ℝ) ^ 2 / X ≤ (H : ℝ) / 2 := by
    rw [div_le_iff₀ hXPos]
    have hMul := mul_le_mul_of_nonneg_left hHeight
      (show (0 : ℝ) ≤ (H : ℝ) / 2 by positivity)
    nlinarith
  calc
    2 * (((Q : ℝ) * C / Real.sqrt X) ^ 2) *
        (2 * (H : ℝ)) ^ 2 =
      8 * (Q : ℝ) ^ 2 * C ^ 2 * ((H : ℝ) ^ 2 / X) := by
        rw [div_pow, Real.sq_sqrt hXPos.le]
        field_simp
        ring
    _ ≤ 8 * (Q : ℝ) ^ 2 * C ^ 2 * ((H : ℝ) / 2) := by
      gcongr
    _ = 4 * (Q : ℝ) ^ 2 * C ^ 2 * H := by ring

/-- Exact finite schedule which reflects precisely the stationary bins
`2H ≤ 2^j`; all remaining bins retain their elementary cardinality bound.
This is the source-faithful alternative to reflecting every bin. -/
noncomputable def heathBrownTraceHybridBound
    (C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  (W.card : ℝ) * Q ^ 2 +
    ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
        2 * (((Q : ℝ) * C /
            Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * (H : ℝ)) ^ 2 *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j)) +
          2 * ((heathBrownDifferenceBin W j).card : ℝ) *
            (heathBrownReflectionBinError q Q
              (heathBrownFixedReflectionLength Q H j) H
              (((2 ^ (j + 1) : ℕ) : ℝ))
              (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
      else
        ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2

/-- The actual smooth trace moment satisfies the hybrid source schedule. -/
theorem heathBrownTraceMoment_le_hybrid
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {T : ℝ} {W : Finset ℝ} {Q H : ℕ},
        IsSeparated 1 W → InBaseInterval T W →
        0 < Q → 0 < H →
        heathBrownTraceMoment cutoff Q W ≤
          heathBrownTraceHybridBound C K L D q T W Q H := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hBin⟩ :=
    heathBrownTraceBinMoment_le_reflection cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro T W Q H hSep hInterval hQ hH
  unfold heathBrownTraceHybridBound
  rw [heathBrownTraceMoment_eq_diagonal_add_offDiagonal,
    heathBrownTraceOffDiagonalMoment_eq_sum_bins hSep hInterval]
  apply add_le_add
  · exact heathBrownTraceDiagonal_le cutoff Q W
  · apply Finset.sum_le_sum
    intro j hj
    by_cases hReflect : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
    · rw [if_pos hReflect]
      have hHeightLower : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hHeightUpper : (H : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / 2 := by
        have hCast : (2 * H : ℕ) ≤ 2 ^ j := hReflect.2
        have hCastReal : (2 : ℝ) * H ≤ ((2 ^ j : ℕ) : ℝ) := by
          exact_mod_cast hCast
        linarith
      exact hBin hSep hReflect.1 hHeightLower hHeightUpper hQ
        (heathBrownFixedReflectionLength_pos Q H j)
    · rw [if_neg hReflect]
      exact heathBrownTraceBinMoment_le_card_mul cutoff Q W j

/-- Source-facing coefficient-one recurrence with the hybrid schedule
inserted into all three exact localization pieces. -/
theorem heathBrownCoefficientOneMoment_le_hybrid
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownCoefficientOneMoment N W ≤
          3 * (heathBrownTraceHybridBound C K L D q T W
                (gmSourceLeftScale N) H +
            heathBrownTraceHybridBound C K L D q T W N H +
            heathBrownTraceHybridBound C K L D q T W
              (gmSourceRightScale N) H) := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hTrace⟩ :=
    heathBrownTraceMoment_le_hybrid cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro N H T W hN hH hSep hInterval
  have hLeftPos : 0 < gmSourceLeftScale N := by
    unfold gmSourceLeftScale
    omega
  have hMiddlePos : 0 < N := by omega
  have hRightPos : 0 < gmSourceRightScale N := by
    unfold gmSourceRightScale
    omega
  have hLeft := hTrace hSep hInterval hLeftPos hH
  have hMiddle := hTrace hSep hInterval hMiddlePos hH
  have hRight := hTrace hSep hInterval hRightPos hH
  have hEntry := sourceCoefficientOne_differenceMoment_le_three_trace
    cutoff N W hN
  calc
    heathBrownCoefficientOneMoment N W ≤
        3 * (heathBrownTraceMoment cutoff (gmSourceLeftScale N) W +
          heathBrownTraceMoment cutoff N W +
          heathBrownTraceMoment cutoff (gmSourceRightScale N) W) := by
      simpa only [heathBrownCoefficientOneMoment] using hEntry
    _ ≤ 3 * (heathBrownTraceHybridBound C K L D q T W
            (gmSourceLeftScale N) H +
          heathBrownTraceHybridBound C K L D q T W N H +
          heathBrownTraceHybridBound C K L D q T W
            (gmSourceRightScale N) H) := by
      gcongr

/-! ## Canonical dyadic reflection schedule -/

/-- The binwise integration height: it grows with the displacement until it
reaches the fixed dyadic cap `2^h`. -/
noncomputable def heathBrownDyadicReflectionHeight
    (h j : ℕ) : ℝ :=
  ((2 ^ min h (j - 1) : ℕ) : ℝ)

/-- Integral ceiling for the physical dual length `2^j H / Q`.  The outer
maximum keeps the reflected polynomial nonempty in every bin. -/
def heathBrownDyadicReflectionLength
    (Q h j : ℕ) : ℕ :=
  max 1 ((2 ^ j * 2 ^ min h (j - 1) + Q - 1) / Q)

/-- The canonical height is admissible in every stationary bin. -/
theorem heathBrownDyadicReflectionHeight_bounds
    (h j : ℕ) (hj : 2 ≤ j) :
    1 ≤ heathBrownDyadicReflectionHeight h j ∧
      heathBrownDyadicReflectionHeight h j ≤
        ((2 ^ j : ℕ) : ℝ) / 2 := by
  have hExp : min h (j - 1) ≤ j - 1 := min_le_right _ _
  have hPowNat : 2 ^ min h (j - 1) ≤ (2 : ℕ) ^ (j - 1) :=
    Nat.pow_le_pow_right (by omega) hExp
  have hjEq : j = (j - 1) + 1 := by omega
  constructor
  · unfold heathBrownDyadicReflectionHeight
    exact_mod_cast (Nat.one_le_pow _ _ (by omega : 0 < (2 : ℕ)))
  · unfold heathBrownDyadicReflectionHeight
    rw [hjEq, pow_succ]
    norm_num
    exact_mod_cast hPowNat

/-- The canonical integral dual length is positive. -/
theorem heathBrownDyadicReflectionLength_pos
    (Q h j : ℕ) : 0 < heathBrownDyadicReflectionLength Q h j := by
  unfold heathBrownDyadicReflectionLength
  omega

/-- The canonical reflected length is large enough for the physical dual
scale.  This is the lower half of the exact ceiling comparison; retaining it
over the naturals avoids any rounding hypothesis in later analytic bounds. -/
theorem heathBrownDyadicReflectionLength_lower
    (Q h j : ℕ) (hQ : 0 < Q) :
    2 ^ j * 2 ^ min h (j - 1) ≤
      Q * heathBrownDyadicReflectionLength Q h j := by
  let A : ℕ := 2 ^ j * 2 ^ min h (j - 1)
  have hCeil : A ≤ Q * CeilDiv.ceilDiv A Q := by
    simpa only [nsmul_eq_mul] using
      (le_smul_ceilDiv (b := A) (a := Q) hQ)
  have hCeilLe : CeilDiv.ceilDiv A Q ≤
      max 1 (CeilDiv.ceilDiv A Q) := le_max_right _ _
  have hMul := Nat.mul_le_mul_left Q hCeilLe
  unfold heathBrownDyadicReflectionLength
  rw [← Nat.ceilDiv_eq_add_pred_div]
  exact hCeil.trans hMul

/-- The canonical reflected length overshoots the physical dual scale by at
most one source block.  Together with
`heathBrownDyadicReflectionLength_lower`, this is the exact integral form of
`M = ceil (2^j H / Q)` used in the source reflection recurrence. -/
theorem heathBrownDyadicReflectionLength_upper
    (Q h j : ℕ) (hQ : 0 < Q) :
    Q * heathBrownDyadicReflectionLength Q h j ≤
      2 ^ j * 2 ^ min h (j - 1) + Q := by
  let A : ℕ := 2 ^ j * 2 ^ min h (j - 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCeilPos : 0 < CeilDiv.ceilDiv A Q := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos
    · omega
    · exact hQ
  have hMax : max 1 (CeilDiv.ceilDiv A Q) =
      CeilDiv.ceilDiv A Q :=
    max_eq_right hCeilPos
  have hDiv : Q * ((A + Q - 1) / Q) ≤ A + Q - 1 :=
    Nat.mul_div_le _ _
  unfold heathBrownDyadicReflectionLength
  change Q * max 1 ((A + Q - 1) / Q) ≤ A + Q
  rw [← Nat.ceilDiv_eq_add_pred_div, hMax,
    Nat.ceilDiv_eq_add_pred_div]
  exact hDiv.trans (Nat.sub_le _ _)

/-- Real-valued two-sided comparison for the canonical reflected length. -/
theorem heathBrownDyadicReflectionLength_bounds_real
    (Q h j : ℕ) (hQ : 0 < Q) :
    (((2 ^ j * 2 ^ min h (j - 1) : ℕ) : ℝ) ≤
        (Q : ℝ) * heathBrownDyadicReflectionLength Q h j) ∧
      (Q : ℝ) * heathBrownDyadicReflectionLength Q h j ≤
        ((2 ^ j * 2 ^ min h (j - 1) : ℕ) : ℝ) + Q := by
  constructor
  · exact_mod_cast heathBrownDyadicReflectionLength_lower Q h j hQ
  · exact_mod_cast heathBrownDyadicReflectionLength_upper Q h j hQ

/-- Specialization of the source recurrence to the explicit dyadic schedule.
No height or reflected-length hypothesis remains: the three source scales use
their literal ceiling lengths. -/
theorem heathBrownCoefficientOneMoment_le_dyadic_reflection
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N h : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → IsSeparated 1 W → InBaseInterval T W →
        heathBrownCoefficientOneMoment N W ≤
          3 *
            (heathBrownTraceScheduleBound C K L D q T W
                (gmSourceLeftScale N)
                (heathBrownDyadicReflectionHeight h)
                (heathBrownDyadicReflectionLength (gmSourceLeftScale N) h) +
              heathBrownTraceScheduleBound C K L D q T W N
                (heathBrownDyadicReflectionHeight h)
                (heathBrownDyadicReflectionLength N h) +
              heathBrownTraceScheduleBound C K L D q T W
                (gmSourceRightScale N)
                (heathBrownDyadicReflectionHeight h)
                (heathBrownDyadicReflectionLength (gmSourceRightScale N) h)) := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hRecurrence⟩ :=
    heathBrownCoefficientOneMoment_le_reflection_schedule cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro N h T W hN hSep hInterval
  apply hRecurrence
    (heathBrownDyadicReflectionHeight h)
    (heathBrownDyadicReflectionLength (gmSourceLeftScale N) h)
    (heathBrownDyadicReflectionLength N h)
    (heathBrownDyadicReflectionLength (gmSourceRightScale N) h)
    hN hSep hInterval
  intro j hjRange hj
  have hHeight := heathBrownDyadicReflectionHeight_bounds h j hj
  exact ⟨hHeight.1, hHeight.2,
    heathBrownDyadicReflectionLength_pos _ _ _,
    heathBrownDyadicReflectionLength_pos _ _ _,
    heathBrownDyadicReflectionLength_pos _ _ _⟩

/-! ## Terminal control of the reflected dyadic prefix -/

/-- The least dyadic integer above a positive natural is smaller than twice
that natural.  This is the exact rounding comparison needed when the
reflected prefix is enlarged to one common terminal dyadic block. -/
theorem pow_clog_two_le_two_mul (M : ℕ) (hM : 0 < M) :
    2 ^ Nat.clog 2 M ≤ 2 * M := by
  by_cases hMOne : M = 1
  · subst M
    norm_num
  · have hMgt : 1 < M := by omega
    have hClogPos : 0 < Nat.clog 2 M :=
      Nat.clog_pos Nat.one_lt_two hMgt
    have hPred : 2 ^ (Nat.clog 2 M - 1) < M := by
      simpa only [Nat.pred_eq_sub_one] using
        (Nat.pow_pred_clog_lt_self Nat.one_lt_two hMgt)
    have hClogEq : Nat.clog 2 M = (Nat.clog 2 M - 1) + 1 := by omega
    calc
      2 ^ Nat.clog 2 M = 2 ^ ((Nat.clog 2 M - 1) + 1) := by
        exact congrArg (fun n : ℕ => 2 ^ n) hClogEq
      _ = 2 ^ (Nat.clog 2 M - 1) * 2 := by rw [pow_succ]
      _ ≤ 2 * M := by omega

theorem heathBrownCommonReflectionLength_le_target
    (Q H : ℕ) (T : ℝ) :
    heathBrownCommonReflectionLength Q H T ≤
      heathBrownReflectionTargetScale Q H T := by
  unfold heathBrownReflectionTargetScale
  exact Nat.le_pow_clog (by omega) _

theorem heathBrownReflectionTargetScale_le_two_mul_common
    (Q H : ℕ) (T : ℝ) :
    heathBrownReflectionTargetScale Q H T ≤
      2 * heathBrownCommonReflectionLength Q H T := by
  unfold heathBrownReflectionTargetScale
  exact pow_clog_two_le_two_mul _ (by
    unfold heathBrownCommonReflectionLength
    omega)

/-- The terminal dyadic scale is explicitly comparable with the physical
dual scale `T H / Q`. -/
theorem heathBrownReflectionTargetScale_bounds_real
    (Q H : ℕ) (T : ℝ) (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T) :
    ((Nat.floor T : ℝ) * H) / Q ≤
        heathBrownReflectionTargetScale Q H T ∧
      (heathBrownReflectionTargetScale Q H T : ℝ) ≤
        2 * (T * H / Q + 1) := by
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hFloorNonneg : (0 : ℝ) ≤ Nat.floor T := by positivity
  have hFloorLe : (Nat.floor T : ℝ) ≤ T :=
    Nat.floor_le (zero_le_one.trans hT)
  have hLowerNat := heathBrownCommonReflectionLength_lower Q H T hQ
  have hCommonTarget := heathBrownCommonReflectionLength_le_target Q H T
  have hUpperNat := heathBrownCommonReflectionLength_upper Q H T hQ hH hT
  have hTargetCommon := heathBrownReflectionTargetScale_le_two_mul_common Q H T
  constructor
  · rw [div_le_iff₀ hQReal]
    calc
      (Nat.floor T : ℝ) * H ≤
          (Q : ℝ) * heathBrownCommonReflectionLength Q H T := by
        exact_mod_cast hLowerNat
      _ ≤ (Q : ℝ) * heathBrownReflectionTargetScale Q H T := by
        gcongr
      _ = (heathBrownReflectionTargetScale Q H T : ℝ) * Q := by ring
  · have hTargetCommonReal :
        (heathBrownReflectionTargetScale Q H T : ℝ) ≤
          2 * (heathBrownCommonReflectionLength Q H T : ℝ) := by
        exact_mod_cast hTargetCommon
    have hCommonUpperReal :
        (Q : ℝ) * heathBrownCommonReflectionLength Q H T ≤
          (Nat.floor T : ℝ) * H + Q := by
        exact_mod_cast hUpperNat
    calc
      (heathBrownReflectionTargetScale Q H T : ℝ) ≤
          2 * (heathBrownCommonReflectionLength Q H T : ℝ) := hTargetCommonReal
      _ ≤ 2 * (((Nat.floor T : ℝ) * H + Q) / Q) := by
        gcongr
        rw [le_div_iff₀ hQReal]
        simpa [mul_comm] using hCommonUpperReal
      _ ≤ 2 * ((T * H + Q) / Q) := by
        gcongr
      _ = 2 * (T * H / Q + 1) := by
        field_simp

/-- Every dyadic coefficient-one prefix occurring in the reflection
integral is bounded by the same terminal weighted Heath--Brown moment.
The factor `2 * P` is precisely the Jutila normalization, while scale
monotonicity supplies the complementary dyadic quotient. -/
theorem heathBrownCoefficientOneMoment_dyadic_le_terminal_weighted
    (M r : ℕ) (W : Finset ℝ) (hr : r < Nat.clog 2 M) :
    heathBrownCoefficientOneMoment (2 ^ r) W ≤
      2 * (2 ^ Nat.clog 2 M : ℕ) *
        heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W := by
  let c : ℕ := Nat.clog 2 M
  let q : ℕ := 2 ^ (c - r)
  have hrc : r ≤ c := hr.le
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hScale := heathBrownWeightedMoment_scale_monotone
    q (2 ^ r) W hq
  have hProduct : q * 2 ^ r = 2 ^ c := by
    dsimp only [q]
    rw [← pow_add]
    congr
    omega
  rw [hProduct] at hScale
  have hNormalize :=
    sourceCoefficientOne_differenceMoment_le_two_mul_weighted (2 ^ r) W
  have hPowNonneg : 0 ≤ (2 * (2 ^ r : ℕ) : ℝ) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hScale hPowNonneg
  have hProductReal : (q : ℝ) * (2 ^ r : ℕ) = (2 ^ c : ℕ) := by
    exact_mod_cast hProduct
  calc
    heathBrownCoefficientOneMoment (2 ^ r) W ≤
        (2 * (2 ^ r : ℕ) : ℝ) * heathBrownWeightedMoment (2 ^ r) W := by
      simpa only [heathBrownCoefficientOneMoment] using hNormalize
    _ ≤ (2 * (2 ^ r : ℕ) : ℝ) *
          ((q : ℝ) * heathBrownWeightedMoment (2 ^ c) W) := hScaled
    _ = 2 * (2 ^ c : ℕ) * heathBrownWeightedMoment (2 ^ c) W := by
      rw [show (2 * (2 ^ r : ℕ) : ℝ) = 2 * (2 ^ r : ℕ) by norm_num]
      calc
        2 * (2 ^ r : ℕ) *
              ((q : ℝ) * heathBrownWeightedMoment (2 ^ c) W) =
            2 * ((q : ℝ) * (2 ^ r : ℕ)) *
              heathBrownWeightedMoment (2 ^ c) W := by ring
        _ = _ := by rw [hProductReal]
    _ = 2 * (2 ^ Nat.clog 2 M : ℕ) *
          heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W := by rfl

/-- Transfer a coefficient-one dyadic prefix to any larger dyadic target.
This uniform form is what allows all displacement bins to share one terminal
moment in the source recurrence. -/
theorem exists_heathBrownCoefficientOneMoment_dyadic_le_target_transfer
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c r : ℕ) (W : Finset ℝ), r ≤ c →
        heathBrownCoefficientOneMoment (2 ^ r) W ≤
          8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W) := by
  obtain ⟨C, hC, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro c r W hrc
  let P : ℕ := 2 ^ r
  let J : ℕ := 2 ^ (c - r)
  let Q : ℕ := 2 ^ c
  have hP : 0 < P := by dsimp only [P]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hProduct : J * P = Q := by
    dsimp only [J, P, Q]
    rw [← pow_add]
    congr
    omega
  have hProductReal : (J : ℝ) * (P : ℝ) = (Q : ℝ) := by
    exact_mod_cast hProduct
  have hTransferLine := hTransfer J P W hJ hP
  rw [hProduct, hProductReal] at hTransferLine
  have hNormalize :=
    sourceCoefficientOne_differenceMoment_le_two_mul_weighted P W
  have hPleQ : P ≤ Q := by
    dsimp only [P, Q]
    exact Nat.pow_le_pow_right (by omega) hrc
  have hPleQReal : (P : ℝ) ≤ Q := by exact_mod_cast hPleQ
  have hMomentNonneg : 0 ≤ heathBrownWeightedMoment P W := by
    unfold heathBrownWeightedMoment
    positivity
  calc
    heathBrownCoefficientOneMoment P W ≤
        (2 * P : ℝ) * heathBrownWeightedMoment P W := by
      simpa only [heathBrownCoefficientOneMoment] using hNormalize
    _ ≤ (2 * Q : ℝ) * heathBrownWeightedMoment P W := by
      gcongr
    _ ≤ (2 * Q : ℝ) *
        (4 * (C * (4 * Q : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment Q W +
            heathBrownWeightedMoment (2 * Q) W)) := by
      exact mul_le_mul_of_nonneg_left hTransferLine (by positivity)
    _ = 8 * (2 ^ c : ℕ) *
        (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ c) W +
            heathBrownWeightedMoment (2 * (2 ^ c)) W) := by
      dsimp only [Q]
      ring

/-- A whole reflected prefix is controlled at any common dyadic exponent
above its own ceiling exponent. -/
theorem exists_heathBrownReflectionDyadicMoment_le_target_transfer
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M c : ℕ) (W : Finset ℝ), Nat.clog 2 M ≤ c →
        heathBrownReflectionDyadicMoment W M ≤
          2 * ((Nat.clog 2 M : ℝ) + 1) *
            (((W.card : ℝ) ^ 2) +
              (Nat.clog 2 M : ℝ) *
                (8 * (2 ^ c : ℕ) *
                  (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
                    (heathBrownWeightedMoment (2 ^ c) W +
                      heathBrownWeightedMoment (2 * (2 ^ c)) W))) := by
  obtain ⟨C, hC, hPrefix⟩ :=
    exists_heathBrownCoefficientOneMoment_dyadic_le_target_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro M c W hc
  rw [heathBrownReflectionDyadicMoment_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr
  calc
    (∑ r ∈ Finset.range (Nat.clog 2 M),
        heathBrownCoefficientOneMoment (2 ^ r) W) ≤
      ∑ _r ∈ Finset.range (Nat.clog 2 M),
        (8 * (2 ^ c : ℕ) *
          (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 * (2 ^ c)) W)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hPrefix c r W ((Finset.mem_range.mp hr).le.trans hc)
    _ = (Nat.clog 2 M : ℝ) *
        (8 * (2 ^ c : ℕ) *
          (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 * (2 ^ c)) W)) := by simp

/-- One common recursive majorant for every reflected bin. -/
noncomputable def heathBrownCommonReflectionMomentBound
    (C η : ℝ) (Q H : ℕ) (T : ℝ) (W : Finset ℝ) : ℝ :=
  let M := heathBrownCommonReflectionLength Q H T
  let c := Nat.clog 2 M
  2 * ((c : ℝ) + 1) *
    (((W.card : ℝ) ^ 2) +
      (c : ℝ) *
        (8 * (2 ^ c : ℕ) *
          (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 * (2 ^ c)) W)))

/-- All stationary bins are bounded by the same transferred terminal
moment at `clog (ceil(floor T * H / Q))`. -/
theorem exists_heathBrownReflectionDyadicMoment_le_common
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ} {j Q H : ℕ} (W : Finset ℝ),
        j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1) →
        2 ≤ j →
        heathBrownReflectionDyadicMoment W
            (heathBrownFixedReflectionLength Q H j) ≤
          heathBrownCommonReflectionMomentBound C η Q H T W := by
  obtain ⟨C, hC, hTarget⟩ :=
    exists_heathBrownReflectionDyadicMoment_le_target_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro T j Q H W hj hjTwo
  let M := heathBrownFixedReflectionLength Q H j
  let M₀ := heathBrownCommonReflectionLength Q H T
  let c := Nat.clog 2 M₀
  have hM : M ≤ M₀ :=
    heathBrownFixedReflectionLength_le_common hj hjTwo
  have hc : Nat.clog 2 M ≤ c := by
    exact Nat.clog_mono_right 2 hM
  have hRaw := hTarget M c W hc
  have hXNonneg : 0 ≤
      8 * (2 ^ c : ℕ) *
        (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ c) W +
            heathBrownWeightedMoment (2 * (2 ^ c)) W) := by
    have hS₁ : 0 ≤ heathBrownWeightedMoment (2 ^ c) W := by
      unfold heathBrownWeightedMoment
      positivity
    have hS₂ : 0 ≤ heathBrownWeightedMoment (2 * (2 ^ c)) W := by
      unfold heathBrownWeightedMoment
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (sq_nonneg (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η)))
      (add_nonneg hS₁ hS₂)
  have hcReal : (Nat.clog 2 M : ℝ) ≤ c := by exact_mod_cast hc
  unfold heathBrownCommonReflectionMomentBound
  dsimp only
  have hInner :
      (W.card : ℝ) ^ 2 + (Nat.clog 2 M : ℝ) *
          (8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W)) ≤
        (W.card : ℝ) ^ 2 + (c : ℝ) *
          (8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W)) := by
    simpa only [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_right hcReal hXNonneg) ((W.card : ℝ) ^ 2)
  have hTargetInnerNonneg : 0 ≤
      (W.card : ℝ) ^ 2 + (c : ℝ) *
        (8 * (2 ^ c : ℕ) *
          (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 * (2 ^ c)) W)) := by
    exact add_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hXNonneg)
  refine hRaw.trans ?_
  calc
    2 * ((Nat.clog 2 M : ℝ) + 1) *
        ((W.card : ℝ) ^ 2 + (Nat.clog 2 M : ℝ) *
          (8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W))) ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        ((W.card : ℝ) ^ 2 + (c : ℝ) *
          (8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W))) := by
      exact mul_le_mul_of_nonneg_left hInner (by positivity)
    _ ≤ 2 * ((c : ℝ) + 1) *
        ((W.card : ℝ) ^ 2 + (c : ℝ) *
          (8 * (2 ^ c : ℕ) *
            (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ c) W +
                heathBrownWeightedMoment (2 * (2 ^ c)) W))) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hTargetInnerNonneg

/-- Collapse the exact hybrid schedule to one common recursive moment plus
the still-explicit analytic remainder sum. -/
theorem exists_heathBrownTraceHybridBound_le_common
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ),
        0 ≤ C → 0 < H → IsSeparated 1 W →
        heathBrownTraceHybridBound C K L D q T W Q H ≤
          (W.card : ℝ) * Q ^ 2 +
            (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
              (8 * (W.card : ℝ) * H * Q ^ 2 +
                4 * Q ^ 2 * C ^ 2 * H *
                  heathBrownCommonReflectionMomentBound
                    Ctr η Q H T W) +
            heathBrownHybridErrorSum K L D q T W Q H := by
  obtain ⟨Ctr, hCtr, hCommon⟩ :=
    exists_heathBrownReflectionDyadicMoment_le_common η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C K L D q T W Q H hC hH hSep
  let E₀ : ℝ := 8 * (W.card : ℝ) * H * Q ^ 2
  let A₀ : ℝ := 4 * Q ^ 2 * C ^ 2 * H *
    heathBrownCommonReflectionMomentBound Ctr η Q H T W
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hPoint : ∀ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      (if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
          2 * (((Q : ℝ) * C /
              Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * (H : ℝ)) ^ 2 *
                heathBrownReflectionDyadicMoment W
                  (heathBrownFixedReflectionLength Q H j)) +
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (heathBrownReflectionBinError q Q
                (heathBrownFixedReflectionLength Q H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
        else ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2) ≤
        E₀ + A₀ +
          (if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
              (heathBrownReflectionBinError q Q
                (heathBrownFixedReflectionLength Q H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
          else 0) := by
    intro j hj
    by_cases hReflect : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
    · rw [if_pos hReflect, if_pos hReflect]
      have hRec := hCommon (Q := Q) (H := H) W hj hReflect.1
      have hRecMomentNonneg : 0 ≤
          heathBrownReflectionDyadicMoment W
            (heathBrownFixedReflectionLength Q H j) := by
        unfold heathBrownReflectionDyadicMoment
        positivity
      have hCommonNonneg : 0 ≤
          heathBrownCommonReflectionMomentBound Ctr η Q H T W :=
        hRecMomentNonneg.trans hRec
      have hCoeff := heathBrown_reflection_main_coefficient_le
        C Q H j hH hReflect.2
      have hMain :
          2 * (((Q : ℝ) * C /
              Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
              ((2 * (H : ℝ)) ^ 2 *
                heathBrownReflectionDyadicMoment W
                  (heathBrownFixedReflectionLength Q H j)) ≤ A₀ := by
        calc
          _ = (2 * (((Q : ℝ) * C /
                Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
                (2 * (H : ℝ)) ^ 2) *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j) := by ring
          _ ≤ (4 * (Q : ℝ) ^ 2 * C ^ 2 * H) *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j) := by
            exact mul_le_mul_of_nonneg_right hCoeff hRecMomentNonneg
          _ ≤ (4 * (Q : ℝ) ^ 2 * C ^ 2 * H) *
              heathBrownCommonReflectionMomentBound Ctr η Q H T W := by
            exact mul_le_mul_of_nonneg_left hRec (by positivity)
          _ = A₀ := by dsimp only [A₀]
      linarith
    · rw [if_neg hReflect, if_neg hReflect]
      have hPow : 2 ^ j ≤ 2 * H := by
        by_cases hjTwo : 2 ≤ j
        · have : 2 ^ j < 2 * H := by
            exact Nat.lt_of_not_ge (fun h => hReflect ⟨hjTwo, h⟩)
          omega
        · have hjLt : j < 2 := by omega
          have : 2 ^ j ≤ 2 := by interval_cases j <;> norm_num
          omega
      have hCardNat := heathBrownDifferenceBin_card_le W j hSep
      have hCardNat' : (heathBrownDifferenceBin W j).card ≤
          W.card * (8 * H) := by
        have hFactor : 2 * 2 ^ (j + 1) ≤ 8 * H := by
          rw [pow_succ]
          omega
        calc
          (heathBrownDifferenceBin W j).card ≤
              W.card * (2 * 2 ^ (j + 1)) := hCardNat
          _ ≤ W.card * (8 * H) := by
            exact Nat.mul_le_mul_left _ hFactor
      have hCardReal : ((heathBrownDifferenceBin W j).card : ℝ) ≤
          (W.card : ℝ) * (8 * H) := by exact_mod_cast hCardNat'
      have hTrivial : ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2 ≤
          E₀ := by
        dsimp only [E₀]
        have hQsq : 0 ≤ (Q : ℝ) ^ 2 := sq_nonneg _
        calc
          ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2 ≤
              ((W.card : ℝ) * (8 * H)) * Q ^ 2 :=
            mul_le_mul_of_nonneg_right hCardReal hQsq
          _ = 8 * (W.card : ℝ) * H * Q ^ 2 := by ring
      have hA₀ : 0 ≤ A₀ := by
        dsimp only [A₀]
        apply mul_nonneg (by positivity)
        unfold heathBrownCommonReflectionMomentBound
        dsimp only
        have hS₁ : 0 ≤ heathBrownWeightedMoment
            (2 ^ Nat.clog 2 (heathBrownCommonReflectionLength Q H T)) W := by
          unfold heathBrownWeightedMoment
          positivity
        have hS₂ : 0 ≤ heathBrownWeightedMoment
            (2 * (2 ^ Nat.clog 2
              (heathBrownCommonReflectionLength Q H T))) W := by
          unfold heathBrownWeightedMoment
          positivity
        have hTransferFactor : 0 ≤
            8 * (2 ^ Nat.clog 2
                (heathBrownCommonReflectionLength Q H T) : ℕ) *
              (Ctr * (4 * (2 ^ Nat.clog 2
                (heathBrownCommonReflectionLength Q H T) : ℕ) : ℝ) ^ η) ^ 2 *
                (heathBrownWeightedMoment
                    (2 ^ Nat.clog 2
                      (heathBrownCommonReflectionLength Q H T)) W +
                  heathBrownWeightedMoment
                    (2 * (2 ^ Nat.clog 2
                      (heathBrownCommonReflectionLength Q H T))) W) := by
          exact mul_nonneg
            (mul_nonneg (by positivity) (sq_nonneg _))
            (add_nonneg hS₁ hS₂)
        exact mul_nonneg
          (mul_nonneg (by norm_num) (by positivity))
          (add_nonneg (sq_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hTransferFactor))
      linarith
  unfold heathBrownTraceHybridBound
  have hSum := Finset.sum_le_sum hPoint
  calc
    (W.card : ℝ) * Q ^ 2 +
        ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          (if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
              2 * (((Q : ℝ) * C /
                  Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
                  ((2 * (H : ℝ)) ^ 2 *
                    heathBrownReflectionDyadicMoment W
                      (heathBrownFixedReflectionLength Q H j)) +
                2 * ((heathBrownDifferenceBin W j).card : ℝ) *
                  (heathBrownReflectionBinError q Q
                    (heathBrownFixedReflectionLength Q H j) H
                    (((2 ^ (j + 1) : ℕ) : ℝ))
                    (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
            else ((heathBrownDifferenceBin W j).card : ℝ) * Q ^ 2) ≤
      (W.card : ℝ) * Q ^ 2 +
        ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          (E₀ + A₀ +
            if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
              2 * ((heathBrownDifferenceBin W j).card : ℝ) *
                (heathBrownReflectionBinError q Q
                  (heathBrownFixedReflectionLength Q H j) H
                  (((2 ^ (j + 1) : ℕ) : ℝ))
                  (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
            else 0) := by
      exact add_le_add le_rfl hSum
    _ = (W.card : ℝ) * Q ^ 2 +
        (Nat.log 2 (Nat.floor T) + 1 : ℕ) * (E₀ + A₀) +
          heathBrownHybridErrorSum K L D q T W Q H := by
      unfold heathBrownHybridErrorSum
      have hSplit :
          (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
            (E₀ + A₀ +
              if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
                2 * ((heathBrownDifferenceBin W j).card : ℝ) *
                  (heathBrownReflectionBinError q Q
                    (heathBrownFixedReflectionLength Q H j) H
                    (((2 ^ (j + 1) : ℕ) : ℝ))
                    (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
              else 0)) =
            (∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), (E₀ + A₀)) +
              ∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
                (if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
                  2 * ((heathBrownDifferenceBin W j).card : ℝ) *
                    (heathBrownReflectionBinError q Q
                      (heathBrownFixedReflectionLength Q H j) H
                      (((2 ^ (j + 1) : ℕ) : ℝ))
                      (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
                else 0) := by
        rw [Finset.sum_add_distrib]
      rw [hSplit]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      ring
    _ = (W.card : ℝ) * Q ^ 2 +
        (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
          (8 * (W.card : ℝ) * H * Q ^ 2 +
            4 * Q ^ 2 * C ^ 2 * H *
              heathBrownCommonReflectionMomentBound Ctr η Q H T W) +
        heathBrownHybridErrorSum K L D q T W Q H := by
      dsimp only [E₀, A₀]

/-- Exact one-scale Heath--Brown recurrence after the complete analytic
remainder has been summed.  The recursive term is the common reflected
weighted moment and the displayed last term contains all three smooth
reflection errors. -/
theorem exists_heathBrownTraceHybridBound_le_source_recurrence
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ),
        0 ≤ C → 0 ≤ K → 0 ≤ L → 0 ≤ D →
        0 < Q → 0 < H → 1 ≤ T → IsSeparated 1 W →
        heathBrownTraceHybridBound C K L D q T W Q H ≤
          (W.card : ℝ) * Q ^ 2 +
            (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
              (8 * (W.card : ℝ) * H * Q ^ 2 +
                4 * Q ^ 2 * C ^ 2 * H *
                  heathBrownCommonReflectionMomentBound
                    Ctr η Q H T W) +
            (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
              (8 * (W.card : ℝ) * T *
                (heathBrownUniformReflectionError K L D q Q H T) ^ 2) := by
  obtain ⟨Ctr, hCtr, hCommon⟩ :=
    exists_heathBrownTraceHybridBound_le_common η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C K L D q T W Q H hC hK hL hD hQ hH hT hSep
  have hBase := hCommon C K L D q T W Q H hC hH hSep
  have hError := heathBrownHybridErrorSum_le_uniform
    K L D q Q H T W hK hL hD hQ hH hT hSep
  exact hBase.trans (add_le_add le_rfl hError)

/-- Source-sharp terminal control of one reflected dyadic prefix.  Unlike
the elementary scale-monotonicity bound above, this invokes the complete
Montgomery--Vaughan auxiliary transfer, so no quotient between the terminal
and prefix scales remains. -/
theorem exists_heathBrownCoefficientOneMoment_dyadic_le_terminal_transfer
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M r : ℕ) (W : Finset ℝ), r < Nat.clog 2 M →
        heathBrownCoefficientOneMoment (2 ^ r) W ≤
          8 * (2 ^ Nat.clog 2 M : ℕ) *
            (C * (4 * (2 ^ Nat.clog 2 M : ℕ) : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W +
                heathBrownWeightedMoment
                  (2 * (2 ^ Nat.clog 2 M)) W) := by
  obtain ⟨C, hC, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro M r W hr
  let c : ℕ := Nat.clog 2 M
  let P : ℕ := 2 ^ r
  let J : ℕ := 2 ^ (c - r)
  let Q : ℕ := 2 ^ c
  have hP : 0 < P := by dsimp only [P]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hProduct : J * P = Q := by
    dsimp only [J, P, Q]
    rw [← pow_add]
    congr
    omega
  have hProductReal : (J : ℝ) * (P : ℝ) = (Q : ℝ) := by
    exact_mod_cast hProduct
  have hTransferLine := hTransfer J P W hJ hP
  rw [hProduct] at hTransferLine
  rw [hProductReal] at hTransferLine
  have hNormalize :=
    sourceCoefficientOne_differenceMoment_le_two_mul_weighted P W
  have hPleQ : P ≤ Q := by
    dsimp only [P, Q, c]
    exact Nat.pow_le_pow_right (by omega) hr.le
  have hPleQReal : (P : ℝ) ≤ Q := by exact_mod_cast hPleQ
  have hMomentNonneg : 0 ≤ heathBrownWeightedMoment P W := by
    unfold heathBrownWeightedMoment
    positivity
  have hScaleFactor : (2 * P : ℝ) ≤ 2 * Q := by linarith
  have hTransferRhsNonneg : 0 ≤
      4 * (C * (4 * Q : ℝ) ^ η) ^ 2 *
        (heathBrownWeightedMoment Q W +
          heathBrownWeightedMoment (2 * Q) W) := by
    have hQ₁ : 0 ≤ heathBrownWeightedMoment Q W := by
      unfold heathBrownWeightedMoment
      positivity
    have hQ₂ : 0 ≤ heathBrownWeightedMoment (2 * Q) W := by
      unfold heathBrownWeightedMoment
      positivity
    positivity
  calc
    heathBrownCoefficientOneMoment P W ≤
        (2 * P : ℝ) * heathBrownWeightedMoment P W := by
      simpa only [heathBrownCoefficientOneMoment] using hNormalize
    _ ≤ (2 * Q : ℝ) * heathBrownWeightedMoment P W := by
      exact mul_le_mul_of_nonneg_right hScaleFactor hMomentNonneg
    _ ≤ (2 * Q : ℝ) *
        (4 * (C * (4 * Q : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment Q W +
            heathBrownWeightedMoment (2 * Q) W)) := by
      exact mul_le_mul_of_nonneg_left hTransferLine (by positivity)
    _ = 8 * (2 ^ Nat.clog 2 M : ℕ) *
        (C * (4 * (2 ^ Nat.clog 2 M : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W +
            heathBrownWeightedMoment
              (2 * (2 ^ Nat.clog 2 M)) W) := by
      dsimp only [Q, c]
      ring

/-- Complete reflected-prefix estimate with the source transfer principle
already consumed.  This is the literal `log^3 M` recursive term in (29.41),
before logarithms and the divisor loss are absorbed into `T^ε`. -/
theorem exists_heathBrownReflectionDyadicMoment_le_terminal_transfer
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (W : Finset ℝ),
        heathBrownReflectionDyadicMoment W M ≤
          2 * ((Nat.clog 2 M : ℝ) + 1) *
            (((W.card : ℝ) ^ 2) +
              (Nat.clog 2 M : ℝ) *
                (8 * (2 ^ Nat.clog 2 M : ℕ) *
                  (C * (4 * (2 ^ Nat.clog 2 M : ℕ) : ℝ) ^ η) ^ 2 *
                    (heathBrownWeightedMoment
                        (2 ^ Nat.clog 2 M) W +
                      heathBrownWeightedMoment
                        (2 * (2 ^ Nat.clog 2 M)) W))) := by
  obtain ⟨C, hC, hPrefix⟩ :=
    exists_heathBrownCoefficientOneMoment_dyadic_le_terminal_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro M W
  rw [heathBrownReflectionDyadicMoment_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr
  calc
    (∑ r ∈ Finset.range (Nat.clog 2 M),
        heathBrownCoefficientOneMoment (2 ^ r) W) ≤
      ∑ _r ∈ Finset.range (Nat.clog 2 M),
        (8 * (2 ^ Nat.clog 2 M : ℕ) *
          (C * (4 * (2 ^ Nat.clog 2 M : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W +
              heathBrownWeightedMoment
                (2 * (2 ^ Nat.clog 2 M)) W)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hPrefix M r W (Finset.mem_range.mp hr)
    _ = (Nat.clog 2 M : ℝ) *
        (8 * (2 ^ Nat.clog 2 M : ℕ) *
          (C * (4 * (2 ^ Nat.clog 2 M : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W +
              heathBrownWeightedMoment
                (2 * (2 ^ Nat.clog 2 M)) W)) := by simp

/-- The complete logarithmic prefix produced by smooth reflection is
controlled by one terminal weighted moment.  This is the finite analogue
of the `log^3 M * S(M)` term in Montgomery--Vaughan (29.41), before the
outer bin sum and harmless logarithms are absorbed into `T^ε`. -/
theorem heathBrownReflectionDyadicMoment_le_terminal_weighted
    (M : ℕ) (W : Finset ℝ) :
    heathBrownReflectionDyadicMoment W M ≤
      2 * ((Nat.clog 2 M : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) +
          (Nat.clog 2 M : ℝ) *
            (2 * (2 ^ Nat.clog 2 M : ℕ) *
              heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W)) := by
  rw [heathBrownReflectionDyadicMoment_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hSum :
    (∑ r ∈ Finset.range (Nat.clog 2 M),
        heathBrownCoefficientOneMoment (2 ^ r) W) ≤
      (Nat.clog 2 M : ℝ) *
        (2 * (2 ^ Nat.clog 2 M : ℕ) *
          heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W) := by
    calc
      (∑ r ∈ Finset.range (Nat.clog 2 M),
          heathBrownCoefficientOneMoment (2 ^ r) W) ≤
        ∑ _r ∈ Finset.range (Nat.clog 2 M),
          (2 * (2 ^ Nat.clog 2 M : ℕ) *
            heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W) := by
        apply Finset.sum_le_sum
        intro r hr
        exact heathBrownCoefficientOneMoment_dyadic_le_terminal_weighted
          M r W (Finset.mem_range.mp hr)
      _ = (Nat.clog 2 M : ℝ) *
          (2 * (2 ^ Nat.clog 2 M : ℕ) *
            heathBrownWeightedMoment (2 ^ Nat.clog 2 M) W) := by
        simp
  exact add_le_add_right hSum _

/-- On the source block `(N,2N]`, multiplying the critical-line weight by
`sqrt N` produces a coefficient bounded by one. -/
theorem sqrt_mul_heathBrownHalfWeight_le_one
    {N n : ℕ} (hn : n ∈ Finset.Ioc N (2 * N)) :
    Real.sqrt N * heathBrownHalfWeight n ≤ 1 := by
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnPosNat : 0 < n := by omega
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hnBounds.1)
  have hSqrtLe : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt hNle
  have hSqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnPos
  unfold heathBrownHalfWeight
  rw [one_div, ← div_eq_mul_inv]
  exact (div_le_one hSqrtPos).2 hSqrtLe

/-- Reverse Jutila normalization.  Together with
`sourceCoefficientOne_differenceMoment_le_two_mul_weighted`, it identifies
the coefficient-one and critical-line moments up to the exact dyadic factor
`[N,2N]`.  This direction is what converts the reflected trace estimate
back into the weighted recurrence. -/
theorem natCast_mul_heathBrownWeightedMoment_le_coefficientOne
    (N : ℕ) (W : Finset ℝ) :
    (N : ℝ) * heathBrownWeightedMoment N W ≤
      heathBrownCoefficientOneMoment N W := by
  let B : ℝ := Real.sqrt N
  let b : ℕ → ℝ := fun n => B * heathBrownHalfWeight n
  have hbNonneg : ∀ n ∈ Finset.Ioc N (2 * N), 0 ≤ b n := by
    intro n hn
    exact mul_nonneg (Real.sqrt_nonneg _) (heathBrownHalfWeight_nonneg n)
  have hbOne : ∀ n ∈ Finset.Ioc N (2 * N), ‖(b n : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbNonneg n hn)]
    simpa only [b, B] using sqrt_mul_heathBrownHalfWeight_le_one hn
  have hMajorant := sourceDirichletPoly_differenceMoment_le_one
    N W (fun n => (b n : ℂ)) hbOne
  have hScaled :
      (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly N (fun n => (b n : ℂ)) (t - u)‖ ^ 2) =
        B ^ 2 * heathBrownWeightedMoment N W := by
    unfold heathBrownWeightedMoment b
    simp_rw [sourceDirichletPoly_real_smul_coeffs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  calc
    (N : ℝ) * heathBrownWeightedMoment N W =
        B ^ 2 * heathBrownWeightedMoment N W := by
      congr 1
      dsimp only [B]
      rw [Real.sq_sqrt]
      positivity
    _ = ∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly N (fun n => (b n : ℂ)) (t - u)‖ ^ 2 :=
      hScaled.symm
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly N (fun _ => (1 : ℂ)) (t - u)‖ ^ 2 :=
      hMajorant
    _ = heathBrownCoefficientOneMoment N W := by rfl

/-- Weighted source recurrence before estimating its explicit hybrid
schedule.  The left side is the actual Jutila moment, and the proof consumes
both directions of the coefficient-one normalization. -/
theorem heathBrownWeightedMoment_le_hybrid
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L D : ℝ,
      0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H →
        IsSeparated 1 W → InBaseInterval T W →
        (N : ℝ) * heathBrownWeightedMoment N W ≤
          3 * (heathBrownTraceHybridBound C K L D q T W
                (gmSourceLeftScale N) H +
            heathBrownTraceHybridBound C K L D q T W N H +
            heathBrownTraceHybridBound C K L D q T W
              (gmSourceRightScale N) H) := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hOne⟩ :=
    heathBrownCoefficientOneMoment_le_hybrid cutoff q hq
  refine ⟨C, K, L, D, hC, hK, hL, hD, ?_⟩
  intro N H T W hN hH hSep hInterval
  exact (natCast_mul_heathBrownWeightedMoment_le_coefficientOne N W).trans
    (hOne hN hH hSep hInterval)

/-- Weighted Jutila source entry for the corrected three-way recurrence. -/
theorem heathBrownWeightedMoment_le_source_bound
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ Cnear C K L D : ℝ,
      0 < Cnear ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H →
        IsSeparated 1 W → InBaseInterval T W →
        (N : ℝ) * heathBrownWeightedMoment N W ≤
          3 * (heathBrownTraceSourceBound Cnear C K L D q T W
                (gmSourceLeftScale N) H +
            heathBrownTraceSourceBound Cnear C K L D q T W N H +
            heathBrownTraceSourceBound Cnear C K L D q T W
              (gmSourceRightScale N) H) := by
  obtain ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, hOne⟩ :=
    heathBrownCoefficientOneMoment_le_source_bound cutoff q hq
  refine ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, ?_⟩
  intro N H T W hN hH hSep hInterval
  exact (natCast_mul_heathBrownWeightedMoment_le_coefficientOne N W).trans
    (hOne hN hH hSep hInterval)

/-- Two adjacent dyadic weighted moments can be transferred to a prescribed
larger dyadic scale.  This is deliberately applied only *after* the
stationary coefficient has been multiplied by the binwise reflected length:
that ordering preserves the `Q * M_j / 2^j` cancellation in the source
recurrence. -/
theorem exists_heathBrownWeightedMoment_pair_le_common_target
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r c : ℕ) (W : Finset ℝ), r + 1 ≤ c →
        heathBrownWeightedMoment (2 ^ r) W +
            heathBrownWeightedMoment (2 ^ (r + 1)) W ≤
          8 * (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
  obtain ⟨C, hC, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_transfer η hη
  refine ⟨C, hC, ?_⟩
  intro r c W hrc
  let J₀ : ℕ := 2 ^ (c - r)
  let J₁ : ℕ := 2 ^ (c - (r + 1))
  have hJ₀ : 0 < J₀ := by dsimp only [J₀]; positivity
  have hJ₁ : 0 < J₁ := by dsimp only [J₁]; positivity
  have hP₀ : 0 < 2 ^ r := by positivity
  have hP₁ : 0 < 2 ^ (r + 1) := by positivity
  have hProduct₀ : J₀ * 2 ^ r = 2 ^ c := by
    dsimp only [J₀]
    rw [← pow_add]
    congr
    omega
  have hProduct₁ : J₁ * 2 ^ (r + 1) = 2 ^ c := by
    dsimp only [J₁]
    rw [← pow_add]
    congr
    omega
  have hProductReal₀ : (J₀ : ℝ) * (2 ^ r : ℕ) = (2 ^ c : ℕ) := by
    exact_mod_cast hProduct₀
  have hProductReal₁ : (J₁ : ℝ) * (2 ^ (r + 1) : ℕ) = (2 ^ c : ℕ) := by
    exact_mod_cast hProduct₁
  have h₀ := hTransfer J₀ (2 ^ r) W hJ₀ hP₀
  have h₁ := hTransfer J₁ (2 ^ (r + 1)) W hJ₁ hP₁
  rw [hProduct₀] at h₀
  rw [hProduct₁] at h₁
  rw [hProductReal₀] at h₀
  rw [hProductReal₁] at h₁
  have hTwoPow : 2 * 2 ^ c = 2 ^ (c + 1) := by
    rw [pow_succ]
    ring
  rw [hTwoPow] at h₀ h₁
  calc
    heathBrownWeightedMoment (2 ^ r) W +
        heathBrownWeightedMoment (2 ^ (r + 1)) W ≤
      4 * (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ c) W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) +
        4 * (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ c) W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) :=
      add_le_add h₀ h₁
    _ = 8 * (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ c) W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) := by ring

/-- The stationary coefficient cancels the *binwise* reflected terminal
length.  This is the quantitative heart of the source recurrence: enlarging
the reflected moment before this multiplication would lose a factor of the
ambient height. -/
theorem heathBrown_reflection_main_coefficient_mul_terminalScale_le
    (C : ℝ) (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H)
    (hNotNear : ¬ 2 ^ (j + 1) ≤ Q) :
    2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
        (2 * (H : ℝ)) ^ 2 *
        (2 ^ Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℕ) ≤
      16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  let M : ℕ := heathBrownFixedReflectionLength Q H j
  let P : ℕ := 2 ^ Nat.clog 2 M
  have hX : 0 < X := by dsimp only [X]; positivity
  have hM : 0 < M := by
    dsimp only [M]
    exact heathBrownFixedReflectionLength_pos Q H j
  have hP : (P : ℝ) ≤ 2 * M := by
    exact_mod_cast pow_clog_two_le_two_mul M hM
  have hQM : (Q : ℝ) * M ≤ X * H + Q := by
    dsimp only [M, X]
    exact (heathBrownFixedReflectionLength_bounds_real Q H j hQ hH).2
  have hQlt : Q < 2 ^ (j + 1) := by omega
  have hQleTwoX : (Q : ℝ) ≤ 2 * X := by
    have hcast : (Q : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hQlt
    have hpow : (((2 ^ (j + 1) : ℕ) : ℝ)) = 2 * X := by
      dsimp only [X]
      rw [pow_succ]
      push_cast
      ring
    rw [hpow] at hcast
    exact hcast.le
  have hQP : (Q : ℝ) * P ≤ 2 * (X * H + Q) := by
    calc
      (Q : ℝ) * P ≤ (Q : ℝ) * (2 * M) := by
        gcongr
      _ = 2 * ((Q : ℝ) * M) := by ring
      _ ≤ 2 * (X * H + Q) := by gcongr
  have hRatio : ((Q : ℝ) * P) / X ≤ 2 * (H + 2) := by
    rw [div_le_iff₀ hX]
    calc
      (Q : ℝ) * P ≤ 2 * (X * H + Q) := hQP
      _ ≤ 2 * (X * H + 2 * X) := by gcongr
      _ = 2 * (H + 2) * X := by ring
  change 2 * (((Q : ℝ) * C / Real.sqrt X) ^ 2) *
      (2 * (H : ℝ)) ^ 2 * (P : ℝ) ≤ _
  rw [div_pow, Real.sq_sqrt hX.le]
  calc
    2 * (((Q : ℝ) * C) ^ 2 / X) * (2 * (H : ℝ)) ^ 2 * P =
        8 * (Q : ℝ) * C ^ 2 * H ^ 2 * (((Q : ℝ) * P) / X) := by
      field_simp
      ring
    _ ≤ 8 * (Q : ℝ) * C ^ 2 * H ^ 2 * (2 * (H + 2)) := by
      gcongr
    _ = 16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) := by ring

/-- Corrected common-target reflection estimate.  The local terminal length
`2^clog M` stays outside the transferred weighted moments, so the subsequent
stationary-phase multiplication can cancel it. -/
theorem exists_heathBrownReflectionDyadicMoment_le_common_preserving_length
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M c : ℕ) (W : Finset ℝ), Nat.clog 2 M + 1 ≤ c →
        heathBrownReflectionDyadicMoment W M ≤
          2 * ((Nat.clog 2 M : ℝ) + 1) *
            (((W.card : ℝ) ^ 2) +
              (Nat.clog 2 M : ℝ) *
                (64 * (2 ^ Nat.clog 2 M : ℕ) *
                  (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 4 *
                    (heathBrownWeightedMoment (2 ^ c) W +
                      heathBrownWeightedMoment (2 ^ (c + 1)) W))) := by
  obtain ⟨Ct, hCt, hTerminal⟩ :=
    exists_heathBrownReflectionDyadicMoment_le_terminal_transfer η hη
  obtain ⟨Ca, hCa, hPair⟩ :=
    exists_heathBrownWeightedMoment_pair_le_common_target η hη
  let C : ℝ := max Ct Ca
  have hC : 0 < C := lt_of_lt_of_le hCt (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M c W hMc
  let r : ℕ := Nat.clog 2 M
  let P : ℕ := 2 ^ r
  let Pc : ℕ := 2 ^ c
  have hrc : r + 1 ≤ c := by simpa only [r] using hMc
  have hrle : r ≤ c := by omega
  have hPle : P ≤ Pc := by
    dsimp only [P, Pc]
    exact Nat.pow_le_pow_right (by omega) hrle
  have hBase : (4 * (P : ℝ)) ≤ 4 * (Pc : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 4 hPle
  have hRpow : (4 * (P : ℝ)) ^ η ≤ (4 * (Pc : ℝ)) ^ η :=
    Real.rpow_le_rpow (by positivity) hBase hη.le
  have hCtC : Ct ≤ C := le_max_left _ _
  have hCaC : Ca ≤ C := le_max_right _ _
  have hFt : Ct * (4 * (P : ℝ)) ^ η ≤ C * (4 * (Pc : ℝ)) ^ η := by
    exact mul_le_mul hCtC hRpow (by positivity) hC.le
  have hFa : Ca * (4 * (Pc : ℝ)) ^ η ≤ C * (4 * (Pc : ℝ)) ^ η := by
    exact mul_le_mul_of_nonneg_right hCaC (by positivity)
  have hFactor :
      (Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
          (Ca * (4 * (Pc : ℝ)) ^ η) ^ 2 ≤
        (C * (4 * (Pc : ℝ)) ^ η) ^ 4 := by
    calc
      (Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
          (Ca * (4 * (Pc : ℝ)) ^ η) ^ 2 ≤
        (C * (4 * (Pc : ℝ)) ^ η) ^ 2 *
          (C * (4 * (Pc : ℝ)) ^ η) ^ 2 := by gcongr
      _ = (C * (4 * (Pc : ℝ)) ^ η) ^ 4 := by ring
  have hPairLine := hPair r c W hrc
  have hWeighted :
      8 * (P : ℝ) * (Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
          (heathBrownWeightedMoment P W +
            heathBrownWeightedMoment (2 * P) W) ≤
        64 * (P : ℝ) * (C * (4 * (Pc : ℝ)) ^ η) ^ 4 *
          (heathBrownWeightedMoment Pc W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
    have hTwoP : 2 * P = 2 ^ (r + 1) := by
      dsimp only [P]
      rw [pow_succ]
      ring
    rw [hTwoP]
    calc
      8 * (P : ℝ) * (Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
          (heathBrownWeightedMoment (2 ^ r) W +
            heathBrownWeightedMoment (2 ^ (r + 1)) W) ≤
        8 * (P : ℝ) * (Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
          (8 * (Ca * (4 * (Pc : ℝ)) ^ η) ^ 2 *
            (heathBrownWeightedMoment (2 ^ c) W +
              heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
        gcongr
      _ = 64 * (P : ℝ) *
          ((Ct * (4 * (P : ℝ)) ^ η) ^ 2 *
            (Ca * (4 * (Pc : ℝ)) ^ η) ^ 2) *
          (heathBrownWeightedMoment Pc W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
        dsimp only [P, Pc]
        ring
      _ ≤ 64 * (P : ℝ) * (C * (4 * (Pc : ℝ)) ^ η) ^ 4 *
          (heathBrownWeightedMoment Pc W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
        gcongr
        unfold heathBrownWeightedMoment
        positivity
  have hRaw := hTerminal M W
  change heathBrownReflectionDyadicMoment W M ≤
      2 * ((r : ℝ) + 1) *
        (((W.card : ℝ) ^ 2) + (r : ℝ) *
          (64 * (P : ℝ) * (C * (4 * (Pc : ℝ)) ^ η) ^ 4 *
            (heathBrownWeightedMoment Pc W +
              heathBrownWeightedMoment (2 ^ (c + 1)) W)))
  apply hRaw.trans
  gcongr

/-- One extra dyadic step above the common ceiling accommodates both adjacent
moments produced by the auxiliary transfer. -/
noncomputable def heathBrownCorrectedCommonExponent
    (Q H : ℕ) (T : ℝ) : ℕ :=
  Nat.clog 2 (heathBrownCommonReflectionLength Q H T) + 1

/-- Corrected common terminal scale for the source recurrence. -/
noncomputable def heathBrownCorrectedCommonScale
    (Q H : ℕ) (T : ℝ) : ℕ :=
  2 ^ heathBrownCorrectedCommonExponent Q H T

/-- Per-bin reflected-main estimate in the source order.  The first term is
the `R²` diagonal.  The second is the recursive term after the binwise dual
length has cancelled one power of the original scale. -/
theorem exists_heathBrownStationaryBinMain_le_common_preserving_length
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C T : ℝ) (W : Finset ℝ) (Q H j : ℕ),
        0 < Q → 0 < H →
        j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1) →
        2 ≤ j ∧ 2 * H ≤ 2 ^ j →
        ¬ 2 ^ (j + 1) ≤ Q →
        2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * (H : ℝ)) ^ 2 *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j)) ≤
          8 * (Q : ℝ) ^ 2 * C ^ 2 * H *
              ((Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) + 1) *
              (W.card : ℝ) ^ 2 +
            2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
              ((Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) + 1) *
              (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) *
              (Ctr * (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
              (heathBrownWeightedMoment
                  (heathBrownCorrectedCommonScale Q H T) W +
                heathBrownWeightedMoment
                  (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W) := by
  obtain ⟨Ctr, hCtr, hReflection⟩ :=
    exists_heathBrownReflectionDyadicMoment_le_common_preserving_length η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C T W Q H j hQ hH hj hStationary hNotNear
  let M : ℕ := heathBrownFixedReflectionLength Q H j
  let r : ℕ := Nat.clog 2 M
  let c : ℕ := heathBrownCorrectedCommonExponent Q H T
  let P : ℕ := 2 ^ r
  let Pc : ℕ := 2 ^ c
  let A : ℝ :=
    2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
      (2 * (H : ℝ)) ^ 2
  have hMCommon : M ≤ heathBrownCommonReflectionLength Q H T := by
    dsimp only [M]
    exact heathBrownFixedReflectionLength_le_common hj hStationary.1
  have hrCommon : r ≤ Nat.clog 2 (heathBrownCommonReflectionLength Q H T) := by
    dsimp only [r]
    exact Nat.clog_mono_right 2 hMCommon
  have hrc : r + 1 ≤ c := by
    dsimp only [c, heathBrownCorrectedCommonExponent]
    omega
  have hMoment := hReflection M c W hrc
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAle : A ≤ 4 * (Q : ℝ) ^ 2 * C ^ 2 * H := by
    dsimp only [A]
    exact heathBrown_reflection_main_coefficient_le C Q H j hH hStationary.2
  have hAPle : A * (P : ℝ) ≤
      16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) := by
    dsimp only [A, P, r, M]
    exact heathBrown_reflection_main_coefficient_mul_terminalScale_le
      C Q H j hQ hH hNotNear
  have hWnonneg : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  have hSnonneg : 0 ≤
      heathBrownWeightedMoment Pc W +
        heathBrownWeightedMoment (2 ^ (c + 1)) W := by
    unfold heathBrownWeightedMoment
    positivity
  have hRecursiveNonneg : 0 ≤
      (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment Pc W +
          heathBrownWeightedMoment (2 ^ (c + 1)) W) := by positivity
  rw [← mul_assoc]
  change A * heathBrownReflectionDyadicMoment W M ≤ _
  calc
    A * heathBrownReflectionDyadicMoment W M ≤
        A * (2 * ((r : ℝ) + 1) *
          ((W.card : ℝ) ^ 2 +
            (r : ℝ) *
              (64 * (P : ℝ) *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)))) :=
      mul_le_mul_of_nonneg_left hMoment hA
    _ = (A * (2 * ((r : ℝ) + 1)) * (W.card : ℝ) ^ 2) +
        ((A * (P : ℝ)) *
          (128 * ((r : ℝ) + 1) * r *
            (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
            (heathBrownWeightedMoment Pc W +
              heathBrownWeightedMoment (2 ^ (c + 1)) W))) := by ring
    _ ≤ (8 * (Q : ℝ) ^ 2 * C ^ 2 * H * ((r : ℝ) + 1) *
          (W.card : ℝ) ^ 2) +
        (2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
          ((r : ℝ) + 1) * r *
          (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
          (heathBrownWeightedMoment Pc W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
      apply add_le_add
      · calc
          A * (2 * ((r : ℝ) + 1)) * (W.card : ℝ) ^ 2 ≤
              (4 * (Q : ℝ) ^ 2 * C ^ 2 * H) *
                (2 * ((r : ℝ) + 1)) * (W.card : ℝ) ^ 2 := by
            gcongr
          _ = 8 * (Q : ℝ) ^ 2 * C ^ 2 * H * ((r : ℝ) + 1) *
                (W.card : ℝ) ^ 2 := by ring
      · calc
          (A * (P : ℝ)) *
              (128 * ((r : ℝ) + 1) * r *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)) ≤
            (16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2)) *
              (128 * ((r : ℝ) + 1) * r *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
              gcongr
          _ = 2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
              ((r : ℝ) + 1) * r *
              (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
              (heathBrownWeightedMoment Pc W +
                heathBrownWeightedMoment (2 ^ (c + 1)) W) := by ring
    _ = _ := by rfl

/-- Source-sharp stationary-bin estimate.  In contrast with the coarse
uniform form above, the diagonal term retains the factor `Q / 2^j`.  The
non-near condition makes that ratio at most two, so after division by the
original source scale this contributes the `R²` term of Lemma 29.10 rather
than the spurious `N R²` term. -/
theorem exists_heathBrownStationaryBinMain_le_source_sharp
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C T : ℝ) (W : Finset ℝ) (Q H j : ℕ),
        0 < Q → 0 < H →
        j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1) →
        2 ≤ j ∧ 2 * H ≤ 2 ^ j →
        ¬ 2 ^ (j + 1) ≤ Q →
        2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
            ((2 * (H : ℝ)) ^ 2 *
              heathBrownReflectionDyadicMoment W
                (heathBrownFixedReflectionLength Q H j)) ≤
          32 * (Q : ℝ) * C ^ 2 * H ^ 2 *
              (heathBrownCorrectedCommonExponent Q H T : ℝ) *
              (W.card : ℝ) ^ 2 +
            2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
              (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 *
              (Ctr *
                (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
              (heathBrownWeightedMoment
                  (heathBrownCorrectedCommonScale Q H T) W +
                heathBrownWeightedMoment
                  (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W) := by
  obtain ⟨Ctr, hCtr, hReflection⟩ :=
    exists_heathBrownReflectionDyadicMoment_le_common_preserving_length η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C T W Q H j hQ hH hj hStationary hNotNear
  let M : ℕ := heathBrownFixedReflectionLength Q H j
  let r : ℕ := Nat.clog 2 M
  let c : ℕ := heathBrownCorrectedCommonExponent Q H T
  let P : ℕ := 2 ^ r
  let Pc : ℕ := 2 ^ c
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  let B : ℝ :=
    2 * (((Q : ℝ) * C / Real.sqrt X) ^ 2) * (2 * (H : ℝ)) ^ 2
  have hMCommon : M ≤ heathBrownCommonReflectionLength Q H T := by
    dsimp only [M]
    exact heathBrownFixedReflectionLength_le_common hj hStationary.1
  have hrCommon : r ≤ Nat.clog 2 (heathBrownCommonReflectionLength Q H T) := by
    dsimp only [r]
    exact Nat.clog_mono_right 2 hMCommon
  have hrc : r + 1 ≤ c := by
    dsimp only [c, heathBrownCorrectedCommonExponent]
    omega
  have hMoment := hReflection M c W hrc
  have hX : 0 < X := by dsimp only [X]; positivity
  have hQlt : Q < 2 ^ (j + 1) := by omega
  have hQleTwoX : (Q : ℝ) ≤ 2 * X := by
    have hcast : (Q : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hQlt
    have hpow : (((2 ^ (j + 1) : ℕ) : ℝ)) = 2 * X := by
      dsimp only [X]
      rw [pow_succ]
      push_cast
      ring
    rw [hpow] at hcast
    exact hcast.le
  have hRatio : (Q : ℝ) / X ≤ 2 := by
    rw [div_le_iff₀ hX]
    simpa only [two_mul] using hQleTwoX
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBSharp : B ≤ 16 * (Q : ℝ) * C ^ 2 * H ^ 2 := by
    have hEq : B =
        8 * (Q : ℝ) * C ^ 2 * H ^ 2 * ((Q : ℝ) / X) := by
      dsimp only [B]
      rw [div_pow, Real.sq_sqrt hX.le]
      field_simp
      ring
    rw [hEq]
    calc
      8 * (Q : ℝ) * C ^ 2 * H ^ 2 * ((Q : ℝ) / X) ≤
          8 * (Q : ℝ) * C ^ 2 * H ^ 2 * 2 := by gcongr
      _ = 16 * (Q : ℝ) * C ^ 2 * H ^ 2 := by ring
  have hBPLocal : B * (P : ℝ) ≤
      16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) := by
    dsimp only [B, P, r, M, X]
    exact heathBrown_reflection_main_coefficient_mul_terminalScale_le
      C Q H j hQ hH hNotNear
  have hCReal : (r : ℝ) + 1 ≤ c := by exact_mod_cast hrc
  have hWnonneg : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  have hRecursiveNonneg : 0 ≤
      (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment Pc W +
          heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
    unfold heathBrownWeightedMoment
    positivity
  rw [← mul_assoc]
  change B * heathBrownReflectionDyadicMoment W M ≤ _
  calc
    B * heathBrownReflectionDyadicMoment W M ≤
        B * (2 * ((r : ℝ) + 1) *
          ((W.card : ℝ) ^ 2 +
            (r : ℝ) *
              (64 * (P : ℝ) *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)))) :=
      mul_le_mul_of_nonneg_left hMoment hB
    _ = (B * (2 * ((r : ℝ) + 1)) * (W.card : ℝ) ^ 2) +
        ((B * (P : ℝ)) *
          (128 * ((r : ℝ) + 1) * r *
            (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
            (heathBrownWeightedMoment Pc W +
              heathBrownWeightedMoment (2 ^ (c + 1)) W))) := by ring
    _ ≤ (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * (W.card : ℝ) ^ 2) +
        (2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
          (c : ℝ) ^ 2 *
          (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
          (heathBrownWeightedMoment Pc W +
            heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
      apply add_le_add
      · calc
          B * (2 * ((r : ℝ) + 1)) * (W.card : ℝ) ^ 2 ≤
              (16 * (Q : ℝ) * C ^ 2 * H ^ 2) *
                (2 * (c : ℝ)) * (W.card : ℝ) ^ 2 := by gcongr
          _ = 32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c *
                (W.card : ℝ) ^ 2 := by ring
      · calc
          (B * (P : ℝ)) *
              (128 * ((r : ℝ) + 1) * r *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)) ≤
            (16 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2)) *
              (128 * (c : ℝ) * c *
                (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                (heathBrownWeightedMoment Pc W +
                  heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
                have hrle : (r : ℝ) ≤ c := by
                  exact_mod_cast (show r ≤ c by omega)
                have hrr : ((r : ℝ) + 1) * r ≤ (c : ℝ) * c :=
                  mul_le_mul hCReal hrle (by positivity) (by positivity)
                have hS : 0 ≤ heathBrownWeightedMoment Pc W +
                    heathBrownWeightedMoment (2 ^ (c + 1)) W := by
                  unfold heathBrownWeightedMoment
                  positivity
                have hTail :
                    128 * ((r : ℝ) + 1) * r *
                        (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                        (heathBrownWeightedMoment Pc W +
                          heathBrownWeightedMoment (2 ^ (c + 1)) W) ≤
                      128 * (c : ℝ) * c *
                        (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                        (heathBrownWeightedMoment Pc W +
                          heathBrownWeightedMoment (2 ^ (c + 1)) W) := by
                  calc
                    _ = 128 * (((r : ℝ) + 1) * r) *
                        ((Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                          (heathBrownWeightedMoment Pc W +
                            heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by ring
                    _ ≤ 128 * ((c : ℝ) * c) *
                        ((Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
                          (heathBrownWeightedMoment Pc W +
                            heathBrownWeightedMoment (2 ^ (c + 1)) W)) := by
                      gcongr
                    _ = _ := by ring
                exact mul_le_mul hBPLocal hTail (by positivity) (by positivity)
          _ = 2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
              (c : ℝ) ^ 2 *
              (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
              (heathBrownWeightedMoment Pc W +
                heathBrownWeightedMoment (2 ^ (c + 1)) W) := by ring
    _ = _ := by rfl

/-- Summed source-sharp reflected main term.  The only outer loss is the
finite number of dyadic displacement bins; the original scale occurs to the
first power in both the diagonal and recursive contributions. -/
theorem exists_heathBrownSourceReflectedMainSum_le_source_sharp
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C T : ℝ) (W : Finset ℝ) (Q H : ℕ),
        0 < Q → 0 < H →
        heathBrownSourceReflectedMainSum C T W Q H ≤
          ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
            (32 * (Q : ℝ) * C ^ 2 * H ^ 2 *
                (heathBrownCorrectedCommonExponent Q H T : ℝ) *
                (W.card : ℝ) ^ 2 +
              2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
                (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 *
                (Ctr *
                  (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
                (heathBrownWeightedMoment
                    (heathBrownCorrectedCommonScale Q H T) W +
                  heathBrownWeightedMoment
                    (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W)) := by
  obtain ⟨Ctr, hCtr, hBin⟩ :=
    exists_heathBrownStationaryBinMain_le_source_sharp η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C T W Q H hQ hH
  let c : ℕ := heathBrownCorrectedCommonExponent Q H T
  let Pc : ℕ := heathBrownCorrectedCommonScale Q H T
  let B : ℝ :=
    32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * (W.card : ℝ) ^ 2 +
      2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * (c : ℝ) ^ 2 *
        (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment Pc W +
          heathBrownWeightedMoment (2 ^ (c + 1)) W)
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold heathBrownWeightedMoment
    positivity
  unfold heathBrownSourceReflectedMainSum
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ^ (j + 1) ≤ Q then 0
      else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
        2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
          ((2 * (H : ℝ)) ^ 2 *
            heathBrownReflectionDyadicMoment W
              (heathBrownFixedReflectionLength Q H j))
      else 0) ≤
        ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), B := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hNear : 2 ^ (j + 1) ≤ Q
      · rw [if_pos hNear]
        exact hB
      · rw [if_neg hNear]
        by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
        · rw [if_pos hStationary]
          simpa only [B, c, Pc] using
            hBin C T W Q H j hQ hH hj hStationary hNear
        · rw [if_neg hStationary]
          exact hB
    _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) * B := by simp
    _ = _ := by rfl

/-- Summed reflected-main contribution in the corrected source recurrence.
All logarithmic factors are now explicit, while the recursive scale is common
to every displacement bin. -/
theorem exists_heathBrownSourceReflectedMainSum_le
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (C T : ℝ) (W : Finset ℝ) (Q H : ℕ),
        0 < Q → 0 < H →
        heathBrownSourceReflectedMainSum C T W Q H ≤
          ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) *
            (8 * (Q : ℝ) ^ 2 * C ^ 2 * H *
                (heathBrownCorrectedCommonExponent Q H T : ℝ) *
                (W.card : ℝ) ^ 2 +
              2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
                (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 *
                (Ctr *
                  (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
                (heathBrownWeightedMoment
                    (heathBrownCorrectedCommonScale Q H T) W +
                  heathBrownWeightedMoment
                    (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W)) := by
  obtain ⟨Ctr, hCtr, hBin⟩ :=
    exists_heathBrownStationaryBinMain_le_common_preserving_length η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro C T W Q H hQ hH
  let c : ℕ := heathBrownCorrectedCommonExponent Q H T
  let Pc : ℕ := heathBrownCorrectedCommonScale Q H T
  let B : ℝ :=
    8 * (Q : ℝ) ^ 2 * C ^ 2 * H * (c : ℝ) * (W.card : ℝ) ^ 2 +
      2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * (c : ℝ) ^ 2 *
        (Ctr * (4 * (Pc : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment Pc W +
          heathBrownWeightedMoment (2 ^ (c + 1)) W)
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hS : 0 ≤ heathBrownWeightedMoment Pc W +
        heathBrownWeightedMoment (2 ^ (c + 1)) W := by
      unfold heathBrownWeightedMoment
      positivity
    positivity
  unfold heathBrownSourceReflectedMainSum
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ^ (j + 1) ≤ Q then 0
      else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
        2 * (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ 2) *
          ((2 * (H : ℝ)) ^ 2 *
            heathBrownReflectionDyadicMoment W
              (heathBrownFixedReflectionLength Q H j))
      else 0) ≤
        ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1), B := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hNear : 2 ^ (j + 1) ≤ Q
      · rw [if_pos hNear]
        exact hB
      · rw [if_neg hNear]
        by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
        · rw [if_pos hStationary]
          have hLocal := hBin C T W Q H j hQ hH hj hStationary hNear
          have hMCommon := heathBrownFixedReflectionLength_le_common
            (Q := Q) (H := H) hj hStationary.1
          have hrCommon :
              Nat.clog 2 (heathBrownFixedReflectionLength Q H j) ≤
                Nat.clog 2 (heathBrownCommonReflectionLength Q H T) :=
            Nat.clog_mono_right 2 hMCommon
          have hrOne :
              (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) + 1 ≤
                c := by
            dsimp only [c, heathBrownCorrectedCommonExponent]
            exact_mod_cast Nat.add_le_add_right hrCommon 1
          have hr :
              (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) ≤ c := by
            linarith
          apply hLocal.trans
          dsimp only [B, Pc, c]
          apply add_le_add
          · gcongr
          · have hS : 0 ≤
                heathBrownWeightedMoment
                    (heathBrownCorrectedCommonScale Q H T) W +
                  heathBrownWeightedMoment
                    (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W := by
              unfold heathBrownWeightedMoment
              positivity
            let K : ℝ :=
              2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
                (Ctr *
                  (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
                (heathBrownWeightedMoment
                    (heathBrownCorrectedCommonScale Q H T) W +
                  heathBrownWeightedMoment
                    (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W)
            have hK : 0 ≤ K := by dsimp only [K]; positivity
            have hLogs :
                ((Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) + 1) *
                    (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) ≤
                  (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 := by
              nlinarith
            calc
              2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
                    ((Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) + 1) *
                    (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ) *
                    (Ctr *
                      (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
                    (heathBrownWeightedMoment
                        (heathBrownCorrectedCommonScale Q H T) W +
                      heathBrownWeightedMoment
                        (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W) =
                  K * (((Nat.clog 2
                    (heathBrownFixedReflectionLength Q H j) : ℝ) + 1) *
                    (Nat.clog 2 (heathBrownFixedReflectionLength Q H j) : ℝ)) := by
                dsimp only [K]
                ring
              _ ≤ K * (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hLogs hK
              _ = 2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) *
                    (heathBrownCorrectedCommonExponent Q H T : ℝ) ^ 2 *
                    (Ctr *
                      (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η) ^ 4 *
                    (heathBrownWeightedMoment
                        (heathBrownCorrectedCommonScale Q H T) W +
                      heathBrownWeightedMoment
                        (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W) := by
                dsimp only [K]
                ring
        · rw [if_neg hStationary]
          exact hB
    _ = ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) * B := by simp
    _ = _ := by rfl

/-- The corrected source error sum is a sub-sum of the already audited
complete reflection error family. -/
theorem heathBrownSourceReflectedErrorSum_le_hybridErrorSum
    (K L D : ℝ) (q : ℕ) (T : ℝ) (W : Finset ℝ) (Q H : ℕ) :
    heathBrownSourceReflectedErrorSum K L D q T W Q H ≤
      heathBrownHybridErrorSum K L D q T W Q H := by
  unfold heathBrownSourceReflectedErrorSum heathBrownHybridErrorSum
  apply Finset.sum_le_sum
  intro j hj
  by_cases hNear : 2 ^ (j + 1) ≤ Q
  · rw [if_pos hNear]
    split_ifs
    · positivity
    · rfl
  · rw [if_neg hNear]

/-- Uniform estimate for every omitted-frequency family in the corrected
source schedule. -/
theorem heathBrownSourceReflectedErrorSum_le_uniform
    (K L D : ℝ) (q Q H : ℕ) (T : ℝ) (W : Finset ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) :
    heathBrownSourceReflectedErrorSum K L D q T W Q H ≤
      (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
        (8 * (W.card : ℝ) * T *
          (heathBrownUniformReflectionError K L D q Q H T) ^ 2) :=
  (heathBrownSourceReflectedErrorSum_le_hybridErrorSum K L D q T W Q H).trans
    (heathBrownHybridErrorSum_le_uniform K L D q Q H T W
      hK hL hD hQ hH hT hSep)

/-- Source-sharp uniform error: unlike the earlier coarse majorant, this
retains the cancellation of `X^q` in the omitted-frequency denominator.
Consequently only `T^2`, rather than `T^(q+2)`, remains. -/
noncomputable def heathBrownSharpUniformReflectionError
    (K L D : ℝ) (q Q H : ℕ) (T : ℝ) : ℝ :=
  K / Q * T ^ 2 * (H + 2 : ℝ) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) +
    L / Q * (3 : ℝ) ^ (q + 2) * T ^ 2 / (H : ℝ) ^ q +
    (Q : ℝ) * D / (H : ℝ) ^ q

theorem heathBrownReflectionBinError_fixed_le_sharp_uniform
    (K L D : ℝ) (q Q H j : ℕ) (T : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hQ : 0 < Q) (hH : 0 < H)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j)
    (hNotNear : ¬ 2 ^ (j + 1) ≤ Q) :
    heathBrownReflectionBinError q Q
        (heathBrownFixedReflectionLength Q H j) H
        (((2 ^ (j + 1) : ℕ) : ℝ)) (((2 ^ j : ℕ) : ℝ)) K L D ≤
      heathBrownSharpUniformReflectionError K L D q Q H T := by
  let X : ℝ := ((2 ^ j : ℕ) : ℝ)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hXLeFloor := two_pow_le_floor_of_mem_difference_range hj hStationary.1
  have hFloorPos : 0 < Nat.floor T := lt_of_lt_of_le (by positivity) hXLeFloor
  have hTOne : 1 ≤ T := Nat.floor_pos.mp hFloorPos
  have hXT : X ≤ T := by
    calc
      X ≤ (Nat.floor T : ℝ) := by
        dsimp only [X]
        exact_mod_cast hXLeFloor
      _ ≤ T := Nat.floor_le (by linarith)
  have hQlt : Q < 2 ^ (j + 1) := by omega
  have hQTwoX : (Q : ℝ) ≤ 2 * X := by
    have hcast : (Q : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hQlt
    have hp : (((2 ^ (j + 1) : ℕ) : ℝ)) = 2 * X := by
      dsimp only [X]
      rw [pow_succ]
      push_cast
      ring
    rw [hp] at hcast
    exact hcast.le
  have hHleX : (H : ℝ) ≤ X := by
    have hNat : H ≤ 2 ^ j := by omega
    dsimp only [X]
    exact_mod_cast hNat
  have hFirstBase : X * H + Q ≤ X * (H + 2) := by nlinarith
  have hFirstSq : (X * H + Q) ^ 2 ≤ (X * (H + 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hFirstBase 2
  have hNumerBase : 1 + 2 * X ≤ 3 * X := by
    have hOneX : 1 ≤ X := by
      dsimp only [X]
      exact_mod_cast Nat.one_le_pow j 2 (by omega)
    linarith
  have hNumerPow : (1 + 2 * X) ^ (q + 2) ≤ (3 * X) ^ (q + 2) :=
    pow_le_pow_left₀ (by positivity) hNumerBase (q + 2)
  have hSecondExact :
      L / (Q : ℝ) * (3 * X) ^ (q + 2) / ((X * H) ^ q) =
        L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * X ^ 2 / (H : ℝ) ^ q := by
    rw [mul_pow, mul_pow, pow_add]
    field_simp
    ring
  have hRaw := heathBrownReflectionBinError_fixed_le
    K L D q Q H j hK hL hQ hH
  have hFirst :
      K / (Q : ℝ) * (X * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) ≤
        K / (Q : ℝ) * T ^ 2 * (H + 2 : ℝ) ^ 2 *
          (H : ℝ) ^ (1 - (q : ℝ)) := by
    have hXTpow : X ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hX.le hXT 2
    calc
      K / (Q : ℝ) * (X * H + Q) ^ 2 * (H : ℝ) ^ (1 - (q : ℝ)) ≤
          K / (Q : ℝ) * (X * (H + 2)) ^ 2 *
            (H : ℝ) ^ (1 - (q : ℝ)) := by gcongr
      _ = K / (Q : ℝ) * X ^ 2 * (H + 2 : ℝ) ^ 2 *
            (H : ℝ) ^ (1 - (q : ℝ)) := by ring
      _ ≤ K / (Q : ℝ) * T ^ 2 * (H + 2 : ℝ) ^ 2 *
            (H : ℝ) ^ (1 - (q : ℝ)) := by gcongr
  have hSecond :
      L / (Q : ℝ) * (1 + 2 * X) ^ (q + 2) / ((X * H) ^ q) ≤
        L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * T ^ 2 / (H : ℝ) ^ q := by
    calc
      L / (Q : ℝ) * (1 + 2 * X) ^ (q + 2) / ((X * H) ^ q) ≤
          L / (Q : ℝ) * (3 * X) ^ (q + 2) / ((X * H) ^ q) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
      _ = L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * X ^ 2 / (H : ℝ) ^ q :=
        hSecondExact
      _ ≤ L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * T ^ 2 / (H : ℝ) ^ q := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
  have hThird :
      (Q : ℝ) * D / X ^ q ≤ (Q : ℝ) * D / (H : ℝ) ^ q :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hHReal.le hHleX q)
  dsimp only [X] at hRaw hFirst hSecond hThird
  unfold heathBrownSharpUniformReflectionError
  exact hRaw.trans (add_le_add (add_le_add hFirst hSecond) hThird)

theorem heathBrownSourceReflectedErrorSum_le_sharp_uniform
    (K L D : ℝ) (q Q H : ℕ) (T : ℝ) (W : Finset ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) :
    heathBrownSourceReflectedErrorSum K L D q T W Q H ≤
      (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
        (8 * (W.card : ℝ) * T *
          (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2) := by
  have hTNonneg : 0 ≤ T := zero_le_one.trans hT
  have hSharpNonneg : 0 ≤
      heathBrownSharpUniformReflectionError K L D q Q H T := by
    unfold heathBrownSharpUniformReflectionError
    positivity
  unfold heathBrownSourceReflectedErrorSum
  calc
    (∑ j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
      if 2 ^ (j + 1) ≤ Q then 0
      else if 2 ≤ j ∧ 2 * H ≤ 2 ^ j then
        2 * ((heathBrownDifferenceBin W j).card : ℝ) *
          (heathBrownReflectionBinError q Q
            (heathBrownFixedReflectionLength Q H j) H
            (((2 ^ (j + 1) : ℕ) : ℝ))
            (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2
      else 0) ≤
        ∑ _j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1),
          8 * (W.card : ℝ) * T *
            (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hNear : 2 ^ (j + 1) ≤ Q
      · rw [if_pos hNear]
        positivity
      · rw [if_neg hNear]
        by_cases hStationary : 2 ≤ j ∧ 2 * H ≤ 2 ^ j
        · rw [if_pos hStationary]
          have hErr := heathBrownReflectionBinError_fixed_le_sharp_uniform
            K L D q Q H j T hK hL hD hQ hH hj hStationary hNear
          have hRawNonneg : 0 ≤
              heathBrownReflectionBinError q Q
                (heathBrownFixedReflectionLength Q H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D := by
            unfold heathBrownReflectionBinError
            positivity
          have hErrSq :
              (heathBrownReflectionBinError q Q
                (heathBrownFixedReflectionLength Q H j) H
                (((2 ^ (j + 1) : ℕ) : ℝ))
                (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 ≤
                (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2 :=
            pow_le_pow_left₀ hRawNonneg hErr 2
          have hCardNat := heathBrownDifferenceBin_card_le W j hSep
          have hPowFloor := two_pow_le_floor_of_mem_difference_range
            hj hStationary.1
          have hPowT : (((2 ^ j : ℕ) : ℝ)) ≤ T := by
            calc
              (((2 ^ j : ℕ) : ℝ)) ≤ (Nat.floor T : ℝ) := by
                exact_mod_cast hPowFloor
              _ ≤ T := Nat.floor_le hTNonneg
          have hCardReal : ((heathBrownDifferenceBin W j).card : ℝ) ≤
              (W.card : ℝ) * (4 * T) := by
            calc
              ((heathBrownDifferenceBin W j).card : ℝ) ≤
                  (W.card : ℝ) * (2 * (((2 ^ (j + 1) : ℕ) : ℝ))) := by
                exact_mod_cast hCardNat
              _ = (W.card : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ))) := by
                rw [pow_succ]
                push_cast
                ring
              _ ≤ (W.card : ℝ) * (4 * T) := by gcongr
          calc
            2 * ((heathBrownDifferenceBin W j).card : ℝ) *
                (heathBrownReflectionBinError q Q
                  (heathBrownFixedReflectionLength Q H j) H
                  (((2 ^ (j + 1) : ℕ) : ℝ))
                  (((2 ^ j : ℕ) : ℝ)) K L D) ^ 2 ≤
              2 * ((W.card : ℝ) * (4 * T)) *
                (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2 := by
              gcongr
            _ = 8 * (W.card : ℝ) * T *
                (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2 := by
              ring
        · rw [if_neg hStationary]
          positivity
    _ = (Nat.log 2 (Nat.floor T) + 1 : ℕ) *
        (8 * (W.card : ℝ) * T *
          (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2) := by
      simp

/-- Explicit corrected source recurrence for one smooth trace scale. -/
noncomputable def heathBrownCorrectedTraceRecurrenceBound
    (Cnear C Ctr K L D η : ℝ) (q : ℕ) (T : ℝ)
    (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  let ℓ : ℝ := (Nat.log 2 (Nat.floor T) + 1 : ℕ)
  let c : ℝ := heathBrownCorrectedCommonExponent Q H T
  let P : ℕ := heathBrownCorrectedCommonScale Q H T
  (W.card : ℝ) * Q ^ 2 +
    8 * (W.card : ℝ) * Cnear ^ 2 * Q ^ 2 +
    ℓ * (8 * (W.card : ℝ) * H * Q ^ 2) +
    ℓ * (8 * (Q : ℝ) ^ 2 * C ^ 2 * H * c * (W.card : ℝ) ^ 2 +
      2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
        (Ctr * (4 * (P : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment P W +
          heathBrownWeightedMoment
            (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W)) +
    ℓ * (8 * (W.card : ℝ) * T *
      (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2)

theorem exists_heathBrownTraceSourceBound_le_corrected_recurrence
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (Cnear C K L D : ℝ) (q : ℕ) (T : ℝ)
        (W : Finset ℝ) (Q H : ℕ),
        0 ≤ K → 0 ≤ L → 0 ≤ D →
        4 ≤ Q → 0 < H → 1 ≤ T → IsSeparated 1 W →
        heathBrownTraceSourceBound Cnear C K L D q T W Q H ≤
          heathBrownCorrectedTraceRecurrenceBound
            Cnear C Ctr K L D η q T W Q H := by
  obtain ⟨Ctr, hCtr, hMain⟩ :=
    exists_heathBrownSourceReflectedMainSum_le η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro Cnear C K L D q T W Q H hK hL hD hQ hH hT hSep
  have hQPos : 0 < Q := by omega
  have hNear := heathBrownSourceNearSum_le Cnear T W Q
  have hTransition := heathBrownSourceTransitionSum_le T W Q H hQ hSep
  have hMainLine := hMain C T W Q H hQPos hH
  have hError := heathBrownSourceReflectedErrorSum_le_sharp_uniform
    K L D q Q H T W hK hL hD hQPos hH hT hSep
  rw [heathBrownTraceSourceBound_eq_components]
  unfold heathBrownCorrectedTraceRecurrenceBound
  dsimp only
  linarith

/-- Source-facing corrected recurrence for the actual weighted Jutila moment.
This composes the exact three-piece localization with every analytic estimate
above; no trace-scale hypothesis remains. -/
theorem exists_heathBrownWeightedMoment_le_corrected_recurrence
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hη : 0 < η) :
    ∃ Cnear C Ctr K L D : ℝ,
      0 < Cnear ∧ 0 < C ∧ 0 < Ctr ∧
      0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H → 1 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        (N : ℝ) * heathBrownWeightedMoment N W ≤
          3 *
            (heathBrownCorrectedTraceRecurrenceBound
                Cnear C Ctr K L D η q T W (gmSourceLeftScale N) H +
              heathBrownCorrectedTraceRecurrenceBound
                Cnear C Ctr K L D η q T W N H +
              heathBrownCorrectedTraceRecurrenceBound
                Cnear C Ctr K L D η q T W (gmSourceRightScale N) H) := by
  obtain ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, hSource⟩ :=
    heathBrownWeightedMoment_le_source_bound cutoff q hq
  obtain ⟨Ctr, hCtr, hTrace⟩ :=
    exists_heathBrownTraceSourceBound_le_corrected_recurrence η hη
  refine ⟨Cnear, C, Ctr, K, L, D,
    hCnear, hC, hCtr, hK, hL, hD, ?_⟩
  intro N H T W hN hH hT hSep hInterval
  have hLeft : 4 ≤ gmSourceLeftScale N := by
    unfold gmSourceLeftScale
    omega
  have hMiddle : 4 ≤ N := by omega
  have hRight : 4 ≤ gmSourceRightScale N := by
    unfold gmSourceRightScale
    omega
  have hRaw := hSource hN hH hSep hInterval
  have h₁ := hTrace Cnear C K L D q T W
    (gmSourceLeftScale N) H hK.le hL.le hD.le hLeft hH hT hSep
  have h₂ := hTrace Cnear C K L D q T W
    N H hK.le hL.le hD.le hMiddle hH hT hSep
  have h₃ := hTrace Cnear C K L D q T W
    (gmSourceRightScale N) H hK.le hL.le hD.le hRight hH hT hSep
  calc
    (N : ℝ) * heathBrownWeightedMoment N W ≤
        3 * (heathBrownTraceSourceBound Cnear C K L D q T W
              (gmSourceLeftScale N) H +
          heathBrownTraceSourceBound Cnear C K L D q T W N H +
          heathBrownTraceSourceBound Cnear C K L D q T W
            (gmSourceRightScale N) H) := hRaw
    _ ≤ 3 *
        (heathBrownCorrectedTraceRecurrenceBound
              Cnear C Ctr K L D η q T W (gmSourceLeftScale N) H +
          heathBrownCorrectedTraceRecurrenceBound
              Cnear C Ctr K L D η q T W N H +
          heathBrownCorrectedTraceRecurrenceBound
              Cnear C Ctr K L D η q T W (gmSourceRightScale N) H) := by
      gcongr

/-- The source-sharp one-scale recurrence.  This is the quantitative form
which is suitable for Montgomery--Vaughan Lemma 29.10: every occurrence of
the original scale outside the elementary `R Q` term is only linear. -/
noncomputable def heathBrownSourceSharpTraceRecurrenceBound
    (Cnear C Ctr K L D η : ℝ) (q : ℕ) (T : ℝ)
    (W : Finset ℝ) (Q H : ℕ) : ℝ :=
  let ℓ : ℝ := (Nat.log 2 (Nat.floor T) + 1 : ℕ)
  let c : ℝ := heathBrownCorrectedCommonExponent Q H T
  let P : ℕ := heathBrownCorrectedCommonScale Q H T
  (W.card : ℝ) * Q ^ 2 +
    8 * (W.card : ℝ) * Cnear ^ 2 * Q ^ 2 +
    ℓ * (8 * (W.card : ℝ) * H * Q ^ 2) +
    ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * (W.card : ℝ) ^ 2 +
      2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
        (Ctr * (4 * (P : ℝ)) ^ η) ^ 4 *
        (heathBrownWeightedMoment P W +
          heathBrownWeightedMoment
            (2 ^ (heathBrownCorrectedCommonExponent Q H T + 1)) W)) +
    ℓ * (8 * (W.card : ℝ) * T *
      (heathBrownSharpUniformReflectionError K L D q Q H T) ^ 2)

theorem exists_heathBrownTraceSourceBound_le_source_sharp_recurrence
    (η : ℝ) (hη : 0 < η) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (Cnear C K L D : ℝ) (q : ℕ) (T : ℝ)
        (W : Finset ℝ) (Q H : ℕ),
        0 ≤ K → 0 ≤ L → 0 ≤ D →
        4 ≤ Q → 0 < H → 1 ≤ T → IsSeparated 1 W →
        heathBrownTraceSourceBound Cnear C K L D q T W Q H ≤
          heathBrownSourceSharpTraceRecurrenceBound
            Cnear C Ctr K L D η q T W Q H := by
  obtain ⟨Ctr, hCtr, hMain⟩ :=
    exists_heathBrownSourceReflectedMainSum_le_source_sharp η hη
  refine ⟨Ctr, hCtr, ?_⟩
  intro Cnear C K L D q T W Q H hK hL hD hQ hH hT hSep
  have hQPos : 0 < Q := by omega
  have hNear := heathBrownSourceNearSum_le Cnear T W Q
  have hTransition := heathBrownSourceTransitionSum_le T W Q H hQ hSep
  have hMainLine := hMain C T W Q H hQPos hH
  have hError := heathBrownSourceReflectedErrorSum_le_sharp_uniform
    K L D q Q H T W hK hL hD hQPos hH hT hSep
  rw [heathBrownTraceSourceBound_eq_components]
  unfold heathBrownSourceSharpTraceRecurrenceBound
  dsimp only
  linarith

/-- Actual weighted Jutila moment with the source-sharp recurrence consumed
at each of the three exact smooth-localization scales. -/
theorem exists_heathBrownWeightedMoment_le_source_sharp_recurrence
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q)
    (η : ℝ) (hη : 0 < η) :
    ∃ Cnear C Ctr K L D : ℝ,
      0 < Cnear ∧ 0 < C ∧ 0 < Ctr ∧
      0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ {N H : ℕ} {T : ℝ} {W : Finset ℝ},
        30 ≤ N → 0 < H → 1 ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        (N : ℝ) * heathBrownWeightedMoment N W ≤
          3 *
            (heathBrownSourceSharpTraceRecurrenceBound
                Cnear C Ctr K L D η q T W (gmSourceLeftScale N) H +
              heathBrownSourceSharpTraceRecurrenceBound
                Cnear C Ctr K L D η q T W N H +
              heathBrownSourceSharpTraceRecurrenceBound
                Cnear C Ctr K L D η q T W (gmSourceRightScale N) H) := by
  obtain ⟨Cnear, C, K, L, D, hCnear, hC, hK, hL, hD, hSource⟩ :=
    heathBrownWeightedMoment_le_source_bound cutoff q hq
  obtain ⟨Ctr, hCtr, hTrace⟩ :=
    exists_heathBrownTraceSourceBound_le_source_sharp_recurrence η hη
  refine ⟨Cnear, C, Ctr, K, L, D,
    hCnear, hC, hCtr, hK, hL, hD, ?_⟩
  intro N H T W hN hH hT hSep hInterval
  have hLeft : 4 ≤ gmSourceLeftScale N := by
    unfold gmSourceLeftScale
    omega
  have hMiddle : 4 ≤ N := by omega
  have hRight : 4 ≤ gmSourceRightScale N := by
    unfold gmSourceRightScale
    omega
  have hRaw := hSource hN hH hSep hInterval
  have h₁ := hTrace Cnear C K L D q T W
    (gmSourceLeftScale N) H hK.le hL.le hD.le hLeft hH hT hSep
  have h₂ := hTrace Cnear C K L D q T W
    N H hK.le hL.le hD.le hMiddle hH hT hSep
  have h₃ := hTrace Cnear C K L D q T W
    (gmSourceRightScale N) H hK.le hL.le hD.le hRight hH hT hSep
  calc
    (N : ℝ) * heathBrownWeightedMoment N W ≤
        3 * (heathBrownTraceSourceBound Cnear C K L D q T W
              (gmSourceLeftScale N) H +
          heathBrownTraceSourceBound Cnear C K L D q T W N H +
          heathBrownTraceSourceBound Cnear C K L D q T W
            (gmSourceRightScale N) H) := hRaw
    _ ≤ 3 *
        (heathBrownSourceSharpTraceRecurrenceBound
              Cnear C Ctr K L D η q T W (gmSourceLeftScale N) H +
          heathBrownSourceSharpTraceRecurrenceBound
              Cnear C Ctr K L D η q T W N H +
          heathBrownSourceSharpTraceRecurrenceBound
              Cnear C Ctr K L D η q T W (gmSourceRightScale N) H) := by
      gcongr

/-- Integral smoothing height corresponding to the paper's `T^η` window. -/
noncomputable def heathBrownSmoothingHeight (T η : ℝ) : ℕ :=
  max 1 (Nat.ceil (T ^ η))

theorem heathBrownSmoothingHeight_pos (T η : ℝ) :
    0 < heathBrownSmoothingHeight T η := by
  unfold heathBrownSmoothingHeight
  omega

theorem rpow_le_heathBrownSmoothingHeight
    (T η : ℝ) :
    T ^ η ≤ (heathBrownSmoothingHeight T η : ℝ) := by
  unfold heathBrownSmoothingHeight
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 (Nat.ceil (T ^ η)))

theorem heathBrownSmoothingHeight_le_two_rpow
    {T η : ℝ} (hT : 1 ≤ T) (hη : 0 ≤ η) :
    (heathBrownSmoothingHeight T η : ℝ) ≤ 2 * T ^ η := by
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hT hη
  have hCeil : (Nat.ceil (T ^ η) : ℝ) < T ^ η + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
  unfold heathBrownSmoothingHeight
  push_cast
  rw [max_le_iff]
  constructor
  · linarith
  · linarith

theorem heathBrownCorrectedCommonScale_eq_two_mul_target
    (Q H : ℕ) (T : ℝ) :
    heathBrownCorrectedCommonScale Q H T =
      2 * heathBrownReflectionTargetScale Q H T := by
  unfold heathBrownCorrectedCommonScale heathBrownCorrectedCommonExponent
    heathBrownReflectionTargetScale
  rw [pow_succ]
  ring

theorem heathBrownCorrectedCommonScale_le_physical
    (Q H : ℕ) (T : ℝ) (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T) :
    (heathBrownCorrectedCommonScale Q H T : ℝ) ≤
      4 * (T * H / Q + 1) := by
  have hTarget := (heathBrownReflectionTargetScale_bounds_real
    Q H T hQ hH hT).2
  rw [heathBrownCorrectedCommonScale_eq_two_mul_target]
  push_cast
  linarith

/-- On the source range `Q ≥ 1`, the corrected reflected scale is at most a
fixed quadratic power of the height.  This is the physical-scale input which
keeps every later `clog` loss logarithmic. -/
theorem heathBrownCorrectedCommonScale_le_twelve_mul_sq
    {η T : ℝ} {Q H : ℕ} (hη : 0 ≤ η) (hηOne : η ≤ 1)
    (hT : 2 ≤ T) (hQ : 0 < Q)
    (hHeight : H = heathBrownSmoothingHeight T η) :
    (heathBrownCorrectedCommonScale Q H T : ℝ) ≤ 12 * T ^ 2 := by
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hHeightBound : (H : ℝ) ≤ 2 * T ^ η := by
    rw [hHeight]
    exact heathBrownSmoothingHeight_le_two_rpow hTOne hη
  have hPowLe : T ^ η ≤ T := by
    calc
      T ^ η ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hηOne
      _ = T := Real.rpow_one T
  have hDiv : T * (H : ℝ) / Q ≤ T * (H : ℝ) := by
    exact div_le_self (mul_nonneg hTPos.le (Nat.cast_nonneg H)) hQOne
  have hPhysical : T * (H : ℝ) / Q ≤ 2 * T ^ 2 := by
    calc
      T * (H : ℝ) / Q ≤ T * (H : ℝ) := hDiv
      _ ≤ T * (2 * T ^ η) := by gcongr
      _ ≤ T * (2 * T) := by gcongr
      _ = 2 * T ^ 2 := by ring
  have hScale := heathBrownCorrectedCommonScale_le_physical
    Q H T hQ (by rw [hHeight]; exact heathBrownSmoothingHeight_pos T η) hTOne
  have hSqOne : 1 ≤ T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTOne) (by linarith : 0 ≤ T + 1)]
  calc
    (heathBrownCorrectedCommonScale Q H T : ℝ) ≤
        4 * (T * H / Q + 1) := hScale
    _ ≤ 4 * (2 * T ^ 2 + 1) := by gcongr
    _ ≤ 12 * T ^ 2 := by nlinarith

/-- Derivative order large enough to absorb a prescribed polynomial error
after the `T^η` smoothing choice. -/
noncomputable def heathBrownReflectionDerivativeOrder
    (A η : ℝ) : ℕ :=
  max 2 (Nat.ceil ((A + 4) / η) + 1)

theorem heathBrownReflectionDerivativeOrder_two_le
    (A η : ℝ) :
    2 ≤ heathBrownReflectionDerivativeOrder A η := by
  unfold heathBrownReflectionDerivativeOrder
  exact le_max_left _ _

theorem heathBrownReflectionDerivativeOrder_budget
    {A η : ℝ} (hη : 0 < η) :
    A + 4 ≤ η * ((heathBrownReflectionDerivativeOrder A η : ℝ) - 1) := by
  let q : ℕ := heathBrownReflectionDerivativeOrder A η
  have hqNat : Nat.ceil ((A + 4) / η) + 1 ≤ q := by
    dsimp only [q, heathBrownReflectionDerivativeOrder]
    exact le_max_right _ _
  have hq : (Nat.ceil ((A + 4) / η) : ℝ) ≤ (q : ℝ) - 1 := by
    have hnat : Nat.ceil ((A + 4) / η) ≤ q - 1 := by omega
    have hcast : (Nat.ceil ((A + 4) / η) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    norm_num at hcast
    exact hcast
  have hceil : (A + 4) / η ≤ (Nat.ceil ((A + 4) / η) : ℝ) :=
    Nat.le_ceil _
  calc
    A + 4 = η * ((A + 4) / η) := by field_simp
    _ ≤ η * (Nat.ceil ((A + 4) / η) : ℝ) := by gcongr
    _ ≤ η * ((q : ℝ) - 1) := by gcongr

theorem heathBrownSmoothingHeight_rpow_one_sub_order_le
    {A η T : ℝ} (hη : 0 < η) (hT : 1 ≤ T) :
    (heathBrownSmoothingHeight T η : ℝ) ^
        (1 - (heathBrownReflectionDerivativeOrder A η : ℝ)) ≤
      T ^ (-(A + 4)) := by
  let q : ℕ := heathBrownReflectionDerivativeOrder A η
  have hq : 2 ≤ q := heathBrownReflectionDerivativeOrder_two_le A η
  have hHeightPos : (0 : ℝ) < heathBrownSmoothingHeight T η := by
    exact_mod_cast heathBrownSmoothingHeight_pos T η
  have hPowPos : 0 < T ^ η :=
    Real.rpow_pos_of_pos (by linarith) _
  have hLower := rpow_le_heathBrownSmoothingHeight T η
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hNonpos : 1 - (q : ℝ) ≤ 0 := by linarith
  have hReverse :
      (heathBrownSmoothingHeight T η : ℝ) ^ (1 - (q : ℝ)) ≤
        (T ^ η) ^ (1 - (q : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hPowPos hLower hNonpos
  have hBudget := heathBrownReflectionDerivativeOrder_budget
    (A := A) (η := η) hη
  have hExponent : η * (1 - (q : ℝ)) ≤ -(A + 4) := by linarith
  calc
    (heathBrownSmoothingHeight T η : ℝ) ^ (1 - (q : ℝ)) ≤
        (T ^ η) ^ (1 - (q : ℝ)) := hReverse
    _ = T ^ (η * (1 - (q : ℝ))) := by
      rw [Real.rpow_mul (by linarith : 0 ≤ T)]
    _ ≤ T ^ (-(A + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hT hExponent

theorem one_div_heathBrownSmoothingHeight_pow_order_le
    {A η T : ℝ} (hη : 0 < η) (hT : 1 ≤ T) :
    1 / (heathBrownSmoothingHeight T η : ℝ) ^
        heathBrownReflectionDerivativeOrder A η ≤
      T ^ (-(A + 4)) := by
  let H : ℝ := heathBrownSmoothingHeight T η
  let q : ℕ := heathBrownReflectionDerivativeOrder A η
  have hH : 1 ≤ H := by
    dsimp only [H, heathBrownSmoothingHeight]
    exact_mod_cast le_max_left 1 (Nat.ceil (T ^ η))
  have hExp : -(q : ℝ) ≤ 1 - (q : ℝ) := by linarith
  have hMono : H ^ (-(q : ℝ)) ≤ H ^ (1 - (q : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hH hExp
  calc
    1 / H ^ q = H ^ (-(q : ℝ)) := by
      rw [div_eq_mul_inv, one_mul, ← Real.rpow_natCast,
        ← Real.rpow_neg (by positivity)]
    _ ≤ H ^ (1 - (q : ℝ)) := hMono
    _ ≤ T ^ (-(A + 4)) := by
      simpa only [H, q] using
        heathBrownSmoothingHeight_rpow_one_sub_order_le
          (A := A) (η := η) (T := T) hη hT

theorem heathBrownSharpUniformReflectionError_smoothing_le
    {A η T K L D : ℝ} {Q : ℕ}
    (hη : 0 < η) (hηOne : η ≤ 1)
    (hT : 1 ≤ T) (hQ : 0 < Q) (hQT : (Q : ℝ) ≤ 2 * T)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    heathBrownSharpUniformReflectionError K L D
        (heathBrownReflectionDerivativeOrder A η) Q
        (heathBrownSmoothingHeight T η) T ≤
      (16 * K + L * (3 : ℝ) ^
          (heathBrownReflectionDerivativeOrder A η + 2) + 2 * D) *
        T ^ (-A) := by
  let q : ℕ := heathBrownReflectionDerivativeOrder A η
  let H : ℕ := heathBrownSmoothingHeight T η
  have hTPos : 0 < T := by linarith
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hHeight : (H : ℝ) ≤ 2 * T ^ η := by
    simpa only [H] using heathBrownSmoothingHeight_le_two_rpow hT hη.le
  have hEtaPow : T ^ η ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT hηOne
  have hHeightFour : (H : ℝ) + 2 ≤ 4 * T := by
    nlinarith
  have hHeightSq : ((H : ℝ) + 2) ^ 2 ≤ 16 * T ^ 2 := by
    nlinarith [sq_nonneg ((H : ℝ) + 2), sq_nonneg T]
  have hDecayOne : (H : ℝ) ^ (1 - (q : ℝ)) ≤ T ^ (-(A + 4)) := by
    simpa only [H, q] using
      heathBrownSmoothingHeight_rpow_one_sub_order_le
        (A := A) (η := η) (T := T) hη hT
  have hDecayInv : 1 / (H : ℝ) ^ q ≤ T ^ (-(A + 4)) := by
    simpa only [H, q] using
      one_div_heathBrownSmoothingHeight_pow_order_le
        (A := A) (η := η) (T := T) hη hT
  have hTfour : T ^ 2 * T ^ 2 = T ^ (4 : ℕ) := by ring
  have hAbsorb : T ^ (4 : ℕ) * T ^ (-(A + 4)) = T ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hTPos]
    congr 1
    norm_num
  have hFirst :
      K / (Q : ℝ) * T ^ 2 * ((H : ℝ) + 2) ^ 2 *
          (H : ℝ) ^ (1 - (q : ℝ)) ≤
        16 * K * T ^ (-A) := by
    calc
      K / (Q : ℝ) * T ^ 2 * ((H : ℝ) + 2) ^ 2 *
          (H : ℝ) ^ (1 - (q : ℝ)) ≤
        K * T ^ 2 * (16 * T ^ 2) * T ^ (-(A + 4)) := by
          gcongr
          · exact div_le_self hK (by exact_mod_cast hQ)
      _ = 16 * K * T ^ (-A) := by
        rw [show K * T ^ 2 * (16 * T ^ 2) * T ^ (-(A + 4)) =
            16 * K * (T ^ (4 : ℕ) * T ^ (-(A + 4))) by ring,
          hAbsorb]
  have hSecond :
      L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * T ^ 2 / (H : ℝ) ^ q ≤
        L * (3 : ℝ) ^ (q + 2) * T ^ (-A) := by
    have hTtwoFour : T ^ 2 ≤ T ^ (4 : ℕ) := by
      have hTtwoOne : 1 ≤ T ^ 2 := by nlinarith [sq_nonneg T]
      nlinarith [sq_nonneg (T ^ 2 - 1)]
    rw [div_eq_mul_inv]
    calc
      L / (Q : ℝ) * (3 : ℝ) ^ (q + 2) * T ^ 2 *
          ((H : ℝ) ^ q)⁻¹ ≤
        L * (3 : ℝ) ^ (q + 2) * T ^ (4 : ℕ) * T ^ (-(A + 4)) := by
          have hInv : ((H : ℝ) ^ q)⁻¹ ≤ T ^ (-(A + 4)) := by
            simpa only [one_div] using hDecayInv
          gcongr
          exact div_le_self hL (by exact_mod_cast hQ)
      _ = L * (3 : ℝ) ^ (q + 2) * T ^ (-A) := by
        rw [show L * (3 : ℝ) ^ (q + 2) * T ^ (4 : ℕ) * T ^ (-(A + 4)) =
            L * (3 : ℝ) ^ (q + 2) *
              (T ^ (4 : ℕ) * T ^ (-(A + 4))) by ring,
          hAbsorb]
  have hThird :
      (Q : ℝ) * D / (H : ℝ) ^ q ≤ 2 * D * T ^ (-A) := by
    have hToneFour : T ≤ T ^ (4 : ℕ) := by
      calc
        T = T * 1 := by ring
        _ ≤ T * T ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hT) hTPos.le
        _ = T ^ (4 : ℕ) := by ring
    rw [div_eq_mul_inv]
    have hQD : (Q : ℝ) * D ≤ (2 * T) * D :=
      mul_le_mul_of_nonneg_right hQT hD
    have hInvNonneg : 0 ≤ ((H : ℝ) ^ q)⁻¹ := by positivity
    have hLeadNonneg : 0 ≤ (2 * T) * D := by positivity
    calc
      (Q : ℝ) * D * ((H : ℝ) ^ q)⁻¹ ≤
          (2 * T) * D * ((H : ℝ) ^ q)⁻¹ :=
        mul_le_mul_of_nonneg_right hQD hInvNonneg
      _ ≤ (2 * T) * D * T ^ (-(A + 4)) := by
        have hInv : ((H : ℝ) ^ q)⁻¹ ≤ T ^ (-(A + 4)) := by
          simpa only [one_div] using hDecayInv
        exact mul_le_mul_of_nonneg_left hInv hLeadNonneg
      _ ≤ 2 * D * (T ^ (4 : ℕ) * T ^ (-(A + 4))) := by
        have hDecayNonneg : 0 ≤ T ^ (-(A + 4)) := Real.rpow_nonneg hTPos.le _
        calc
          (2 * T) * D * T ^ (-(A + 4)) =
              2 * D * (T * T ^ (-(A + 4))) := by ring
          _ ≤ 2 * D * (T ^ (4 : ℕ) * T ^ (-(A + 4))) := by
            gcongr
      _ = 2 * D * T ^ (-A) := by rw [hAbsorb]
  unfold heathBrownSharpUniformReflectionError
  dsimp only [H, q] at hFirst hSecond hThird ⊢
  linarith

/-! ## Comparable-scale moment bridges -/

/-- The weighted ordered-difference moment on an arbitrary finite frequency
set.  This lets the source proof compare non-dyadic target intervals without
pretending that one sharp polynomial is pointwise monotone in its support. -/
noncomputable def heathBrownWeightedSetMoment
    (s : Finset ℕ) (W : Finset ℝ) : ℝ :=
  heathBrownDifferenceMoment s W
    (fun n => (heathBrownHalfWeight n : ℂ))

theorem heathBrownWeightedSetMoment_eq_kernel_sum
    (s : Finset ℕ) (W : Finset ℝ) :
    heathBrownWeightedSetMoment s W =
      ∑ n ∈ s, ∑ m ∈ s,
        heathBrownHalfWeight n * heathBrownHalfWeight m *
          heathBrownMajorantKernel W n m := by
  unfold heathBrownWeightedSetMoment
  exact heathBrownDifferenceMoment_ofReal_eq_kernel_sum
    s W heathBrownHalfWeight

theorem heathBrownWeightedSetMoment_dyadic
    (N : ℕ) (W : Finset ℝ) :
    heathBrownWeightedSetMoment (dyadicInterval N) W =
      heathBrownWeightedMoment N W := by
  rw [heathBrownWeightedSetMoment_eq_kernel_sum,
    heathBrownWeightedMoment_eq_kernel_sum]

theorem heathBrownWeightedSetMoment_mono
    {s t : Finset ℕ} (W : Finset ℝ) (hst : s ⊆ t) :
    heathBrownWeightedSetMoment s W ≤
      heathBrownWeightedSetMoment t W := by
  rw [heathBrownWeightedSetMoment_eq_kernel_sum,
    heathBrownWeightedSetMoment_eq_kernel_sum]
  let f : ℕ → ℕ → ℝ := fun n m =>
    heathBrownHalfWeight n * heathBrownHalfWeight m *
      heathBrownMajorantKernel W n m
  have hf : ∀ n m, 0 ≤ f n m := by
    intro n m
    dsimp only [f]
    exact mul_nonneg
      (mul_nonneg (heathBrownHalfWeight_nonneg n)
        (heathBrownHalfWeight_nonneg m))
      (heathBrownMajorantKernel_nonneg W n m)
  change (∑ n ∈ s, ∑ m ∈ s, f n m) ≤
    ∑ n ∈ t, ∑ m ∈ t, f n m
  calc
    (∑ n ∈ s, ∑ m ∈ s, f n m) ≤
        ∑ n ∈ s, ∑ m ∈ t, f n m := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum_of_subset_of_nonneg hst
        (fun m hm hms => hf n m)
    _ ≤ ∑ n ∈ t, ∑ m ∈ t, f n m :=
      Finset.sum_le_sum_of_subset_of_nonneg hst
        (fun n hn hns => Finset.sum_nonneg fun m hm => hf n m)

theorem norm_add_sq_le_two (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hTri := norm_add_le a b
  have ha : 0 ≤ ‖a‖ := norm_nonneg _
  have hb : 0 ≤ ‖b‖ := norm_nonneg _
  have hab : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem heathBrownWeightedSetMoment_union_le_two
    {s t : Finset ℕ} (W : Finset ℝ) (hst : Disjoint s t) :
    heathBrownWeightedSetMoment (s ∪ t) W ≤
      2 * (heathBrownWeightedSetMoment s W +
        heathBrownWeightedSetMoment t W) := by
  unfold heathBrownWeightedSetMoment heathBrownDifferenceMoment
  calc
    (∑ x ∈ W, ∑ y ∈ W,
        ‖heathBrownDifferencePolynomial (s ∪ t)
          (fun n => (heathBrownHalfWeight n : ℂ)) x y‖ ^ 2) ≤
      ∑ x ∈ W, ∑ y ∈ W,
        2 *
          (‖heathBrownDifferencePolynomial s
              (fun n => (heathBrownHalfWeight n : ℂ)) x y‖ ^ 2 +
            ‖heathBrownDifferencePolynomial t
              (fun n => (heathBrownHalfWeight n : ℂ)) x y‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        unfold heathBrownDifferencePolynomial
        rw [Finset.sum_union hst]
        exact norm_add_sq_le_two _ _
    _ = 2 *
        ((∑ x ∈ W, ∑ y ∈ W,
            ‖heathBrownDifferencePolynomial s
              (fun n => (heathBrownHalfWeight n : ℂ)) x y‖ ^ 2) +
          ∑ x ∈ W, ∑ y ∈ W,
            ‖heathBrownDifferencePolynomial t
              (fun n => (heathBrownHalfWeight n : ℂ)) x y‖ ^ 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Jutila's comparable-scale bridge: if `M ≤ N ≤ 2M`, then the whole
interval `(N,2N]` lies in the two adjacent `M`-blocks.  Positivity of the
expanded kernel handles restriction to the subinterval, while one exact
two-term norm inequality handles the union. -/
theorem heathBrownWeightedMoment_le_two_adjacent_of_comparable
    {M N : ℕ} (W : Finset ℝ) (hMN : M ≤ N) (hNM : N ≤ 2 * M) :
    heathBrownWeightedMoment N W ≤
      2 * (heathBrownWeightedMoment M W +
        heathBrownWeightedMoment (2 * M) W) := by
  let s := dyadicInterval M
  let t := dyadicInterval (2 * M)
  have hsub : dyadicInterval N ⊆ s ∪ t := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    by_cases hmid : n ≤ 2 * M
    · apply Finset.mem_union_left
      exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hMN hn'.1, hmid⟩
    · apply Finset.mem_union_right
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro n hns hnt
    have hs := Finset.mem_Ioc.mp hns
    have ht := Finset.mem_Ioc.mp hnt
    omega
  calc
    heathBrownWeightedMoment N W =
        heathBrownWeightedSetMoment (dyadicInterval N) W :=
      (heathBrownWeightedSetMoment_dyadic N W).symm
    _ ≤ heathBrownWeightedSetMoment (s ∪ t) W :=
      heathBrownWeightedSetMoment_mono W hsub
    _ ≤ 2 * (heathBrownWeightedSetMoment s W +
        heathBrownWeightedSetMoment t W) :=
      heathBrownWeightedSetMoment_union_le_two W hdisj
    _ = 2 * (heathBrownWeightedMoment M W +
        heathBrownWeightedMoment (2 * M) W) := by
      rw [show s = dyadicInterval M by rfl,
        show t = dyadicInterval (2 * M) by rfl,
        heathBrownWeightedSetMoment_dyadic,
        heathBrownWeightedSetMoment_dyadic]

/-- The exact `k = c = 2` specialization of Montgomery--Vaughan Lemma
29.9.  After cancelling the physical factor `M^2`, the powered moment is
controlled by the two source terminal scales `4 M^2` and `8 M^2`.
All coefficient and transfer losses remain visible in `E`. -/
theorem exists_heathBrownWeightedMoment_sq_le_four_mul_sq
    (M : ℕ) (W : Finset ℝ) (hM : 0 < M) (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ, 0 < E ∧
      heathBrownWeightedMoment M W ^ 2 ≤
        E * ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          ((16 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          (W.card : ℝ) ^ 2 *
          (heathBrownWeightedMoment (4 * M ^ 2) W +
            heathBrownWeightedMoment (8 * M ^ 2) W) := by
  obtain ⟨C, D, hC, hD, hRec⟩ :=
    exists_heathBrownWeightedMoment_powering_recurrence
      M 2 2 W hM (by omega) (by omega) η hη
  refine ⟨128 * C ^ 2 * D ^ 2, by positivity, ?_⟩
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := sq_pos_of_pos hMReal
  have hRec' :
      (M : ℝ) ^ 2 * heathBrownWeightedMoment M W ^ 2 ≤
        (M : ℝ) ^ 2 *
          (128 * C ^ 2 * D ^ 2 *
            ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
            ((16 * (M : ℝ) ^ 2) ^ η) ^ 2 *
            (W.card : ℝ) ^ 2 *
            (heathBrownWeightedMoment (4 * M ^ 2) W +
              heathBrownWeightedMoment (8 * M ^ 2) W)) := by
    norm_num [heathBrownPoweredTargetScale, Nat.cast_pow,
      Nat.cast_mul] at hRec ⊢
    convert hRec using 1
    all_goals ring_nf
  exact le_of_mul_le_mul_left hRec' hM2

/-- The two auxiliary localization scales and the central scale are all
uniformly comparable with the original dyadic length. -/
theorem heathBrown_source_scales_comparable
    {N Q : ℕ} (hN : 30 ≤ N)
    (hQ : Q = gmSourceLeftScale N ∨ Q = N ∨ Q = gmSourceRightScale N) :
    4 ≤ Q ∧ N ≤ 2 * Q ∧ Q ≤ 2 * N := by
  rcases hQ with rfl | rfl | rfl
  · unfold gmSourceLeftScale
    omega
  · omega
  · unfold gmSourceRightScale
    omega

/-- Real logarithmic majorant for the floor logarithm used to count
displacement bins. -/
theorem natCast_log_two_le_log (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpowNat : 2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowPos : (0 : ℝ) < (2 ^ Nat.log 2 n : ℕ) := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hpowPos) (Set.mem_Ioi.mpr hnPos)
    (by exact_mod_cast hpowNat)
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlogTwo]
  simpa using hlog

theorem heathBrown_displacement_bin_count_le_log
    {T : ℝ} (hT : 2 ≤ T) :
    ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) ≤
      1 + Real.log T / Real.log 2 := by
  have hFloorOne : 1 ≤ Nat.floor T := by
    rw [Nat.le_floor_iff (by linarith : 0 ≤ T)]
    norm_num
    linarith
  have hFloorPos : (0 : ℝ) < Nat.floor T := by exact_mod_cast hFloorOne
  have hFloorLe : (Nat.floor T : ℝ) ≤ T :=
    Nat.floor_le (by linarith)
  have hLogFloor := natCast_log_two_le_log (Nat.floor T) hFloorOne
  have hLogMono : Real.log (Nat.floor T : ℝ) ≤ Real.log T :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hFloorPos) (Set.mem_Ioi.mpr (by linarith)) hFloorLe
  push_cast
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.log 2 (Nat.floor T) : ℝ) + 1 ≤
        Real.log (Nat.floor T : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log T / Real.log 2 + 1 := by gcongr
    _ = 1 + Real.log T / Real.log 2 := by ring

theorem heathBrown_natCast_clog_two_le_one_add_log
    (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 1 + Real.log n / Real.log 2 := by
  by_cases hnOne : n = 1
  · subst n
    simp
  · have hnTwo : 1 < n := by omega
    have hkPos : 0 < Nat.clog 2 n :=
      Nat.clog_pos Nat.one_lt_two hnTwo
    have hpowNat : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two hnTwo
    have hpow : (0 : ℝ) < (2 ^ (Nat.clog 2 n - 1) : ℕ) := by positivity
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hnTwo)
    have hlog := Real.strictMonoOn_log (Set.mem_Ioi.mpr hpow)
      (Set.mem_Ioi.mpr hnPos) (by exact_mod_cast hpowNat)
    rw [Nat.cast_pow, Real.log_pow] at hlog
    have hcastSub : ((Nat.clog 2 n - 1 : ℕ) : ℝ) =
        (Nat.clog 2 n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num [Real.rpow_natCast]
    rw [hcastSub] at hlog
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : (Nat.clog 2 n : ℝ) - 1 ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hlogTwo]
      simpa using hlog.le
    linarith

/-- The common dyadic exponent is logarithmic in its physical terminal
scale. -/
theorem heathBrown_corrected_common_exponent_le_log
    (Q H : ℕ) (T : ℝ) :
    (heathBrownCorrectedCommonExponent Q H T : ℝ) ≤
      2 + Real.log (heathBrownCorrectedCommonScale Q H T : ℝ) /
        Real.log 2 := by
  have hCommonPos : 0 < heathBrownCommonReflectionLength Q H T := by
    unfold heathBrownCommonReflectionLength
    omega
  have hClog := heathBrown_natCast_clog_two_le_one_add_log
    (heathBrownCommonReflectionLength Q H T) hCommonPos
  have hCommonLe := heathBrownCommonReflectionLength_le_target Q H T
  have hCommonRealPos : (0 : ℝ) < heathBrownCommonReflectionLength Q H T := by
    exact_mod_cast hCommonPos
  have hTargetPos : (0 : ℝ) < heathBrownReflectionTargetScale Q H T := by
    exact_mod_cast (pow_pos (by omega : 0 < (2 : ℕ)) _)
  have hLogMono :
      Real.log (heathBrownCommonReflectionLength Q H T : ℝ) ≤
        Real.log (heathBrownReflectionTargetScale Q H T : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hCommonRealPos) (Set.mem_Ioi.mpr hTargetPos)
      (by exact_mod_cast hCommonLe)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTargetLeCorrected :
      heathBrownReflectionTargetScale Q H T ≤
        heathBrownCorrectedCommonScale Q H T := by
    rw [heathBrownCorrectedCommonScale_eq_two_mul_target]
    omega
  have hCorrectedPos : (0 : ℝ) < heathBrownCorrectedCommonScale Q H T := by
    exact_mod_cast (lt_of_lt_of_le
      (show 0 < heathBrownReflectionTargetScale Q H T by
        unfold heathBrownReflectionTargetScale
        exact pow_pos (by omega) _)
      hTargetLeCorrected)
  have hLogTargetCorrected :
      Real.log (heathBrownReflectionTargetScale Q H T : ℝ) ≤
        Real.log (heathBrownCorrectedCommonScale Q H T : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hTargetPos) (Set.mem_Ioi.mpr hCorrectedPos)
      (by exact_mod_cast hTargetLeCorrected)
  unfold heathBrownCorrectedCommonExponent
  push_cast
  calc
    (Nat.clog 2 (heathBrownCommonReflectionLength Q H T) : ℝ) + 1 ≤
        2 + Real.log (heathBrownCommonReflectionLength Q H T : ℝ) /
          Real.log 2 := by linarith
    _ ≤ 2 + Real.log (heathBrownReflectionTargetScale Q H T : ℝ) /
          Real.log 2 := by gcongr
    _ ≤ 2 + Real.log (heathBrownCorrectedCommonScale Q H T : ℝ) /
          Real.log 2 := by gcongr

/-- One positive quantity dominating every dyadic, smoothing and Mellin
factor in a single reflected trace. -/
noncomputable def heathBrownLocalRecurrenceProfile
    (η T : ℝ) (Q H : ℕ) : ℝ :=
  1 + (Nat.log 2 (Nat.floor T) + 1 : ℕ) + H +
    heathBrownCorrectedCommonExponent Q H T +
    (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η

theorem heathBrownLocalRecurrenceProfile_components
    {η T : ℝ} {Q H : ℕ} :
    1 ≤ heathBrownLocalRecurrenceProfile η T Q H ∧
    ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) ≤
      heathBrownLocalRecurrenceProfile η T Q H ∧
    (H : ℝ) ≤ heathBrownLocalRecurrenceProfile η T Q H ∧
    (heathBrownCorrectedCommonExponent Q H T : ℝ) ≤
      heathBrownLocalRecurrenceProfile η T Q H ∧
    (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η ≤
      heathBrownLocalRecurrenceProfile η T Q H := by
  unfold heathBrownLocalRecurrenceProfile
  have hp : 0 ≤
      (4 * (heathBrownCorrectedCommonScale Q H T : ℕ) : ℝ) ^ η :=
    Real.rpow_nonneg (by positivity) _
  have hℓ : 0 ≤ ((Nat.log 2 (Nat.floor T) + 1 : ℕ) : ℝ) := by positivity
  have hH : 0 ≤ (H : ℝ) := by positivity
  have hc : 0 ≤ (heathBrownCorrectedCommonExponent Q H T : ℝ) := by positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Explicit source-scale majorant for the local trace profile.  It exposes
only logarithms and the genuine smoothing powers, so a later epsilon-budget
lemma can absorb the entire tenth power without losing the Heath--Brown
exponent. -/
theorem heathBrownLocalRecurrenceProfile_le_explicit
    {η T : ℝ} {Q H : ℕ} (hη : 0 ≤ η) (hηOne : η ≤ 1)
    (hT : 2 ≤ T) (hQ : 0 < Q)
    (hHeight : H = heathBrownSmoothingHeight T η) :
    heathBrownLocalRecurrenceProfile η T Q H ≤
      4 + Real.log T / Real.log 2 + 2 * T ^ η +
        (Real.log 12 + 2 * Real.log T) / Real.log 2 +
        (48 * T ^ 2) ^ η := by
  let P := heathBrownCorrectedCommonScale Q H T
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEll := heathBrown_displacement_bin_count_le_log hT
  have hHeightBound : (H : ℝ) ≤ 2 * T ^ η := by
    rw [hHeight]
    exact heathBrownSmoothingHeight_le_two_rpow hTOne hη
  have hPBound : (P : ℝ) ≤ 12 * T ^ 2 := by
    dsimp only [P]
    exact heathBrownCorrectedCommonScale_le_twelve_mul_sq
      hη hηOne hT hQ hHeight
  have hPPosNat : 0 < P := by
    dsimp only [P]
    rw [heathBrownCorrectedCommonScale_eq_two_mul_target]
    exact Nat.mul_pos (by omega) (by
      unfold heathBrownReflectionTargetScale
      exact pow_pos (by omega) _)
  have hPPos : (0 : ℝ) < P := by exact_mod_cast hPPosNat
  have hUpperPos : 0 < 12 * T ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hTPos)
  have hLogP : Real.log (P : ℝ) ≤ Real.log 12 + 2 * Real.log T := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hPPos) (Set.mem_Ioi.mpr hUpperPos) hPBound
    calc
      Real.log (P : ℝ) ≤ Real.log (12 * T ^ 2) := hmono
      _ = Real.log 12 + 2 * Real.log T := by
        rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0)
          (pow_ne_zero 2 hTPos.ne'), Real.log_pow]
        norm_num
  have hExponent := heathBrown_corrected_common_exponent_le_log Q H T
  have hExponentBound :
      (heathBrownCorrectedCommonExponent Q H T : ℝ) ≤
        2 + (Real.log 12 + 2 * Real.log T) / Real.log 2 := by
    calc
      _ ≤ 2 + Real.log (P : ℝ) / Real.log 2 := by simpa only [P] using hExponent
      _ ≤ 2 + (Real.log 12 + 2 * Real.log T) / Real.log 2 := by gcongr
  have hFourPReal : (4 * P : ℝ) ≤ 48 * T ^ 2 := by
    linarith
  have hPower : (4 * P : ℝ) ^ η ≤ (48 * T ^ 2) ^ η :=
    Real.rpow_le_rpow (by positivity) hFourPReal hη
  unfold heathBrownLocalRecurrenceProfile
  dsimp only [P] at hPower
  nlinarith

/-- A single logarithm is eventually smaller than any prescribed positive
power.  This local form avoids an import cycle with the classical endpoint
assembly, where the same asymptotic fact is used independently. -/
theorem heathBrown_eventually_log_le_rpow
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, Real.log T ≤ T ^ η := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (1 : ℝ) hη
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with T hBound hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTNonneg : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _),
    Real.rpow_one] at hBound
  exact hBound

/-- All dyadic, smoothing and Mellin losses in the exact source trace cost
at most `T^(20η)` after the tenth-power envelope.  The constant and starting
height depend only on `η`, never on the source scale `Q` or the zero set. -/
theorem eventually_heathBrownLocalRecurrenceProfile_pow_ten_le_rpow
    (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q H : ℕ), T₀ ≤ T → 0 < Q →
        H = heathBrownSmoothingHeight T η →
        heathBrownLocalRecurrenceProfile η T Q H ^ 10 ≤
          C * T ^ (20 * η) := by
  have hEventually := heathBrown_eventually_log_le_rpow η hη
  rw [eventually_atTop] at hEventually
  obtain ⟨Tlog, hTlog⟩ := hEventually
  let C₀ : ℝ := 6 + 48 ^ η +
    (Real.log 12 + 3) / Real.log 2
  let C : ℝ := C₀ ^ (10 : ℕ)
  let T₀ : ℝ := max 2 Tlog
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogTwelve : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀]
    positivity
  refine ⟨C, pow_pos hC₀ 10, T₀, le_max_left _ _, ?_⟩
  intro T Q H hT hQ hHeight
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTLog : Tlog ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hLogBound : Real.log T ≤ T ^ η := hTlog T hTLog
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
  have hPowOne : 1 ≤ T ^ η := Real.one_le_rpow hTOne hη.le
  have hPowMono : T ^ η ≤ T ^ (2 * η) := by
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hOneToTwo : 1 ≤ T ^ (2 * η) := hPowOne.trans hPowMono
  have hLogToTwo : Real.log T ≤ T ^ (2 * η) :=
    hLogBound.trans hPowMono
  have hLastIdentity : (48 * T ^ 2) ^ η = 48 ^ η * T ^ (2 * η) := by
    calc
      (48 * T ^ 2) ^ η = 48 ^ η * (T ^ 2) ^ η :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 48) (sq_nonneg T)
      _ = 48 ^ η * T ^ (2 * η) := by
        congr 1
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hTPos.le]
        norm_num
  have hProfile := heathBrownLocalRecurrenceProfile_le_explicit
    hη.le hηOne hTTwo hQ hHeight
  have hProfileBound :
      heathBrownLocalRecurrenceProfile η T Q H ≤
        C₀ * T ^ (2 * η) := by
    have hFour : 4 ≤ 4 * T ^ (2 * η) := by nlinarith
    have hLogTerm :
        Real.log T / Real.log 2 ≤ T ^ (2 * η) / Real.log 2 :=
      div_le_div_of_nonneg_right hLogToTwo hLogTwo.le
    have hTwoPower : 2 * T ^ η ≤ 2 * T ^ (2 * η) := by gcongr
    have hLogTwelveScale :
        Real.log 12 ≤ Real.log 12 * T ^ (2 * η) := by
      calc
        Real.log 12 = Real.log 12 * 1 := by ring
        _ ≤ Real.log 12 * T ^ (2 * η) := by gcongr
    have hFractionInside :
        Real.log 12 + 2 * Real.log T ≤
          Real.log 12 * T ^ (2 * η) + 2 * T ^ (2 * η) := by
      linarith
    have hFraction :
        (Real.log 12 + 2 * Real.log T) / Real.log 2 ≤
          (Real.log 12 * T ^ (2 * η) + 2 * T ^ (2 * η)) /
            Real.log 2 :=
      div_le_div_of_nonneg_right hFractionInside hLogTwo.le
    calc
      heathBrownLocalRecurrenceProfile η T Q H ≤
          4 + Real.log T / Real.log 2 + 2 * T ^ η +
            (Real.log 12 + 2 * Real.log T) / Real.log 2 +
            (48 * T ^ 2) ^ η := hProfile
      _ ≤ 4 * T ^ (2 * η) + T ^ (2 * η) / Real.log 2 +
            2 * T ^ (2 * η) +
            (Real.log 12 * T ^ (2 * η) +
              2 * T ^ (2 * η)) / Real.log 2 +
            48 ^ η * T ^ (2 * η) := by
        rw [hLastIdentity]
        gcongr
      _ = C₀ * T ^ (2 * η) := by
        dsimp only [C₀]
        field_simp [hLogTwo.ne']
        ring
  have hProfileNonneg : 0 ≤ heathBrownLocalRecurrenceProfile η T Q H :=
    (heathBrownLocalRecurrenceProfile_components (η := η) (T := T)
      (Q := Q) (H := H)).1.trans' zero_le_one
  have hPowBound := pow_le_pow_left₀ hProfileNonneg hProfileBound 10
  calc
    heathBrownLocalRecurrenceProfile η T Q H ^ 10 ≤
        (C₀ * T ^ (2 * η)) ^ 10 := hPowBound
    _ = C * T ^ (20 * η) := by
      dsimp only [C]
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hTPos.le]
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- A single source-sharp trace, with all analytic constants and all finite
losses dominated by the tenth power of the local recurrence profile. -/
theorem heathBrownSourceSharpTraceRecurrenceBound_le_profile
    {η T Cnear C Ctr K L D : ℝ} {N Q H : ℕ} {W : Finset ℝ}
    (hη : 0 < η) (hηOne : η ≤ 1) (hT : 2 ≤ T)
    (hN : 0 < N) (hQ : 0 < Q) (hQUpper : Q ≤ 2 * N)
    (hNT : (N : ℝ) ≤ T)
    (hH : 0 < H) (hHeight : H = heathBrownSmoothingHeight T η)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    heathBrownSourceSharpTraceRecurrenceBound Cnear C Ctr K L D η
        (heathBrownReflectionDerivativeOrder 2 η) T W Q H ≤
      (100000 * (1 + Cnear ^ 2 + C ^ 2 + C ^ 2 * Ctr ^ 4 +
          (16 * K + L * (3 : ℝ) ^
            (heathBrownReflectionDerivativeOrder 2 η + 2) + 2 * D) ^ 2)) *
        heathBrownLocalRecurrenceProfile η T Q H ^ 10 * (N : ℝ) *
          ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
            heathBrownWeightedMoment
              (heathBrownCorrectedCommonScale Q H T) W +
            heathBrownWeightedMoment
              (2 * heathBrownCorrectedCommonScale Q H T) W + 1) := by
  let R : ℝ := W.card
  let ℓ : ℝ := (Nat.log 2 (Nat.floor T) + 1 : ℕ)
  let c : ℝ := heathBrownCorrectedCommonExponent Q H T
  let P : ℕ := heathBrownCorrectedCommonScale Q H T
  let B : ℝ := heathBrownLocalRecurrenceProfile η T Q H
  let E : ℝ := 16 * K + L * (3 : ℝ) ^
    (heathBrownReflectionDerivativeOrder 2 η + 2) + 2 * D
  let X : ℝ := R * N + R ^ 2 + heathBrownWeightedMoment P W +
    heathBrownWeightedMoment (2 * P) W + 1
  have hcomp := heathBrownLocalRecurrenceProfile_components
    (η := η) (T := T) (Q := Q) (H := H)
  have hBOne : 1 ≤ B := by simpa only [B] using hcomp.1
  have hℓB : ℓ ≤ B := by simpa only [ℓ, B] using hcomp.2.1
  have hHB : (H : ℝ) ≤ B := by simpa only [B] using hcomp.2.2.1
  have hcB : c ≤ B := by simpa only [c, B] using hcomp.2.2.2.1
  have hpB : (4 * (P : ℕ) : ℝ) ^ η ≤ B := by
    simpa only [P, B] using hcomp.2.2.2.2
  have hB0 : 0 ≤ B := hBOne.trans' zero_le_one
  have hℓ0 : 0 ≤ ℓ := by dsimp only [ℓ]; positivity
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hp0 : 0 ≤ (4 * (P : ℕ) : ℝ) ^ η :=
    Real.rpow_nonneg (by positivity) _
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hS0 : 0 ≤ heathBrownWeightedMoment P W := by
    unfold heathBrownWeightedMoment
    positivity
  have hS20 : 0 ≤ heathBrownWeightedMoment (2 * P) W := by
    unfold heathBrownWeightedMoment
    positivity
  have hRN0 : 0 ≤ R * (N : ℝ) := mul_nonneg hR0 (by positivity)
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  have hTail0 : 0 ≤ heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W := add_nonneg hS0 hS20
  have hX0 : 0 ≤ X := by
    change 0 ≤ R * (N : ℝ) + R ^ 2 +
      heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W + 1
    linarith only [hRN0, hR20, hS0, hS20]
  have hRNX : R * (N : ℝ) ≤ X := by
    change R * (N : ℝ) ≤ R * (N : ℝ) + R ^ 2 +
      heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W + 1
    linarith only [hR20, hS0, hS20]
  have hR2X : R ^ 2 ≤ X := by
    change R ^ 2 ≤ R * (N : ℝ) + R ^ 2 +
      heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W + 1
    linarith only [hRN0, hS0, hS20]
  have hSX : heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W ≤ X := by
    change heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W ≤
      R * (N : ℝ) + R ^ 2 + heathBrownWeightedMoment P W +
      heathBrownWeightedMoment (2 * P) W + 1
    linarith only [hRN0, hR20]
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQN : (Q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hQUpper
  have hQsq : (Q : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
  have hPowMono : ∀ k : ℕ, k ≤ 10 → B ^ k ≤ B ^ 10 := by
    intro k hk
    exact pow_le_pow_right₀ hBOne (by omega)
  have hB10One : 1 ≤ B ^ 10 := one_le_pow₀ hBOne
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hQT : (Q : ℝ) ≤ 2 * T := by
    exact hQN.trans (by gcongr)
  have hErr := heathBrownSharpUniformReflectionError_smoothing_le
    (A := (2 : ℝ)) (η := η) (T := T) (K := K) (L := L) (D := D)
    (Q := Q) hη hηOne (by linarith) hQ hQT hK hL hD
  rw [← hHeight] at hErr
  have hErr0 : 0 ≤ heathBrownSharpUniformReflectionError K L D
      (heathBrownReflectionDerivativeOrder 2 η) Q H T := by
    unfold heathBrownSharpUniformReflectionError
    positivity
  have hTPos : 0 < T := by linarith
  have hTDecay : T * (T ^ (-(2 : ℝ))) ^ 2 ≤ 1 := by
    have heq : T * (T ^ (-(2 : ℝ))) ^ 2 = (T ^ 3)⁻¹ := by
      rw [Real.rpow_neg hTPos.le, Real.rpow_two]
      field_simp [hTPos.ne']
    rw [heq]
    exact (inv_le_one₀ (pow_pos hTPos 3)).2
      (one_le_pow₀ (by linarith : 1 ≤ T))
  have hErrSq : T *
      (heathBrownSharpUniformReflectionError K L D
        (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2 ≤ E ^ 2 := by
    calc
      T * (heathBrownSharpUniformReflectionError K L D
          (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2 ≤
          T * (E * T ^ (-(2 : ℝ))) ^ 2 := by gcongr
      _ = E ^ 2 * (T * (T ^ (-(2 : ℝ))) ^ 2) := by ring
      _ ≤ E ^ 2 * 1 := by gcongr
      _ = E ^ 2 := by ring
  have hPsucc : 2 ^ (heathBrownCorrectedCommonExponent Q H T + 1) = 2 * P := by
    dsimp only [P, heathBrownCorrectedCommonScale]
    rw [pow_succ]
    ring
  have hTerm1 : R * (Q : ℝ) ^ 2 ≤ 4 * B ^ 10 * (N : ℝ) * X := by
    calc
      R * (Q : ℝ) ^ 2 ≤ R * (4 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hQsq hR0
      _ = 4 * (N : ℝ) * (R * (N : ℝ)) := by ring
      _ ≤ 4 * (N : ℝ) * X :=
        mul_le_mul_of_nonneg_left hRNX (by positivity)
      _ ≤ 4 * B ^ 10 * (N : ℝ) * X := by
        have hcoef : 4 ≤ 4 * B ^ 10 := by nlinarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hNReal.le) hX0
  have hTerm2 : 8 * R * Cnear ^ 2 * (Q : ℝ) ^ 2 ≤
      32 * Cnear ^ 2 * B ^ 10 * (N : ℝ) * X := by
    calc
      8 * R * Cnear ^ 2 * (Q : ℝ) ^ 2 ≤
          8 * R * Cnear ^ 2 * (4 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hQsq (by positivity)
      _ = 32 * Cnear ^ 2 * (N : ℝ) * (R * (N : ℝ)) := by ring
      _ ≤ 32 * Cnear ^ 2 * (N : ℝ) * X :=
        mul_le_mul_of_nonneg_left hRNX (by positivity)
      _ ≤ 32 * Cnear ^ 2 * B ^ 10 * (N : ℝ) * X := by
        have hcoef : 32 * Cnear ^ 2 ≤ 32 * Cnear ^ 2 * B ^ 10 := by
          nlinarith [sq_nonneg Cnear]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hNReal.le) hX0
  have hℓH : ℓ * (H : ℝ) ≤ B ^ 2 := by
    calc
      ℓ * (H : ℝ) ≤ B * B :=
        mul_le_mul hℓB hHB hH0 hB0
      _ = B ^ 2 := by ring
  have hTerm3 : ℓ * (8 * R * H * (Q : ℝ) ^ 2) ≤
      32 * B ^ 10 * (N : ℝ) * X := by
    calc
      ℓ * (8 * R * H * (Q : ℝ) ^ 2) =
          8 * R * (ℓ * (H : ℝ)) * (Q : ℝ) ^ 2 := by ring
      _ ≤ 8 * R * B ^ 2 * (4 * (N : ℝ) ^ 2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hℓH (by positivity)) hQsq
          (by positivity) (by positivity)
      _ = 32 * B ^ 2 * (N : ℝ) * (R * (N : ℝ)) := by ring
      _ ≤ 32 * B ^ 2 * (N : ℝ) * X :=
        mul_le_mul_of_nonneg_left hRNX (by positivity)
      _ ≤ 32 * B ^ 10 * (N : ℝ) * X := by
        have hcoef : 32 * B ^ 2 ≤ 32 * B ^ 10 := by
          exact mul_le_mul_of_nonneg_left (hPowMono 2 (by omega)) (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hNReal.le) hX0
  have hℓH2c : ℓ * (H : ℝ) ^ 2 * c ≤ B ^ 4 := by
    calc
      ℓ * (H : ℝ) ^ 2 * c = ℓ * (H : ℝ) * (H : ℝ) * c := by ring
      _ ≤ B * B * B * B := by gcongr
      _ = B ^ 4 := by ring
  have hTerm4 : ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * R ^ 2) ≤
      64 * C ^ 2 * B ^ 10 * (N : ℝ) * X := by
    calc
      ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * R ^ 2) =
          32 * C ^ 2 * (ℓ * (H : ℝ) ^ 2 * c) * (Q : ℝ) * R ^ 2 := by ring
      _ ≤ 32 * C ^ 2 * B ^ 4 * (2 * (N : ℝ)) * R ^ 2 := by
        have hCoeff :
            32 * C ^ 2 * (ℓ * (H : ℝ) ^ 2 * c) ≤
              32 * C ^ 2 * B ^ 4 :=
          mul_le_mul_of_nonneg_left hℓH2c (by positivity)
        have hCoeffQ :
            (32 * C ^ 2 * (ℓ * (H : ℝ) ^ 2 * c)) * (Q : ℝ) ≤
              (32 * C ^ 2 * B ^ 4) * (2 * (N : ℝ)) :=
          mul_le_mul hCoeff hQN hQReal.le (by positivity)
        exact mul_le_mul hCoeffQ le_rfl hR20 (by positivity)
      _ = 64 * C ^ 2 * B ^ 4 * (N : ℝ) * R ^ 2 := by ring
      _ ≤ 64 * C ^ 2 * B ^ 4 * (N : ℝ) * X :=
        mul_le_mul_of_nonneg_left hR2X (by positivity)
      _ ≤ 64 * C ^ 2 * B ^ 10 * (N : ℝ) * X := by
        have hcoef : 64 * C ^ 2 * B ^ 4 ≤ 64 * C ^ 2 * B ^ 10 := by
          exact mul_le_mul_of_nonneg_left (hPowMono 4 (by omega)) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hNReal.le) hX0
  have hHplus : (H : ℝ) + 2 ≤ 3 * B := by nlinarith
  have hProfileProduct :
      ℓ * (H : ℝ) ^ 2 * ((H : ℝ) + 2) * c ^ 2 *
          ((4 * (P : ℕ) : ℝ) ^ η) ^ 4 ≤ 3 * B ^ 10 := by
    calc
      _ = ℓ * (H : ℝ) * (H : ℝ) * ((H : ℝ) + 2) * c * c *
          ((4 * (P : ℕ) : ℝ) ^ η) *
          ((4 * (P : ℕ) : ℝ) ^ η) *
          ((4 * (P : ℕ) : ℝ) ^ η) *
          ((4 * (P : ℕ) : ℝ) ^ η) := by ring
      _ ≤ B * B * B * (3 * B) * B * B * B * B * B * B := by gcongr
      _ = 3 * B ^ 10 := by ring
  have hTerm5 : ℓ * (2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
        (Ctr * (4 * (P : ℕ) : ℝ) ^ η) ^ 4 *
        (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W)) ≤
      12288 * C ^ 2 * Ctr ^ 4 * B ^ 10 * (N : ℝ) * X := by
    calc
      _ = 2048 * C ^ 2 * Ctr ^ 4 *
          (ℓ * (H : ℝ) ^ 2 * ((H : ℝ) + 2) * c ^ 2 *
            ((4 * (P : ℕ) : ℝ) ^ η) ^ 4) * (Q : ℝ) *
          (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W) := by ring
      _ ≤ 2048 * C ^ 2 * Ctr ^ 4 * (3 * B ^ 10) *
          (2 * (N : ℝ)) *
          (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W) := by
            have hCoeff :
                2048 * C ^ 2 * Ctr ^ 4 *
                    (ℓ * (H : ℝ) ^ 2 * ((H : ℝ) + 2) * c ^ 2 *
                      ((4 * (P : ℕ) : ℝ) ^ η) ^ 4) ≤
                  2048 * C ^ 2 * Ctr ^ 4 * (3 * B ^ 10) :=
              mul_le_mul_of_nonneg_left hProfileProduct (by positivity)
            have hCoeffQ :
                (2048 * C ^ 2 * Ctr ^ 4 *
                    (ℓ * (H : ℝ) ^ 2 * ((H : ℝ) + 2) * c ^ 2 *
                      ((4 * (P : ℕ) : ℝ) ^ η) ^ 4)) * (Q : ℝ) ≤
                  (2048 * C ^ 2 * Ctr ^ 4 * (3 * B ^ 10)) *
                    (2 * (N : ℝ)) :=
              mul_le_mul hCoeff hQN hQReal.le (by positivity)
            exact mul_le_mul hCoeffQ le_rfl hTail0 (by positivity)
      _ = 12288 * C ^ 2 * Ctr ^ 4 * B ^ 10 * (N : ℝ) *
          (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W) := by
            ring
      _ ≤ 12288 * C ^ 2 * Ctr ^ 4 * B ^ 10 * (N : ℝ) * X :=
        mul_le_mul_of_nonneg_left hSX (by positivity)
  have hTerm6 : ℓ * (8 * R * T *
      (heathBrownSharpUniformReflectionError K L D
        (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2) ≤
      8 * E ^ 2 * B ^ 10 * (N : ℝ) * X := by
    calc
      _ = 8 * ℓ * R * (T *
          (heathBrownSharpUniformReflectionError K L D
            (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2) := by ring
      _ ≤ 8 * B * R * E ^ 2 := by gcongr
      _ ≤ 8 * E ^ 2 * B ^ 10 * (N : ℝ) * X := by
        have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        have hRle : R ≤ X := by
          calc R = R * 1 := by ring
          _ ≤ R * (N : ℝ) := mul_le_mul_of_nonneg_left hNOne hR0
          _ ≤ X := hRNX
        have hXleNX : X ≤ (N : ℝ) * X := by
          calc X = 1 * X := by ring
          _ ≤ (N : ℝ) * X := mul_le_mul_of_nonneg_right hNOne hX0
        have hRleNX : R ≤ (N : ℝ) * X := hRle.trans hXleNX
        have hBpow : B ≤ B ^ 10 := by
          simpa only [pow_one] using hPowMono 1 (by omega)
        have hCore : B * R ≤ B ^ 10 * ((N : ℝ) * X) :=
          mul_le_mul hBpow hRleNX hR0 (by positivity)
        calc
          8 * B * R * E ^ 2 = 8 * E ^ 2 * (B * R) := by ring
          _ ≤ 8 * E ^ 2 * (B ^ 10 * ((N : ℝ) * X)) :=
            mul_le_mul_of_nonneg_left hCore (by positivity)
          _ = 8 * E ^ 2 * B ^ 10 * (N : ℝ) * X := by ring
  rw [heathBrownSourceSharpTraceRecurrenceBound]
  rw [hPsucc]
  let Y : ℝ := B ^ 10 * (N : ℝ) * X
  have hY0 : 0 ≤ Y := by
    dsimp only [Y]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hB0 10) hNReal.le) hX0
  have hSum :
      R * (Q : ℝ) ^ 2 + 8 * R * Cnear ^ 2 * (Q : ℝ) ^ 2 +
          ℓ * (8 * R * H * (Q : ℝ) ^ 2) +
          ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * R ^ 2 +
            2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
              (Ctr * (4 * (P : ℕ) : ℝ) ^ η) ^ 4 *
              (heathBrownWeightedMoment P W +
                heathBrownWeightedMoment (2 * P) W)) +
          ℓ * (8 * R * T *
            (heathBrownSharpUniformReflectionError K L D
              (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2) ≤
        (4 + 32 * Cnear ^ 2 + 32 + 64 * C ^ 2 +
          12288 * C ^ 2 * Ctr ^ 4 + 8 * E ^ 2) * Y := by
    have ht1 : R * (Q : ℝ) ^ 2 ≤ 4 * Y := by
      calc
        _ ≤ 4 * B ^ 10 * (N : ℝ) * X := hTerm1
        _ = 4 * Y := by dsimp only [Y]; ring
    have ht2 : 8 * R * Cnear ^ 2 * (Q : ℝ) ^ 2 ≤
        (32 * Cnear ^ 2) * Y := by
      calc
        _ ≤ 32 * Cnear ^ 2 * B ^ 10 * (N : ℝ) * X := hTerm2
        _ = (32 * Cnear ^ 2) * Y := by dsimp only [Y]; ring
    have ht3 : ℓ * (8 * R * H * (Q : ℝ) ^ 2) ≤ 32 * Y := by
      calc
        _ ≤ 32 * B ^ 10 * (N : ℝ) * X := hTerm3
        _ = 32 * Y := by dsimp only [Y]; ring
    have ht4 : ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * R ^ 2) ≤
        (64 * C ^ 2) * Y := by
      calc
        _ ≤ 64 * C ^ 2 * B ^ 10 * (N : ℝ) * X := hTerm4
        _ = (64 * C ^ 2) * Y := by dsimp only [Y]; ring
    have ht5 : ℓ * (2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
          (Ctr * (4 * (P : ℕ) : ℝ) ^ η) ^ 4 *
          (heathBrownWeightedMoment P W +
            heathBrownWeightedMoment (2 * P) W)) ≤
        (12288 * C ^ 2 * Ctr ^ 4) * Y := by
      calc
        _ ≤ 12288 * C ^ 2 * Ctr ^ 4 * B ^ 10 * (N : ℝ) * X := hTerm5
        _ = (12288 * C ^ 2 * Ctr ^ 4) * Y := by dsimp only [Y]; ring
    have ht6 : ℓ * (8 * R * T *
        (heathBrownSharpUniformReflectionError K L D
          (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2) ≤
        (8 * E ^ 2) * Y := by
      calc
        _ ≤ 8 * E ^ 2 * B ^ 10 * (N : ℝ) * X := hTerm6
        _ = (8 * E ^ 2) * Y := by dsimp only [Y]; ring
    calc
      _ = R * (Q : ℝ) ^ 2 +
          8 * R * Cnear ^ 2 * (Q : ℝ) ^ 2 +
          ℓ * (8 * R * H * (Q : ℝ) ^ 2) +
          ℓ * (32 * (Q : ℝ) * C ^ 2 * H ^ 2 * c * R ^ 2) +
          ℓ * (2048 * (Q : ℝ) * C ^ 2 * H ^ 2 * (H + 2) * c ^ 2 *
            (Ctr * (4 * (P : ℕ) : ℝ) ^ η) ^ 4 *
            (heathBrownWeightedMoment P W +
              heathBrownWeightedMoment (2 * P) W)) +
          ℓ * (8 * R * T *
            (heathBrownSharpUniformReflectionError K L D
              (heathBrownReflectionDerivativeOrder 2 η) Q H T) ^ 2) := by ring
      _ ≤ 4 * Y + (32 * Cnear ^ 2) * Y + 32 * Y +
          (64 * C ^ 2) * Y + (12288 * C ^ 2 * Ctr ^ 4) * Y +
          (8 * E ^ 2) * Y := by gcongr
      _ = (4 + 32 * Cnear ^ 2 + 32 + 64 * C ^ 2 +
          12288 * C ^ 2 * Ctr ^ 4 + 8 * E ^ 2) * Y := by ring
  apply hSum.trans
  have hCoeff :
      4 + 32 * Cnear ^ 2 + 32 + 64 * C ^ 2 +
          12288 * C ^ 2 * Ctr ^ 4 + 8 * E ^ 2 ≤
        100000 * (1 + Cnear ^ 2 + C ^ 2 + C ^ 2 * Ctr ^ 4 + E ^ 2) := by
    rw [← sub_nonneg]
    ring_nf
    positivity
  calc
    (4 + 32 * Cnear ^ 2 + 32 + 64 * C ^ 2 +
        12288 * C ^ 2 * Ctr ^ 4 + 8 * E ^ 2) * Y ≤
      (100000 * (1 + Cnear ^ 2 + C ^ 2 + C ^ 2 * Ctr ^ 4 + E ^ 2)) * Y :=
        mul_le_mul_of_nonneg_right hCoeff hY0
    _ = _ := by
      dsimp only [Y, E, X, B, R, P]
      ring

/-- The weighted Heath--Brown moment is nonnegative term by term. -/
theorem heathBrownWeightedMoment_nonneg (N : ℕ) (W : Finset ℝ) :
    0 ≤ heathBrownWeightedMoment N W := by
  unfold heathBrownWeightedMoment
  positivity

/-- The six child moments produced by the three literal source-localization
scales.  Keeping this package explicit prevents the recurrence from silently
identifying the left, central and right reflected lengths. -/
noncomputable def heathBrownSourceReflectedMomentPackage
    (T : ℝ) (N H : ℕ) (W : Finset ℝ) : ℝ :=
  let P₁ := heathBrownCorrectedCommonScale (gmSourceLeftScale N) H T
  let P₂ := heathBrownCorrectedCommonScale N H T
  let P₃ := heathBrownCorrectedCommonScale (gmSourceRightScale N) H T
  heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W +
    heathBrownWeightedMoment P₂ W + heathBrownWeightedMoment (2 * P₂) W +
    heathBrownWeightedMoment P₃ W + heathBrownWeightedMoment (2 * P₃) W

/-- The exact three-scale source recurrence after all local analytic losses
have been absorbed.  This theorem consumes the source localization theorem,
the source-sharp reflection at each literal scale, and the uniform profile
bound in one proof term. -/
theorem exists_heathBrownWeightedMoment_source_recurrence
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ N → T₀ ≤ T → (2 * N : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        (N : ℝ) * heathBrownWeightedMoment N W ≤
          C * T ^ (20 * η) * (N : ℝ) *
            ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
              heathBrownSourceReflectedMomentPackage T N
                (heathBrownSmoothingHeight T η) W + 1) := by
  let q := heathBrownReflectionDerivativeOrder 2 η
  obtain ⟨Cnear, Cmain, Ctr, K, L, D,
      hCnear, hCmain, hCtr, hK, hL, hD, hSource⟩ :=
    exists_heathBrownWeightedMoment_le_source_sharp_recurrence
      cutoff q (heathBrownReflectionDerivativeOrder_two_le 2 η) η hη
  obtain ⟨Cprofile, hCprofile, Tprofile, hTprofile, hProfile⟩ :=
    eventually_heathBrownLocalRecurrenceProfile_pow_ten_le_rpow η hη hηOne
  let A : ℝ := 100000 * (1 + Cnear ^ 2 + Cmain ^ 2 +
    Cmain ^ 2 * Ctr ^ 4 +
    (16 * K + L * (3 : ℝ) ^ (q + 2) + 2 * D) ^ 2)
  let Cfinal : ℝ := 9 * A * Cprofile
  refine ⟨Cfinal, by
    dsimp only [Cfinal, A]
    positivity, Tprofile, hTprofile, ?_⟩
  intro N T W hN hT hTwoNT hSep hInterval
  let H := heathBrownSmoothingHeight T η
  let Q₁ := gmSourceLeftScale N
  let Q₂ := N
  let Q₃ := gmSourceRightScale N
  let P₁ := heathBrownCorrectedCommonScale Q₁ H T
  let P₂ := heathBrownCorrectedCommonScale Q₂ H T
  let P₃ := heathBrownCorrectedCommonScale Q₃ H T
  let R : ℝ := W.card
  let U : ℝ := T ^ (20 * η)
  let F : ℝ := A * Cprofile * U * N
  let X₁ : ℝ := R * N + R ^ 2 + heathBrownWeightedMoment P₁ W +
    heathBrownWeightedMoment (2 * P₁) W + 1
  let X₂ : ℝ := R * N + R ^ 2 + heathBrownWeightedMoment P₂ W +
    heathBrownWeightedMoment (2 * P₂) W + 1
  let X₃ : ℝ := R * N + R ^ 2 + heathBrownWeightedMoment P₃ W +
    heathBrownWeightedMoment (2 * P₃) W + 1
  have hTTwo : 2 ≤ T := hTprofile.trans hT
  have hTPos : 0 < T := by linarith
  have hHPos : 0 < H := heathBrownSmoothingHeight_pos T η
  have hNPos : 0 < N := by omega
  have hNToT : (N : ℝ) ≤ T := by
    have hcast : ((2 * N : ℕ) : ℝ) ≤ T := hTwoNT
    push_cast at hcast
    linarith
  have hU : 0 ≤ U := Real.rpow_nonneg hTPos.le _
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hF : 0 ≤ F := by
    dsimp only [F]
    positivity
  have hX₁ : 0 ≤ X₁ := by
    dsimp only [X₁, R]
    have h₁ := heathBrownWeightedMoment_nonneg P₁ W
    have h₂ := heathBrownWeightedMoment_nonneg (2 * P₁) W
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by positivity) (by positivity))
            (sq_nonneg (W.card : ℝ))) h₁) h₂) zero_le_one
  have hX₂ : 0 ≤ X₂ := by
    dsimp only [X₂, R]
    have h₁ := heathBrownWeightedMoment_nonneg P₂ W
    have h₂ := heathBrownWeightedMoment_nonneg (2 * P₂) W
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by positivity) (by positivity))
            (sq_nonneg (W.card : ℝ))) h₁) h₂) zero_le_one
  have hX₃ : 0 ≤ X₃ := by
    dsimp only [X₃, R]
    have h₁ := heathBrownWeightedMoment_nonneg P₃ W
    have h₂ := heathBrownWeightedMoment_nonneg (2 * P₃) W
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by positivity) (by positivity))
            (sq_nonneg (W.card : ℝ))) h₁) h₂) zero_le_one
  have hQ₁ := heathBrown_source_scales_comparable hN (Q := Q₁) (by left; rfl)
  have hQ₂ := heathBrown_source_scales_comparable hN (Q := Q₂) (by right; left; rfl)
  have hQ₃ := heathBrown_source_scales_comparable hN (Q := Q₃) (by right; right; rfl)
  have trace_le (Q P : ℕ)
      (hQP : P = heathBrownCorrectedCommonScale Q H T)
      (hQData : 4 ≤ Q ∧ N ≤ 2 * Q ∧ Q ≤ 2 * N) :
      heathBrownSourceSharpTraceRecurrenceBound
          Cnear Cmain Ctr K L D η q T W Q H ≤
        F * (R * N + R ^ 2 + heathBrownWeightedMoment P W +
          heathBrownWeightedMoment (2 * P) W + 1) := by
    have hQPos : 0 < Q := by omega
    have hTrace := heathBrownSourceSharpTraceRecurrenceBound_le_profile
      (η := η) (T := T) (Cnear := Cnear) (C := Cmain) (Ctr := Ctr)
      (K := K) (L := L) (D := D) (N := N) (Q := Q) (H := H) (W := W)
      hη hηOne hTTwo hNPos hQPos hQData.2.2 hNToT hHPos rfl
      hK.le hL.le hD.le
    have hProf := hProfile T Q H hT hQPos rfl
    change heathBrownLocalRecurrenceProfile η T Q H ^ 10 ≤
      Cprofile * U at hProf
    have hMoment₁ := heathBrownWeightedMoment_nonneg
      (heathBrownCorrectedCommonScale Q H T) W
    have hMoment₂ := heathBrownWeightedMoment_nonneg
      (2 * heathBrownCorrectedCommonScale Q H T) W
    have hX : 0 ≤ R * N + R ^ 2 + heathBrownWeightedMoment
          (heathBrownCorrectedCommonScale Q H T) W +
        heathBrownWeightedMoment
          (2 * heathBrownCorrectedCommonScale Q H T) W + 1 := by
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (by positivity) (by positivity))
              (sq_nonneg R)) hMoment₁) hMoment₂) zero_le_one
    have hCoefficient :
        A * heathBrownLocalRecurrenceProfile η T Q H ^ 10 * N ≤
          A * (Cprofile * U) * N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hProf hA) (by positivity)
    rw [hQP]
    calc
      _ ≤ A * heathBrownLocalRecurrenceProfile η T Q H ^ 10 * N *
          (R * N + R ^ 2 + heathBrownWeightedMoment
              (heathBrownCorrectedCommonScale Q H T) W +
            heathBrownWeightedMoment
              (2 * heathBrownCorrectedCommonScale Q H T) W + 1) := by
        simpa only [A, q, R] using hTrace
      _ ≤ A * (Cprofile * U) * N *
          (R * N + R ^ 2 + heathBrownWeightedMoment
              (heathBrownCorrectedCommonScale Q H T) W +
            heathBrownWeightedMoment
              (2 * heathBrownCorrectedCommonScale Q H T) W + 1) := by
        exact mul_le_mul_of_nonneg_right hCoefficient hX
      _ = F * (R * N + R ^ 2 + heathBrownWeightedMoment
              (heathBrownCorrectedCommonScale Q H T) W +
            heathBrownWeightedMoment
              (2 * heathBrownCorrectedCommonScale Q H T) W + 1) := by
        change A * (Cprofile * U) * N * _ =
          (A * Cprofile * U * N) * _
        ring
  have hTrace₁ : heathBrownSourceSharpTraceRecurrenceBound
      Cnear Cmain Ctr K L D η q T W Q₁ H ≤ F * X₁ := by
    simpa only [X₁] using trace_le Q₁ P₁ rfl hQ₁
  have hTrace₂ : heathBrownSourceSharpTraceRecurrenceBound
      Cnear Cmain Ctr K L D η q T W Q₂ H ≤ F * X₂ := by
    simpa only [X₂] using trace_le Q₂ P₂ rfl hQ₂
  have hTrace₃ : heathBrownSourceSharpTraceRecurrenceBound
      Cnear Cmain Ctr K L D η q T W Q₃ H ≤ F * X₃ := by
    simpa only [X₃] using trace_le Q₃ P₃ rfl hQ₃
  have hRaw := hSource (N := N) (H := H) (T := T) (W := W)
    hN hHPos (by linarith) hSep hInterval
  have hPackage :
      heathBrownSourceReflectedMomentPackage T N H W =
        (heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W) +
        (heathBrownWeightedMoment P₂ W + heathBrownWeightedMoment (2 * P₂) W) +
        (heathBrownWeightedMoment P₃ W + heathBrownWeightedMoment (2 * P₃) W) := by
    dsimp only [heathBrownSourceReflectedMomentPackage, P₁, P₂, P₃, Q₁, Q₂, Q₃]
    ring
  have hSumX : X₁ + X₂ + X₃ ≤
      3 * (R * N + R ^ 2 +
        heathBrownSourceReflectedMomentPackage T N H W + 1) := by
    rw [hPackage]
    dsimp only [X₁, X₂, X₃]
    have hMom : 0 ≤
        (heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W) +
        (heathBrownWeightedMoment P₂ W + heathBrownWeightedMoment (2 * P₂) W) +
        (heathBrownWeightedMoment P₃ W + heathBrownWeightedMoment (2 * P₃) W) := by
      have hP₁ := heathBrownWeightedMoment_nonneg P₁ W
      have h2P₁ := heathBrownWeightedMoment_nonneg (2 * P₁) W
      have hP₂ := heathBrownWeightedMoment_nonneg P₂ W
      have h2P₂ := heathBrownWeightedMoment_nonneg (2 * P₂) W
      have hP₃ := heathBrownWeightedMoment_nonneg P₃ W
      have h2P₃ := heathBrownWeightedMoment_nonneg (2 * P₃) W
      exact add_nonneg (add_nonneg (add_nonneg hP₁ h2P₁)
        (add_nonneg hP₂ h2P₂)) (add_nonneg hP₃ h2P₃)
    let M : ℝ :=
      (heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W) +
      (heathBrownWeightedMoment P₂ W + heathBrownWeightedMoment (2 * P₂) W) +
      (heathBrownWeightedMoment P₃ W + heathBrownWeightedMoment (2 * P₃) W)
    have hM : 0 ≤ M := by simpa only [M] using hMom
    calc
      _ = 3 * (R * N + R ^ 2 + 1) + M := by
        dsimp only [M]
        ring
      _ ≤ 3 * (R * N + R ^ 2 + 1) + 3 * M := by
        gcongr
        nlinarith
      _ = _ := by
        dsimp only [M]
        ring
  calc
    (N : ℝ) * heathBrownWeightedMoment N W ≤
        3 * (heathBrownSourceSharpTraceRecurrenceBound
              Cnear Cmain Ctr K L D η q T W Q₁ H +
          heathBrownSourceSharpTraceRecurrenceBound
              Cnear Cmain Ctr K L D η q T W Q₂ H +
          heathBrownSourceSharpTraceRecurrenceBound
              Cnear Cmain Ctr K L D η q T W Q₃ H) := by
      simpa only [Q₁, Q₂, Q₃, H] using hRaw
    _ ≤ 3 * (F * X₁ + F * X₂ + F * X₃) := by gcongr
    _ = 3 * F * (X₁ + X₂ + X₃) := by ring
    _ ≤ 3 * F * (3 * (R * N + R ^ 2 +
        heathBrownSourceReflectedMomentPackage T N H W + 1)) := by
      exact mul_le_mul_of_nonneg_left hSumX (mul_nonneg (by norm_num) hF)
    _ = 9 * F * (R * N + R ^ 2 +
        heathBrownSourceReflectedMomentPackage T N H W + 1) := by
      ring
    _ = Cfinal * T ^ (20 * η) * (N : ℝ) *
        ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
          heathBrownSourceReflectedMomentPackage T N
            (heathBrownSmoothingHeight T η) W + 1) := by
      rw [show F = A * Cprofile * U * (N : ℝ) by rfl,
        show U = T ^ (20 * η) by rfl,
        show R = (W.card : ℝ) by rfl,
        show H = heathBrownSmoothingHeight T η by rfl,
        show Cfinal = 9 * A * Cprofile by rfl]
      ring

/-! ## Source-sharp powering recurrence

The earlier coefficient-one route through the powered block introduces a
factor proportional to its length.  Montgomery--Vaughan Lemma 29.9 instead
keeps the critical-line weight `m⁻¹ᐟ²` attached to the arithmetic
multiplicity.  The following declarations formalize that normalization
directly. -/

/-- The literal coefficients of the `k`-th power of the weighted
critical-line block. -/
noncomputable def heathBrownRawPoweredCoeffs
    (N k : ℕ) (m : ℕ) : ℂ :=
  finitePowCoeff N k (fun _ => (1 : ℂ)) m *
    (heathBrownHalfWeight m : ℂ)

/-- Exact source-normalized powering identity, with no artificial
left-endpoint square-root. -/
theorem heathBrownRawPoweredWide_eq
    (N k : ℕ) (y : ℝ) (hN : 0 < N) (hk : 0 < k) :
    wideDirichletPoly (N ^ k) k
        (heathBrownRawPoweredCoeffs N k) (-y) =
      (sourceDirichletPoly N
        (fun n => (heathBrownHalfWeight n : ℂ)) y) ^ k := by
  rw [sourceDirichletPoly_halfWeight_pow_eq_finitePowPoly,
    finite_polynomial_power_identity_Ioc N k (fun _ => (1 : ℂ))
      ((1 / 2 : ℂ) - (y : ℂ) * I) hN hk]
  unfold wideDirichletPoly
  have hUpper : 2 ^ k * N ^ k = (2 * N) ^ k := by rw [mul_pow]
  rw [hUpper]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
  unfold heathBrownRawPoweredCoeffs
  rw [mul_assoc]
  have hPhase := heathBrownHalfWeight_mul_phase_eq_cpow m y hmPos
  have hExponent : -(((-y : ℝ) : ℂ)) * I = (y : ℂ) * I := by
    push_cast
    ring
  rw [hExponent, hPhase]

/-- Squared-moment form of the exact raw powering identity. -/
theorem sum_norm_heathBrownRawPoweredWide_sq
    (N k : ℕ) (W : Finset ℝ) (hN : 0 < N) (hk : 0 < k) :
    (∑ t ∈ W, ∑ u ∈ W,
      ‖wideDirichletPoly (N ^ k) k
        (heathBrownRawPoweredCoeffs N k) (-(t - u))‖ ^ 2) =
      heathBrownWeightedPowerMoment N k W := by
  unfold heathBrownWeightedPowerMoment
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  rw [heathBrownRawPoweredWide_eq N k (t - u) hN hk, norm_pow,
    ← pow_mul]
  congr 1
  omega

/-- Cauchy--Schwarz over the exact `k` dyadic pieces of the raw powered
critical-line polynomial. -/
theorem sum_norm_heathBrownRawPoweredWide_sq_le_blocks
    (N k : ℕ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
      ‖wideDirichletPoly (N ^ k) k (heathBrownRawPoweredCoeffs N k)
        (-(t - u))‖ ^ 2) ≤
      (k : ℝ) * ∑ r ∈ Finset.range k,
        ∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, (k : ℝ) *
        ∑ r ∈ Finset.range k,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [wideDirichletPoly_eq_sum_blocks]
      have hCS := complex_sum_sq_le_card_mul_sum_sq (Finset.range k)
        (fun r => dirichletPoly (2 ^ r * N ^ k)
          (heathBrownRawPoweredCoeffs N k) (-(t - u)))
      simpa only [dirichletPoly_neg_eq_sourceDirichletPoly,
        Finset.card_range, Nat.cast_id] using hCS
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        (∑ t ∈ W, ∑ u ∈ W, ∑ r ∈ Finset.range k,
            (k : ℝ) *
              ‖sourceDirichletPoly (2 ^ r * N ^ k)
                (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) =
            ∑ t ∈ W, ∑ r ∈ Finset.range k, ∑ u ∈ W,
              (k : ℝ) *
                ‖sourceDirichletPoly (2 ^ r * N ^ k)
                  (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range k, ∑ t ∈ W, ∑ u ∈ W,
              (k : ℝ) *
                ‖sourceDirichletPoly (2 ^ r * N ^ k)
                  (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2 := by
          rw [Finset.sum_comm]

/-- Each raw powered dyadic block is bounded directly by the weighted
moment at its own scale.  This is the normalization missing from the
coefficient-one route. -/
theorem exists_heathBrownRawPoweredBlockMoment_le_weighted
    (N k : ℕ) (W : Finset ℝ) (hN : 0 < N)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ r < k,
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
          heathBrownWeightedMoment (2 ^ r * N ^ k) W := by
  obtain ⟨C, hC, hCoeff⟩ := finitePowCoeff_bound N k
    (fun _ => (1 : ℂ)) (by intro n hn; simp)
    η hη
  refine ⟨C, hC, ?_⟩
  intro r hr
  let Q : ℕ := 2 ^ r * N ^ k
  let B : ℝ := C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hMajorant := sourceDirichletPoly_differenceMoment_le_of_norm_le
    Q W (heathBrownRawPoweredCoeffs N k)
      (fun m => B * heathBrownHalfWeight m)
    (by
      intro m hm
      exact mul_nonneg hB (heathBrownHalfWeight_nonneg m))
    (by
      intro m hm
      have hmWide := heathBrown_poweredBlock_subset N k r m hr hm
      have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp hmWide).1
      have hmUpper : m ≤ 2 ^ k * N ^ k := (Finset.mem_Ioc.mp hmWide).2
      have hPow : (m : ℝ) ^ η ≤ ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
        exact Real.rpow_le_rpow (Nat.cast_nonneg m)
          (by exact_mod_cast hmUpper) hη.le
      have hCoeff' : ‖finitePowCoeff N k (fun _ => (1 : ℂ)) m‖ ≤ B := by
        calc
          _ ≤ C * (m : ℝ) ^ η := hCoeff m hmPos
          _ ≤ C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
            exact mul_le_mul_of_nonneg_left hPow hC.le
          _ = B := rfl
      unfold heathBrownRawPoweredCoeffs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heathBrownHalfWeight_nonneg m)]
      exact mul_le_mul_of_nonneg_right hCoeff'
        (heathBrownHalfWeight_nonneg m))
  have hConstant :
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly Q
            (fun m => ((B * heathBrownHalfWeight m : ℝ) : ℂ))
              (t - u)‖ ^ 2) =
        B ^ 2 * heathBrownWeightedMoment Q W := by
    unfold heathBrownWeightedMoment
    have hPoly (x : ℝ) :
        sourceDirichletPoly Q
            (fun m => ((B * heathBrownHalfWeight m : ℝ) : ℂ)) x =
          (B : ℂ) * sourceDirichletPoly Q
            (fun m => (heathBrownHalfWeight m : ℂ)) x := by
      simpa only [ofReal_mul] using sourceDirichletPoly_real_smul_coeffs
        Q heathBrownHalfWeight B x
    simp_rw [hPoly]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB, mul_pow]
  simpa only [Q, B, hConstant] using hMajorant.trans_eq hConstant

/-- A raw powered block transferred to the common power-of-two terminal
scale without any factor proportional to that scale. -/
theorem exists_heathBrownRawPoweredBlockMoment_le_target
    (N k c : ℕ) (W : Finset ℝ) (hN : 0 < N) (hkc : k ≤ c)
    (η : ℝ) (hη : 0 < η) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ r < k,
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
          (4 * (D * (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (heathBrownPoweredTargetScale N k c) W +
              heathBrownWeightedMoment
                (2 * heathBrownPoweredTargetScale N k c) W)) := by
  obtain ⟨C, hC, hBlock⟩ :=
    exists_heathBrownRawPoweredBlockMoment_le_weighted N k W hN η hη
  obtain ⟨D, hD, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_transfer η hη
  refine ⟨C, D, hC, hD, ?_⟩
  intro r hr
  let Q : ℕ := 2 ^ r * N ^ k
  let J : ℕ := 2 ^ (c - r)
  let P : ℕ := heathBrownPoweredTargetScale N k c
  have hrc : r ≤ c := le_trans (Nat.le_of_lt hr) hkc
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hJQ : J * Q = P := by
    simpa only [J, Q, P] using
      heathBrownPoweredBlock_mul_aux_eq_target N k c r hrc
  have hTransferred := hTransfer J Q W hJ hQ
  rw [hJQ] at hTransferred
  have hCastJQ : (J : ℝ) * (Q : ℝ) = (P : ℝ) := by exact_mod_cast hJQ
  rw [hCastJQ] at hTransferred
  have hTransferred' :
      heathBrownWeightedMoment (2 ^ r * N ^ k) W ≤
        4 * (D * (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (heathBrownPoweredTargetScale N k c) W +
            heathBrownWeightedMoment
              (2 * heathBrownPoweredTargetScale N k c) W) := by
    simpa only [Q, P] using hTransferred
  exact (hBlock r hr).trans
    (mul_le_mul_of_nonneg_left hTransferred' (by positivity))

/-- Source-sharp Montgomery--Vaughan Lemma 29.9.  In particular, the
terminal factor is a weighted moment, not the terminal length times that
moment. -/
theorem exists_heathBrownWeightedMoment_powering_recurrence_sharp
    (N k c : ℕ) (W : Finset ℝ) (hN : 0 < N) (hk : 0 < k)
    (hkc : k ≤ c) (η : ℝ) (hη : 0 < η) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      heathBrownWeightedMoment N W ^ k ≤
        (((W.card : ℝ) ^ 2) ^ (k - 1)) * (k : ℝ) ^ 2 *
          (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
          (4 * (D * (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (heathBrownPoweredTargetScale N k c) W +
              heathBrownWeightedMoment
                (2 * heathBrownPoweredTargetScale N k c) W)) := by
  obtain ⟨C, D, hC, hD, hBlock⟩ :=
    exists_heathBrownRawPoweredBlockMoment_le_target
      N k c W hN hkc η hη
  refine ⟨C, D, hC, hD, ?_⟩
  let P : ℕ := heathBrownPoweredTargetScale N k c
  let B : ℝ := C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η
  let E : ℝ := 4 * (D * (4 * P : ℝ) ^ η) ^ 2 *
    (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (by positivity) (add_nonneg
      (heathBrownWeightedMoment_nonneg P W)
      (heathBrownWeightedMoment_nonneg (2 * P) W))
  have hHolder := heathBrownWeightedMoment_pow_le N k W hk
  have hIdentity := sum_norm_heathBrownRawPoweredWide_sq N k W hN hk
  have hBlocks := sum_norm_heathBrownRawPoweredWide_sq_le_blocks N k W
  have hUniform : ∀ r ∈ Finset.range k,
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤ B ^ 2 * E := by
    intro r hr
    simpa only [B, E, P] using hBlock r (Finset.mem_range.mp hr)
  have hSum :
      (∑ r ∈ Finset.range k,
          ∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
        (k : ℝ) * (B ^ 2 * E) := by
    calc
      _ ≤ ∑ r ∈ Finset.range k, B ^ 2 * E := Finset.sum_le_sum hUniform
      _ = (k : ℝ) * (B ^ 2 * E) := by simp
  calc
    heathBrownWeightedMoment N W ^ k ≤
        (((W.card : ℝ) ^ 2) ^ (k - 1)) *
          heathBrownWeightedPowerMoment N k W := hHolder
    _ = (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        (∑ t ∈ W, ∑ u ∈ W,
          ‖wideDirichletPoly (N ^ k) k (heathBrownRawPoweredCoeffs N k)
            (-(t - u))‖ ^ 2) := by rw [hIdentity]
    _ ≤ (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        ((k : ℝ) * ∑ r ∈ Finset.range k,
          ∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hBlocks (by positivity)
    _ ≤ (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        ((k : ℝ) * ((k : ℝ) * (B ^ 2 * E))) := by gcongr
    _ = (((W.card : ℝ) ^ 2) ^ (k - 1)) * (k : ℝ) ^ 2 *
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
        (4 * (D * (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment (heathBrownPoweredTargetScale N k c) W +
            heathBrownWeightedMoment
              (2 * heathBrownPoweredTargetScale N k c) W)) := by
      simp only [B, E, P]
      ring

/-- Exact `k = c = 2` source-sharp powering inequality used in the middle
range of Montgomery--Vaughan Lemma 29.10. -/
theorem exists_heathBrownWeightedMoment_sq_le_four_mul_sq_sharp
    (M : ℕ) (W : Finset ℝ) (hM : 0 < M) (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ, 0 < E ∧
      heathBrownWeightedMoment M W ^ 2 ≤
        E * ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          ((16 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          (W.card : ℝ) ^ 2 *
          (heathBrownWeightedMoment (4 * M ^ 2) W +
            heathBrownWeightedMoment (8 * M ^ 2) W) := by
  obtain ⟨C, D, hC, hD, hRec⟩ :=
    exists_heathBrownWeightedMoment_powering_recurrence_sharp
      M 2 2 W hM (by omega) (by omega) η hη
  refine ⟨16 * C ^ 2 * D ^ 2, by positivity, ?_⟩
  norm_num [heathBrownPoweredTargetScale, Nat.cast_pow,
    Nat.cast_mul] at hRec ⊢
  convert hRec using 1
  all_goals ring_nf

/-- The least common power-of-two exponent above all three literal source
reflection pairs. -/
noncomputable def heathBrownSourceTerminalExponent
    (T : ℝ) (N H : ℕ) : ℕ :=
  max (heathBrownCorrectedCommonExponent (gmSourceLeftScale N) H T)
      (max (heathBrownCorrectedCommonExponent N H T)
        (heathBrownCorrectedCommonExponent (gmSourceRightScale N) H T)) + 1

/-- Common terminal scale for the complete six-child source package. -/
noncomputable def heathBrownSourceTerminalScale
    (T : ℝ) (N H : ℕ) : ℕ :=
  2 ^ heathBrownSourceTerminalExponent T N H

theorem heathBrown_source_exponent_succ_le_terminal
    (T : ℝ) (N H : ℕ) :
    let c := heathBrownSourceTerminalExponent T N H
    heathBrownCorrectedCommonExponent (gmSourceLeftScale N) H T + 1 ≤ c ∧
      heathBrownCorrectedCommonExponent N H T + 1 ≤ c ∧
      heathBrownCorrectedCommonExponent (gmSourceRightScale N) H T + 1 ≤ c := by
  dsimp only [heathBrownSourceTerminalExponent]
  omega

/-- The six reflected child moments are transferred, in their actual
source grouping, to one common terminal pair. -/
theorem exists_heathBrownSourceReflectedMomentPackage_le_terminal
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (N H : ℕ) (W : Finset ℝ),
        heathBrownSourceReflectedMomentPackage T N H W ≤
          24 * (C * (4 * heathBrownSourceTerminalScale T N H : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment (heathBrownSourceTerminalScale T N H) W +
              heathBrownWeightedMoment
                (2 * heathBrownSourceTerminalScale T N H) W) := by
  obtain ⟨C, hC, hPair⟩ :=
    exists_heathBrownWeightedMoment_pair_le_common_target η hη
  refine ⟨C, hC, ?_⟩
  intro T N H W
  let e₁ := heathBrownCorrectedCommonExponent (gmSourceLeftScale N) H T
  let e₂ := heathBrownCorrectedCommonExponent N H T
  let e₃ := heathBrownCorrectedCommonExponent (gmSourceRightScale N) H T
  let c := heathBrownSourceTerminalExponent T N H
  let Z : ℝ := 8 * (C * (4 * (2 ^ c : ℕ) : ℝ) ^ η) ^ 2 *
    (heathBrownWeightedMoment (2 ^ c) W +
      heathBrownWeightedMoment (2 ^ (c + 1)) W)
  have hc := heathBrown_source_exponent_succ_le_terminal T N H
  change e₁ + 1 ≤ c ∧ e₂ + 1 ≤ c ∧ e₃ + 1 ≤ c at hc
  have h₁ := hPair e₁ c W hc.1
  have h₂ := hPair e₂ c W hc.2.1
  have h₃ := hPair e₃ c W hc.2.2
  change _ ≤ Z at h₁
  change _ ≤ Z at h₂
  change _ ≤ Z at h₃
  have hTwo : 2 * 2 ^ c = 2 ^ (c + 1) := by rw [pow_succ]; ring
  have hPackage :
      heathBrownSourceReflectedMomentPackage T N H W =
        (heathBrownWeightedMoment (2 ^ e₁) W +
          heathBrownWeightedMoment (2 ^ (e₁ + 1)) W) +
        (heathBrownWeightedMoment (2 ^ e₂) W +
          heathBrownWeightedMoment (2 ^ (e₂ + 1)) W) +
        (heathBrownWeightedMoment (2 ^ e₃) W +
          heathBrownWeightedMoment (2 ^ (e₃ + 1)) W) := by
    dsimp only [heathBrownSourceReflectedMomentPackage, e₁, e₂, e₃,
      heathBrownCorrectedCommonScale]
    simp only [pow_succ]
    ring_nf
  have hSum :
      (heathBrownWeightedMoment (2 ^ e₁) W +
          heathBrownWeightedMoment (2 ^ (e₁ + 1)) W) +
        (heathBrownWeightedMoment (2 ^ e₂) W +
          heathBrownWeightedMoment (2 ^ (e₂ + 1)) W) +
        (heathBrownWeightedMoment (2 ^ e₃) W +
          heathBrownWeightedMoment (2 ^ (e₃ + 1)) W) ≤ 3 * Z := by
    calc
      _ ≤ Z + Z + Z := add_le_add (add_le_add h₁ h₂) h₃
      _ = 3 * Z := by ring
  calc
    heathBrownSourceReflectedMomentPackage T N H W ≤ 3 * Z := by
      rw [hPackage]
      exact hSum
    _ = 24 * (C * (4 * heathBrownSourceTerminalScale T N H : ℝ) ^ η) ^ 2 *
        (heathBrownWeightedMoment (heathBrownSourceTerminalScale T N H) W +
          heathBrownWeightedMoment
            (2 * heathBrownSourceTerminalScale T N H) W) := by
      dsimp only [Z, c, heathBrownSourceTerminalScale]
      rw [hTwo]
      ring

/-- The common six-child terminal remains at most quadratic in the height.
This deliberately records the rounded power-of-two scale used by the proof,
not an unrelated real proxy. -/
theorem heathBrownSourceTerminalScale_le_twenty_four_mul_sq
    {η T : ℝ} {N H : ℕ} (hη : 0 ≤ η) (hηOne : η ≤ 1)
    (hT : 2 ≤ T) (hN : 30 ≤ N)
    (hHeight : H = heathBrownSmoothingHeight T η) :
    (heathBrownSourceTerminalScale T N H : ℝ) ≤ 24 * T ^ 2 := by
  let e₁ := heathBrownCorrectedCommonExponent (gmSourceLeftScale N) H T
  let e₂ := heathBrownCorrectedCommonExponent N H T
  let e₃ := heathBrownCorrectedCommonExponent (gmSourceRightScale N) H T
  have hQ₁ := (heathBrown_source_scales_comparable hN
    (Q := gmSourceLeftScale N) (by left; rfl)).1
  have hQ₂ := (heathBrown_source_scales_comparable hN
    (Q := N) (by right; left; rfl)).1
  have hQ₃ := (heathBrown_source_scales_comparable hN
    (Q := gmSourceRightScale N) (by right; right; rfl)).1
  have h₁ := heathBrownCorrectedCommonScale_le_twelve_mul_sq
    hη hηOne hT (by omega : 0 < gmSourceLeftScale N) hHeight
  have h₂ := heathBrownCorrectedCommonScale_le_twelve_mul_sq
    hη hηOne hT (by omega : 0 < N) hHeight
  have h₃ := heathBrownCorrectedCommonScale_le_twelve_mul_sq
    hη hηOne hT (by omega : 0 < gmSourceRightScale N) hHeight
  have h₁' : (2 : ℝ) * (2 ^ e₁ : ℕ) ≤ 24 * T ^ 2 := by
    change ((2 ^ e₁ : ℕ) : ℝ) ≤ 12 * T ^ 2 at h₁
    have := mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have h₂' : (2 : ℝ) * (2 ^ e₂ : ℕ) ≤ 24 * T ^ 2 := by
    change ((2 ^ e₂ : ℕ) : ℝ) ≤ 12 * T ^ 2 at h₂
    have := mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have h₃' : (2 : ℝ) * (2 ^ e₃ : ℕ) ≤ 24 * T ^ 2 := by
    change ((2 ^ e₃ : ℕ) : ℝ) ≤ 12 * T ^ 2 at h₃
    have := mul_le_mul_of_nonneg_left h₃ (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  change (2 ^ (max e₁ (max e₂ e₃) + 1) : ℕ) ≤ (24 * T ^ 2 : ℝ)
  rw [pow_succ]
  push_cast at h₁' h₂' h₃' ⊢
  by_cases h12 : e₁ ≤ max e₂ e₃
  · rw [max_eq_right h12]
    by_cases h23 : e₂ ≤ e₃
    · rw [max_eq_right h23]
      nlinarith
    · rw [max_eq_left (le_of_not_ge h23)]
      nlinarith
  · rw [max_eq_left (le_of_not_ge h12)]
    nlinarith

/-- Source-scale physical bound retaining the reciprocal dependence on the
original length.  This is the quantitative `M = T H / N` relation in
Montgomery--Vaughan (29.40). -/
theorem heathBrownSourceTerminalScale_le_physical
    {T : ℝ} {N H : ℕ} (hT : 1 ≤ T) (hN : 30 ≤ N) (hH : 0 < H) :
    (heathBrownSourceTerminalScale T N H : ℝ) ≤
      16 * (T * H / N + 1) := by
  let e₁ := heathBrownCorrectedCommonExponent (gmSourceLeftScale N) H T
  let e₂ := heathBrownCorrectedCommonExponent N H T
  let e₃ := heathBrownCorrectedCommonExponent (gmSourceRightScale N) H T
  have hData₁ := heathBrown_source_scales_comparable hN
    (Q := gmSourceLeftScale N) (by left; rfl)
  have hData₂ := heathBrown_source_scales_comparable hN
    (Q := N) (by right; left; rfl)
  have hData₃ := heathBrown_source_scales_comparable hN
    (Q := gmSourceRightScale N) (by right; right; rfl)
  have hTH : 0 ≤ T * (H : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg H)
  have hNReal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have physical (Q : ℕ) (hQ : 0 < Q) (hNQ : N ≤ 2 * Q) :
      (heathBrownCorrectedCommonScale Q H T : ℝ) ≤
        8 * (T * H / N + 1) := by
    have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hHalfNPos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    have hNQReal : (N : ℝ) ≤ 2 * Q := by exact_mod_cast hNQ
    have hHalfNQ : (N : ℝ) / 2 ≤ Q := by linarith
    have hDiv₁ : T * H / Q ≤ T * H / ((N : ℝ) / 2) :=
      div_le_div_of_nonneg_left hTH hHalfNPos hHalfNQ
    have hDiv₂ : T * H / ((N : ℝ) / 2) = 2 * (T * H / N) := by
      field_simp
    have hScale := heathBrownCorrectedCommonScale_le_physical
      Q H T hQ hH hT
    calc
      _ ≤ 4 * (T * H / Q + 1) := hScale
      _ ≤ 4 * (2 * (T * H / N) + 1) := by rw [← hDiv₂]; gcongr
      _ ≤ 8 * (T * H / N + 1) := by
        have hDivNonneg : 0 ≤ T * H / N := div_nonneg hTH hNReal.le
        nlinarith
  have h₁ := physical (gmSourceLeftScale N) (by omega) hData₁.2.1
  have h₂ := physical N (by omega) hData₂.2.1
  have h₃ := physical (gmSourceRightScale N) (by omega) hData₃.2.1
  have h₁' : (2 : ℝ) * (2 ^ e₁ : ℕ) ≤ 16 * (T * H / N + 1) := by
    change ((2 ^ e₁ : ℕ) : ℝ) ≤ 8 * (T * H / N + 1) at h₁
    nlinarith
  have h₂' : (2 : ℝ) * (2 ^ e₂ : ℕ) ≤ 16 * (T * H / N + 1) := by
    change ((2 ^ e₂ : ℕ) : ℝ) ≤ 8 * (T * H / N + 1) at h₂
    nlinarith
  have h₃' : (2 : ℝ) * (2 ^ e₃ : ℕ) ≤ 16 * (T * H / N + 1) := by
    change ((2 ^ e₃ : ℕ) : ℝ) ≤ 8 * (T * H / N + 1) at h₃
    nlinarith
  change (2 ^ (max e₁ (max e₂ e₃) + 1) : ℕ) ≤
    (16 * (T * H / N + 1) : ℝ)
  rw [pow_succ]
  push_cast at h₁' h₂' h₃' ⊢
  by_cases h12 : e₁ ≤ max e₂ e₃
  · rw [max_eq_right h12]
    by_cases h23 : e₂ ≤ e₃
    · rw [max_eq_right h23]
      nlinarith
    · rw [max_eq_left (le_of_not_ge h23)]
      nlinarith
  · rw [max_eq_left (le_of_not_ge h12)]
    nlinarith

/-- Montgomery--Vaughan (29.41) with the literal three-scale reflection
output consolidated to its actual terminal dyadic pair. -/
theorem exists_heathBrownWeightedMoment_terminal_recurrence
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ N → T₀ ≤ T → (2 * N : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownWeightedMoment N W ≤
          C * T ^ (20 * η) *
            ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
              24 * (D *
                (4 * heathBrownSourceTerminalScale T N
                  (heathBrownSmoothingHeight T η) : ℝ) ^ η) ^ 2 *
                (heathBrownWeightedMoment
                    (heathBrownSourceTerminalScale T N
                      (heathBrownSmoothingHeight T η)) W +
                  heathBrownWeightedMoment
                    (2 * heathBrownSourceTerminalScale T N
                      (heathBrownSmoothingHeight T η)) W) + 1) := by
  obtain ⟨C, hC, T₀, hT₀, hSource⟩ :=
    exists_heathBrownWeightedMoment_source_recurrence cutoff η hη hηOne
  obtain ⟨D, hD, hPackage⟩ :=
    exists_heathBrownSourceReflectedMomentPackage_le_terminal η hη
  refine ⟨C, D, hC, hD, T₀, hT₀, ?_⟩
  intro N T W hN hT hTwoNT hSep hInterval
  have hNPosNat : 0 < N := by omega
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hNPosNat
  have hRaw := hSource N T W hN hT hTwoNT hSep hInterval
  have hPack := hPackage T N (heathBrownSmoothingHeight T η) W
  have hOuter : 0 ≤ C * T ^ (20 * η) * (N : ℝ) := by
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
      (Nat.cast_nonneg N)
  have hInside :
      (W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
          heathBrownSourceReflectedMomentPackage T N
            (heathBrownSmoothingHeight T η) W + 1 ≤
        (W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
          24 * (D *
            (4 * heathBrownSourceTerminalScale T N
              (heathBrownSmoothingHeight T η) : ℝ) ^ η) ^ 2 *
            (heathBrownWeightedMoment
                (heathBrownSourceTerminalScale T N
                  (heathBrownSmoothingHeight T η)) W +
              heathBrownWeightedMoment
                (2 * heathBrownSourceTerminalScale T N
                  (heathBrownSmoothingHeight T η)) W) + 1 := by
    linarith
  have hScaled := hRaw.trans
    (mul_le_mul_of_nonneg_left hInside hOuter)
  have hCancel :
      (N : ℝ) * heathBrownWeightedMoment N W ≤
        (N : ℝ) *
          (C * T ^ (20 * η) *
            ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
              24 * (D *
                (4 * heathBrownSourceTerminalScale T N
                  (heathBrownSmoothingHeight T η) : ℝ) ^ η) ^ 2 *
                (heathBrownWeightedMoment
                    (heathBrownSourceTerminalScale T N
                      (heathBrownSmoothingHeight T η)) W +
                  heathBrownWeightedMoment
                    (2 * heathBrownSourceTerminalScale T N
                      (heathBrownSmoothingHeight T η)) W) + 1)) := by
    convert hScaled using 1
    all_goals ring
  exact le_of_mul_le_mul_left hCancel hNPos

/-- Uniform finite fallback for bounded source lengths.  It uses the exact
critical-line square-sum and Cauchy--Schwarz, so it is independent of the
height. -/
theorem heathBrownWeightedMoment_le_card_sq_mul_length
    (N : ℕ) (W : Finset ℝ) (hN : 0 < N) :
    heathBrownWeightedMoment N W ≤
      (W.card : ℝ) ^ 2 * N := by
  have hPoint (y : ℝ) :
      ‖sourceDirichletPoly N
          (fun n => (heathBrownHalfWeight n : ℂ)) y‖ ^ 2 ≤ (N : ℝ) := by
    have hCS := complex_sum_sq_le_card_mul_sum_sq (Finset.Ioc N (2 * N))
      (fun n => (heathBrownHalfWeight n : ℂ) * (n : ℂ) ^ (y * I))
    have hL2 := sum_heathBrownHalfWeight_sq_le_one N hN
    have hTerm : ∀ n ∈ Finset.Ioc N (2 * N),
        ‖(heathBrownHalfWeight n : ℂ) * (n : ℂ) ^ (y * I)‖ ^ 2 =
          ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2 := by
      intro n hn
      have hnBounds := Finset.mem_Ioc.mp hn
      have hnPos : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by omega)
      have hNormPhase : ‖(n : ℂ) ^ (y * I)‖ = 1 := by
        change ‖((n : ℝ) : ℂ) ^ (y * I)‖ = 1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
        norm_num
      rw [norm_mul, hNormPhase, mul_one]
    have hCard : (Finset.Ioc N (2 * N)).card = N := by
      simp only [Nat.card_Ioc]
      omega
    unfold sourceDirichletPoly
    calc
      _ ≤ ((Finset.Ioc N (2 * N)).card : ℝ) *
          ∑ n ∈ Finset.Ioc N (2 * N),
            ‖(heathBrownHalfWeight n : ℂ) * (n : ℂ) ^ (y * I)‖ ^ 2 := hCS
      _ = (N : ℝ) * ∑ n ∈ Finset.Ioc N (2 * N),
          ‖(heathBrownHalfWeight n : ℂ)‖ ^ 2 := by
        rw [hCard]
        congr 1
        exact Finset.sum_congr rfl hTerm
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  unfold heathBrownWeightedMoment
  calc
    _ ≤ ∑ _t ∈ W, ∑ _u ∈ W, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      exact hPoint (t - u)
    _ = (W.card : ℝ) ^ 2 * N := by simp; ring

/-- Single loss factor in the exact terminal recurrence. -/
noncomputable def heathBrownTerminalRecurrenceLoss
    (C D η T : ℝ) (P : ℕ) : ℝ :=
  C * T ^ (20 * η) * (1 + 24 * (D * (4 * P : ℝ) ^ η) ^ 2)

/-- Factored form of (29.41), convenient for the three-range induction. -/
theorem exists_heathBrownWeightedMoment_terminal_recurrence_factored
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ N → T₀ ≤ T → (2 * N : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        let P := heathBrownSourceTerminalScale T N
          (heathBrownSmoothingHeight T η)
        heathBrownWeightedMoment N W ≤
          heathBrownTerminalRecurrenceLoss C D η T P *
            ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
              heathBrownWeightedMoment P W +
              heathBrownWeightedMoment (2 * P) W + 1) := by
  obtain ⟨C, D, hC, hD, T₀, hT₀, hRec⟩ :=
    exists_heathBrownWeightedMoment_terminal_recurrence cutoff η hη hηOne
  refine ⟨C, D, hC, hD, T₀, hT₀, ?_⟩
  intro N T W hN hT hTwoNT hSep hInterval
  let P := heathBrownSourceTerminalScale T N
    (heathBrownSmoothingHeight T η)
  let A : ℝ := (W.card : ℝ) * N + (W.card : ℝ) ^ 2 + 1
  let S : ℝ := heathBrownWeightedMoment P W +
    heathBrownWeightedMoment (2 * P) W
  let B : ℝ := 24 * (D * (4 * P : ℝ) ^ η) ^ 2
  have hRaw := hRec N T W hN hT hTwoNT hSep hInterval
  have hRaw' : heathBrownWeightedMoment N W ≤
      C * T ^ (20 * η) * (A + B * S) := by
    convert hRaw using 1
    dsimp only [A, B, S, P]
    ring
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (heathBrownWeightedMoment_nonneg P W)
      (heathBrownWeightedMoment_nonneg (2 * P) W)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hInside : A + B * S ≤ (1 + B) * (A + S) := by
    nlinarith [mul_nonneg hA hB, mul_nonneg hB hS]
  have hOuter : 0 ≤ C * T ^ (20 * η) := by
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  calc
    heathBrownWeightedMoment N W ≤ C * T ^ (20 * η) * (A + B * S) := hRaw'
    _ ≤ C * T ^ (20 * η) * ((1 + B) * (A + S)) :=
      mul_le_mul_of_nonneg_left hInside hOuter
    _ = heathBrownTerminalRecurrenceLoss C D η T P *
        ((W.card : ℝ) * N + (W.card : ℝ) ^ 2 +
          heathBrownWeightedMoment P W +
          heathBrownWeightedMoment (2 * P) W + 1) := by
      dsimp only [heathBrownTerminalRecurrenceLoss, A, S, B]
      ring

/-- The complete local recurrence loss is an arbitrarily small power of
the height.  The exponent `24η` records the already proved analytic
profile (`20η`) and the squared terminal coefficient (`4η`). -/
theorem heathBrownTerminalRecurrenceLoss_le_rpow
    {C D η T : ℝ} {N : ℕ}
    (hC : 0 < C) (hη : 0 < η) (hηOne : η ≤ 1)
    (hT : 2 ≤ T) (hN : 30 ≤ N) :
    let P := heathBrownSourceTerminalScale T N
      (heathBrownSmoothingHeight T η)
    heathBrownTerminalRecurrenceLoss C D η T P ≤
      (C * (1 + 24 * D ^ 2 * 96 ^ (2 * η))) * T ^ (24 * η) := by
  let P := heathBrownSourceTerminalScale T N
    (heathBrownSmoothingHeight T η)
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hP : (P : ℝ) ≤ 24 * T ^ 2 := by
    dsimp only [P]
    exact heathBrownSourceTerminalScale_le_twenty_four_mul_sq
      hη.le hηOne hT hN rfl
  have hFourP : (4 * P : ℝ) ≤ 96 * T ^ 2 := by
    linarith
  have hRpow : (4 * P : ℝ) ^ η ≤ (96 * T ^ 2) ^ η :=
    Real.rpow_le_rpow (by positivity) hFourP hη.le
  have hIdentity : (96 * T ^ 2) ^ η = 96 ^ η * T ^ (2 * η) := by
    calc
      (96 * T ^ 2) ^ η = 96 ^ η * (T ^ 2) ^ η :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 96) (sq_nonneg T)
      _ = 96 ^ η * T ^ (2 * η) := by
        congr 1
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hTPos.le]
        norm_num
  have hSquare : ((4 * P : ℝ) ^ η) ^ 2 ≤
      96 ^ (2 * η) * T ^ (4 * η) := by
    have hnonneg : 0 ≤ (4 * P : ℝ) ^ η := Real.rpow_nonneg (by positivity) _
    have hsq := pow_le_pow_left₀ hnonneg (hRpow.trans_eq hIdentity) 2
    have h96 : ((96 : ℝ) ^ η) ^ 2 = (96 : ℝ) ^ (2 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 96)]
      congr 1
      ring
    have hTpow : (T ^ (2 * η)) ^ 2 = T ^ (4 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      congr 1
      ring
    calc
      ((4 * P : ℝ) ^ η) ^ 2 ≤ (96 ^ η * T ^ (2 * η)) ^ 2 := hsq
      _ = 96 ^ (2 * η) * T ^ (4 * η) := by
        rw [mul_pow, h96, hTpow]
  have hPowOne : 1 ≤ T ^ (4 * η) :=
    Real.one_le_rpow hTOne (by positivity)
  have hFactor :
      1 + 24 * (D * (4 * P : ℝ) ^ η) ^ 2 ≤
        (1 + 24 * D ^ 2 * 96 ^ (2 * η)) * T ^ (4 * η) := by
    have hMulSquare :
        24 * D ^ 2 * ((4 * P : ℝ) ^ η) ^ 2 ≤
          24 * D ^ 2 * (96 ^ (2 * η) * T ^ (4 * η)) :=
      mul_le_mul_of_nonneg_left hSquare
        (mul_nonneg (by norm_num) (sq_nonneg D))
    have hReplaceOne :
        1 + 24 * D ^ 2 * (96 ^ (2 * η) * T ^ (4 * η)) ≤
          T ^ (4 * η) + 24 * D ^ 2 * 96 ^ (2 * η) * T ^ (4 * η) := by
      have := add_le_add_right hPowOne
        (24 * D ^ 2 * 96 ^ (2 * η) * T ^ (4 * η))
      convert this using 1 <;> ring
    calc
      _ = 1 + 24 * D ^ 2 * ((4 * P : ℝ) ^ η) ^ 2 := by ring
      _ ≤ 1 + 24 * D ^ 2 * (96 ^ (2 * η) * T ^ (4 * η)) :=
        by simpa [add_comm] using add_le_add_right hMulSquare 1
      _ ≤ T ^ (4 * η) +
          24 * D ^ 2 * 96 ^ (2 * η) * T ^ (4 * η) := hReplaceOne
      _ = (1 + 24 * D ^ 2 * 96 ^ (2 * η)) * T ^ (4 * η) := by ring
  have hOuter : 0 ≤ C * T ^ (20 * η) := by positivity
  calc
    heathBrownTerminalRecurrenceLoss C D η T P =
        C * T ^ (20 * η) *
          (1 + 24 * (D * (4 * P : ℝ) ^ η) ^ 2) := rfl
    _ ≤ C * T ^ (20 * η) *
        ((1 + 24 * D ^ 2 * 96 ^ (2 * η)) * T ^ (4 * η)) :=
      mul_le_mul_of_nonneg_left hFactor hOuter
    _ = (C * (1 + 24 * D ^ 2 * 96 ^ (2 * η))) *
        (T ^ (20 * η) * T ^ (4 * η)) := by ring
    _ = (C * (1 + 24 * D ^ 2 * 96 ^ (2 * η))) * T ^ (24 * η) := by
      congr 1
      rw [← Real.rpow_add hTPos]
      congr 1
      ring

/-! ## Uniform source-sharp powering

The local versions above are useful during construction, but their displayed
existential constants occur after the source length.  The following theorem
chooses the divisor-bound constant first.  This quantifier order is required
when the powering lemma is iterated in the proof of Montgomery--Vaughan
Lemma 29.10. -/

/-- Uniform raw-block majorant: for fixed power and epsilon the constant is
independent of the source length, ordinate set, and dyadic block. -/
theorem exists_heathBrownRawPoweredBlockMoment_le_weighted_uniform
    (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (W : Finset ℝ), 0 < N → ∀ r < k,
        (∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
          (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
            heathBrownWeightedMoment (2 ^ r * N ^ k) W := by
  obtain ⟨C, hC, hCoeff⟩ := finitePowCoeff_bound_uniform k η hη
  refine ⟨C, hC, ?_⟩
  intro N W hN r hr
  let Q : ℕ := 2 ^ r * N ^ k
  let B : ℝ := C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hMajorant := sourceDirichletPoly_differenceMoment_le_of_norm_le
    Q W (heathBrownRawPoweredCoeffs N k)
      (fun m => B * heathBrownHalfWeight m)
    (by
      intro m hm
      exact mul_nonneg hB (heathBrownHalfWeight_nonneg m))
    (by
      intro m hm
      have hmWide := heathBrown_poweredBlock_subset N k r m hr hm
      have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp hmWide).1
      have hmUpper : m ≤ 2 ^ k * N ^ k := (Finset.mem_Ioc.mp hmWide).2
      have hPow : (m : ℝ) ^ η ≤ ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by
        exact Real.rpow_le_rpow (Nat.cast_nonneg m)
          (by exact_mod_cast hmUpper) hη.le
      have hCoeff' : ‖finitePowCoeff N k (fun _ => (1 : ℂ)) m‖ ≤ B := by
        calc
          _ ≤ C * (m : ℝ) ^ η := hCoeff N (fun _ => (1 : ℂ))
            (by intro n hn; simp) m hmPos
          _ ≤ C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η :=
            mul_le_mul_of_nonneg_left hPow hC.le
          _ = B := rfl
      unfold heathBrownRawPoweredCoeffs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heathBrownHalfWeight_nonneg m)]
      exact mul_le_mul_of_nonneg_right hCoeff'
        (heathBrownHalfWeight_nonneg m))
  have hConstant :
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly Q
            (fun m => ((B * heathBrownHalfWeight m : ℝ) : ℂ))
              (t - u)‖ ^ 2) =
        B ^ 2 * heathBrownWeightedMoment Q W := by
    unfold heathBrownWeightedMoment
    have hPoly (x : ℝ) :
        sourceDirichletPoly Q
            (fun m => ((B * heathBrownHalfWeight m : ℝ) : ℂ)) x =
          (B : ℂ) * sourceDirichletPoly Q
            (fun m => (heathBrownHalfWeight m : ℂ)) x := by
      simpa only [ofReal_mul] using sourceDirichletPoly_real_smul_coeffs
        Q heathBrownHalfWeight B x
    simp_rw [hPoly]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB, mul_pow]
  simpa only [Q, B, hConstant] using hMajorant.trans_eq hConstant

/-- Uniform common-target form of the raw-block estimate.  Both constants
are chosen before every source and terminal scale. -/
theorem exists_heathBrownRawPoweredBlockMoment_le_target_uniform
    (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N c : ℕ) (W : Finset ℝ), 0 < N → k ≤ c → ∀ r < k,
        (∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
          (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
            (4 * (D *
              (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment
                  (heathBrownPoweredTargetScale N k c) W +
                heathBrownWeightedMoment
                  (2 * heathBrownPoweredTargetScale N k c) W)) := by
  obtain ⟨C, hC, hBlock⟩ :=
    exists_heathBrownRawPoweredBlockMoment_le_weighted_uniform k η hη
  obtain ⟨D, hD, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_transfer η hη
  refine ⟨C, D, hC, hD, ?_⟩
  intro N c W hN hkc r hr
  let Q : ℕ := 2 ^ r * N ^ k
  let J : ℕ := 2 ^ (c - r)
  let P : ℕ := heathBrownPoweredTargetScale N k c
  have hrc : r ≤ c := le_trans (Nat.le_of_lt hr) hkc
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hJQ : J * Q = P := by
    simpa only [J, Q, P] using
      heathBrownPoweredBlock_mul_aux_eq_target N k c r hrc
  have hTransferred := hTransfer J Q W hJ hQ
  rw [hJQ] at hTransferred
  have hCastJQ : (J : ℝ) * (Q : ℝ) = (P : ℝ) := by exact_mod_cast hJQ
  rw [hCastJQ] at hTransferred
  have hTransferred' :
      heathBrownWeightedMoment (2 ^ r * N ^ k) W ≤
        4 * (D *
          (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment
              (heathBrownPoweredTargetScale N k c) W +
            heathBrownWeightedMoment
              (2 * heathBrownPoweredTargetScale N k c) W) := by
    simpa only [Q, P] using hTransferred
  exact (hBlock N W hN r hr).trans
    (mul_le_mul_of_nonneg_left hTransferred' (by positivity))

/-- Uniform source-sharp Montgomery--Vaughan Lemma 29.9.  The constants
depend only on the fixed power and epsilon, never on either scale or the
ordinate set. -/
theorem exists_heathBrownWeightedMoment_powering_recurrence_sharp_uniform
    (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N c : ℕ) (W : Finset ℝ), 0 < N → k ≤ c →
        heathBrownWeightedMoment N W ^ k ≤
          (((W.card : ℝ) ^ 2) ^ (k - 1)) * (k : ℝ) ^ 2 *
            (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
            (4 * (D *
              (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
              (heathBrownWeightedMoment
                  (heathBrownPoweredTargetScale N k c) W +
                heathBrownWeightedMoment
                  (2 * heathBrownPoweredTargetScale N k c) W)) := by
  obtain ⟨C, D, hC, hD, hBlock⟩ :=
    exists_heathBrownRawPoweredBlockMoment_le_target_uniform k η hη
  refine ⟨C, D, hC, hD, ?_⟩
  intro N c W hN hkc
  let P : ℕ := heathBrownPoweredTargetScale N k c
  let B : ℝ := C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η
  let E : ℝ := 4 * (D * (4 * P : ℝ) ^ η) ^ 2 *
    (heathBrownWeightedMoment P W + heathBrownWeightedMoment (2 * P) W)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (by positivity) (add_nonneg
      (heathBrownWeightedMoment_nonneg P W)
      (heathBrownWeightedMoment_nonneg (2 * P) W))
  have hHolder := heathBrownWeightedMoment_pow_le N k W hk
  have hIdentity := sum_norm_heathBrownRawPoweredWide_sq N k W hN hk
  have hBlocks := sum_norm_heathBrownRawPoweredWide_sq_le_blocks N k W
  have hUniform : ∀ r ∈ Finset.range k,
      (∑ t ∈ W, ∑ u ∈ W,
          ‖sourceDirichletPoly (2 ^ r * N ^ k)
            (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤ B ^ 2 * E := by
    intro r hr
    simpa only [B, E, P] using
      hBlock N c W hN hkc r (Finset.mem_range.mp hr)
  have hSum :
      (∑ r ∈ Finset.range k,
          ∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) ≤
        (k : ℝ) * (B ^ 2 * E) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range k, B ^ 2 * E := Finset.sum_le_sum hUniform
      _ = (k : ℝ) * (B ^ 2 * E) := by simp
  calc
    heathBrownWeightedMoment N W ^ k ≤
        (((W.card : ℝ) ^ 2) ^ (k - 1)) *
          heathBrownWeightedPowerMoment N k W := hHolder
    _ = (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        (∑ t ∈ W, ∑ u ∈ W,
          ‖wideDirichletPoly (N ^ k) k (heathBrownRawPoweredCoeffs N k)
            (-(t - u))‖ ^ 2) := by rw [hIdentity]
    _ ≤ (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        ((k : ℝ) * ∑ r ∈ Finset.range k,
          ∑ t ∈ W, ∑ u ∈ W,
            ‖sourceDirichletPoly (2 ^ r * N ^ k)
              (heathBrownRawPoweredCoeffs N k) (t - u)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hBlocks (by positivity)
    _ ≤ (((W.card : ℝ) ^ 2) ^ (k - 1)) *
        ((k : ℝ) * ((k : ℝ) * (B ^ 2 * E))) := by gcongr
    _ = (((W.card : ℝ) ^ 2) ^ (k - 1)) * (k : ℝ) ^ 2 *
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η) ^ 2 *
        (4 * (D *
          (4 * heathBrownPoweredTargetScale N k c : ℝ) ^ η) ^ 2 *
          (heathBrownWeightedMoment
              (heathBrownPoweredTargetScale N k c) W +
            heathBrownWeightedMoment
              (2 * heathBrownPoweredTargetScale N k c) W)) := by
      simp only [B, E, P]
      ring

/-- Uniform `k = c = 2` instance used when the powered scale is
`4 M²`. -/
theorem exists_heathBrownWeightedMoment_sq_le_four_mul_sq_sharp_uniform
    (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ, 0 < E ∧ ∀ (M : ℕ) (W : Finset ℝ), 0 < M →
      heathBrownWeightedMoment M W ^ 2 ≤
        E * ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          ((16 * (M : ℝ) ^ 2) ^ η) ^ 2 *
          (W.card : ℝ) ^ 2 *
          (heathBrownWeightedMoment (4 * M ^ 2) W +
            heathBrownWeightedMoment (8 * M ^ 2) W) := by
  obtain ⟨C, D, hC, hD, hRec⟩ :=
    exists_heathBrownWeightedMoment_powering_recurrence_sharp_uniform
      2 (by omega) η hη
  refine ⟨16 * C ^ 2 * D ^ 2, by positivity, ?_⟩
  intro M W hM
  have h := hRec M 2 W hM (by omega)
  norm_num [heathBrownPoweredTargetScale, Nat.cast_pow,
    Nat.cast_mul] at h ⊢
  convert h using 1
  all_goals ring_nf

/-- The adjacent dyadic pair which is invariant under the exact source
powering return. -/
noncomputable def heathBrownDyadicPairMoment
    (q : ℕ) (W : Finset ℝ) : ℝ :=
  heathBrownWeightedMoment (2 ^ q) W +
    heathBrownWeightedMoment (2 ^ (q + 1)) W

/-- Uniform `k=2` return from a dyadic child scale to a prescribed dyadic
parent.  This is the exact formal counterpart of taking `P=N` in
Montgomery--Vaughan Lemma 29.9. -/
theorem exists_heathBrownWeightedMoment_sq_le_dyadic_parent_uniform
    (η : ℝ) (hη : 0 < η) :
    ∃ E : ℝ, 0 < E ∧ ∀ (p q : ℕ) (W : Finset ℝ),
      2 * p + 2 ≤ q →
      heathBrownWeightedMoment (2 ^ p) W ^ 2 ≤
        E * ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 *
          (W.card : ℝ) ^ 2 * heathBrownDyadicPairMoment q W := by
  obtain ⟨C, D, hC, hD, hRec⟩ :=
    exists_heathBrownWeightedMoment_powering_recurrence_sharp_uniform
      2 (by omega) η hη
  refine ⟨16 * C ^ 2 * D ^ 2, by positivity, ?_⟩
  intro p q W hpq
  let c : ℕ := q - 2 * p
  have hc : 2 ≤ c := by dsimp only [c]; omega
  have hP : 0 < 2 ^ p := by positivity
  have hTarget : heathBrownPoweredTargetScale (2 ^ p) 2 c = 2 ^ q := by
    dsimp only [heathBrownPoweredTargetScale, c]
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hRaw := hRec (2 ^ p) c W hP hc
  rw [hTarget] at hRaw
  have hScaleNat : (2 ^ p) ^ 2 ≤ 2 ^ q := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hScale : (4 * ((2 ^ p : ℕ) : ℝ) ^ 2) ≤
      (4 * (2 ^ q : ℕ) : ℝ) := by
    push_cast
    exact_mod_cast Nat.mul_le_mul_left 4 hScaleNat
  have hRpow :
      (4 * ((2 ^ p : ℕ) : ℝ) ^ 2) ^ η ≤
        (4 * (2 ^ q : ℕ) : ℝ) ^ η :=
    Real.rpow_le_rpow (by positivity) hScale hη.le
  have hMoment : 0 ≤ heathBrownDyadicPairMoment q W := by
    unfold heathBrownDyadicPairMoment
    exact add_nonneg (heathBrownWeightedMoment_nonneg (2 ^ q) W)
      (heathBrownWeightedMoment_nonneg (2 ^ (q + 1)) W)
  have hFactor :
      ((4 * ((2 ^ p : ℕ) : ℝ) ^ 2) ^ η) ^ 2 *
          ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 2 ≤
        ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 := by
    calc
      _ ≤ ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 2 *
          ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 2 := by gcongr
      _ = _ := by ring
  have hFactor' :
      (((4 : ℝ) * (2 : ℝ) ^ (p * 2)) ^ η) ^ 2 *
          (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 2 ≤
        (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 4 := by
    norm_num [Nat.cast_pow, Nat.cast_mul] at hFactor
    simpa only [pow_mul] using hFactor
  norm_num [Nat.cast_pow, Nat.cast_mul, heathBrownDyadicPairMoment] at hRaw ⊢
  calc
    heathBrownWeightedMoment (2 ^ p) W ^ 2 ≤
        16 * C ^ 2 * D ^ 2 *
          (((4 : ℝ) * (2 : ℝ) ^ (p * 2)) ^ η) ^ 2 *
          (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 2 *
          (W.card : ℝ) ^ 2 *
          (heathBrownWeightedMoment (2 ^ q) W +
            heathBrownWeightedMoment (2 ^ (q + 1)) W) := by
      ring_nf at hRaw ⊢
      exact hRaw
    _ ≤ 16 * C ^ 2 * D ^ 2 *
          (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 4 *
          (W.card : ℝ) ^ 2 *
          (heathBrownWeightedMoment (2 ^ q) W +
            heathBrownWeightedMoment (2 ^ (q + 1)) W) := by
      have hNonneg : 0 ≤
          16 * C ^ 2 * D ^ 2 * (W.card : ℝ) ^ 2 *
            (heathBrownWeightedMoment (2 ^ q) W +
              heathBrownWeightedMoment (2 ^ (q + 1)) W) := by
        positivity
      calc
        _ = (16 * C ^ 2 * D ^ 2 * (W.card : ℝ) ^ 2 *
              (heathBrownWeightedMoment (2 ^ q) W +
                heathBrownWeightedMoment (2 ^ (q + 1)) W)) *
              ((((4 : ℝ) * (2 : ℝ) ^ (p * 2)) ^ η) ^ 2 *
                (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 2) := by ring
        _ ≤ (16 * C ^ 2 * D ^ 2 * (W.card : ℝ) ^ 2 *
              (heathBrownWeightedMoment (2 ^ q) W +
                heathBrownWeightedMoment (2 ^ (q + 1)) W)) *
              (((4 : ℝ) * (2 : ℝ) ^ q) ^ η) ^ 4 :=
          mul_le_mul_of_nonneg_left hFactor' hNonneg
        _ = _ := by ring
    _ = _ := by ring

/-- Matching lower bound for the common six-child terminal.  Together with
`heathBrownSourceTerminalScale_le_physical`, this pins the rounded dyadic
scale to the physical dual length rather than merely bounding it above. -/
theorem two_mul_floor_mul_height_div_le_heathBrownSourceTerminalScale
    {T : ℝ} {N H : ℕ} (hT : 1 ≤ T) (hN : 30 ≤ N) (hH : 0 < H) :
    2 * ((Nat.floor T : ℝ) * H / N) ≤
      (heathBrownSourceTerminalScale T N H : ℝ) := by
  let e : ℕ := heathBrownCorrectedCommonExponent N H T
  let c : ℕ := heathBrownSourceTerminalExponent T N H
  have hNPos : 0 < N := by omega
  have hTarget := (heathBrownReflectionTargetScale_bounds_real
    N H T hNPos hH hT).1
  have hec : e ≤ c := by
    have hAll :=
      (heathBrown_source_exponent_succ_le_terminal T N H).2.1
    change e + 1 ≤ c at hAll
    omega
  have hScaleNat : 2 ^ e ≤ 2 ^ c :=
    Nat.pow_le_pow_right (by omega) hec
  have hScaleReal :
      (heathBrownCorrectedCommonScale N H T : ℝ) ≤
        (heathBrownSourceTerminalScale T N H : ℝ) := by
    exact_mod_cast hScaleNat
  calc
    2 * ((Nat.floor T : ℝ) * H / N) ≤
        2 * (heathBrownReflectionTargetScale N H T : ℝ) := by gcongr
    _ = (heathBrownCorrectedCommonScale N H T : ℝ) := by
      rw [heathBrownCorrectedCommonScale_eq_two_mul_target]
      push_cast
      rfl
    _ ≤ (heathBrownSourceTerminalScale T N H : ℝ) := hScaleReal

/-- The four reflected moments produced by applying (29.41) at two
adjacent dyadic parent scales. -/
noncomputable def heathBrownDyadicChildPackage
    (η T : ℝ) (q : ℕ) (W : Finset ℝ) : ℝ :=
  let H := heathBrownSmoothingHeight T η
  let P₀ := heathBrownSourceTerminalScale T (2 ^ q) H
  let P₁ := heathBrownSourceTerminalScale T (2 ^ (q + 1)) H
  heathBrownWeightedMoment P₀ W + heathBrownWeightedMoment (2 * P₀) W +
    heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W

theorem add_four_sq_le_four_mul_sum_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Quadratic absorption used in the high-scale case of Montgomery--Vaughan
Lemma 29.10.  It is the algebraic content of solving the recurrence after
the `k = 2` powering estimate has returned the reflected child to its
parent. -/
theorem le_two_mul_add_of_le_mul_add_of_sq_le_mul
    {X A L B S : ℝ} (hX₀ : 0 ≤ X) (hL₀ : 0 ≤ L) (hB₀ : 0 ≤ B)
    (hS₀ : 0 ≤ S) (hRec : X ≤ L * (A + S)) (hPow : S ^ 2 ≤ B * X) :
    X ≤ 2 * L * A + 2 * L ^ 2 * B := by
  have hLS : 2 * L * S ≤ X + L ^ 2 * B := by
    have hSquared : (2 * L * S) ^ 2 ≤ (X + L ^ 2 * B) ^ 2 := by
      calc
        (2 * L * S) ^ 2 = 4 * L ^ 2 * S ^ 2 := by ring
        _ ≤ 4 * L ^ 2 * (B * X) := by gcongr
        _ ≤ (X + L ^ 2 * B) ^ 2 := by
          nlinarith [sq_nonneg (X - L ^ 2 * B)]
    have hLeft : 0 ≤ 2 * L * S := by positivity
    have hRight : 0 ≤ X + L ^ 2 * B := by positivity
    nlinarith
  nlinarith [hRec, hLS]

/-- Exact exponent extraction behind the high-scale cutoff: the physical
inequality `16 (2^p)^2 ≤ 2^q` is equivalent to having four spare dyadic
powers after doubling the child exponent. -/
theorem two_mul_add_four_le_of_sixteen_mul_sq_le_pow
    {p q : ℕ} (h : 16 * (2 ^ p) ^ 2 ≤ 2 ^ q) :
    2 * p + 4 ≤ q := by
  by_contra hNot
  have hExp : q < 2 * p + 4 := Nat.lt_of_not_ge hNot
  have hPow : 2 ^ q < 2 ^ (2 * p + 4) :=
    (Nat.pow_lt_pow_iff_right (by omega)).2 hExp
  have hIdentity : 2 ^ (2 * p + 4) = 16 * (2 ^ p) ^ 2 := by
    calc
      2 ^ (2 * p + 4) = 2 ^ (p + p + 4) := by congr 1; omega
      _ = 2 ^ p * 2 ^ p * 2 ^ 4 := by rw [pow_add, pow_add]
      _ = 16 * (2 ^ p) ^ 2 := by norm_num; ring
  rw [hIdentity] at hPow
  omega

/-- Exact dyadic self-recurrence underlying the first part of
Montgomery--Vaughan Lemma 29.10.  The exponent hypotheses say precisely
that both reflected terminal pairs can be powered back to the displayed
parent pair. -/
theorem exists_heathBrownDyadicPairMoment_self_recurrence
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ K E T₀ : ℝ, 0 < K ∧ 0 < E ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        let p₀ := heathBrownSourceTerminalExponent T (2 ^ q)
          (heathBrownSmoothingHeight T η)
        let p₁ := heathBrownSourceTerminalExponent T (2 ^ (q + 1))
          (heathBrownSmoothingHeight T η)
        2 * p₀ + 4 ≤ q → 2 * p₁ + 4 ≤ q →
        heathBrownDyadicPairMoment q W ≤
          K * T ^ (24 * η) *
            (3 * (W.card : ℝ) * (2 ^ q : ℕ) +
              2 * (W.card : ℝ) ^ 2 +
              heathBrownDyadicChildPackage η T q W + 2) ∧
        heathBrownDyadicChildPackage η T q W ^ 2 ≤
          16 * E * ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 *
            (W.card : ℝ) ^ 2 * heathBrownDyadicPairMoment q W := by
  obtain ⟨C, D, hC, hD, T₀, hT₀, hRec⟩ :=
    exists_heathBrownWeightedMoment_terminal_recurrence_factored
      cutoff η hη hηOne
  obtain ⟨E, hE, hPower⟩ :=
    exists_heathBrownWeightedMoment_sq_le_dyadic_parent_uniform η hη
  let K : ℝ := C * (1 + 24 * D ^ 2 * 96 ^ (2 * η))
  refine ⟨K, E, T₀, by dsimp only [K]; positivity, hE, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase
  dsimp only
  let Q : ℕ := 2 ^ q
  let Q₁ : ℕ := 2 ^ (q + 1)
  let H : ℕ := heathBrownSmoothingHeight T η
  let p₀ : ℕ := heathBrownSourceTerminalExponent T Q H
  let p₁ : ℕ := heathBrownSourceTerminalExponent T Q₁ H
  let P₀ : ℕ := 2 ^ p₀
  let P₁ : ℕ := 2 ^ p₁
  intro hp₀ hp₁
  change 2 * p₀ + 4 ≤ q at hp₀
  change 2 * p₁ + 4 ≤ q at hp₁
  have hTTwo : 2 ≤ T := hT₀.trans hT
  have hQ30 : 30 ≤ Q := by simpa only [Q] using hQ
  have hQ₁eq : Q₁ = 2 * Q := by
    dsimp only [Q₁, Q]
    rw [pow_succ]
    ring
  have hQ₁30 : 30 ≤ Q₁ := by rw [hQ₁eq]; omega
  have hFour : (((4 * Q : ℕ) : ℝ)) ≤ T := by simpa only [Q] using hFourQ
  have h2Q : (((2 * Q : ℕ) : ℝ)) ≤ T := by
    have hCast : (((2 * Q : ℕ) : ℝ)) ≤ ((4 * Q : ℕ) : ℝ) := by
      exact_mod_cast (show (2 * Q : ℕ) ≤ 4 * Q by omega)
    exact hCast.trans hFour
  have h2Q₁ : (((2 * Q₁ : ℕ) : ℝ)) ≤ T := by
    calc
      (((2 * Q₁ : ℕ) : ℝ)) = (((4 * Q : ℕ) : ℝ)) := by
        rw [hQ₁eq]
        norm_num
        ring
      _ ≤ T := hFour
  have hRec₀ := hRec Q T W hQ30 hT h2Q hSep hBase
  have hRec₁ := hRec Q₁ T W hQ₁30 hT h2Q₁ hSep hBase
  have hLoss₀ := heathBrownTerminalRecurrenceLoss_le_rpow
    (C := C) (D := D) (η := η) (T := T) (N := Q)
    hC hη hηOne hTTwo hQ30
  have hLoss₁ := heathBrownTerminalRecurrenceLoss_le_rpow
    (C := C) (D := D) (η := η) (T := T) (N := Q₁)
    hC hη hηOne hTTwo hQ₁30
  change heathBrownWeightedMoment Q W ≤
    heathBrownTerminalRecurrenceLoss C D η T P₀ *
      ((W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₀ W +
        heathBrownWeightedMoment (2 * P₀) W + 1) at hRec₀
  change heathBrownWeightedMoment Q₁ W ≤
    heathBrownTerminalRecurrenceLoss C D η T P₁ *
      ((W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₁ W +
        heathBrownWeightedMoment (2 * P₁) W + 1) at hRec₁
  change heathBrownTerminalRecurrenceLoss C D η T P₀ ≤
    K * T ^ (24 * η) at hLoss₀
  change heathBrownTerminalRecurrenceLoss C D η T P₁ ≤
    K * T ^ (24 * η) at hLoss₁
  have hPackage : heathBrownDyadicChildPackage η T q W =
      heathBrownWeightedMoment P₀ W +
        heathBrownWeightedMoment (2 * P₀) W +
        heathBrownWeightedMoment P₁ W +
        heathBrownWeightedMoment (2 * P₁) W := by rfl
  have hFirst : heathBrownDyadicPairMoment q W ≤
      K * T ^ (24 * η) *
        (3 * (W.card : ℝ) * (Q : ℝ) + 2 * (W.card : ℝ) ^ 2 +
          heathBrownDyadicChildPackage η T q W + 2) := by
    have hInside₀ : 0 ≤
        (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
          heathBrownWeightedMoment P₀ W +
          heathBrownWeightedMoment (2 * P₀) W + 1 := by
      have h₀ := heathBrownWeightedMoment_nonneg P₀ W
      have h₁ := heathBrownWeightedMoment_nonneg (2 * P₀) W
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (sq_nonneg (W.card : ℝ))) h₀) h₁) zero_le_one
    have hInside₁ : 0 ≤
        (W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
          heathBrownWeightedMoment P₁ W +
          heathBrownWeightedMoment (2 * P₁) W + 1 := by
      have h₀ := heathBrownWeightedMoment_nonneg P₁ W
      have h₁ := heathBrownWeightedMoment_nonneg (2 * P₁) W
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (sq_nonneg (W.card : ℝ))) h₀) h₁) zero_le_one
    have hBound₀ : heathBrownWeightedMoment Q W ≤
        K * T ^ (24 * η) *
          ((W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
            heathBrownWeightedMoment P₀ W +
            heathBrownWeightedMoment (2 * P₀) W + 1) :=
      hRec₀.trans (mul_le_mul_of_nonneg_right hLoss₀ hInside₀)
    have hBound₁ : heathBrownWeightedMoment Q₁ W ≤
        K * T ^ (24 * η) *
          ((W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
            heathBrownWeightedMoment P₁ W +
            heathBrownWeightedMoment (2 * P₁) W + 1) :=
      hRec₁.trans (mul_le_mul_of_nonneg_right hLoss₁ hInside₁)
    unfold heathBrownDyadicPairMoment
    rw [show 2 ^ (q + 1) = Q₁ by rfl]
    calc
      _ ≤ K * T ^ (24 * η) *
            ((W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
              heathBrownWeightedMoment P₀ W +
              heathBrownWeightedMoment (2 * P₀) W + 1) +
          K * T ^ (24 * η) *
            ((W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
              heathBrownWeightedMoment P₁ W +
              heathBrownWeightedMoment (2 * P₁) W + 1) :=
        add_le_add hBound₀ hBound₁
      _ = K * T ^ (24 * η) *
          (3 * (W.card : ℝ) * (Q : ℝ) + 2 * (W.card : ℝ) ^ 2 +
            heathBrownDyadicChildPackage η T q W + 2) := by
        rw [hPackage, hQ₁eq]
        push_cast
        ring
  have hPow₀ := hPower p₀ q W (by omega)
  have hPow₀' := hPower (p₀ + 1) q W (by omega)
  have hPow₁ := hPower p₁ q W (by omega)
  have hPow₁' := hPower (p₁ + 1) q W (by omega)
  have hTwoP₀ : 2 * P₀ = 2 ^ (p₀ + 1) := by
    dsimp only [P₀]
    rw [pow_succ]
    ring
  have hTwoP₁ : 2 * P₁ = 2 ^ (p₁ + 1) := by
    dsimp only [P₁]
    rw [pow_succ]
    ring
  rw [← hTwoP₀] at hPow₀'
  rw [← hTwoP₁] at hPow₁'
  let A : ℝ := E * ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 *
    (W.card : ℝ) ^ 2 * heathBrownDyadicPairMoment q W
  have hPow₀P : heathBrownWeightedMoment P₀ W ^ 2 ≤
      A := by
    dsimp only [A]
    simpa only [P₀] using hPow₀
  have hPow₁P : heathBrownWeightedMoment P₁ W ^ 2 ≤
      A := by
    dsimp only [A]
    simpa only [P₁] using hPow₁
  change heathBrownWeightedMoment (2 * P₀) W ^ 2 ≤ A at hPow₀'
  change heathBrownWeightedMoment (2 * P₁) W ^ 2 ≤ A at hPow₁'
  have hCS : heathBrownDyadicChildPackage η T q W ^ 2 ≤
      4 * (heathBrownWeightedMoment P₀ W ^ 2 +
        heathBrownWeightedMoment (2 * P₀) W ^ 2 +
        heathBrownWeightedMoment P₁ W ^ 2 +
        heathBrownWeightedMoment (2 * P₁) W ^ 2) := by
    rw [hPackage]
    exact add_four_sq_le_four_mul_sum_sq
      (heathBrownWeightedMoment P₀ W)
      (heathBrownWeightedMoment (2 * P₀) W)
      (heathBrownWeightedMoment P₁ W)
      (heathBrownWeightedMoment (2 * P₁) W)
  have hSumSquares :
      heathBrownWeightedMoment P₀ W ^ 2 +
          heathBrownWeightedMoment (2 * P₀) W ^ 2 +
          heathBrownWeightedMoment P₁ W ^ 2 +
          heathBrownWeightedMoment (2 * P₁) W ^ 2 ≤
        4 * A := by
    linarith [hPow₀P, hPow₀', hPow₁P, hPow₁']
  refine ⟨?_, ?_⟩
  · simpa only [Q] using hFirst
  · calc
      _ ≤ 4 * (4 * A) := hCS.trans (mul_le_mul_of_nonneg_left hSumSquares (by norm_num))
      _ = _ := by dsimp only [A]; ring

/-- High-scale conclusion of Montgomery--Vaughan Lemma 29.10 for an
adjacent dyadic pair.  The hypotheses are exactly the two terminal-exponent
conditions needed to return every reflected child by the source-sharp
`k = 2` powering lemma. -/
theorem exists_heathBrownDyadicPairMoment_high_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        let p₀ := heathBrownSourceTerminalExponent T (2 ^ q)
          (heathBrownSmoothingHeight T η)
        let p₁ := heathBrownSourceTerminalExponent T (2 ^ (q + 1))
          (heathBrownSmoothingHeight T η)
        2 * p₀ + 4 ≤ q → 2 * p₁ + 4 ≤ q →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨K, E, T₀, hK, hE, hT₀, hPair⟩ :=
    exists_heathBrownDyadicPairMoment_self_recurrence cutoff η hη hηOne
  let C : ℝ := 6 * K + 32 * K ^ 2 * E
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase
  dsimp only
  intro hp₀ hp₁
  obtain ⟨hRec, hPow⟩ := hPair q T W hQ hT hFourQ hSep hBase hp₀ hp₁
  let X : ℝ := heathBrownDyadicPairMoment q W
  let S : ℝ := heathBrownDyadicChildPackage η T q W
  let L : ℝ := K * T ^ (24 * η)
  let B : ℝ := 16 * E * ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 *
    (W.card : ℝ) ^ 2
  let A : ℝ := 3 * (W.card : ℝ) * (2 ^ q : ℕ) +
    2 * (W.card : ℝ) ^ 2 + 2
  let G : ℝ := (W.card : ℝ) * (2 ^ q : ℕ) +
    (W.card : ℝ) ^ 2 + 1
  have hTTwo : 2 ≤ T := hT₀.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hX₀ : 0 ≤ X := by
    dsimp only [X, heathBrownDyadicPairMoment]
    exact add_nonneg (heathBrownWeightedMoment_nonneg (2 ^ q) W)
      (heathBrownWeightedMoment_nonneg (2 ^ (q + 1)) W)
  have hS₀ : 0 ≤ S := by
    dsimp only [S, heathBrownDyadicChildPackage]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (heathBrownWeightedMoment_nonneg
            (heathBrownSourceTerminalScale T (2 ^ q)
              (heathBrownSmoothingHeight T η)) W)
          (heathBrownWeightedMoment_nonneg
            (2 * heathBrownSourceTerminalScale T (2 ^ q)
              (heathBrownSmoothingHeight T η)) W))
        (heathBrownWeightedMoment_nonneg
          (heathBrownSourceTerminalScale T (2 ^ (q + 1))
            (heathBrownSmoothingHeight T η)) W))
      (heathBrownWeightedMoment_nonneg
        (2 * heathBrownSourceTerminalScale T (2 ^ (q + 1))
          (heathBrownSmoothingHeight T η)) W)
  have hL₀ : 0 ≤ L := by dsimp only [L]; positivity
  have hB₀ : 0 ≤ B := by dsimp only [B]; positivity
  have hRec' : X ≤ L * (A + S) := by
    change X ≤ L *
      (3 * (W.card : ℝ) * (2 ^ q : ℕ) + 2 * (W.card : ℝ) ^ 2 + S + 2) at hRec
    calc
      X ≤ L *
          (3 * (W.card : ℝ) * (2 ^ q : ℕ) + 2 * (W.card : ℝ) ^ 2 + S + 2) := hRec
      _ = L * (A + S) := by dsimp only [A]; ring
  have hPow' : S ^ 2 ≤ B * X := by
    simpa only [S, B, X] using hPow
  have hAbsorb : X ≤ 2 * L * A + 2 * L ^ 2 * B :=
    le_two_mul_add_of_le_mul_add_of_sq_le_mul hX₀ hL₀ hB₀ hS₀ hRec' hPow'
  have hA : A ≤ 3 * G := by
    dsimp only [A, G]
    nlinarith [sq_nonneg (W.card : ℝ)]
  have hFourReal : (4 : ℝ) * (2 ^ q : ℕ) ≤ T := by
    have h := hFourQ
    norm_num [Nat.cast_pow, Nat.cast_mul] at h ⊢
    exact h
  have hScale : ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ≤ T ^ η := by
    exact Real.rpow_le_rpow (by positivity) hFourReal hη.le
  have hScaleFour : ((4 * (2 ^ q : ℕ) : ℝ) ^ η) ^ 4 ≤
      (T ^ η) ^ 4 := by gcongr
  have hB : B ≤ 16 * E * (T ^ η) ^ 4 * (W.card : ℝ) ^ 2 := by
    dsimp only [B]
    gcongr
  have hExponent : 24 * η ≤ 52 * η := by nlinarith
  have hTwentyFour : T ^ (24 * η) ≤ T ^ (52 * η) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hPowerIdentity : (T ^ (24 * η)) ^ 2 * (T ^ η) ^ 4 =
      T ^ (52 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hTPos.le,
      ← Real.rpow_add hTPos]
    congr 1
    norm_num
    ring
  have hG₀ : 0 ≤ G := by dsimp only [G]; positivity
  have hCardSqG : (W.card : ℝ) ^ 2 ≤ G := by
    dsimp only [G]
    have hRQ : 0 ≤ (W.card : ℝ) * (2 ^ q : ℕ) := by positivity
    nlinarith
  have hTerm₁ : 2 * L * A ≤ 6 * K * T ^ (52 * η) * G := by
    calc
      2 * L * A ≤ 2 * L * (3 * G) := by gcongr
      _ = 6 * K * T ^ (24 * η) * G := by dsimp only [L]; ring
      _ ≤ 6 * K * T ^ (52 * η) * G := by gcongr
  have hTerm₂ : 2 * L ^ 2 * B ≤
      32 * K ^ 2 * E * T ^ (52 * η) * G := by
    calc
      2 * L ^ 2 * B ≤
          2 * L ^ 2 * (16 * E * (T ^ η) ^ 4 * (W.card : ℝ) ^ 2) := by
        gcongr
      _ = 32 * K ^ 2 * E *
          ((T ^ (24 * η)) ^ 2 * (T ^ η) ^ 4) * (W.card : ℝ) ^ 2 := by
        dsimp only [L]
        ring
      _ = 32 * K ^ 2 * E * T ^ (52 * η) * (W.card : ℝ) ^ 2 := by
        rw [hPowerIdentity]
      _ ≤ 32 * K ^ 2 * E * T ^ (52 * η) * G := by gcongr
  calc
    heathBrownDyadicPairMoment q W = X := rfl
    _ ≤ 2 * L * A + 2 * L ^ 2 * B := hAbsorb
    _ ≤ 6 * K * T ^ (52 * η) * G +
        32 * K ^ 2 * E * T ^ (52 * η) * G := add_le_add hTerm₁ hTerm₂
    _ = C * T ^ (52 * η) * G := by dsimp only [C]; ring
    _ = C * T ^ (52 * η) *
        ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := rfl

/-- High-scale dyadic bound with the exponent hypotheses replaced by their
physical terminal-scale inequalities.  This is the interface consumed by
the three-range argument. -/
theorem exists_heathBrownDyadicPairMoment_high_bound_of_terminal_sq
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        let P₀ := heathBrownSourceTerminalScale T (2 ^ q)
          (heathBrownSmoothingHeight T η)
        let P₁ := heathBrownSourceTerminalScale T (2 ^ (q + 1))
          (heathBrownSmoothingHeight T η)
        16 * P₀ ^ 2 ≤ 2 ^ q → 16 * P₁ ^ 2 ≤ 2 ^ q →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨C, T₀, hC, hT₀, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound cutoff η hη hηOne
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase
  dsimp only
  intro hP₀ hP₁
  apply hHigh q T W hQ hT hFourQ hSep hBase
  · apply two_mul_add_four_le_of_sixteen_mul_sq_le_pow
    simpa only [heathBrownSourceTerminalScale] using hP₀
  · apply two_mul_add_four_le_of_sixteen_mul_sq_le_pow
    simpa only [heathBrownSourceTerminalScale] using hP₁

/-- The physical reflected-length inequality implies the exact natural
terminal-square condition used by the dyadic high-scale theorem.  The target
`R` is kept separate from the source scale `N`; this is needed for the
adjacent source `2Q`, whose powered child is returned to the same parent
`Q`. -/
theorem heathBrownSourceTerminal_sixteen_sq_le_of_physical
    {T : ℝ} {N H R : ℕ} (hT : 1 ≤ T) (hN : 30 ≤ N) (hH : 0 < H)
    (hPhysical : 4096 * (T * H / N + 1) ^ 2 ≤ (R : ℝ)) :
    16 * (heathBrownSourceTerminalScale T N H) ^ 2 ≤ R := by
  let P : ℕ := heathBrownSourceTerminalScale T N H
  let Y : ℝ := T * H / N + 1
  have hP : (P : ℝ) ≤ 16 * Y := by
    simpa only [P, Y] using heathBrownSourceTerminalScale_le_physical hT hN hH
  have hT₀ : 0 ≤ T := by linarith
  have hY₀ : 0 ≤ Y := by
    dsimp only [Y]
    positivity
  have hP₀ : (0 : ℝ) ≤ P := by positivity
  have hSquare : (P : ℝ) ^ 2 ≤ (16 * Y) ^ 2 :=
    (sq_le_sq₀ hP₀ (mul_nonneg (by norm_num) hY₀)).2 hP
  have hReal : ((16 * P ^ 2 : ℕ) : ℝ) ≤ (R : ℝ) := by
    calc
      ((16 * P ^ 2 : ℕ) : ℝ) = 16 * (P : ℝ) ^ 2 := by push_cast; ring
      _ ≤ 16 * (16 * Y) ^ 2 := by gcongr
      _ = 4096 * Y ^ 2 := by ring
      _ ≤ (R : ℝ) := by simpa only [Y] using hPhysical
  exact_mod_cast hReal

/-- Source-form high range of Montgomery--Vaughan Lemma 29.10.  The single
physical inequality controls both adjacent reflected terminal scales. -/
theorem exists_heathBrownDyadicPairMoment_high_bound_physical
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        4096 *
            (T * heathBrownSmoothingHeight T η / (2 ^ q : ℕ) + 1) ^ 2 ≤
          (2 ^ q : ℕ) →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨C, T₀, hC, hT₀, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound_of_terminal_sq
      cutoff η hη hηOne
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase hPhysical
  let Q : ℕ := 2 ^ q
  let H : ℕ := heathBrownSmoothingHeight T η
  have hTOne : 1 ≤ T := by linarith [hT₀.trans hT]
  have hQ30 : 30 ≤ Q := by simpa only [Q] using hQ
  have hQ₀ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hH : 0 < H := by
    dsimp only [H]
    exact heathBrownSmoothingHeight_pos T η
  have hP₀ : 16 * (heathBrownSourceTerminalScale T Q H) ^ 2 ≤ Q :=
    heathBrownSourceTerminal_sixteen_sq_le_of_physical hTOne hQ30 hH
      (by simpa only [Q, H] using hPhysical)
  have hNumerator : 0 ≤ T * (H : ℝ) := by positivity
  have hDenominator : (Q : ℝ) ≤ (2 * Q : ℕ) := by
    exact_mod_cast (show Q ≤ 2 * Q by omega)
  have hDiv : T * H / (2 * Q : ℕ) ≤ T * H / Q :=
    div_le_div_of_nonneg_left hNumerator hQ₀ hDenominator
  have hLeft₀ : 0 ≤ T * H / (2 * Q : ℕ) + 1 := by positivity
  have hRight₀ : 0 ≤ T * H / Q + 1 := by positivity
  have hSquare : (T * H / (2 * Q : ℕ) + 1) ^ 2 ≤
      (T * H / Q + 1) ^ 2 :=
    (sq_le_sq₀ hLeft₀ hRight₀).2 (by linarith)
  have hPhysical₁ : 4096 * (T * H / (2 * Q : ℕ) + 1) ^ 2 ≤ (Q : ℝ) :=
    (mul_le_mul_of_nonneg_left hSquare (by norm_num)).trans
      (by simpa only [Q, H] using hPhysical)
  have hP₁ : 16 * (heathBrownSourceTerminalScale T (2 * Q) H) ^ 2 ≤ Q :=
    heathBrownSourceTerminal_sixteen_sq_le_of_physical hTOne (by omega) hH hPhysical₁
  apply hHigh q T W hQ hT hFourQ hSep hBase
  · simpa only [Q, H] using hP₀
  · have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
      dsimp only [Q]
      rw [pow_succ]
      ring
    rw [hTwoQ]
    simpa only [H] using hP₁

/-- Cubic high-range arithmetic from Montgomery--Vaughan Lemma 29.10.  The
The constant is explicit and the smoothing height is still the actual rounded
natural used by the reflection theorem. -/
theorem heathBrown_high_physical_of_cube
    {η T : ℝ} {Q : ℕ} (hT : 1 ≤ T) (hQ : 0 < Q)
    (hQT : (Q : ℝ) ≤ T)
    (hCube : 16384 *
        (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 ≤ (Q : ℝ) ^ 3) :
    4096 *
        (T * heathBrownSmoothingHeight T η / Q + 1) ^ 2 ≤ (Q : ℝ) := by
  let H : ℕ := heathBrownSmoothingHeight T η
  let X : ℝ := T * H / Q
  have hQ₀ : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHOne : (1 : ℝ) ≤ H := by
    have hHNat : 1 ≤ H := by
      dsimp only [H]
      exact heathBrownSmoothingHeight_pos T η
    exact_mod_cast hHNat
  have hTH : (Q : ℝ) ≤ T * H := by
    calc
      (Q : ℝ) ≤ T := hQT
      _ ≤ T * H := by nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.2 hHOne)]
  have hXOne : 1 ≤ X := by
    dsimp only [X]
    exact (le_div_iff₀ hQ₀).2 (by simpa using hTH)
  have hX₀ : 0 ≤ X := zero_le_one.trans hXOne
  have hY : X + 1 ≤ 2 * X := by linarith
  have hYSquare : (X + 1) ^ 2 ≤ (2 * X) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hY
  have hCube' : 16384 * (T * (H : ℝ)) ^ 2 ≤ (Q : ℝ) ^ 3 := by
    simpa only [H] using hCube
  have hQuotient : 16384 * X ^ 2 ≤ (Q : ℝ) := by
    have hNumerator : 16384 * (T * (H : ℝ)) ^ 2 ≤
        (Q : ℝ) * (Q : ℝ) ^ 2 := by
      convert hCube' using 1
      ring
    have hDivided :
        (16384 * (T * (H : ℝ)) ^ 2) / (Q : ℝ) ^ 2 ≤ (Q : ℝ) :=
      (div_le_iff₀ (sq_pos_of_pos hQ₀)).2 (by
        simpa only [mul_assoc] using hNumerator)
    calc
      16384 * X ^ 2 =
          (16384 * (T * (H : ℝ)) ^ 2) / (Q : ℝ) ^ 2 := by
        dsimp only [X]
        field_simp
      _ ≤ (Q : ℝ) := hDivided
  calc
    4096 * (T * heathBrownSmoothingHeight T η / Q + 1) ^ 2 =
        4096 * (X + 1) ^ 2 := by rfl
    _ ≤ 4096 * (2 * X) ^ 2 := by gcongr
    _ = 16384 * X ^ 2 := by ring
    _ ≤ (Q : ℝ) := hQuotient

/-- High-range dyadic estimate with the source's cubic scale condition as
its only terminal-size hypothesis. -/
theorem exists_heathBrownDyadicPairMoment_high_bound_cube
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        16384 *
            (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 ≤
          ((2 ^ q : ℕ) : ℝ) ^ 3 →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨C, T₀, hC, hT₀, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound_physical cutoff η hη hηOne
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase hCube
  have hTOne : 1 ≤ T := by linarith [hT₀.trans hT]
  have hQPos : 0 < 2 ^ q := by positivity
  have hQT : ((2 ^ q : ℕ) : ℝ) ≤ T := by
    have h := hFourQ
    norm_num [Nat.cast_pow, Nat.cast_mul] at h ⊢
    linarith
  exact hHigh q T W hQ hT hFourQ hSep hBase
    (heathBrown_high_physical_of_cube hTOne hQPos hQT hCube)

/-- Complete high-range pair estimate.  Below height the reflected
recurrence and powered return are used; once `4Q > T`, the direct
Montgomery mean value is already of the required `|W|Q` size. -/
theorem exists_heathBrownDyadicPairMoment_high_bound_cube_total
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        16384 *
            (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 ≤
          ((2 ^ q : ℕ) : ℝ) ^ 3 →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨C, T₀, hC, hT₀, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound_cube cutoff η hη hηOne
  let A₀ : ℝ := 3 * (2 + 2 * (5 * Real.pi + 1))
  let C' : ℝ := C + 19 * A₀
  refine ⟨C', T₀, by dsimp only [C', A₀]; positivity, hT₀, ?_⟩
  intro q T W hQ hT hSep hBase hCube
  let Q : ℕ := 2 ^ q
  let G : ℝ := (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 + 1
  have hTTwo : 2 ≤ T := hT₀.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPow : 1 ≤ T ^ (52 * η) :=
    Real.one_le_rpow hTOne (by positivity)
  have hG₀ : 0 ≤ G := by dsimp only [G]; positivity
  have hRQ₀ : 0 ≤ (W.card : ℝ) * Q := by positivity
  by_cases hBelow : ((4 * Q : ℕ) : ℝ) ≤ T
  · have hRaw := hHigh q T W hQ hT (by simpa only [Q] using hBelow)
      hSep hBase (by simpa only [Q] using hCube)
    calc
      heathBrownDyadicPairMoment q W ≤
          C * T ^ (52 * η) * G := by simpa only [G, Q] using hRaw
      _ ≤ C' * T ^ (52 * η) * G := by
        dsimp only [C']
        gcongr
        have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
        linarith
  · have hQPos : 0 < Q := by dsimp only [Q]; positivity
    have hTwoQPos : 0 < 2 * Q := by omega
    have hTlt : T < (4 * Q : ℕ) := lt_of_not_ge hBelow
    have hDirect₀ := heathBrownWeightedMoment_direct_meanValue
      Q T W hQPos hTOne hSep hBase
    have hDirect₁ := heathBrownWeightedMoment_direct_meanValue
      (2 * Q) T W hTwoQPos hTOne hSep hBase
    have hFirst : heathBrownWeightedMoment Q W ≤
        9 * A₀ * (W.card : ℝ) * Q := by
      calc
        _ ≤ A₀ * (W.card : ℝ) * (2 * T + (Q : ℝ)) := by
          simpa only [A₀] using hDirect₀
        _ ≤ 9 * A₀ * (W.card : ℝ) * Q := by
          have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
          have hR₀ : 0 ≤ (W.card : ℝ) := by positivity
          have hLength : 2 * T + (Q : ℝ) ≤ 9 * Q := by
            have hCast : T < 4 * (Q : ℝ) := by
              norm_num [Nat.cast_mul] at hTlt ⊢
              exact hTlt
            linarith
          calc
            _ ≤ A₀ * (W.card : ℝ) * (9 * Q) :=
              mul_le_mul_of_nonneg_left hLength (mul_nonneg hA₀ hR₀)
            _ = _ := by ring
    have hSecond : heathBrownWeightedMoment (2 * Q) W ≤
        10 * A₀ * (W.card : ℝ) * Q := by
      calc
        _ ≤ A₀ * (W.card : ℝ) * (2 * T + (2 * Q : ℕ)) := by
          simpa only [A₀] using hDirect₁
        _ ≤ 10 * A₀ * (W.card : ℝ) * Q := by
          have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
          have hR₀ : 0 ≤ (W.card : ℝ) := by positivity
          have hLength : 2 * T + ((2 * Q : ℕ) : ℝ) ≤ 10 * Q := by
            have hCast : T < 4 * (Q : ℝ) := by
              norm_num [Nat.cast_mul] at hTlt ⊢
              exact hTlt
            push_cast
            linarith
          calc
            _ ≤ A₀ * (W.card : ℝ) * (10 * Q) :=
              mul_le_mul_of_nonneg_left hLength (mul_nonneg hA₀ hR₀)
            _ = _ := by ring
    have hPair : heathBrownDyadicPairMoment q W ≤
        19 * A₀ * (W.card : ℝ) * Q := by
      have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
        dsimp only [Q]
        rw [pow_succ]
        ring
      unfold heathBrownDyadicPairMoment
      rw [show 2 ^ q = Q by rfl, hTwoQ]
      calc
        _ ≤ 9 * A₀ * (W.card : ℝ) * Q +
            10 * A₀ * (W.card : ℝ) * Q := add_le_add hFirst hSecond
        _ = _ := by ring
    calc
      heathBrownDyadicPairMoment q W ≤
          19 * A₀ * (W.card : ℝ) * Q := hPair
      _ ≤ (19 * A₀) * T ^ (52 * η) * G := by
        have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
        have hRQG : (W.card : ℝ) * Q ≤ G := by
          dsimp only [G]
          nlinarith [sq_nonneg (W.card : ℝ)]
        calc
          _ = (19 * A₀) * ((W.card : ℝ) * Q) := by ring
          _ ≤ (19 * A₀) * G := by gcongr
          _ ≤ (19 * A₀) * T ^ (52 * η) * G := by
            calc
              _ = (19 * A₀) * 1 * G := by ring
              _ ≤ _ := by gcongr
      _ ≤ C' * T ^ (52 * η) * G := by
        dsimp only [C']
        gcongr
        linarith [hC]

/-- The unclosed adjacent-pair form of (29.41).  Unlike the high-range
self-recurrence, this theorem has no powered-return hypothesis and is the
entry point for the medium and small ranges of Lemma 29.10. -/
theorem exists_heathBrownDyadicPairMoment_recurrence
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ K T₀ : ℝ, 0 < K ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownDyadicPairMoment q W ≤
          K * T ^ (24 * η) *
            (3 * (W.card : ℝ) * (2 ^ q : ℕ) +
              2 * (W.card : ℝ) ^ 2 +
              heathBrownDyadicChildPackage η T q W + 2) := by
  obtain ⟨C, D, hC, hD, T₀, hT₀, hRec⟩ :=
    exists_heathBrownWeightedMoment_terminal_recurrence_factored
      cutoff η hη hηOne
  let K : ℝ := C * (1 + 24 * D ^ 2 * 96 ^ (2 * η))
  refine ⟨K, T₀, by dsimp only [K]; positivity, hT₀, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase
  let Q : ℕ := 2 ^ q
  let Q₁ : ℕ := 2 ^ (q + 1)
  let H : ℕ := heathBrownSmoothingHeight T η
  let P₀ : ℕ := heathBrownSourceTerminalScale T Q H
  let P₁ : ℕ := heathBrownSourceTerminalScale T Q₁ H
  have hTTwo : 2 ≤ T := hT₀.trans hT
  have hQ30 : 30 ≤ Q := by simpa only [Q] using hQ
  have hQ₁eq : Q₁ = 2 * Q := by
    dsimp only [Q₁, Q]
    rw [pow_succ]
    ring
  have hQ₁30 : 30 ≤ Q₁ := by rw [hQ₁eq]; omega
  have hFour : (((4 * Q : ℕ) : ℝ)) ≤ T := by simpa only [Q] using hFourQ
  have h2Q : (((2 * Q : ℕ) : ℝ)) ≤ T := by
    have hCast : (((2 * Q : ℕ) : ℝ)) ≤ ((4 * Q : ℕ) : ℝ) := by
      exact_mod_cast (show (2 * Q : ℕ) ≤ 4 * Q by omega)
    exact hCast.trans hFour
  have h2Q₁ : (((2 * Q₁ : ℕ) : ℝ)) ≤ T := by
    calc
      (((2 * Q₁ : ℕ) : ℝ)) = (((4 * Q : ℕ) : ℝ)) := by
        rw [hQ₁eq]
        norm_num
        ring
      _ ≤ T := hFour
  have hRec₀ := hRec Q T W hQ30 hT h2Q hSep hBase
  have hRec₁ := hRec Q₁ T W hQ₁30 hT h2Q₁ hSep hBase
  have hLoss₀ := heathBrownTerminalRecurrenceLoss_le_rpow
    (C := C) (D := D) (η := η) (T := T) (N := Q)
    hC hη hηOne hTTwo hQ30
  have hLoss₁ := heathBrownTerminalRecurrenceLoss_le_rpow
    (C := C) (D := D) (η := η) (T := T) (N := Q₁)
    hC hη hηOne hTTwo hQ₁30
  change heathBrownWeightedMoment Q W ≤
    heathBrownTerminalRecurrenceLoss C D η T P₀ *
      ((W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₀ W +
        heathBrownWeightedMoment (2 * P₀) W + 1) at hRec₀
  change heathBrownWeightedMoment Q₁ W ≤
    heathBrownTerminalRecurrenceLoss C D η T P₁ *
      ((W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₁ W +
        heathBrownWeightedMoment (2 * P₁) W + 1) at hRec₁
  change heathBrownTerminalRecurrenceLoss C D η T P₀ ≤
    K * T ^ (24 * η) at hLoss₀
  change heathBrownTerminalRecurrenceLoss C D η T P₁ ≤
    K * T ^ (24 * η) at hLoss₁
  have hInside₀ : 0 ≤
      (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₀ W +
        heathBrownWeightedMoment (2 * P₀) W + 1 := by
    have h₀ := heathBrownWeightedMoment_nonneg P₀ W
    have h₁ := heathBrownWeightedMoment_nonneg (2 * P₀) W
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (sq_nonneg (W.card : ℝ))) h₀) h₁) zero_le_one
  have hInside₁ : 0 ≤
      (W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
        heathBrownWeightedMoment P₁ W +
        heathBrownWeightedMoment (2 * P₁) W + 1 := by
    have h₀ := heathBrownWeightedMoment_nonneg P₁ W
    have h₁ := heathBrownWeightedMoment_nonneg (2 * P₁) W
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (sq_nonneg (W.card : ℝ))) h₀) h₁) zero_le_one
  have hBound₀ := hRec₀.trans
    (mul_le_mul_of_nonneg_right hLoss₀ hInside₀)
  have hBound₁ := hRec₁.trans
    (mul_le_mul_of_nonneg_right hLoss₁ hInside₁)
  have hPackage : heathBrownDyadicChildPackage η T q W =
      heathBrownWeightedMoment P₀ W +
        heathBrownWeightedMoment (2 * P₀) W +
        heathBrownWeightedMoment P₁ W +
        heathBrownWeightedMoment (2 * P₁) W := by rfl
  unfold heathBrownDyadicPairMoment
  rw [show 2 ^ (q + 1) = Q₁ by rfl]
  calc
    _ ≤ K * T ^ (24 * η) *
          ((W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
            heathBrownWeightedMoment P₀ W +
            heathBrownWeightedMoment (2 * P₀) W + 1) +
        K * T ^ (24 * η) *
          ((W.card : ℝ) * Q₁ + (W.card : ℝ) ^ 2 +
            heathBrownWeightedMoment P₁ W +
            heathBrownWeightedMoment (2 * P₁) W + 1) :=
      add_le_add hBound₀ hBound₁
    _ = K * T ^ (24 * η) *
        (3 * (W.card : ℝ) * (Q : ℝ) + 2 * (W.card : ℝ) ^ 2 +
          heathBrownDyadicChildPackage η T q W + 2) := by
      rw [hPackage, hQ₁eq]
      push_cast
      ring
    _ = _ := by rfl

private lemma nonneg_le_add_one_sq (x : ℝ) (hx : 0 ≤ x) : x ≤ (x + 1) ^ 2 := by
  nlinarith [sq_nonneg x]

private lemma add_four_le_add_four {a b c d A B C D : ℝ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    a + b + c + d ≤ A + B + C + D := by
  linarith

private lemma cast_four_mul_sq_pow_three (P : ℕ) :
    (((4 * P ^ 2 : ℕ) : ℝ) ^ 3) = 64 * ((P : ℝ) ^ 3) ^ 2 := by
  push_cast
  ring

private lemma pow_two_succ_eq_two_mul (q : ℕ) : 2 ^ (q + 1) = 2 * 2 ^ q := by
  rw [pow_succ]
  omega

private lemma zero_le_sixty_four : (0 : ℝ) ≤ 64 := by
  norm_num

/-- Medium-range estimate for one dyadic reflected child.  This is the
literal `k = 2`, `4M²` step in Montgomery--Vaughan Lemma 29.10, with the
high-range theorem applied to the resulting adjacent pair. -/
theorem exists_heathBrownWeightedMoment_medium_child_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ D T₀ : ℝ, 0 < D ∧ 36864 ≤ T₀ ∧
      ∀ (p : ℕ) (T : ℝ) (W : Finset ℝ),
        3 ≤ 2 ^ p → T₀ ≤ T →
        ((2 ^ p : ℕ) : ℝ) ≤ 48 * T ^ 2 →
        IsSeparated 1 W → InBaseInterval T W →
        16384 * (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 ≤
          ((4 * (2 ^ p) ^ 2 : ℕ) : ℝ) ^ 3 →
        heathBrownWeightedMoment (2 ^ p) W ≤
          D * T ^ (36 * η) *
            (2 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) * (2 ^ p : ℕ) +
              (W.card : ℝ) ^ 2 + (W.card : ℝ)) := by
  obtain ⟨E, hE, hPower⟩ :=
    exists_heathBrownWeightedMoment_sq_le_four_mul_sq_sharp_uniform η hη
  obtain ⟨C, T₀, hC, hT₀, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound_cube_total
      cutoff η hη hηOne
  let D : ℝ := E * C + 1
  let T₁ : ℝ := max T₀ 36864
  refine ⟨D, T₁, by dsimp only [D]; positivity,
    le_max_right _ _, ?_⟩
  intro p T W hMThree hT hMUpper hSep hBase hCube
  let M : ℕ := 2 ^ p
  let q : ℕ := 2 * p + 2
  let Q : ℕ := 4 * M ^ 2
  let R : ℝ := W.card
  let Z : ℝ := 2 * R * Real.sqrt R * M + R ^ 2 + R
  have hTSource : T₀ ≤ T := (le_max_left _ _).trans hT
  have hTLarge : (36864 : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hMPos : 0 < M := by dsimp only [M]; positivity
  have hMThree' : 3 ≤ M := by simpa only [M] using hMThree
  have hQIdentity : 2 ^ q = Q := by
    dsimp only [q, Q, M]
    calc
      2 ^ (2 * p + 2) = 2 ^ (p + p + 2) := by congr 1; omega
      _ = 2 ^ p * 2 ^ p * 2 ^ 2 := by rw [pow_add, pow_add]
      _ = 4 * (2 ^ p) ^ 2 := by norm_num; ring
  have hQThirty : 30 ≤ 2 ^ q := by rw [hQIdentity]; dsimp only [Q]; nlinarith
  have hHighApplied := hHigh q T W hQThirty hTSource hSep hBase
    (by simpa only [hQIdentity, Q, M] using hCube)
  have hHighQ : heathBrownDyadicPairMoment q W ≤
      C * T ^ (52 * η) * (R * Q + R ^ 2 + 1) := by
    simpa only [R, Q, hQIdentity] using hHighApplied
  have hPowered := hPower M W hMPos
  have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
    rw [pow_succ, hQIdentity]
    omega
  have hPairIdentity :
      heathBrownWeightedMoment (4 * M ^ 2) W +
          heathBrownWeightedMoment (8 * M ^ 2) W =
        heathBrownDyadicPairMoment q W := by
    have hEight : 8 * M ^ 2 = 2 * Q := by
      dsimp only [Q]
      ring
    unfold heathBrownDyadicPairMoment
    rw [hQIdentity, hTwoQ, hEight]
  rw [hPairIdentity] at hPowered
  have hM₀ : (0 : ℝ) ≤ M := by positivity
  have hMUpper' : (M : ℝ) ≤ 48 * T ^ 2 := by simpa only [M] using hMUpper
  have hMSquare : (M : ℝ) ^ 2 ≤ (48 * T ^ 2) ^ 2 :=
    (sq_le_sq₀ hM₀ (by positivity)).2 hMUpper'
  have hBaseSixteen : (16 * M ^ 2 : ℕ) ≤ (T : ℝ) ^ 5 := by
    have hFirst : ((16 * M ^ 2 : ℕ) : ℝ) ≤ 36864 * T ^ 4 := by
      push_cast
      nlinarith
    have hSecond : 36864 * T ^ 4 ≤ T ^ 5 := by
      have := mul_le_mul_of_nonneg_right hTLarge (pow_nonneg (show 0 ≤ T by linarith) 4)
      nlinarith
    exact hFirst.trans hSecond
  have hBaseFour : (4 * M ^ 2 : ℕ) ≤ (T : ℝ) ^ 5 := by
    have hNat : 4 * M ^ 2 ≤ 16 * M ^ 2 := by omega
    have hNatReal : ((4 * M ^ 2 : ℕ) : ℝ) ≤ ((16 * M ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    exact hNatReal.trans hBaseSixteen
  have hScaleIdentity : ((T : ℝ) ^ 5) ^ η = T ^ (5 * η) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hTPos.le]
    norm_num
  have hScaleFour : ((4 * (M : ℝ) ^ 2) ^ η) ≤ T ^ (5 * η) := by
    calc
      _ ≤ ((T : ℝ) ^ 5) ^ η :=
        Real.rpow_le_rpow (by positivity) (by
          norm_num [Nat.cast_mul, Nat.cast_pow] at hBaseFour ⊢
          exact hBaseFour) hη.le
      _ = _ := hScaleIdentity
  have hScaleSixteen : ((16 * (M : ℝ) ^ 2) ^ η) ≤ T ^ (5 * η) := by
    calc
      _ ≤ ((T : ℝ) ^ 5) ^ η :=
        Real.rpow_le_rpow (by positivity) (by
          norm_num [Nat.cast_mul, Nat.cast_pow] at hBaseSixteen ⊢
          exact hBaseSixteen) hη.le
      _ = _ := hScaleIdentity
  have hScaleProduct : ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
        ((16 * (M : ℝ) ^ 2) ^ η) ^ 2 ≤
      (T ^ (5 * η)) ^ 4 := by
    calc
      _ ≤ (T ^ (5 * η)) ^ 2 * (T ^ (5 * η)) ^ 2 := by gcongr
      _ = _ := by ring
  have hPowerIdentity : (T ^ (5 * η)) ^ 4 * T ^ (52 * η) =
      T ^ (72 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le,
      ← Real.rpow_add hTPos]
    congr 1
    norm_num
    ring
  have hR₀ : 0 ≤ R := by dsimp only [R]; positivity
  have hSqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR₀
  have hZ₀ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hD₀ : 0 ≤ D := by dsimp only [D]; positivity
  have hShape : R ^ 2 * (R * Q + R ^ 2 + 1) ≤ Z ^ 2 := by
    let a : ℝ := 2 * R * Real.sqrt R * M
    let b : ℝ := R ^ 2
    let c : ℝ := R
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hb : 0 ≤ b := by dsimp only [b]; positivity
    have hc : 0 ≤ c := hR₀
    have hSum : a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
      have hab : 0 ≤ 2 * a * b := by positivity
      have hac : 0 ≤ 2 * a * c := by positivity
      have hbc : 0 ≤ 2 * b * c := by positivity
      calc
        a ^ 2 + b ^ 2 + c ^ 2 ≤
            a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c := by
          linarith
        _ = (a + b + c) ^ 2 := by ring
    calc
      R ^ 2 * (R * Q + R ^ 2 + 1) = a ^ 2 + b ^ 2 + c ^ 2 := by
        have haSquare : a ^ 2 = 4 * R ^ 3 * (M : ℝ) ^ 2 := by
          dsimp only [a]
          calc
            (2 * R * Real.sqrt R * (M : ℝ)) ^ 2 =
                4 * R ^ 2 * (Real.sqrt R) ^ 2 * (M : ℝ) ^ 2 := by ring
            _ = 4 * R ^ 3 * (M : ℝ) ^ 2 := by rw [hSqrtSq]; ring
        rw [haSquare]
        dsimp only [b, c, Q]
        push_cast
        ring
      _ ≤ (a + b + c) ^ 2 := hSum
      _ = Z ^ 2 := by rfl
  have hRaw : heathBrownWeightedMoment M W ^ 2 ≤
      E * C * T ^ (72 * η) * Z ^ 2 := by
    let U : ℝ := ((4 * (M : ℝ) ^ 2) ^ η) ^ 2 *
      ((16 * (M : ℝ) ^ 2) ^ η) ^ 2
    let P : ℝ := heathBrownDyadicPairMoment q W
    let V : ℝ := C * T ^ (52 * η) * (R * Q + R ^ 2 + 1)
    have hPowered' : heathBrownWeightedMoment M W ^ 2 ≤ E * U * R ^ 2 * P := by
      dsimp only [U, P]
      simpa only [R, mul_assoc] using hPowered
    have hPair' : P ≤ V := by
      simpa only [P, V] using hHighQ
    have hU : U ≤ (T ^ (5 * η)) ^ 4 := by
      simpa only [U] using hScaleProduct
    have hE₀ : 0 ≤ E := by positivity
    have hR2₀ : 0 ≤ R ^ 2 := sq_nonneg R
    have hP₀ : 0 ≤ P := by
      dsimp only [P]
      unfold heathBrownDyadicPairMoment
      exact add_nonneg (heathBrownWeightedMoment_nonneg (2 ^ q) W)
        (heathBrownWeightedMoment_nonneg (2 ^ (q + 1)) W)
    calc
      _ ≤ E * U * R ^ 2 * P := hPowered'
      _ = E * U * (R ^ 2 * P) := by ring
      _ ≤ E * (T ^ (5 * η)) ^ 4 *
          (R ^ 2 * P) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hU hE₀)
          (mul_nonneg hR2₀ hP₀)
      _ ≤ E * (T ^ (5 * η)) ^ 4 * (R ^ 2 * V) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hPair' hR2₀)
          (mul_nonneg hE₀ (pow_nonneg (Real.rpow_nonneg hTPos.le (5 * η)) 4))
      _ = E * (T ^ (5 * η)) ^ 4 * R ^ 2 * V := by ring
      _ = E * C * ((T ^ (5 * η)) ^ 4 * T ^ (52 * η)) *
          (R ^ 2 * (R * Q + R ^ 2 + 1)) := by
        dsimp only [V]
        ring
      _ = E * C * T ^ (72 * η) *
          (R ^ 2 * (R * Q + R ^ 2 + 1)) := by rw [hPowerIdentity]
      _ ≤ E * C * T ^ (72 * η) * Z ^ 2 := by gcongr
  have hDsq : E * C ≤ D ^ 2 := by
    simpa only [D] using nonneg_le_add_one_sq (E * C) (mul_nonneg hE.le hC.le)
  have hThirtySixIdentity : (T ^ (36 * η)) ^ 2 = T ^ (72 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
    norm_num
    congr 1
    ring
  have hTargetSquare : heathBrownWeightedMoment M W ^ 2 ≤
      (D * T ^ (36 * η) * Z) ^ 2 := by
    calc
      _ ≤ E * C * T ^ (72 * η) * Z ^ 2 := hRaw
      _ ≤ D ^ 2 * T ^ (72 * η) * Z ^ 2 := by gcongr
      _ = (D * T ^ (36 * η) * Z) ^ 2 := by
        rw [← hThirtySixIdentity]
        ring
  have hLeft₀ := heathBrownWeightedMoment_nonneg M W
  have hRight₀ : 0 ≤ D * T ^ (36 * η) * Z := by
    exact mul_nonneg (mul_nonneg hD₀ (Real.rpow_nonneg hTPos.le _)) hZ₀
  have hResult := (sq_le_sq₀ hLeft₀ hRight₀).1 hTargetSquare
  simpa only [M, R, Z] using hResult

/-- The four reflected children in the unclosed `(29.41)` recurrence obey
the medium estimate once each base terminal has entered the `k = 2`
window.  The two doubled terminals are handled at the same time; no
independent estimate is assumed for them. -/
theorem exists_heathBrownDyadicChildPackage_medium_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ D T₀ : ℝ, 0 < D ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        let H := heathBrownSmoothingHeight T η
        let P₀ := heathBrownSourceTerminalScale T (2 ^ q) H
        let P₁ := heathBrownSourceTerminalScale T (2 ^ (q + 1)) H
        3 ≤ P₀ → 3 ≤ P₁ → T₀ ≤ T →
        (P₀ : ℝ) ≤ 24 * T ^ 2 → (P₁ : ℝ) ≤ 24 * T ^ 2 →
        IsSeparated 1 W → InBaseInterval T W →
        16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 →
        16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 →
        heathBrownDyadicChildPackage η T q W ≤
          D * T ^ (36 * η) *
            (6 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) *
                ((P₀ : ℝ) + P₁) +
              4 * ((W.card : ℝ) ^ 2 + (W.card : ℝ))) := by
  obtain ⟨D, T₀, hD, hT₀, hChild⟩ :=
    exists_heathBrownWeightedMoment_medium_child_bound cutoff η hη hηOne
  refine ⟨D, T₀, hD, hT₀, ?_⟩
  intro q T W
  dsimp only
  let H := heathBrownSmoothingHeight T η
  let e₀ := heathBrownSourceTerminalExponent T (2 ^ q) H
  let e₁ := heathBrownSourceTerminalExponent T (2 ^ (q + 1)) H
  let P₀ := heathBrownSourceTerminalScale T (2 ^ q) H
  let P₁ := heathBrownSourceTerminalScale T (2 ^ (q + 1)) H
  intro hP₀Three hP₁Three hT hP₀Upper hP₁Upper hSep hBase hP₀Cube hP₁Cube
  change 3 ≤ P₀ at hP₀Three
  change 3 ≤ P₁ at hP₁Three
  change (P₀ : ℝ) ≤ 24 * T ^ 2 at hP₀Upper
  change (P₁ : ℝ) ≤ 24 * T ^ 2 at hP₁Upper
  change 16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 at hP₀Cube
  change 16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 at hP₁Cube
  have hP₀Eq : 2 ^ e₀ = P₀ := by rfl
  have hP₁Eq : 2 ^ e₁ = P₁ := by rfl
  have hP₀Double : 2 ^ (e₀ + 1) = 2 * P₀ := by
    rw [pow_succ, hP₀Eq]
    omega
  have hP₁Double : 2 ^ (e₁ + 1) = 2 * P₁ := by
    rw [pow_succ, hP₁Eq]
    omega
  have hP₀DoubleThree : 3 ≤ 2 * P₀ := by omega
  have hP₁DoubleThree : 3 ≤ 2 * P₁ := by omega
  have hP₀DoubleUpper : ((2 * P₀ : ℕ) : ℝ) ≤ 48 * T ^ 2 := by
    push_cast
    linarith
  have hP₁DoubleUpper : ((2 * P₁ : ℕ) : ℝ) ≤ 48 * T ^ 2 := by
    push_cast
    linarith
  have hP₀Upper' : (P₀ : ℝ) ≤ 48 * T ^ 2 := hP₀Upper.trans (by gcongr; norm_num)
  have hP₁Upper' : (P₁ : ℝ) ≤ 48 * T ^ 2 := hP₁Upper.trans (by gcongr; norm_num)
  have hP₀DoubleCube :
      16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * (2 * P₀) ^ 2 : ℕ) : ℝ) ^ 3 := by
    calc
      _ ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 := hP₀Cube
      _ ≤ ((4 * (2 * P₀) ^ 2 : ℕ) : ℝ) ^ 3 := by
        gcongr
        omega
  have hP₁DoubleCube :
      16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * (2 * P₁) ^ 2 : ℕ) : ℝ) ^ 3 := by
    calc
      _ ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 := hP₁Cube
      _ ≤ ((4 * (2 * P₁) ^ 2 : ℕ) : ℝ) ^ 3 := by
        gcongr
        omega
  have h₀ := hChild e₀ T W (by simpa only [hP₀Eq] using hP₀Three) hT
    (by simpa only [hP₀Eq] using hP₀Upper') hSep hBase
    (by simpa only [hP₀Eq, H] using hP₀Cube)
  have h₀' := hChild (e₀ + 1) T W
    (by simpa only [hP₀Double] using hP₀DoubleThree) hT
    (by simpa only [hP₀Double] using hP₀DoubleUpper) hSep hBase
    (by simpa only [hP₀Double, H] using hP₀DoubleCube)
  have h₁ := hChild e₁ T W (by simpa only [hP₁Eq] using hP₁Three) hT
    (by simpa only [hP₁Eq] using hP₁Upper') hSep hBase
    (by simpa only [hP₁Eq, H] using hP₁Cube)
  have h₁' := hChild (e₁ + 1) T W
    (by simpa only [hP₁Double] using hP₁DoubleThree) hT
    (by simpa only [hP₁Double] using hP₁DoubleUpper) hSep hBase
    (by simpa only [hP₁Double, H] using hP₁DoubleCube)
  rw [hP₀Eq] at h₀
  rw [hP₀Double] at h₀'
  rw [hP₁Eq] at h₁
  rw [hP₁Double] at h₁'
  change heathBrownWeightedMoment P₀ W + heathBrownWeightedMoment (2 * P₀) W +
      heathBrownWeightedMoment P₁ W + heathBrownWeightedMoment (2 * P₁) W ≤ _
  calc
    _ ≤ D * T ^ (36 * η) *
          (2 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) * P₀ +
            (W.card : ℝ) ^ 2 + (W.card : ℝ)) +
        D * T ^ (36 * η) *
          (2 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) * (2 * P₀ : ℕ) +
            (W.card : ℝ) ^ 2 + (W.card : ℝ)) +
        D * T ^ (36 * η) *
          (2 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) * P₁ +
            (W.card : ℝ) ^ 2 + (W.card : ℝ)) +
        D * T ^ (36 * η) *
          (2 * (W.card : ℝ) * Real.sqrt (W.card : ℝ) * (2 * P₁ : ℕ) +
            (W.card : ℝ) ^ 2 + (W.card : ℝ)) := by
      exact add_four_le_add_four h₀ h₀' h₁ h₁'
    _ = _ := by
      push_cast
      ring

set_option maxHeartbeats 600000 in
/-- If the parent is below the cubic transition, both rounded reciprocal
terminals (for `Q` and `2Q`) lie in the medium `k = 2` window.  This is the
fully quantitative replacement for the paper's use of `M = T^(1+ε)/N`.
The factor `128` is exactly what is needed for the second parent `2Q`. -/
theorem heathBrownDyadicTerminals_enter_medium_window
    {η T : ℝ} {q : ℕ} (hη : 0 ≤ η) (hηOne : η ≤ 1)
    (hT : 36864 ≤ T) (hQ : 30 ≤ 2 ^ q)
    (hFourQ : ((4 * 2 ^ q : ℕ) : ℝ) ≤ T)
    (hLow : 128 * ((2 ^ q : ℕ) : ℝ) ^ 3 ≤
      (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2) :
    let H := heathBrownSmoothingHeight T η
    let P₀ := heathBrownSourceTerminalScale T (2 ^ q) H
    let P₁ := heathBrownSourceTerminalScale T (2 ^ (q + 1)) H
    3 ≤ P₀ ∧ 3 ≤ P₁ ∧
      (P₀ : ℝ) ≤ 24 * T ^ 2 ∧ (P₁ : ℝ) ≤ 24 * T ^ 2 ∧
      16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 ∧
      16384 * (T * (H : ℝ)) ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 := by
  let Q : ℕ := 2 ^ q
  let H : ℕ := heathBrownSmoothingHeight T η
  let P₀ : ℕ := heathBrownSourceTerminalScale T Q H
  let P₁ : ℕ := heathBrownSourceTerminalScale T (2 * Q) H
  have hTTwo : 2 ≤ T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hQ30 : 30 ≤ Q := by simpa only [Q] using hQ
  have hQPos : 0 < Q := by omega
  have hTwoQ30 : 30 ≤ 2 * Q := by omega
  have hHPos : 0 < H := by
    dsimp only [H]
    exact heathBrownSmoothingHeight_pos T η
  have hFloorHalf : T / 2 ≤ (Nat.floor T : ℝ) := by
    have hFloorSucc : T < (Nat.floor T : ℝ) + 1 := Nat.lt_floor_add_one T
    linarith
  have hX₀ : 0 ≤ T * (H : ℝ) := by positivity
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQPos
  have hTwoQReal : (0 : ℝ) < 2 * Q := by positivity
  have hTerminalLower₀ : T * (H : ℝ) / Q ≤ (P₀ : ℝ) := by
    have hScaled : T * (H : ℝ) ≤ 2 * ((Nat.floor T : ℝ) * H) := by
      have := mul_le_mul_of_nonneg_right hFloorHalf (show 0 ≤ (H : ℝ) by positivity)
      nlinarith
    calc
      T * (H : ℝ) / Q ≤ 2 * ((Nat.floor T : ℝ) * H) / Q :=
        div_le_div_of_nonneg_right hScaled hQReal.le
      _ = 2 * ((Nat.floor T : ℝ) * H / Q) := by ring
      _ ≤ (P₀ : ℝ) := by
        simpa only [P₀, Q] using
          two_mul_floor_mul_height_div_le_heathBrownSourceTerminalScale
            hTOne hQ30 hHPos
  have hTerminalLower₁ : T * (H : ℝ) / (2 * Q) ≤ (P₁ : ℝ) := by
    have hScaled : T * (H : ℝ) ≤ 2 * ((Nat.floor T : ℝ) * H) := by
      have := mul_le_mul_of_nonneg_right hFloorHalf (show 0 ≤ (H : ℝ) by positivity)
      nlinarith
    calc
      T * (H : ℝ) / (2 * Q) ≤ 2 * ((Nat.floor T : ℝ) * H) / (2 * Q) :=
        div_le_div_of_nonneg_right hScaled hTwoQReal.le
      _ = 2 * ((Nat.floor T : ℝ) * H / (2 * Q)) := by ring
      _ ≤ (P₁ : ℝ) := by
        have h := two_mul_floor_mul_height_div_le_heathBrownSourceTerminalScale
          hTOne hTwoQ30 hHPos
        norm_num [Nat.cast_mul] at h ⊢
        simpa only [P₁, Q] using h
  have hFourQ' : ((4 * Q : ℕ) : ℝ) ≤ T := by
    simpa only [Q] using hFourQ
  have hFourQNat : 4 * Q ≤ Nat.floor T := Nat.le_floor hFourQ'
  have hFloorFourQ : (4 * (Q : ℝ)) ≤ (Nat.floor T : ℝ) := by
    exact_mod_cast hFourQNat
  have hFourQReal : 4 * (Q : ℝ) ≤ T := by
    norm_num [Nat.cast_mul] at hFourQ'
    exact hFourQ'
  have hRatio₀ : 4 ≤ T * (H : ℝ) / Q := by
    apply (le_div_iff₀ hQReal).2
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hHPos
    calc
      (4 : ℝ) * Q ≤ T := hFourQReal
      _ ≤ T * H := by
        nlinarith [mul_nonneg (show 0 ≤ T by linarith) (sub_nonneg.2 hHOne)]
  have hRatio₁ : 2 ≤ T * (H : ℝ) / (2 * Q) := by
    calc
      (2 : ℝ) = 4 / 2 := by norm_num
      _ ≤ (T * (H : ℝ) / Q) / 2 := by gcongr
      _ = T * (H : ℝ) / (2 * Q) := by field_simp
  have hP₁Four : (4 : ℝ) ≤ P₁ := by
    have hExact := two_mul_floor_mul_height_div_le_heathBrownSourceTerminalScale
      hTOne hTwoQ30 hHPos
    have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hHPos
    have hFourRatio : (4 : ℝ) ≤
        2 * ((Nat.floor T : ℝ) * H / (2 * Q)) := by
      have hIdentity :
          2 * ((Nat.floor T : ℝ) * H / (2 * Q)) =
            (Nat.floor T : ℝ) * H / Q := by field_simp
      rw [hIdentity, le_div_iff₀ hQReal]
      calc
        (4 : ℝ) * Q ≤ (Nat.floor T : ℝ) := hFloorFourQ
        _ ≤ (Nat.floor T : ℝ) * H := by
          nlinarith [mul_nonneg (show 0 ≤ (Nat.floor T : ℝ) by positivity)
            (sub_nonneg.2 hHOne)]
    norm_num [Nat.cast_mul] at hExact
    change 2 * ((Nat.floor T : ℝ) * H / (2 * (Q : ℝ))) ≤ (P₁ : ℝ) at hExact
    exact hFourRatio.trans hExact
  have hP₀ThreeReal : (3 : ℝ) ≤ P₀ := by linarith
  have hP₁ThreeReal : (3 : ℝ) ≤ P₁ := by linarith
  have hP₀Three : 3 ≤ P₀ := by exact_mod_cast hP₀ThreeReal
  have hP₁Three : 3 ≤ P₁ := by exact_mod_cast hP₁ThreeReal
  have hP₀Upper : (P₀ : ℝ) ≤ 24 * T ^ 2 := by
    simpa only [P₀, Q, H] using
      heathBrownSourceTerminalScale_le_twenty_four_mul_sq
        hη hηOne hTTwo hQ30 rfl
  have hP₁Upper : (P₁ : ℝ) ≤ 24 * T ^ 2 := by
    simpa only [P₁, Q, H] using
      heathBrownSourceTerminalScale_le_twenty_four_mul_sq
        hη hηOne hTTwo hTwoQ30 rfl
  let X : ℝ := T * (H : ℝ)
  have hLow' : 128 * (Q : ℝ) ^ 3 ≤ X ^ 2 := by
    simpa only [Q, H, X] using hLow
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hRatioCube₀ : 16 * X ≤ (X / Q) ^ 3 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hQReal 3)).2
    have hScaled := mul_le_mul_of_nonneg_left hLow' (show 0 ≤ X / 8 by positivity)
    calc
      16 * X * (Q : ℝ) ^ 3 = X / 8 * (128 * (Q : ℝ) ^ 3) := by ring
      _ ≤ X / 8 * X ^ 2 := hScaled
      _ ≤ X ^ 3 := by nlinarith [sq_nonneg X]
  have hRatioCube₁ : 16 * X ≤ (X / (2 * Q)) ^ 3 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hTwoQReal 3)).2
    have hScaled := mul_le_mul_of_nonneg_left hLow' hXPos.le
    calc
      16 * X * (2 * (Q : ℝ)) ^ 3 = 128 * (X * (Q : ℝ) ^ 3) := by ring
      _ ≤ X * X ^ 2 := by nlinarith
      _ = X ^ 3 := by ring
  have hP₀CubeBase : 16 * X ≤ (P₀ : ℝ) ^ 3 :=
    hRatioCube₀.trans (pow_le_pow_left₀ (by positivity) hTerminalLower₀ 3)
  have hP₁CubeBase : 16 * X ≤ (P₁ : ℝ) ^ 3 :=
    hRatioCube₁.trans (pow_le_pow_left₀ (by positivity) hTerminalLower₁ 3)
  have hCube₀ : 16384 * X ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 := by
    have hSq := pow_le_pow_left₀ (by positivity) hP₀CubeBase 2
    calc
      16384 * X ^ 2 = 64 * (16 * X) ^ 2 := by ring
      _ ≤ 64 * ((P₀ : ℝ) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left hSq zero_le_sixty_four
      _ = ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 := (cast_four_mul_sq_pow_three P₀).symm
  have hCube₁ : 16384 * X ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 := by
    have hSq := pow_le_pow_left₀ (by positivity) hP₁CubeBase 2
    calc
      16384 * X ^ 2 = 64 * (16 * X) ^ 2 := by ring
      _ ≤ 64 * ((P₁ : ℝ) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left hSq zero_le_sixty_four
      _ = ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 := (cast_four_mul_sq_pow_three P₁).symm
  have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
    change 2 ^ (q + 1) = 2 * 2 ^ q
    exact pow_two_succ_eq_two_mul q
  dsimp only
  rw [hTwoQ]
  change 3 ≤ P₀ ∧ 3 ≤ P₁ ∧
    (P₀ : ℝ) ≤ 24 * T ^ 2 ∧ (P₁ : ℝ) ≤ 24 * T ^ 2 ∧
    16384 * X ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 ∧
    16384 * X ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3
  exact ⟨hP₀Three, hP₁Three, hP₀Upper, hP₁Upper, hCube₀, hCube₁⟩

set_option maxHeartbeats 800000 in
/-- The medium alternative in Montgomery--Vaughan Lemma 29.10, before the
physical reciprocal term is absorbed.  The bound is stated for the same
adjacent dyadic pair as the source recurrence, and every occurrence of the
dual length is the actual rounded terminal produced by that recurrence. -/
theorem exists_heathBrownDyadicPairMoment_medium_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        128 * ((2 ^ q : ℕ) : ℝ) ^ 3 ≤
            (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (60 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) * Real.sqrt (W.card : ℝ) *
                (T * (heathBrownSmoothingHeight T η : ℝ) /
                    (2 ^ q : ℕ) + 1) +
              (W.card : ℝ) + 1) := by
  obtain ⟨K, TK, hK, hTK, hRec⟩ :=
    exists_heathBrownDyadicPairMoment_recurrence cutoff η hη hηOne
  obtain ⟨D, TD, hD, hTD, hChild⟩ :=
    exists_heathBrownDyadicChildPackage_medium_bound cutoff η hη hηOne
  let C : ℝ := 3 * K + 200 * K * D
  let T₀ : ℝ := max 36864 (max TK TD)
  refine ⟨C, T₀, by dsimp only [C]; positivity, le_max_left _ _, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase hLow
  let Q : ℕ := 2 ^ q
  let H : ℕ := heathBrownSmoothingHeight T η
  let P₀ : ℕ := heathBrownSourceTerminalScale T Q H
  let P₁ : ℕ := heathBrownSourceTerminalScale T (2 ^ (q + 1)) H
  let R : ℝ := W.card
  let X : ℝ := T * (H : ℝ)
  let G : ℝ := R * Q + R ^ 2 + R * Real.sqrt R * (X / Q + 1) + R + 1
  have hT36864 : 36864 ≤ T := (le_max_left 36864 (max TK TD)).trans hT
  have hTK' : TK ≤ T := (le_trans (le_max_of_le_right (le_max_left TK TD)) hT)
  have hTD' : TD ≤ T := (le_trans (le_max_of_le_right (le_max_right TK TD)) hT)
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hQ30 : 30 ≤ Q := by simpa only [Q] using hQ
  have hQPos : 0 < Q := by omega
  have hHPos : 0 < H := by
    dsimp only [H]
    exact heathBrownSmoothingHeight_pos T η
  have hFourQ' : ((4 * Q : ℕ) : ℝ) ≤ T := by simpa only [Q] using hFourQ
  have hEntry := heathBrownDyadicTerminals_enter_medium_window
    hη.le hηOne hT36864 hQ hFourQ hLow
  dsimp only at hEntry
  have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
    change 2 ^ (q + 1) = 2 * 2 ^ q
    exact pow_two_succ_eq_two_mul q
  have hEntry' : 3 ≤ P₀ ∧ 3 ≤ P₁ ∧
      (P₀ : ℝ) ≤ 24 * T ^ 2 ∧ (P₁ : ℝ) ≤ 24 * T ^ 2 ∧
      16384 * X ^ 2 ≤ ((4 * P₀ ^ 2 : ℕ) : ℝ) ^ 3 ∧
      16384 * X ^ 2 ≤ ((4 * P₁ ^ 2 : ℕ) : ℝ) ^ 3 := by
    simpa only [P₀, P₁, Q, H, X, hTwoQ] using hEntry
  rcases hEntry' with ⟨hP₀Three, hP₁Three, hP₀Upper, hP₁Upper, hP₀Cube, hP₁Cube⟩
  have hChildRaw := hChild q T W hP₀Three hP₁Three hTD'
    hP₀Upper hP₁Upper hSep hBase hP₀Cube hP₁Cube
  change heathBrownDyadicChildPackage η T q W ≤
      D * T ^ (36 * η) *
        (6 * R * Real.sqrt R * ((P₀ : ℝ) + P₁) +
          4 * (R ^ 2 + R)) at hChildRaw
  have hP₀Physical : (P₀ : ℝ) ≤ 16 * (X / Q + 1) := by
    simpa only [P₀, Q, H, X] using
      heathBrownSourceTerminalScale_le_physical hTOne hQ30 hHPos
  have hP₁Physical : (P₁ : ℝ) ≤ 16 * (X / (2 * Q) + 1) := by
    have hTwoQ30 : 30 ≤ 2 * Q := by omega
    have h := heathBrownSourceTerminalScale_le_physical
      (T := T) (N := 2 * Q) (H := H) hTOne hTwoQ30 hHPos
    change (heathBrownSourceTerminalScale T (2 ^ (q + 1)) H : ℝ) ≤
      16 * (X / (2 * Q) + 1)
    rw [hTwoQ]
    simpa only [X, Nat.cast_mul, Nat.cast_ofNat] using h
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQPos
  have hHalfRatio : X / (2 * Q) = (X / Q) / 2 := by field_simp
  have hXNonneg : 0 ≤ X := by dsimp only [X]; positivity
  have hRatioNonneg : 0 ≤ X / Q := div_nonneg hXNonneg hQReal.le
  have hPSum : (P₀ : ℝ) + P₁ ≤ 24 * (X / Q) + 32 := by
    calc
      (P₀ : ℝ) + P₁ ≤ 16 * (X / Q + 1) +
          16 * (X / (2 * Q) + 1) := add_le_add hP₀Physical hP₁Physical
      _ = 24 * (X / Q) + 32 := by rw [hHalfRatio]; ring
  have hRNonneg : 0 ≤ R := by dsimp only [R]; positivity
  have hSqrtNonneg : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hChildCore :
      6 * R * Real.sqrt R * ((P₀ : ℝ) + P₁) + 4 * (R ^ 2 + R) ≤
        200 * (R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R) := by
    have hFactorNonneg : 0 ≤ 6 * R * Real.sqrt R := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hPSum
      hFactorNonneg
    calc
      6 * R * Real.sqrt R * ((P₀ : ℝ) + P₁) + 4 * (R ^ 2 + R) ≤
          6 * R * Real.sqrt R * (24 * (X / Q) + 32) +
            4 * (R ^ 2 + R) := by linarith
      _ ≤ 200 * (R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R) := by
        nlinarith [mul_nonneg (mul_nonneg hRNonneg hSqrtNonneg) hRatioNonneg,
          sq_nonneg R]
  have hChildBound : heathBrownDyadicChildPackage η T q W ≤
      200 * D * T ^ (36 * η) *
        (R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R) := by
    calc
      _ ≤ D * T ^ (36 * η) *
          (6 * R * Real.sqrt R * ((P₀ : ℝ) + P₁) + 4 * (R ^ 2 + R)) := hChildRaw
      _ ≤ D * T ^ (36 * η) *
          (200 * (R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R)) := by
        gcongr
      _ = _ := by ring
  have hRecRaw := hRec q T W hQ hTK' hFourQ hSep hBase
  change heathBrownDyadicPairMoment q W ≤
      K * T ^ (24 * η) *
        (3 * R * Q + 2 * R ^ 2 + heathBrownDyadicChildPackage η T q W + 2) at hRecRaw
  have hGNonneg : 0 ≤ G := by dsimp only [G]; positivity
  have hBasePart : 3 * R * Q + 2 * R ^ 2 + 2 ≤ 3 * G := by
    dsimp only [G]
    nlinarith [mul_nonneg hRNonneg (show 0 ≤ (Q : ℝ) by positivity),
      mul_nonneg (mul_nonneg hRNonneg hSqrtNonneg)
        (add_nonneg hRatioNonneg zero_le_one)]
  have hChildPart :
      R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R ≤ G := by
    dsimp only [G]
    nlinarith [mul_nonneg hRNonneg (show 0 ≤ (Q : ℝ) by positivity)]
  have hPow24 : T ^ (24 * η) ≤ T ^ (60 * η) := by
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by nlinarith)
  have hPow36Nonneg : 0 ≤ T ^ (36 * η) := Real.rpow_nonneg hTPos.le _
  have hPow24Nonneg : 0 ≤ T ^ (24 * η) := Real.rpow_nonneg hTPos.le _
  have hPow60Nonneg : 0 ≤ T ^ (60 * η) := Real.rpow_nonneg hTPos.le _
  have hPowProduct : T ^ (24 * η) * T ^ (36 * η) = T ^ (60 * η) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hChildToG : heathBrownDyadicChildPackage η T q W ≤
      200 * D * T ^ (36 * η) * G := by
    calc
      _ ≤ 200 * D * T ^ (36 * η) *
          (R * Real.sqrt R * (X / Q + 1) + R ^ 2 + R) := hChildBound
      _ ≤ 200 * D * T ^ (36 * η) * G := by gcongr
  have hBody :
      3 * R * Q + 2 * R ^ 2 + heathBrownDyadicChildPackage η T q W + 2 ≤
        3 * G + 200 * D * T ^ (36 * η) * G := by
    linarith [hBasePart, hChildToG]
  have hFirstTerm : K * T ^ (24 * η) * (3 * G) ≤
      3 * K * T ^ (60 * η) * G := by
    calc
      _ = 3 * K * T ^ (24 * η) * G := by ring
      _ ≤ 3 * K * T ^ (60 * η) * G := by gcongr
  have hSecondTerm :
      K * T ^ (24 * η) * (200 * D * T ^ (36 * η) * G) =
        200 * K * D * T ^ (60 * η) * G := by
    rw [← hPowProduct]
    ring
  calc
    heathBrownDyadicPairMoment q W ≤
        K * T ^ (24 * η) *
          (3 * R * Q + 2 * R ^ 2 + heathBrownDyadicChildPackage η T q W + 2) := hRecRaw
    _ ≤ K * T ^ (24 * η) *
        (3 * G + 200 * D * T ^ (36 * η) * G) := by
      exact mul_le_mul_of_nonneg_left hBody
        (mul_nonneg hK.le hPow24Nonneg)
    _ ≤ 3 * K * T ^ (60 * η) * G +
        200 * K * D * T ^ (60 * η) * G := by
      rw [mul_add]
      exact add_le_add hFirstTerm hSecondTerm.le
    _ = C * T ^ (60 * η) * G := by dsimp only [C]; ring
    _ = _ := by rfl

set_option maxHeartbeats 600000 in
/-- Complementary cubic range for the dyadic pair.  If the parent has not
entered the medium reciprocal window, seven exact dyadic transfer steps
make the source high-range inequality applicable: `2^(3*7) = 16384*128`.
This closes the constants gap without an asymptotic or unproved rounding
convention. -/
theorem exists_heathBrownDyadicPairMoment_nonmedium_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        ¬ 128 * ((2 ^ q : ℕ) : ℝ) ^ 3 ≤
            (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2 →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (68 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := by
  obtain ⟨A, hA, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_pair_le_common_target η hη
  obtain ⟨B, TB, hB, hTB, hHigh⟩ :=
    exists_heathBrownDyadicPairMoment_high_bound_cube_total cutoff η hη hηOne
  let C : ℝ := 1024 * A ^ 2 * B
  refine ⟨C, TB, by dsimp only [C]; positivity, hTB, ?_⟩
  intro q T W hQ hT hFourQ hSep hBase hNotLow
  let Q : ℕ := 2 ^ q
  let X : ℝ := T * (heathBrownSmoothingHeight T η : ℝ)
  let G : ℝ := (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 + 1
  have hTTwo : 2 ≤ T := hTB.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hShift : 2 ^ (q + 7) = 128 * Q := by
    dsimp only [Q]
    rw [pow_add]
    norm_num
    ring
  have hShiftThirty : 30 ≤ 2 ^ (q + 7) := by
    rw [hShift]
    have hQ' : 30 ≤ Q := by simpa only [Q] using hQ
    omega
  have hNotLow' : X ^ 2 < 128 * (Q : ℝ) ^ 3 := by
    exact lt_of_not_ge (by simpa only [Q, X] using hNotLow)
  have hCube : 16384 * X ^ 2 ≤ ((2 ^ (q + 7) : ℕ) : ℝ) ^ 3 := by
    exact (calc
        16384 * X ^ 2 < 16384 * (128 * (Q : ℝ) ^ 3) :=
          mul_lt_mul_of_pos_left hNotLow' (by norm_num)
        _ = ((2 ^ (q + 7) : ℕ) : ℝ) ^ 3 := by
          rw [hShift]
          push_cast
          ring).le
  have hHighRaw := hHigh (q + 7) T W hShiftThirty hT hSep hBase
    (by simpa only [X] using hCube)
  have hHighBound : heathBrownDyadicPairMoment (q + 7) W ≤
      B * T ^ (52 * η) *
        (128 * (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 + 1) := by
    rw [hShift] at hHighRaw
    push_cast at hHighRaw
    convert hHighRaw using 1
    ring
  have hTransferRaw := hTransfer q (q + 7) W (by omega)
  have hTransferBound : heathBrownDyadicPairMoment q W ≤
      8 * (A * ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η) ^ 2 *
        heathBrownDyadicPairMoment (q + 7) W := by
    simpa only [heathBrownDyadicPairMoment] using hTransferRaw
  have hFourReal : ((4 * Q : ℕ) : ℝ) ≤ T := by simpa only [Q] using hFourQ
  have hTSeven : (128 : ℝ) ≤ T ^ 7 := by
    calc
      (128 : ℝ) = (2 : ℝ) ^ 7 := by norm_num
      _ ≤ T ^ 7 := pow_le_pow_left₀ (by norm_num) hTTwo 7
  have h128T : 128 * T ≤ T ^ 8 := by
    calc
      128 * T ≤ T ^ 7 * T := mul_le_mul_of_nonneg_right hTSeven (by positivity)
      _ = T ^ 8 := by ring
  have hScaleBase : (4 : ℝ) * (2 ^ (q + 7) : ℕ) ≤ T ^ 8 := by
    calc
      (4 : ℝ) * (2 ^ (q + 7) : ℕ) = 128 * ((4 * Q : ℕ) : ℝ) := by
        rw [hShift]
        push_cast
        ring
      _ ≤ 128 * T := mul_le_mul_of_nonneg_left hFourReal (by norm_num)
      _ ≤ T ^ 8 := h128T
  have hScale : ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η ≤ T ^ (8 * η) := by
    calc
      _ ≤ (T ^ 8) ^ η := Real.rpow_le_rpow (by positivity) hScaleBase hη.le
      _ = T ^ (8 * η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        norm_num
  have hScaleSq : (A * ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η) ^ 2 ≤
      A ^ 2 * T ^ (16 * η) := by
    have hMul : A * ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η ≤
        A * T ^ (8 * η) := mul_le_mul_of_nonneg_left hScale hA.le
    have hLeftNonneg : 0 ≤ A * ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η := by positivity
    have hSq := pow_le_pow_left₀ hLeftNonneg hMul 2
    have hTpow : (T ^ (8 * η)) ^ 2 = T ^ (16 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (A * T ^ (8 * η)) ^ 2 := hSq
      _ = A ^ 2 * T ^ (16 * η) := by
        rw [mul_pow, hTpow]
  have hTarget :
      128 * (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 + 1 ≤ 128 * G := by
    dsimp only [G]
    have hCardSq : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hPowProduct : T ^ (16 * η) * T ^ (52 * η) = T ^ (68 * η) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hGNonneg : 0 ≤ G := by dsimp only [G]; positivity
  have hPairNonneg : 0 ≤ heathBrownDyadicPairMoment (q + 7) W := by
    dsimp only [heathBrownDyadicPairMoment]
    exact add_nonneg
      (heathBrownWeightedMoment_nonneg (2 ^ (q + 7)) W)
      (heathBrownWeightedMoment_nonneg (2 ^ (q + 7 + 1)) W)
  calc
    heathBrownDyadicPairMoment q W ≤
        8 * (A * ((4 : ℝ) * (2 ^ (q + 7) : ℕ)) ^ η) ^ 2 *
          heathBrownDyadicPairMoment (q + 7) W := hTransferBound
    _ ≤ 8 * (A ^ 2 * T ^ (16 * η)) *
        (B * T ^ (52 * η) *
          (128 * (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 + 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hScaleSq (by norm_num)) hHighBound
        hPairNonneg (by positivity)
    _ ≤ 8 * (A ^ 2 * T ^ (16 * η)) *
        (B * T ^ (52 * η) * (128 * G)) := by gcongr
    _ = C * T ^ (68 * η) * G := by
      dsimp only [C]
      rw [← hPowProduct]
      ring
    _ = _ := by rfl

private lemma rpow_five_four_mul_rpow_one_four (x : ℝ) (hx : 0 < x) :
    x ^ (5 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  calc
    x ^ (5 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hx]
      congr 1
      norm_num
    _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hx]
      congr 1
      norm_num
    _ = x * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]

private lemma rpow_half_mul_rpow_half (x : ℝ) (hx : 0 < x) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  calc
    _ = x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hx]
      congr 1
      norm_num
    _ = x := Real.rpow_one x

private lemma heathBrown_reciprocal_absorption
    {R T Q : ℝ} (hR : 0 < R) (hT : 0 < T) (hQ : 0 < Q)
    (hScale : R ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ Q) :
    R * Real.sqrt R * T / Q ≤
      R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
  apply (div_le_iff₀ hQ).2
  have hTargetNonneg : 0 ≤ R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
  have hMul := mul_le_mul_of_nonneg_left hScale hTargetNonneg
  calc
    R * Real.sqrt R * T =
        (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) *
          (R ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) := by
      rw [mul_mul_mul_comm, rpow_five_four_mul_rpow_one_four R hR,
        rpow_half_mul_rpow_half T hT]
    _ ≤ (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * Q := hMul
    _ = R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * Q := by ring

set_option maxHeartbeats 800000 in
/-- Large physical scales in Lemma 29.10.  The hypothesis is the literal
transition `|W|^(1/4) T^(1/2) ≤ Q`; in the medium branch it absorbs the
reciprocal dual length, while the complementary branch is returned through
the fixed seven-step high-range transfer. -/
theorem exists_heathBrownDyadicPairMoment_large_scale_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T → (4 * 2 ^ q : ℕ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W → 0 < W.card →
        (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ (2 ^ q : ℕ) →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (68 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
  obtain ⟨CM, TM, hCM, hTM, hMedium⟩ :=
    exists_heathBrownDyadicPairMoment_medium_bound cutoff η hη hηOne
  obtain ⟨CN, TN, hCN, hTN, hNonmedium⟩ :=
    exists_heathBrownDyadicPairMoment_nonmedium_bound cutoff η hη hηOne
  let C : ℝ := 4 * CM + CN
  let T₀ : ℝ := max TM TN
  refine ⟨C, T₀, by dsimp only [C]; positivity,
    hTM.trans (le_max_left _ _), ?_⟩
  intro q T W hQ hT hFourQ hSep hBase hWPos hScale
  let Q : ℕ := 2 ^ q
  let H : ℕ := heathBrownSmoothingHeight T η
  let R : ℝ := W.card
  let X : ℝ := T * (H : ℝ)
  let F : ℝ := R * Q + R ^ 2 + R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1
  have hTM' : TM ≤ T := (le_max_left TM TN).trans hT
  have hTN' : TN ≤ T := (le_max_right TM TN).trans hT
  have hTOne : 1 ≤ T := by linarith [hTM.trans hTM']
  have hTPos : 0 < T := by linarith
  have hQPos : 0 < Q := by dsimp only [Q]; positivity
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQPos
  have hRPos : 0 < R := by dsimp only [R]; exact_mod_cast hWPos
  have hRNonneg : 0 ≤ R := hRPos.le
  have hROne : 1 ≤ R := by dsimp only [R]; exact_mod_cast hWPos
  have hFNonneg : 0 ≤ F := by dsimp only [F]; positivity
  have hTPowOne : 1 ≤ T ^ η := Real.one_le_rpow hTOne hη.le
  have hHBound : (H : ℝ) ≤ 2 * T ^ η := by
    dsimp only [H]
    exact heathBrownSmoothingHeight_le_two_rpow hTOne hη.le
  have hScale' : R ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    simpa only [R, Q] using hScale
  have hReciprocal : R * Real.sqrt R * T / Q ≤
      R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) :=
    heathBrown_reciprocal_absorption hRPos hTPos hQReal hScale'
  have hSpecialNonneg :
      0 ≤ R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
  have hDual : R * Real.sqrt R * (X / Q) ≤
      2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) := by
    calc
      R * Real.sqrt R * (X / Q) =
          (R * Real.sqrt R * T / Q) * H := by
        dsimp only [X]
        field_simp
      _ ≤ (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * H :=
        mul_le_mul_of_nonneg_right hReciprocal (by positivity)
      _ ≤ (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * (2 * T ^ η) :=
        mul_le_mul_of_nonneg_left hHBound hSpecialNonneg
      _ = 2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) := by ring
  have hRLeSq : R ≤ R ^ 2 := by nlinarith
  have hSqrtR : Real.sqrt R ≤ R := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hRNonneg
    · exact hRLeSq
  have hRSqrt : R * Real.sqrt R ≤ R ^ 2 := by
    calc
      _ ≤ R * R := mul_le_mul_of_nonneg_left hSqrtR hRNonneg
      _ = R ^ 2 := by ring
  by_cases hLow : 128 * ((2 ^ q : ℕ) : ℝ) ^ 3 ≤
      (T * (heathBrownSmoothingHeight T η : ℝ)) ^ 2
  · have hRaw := hMedium q T W hQ hTM' hFourQ hSep hBase hLow
    have hRaw' : heathBrownDyadicPairMoment q W ≤
        CM * T ^ (60 * η) *
          (R * Q + R ^ 2 + R * Real.sqrt R * (X / Q + 1) + R + 1) := by
      simpa only [R, Q, H, X] using hRaw
    have hDualWhole : R * Real.sqrt R * (X / Q + 1) ≤
        2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) + R ^ 2 := by
      calc
        _ = R * Real.sqrt R * (X / Q) + R * Real.sqrt R := by ring
        _ ≤ 2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) +
            R ^ 2 := add_le_add hDual hRSqrt
    have hInside :
        R * Q + R ^ 2 + R * Real.sqrt R * (X / Q + 1) + R + 1 ≤
          4 * T ^ η * F := by
      have hExpanded :
          R * Q + R ^ 2 + R * Real.sqrt R * (X / Q + 1) + R + 1 ≤
            R * Q + 3 * R ^ 2 +
              2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) + 1 := by
        linarith [hDualWhole, hRLeSq]
      calc
        _ ≤ R * Q + 3 * R ^ 2 +
              2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) + 1 := hExpanded
        _ ≤ 4 * T ^ η * F := by
          have hU : 0 ≤ T ^ η := zero_le_one.trans hTPowOne
          have hA : 0 ≤ R * (Q : ℝ) := by positivity
          have hB : 0 ≤ R ^ 2 := sq_nonneg _
          have hUA := mul_nonneg (sub_nonneg.2 hTPowOne) hA
          have hUB := mul_nonneg (sub_nonneg.2 hTPowOne) hB
          calc
            R * Q + 3 * R ^ 2 +
                2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) + 1 ≤
              T ^ η * (R * Q) + 3 * T ^ η * R ^ 2 +
                2 * T ^ η * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) +
                T ^ η := by nlinarith
            _ ≤ 4 * T ^ η * F := by
              dsimp only [F]
              nlinarith [mul_nonneg hU hA, mul_nonneg hU hB,
                mul_nonneg hU hSpecialNonneg]
    have hPowProduct : T ^ (60 * η) * T ^ η = T ^ (61 * η) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    have hPow61 : T ^ (61 * η) ≤ T ^ (68 * η) :=
      Real.rpow_le_rpow_of_exponent_le hTOne (by nlinarith)
    calc
      _ ≤ CM * T ^ (60 * η) *
          (R * Q + R ^ 2 + R * Real.sqrt R * (X / Q + 1) + R + 1) := hRaw'
      _ ≤ CM * T ^ (60 * η) * (4 * T ^ η * F) := by gcongr
      _ = 4 * CM * T ^ (61 * η) * F := by rw [← hPowProduct]; ring
      _ ≤ 4 * CM * T ^ (68 * η) * F := by gcongr
      _ ≤ C * T ^ (68 * η) * F := by
        dsimp only [C]
        gcongr
        linarith [hCN]
      _ = _ := by rfl
  · have hRaw := hNonmedium q T W hQ hTN' hFourQ hSep hBase hLow
    have hSub :
        (W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1 ≤
          (W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 := by
      nlinarith [hSpecialNonneg]
    calc
      _ ≤ CN * T ^ (68 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 + 1) := hRaw
      _ ≤ CN * T ^ (68 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by gcongr
      _ ≤ C * T ^ (68 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
        dsimp only [C]
        gcongr
        nlinarith [hCM]

set_option maxHeartbeats 600000 in
/-- Total large-scale estimate.  Once `4Q` exceeds the height, the direct
Montgomery mean value is already of `|W|Q` size, so the physical transition
estimate remains valid without an artificial upper restriction on `Q`. -/
theorem exists_heathBrownDyadicPairMoment_large_scale_bound_total
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W → 0 < W.card →
        (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ (2 ^ q : ℕ) →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (68 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
  obtain ⟨C, T₀, hC, hT₀, hLarge⟩ :=
    exists_heathBrownDyadicPairMoment_large_scale_bound cutoff η hη hηOne
  let A₀ : ℝ := 3 * (2 + 2 * (5 * Real.pi + 1))
  let C' : ℝ := C + 19 * A₀
  refine ⟨C', T₀, by dsimp only [C', A₀]; positivity, hT₀, ?_⟩
  intro q T W hQ hT hSep hBase hWPos hScale
  let Q : ℕ := 2 ^ q
  let F : ℝ := (W.card : ℝ) * Q + (W.card : ℝ) ^ 2 +
    (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1
  have hTOne : 1 ≤ T := by linarith [hT₀.trans hT]
  have hTPow : 1 ≤ T ^ (68 * η) :=
    Real.one_le_rpow hTOne (by positivity)
  have hFNonneg : 0 ≤ F := by dsimp only [F]; positivity
  by_cases hBelow : ((4 * Q : ℕ) : ℝ) ≤ T
  · have hRaw := hLarge q T W hQ hT (by simpa only [Q] using hBelow)
      hSep hBase hWPos hScale
    calc
      _ ≤ C * T ^ (68 * η) * F := by simpa only [F, Q] using hRaw
      _ ≤ C' * T ^ (68 * η) * F := by
        dsimp only [C']
        gcongr
        have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
        linarith
      _ = _ := by rfl
  · have hQPos : 0 < Q := by dsimp only [Q]; positivity
    have hTwoQPos : 0 < 2 * Q := by omega
    have hTlt : T < (4 * Q : ℕ) := lt_of_not_ge hBelow
    have hDirect₀ := heathBrownWeightedMoment_direct_meanValue
      Q T W hQPos hTOne hSep hBase
    have hDirect₁ := heathBrownWeightedMoment_direct_meanValue
      (2 * Q) T W hTwoQPos hTOne hSep hBase
    have hFirst : heathBrownWeightedMoment Q W ≤
        9 * A₀ * (W.card : ℝ) * Q := by
      calc
        _ ≤ A₀ * (W.card : ℝ) * (2 * T + (Q : ℝ)) := by
          simpa only [A₀] using hDirect₀
        _ ≤ 9 * A₀ * (W.card : ℝ) * Q := by
          have hLength : 2 * T + (Q : ℝ) ≤ 9 * Q := by
            have hCast : T < 4 * (Q : ℝ) := by
              norm_num [Nat.cast_mul] at hTlt ⊢
              exact hTlt
            linarith
          calc
            _ ≤ A₀ * (W.card : ℝ) * (9 * Q) := by gcongr
            _ = _ := by ring
    have hSecond : heathBrownWeightedMoment (2 * Q) W ≤
        10 * A₀ * (W.card : ℝ) * Q := by
      calc
        _ ≤ A₀ * (W.card : ℝ) * (2 * T + (2 * Q : ℕ)) := by
          simpa only [A₀] using hDirect₁
        _ ≤ 10 * A₀ * (W.card : ℝ) * Q := by
          have hLength : 2 * T + ((2 * Q : ℕ) : ℝ) ≤ 10 * Q := by
            have hCast : T < 4 * (Q : ℝ) := by
              norm_num [Nat.cast_mul] at hTlt ⊢
              exact hTlt
            push_cast
            linarith
          calc
            _ ≤ A₀ * (W.card : ℝ) * (10 * Q) := by gcongr
            _ = _ := by ring
    have hTwoQ : 2 ^ (q + 1) = 2 * Q := by
      change 2 ^ (q + 1) = 2 * 2 ^ q
      exact pow_two_succ_eq_two_mul q
    have hPair : heathBrownDyadicPairMoment q W ≤
        19 * A₀ * (W.card : ℝ) * Q := by
      dsimp only [heathBrownDyadicPairMoment]
      rw [show 2 ^ q = Q by rfl, hTwoQ]
      calc
        _ ≤ 9 * A₀ * (W.card : ℝ) * Q +
            10 * A₀ * (W.card : ℝ) * Q := add_le_add hFirst hSecond
        _ = _ := by ring
    have hRQF : (W.card : ℝ) * Q ≤ F := by
      dsimp only [F]
      have hSq : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
      have hSpecial : 0 ≤
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
      linarith
    calc
      _ ≤ 19 * A₀ * (W.card : ℝ) * Q := hPair
      _ ≤ 19 * A₀ * F := by
        calc
          _ = 19 * A₀ * ((W.card : ℝ) * Q) := by ring
          _ ≤ _ := by gcongr
      _ ≤ 19 * A₀ * T ^ (68 * η) * F := by
        calc
          _ = 19 * A₀ * 1 * F := by ring
          _ ≤ _ := by gcongr
      _ ≤ C' * T ^ (68 * η) * F := by
        dsimp only [C']
        gcongr
        linarith [hC]
      _ = _ := by rfl

set_option maxHeartbeats 600000 in
/-- Exact dyadic target used in the small-scale part of Lemma 29.10.  The
target is the least power of two above the larger of `30` and the natural
ceiling of `|W|^(1/4) T^(1/2)`.  All rounding and ambient-height bounds are
recorded in one reusable package. -/
theorem heathBrown_large_scale_target_package
    {T : ℝ} {W : Finset ℝ} (hT : 36864 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    let A : ℝ := (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)
    let M : ℕ := max 30 (Nat.ceil A)
    let c : ℕ := Nat.clog 2 M
    30 ≤ 2 ^ c ∧ A ≤ (2 ^ c : ℕ) ∧
      ((2 ^ c : ℕ) : ℝ) ≤ 2 * (A + 31) ∧
      ((4 * 2 ^ c : ℕ) : ℝ) ≤ T ^ 5 := by
  let R : ℝ := W.card
  let A : ℝ := R ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)
  let P : ℕ := Nat.ceil A
  let M : ℕ := max 30 P
  let c : ℕ := Nat.clog 2 M
  have hTOne : 1 ≤ T := by linarith
  have hTTwo : 2 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hRNonneg : 0 ≤ R := by dsimp only [R]; positivity
  have hANonneg : 0 ≤ A := by dsimp only [A]; positivity
  have hM30 : 30 ≤ M := by dsimp only [M]; exact le_max_left _ _
  have hMPos : 0 < M := by omega
  have hMTarget : M ≤ 2 ^ c := by
    dsimp only [c]
    exact Nat.le_pow_clog Nat.one_lt_two M
  have hThirty : 30 ≤ 2 ^ c := hM30.trans hMTarget
  have hAP : A ≤ (P : ℝ) := by
    dsimp only [P]
    exact Nat.le_ceil A
  have hPM : P ≤ M := by dsimp only [M]; exact le_max_right _ _
  have hPMLift : (P : ℝ) ≤ M := by exact_mod_cast hPM
  have hMTargetLift : (M : ℝ) ≤ (2 ^ c : ℕ) := by exact_mod_cast hMTarget
  have hLower : A ≤ ((2 ^ c : ℕ) : ℝ) := hAP.trans (hPMLift.trans hMTargetLift)
  have hCeilUpper : (P : ℝ) ≤ A + 1 := by
    dsimp only [P]
    exact (Nat.ceil_lt_add_one hANonneg).le
  have hMNatUpper : M ≤ 30 + P := by
    dsimp only [M]
    exact max_le (by omega) (by omega)
  have hMRealUpper : (M : ℝ) ≤ 30 + P := by exact_mod_cast hMNatUpper
  have hMUpper : (M : ℝ) ≤ A + 31 := by
    push_cast at hMRealUpper
    linarith
  have hTargetNatUpper : 2 ^ c ≤ 2 * M := by
    dsimp only [c]
    exact pow_clog_two_le_two_mul M hMPos
  have hTargetRealUpper : ((2 ^ c : ℕ) : ℝ) ≤ 2 * (A + 31) := by
    have hCast : ((2 ^ c : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast hTargetNatUpper
    calc
      _ ≤ 2 * (M : ℝ) := by simpa using hCast
      _ ≤ 2 * (A + 31) := mul_le_mul_of_nonneg_left hMUpper (by norm_num)
  have hCard : R ≤ 2 * T := by
    dsimp only [R]
    exact gmSeparated_card_le_two_height hTOne hSep hBase
  have hTwoT : 2 * T ≤ T ^ 2 := by nlinarith
  have hRootR : R ^ (1 / 4 : ℝ) ≤ (2 * T) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hRNonneg hCard (by norm_num)
  have hRootTwoT : (2 * T) ^ (1 / 4 : ℝ) ≤ (T ^ 2) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hTwoT (by norm_num)
  have hPowerQuarter : (T ^ 2) ^ (1 / 4 : ℝ) = T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
    congr 1
    norm_num
  have hRoot : R ^ (1 / 4 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
    hRootR.trans (hRootTwoT.trans_eq hPowerQuarter)
  have hAUpper : A ≤ T := by
    calc
      A ≤ T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
        dsimp only [A]
        gcongr
      _ = T := rpow_half_mul_rpow_half T hTPos
  have hTargetFour : ((2 ^ c : ℕ) : ℝ) ≤ 4 * T := by
    calc
      _ ≤ 2 * (A + 31) := hTargetRealUpper
      _ ≤ 4 * T := by linarith
  have hTFour : (16 : ℝ) ≤ T ^ 4 := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ T ^ 4 := pow_le_pow_left₀ (by norm_num) hTTwo 4
  have hFourTarget : ((4 * 2 ^ c : ℕ) : ℝ) ≤ T ^ 5 := by
    calc
      ((4 * 2 ^ c : ℕ) : ℝ) = 4 * ((2 ^ c : ℕ) : ℝ) := by push_cast; ring
      _ ≤ 16 * T := by
        calc
          4 * ((2 ^ c : ℕ) : ℝ) ≤ 4 * (4 * T) :=
            mul_le_mul_of_nonneg_left hTargetFour (by norm_num)
          _ = 16 * T := by ring
      _ ≤ T ^ 4 * T := mul_le_mul_of_nonneg_right hTFour (by positivity)
      _ = T ^ 5 := by ring
  dsimp only
  exact ⟨hThirty, hLower, hTargetRealUpper, hFourTarget⟩

private lemma rpow_one_mul_rpow_one_four (x : ℝ) (hx : 0 < x) :
    x * x ^ (1 / 4 : ℝ) = x ^ (5 / 4 : ℝ) := by
  calc
    x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + 1 / 4) := by rw [Real.rpow_add hx]
    _ = x ^ (5 / 4 : ℝ) := by norm_num

set_option maxHeartbeats 800000 in
/-- Small physical scales in Lemma 29.10.  The adjacent pair is transferred
to the exact `Nat.clog` target above `|W|^(1/4)T^(1/2)`, where the total
large-scale theorem applies.  The target's rounding loss is absorbed into
the same three source terms. -/
theorem exists_heathBrownDyadicPairMoment_small_scale_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W → 0 < W.card →
        ((2 ^ q : ℕ) : ℝ) <
          (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (78 * η) *
            ((W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
  obtain ⟨A, hA, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_pair_le_common_target η hη
  obtain ⟨B, T₀, hB, hT₀, hLarge⟩ :=
    exists_heathBrownDyadicPairMoment_large_scale_bound_total cutoff η hη hηOne
  let C : ℝ := 512 * A ^ 2 * B
  refine ⟨C, T₀, by dsimp only [C]; positivity, hT₀, ?_⟩
  intro q T W hQ hT hSep hBase hWPos hSmall
  let R : ℝ := W.card
  let Y : ℝ := R ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)
  let M : ℕ := max 30 (Nat.ceil Y)
  let c : ℕ := Nat.clog 2 M
  let F : ℝ := R ^ 2 + R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1
  have hT36864 : 36864 ≤ T := hT₀.trans hT
  have hTPos : 0 < T := by linarith
  have hTargetData := heathBrown_large_scale_target_package
    hT36864 hSep hBase
  dsimp only at hTargetData
  have hTargetData' : 30 ≤ 2 ^ c ∧ Y ≤ (2 ^ c : ℕ) ∧
      ((2 ^ c : ℕ) : ℝ) ≤ 2 * (Y + 31) ∧
      ((4 * 2 ^ c : ℕ) : ℝ) ≤ T ^ 5 := by
    simpa only [R, Y, M, c] using hTargetData
  rcases hTargetData' with ⟨hTargetThirty, hTargetLower, hTargetUpper, hTargetPower⟩
  have hSmall' : ((2 ^ q : ℕ) : ℝ) < Y := by simpa only [R, Y] using hSmall
  have hPowLt : 2 ^ q < 2 ^ c := by exact_mod_cast hSmall'.trans_le hTargetLower
  have hqc : q + 1 ≤ c := by
    have hqc' : q < c := (Nat.pow_lt_pow_iff_right (by omega)).1 hPowLt
    omega
  have hTransferRaw := hTransfer q c W hqc
  have hTransferBound : heathBrownDyadicPairMoment q W ≤
      8 * (A * ((4 : ℝ) * (2 ^ c : ℕ)) ^ η) ^ 2 *
        heathBrownDyadicPairMoment c W := by
    simpa only [heathBrownDyadicPairMoment] using hTransferRaw
  have hLargeRaw := hLarge c T W hTargetThirty hT hSep hBase hWPos
    (by simpa only [R, Y] using hTargetLower)
  have hLargeBound : heathBrownDyadicPairMoment c W ≤
      B * T ^ (68 * η) *
        (R * (2 ^ c : ℕ) + R ^ 2 +
          R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
    simpa only [R] using hLargeRaw
  have hScale : ((4 : ℝ) * (2 ^ c : ℕ)) ^ η ≤ T ^ (5 * η) := by
    calc
      _ ≤ (T ^ 5) ^ η :=
        Real.rpow_le_rpow (by positivity) (by simpa only [Nat.cast_mul,
          Nat.cast_ofNat] using hTargetPower) hη.le
      _ = T ^ (5 * η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        norm_num
  have hScaleSq : (A * ((4 : ℝ) * (2 ^ c : ℕ)) ^ η) ^ 2 ≤
      A ^ 2 * T ^ (10 * η) := by
    have hMul := mul_le_mul_of_nonneg_left hScale hA.le
    have hSq := pow_le_pow_left₀
      (show 0 ≤ A * ((4 : ℝ) * (2 ^ c : ℕ)) ^ η by positivity) hMul 2
    have hTpow : (T ^ (5 * η)) ^ 2 = T ^ (10 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (A * T ^ (5 * η)) ^ 2 := hSq
      _ = A ^ 2 * T ^ (10 * η) := by rw [mul_pow, hTpow]
  have hRPos : 0 < R := by dsimp only [R]; exact_mod_cast hWPos
  have hROne : 1 ≤ R := by dsimp only [R]; exact_mod_cast hWPos
  have hRLeSq : R ≤ R ^ 2 := by nlinarith
  have hRY : R * Y = R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
    dsimp only [Y]
    rw [← mul_assoc, rpow_one_mul_rpow_one_four R hRPos]
  have hTargetTerm : R * (2 ^ c : ℕ) ≤
      2 * (R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) + 62 * R := by
    calc
      _ ≤ R * (2 * (Y + 31)) :=
        mul_le_mul_of_nonneg_left hTargetUpper hRPos.le
      _ = 2 * (R * Y) + 62 * R := by ring
      _ = _ := by rw [hRY]
  have hFNonneg : 0 ≤ F := by dsimp only [F]; positivity
  have hLargeInside :
      R * (2 ^ c : ℕ) + R ^ 2 +
          R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 ≤ 64 * F := by
    dsimp only [F]
    nlinarith [hTargetTerm]
  have hPairNonneg : 0 ≤ heathBrownDyadicPairMoment c W := by
    dsimp only [heathBrownDyadicPairMoment]
    exact add_nonneg (heathBrownWeightedMoment_nonneg (2 ^ c) W)
      (heathBrownWeightedMoment_nonneg (2 ^ (c + 1)) W)
  have hPowProduct : T ^ (10 * η) * T ^ (68 * η) = T ^ (78 * η) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  calc
    _ ≤ 8 * (A * ((4 : ℝ) * (2 ^ c : ℕ)) ^ η) ^ 2 *
        heathBrownDyadicPairMoment c W := hTransferBound
    _ ≤ 8 * (A ^ 2 * T ^ (10 * η)) *
        (B * T ^ (68 * η) *
          (R * (2 ^ c : ℕ) + R ^ 2 +
            R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hScaleSq (by norm_num)) hLargeBound
        hPairNonneg (by positivity)
    _ ≤ 8 * (A ^ 2 * T ^ (10 * η)) *
        (B * T ^ (68 * η) * (64 * F)) := by gcongr
    _ = C * T ^ (78 * η) * F := by
      dsimp only [C]
      rw [← hPowProduct]
      ring
    _ = _ := by rfl

set_option maxHeartbeats 600000 in
/-- Montgomery--Vaughan Lemma 29.10 for every dyadic source scale at least
`30`, with its three source terms and an adjacent-pair left side. -/
theorem exists_heathBrownDyadicPairMoment_ge_thirty_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ),
        30 ≤ 2 ^ q → T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
  obtain ⟨CL, TL, hCL, hTL, hLarge⟩ :=
    exists_heathBrownDyadicPairMoment_large_scale_bound_total cutoff η hη hηOne
  obtain ⟨CS, TS, hCS, hTS, hSmall⟩ :=
    exists_heathBrownDyadicPairMoment_small_scale_bound cutoff η hη hηOne
  let C : ℝ := CL + CS
  let T₀ : ℝ := max TL TS
  refine ⟨C, T₀, by dsimp only [C]; positivity,
    hTL.trans (le_max_left _ _), ?_⟩
  intro q T W hQ hT hSep hBase
  have hTL' : TL ≤ T := (le_max_left TL TS).trans hT
  have hTS' : TS ≤ T := (le_max_right TL TS).trans hT
  have hTOne : 1 ≤ T := by linarith [hTL.trans hTL']
  have hTPos : 0 < T := by linarith
  have hPow : T ^ (68 * η) ≤ T ^ (78 * η) :=
    Real.rpow_le_rpow_of_exponent_le hTOne (by nlinarith)
  by_cases hWZero : W.card = 0
  · have hWEmpty : W = ∅ := Finset.card_eq_zero.mp hWZero
    subst W
    have hCNonneg : 0 ≤ C := by
      dsimp only [C]
      linarith
    have hRpowNonneg : 0 ≤ T ^ (78 * η) := Real.rpow_nonneg hTPos.le _
    have hProductNonneg : 0 ≤ C * T ^ (78 * η) :=
      mul_nonneg hCNonneg hRpowNonneg
    simpa [heathBrownDyadicPairMoment, heathBrownWeightedMoment] using hProductNonneg
  · have hWPos : 0 < W.card := Nat.pos_of_ne_zero hWZero
    by_cases hTransition :
        (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) ≤ (2 ^ q : ℕ)
    · have hRaw := hLarge q T W hQ hTL' hSep hBase hWPos hTransition
      calc
        _ ≤ CL * T ^ (68 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := hRaw
        _ ≤ CL * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by gcongr
        _ ≤ C * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
          dsimp only [C]
          gcongr
          linarith [hCS]
    · have hTransition' : ((2 ^ q : ℕ) : ℝ) <
          (W.card : ℝ) ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := lt_of_not_ge hTransition
      have hRaw := hSmall q T W hQ hTS' hSep hBase hWPos hTransition'
      have hSub :
          (W.card : ℝ) ^ 2 +
                (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 ≤
            (W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
                (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 := by
        have hRQ : 0 ≤ (W.card : ℝ) * (2 ^ q : ℕ) := by positivity
        linarith
      calc
        _ ≤ CS * T ^ (78 * η) *
            ((W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := hRaw
        _ ≤ CS * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by gcongr
        _ ≤ C * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
          dsimp only [C]
          gcongr
          linarith [hCL]

set_option maxHeartbeats 600000 in
/-- Montgomery--Vaughan Lemma 29.10 on every dyadic scale.  The finitely
many scales below `30` are moved exactly five dyadic steps upward, so the
source interval is still controlled by two adjacent terminal blocks. -/
theorem exists_heathBrownDyadicPairMoment_all_scales_bound
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (hηOne : η ≤ 1) :
    ∃ C T₀ : ℝ, 0 < C ∧ 36864 ≤ T₀ ∧
      ∀ (q : ℕ) (T : ℝ) (W : Finset ℝ), T₀ ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        heathBrownDyadicPairMoment q W ≤
          C * T ^ (80 * η) *
            ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
  obtain ⟨A, hA, hTransfer⟩ :=
    exists_heathBrownWeightedMoment_pair_le_common_target η hη
  obtain ⟨B, T₀, hB, hT₀, hThirty⟩ :=
    exists_heathBrownDyadicPairMoment_ge_thirty_bound cutoff η hη hηOne
  let Csmall : ℝ := 256 * A ^ 2 * B
  let C : ℝ := B + Csmall
  refine ⟨C, T₀, by dsimp only [C, Csmall]; positivity, hT₀, ?_⟩
  intro q T W hT hSep hBase
  have hT36864 : 36864 ≤ T := hT₀.trans hT
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hPow7880 : T ^ (78 * η) ≤ T ^ (80 * η) :=
    Real.rpow_le_rpow_of_exponent_le hTOne (by nlinarith)
  by_cases hQ : 30 ≤ 2 ^ q
  · have hRaw := hThirty q T W hQ hT hSep hBase
    have hFactorNonneg : 0 ≤
        (W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 := by
      positivity
    calc
      _ ≤ B * T ^ (78 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := hRaw
      _ ≤ B * T ^ (80 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
        gcongr
      _ ≤ C * T ^ (80 * η) *
          ((W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
        dsimp only [C]
        have hPowNonneg : 0 ≤ T ^ (80 * η) := Real.rpow_nonneg hTPos.le _
        have hCsmallNonneg : 0 ≤ Csmall := by dsimp only [Csmall]; positivity
        nlinarith [mul_nonneg hPowNonneg hFactorNonneg,
          mul_nonneg hCsmallNonneg (mul_nonneg hPowNonneg hFactorNonneg)]
  · have hQLt : 2 ^ q < 30 := Nat.lt_of_not_ge hQ
    have hShift : 2 ^ (q + 5) = 32 * 2 ^ q := by
      rw [pow_add]
      norm_num
      omega
    have hShiftThirty : 30 ≤ 2 ^ (q + 5) := by
      rw [hShift]
      have hPowPositive : 0 < 2 ^ q := by positivity
      omega
    have hTransferRaw := hTransfer q (q + 5) W (by omega)
    have hTransferBound : heathBrownDyadicPairMoment q W ≤
        8 * (A * ((4 : ℝ) * (2 ^ (q + 5) : ℕ)) ^ η) ^ 2 *
          heathBrownDyadicPairMoment (q + 5) W := by
      simpa only [heathBrownDyadicPairMoment] using hTransferRaw
    have hTargetRaw := hThirty (q + 5) T W hShiftThirty hT hSep hBase
    have hScaleNat : 4 * 2 ^ (q + 5) ≤ 3840 := by
      rw [hShift]
      omega
    have hScaleReal : (4 : ℝ) * (2 ^ (q + 5) : ℕ) ≤ T := by
      calc
        (4 : ℝ) * (2 ^ (q + 5) : ℕ) = ((4 * 2 ^ (q + 5) : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ 3840 := by exact_mod_cast hScaleNat
        _ ≤ T := by linarith
    have hScale : ((4 : ℝ) * (2 ^ (q + 5) : ℕ)) ^ η ≤ T ^ η :=
      Real.rpow_le_rpow (by positivity) hScaleReal hη.le
    have hScaleSq :
        (A * ((4 : ℝ) * (2 ^ (q + 5) : ℕ)) ^ η) ^ 2 ≤
          A ^ 2 * T ^ (2 * η) := by
      have hMul := mul_le_mul_of_nonneg_left hScale hA.le
      have hSq := pow_le_pow_left₀
        (show 0 ≤ A * ((4 : ℝ) * (2 ^ (q + 5) : ℕ)) ^ η by positivity)
        hMul 2
      calc
        _ ≤ (A * T ^ η) ^ 2 := hSq
        _ = A ^ 2 * T ^ (2 * η) := by
          rw [mul_pow, pow_two (T ^ η), ← Real.rpow_add hTPos]
          congr 2
          ring
    let F : ℝ := (W.card : ℝ) * (2 ^ q : ℕ) + (W.card : ℝ) ^ 2 +
      (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1
    have hTargetInside :
        (W.card : ℝ) * (2 ^ (q + 5) : ℕ) + (W.card : ℝ) ^ 2 +
            (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 ≤
          32 * F := by
      have hCardNonneg : 0 ≤ (W.card : ℝ) := by positivity
      have hSqNonneg : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
      have hFracNonneg : 0 ≤
          (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
      dsimp only [F]
      rw [hShift]
      push_cast
      nlinarith
    have hPairNonneg : 0 ≤ heathBrownDyadicPairMoment (q + 5) W := by
      dsimp only [heathBrownDyadicPairMoment]
      exact add_nonneg (heathBrownWeightedMoment_nonneg _ _)
        (heathBrownWeightedMoment_nonneg _ _)
    have hPowProduct : T ^ (2 * η) * T ^ (78 * η) = T ^ (80 * η) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    calc
      _ ≤ 8 * (A * ((4 : ℝ) * (2 ^ (q + 5) : ℕ)) ^ η) ^ 2 *
          heathBrownDyadicPairMoment (q + 5) W := hTransferBound
      _ ≤ 8 * (A ^ 2 * T ^ (2 * η)) *
          (B * T ^ (78 * η) *
            ((W.card : ℝ) * (2 ^ (q + 5) : ℕ) + (W.card : ℝ) ^ 2 +
              (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hScaleSq (by norm_num)) hTargetRaw
          hPairNonneg (by positivity)
      _ ≤ 8 * (A ^ 2 * T ^ (2 * η)) *
          (B * T ^ (78 * η) * (32 * F)) := by gcongr
      _ = Csmall * T ^ (80 * η) * F := by
        dsimp only [Csmall]
        rw [← hPowProduct]
        ring
      _ ≤ C * T ^ (80 * η) * F := by
        dsimp only [C]
        have hPowNonneg : 0 ≤ T ^ (80 * η) := Real.rpow_nonneg hTPos.le _
        have hFNonneg : 0 ≤ F := by dsimp only [F]; positivity
        nlinarith [mul_nonneg hB.le (mul_nonneg hPowNonneg hFNonneg)]
      _ = _ := by rfl

set_option maxHeartbeats 600000 in
/-- The arbitrary-scale weighted form of Heath--Brown's Theorem 1.6.
The dyadic scale is chosen below `N`; the complete source interval is then
contained in two adjacent dyadic blocks, and the harmless constant term is
absorbed by the nonempty-set `|W|²` contribution. -/
theorem heathBrownWeightedMeanSquare_of_cutoff
    (cutoff : GMSmoothCutoff) : HeathBrownWeightedMeanSquare := by
  intro ε hε
  let η : ℝ := min (ε / 80) 1
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  have hηOne : η ≤ 1 := by
    dsimp only [η]
    exact min_le_right _ _
  have hExponent : 80 * η ≤ ε := by
    have hηLe : η ≤ ε / 80 := by
      dsimp only [η]
      exact min_le_left _ _
    nlinarith
  obtain ⟨C, T₀, hC, hT₀, hPair⟩ :=
    exists_heathBrownDyadicPairMoment_all_scales_bound cutoff η hη hηOne
  refine ⟨4 * C, T₀, by positivity, by linarith, ?_⟩
  intro N T W hN hT hSep hBase
  have hTOne : 1 ≤ T := by linarith [hT₀.trans hT]
  have hTPos : 0 < T := by linarith
  have hPower : T ^ (80 * η) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  by_cases hWZero : W.card = 0
  · have hWEmpty : W = ∅ := Finset.card_eq_zero.mp hWZero
    subst W
    simp [heathBrownWeightedMoment]
  · let q : ℕ := Nat.log 2 N
    let M : ℕ := 2 ^ q
    have hNNe : N ≠ 0 := Nat.ne_of_gt hN
    have hMN : M ≤ N := by
      dsimp only [M, q]
      exact Nat.pow_log_le_self 2 hNNe
    have hNMSucc : N < 2 ^ (q + 1) := by
      dsimp only [q]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two N
    have hNM : N ≤ 2 * M := by
      have hPowSucc : 2 ^ (q + 1) = 2 * M := by
        dsimp only [M]
        rw [pow_succ]
        omega
      rw [← hPowSucc]
      exact hNMSucc.le
    have hCover := heathBrownWeightedMoment_le_two_adjacent_of_comparable
      W hMN hNM
    have hCover' : heathBrownWeightedMoment N W ≤
        2 * heathBrownDyadicPairMoment q W := by
      simpa only [heathBrownDyadicPairMoment, M, pow_succ, mul_comm] using hCover
    have hPairBound := hPair q T W hT hSep hBase
    let R : ℝ := W.card
    let D : ℝ := R ^ 2 + R * N +
      R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)
    have hRPos : 0 < R := by
      dsimp only [R]
      exact_mod_cast Nat.pos_of_ne_zero hWZero
    have hROne : 1 ≤ R := by
      dsimp only [R]
      exact_mod_cast Nat.pos_of_ne_zero hWZero
    have hMReal : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hRM : R * M ≤ R * N :=
      mul_le_mul_of_nonneg_left hMReal hRPos.le
    have hOneSq : 1 ≤ R ^ 2 := by nlinarith
    have hDNonneg : 0 ≤ D := by dsimp only [D]; positivity
    have hRNNonneg : 0 ≤ R * (N : ℝ) := by positivity
    have hTailNonneg : 0 ≤
        R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
    have hBracket :
        R * M + R ^ 2 + R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1 ≤
          2 * D := by
      dsimp only [D]
      linarith
    have hPairBound' : heathBrownDyadicPairMoment q W ≤
        C * T ^ (80 * η) * (2 * D) := by
      calc
        _ ≤ C * T ^ (80 * η) *
            (R * M + R ^ 2 +
              R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) + 1) := by
          simpa only [R, M] using hPairBound
        _ ≤ C * T ^ (80 * η) * (2 * D) := by gcongr
    calc
      heathBrownWeightedMoment N W ≤
          2 * heathBrownDyadicPairMoment q W := hCover'
      _ ≤ 2 * (C * T ^ (80 * η) * (2 * D)) :=
        mul_le_mul_of_nonneg_left hPairBound' (by norm_num)
      _ = (4 * C) * T ^ (80 * η) * D := by ring
      _ ≤ (4 * C) * T ^ ε * D := by gcongr
      _ = (4 * C) * T ^ ε *
          (((W.card : ℝ) ^ 2) + ((W.card : ℝ) * N) +
            ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ))) := by rfl

/-- Native weighted Heath--Brown theorem, obtained from the explicitly
constructed project cutoff and the complete dyadic recurrence. -/
theorem heathBrownWeightedMeanSquare_native : HeathBrownWeightedMeanSquare := by
  exact heathBrownWeightedMeanSquare_of_cutoff
    (Classical.choice exists_gmSmoothCutoff)

/-- Native coefficient-one Heath--Brown theorem. -/
theorem heathBrownCoefficientOneMeanSquare_native :
    HeathBrownCoefficientOneMeanSquare :=
  heathBrownCoefficientOneMeanSquare_of_weighted
    heathBrownWeightedMeanSquare_native

/-- Native source-facing Heath--Brown Theorem 1.6 for arbitrary
unit-bounded coefficients. -/
theorem heathBrownDifferenceSetMeanSquare_native :
    HeathBrownDifferenceSetMeanSquare :=
  heathBrownDifferenceSetMeanSquare_of_coefficientOne
    heathBrownCoefficientOneMeanSquare_native

end RiemannZeta.GuthMaynard
