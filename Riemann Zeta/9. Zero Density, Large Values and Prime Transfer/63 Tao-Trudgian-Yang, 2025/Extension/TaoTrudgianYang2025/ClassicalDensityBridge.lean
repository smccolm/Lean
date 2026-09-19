import TaoTrudgianYang2025.ZeroDensityExponent
import GuthMaynard.Asymptotics
import GuthMaynard.NativeZeroDensity

/-!
# Classical density bridges

This module converts the local `EpsilonPowerBound` convention into the
paper's shifted zero-density predicate. The analytic Ingham, Huxley, and
Guth--Maynard estimates are imported from their native local proofs; their
rational shift calculations are instantiated below this common adapter.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- Convert a family of local epsilon-power estimates at `σ-δ` into the
paper's non-asymptotic density predicate at `σ`. -/
theorem isZeroDensityBound_of_shiftedEpsilonPowerBound
    {σ A : ℝ} {q : ℝ → ℝ}
    (hsource : ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        EpsilonPowerBound
          (fun T ↦ (paperZeroCount (σ - δ) T : ℝ))
          (fun T ↦ T ^ q δ) ∧
        q δ ≤ A * (1 - σ) + ε / 2) :
    IsZeroDensityBound σ A := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal, hq⟩ := hsource ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨K, hKpos, hK⟩ := (hlocal (ε / 2) hhalf).exists_pos
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hK.bound
  let C : ℝ := max 1 (max K T₀)
  have hCone : 1 ≤ C := le_max_left _ _
  have hKC : K ≤ C := (le_max_left K T₀).trans (le_max_right 1 _)
  have hT₀C : T₀ ≤ C := (le_max_right K T₀).trans (le_max_right 1 _)
  refine ⟨C, hCone, δ, hδ, ?_⟩
  intro T hCT
  have hTone : 1 ≤ T := hCone.trans hCT
  have hi := hT₀ T (hT₀C.trans hCT)
  have hcountNonneg : 0 ≤ (paperZeroCount (σ - δ) T : ℝ) :=
    Nat.cast_nonneg _
  have hi' :
      (paperZeroCount (σ - δ) T : ℝ) ≤
        K * (T ^ (ε / 2) * T ^ q δ) := by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg hcountNonneg,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hTone) _)] using hi
  calc
    (paperZeroCount (σ - δ) T : ℝ) ≤
        K * (T ^ (ε / 2) * T ^ q δ) := hi'
    _ ≤ C * (T ^ (ε / 2) * T ^ q δ) := by
      exact mul_le_mul_of_nonneg_right hKC
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hTone) _)
          (Real.rpow_nonneg (zero_le_one.trans hTone) _))
    _ = C * T ^ (q δ + ε / 2) := by
      rw [add_comm, Real.rpow_add (zero_lt_one.trans_le hTone)]
    _ ≤ C * T ^ (A * (1 - σ) + ε) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hCone)
      apply Real.rpow_le_rpow_of_exponent_le hTone
      linarith

/-- A continuity-based form of the shift adapter.  The positive radius `d`
keeps the shifted parameter inside the range of the imported estimate. -/
theorem isZeroDensityBound_of_continuous_shift
    {σ A d : ℝ} {q : ℝ → ℝ}
    (hd : 0 < d)
    (hsource : ∀ δ : ℝ, 0 < δ → δ < d →
      EpsilonPowerBound
        (fun T ↦ (paperZeroCount (σ - δ) T : ℝ))
        (fun T ↦ T ^ q δ))
    (hq : ContinuousAt q 0)
    (hqzero : q 0 = A * (1 - σ)) :
    IsZeroDensityBound σ A := by
  apply isZeroDensityBound_of_shiftedEpsilonPowerBound
  intro ε hε
  obtain ⟨η, hη, hclose⟩ :=
    (Metric.continuousAt_iff.1 hq) (ε / 2) (by linarith)
  let δ : ℝ := min d η / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hd hη) (by norm_num)
  have hδd : δ < d := by
    dsimp [δ]
    have hmin : min d η ≤ d := min_le_left _ _
    nlinarith [lt_min hd hη]
  have hδη : δ < η := by
    dsimp [δ]
    have hmin : min d η ≤ η := min_le_right _ _
    nlinarith [lt_min hd hη]
  have hdist : dist δ 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact hδη
  have hqclose := hclose hdist
  rw [Real.dist_eq, hqzero, abs_lt] at hqclose
  refine ⟨δ, hδ, hsource δ hδ hδd, ?_⟩
  linarith

/-- Ingham's native estimate in the paper's shifted density convention. -/
theorem ingham_isZeroDensityBound {σ : ℝ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ ≤ 1) :
    IsZeroDensityBound σ (3 / (2 - σ)) := by
  let q : ℝ → ℝ := fun δ ↦
    3 * (1 - (σ - δ)) / (2 - (σ - δ))
  apply isZeroDensityBound_of_continuous_shift
      (d := σ - 1 / 2) (q := q)
  · linarith
  · intro δ hδ hδRange
    simpa [q, paperZeroCount_eq_localN] using
      ingham_zero_density_native (σ - δ) (by linarith) (by linarith)
  · dsimp [q]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
      linarith
  · dsimp [q]
    field_simp
    ring

/-- Huxley's native estimate in the paper's shifted density convention. -/
theorem huxley_isZeroDensityBound {σ : ℝ}
    (hσLower : 3 / 4 < σ) (hσUpper : σ ≤ 1) :
    IsZeroDensityBound σ (3 / (3 * σ - 1)) := by
  let q : ℝ → ℝ := fun δ ↦
    3 * (1 - (σ - δ)) / (3 * (σ - δ) - 1)
  apply isZeroDensityBound_of_continuous_shift
      (d := σ - 3 / 4) (q := q)
  · linarith
  · intro δ hδ hδRange
    simpa [q, paperZeroCount_eq_localN] using
      huxley_zero_density_native (σ - δ) (by linarith) (by linarith)
  · dsimp [q]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
      linarith
  · dsimp [q]
    field_simp
    ring

/-- The native Guth--Maynard estimate in the paper's shifted density
convention. -/
theorem guthMaynard_isZeroDensityBound {σ : ℝ}
    (hσLower : 7 / 10 < σ) (hσUpper : σ ≤ 1) :
    IsZeroDensityBound σ (15 / (3 + 5 * σ)) := by
  let q : ℝ → ℝ := fun δ ↦
    15 * (1 - (σ - δ)) / (3 + 5 * (σ - δ))
  apply isZeroDensityBound_of_continuous_shift
      (d := σ - 7 / 10) (q := q)
  · linarith
  · intro δ hδ hδRange
    simpa [q, paperZeroCount_eq_localN] using
      guthMaynardZeroDensity_native (σ - δ) (by linarith) (by linarith)
  · dsimp [q]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
      linarith
  · dsimp [q]
    ring

/-- Huxley's lower endpoint is supplied by Ingham, where the two rational
coefficients agree. -/
theorem huxley_isZeroDensityBound_inclusive {σ : ℝ}
    (hσLower : 3 / 4 ≤ σ) (hσUpper : σ ≤ 1) :
    IsZeroDensityBound σ (3 / (3 * σ - 1)) := by
  rcases hσLower.eq_or_lt with rfl | hσLower
  · convert
      (ingham_isZeroDensityBound (σ := (3 / 4 : ℝ)) (by norm_num) (by norm_num)) using 1
    norm_num
  · exact huxley_isZeroDensityBound hσLower hσUpper

/-- The Guth--Maynard lower endpoint is likewise supplied by Ingham; both
coefficients are `30/13` there. -/
theorem guthMaynard_isZeroDensityBound_inclusive {σ : ℝ}
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 1) :
    IsZeroDensityBound σ (15 / (3 + 5 * σ)) := by
  rcases hσLower.eq_or_lt with rfl | hσLower
  · convert
      (ingham_isZeroDensityBound (σ := (7 / 10 : ℝ)) (by norm_num) (by norm_num)) using 1
    norm_num
  · exact guthMaynard_isZeroDensityBound hσLower hσUpper

theorem zeroDensityExponent_le_ingham {σ : ℝ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3 / (2 - σ) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound (ingham_isZeroDensityBound hσLower hσUpper)

theorem zeroDensityExponent_le_huxley {σ : ℝ}
    (hσLower : 3 / 4 ≤ σ) (hσUpper : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((3 / (3 * σ - 1) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound
    (huxley_isZeroDensityBound_inclusive hσLower hσUpper)

theorem zeroDensityExponent_le_guthMaynard {σ : ℝ}
    (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((15 / (3 + 5 * σ) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound
    (guthMaynard_isZeroDensityBound_inclusive hσLower hσUpper)

end TaoTrudgianYang2025
