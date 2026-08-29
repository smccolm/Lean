import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.ScaledSeparated
import RiemannZeta.GuthMaynard.TypeIIContour

open Asymptotics Filter MeasureTheory Topology
open Complex Finset
open scoped BigOperators Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# Native Type-II fourth-moment reduction

This module implements Maynard--Pratt Lemma 24 for the concrete finite zeta
zero family.  The first layer below performs the multiplicity-preserving
selection of separated ordinates.
-/

/-- The `contourTypeIIZeroSet` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def contourTypeIIZeroSet (σ T : ℝ) : Finset ℂ :=
  (dyadicZetaZeros σ T).filter (zetaIsContourTypeII T)

/-- The `contourTypeIIOrdinates` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def contourTypeIIOrdinates (σ T : ℝ) : Finset ℝ :=
  (contourTypeIIZeroSet σ T).image Complex.im

/-- The `contourTypeIIOrdinateWeight` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def contourTypeIIOrdinateWeight (σ T u : ℝ) : ℕ :=
  ∑ ρ ∈ (contourTypeIIZeroSet σ T).filter (fun z => z.im = u),
    analyticVanishingOrder riemannZeta ρ

/-- The `zeroUnitJensenMajorant` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def zeroUnitJensenMajorant (T : ℝ) : ℝ :=
  Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
    Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))

/-- The `zeroUnitJensenCeil` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def zeroUnitJensenCeil (T : ℝ) : ℕ :=
  ⌈zeroUnitJensenMajorant T⌉₊

theorem zeroUnitJensenCeil_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 2 ≤ T →
      (zeroUnitJensenCeil T : ℝ) ≤ C * Real.log T := by
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))
  let K : ℝ := 100 / D
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hK : 0 < K := div_pos (by norm_num) hD
  refine ⟨K + 1, by linarith, ?_⟩
  intro T hTExp
  have hTpos : 0 < T := (Real.exp_pos 2).trans_le hTExp
  have hLogTwo : 2 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hTExp
    simpa using h
  have hLogOne : 1 ≤ Real.log T := by linarith
  have hNumerator :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) ≤ 100 * Real.log T := by
    have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 3 by norm_num)
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) =
          Real.log ((500 / 3 : ℝ) * T ^ (3 : ℝ)) := by
            congr 1
            ring
      _ = Real.log (500 / 3 : ℝ) + Real.log (T ^ (3 : ℝ)) := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTpos 3).ne']
      _ = Real.log (500 / 3 : ℝ) + 3 * Real.log T := by
        rw [Real.log_rpow hTpos]
      _ ≤ 100 * Real.log T := by linarith
  have hMajorant : zeroUnitJensenMajorant T ≤ K * Real.log T := by
    dsimp [zeroUnitJensenMajorant, K, D]
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) ≤
          (100 * Real.log T) / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
        div_le_div_of_nonneg_right hNumerator hD.le
      _ = (100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) * Real.log T := by ring
  have hMajorantNonneg : 0 ≤ zeroUnitJensenMajorant T := by
    dsimp [zeroUnitJensenMajorant]
    have hTOne : 1 ≤ T := by
      have hOneExp : (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      exact hOneExp.le.trans hTExp
    have hPowOne : 1 ≤ T ^ (3 : ℝ) := Real.one_le_rpow hTOne (by norm_num)
    have hArg : 1 < (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      calc
        (1 : ℝ) < 100 * 1 / 0.6 := by norm_num
        _ ≤ (100 * T ^ (3 : ℝ)) / 0.6 := by gcongr
    exact div_nonneg (Real.log_nonneg hArg.le) hD.le
  have hCeil : (zeroUnitJensenCeil T : ℝ) < zeroUnitJensenMajorant T + 1 := by
    simpa [zeroUnitJensenCeil] using Nat.ceil_lt_add_one hMajorantNonneg
  calc
    (zeroUnitJensenCeil T : ℝ) ≤ zeroUnitJensenMajorant T + 1 := hCeil.le
    _ ≤ K * Real.log T + 1 := by
      simpa only [add_comm] using add_le_add_right hMajorant 1
    _ ≤ (K + 1) * Real.log T := by nlinarith

theorem contourTypeII_weight_sum_eq (σ T : ℝ) :
    ∑ u ∈ contourTypeIIOrdinates σ T, contourTypeIIOrdinateWeight σ T u =
      ∑ ρ ∈ contourTypeIIZeroSet σ T,
        analyticVanishingOrder riemannZeta ρ := by
  let S := contourTypeIIZeroSet σ T
  let U := contourTypeIIOrdinates σ T
  let mult := analyticVanishingOrder riemannZeta
  have hAll : S.filter (fun ρ => ρ.im ∈ U) = S := by
    apply Finset.filter_eq_self.mpr
    intro ρ hρ
    exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S U Complex.im mult
  rw [hAll] at hFiber
  simpa [S, U, mult, contourTypeIIOrdinateWeight] using hFiber

theorem contourTypeII_weight_sum_eq_weightedCount (σ T : ℝ) :
    ((∑ u ∈ contourTypeIIOrdinates σ T,
      contourTypeIIOrdinateWeight σ T u : ℕ) : ℝ) =
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
        zetaIsContourTypeII σ T := by
  rw [contourTypeII_weight_sum_eq]
  simp only [weightedCount, contourTypeIIZeroSet, Nat.cast_sum]

theorem contourTypeII_unit_bin_weight_le (σ T : ℝ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) (z : ℤ) :
    ∑ u ∈ (contourTypeIIOrdinates σ T).filter
        (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1),
      contourTypeIIOrdinateWeight σ T u ≤ zeroUnitJensenCeil T := by
  let S := contourTypeIIZeroSet σ T
  let U := contourTypeIIOrdinates σ T
  let B := U.filter (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1)
  let mult := analyticVanishingOrder riemannZeta
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S B Complex.im mult
  have hSubset : S.filter (fun ρ => ρ.im ∈ B) ⊆ zeroUnitBin σ T z := by
    intro ρ hρ
    simp only [Finset.mem_filter] at hρ
    rw [zeroUnitBin, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hρ.1).1
    · exact (Finset.mem_filter.mp hρ.2).2
  have hNat :
      ∑ ρ ∈ S.filter (fun w => w.im ∈ B), mult ρ ≤
        ∑ ρ ∈ zeroUnitBin σ T z, mult ρ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
    intro ρ hρ hnot
    exact Nat.zero_le _
  have hReal :
      ((∑ ρ ∈ S.filter (fun w => w.im ∈ B), mult ρ : ℕ) : ℝ) ≤
        zeroUnitJensenMajorant T := by
    have hNatReal :
        ((∑ ρ ∈ S.filter (fun w => w.im ∈ B), mult ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ zeroUnitBin σ T z, mult ρ : ℕ) : ℝ) := by
      exact_mod_cast hNat
    exact hNatReal.trans (by
      simpa [mult, zeroUnitJensenMajorant] using
        zeroUnitBin_multiplicity_le_jensen σ T z hσ hT)
  have hCeil :
      ∑ ρ ∈ S.filter (fun w => w.im ∈ B), mult ρ ≤
        zeroUnitJensenCeil T := by
    apply_mod_cast hReal.trans (Nat.le_ceil (zeroUnitJensenMajorant T))
  rw [← hFiber] at hCeil
  simpa [S, U, B, mult, contourTypeIIOrdinateWeight] using hCeil

/-- Multiplicity-preserving one-separated extraction for the concrete Type-II
zero set. -/
theorem exists_separated_contourTypeII_ordinates (σ T : ℝ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ∃ W ⊆ contourTypeIIOrdinates σ T, IsSeparated 1 W ∧
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T ≤
        (2 * zeroUnitJensenCeil T * W.card : ℕ) := by
  obtain ⟨W, hWU, hWSeparated, hWeight⟩ :=
    weighted_separated_selection (contourTypeIIOrdinates σ T)
      (contourTypeIIOrdinateWeight σ T) (zeroUnitJensenCeil T)
      (contourTypeII_unit_bin_weight_le σ T hσ hT)
  refine ⟨W, hWU, hWSeparated, ?_⟩
  rw [← contourTypeII_weight_sum_eq_weightedCount]
  exact_mod_cast hWeight

/-- A normalized unit bin is an interval of length `G` before scaling.  Its
weight is controlled by at most `ceil G + 1` ordinary unit bins. -/
theorem contourTypeII_scaled_bin_weight_le (σ T G : ℝ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) (hG : 1 ≤ G) (z : ℤ) :
    ∑ u ∈ ((contourTypeIIOrdinates σ T).image (fun t => t / G)).filter
        (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1),
      scaledFiberWeight (contourTypeIIOrdinates σ T)
        (contourTypeIIOrdinateWeight σ T) G u ≤
      (⌈G⌉₊ + 1) * zeroUnitJensenCeil T := by
  let S := contourTypeIIOrdinates σ T
  let weight := contourTypeIIOrdinateWeight σ T
  let A := S.filter (fun t => (z : ℝ) ≤ t / G ∧ t / G < (z : ℝ) + 1)
  let k : ℕ := ⌈G⌉₊
  let q : ℤ := ⌊(z : ℝ) * G⌋
  let J : Finset ℤ := Finset.Icc q (q + (k : ℤ))
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hFiber :
      ∑ u ∈ (S.image (fun t => t / G)).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1),
        scaledFiberWeight S weight G u = ∑ t ∈ A, weight t := by
    have h := Finset.sum_fiberwise_eq_sum_filter S
      ((S.image (fun t => t / G)).filter
        (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1))
      (fun t => t / G) weight
    have hFilter : S.filter (fun t =>
        t / G ∈ (S.image (fun x => x / G)).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1)) = A := by
      apply Finset.filter_congr
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · exact fun hmem => hmem.2
      · exact fun hz => ⟨⟨t, ht, rfl⟩, hz⟩
    rw [hFilter] at h
    simpa [scaledFiberWeight] using h
  have hFloors : ∀ t ∈ A, ⌊t⌋ ∈ J := by
    intro t ht
    have htData := Finset.mem_filter.mp ht
    have hk : G ≤ (k : ℝ) := Nat.le_ceil G
    have hqLower : (q : ℝ) ≤ (z : ℝ) * G := Int.floor_le _
    have hqUpper : (z : ℝ) * G < (q : ℝ) + 1 := Int.lt_floor_add_one _
    have htLower : (z : ℝ) * G ≤ t := by
      exact (le_div_iff₀ hGpos).mp htData.2.1
    have htUpper : t < ((z : ℝ) + 1) * G := by
      exact (div_lt_iff₀ hGpos).mp htData.2.2
    change ⌊t⌋ ∈ Finset.Icc q (q + (k : ℤ))
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      exact hqLower.trans htLower
    · have hlt : t < ((q + (k : ℤ) : ℤ) : ℝ) + 1 := by
        push_cast
        calc
          t < ((z : ℝ) + 1) * G := htUpper
          _ = (z : ℝ) * G + G := by ring
          _ < ((q : ℝ) + 1) + (k : ℝ) := add_lt_add_of_lt_of_le hqUpper hk
          _ = (q : ℝ) + (k : ℝ) + 1 := by ring
      have hFloorLt : ⌊t⌋ < q + (k : ℤ) + 1 := by
        rw [Int.floor_lt]
        simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hlt
      omega
  have hAll : A.filter (fun t => ⌊t⌋ ∈ J) = A :=
    Finset.filter_eq_self.mpr hFloors
  have hFloorFiber := Finset.sum_fiberwise_eq_sum_filter A J
    (fun t => ⌊t⌋) weight
  rw [hAll] at hFloorFiber
  rw [hFiber, ← hFloorFiber]
  calc
    ∑ j ∈ J, ∑ t ∈ A.filter (fun x => ⌊x⌋ = j), weight t
        ≤ ∑ _j ∈ J, zeroUnitJensenCeil T := by
          apply Finset.sum_le_sum
          intro j hj
          apply le_trans (Finset.sum_le_sum_of_subset ?_)
            (contourTypeII_unit_bin_weight_le σ T hσ hT j)
          intro t ht
          rw [Finset.mem_filter] at ht ⊢
          refine ⟨(Finset.mem_filter.mp ht.1).1, ?_⟩
          exact Int.floor_eq_iff.mp ht.2
    _ = J.card * zeroUnitJensenCeil T := by simp
    _ = (k + 1) * zeroUnitJensenCeil T := by
      congr 1
      change (Finset.Icc q (q + (k : ℤ))).card = k + 1
      rw [Int.card_Icc]
      omega

/-- Multiplicity-preserving extraction at every scale `G ≥ 1`. -/
theorem exists_scaled_separated_contourTypeII_ordinates (σ T G : ℝ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) (hG : 1 ≤ G) :
    ∃ W ⊆ contourTypeIIOrdinates σ T, IsSeparated G W ∧
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T ≤
        (2 * ((⌈G⌉₊ + 1) * zeroUnitJensenCeil T) * W.card : ℕ) := by
  obtain ⟨W, hWU, hWSeparated, hWeight⟩ :=
    scaled_weighted_separated_selection (contourTypeIIOrdinates σ T)
      (contourTypeIIOrdinateWeight σ T)
      ((⌈G⌉₊ + 1) * zeroUnitJensenCeil T) (lt_of_lt_of_le zero_lt_one hG)
      (contourTypeII_scaled_bin_weight_le σ T G hσ hT hG)
  refine ⟨W, hWU, hWSeparated, ?_⟩
  rw [← contourTypeII_weight_sum_eq_weightedCount]
  exact_mod_cast hWeight

/-- One concrete Type-II zero above an occupied ordinate. -/
noncomputable def contourTypeIIRepresentative (σ T u : ℝ) : ℂ :=
  if hu : u ∈ contourTypeIIOrdinates σ T then
    Classical.choose (Finset.mem_image.mp hu)
  else 0

theorem contourTypeIIRepresentative_spec {σ T u : ℝ}
    (hu : u ∈ contourTypeIIOrdinates σ T) :
    contourTypeIIRepresentative σ T u ∈ contourTypeIIZeroSet σ T ∧
      (contourTypeIIRepresentative σ T u).im = u := by
  rw [contourTypeIIRepresentative, dif_pos hu]
  exact Classical.choose_spec (Finset.mem_image.mp hu)

/-- The `criticalTwistedNorm` definition used by the source-facing construction in `TypeIIFourthMomentReduction`. -/
noncomputable def criticalTwistedNorm (T t : ℝ) : ℝ :=
  ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) *
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖

theorem criticalTwistedNorm_pow_four (T t : ℝ) :
    criticalTwistedNorm T t ^ 4 = twistedZetaMomentIntegrand T t := rfl

theorem detectorCutoff_le_three_mul_height (T : ℝ) (hT : 1 ≤ T) :
    (detectorCutoff T : ℝ) ≤ 3 * T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hPow : T ^ (1 / 100 : ℝ) ≤ T := by
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (1 / 100 : ℝ) ≤ 1 by norm_num)
  have hFloor :
      (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ 2 * T ^ (1 / 100 : ℝ))
  rw [detectorCutoff, Nat.cast_add, Nat.cast_one]
  linarith

theorem criticalTwistedNorm_shifted_le (T b u : ℝ) :
    criticalTwistedNorm T (b + u) ≤
      (detectorCutoff T : ℝ) * (4 * (1 + |b|)) * (1 + |u|) := by
  rw [criticalTwistedNorm, norm_mul]
  calc
    ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + ((b + u : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta ((1 / 2 : ℂ) + ((b + u : ℝ) : ℂ) * I)‖
        ≤ (detectorCutoff T : ℝ) *
            ((4 * (1 + |b|)) * (1 + |u|)) := by
          gcongr
          · exact norm_shortMobiusPolynomial_criticalLine_le T (b + u)
          · exact norm_riemannZeta_shifted_criticalLine_le b u
    _ = (detectorCutoff T : ℝ) * (4 * (1 + |b|)) * (1 + |u|) := by ring

theorem continuous_criticalTwistedNorm (T : ℝ) :
    Continuous (criticalTwistedNorm T) := by
  have hM : Continuous (fun t : ℝ =>
      shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    simpa using continuous_shortMobiusPolynomial_vertical T (1 / 2 : ℂ)
  have hZ : Continuous (fun t : ℝ =>
      riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hPoint : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h
      have hRe := congrArg Complex.re h
      norm_num at hRe
    exact ContinuousAt.comp'
      (differentiableAt_riemannZeta hPoint).continuousAt (by fun_prop)
  unfold criticalTwistedNorm
  exact (hM.mul hZ).norm

theorem criticalTwistedNorm_representative_le {σ T u v : ℝ}
    (hu : u ∈ contourTypeIIOrdinates σ T) (hT : 1 ≤ T) :
    criticalTwistedNorm T (u + v) ≤ 36 * T ^ 2 * (1 + |v|) := by
  have hRep := (contourTypeIIRepresentative_spec hu).1
  have hZeroMem : contourTypeIIRepresentative σ T u ∈ dyadicZetaZeros σ T :=
    (Finset.mem_filter.mp hRep).1
  rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, mem_ZeroRectangle] at hZeroMem
  rw [(contourTypeIIRepresentative_spec hu).2] at hZeroMem
  have huBounds : T ≤ u ∧ u ≤ 2 * T := by
    exact ⟨hZeroMem.1.2.2.1, hZeroMem.1.2.2.2⟩
  have huNonneg : 0 ≤ u := le_trans (by linarith) huBounds.1
  have hU : 1 + |u| ≤ 3 * T := by
    rw [abs_of_nonneg huNonneg]
    linarith
  have hCut := detectorCutoff_le_three_mul_height T hT
  calc
    criticalTwistedNorm T (u + v) ≤
        (detectorCutoff T : ℝ) * (4 * (1 + |u|)) * (1 + |v|) :=
      criticalTwistedNorm_shifted_le T u v
    _ ≤ (3 * T) * (4 * (3 * T)) * (1 + |v|) := by gcongr
    _ = 36 * T ^ 2 * (1 + |v|) := by ring

set_option maxHeartbeats 800000 in
/-- Exact symmetric tail integral for a negative real power. -/
theorem integral_abs_rpow_compl_Icc {a H : ℝ} (ha : a < -1) (hH : 0 < H) :
    ∫ u : ℝ in (Set.Icc (-H) H)ᶜ, |u| ^ a =
      -2 * H ^ (a + 1) / (a + 1) := by
  have hPosInt : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt ha hH
  have hNegInt : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    have hPosInt' : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi (-(-H))) := by
      simpa only [neg_neg] using hPosInt
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) := by
      exact hPosInt'.comp_neg_Iio (c := -H)
    apply h.congr_fun
    intro u hu
    change (-u) ^ a = |u| ^ a
    rw [abs_of_neg (lt_trans hu (neg_neg_of_pos hH))]
    simp
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    intro u hu
    change u ^ a = |u| ^ a
    rw [abs_of_pos (hH.trans hu)]
    exact measurableSet_Ioi
  have hDisjoint : Disjoint (Set.Iio (-H)) (Set.Ioi H) := by
    rw [Set.disjoint_left]
    intro u huNeg huPos
    change u < -H at huNeg
    change H < u at huPos
    linarith
  have hCompl : (Set.Icc (-H) H)ᶜ = Set.Iio (-H) ∪ Set.Ioi H := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      by_cases hu : u < -H
      · exact Or.inl hu
      · exact Or.inr (lt_of_not_ge fun huH => h ⟨le_of_not_gt hu, huH⟩)
    · intro h hu
      rcases h with h | h <;> linarith
  rw [hCompl, setIntegral_union hDisjoint measurableSet_Ioi hNegInt hPosAbs]
  have hNegEq :
      ∫ u : ℝ in Set.Iio (-H), |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [← integral_comp_neg_Ioi H (fun u : ℝ => |u| ^ a)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |-u| ^ a = u ^ a
    rw [abs_neg, abs_of_pos (hH.trans hu)]
  have hPosEq :
      ∫ u : ℝ in Set.Ioi H, |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |u| ^ a = u ^ a
    rw [abs_of_pos (hH.trans hu)]
  rw [hNegEq, hPosEq, integral_Ioi_rpow_of_lt ha hH]
  ring

theorem integrableOn_abs_rpow_compl_Icc {a H : ℝ} (ha : a < -1) (hH : 0 < H) :
    IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Icc (-H) H)ᶜ := by
  have hPosInt : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt ha hH
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    · intro u hu
      change u ^ a = |u| ^ a
      rw [abs_of_pos (hH.trans hu)]
    · exact measurableSet_Ioi
  have hNegAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    have hPosInt' : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi (-(-H))) := by
      simpa only [neg_neg] using hPosInt
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) :=
      hPosInt'.comp_neg_Iio (c := -H)
    apply h.congr_fun
    intro u hu
    change (-u) ^ a = |u| ^ a
    rw [abs_of_neg (lt_trans hu (neg_neg_of_pos hH))]
    simp
  have hCompl : (Set.Icc (-H) H)ᶜ = Set.Iio (-H) ∪ Set.Ioi H := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      by_cases hu : u < -H
      · exact Or.inl hu
      · exact Or.inr (lt_of_not_ge fun huH => h ⟨le_of_not_gt hu, huH⟩)
    · intro h hu
      rcases h with h | h <;> linarith
  rw [hCompl]
  exact hNegAbs.union hPosAbs

/-- Uniform `L¹` control of the Gamma kernel throughout the contour strip. -/
theorem integral_norm_typeII_Gamma_le_thirty {a : ℝ}
    (haLower : -(1 / 2 : ℝ) ≤ a) (haUpper : a ≤ -(1 / 5 : ℝ)) :
    ∫ u : ℝ, ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ ≤ 30 := by
  let f : ℝ → ℝ := fun u => ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖
  have hf : Integrable f :=
    (integrable_typeII_Gamma_horizontal haLower haUpper).norm
  have hCentral : ∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u ≤ 28 := by
    have hConst : IntegrableOn (fun _u : ℝ => (14 : ℝ)) (Set.Icc (-1 : ℝ) 1) :=
      integrableOn_const (μ := volume) measure_Icc_lt_top.ne (by norm_num)
    calc
      ∫ u : ℝ in Set.Icc (-1 : ℝ) 1, f u
          ≤ ∫ _u : ℝ in Set.Icc (-1 : ℝ) 1, (14 : ℝ) := by
            apply integral_mono_ae hf.integrableOn hConst
            filter_upwards with u
            exact typeII_Gamma_norm_le_fourteen haLower haUpper
      _ = 28 := by norm_num [MeasureTheory.integral_const, Real.volume_Icc]
  have hTailDom : IntegrableOn (fun u : ℝ => 2 * |u| ^ (-(3 : ℝ)))
      (Set.Icc (-1 : ℝ) 1)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc (by norm_num) (by norm_num)).const_mul 2
  have hTail : ∫ u : ℝ in (Set.Icc (-1 : ℝ) 1)ᶜ, f u ≤ 2 := by
    calc
      ∫ u : ℝ in (Set.Icc (-1 : ℝ) 1)ᶜ, f u
          ≤ ∫ u : ℝ in (Set.Icc (-1 : ℝ) 1)ᶜ,
              2 * |u| ^ (-(3 : ℝ)) := by
            apply integral_mono_ae hf.integrableOn hTailDom
            filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with u hu
            have hAbs : 1 ≤ |u| := by
              by_contra h
              have hlt : |u| < 1 := lt_of_not_ge h
              exact hu (abs_le.mp hlt.le)
            have hDecay := typeII_Gamma_norm_le_inv_pow 3 (by norm_num)
              haLower haUpper hAbs
            have hAbsPos : 0 < |u| := lt_of_lt_of_le zero_lt_one hAbs
            calc
              f u ≤ 2 / |u| ^ 3 := by simpa [f] using hDecay
              _ = 2 * |u| ^ (-(3 : ℝ)) := by
                rw [div_eq_mul_inv, show |u| ^ 3 = |u| ^ (3 : ℝ) by simp,
                  ← Real.rpow_neg hAbsPos.le]
      _ = 2 := by
        rw [integral_const_mul,
          integral_abs_rpow_compl_Icc (by norm_num) (by norm_num)]
        norm_num
  rw [← integral_add_compl measurableSet_Icc hf]
  linarith

/-- Translation of an `Icc` set integral, written for the additive convention
used by the Type-II windows. -/
theorem setIntegral_comp_add_Icc (f : ℝ → ℝ) (u H : ℝ) :
    ∫ v : ℝ in Set.Icc (-H) H, f (u + v) =
      ∫ t : ℝ in Set.Icc (u - H) (u + H), f t := by
  rw [← integral_indicator measurableSet_Icc,
    ← integral_indicator measurableSet_Icc]
  have hFun :
      Set.indicator (Set.Icc (-H) H) (fun v => f (u + v)) =
        fun v => Set.indicator (Set.Icc (u - H) (u + H)) f (v + u) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-H) H
    · have hTarget : v + u ∈ Set.Icc (u - H) (u + H) := by
        rw [Set.mem_Icc] at hv ⊢
        constructor <;> linarith
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hTarget]
      congr 1
      ring
    · have hTarget : v + u ∉ Set.Icc (u - H) (u + H) := by
        intro h
        apply hv
        rw [Set.mem_Icc] at h ⊢
        constructor <;> linarith
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hTarget]
  rw [hFun]
  exact integral_add_right_eq_self _ u

theorem norm_typeIIContourIntegrand_eq {ρ : ℂ} {T u : ℝ} (hT : 0 < T) :
    ‖typeIIContourIntegrand ρ T u‖ =
      T ^ ((1 / 2 - ρ.re) / 2) *
        ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
          criticalTwistedNorm T (ρ.im + u) := by
  rw [typeIIContourIntegrand]
  rw [norm_mul, norm_mul, norm_mul]
  have hPowRe : (typeIIContourShift ρ u / 2).re = (1 / 2 - ρ.re) / 2 := by
    simp [typeIIContourShift]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hT, hPowRe]
  rw [rho_add_typeIIContourShift]
  rw [criticalTwistedNorm, norm_mul]
  simp only [typeIIContourShift]
  ring

/-- The Gamma convolution occurring after taking norms is genuinely
integrable; this is extracted from the proved contour-integrand integrability
by dividing by its positive constant factor. -/
theorem integrable_gamma_mul_criticalTwistedNorm {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hρLower : 7 / 10 ≤ ρ.re) (hρUpper : ρ.re ≤ 1) :
    Integrable (fun u : ℝ =>
      ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        criticalTwistedNorm T (ρ.im + u)) := by
  let c : ℝ := T ^ ((1 / 2 - ρ.re) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos hT _
  have hNorm := (integrable_typeIIContourIntegrand hT hρLower hρUpper).norm
  have hScaled := hNorm.const_mul c⁻¹
  apply hScaled.congr
  filter_upwards with u
  rw [norm_typeIIContourIntegrand_eq hT]
  dsimp [c]
  field_simp

/-- Arbitrary-order quantitative removal of the two Gamma tails for a
representative contour-Type-II zero. -/
theorem representative_typeII_gamma_tail_le {σ T u H : ℝ} (n : ℕ)
    (hn : 3 ≤ n) (hu : u ∈ contourTypeIIOrdinates σ T)
    (hσ : 7 / 10 ≤ σ) (hT : 8 ≤ T) (hH : 1 ≤ H) :
    ∫ v : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖Complex.Gamma
          (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
            (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ≤
      (72 * (Nat.factorial (n - 1) : ℝ) * T ^ 2) *
        (-2 * H ^ (2 - (n : ℝ)) / (2 - (n : ℝ))) := by
  let ρ := contourTypeIIRepresentative σ T u
  have hRep := contourTypeIIRepresentative_spec hu
  have hZeroMem : ρ ∈ dyadicZetaZeros σ T := (Finset.mem_filter.mp hRep.1).1
  rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, mem_ZeroRectangle] at hZeroMem
  have hρLower : 7 / 10 ≤ ρ.re := hσ.trans hZeroMem.1.1
  have hρUpper : ρ.re ≤ 1 := hZeroMem.1.2.1
  have haLower : -(1 / 2 : ℝ) ≤ 1 / 2 - ρ.re := by linarith
  have haUpper : 1 / 2 - ρ.re ≤ -(1 / 5 : ℝ) := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let a : ℝ := 1 - (n : ℝ)
  have ha : a < -1 := by
    have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [a]
    linarith
  let K : ℝ := 72 * (Nat.factorial (n - 1) : ℝ) * T ^ 2
  have hK : 0 ≤ K := by positivity
  have hTargetInt := integrable_gamma_mul_criticalTwistedNorm
    (ρ := ρ) hTpos hρLower hρUpper
  have hTargetOn : IntegrableOn (fun v : ℝ =>
      ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
        criticalTwistedNorm T (u + v)) (Set.Icc (-H) H)ᶜ := by
    rw [← hRep.2]
    exact hTargetInt.integrableOn
  have hDomOn : IntegrableOn (fun v : ℝ => K * |v| ^ a)
      (Set.Icc (-H) H)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc ha hHpos).const_mul K
  have hPoint : ∀ v ∈ (Set.Icc (-H) H)ᶜ,
      ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          criticalTwistedNorm T (u + v) ≤ K * |v| ^ a := by
    intro v hv
    have hvOut : v < -H ∨ H < v := by
      by_contra h
      have hvLower : -H ≤ v := le_of_not_gt (not_or.mp h).1
      have hvUpper : v ≤ H := le_of_not_gt (not_or.mp h).2
      exact hv ⟨hvLower, hvUpper⟩
    have hAbs : H < |v| := by
      rcases hvOut with hvNeg | hvPos
      · rw [abs_of_neg (lt_trans hvNeg (neg_neg_of_pos hHpos))]
        linarith
      · exact hvPos.trans_le (le_abs_self v)
    have hAbsOne : 1 ≤ |v| := hH.trans hAbs.le
    have hAbsPos : 0 < |v| := lt_of_lt_of_le zero_lt_one hAbsOne
    have hGamma := typeII_Gamma_norm_le_inv_pow n hn haLower haUpper hAbsOne
    have hF := criticalTwistedNorm_representative_le (v := v) hu hTOne
    have hOneAbs : 1 + |v| ≤ 2 * |v| := by linarith
    have hRatio : |v| / |v| ^ n = |v| ^ a := by
      rw [show |v| ^ n = |v| ^ (n : ℝ) by simp]
      rw [show a = 1 - (n : ℝ) by rfl, Real.rpow_sub hAbsPos,
        Real.rpow_one]
    dsimp [K]
    calc
      ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          criticalTwistedNorm T (u + v)
          ≤ ((Nat.factorial (n - 1) : ℝ) / |v| ^ n) *
              (36 * T ^ 2 * (1 + |v|)) := by
            exact mul_le_mul hGamma hF (norm_nonneg _)
              (by positivity)
      _ ≤ ((Nat.factorial (n - 1) : ℝ) / |v| ^ n) *
              (36 * T ^ 2 * (2 * |v|)) := by gcongr
      _ = 72 * (Nat.factorial (n - 1) : ℝ) * T ^ 2 * |v| ^ a := by
        rw [← hRatio]
        field_simp
        ring
  calc
    ∫ v : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
          criticalTwistedNorm T (u + v)
        ≤ ∫ v : ℝ in (Set.Icc (-H) H)ᶜ, K * |v| ^ a := by
          apply integral_mono_ae hTargetOn hDomOn
          filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
          exact hPoint v hv
    _ = K * (-2 * H ^ (a + 1) / (a + 1)) := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc ha hHpos]
    _ = (72 * (Nat.factorial (n - 1) : ℝ) * T ^ 2) *
        (-2 * H ^ (2 - (n : ℝ)) / (2 - (n : ℝ))) := by
      have hExp : (1 - (n : ℝ)) + 1 = 2 - (n : ℝ) := by ring
      dsimp [K, a]
      rw [hExp]

/-- A power-sized window makes the Gamma tail uniformly negligible.  The
decay order is chosen once from the requested window exponent. -/
theorem eventually_representative_typeII_gamma_tail_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 3 ≤ n ∧ ∀ᶠ T : ℝ in atTop,
      8 ≤ T → ∀ (σ u : ℝ), 7 / 10 ≤ σ →
        u ∈ contourTypeIIOrdinates σ T →
        ∫ v : ℝ in (Set.Icc (-(T ^ δ)) (T ^ δ))ᶜ,
            ‖Complex.Gamma
              (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
                (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ≤
          1 / (12 * Real.pi) := by
  let k : ℕ := ⌈4 / δ⌉₊
  let n : ℕ := k + 3
  have hk : 4 / δ ≤ (k : ℝ) := Nat.le_ceil (4 / δ)
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hDecayExp : 2 + δ * (2 - (n : ℝ)) < 0 := by
    have hkδ : 4 ≤ δ * (k : ℝ) := by
      calc
        4 = δ * (4 / δ) := by field_simp
        _ ≤ δ * (k : ℝ) := mul_le_mul_of_nonneg_left hk hδ.le
    dsimp [n]
    push_cast
    linarith
  let C : ℝ := -144 * (Nat.factorial (n - 1) : ℝ) / (2 - (n : ℝ))
  let q : ℝ := 2 + δ * (2 - (n : ℝ))
  have hq : q < 0 := by simpa [q] using hDecayExp
  have hTendsto : Tendsto (fun T : ℝ => C * T ^ q) atTop (𝓝 0) := by
    have hPow := tendsto_rpow_neg_atTop (show 0 < -q by linarith)
    have hScaled : Tendsto (fun T : ℝ => C * T ^ (-(-q))) atTop (𝓝 0) := by
      simpa using hPow.const_mul C
    apply hScaled.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    congr 1
    congr 1
    ring
  have hEventually : ∀ᶠ T : ℝ in atTop, C * T ^ q < 1 / (12 * Real.pi) :=
    (tendsto_order.1 hTendsto).2 _ (by positivity)
  refine ⟨n, hn, ?_⟩
  filter_upwards [hEventually, eventually_ge_atTop (8 : ℝ)] with T hSmall hTEight
  intro hT σ u hσ hu
  have hTpos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hHOne : 1 ≤ T ^ δ := Real.one_le_rpow hTOne hδ.le
  have hRaw := representative_typeII_gamma_tail_le n hn hu hσ hT hHOne
  have hRawEq :
      (72 * (Nat.factorial (n - 1) : ℝ) * T ^ 2) *
          (-2 * (T ^ δ) ^ (2 - (n : ℝ)) / (2 - (n : ℝ))) =
        C * T ^ q := by
    rw [show T ^ (2 : ℕ) = T ^ (2 : ℝ) by simp,
      ← Real.rpow_mul hTpos.le]
    have hPows : T ^ (2 : ℝ) * T ^ (δ * (2 - (n : ℝ))) = T ^ q := by
      rw [← Real.rpow_add hTpos]
    calc
      (72 * (Nat.factorial (n - 1) : ℝ) * T ^ (2 : ℝ)) *
          (-2 * T ^ (δ * (2 - (n : ℝ))) / (2 - (n : ℝ))) =
          C * (T ^ (2 : ℝ) * T ^ (δ * (2 - (n : ℝ)))) := by
            dsimp [C]
            ring
      _ = C * T ^ q := by rw [hPows]
  rw [hRawEq] at hRaw
  exact hRaw.trans hSmall.le

/-- The Type-II detector is bounded by its positive Gamma convolution on the
critical line. -/
theorem norm_typeIIContourIntegral_le {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hρLower : 7 / 10 ≤ ρ.re) (hρUpper : ρ.re ≤ 1) :
    ‖typeIIContourIntegral ρ T‖ ≤
      (1 / (2 * Real.pi)) * T ^ ((1 / 2 - ρ.re) / 2) *
        ∫ u : ℝ,
          ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
            criticalTwistedNorm T (ρ.im + u) := by
  have hInt := integrable_typeIIContourIntegrand hT hρLower hρUpper
  rw [typeIIContourIntegral, norm_mul]
  have hConst : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ =
      1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [hConst]
  calc
    (1 / (2 * Real.pi)) * ‖∫ u : ℝ, typeIIContourIntegrand ρ T u‖
        ≤ (1 / (2 * Real.pi)) *
            ∫ u : ℝ, ‖typeIIContourIntegrand ρ T u‖ := by
          gcongr
          exact norm_integral_le_integral_norm _
    _ = (1 / (2 * Real.pi)) * T ^ ((1 / 2 - ρ.re) / 2) *
        ∫ u : ℝ,
          ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
            criticalTwistedNorm T (ρ.im + u) := by
      rw [show (∫ u : ℝ, ‖typeIIContourIntegrand ρ T u‖) =
          T ^ ((1 / 2 - ρ.re) / 2) *
            ∫ u : ℝ,
              ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
                criticalTwistedNorm T (ρ.im + u) by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simpa [mul_assoc] using norm_typeIIContourIntegrand_eq hT]
      ring

theorem one_le_typeII_gamma_convolution {σ T : ℝ} {ρ : ℂ}
    (hT : 1 ≤ T) (hσρ : σ ≤ ρ.re)
    (hρLower : 7 / 10 ≤ ρ.re) (hρUpper : ρ.re ≤ 1)
    (hII : IsContourTypeIIZero ρ T) :
    1 ≤ (6 * Real.pi) * T ^ ((1 / 2 - σ) / 2) *
      ∫ u : ℝ,
        ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
          criticalTwistedNorm T (ρ.im + u) := by
  let J : ℝ := ∫ u : ℝ,
    ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I)‖ *
      criticalTwistedNorm T (ρ.im + u)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hUpper := norm_typeIIContourIntegral_le hTpos hρLower hρUpper
  have hJ : 0 ≤ J := by
    apply MeasureTheory.integral_nonneg
    intro u
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hExp : (1 / 2 - ρ.re) / 2 ≤ (1 / 2 - σ) / 2 := by linarith
  have hPow : T ^ ((1 / 2 - ρ.re) / 2) ≤ T ^ ((1 / 2 - σ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hT hExp
  have hScale :
      T ^ ((1 / 2 - ρ.re) / 2) * J ≤
        T ^ ((1 / 2 - σ) / 2) * J :=
    mul_le_mul_of_nonneg_right hPow hJ
  change (1 / 3 : ℝ) ≤ ‖typeIIContourIntegral ρ T‖ at hII
  change ‖typeIIContourIntegral ρ T‖ ≤
    (1 / (2 * Real.pi)) * T ^ ((1 / 2 - ρ.re) / 2) * J at hUpper
  change 1 ≤ (6 * Real.pi) * T ^ ((1 / 2 - σ) / 2) * J
  have hX : 0 ≤ T ^ ((1 / 2 - ρ.re) / 2) * J :=
    mul_nonneg (Real.rpow_nonneg hTpos.le _) hJ
  have hCoeff : 3 / (2 * Real.pi) ≤ 6 * Real.pi := by
    calc
      3 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).2 (by
        nlinarith [Real.pi_gt_three])
      _ ≤ 6 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    1 = 3 * (1 / 3 : ℝ) := by norm_num
    _ ≤ 3 * ‖typeIIContourIntegral ρ T‖ :=
      mul_le_mul_of_nonneg_left hII (by norm_num)
    _ ≤ 3 * ((1 / (2 * Real.pi)) *
        T ^ ((1 / 2 - ρ.re) / 2) * J) :=
      mul_le_mul_of_nonneg_left hUpper (by norm_num)
    _ = (3 / (2 * Real.pi)) *
        (T ^ ((1 / 2 - ρ.re) / 2) * J) := by ring
    _ ≤ (6 * Real.pi) *
        (T ^ ((1 / 2 - ρ.re) / 2) * J) :=
      mul_le_mul_of_nonneg_right hCoeff hX
    _ ≤ (6 * Real.pi) *
        (T ^ ((1 / 2 - σ) / 2) * J) :=
      mul_le_mul_of_nonneg_left hScale (by positivity)
    _ = (6 * Real.pi) * T ^ ((1 / 2 - σ) / 2) * J := by ring

/-- The whole-line detector lower bound remains after the quantitatively small
Gamma tail is removed. -/
theorem one_le_representative_gamma_window {σ T u H : ℝ}
    (hu : u ∈ contourTypeIIOrdinates σ T)
    (hσLower : 7 / 10 ≤ σ) (hT : 8 ≤ T)
    (hTail :
      ∫ v : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ≤
        1 / (12 * Real.pi)) :
    1 ≤ (12 * Real.pi) * T ^ ((1 / 2 - σ) / 2) *
      ∫ v : ℝ in Set.Icc (-H) H,
        ‖Complex.Gamma
          (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
            (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) := by
  let ρ := contourTypeIIRepresentative σ T u
  let f : ℝ → ℝ := fun v =>
    ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
      criticalTwistedNorm T (u + v)
  let A : ℝ := (6 * Real.pi) * T ^ ((1 / 2 - σ) / 2)
  have hRep := contourTypeIIRepresentative_spec hu
  have hZeroMem : ρ ∈ dyadicZetaZeros σ T :=
    (Finset.mem_filter.mp hRep.1).1
  rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, mem_ZeroRectangle] at hZeroMem
  have hρLower : 7 / 10 ≤ ρ.re := hσLower.trans hZeroMem.1.1
  have hρUpper : ρ.re ≤ 1 := hZeroMem.1.2.1
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hAll := one_le_typeII_gamma_convolution hTOne hZeroMem.1.1
    hρLower hρUpper (show IsContourTypeIIZero ρ T from (Finset.mem_filter.mp hRep.1).2)
  rw [hRep.2] at hAll
  change 1 ≤ A * ∫ v, f v at hAll
  have hf : Integrable f := by
    dsimp [f]
    rw [← hRep.2]
    exact integrable_gamma_mul_criticalTwistedNorm hTpos hρLower hρUpper
  have hSplit :
      (∫ v : ℝ in Set.Icc (-H) H, f v) +
          ∫ v : ℝ in (Set.Icc (-H) H)ᶜ, f v = ∫ v : ℝ, f v :=
    integral_add_compl measurableSet_Icc hf
  have hANonneg : 0 ≤ A := by dsimp [A]; positivity
  have hExpNonpos : (1 / 2 - σ) / 2 ≤ 0 := by linarith
  have hPowLe : T ^ ((1 / 2 - σ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hTOne hExpNonpos
  have hTailNonneg : 0 ≤ ∫ v : ℝ in (Set.Icc (-H) H)ᶜ, f v := by
    apply integral_nonneg
    intro v
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hATail : A * (∫ v : ℝ in (Set.Icc (-H) H)ᶜ, f v) ≤ 1 / 2 := by
    calc
      A * (∫ v : ℝ in (Set.Icc (-H) H)ᶜ, f v)
          ≤ (6 * Real.pi) * 1 * (1 / (12 * Real.pi)) := by
            dsimp [A]
            gcongr
      _ = 1 / 2 := by
        field_simp [Real.pi_ne_zero]
        ring
  have hNearNonneg : 0 ≤ ∫ v : ℝ in Set.Icc (-H) H, f v := by
    apply integral_nonneg
    intro v
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [← hSplit] at hAll
  change 1 ≤ A *
    ((∫ v : ℝ in Set.Icc (-H) H, f v) +
      ∫ v : ℝ in (Set.Icc (-H) H)ᶜ, f v) at hAll
  have hHalf : 1 / 2 ≤ A * ∫ v : ℝ in Set.Icc (-H) H, f v := by
    nlinarith
  calc
    1 ≤ 2 * A * ∫ v : ℝ in Set.Icc (-H) H, f v := by nlinarith
    _ = (12 * Real.pi) * T ^ ((1 / 2 - σ) / 2) *
        ∫ v : ℝ in Set.Icc (-H) H,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) := by
      dsimp [A, f, ρ]
      ring

/-- Weighted fourth-power Hölder inequality in the exact form needed for the
Gamma convolution. -/
theorem integral_mul_fourth_holder {g F : ℝ → ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hF0 : ∀ u, 0 ≤ F u)
    (hg : Integrable g) (hgF : Integrable (fun u => g u * F u ^ 4)) :
    (∫ u, g u * F u) ^ 4 ≤
      (∫ u, g u) ^ 3 * ∫ u, g u * F u ^ 4 := by
  let A : ℝ → ℝ := fun u => g u ^ (3 / 4 : ℝ)
  let B : ℝ → ℝ := fun u => (g u * F u ^ 4) ^ (1 / 4 : ℝ)
  have hgMem : MemLp g 1 := memLp_one_iff_integrable.mpr hg
  have hgFMem : MemLp (fun u => g u * F u ^ 4) 1 :=
    memLp_one_iff_integrable.mpr hgF
  have hAMem : MemLp A (ENNReal.ofReal (4 / 3 : ℝ)) := by
    have h := hgMem.norm_rpow_div (ENNReal.ofReal (3 / 4 : ℝ))
    convert h using 1
    · ext u
      change g u ^ (3 / 4 : ℝ) = _
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 u)]
      congr 1
      norm_num
    · rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp [div_eq_mul_inv]
  have hBMem : MemLp B (ENNReal.ofReal (4 : ℝ)) := by
    have h := hgFMem.norm_rpow_div (ENNReal.ofReal (1 / 4 : ℝ))
    convert h using 1
    · ext u
      change (g u * F u ^ 4) ^ (1 / 4 : ℝ) = _
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (hg0 u) (pow_nonneg (hF0 u) 4))]
      congr 1
      norm_num
    · rw [show (4 : ℝ) = (1 / 4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp [div_eq_mul_inv]
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun u => Real.rpow_nonneg (hg0 u) _)
    (Eventually.of_forall fun u =>
      Real.rpow_nonneg (mul_nonneg (hg0 u) (pow_nonneg (hF0 u) 4)) _)
    hAMem hBMem
  have hAB : ∀ u, A u * B u = g u * F u := by
    intro u
    by_cases hgu : g u = 0
    · simp [A, B, hgu]
    have hgupos : 0 < g u := lt_of_le_of_ne (hg0 u) (Ne.symm hgu)
    dsimp [A, B]
    rw [Real.mul_rpow (hg0 u) (pow_nonneg (hF0 u) 4)]
    rw [← Real.rpow_natCast_mul (hF0 u) 4 (1 / 4 : ℝ)]
    rw [← mul_assoc, ← Real.rpow_add hgupos]
    norm_num
  have hA : ∀ u, A u ^ (4 / 3 : ℝ) = g u := by
    intro u
    dsimp [A]
    rw [← Real.rpow_mul (hg0 u)]
    norm_num
  have hB : ∀ u, B u ^ (4 : ℝ) = g u * F u ^ 4 := by
    intro u
    dsimp [B]
    rw [← Real.rpow_mul (mul_nonneg (hg0 u) (pow_nonneg (hF0 u) 4))]
    norm_num
  rw [show (fun u => A u * B u) = fun u => g u * F u by
      funext u; exact hAB u] at hHolder
  rw [show (fun u => A u ^ (4 / 3 : ℝ)) = g by
      funext u; exact hA u] at hHolder
  rw [show (fun u => B u ^ (4 : ℝ)) = fun u => g u * F u ^ 4 by
      funext u; exact hB u] at hHolder
  have hIntNonneg : 0 ≤ ∫ u, g u * F u := by
    apply integral_nonneg
    intro u
    exact mul_nonneg (hg0 u) (hF0 u)
  have hGNonneg : 0 ≤ ∫ u, g u := integral_nonneg hg0
  have hGFNonneg : 0 ≤ ∫ u, g u * F u ^ 4 := by
    apply integral_nonneg
    intro u
    exact mul_nonneg (hg0 u) (pow_nonneg (hF0 u) 4)
  have hPow := pow_le_pow_left₀ hIntNonneg hHolder 4
  calc
    (∫ u, g u * F u) ^ 4
        ≤ (((∫ u, g u) ^ (1 / (4 / 3 : ℝ))) *
          ((∫ u, g u * F u ^ 4) ^ (1 / (4 : ℝ)))) ^ 4 := hPow
    _ = (∫ u, g u) ^ 3 * ∫ u, g u * F u ^ 4 := by
      rw [mul_pow]
      rw [show (1 / (4 / 3 : ℝ)) = (3 : ℝ) / 4 by norm_num]
      rw [show (1 / (4 : ℝ)) = (1 : ℝ) / 4 by norm_num]
      have hGroot : ((∫ u, g u) ^ (3 / 4 : ℝ)) ^ 4 =
          (∫ u, g u) ^ 3 := by
        rw [show (3 / 4 : ℝ) = (3 : ℝ) * (4 : ℝ)⁻¹ by norm_num]
        rw [Real.rpow_mul hGNonneg]
        have hroot := Real.rpow_inv_natCast_pow (n := 4)
          (pow_nonneg hGNonneg 3) (by norm_num)
        convert hroot using 1
        all_goals norm_num
      have hGFroot : ((∫ u, g u * F u ^ 4) ^ (1 / 4 : ℝ)) ^ 4 =
          ∫ u, g u * F u ^ 4 := by
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
        exact Real.rpow_inv_natCast_pow (n := 4) hGFNonneg (by norm_num)
      rw [hGroot, hGFroot]

/-- Hölder on a truncated Gamma window, with the strip-uniform `L¹` constant
already evaluated. -/
theorem representative_gamma_window_holder {σ T u H : ℝ}
    (hu : u ∈ contourTypeIIOrdinates σ T)
    (hσ : 7 / 10 ≤ σ) :
    (∫ v : ℝ in Set.Icc (-H) H,
        ‖Complex.Gamma
          (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
            (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v)) ^ 4 ≤
      30 ^ 3 *
        ∫ v : ℝ in Set.Icc (-H) H,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ^ 4 := by
  let ρ := contourTypeIIRepresentative σ T u
  let S : Set ℝ := Set.Icc (-H) H
  let gammaWeight : ℝ → ℝ := fun v =>
    ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖
  let g : ℝ → ℝ := S.indicator gammaWeight
  let F : ℝ → ℝ := fun v => criticalTwistedNorm T (u + v)
  have hRep := contourTypeIIRepresentative_spec hu
  have hZeroMem : ρ ∈ dyadicZetaZeros σ T :=
    (Finset.mem_filter.mp hRep.1).1
  rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, mem_ZeroRectangle] at hZeroMem
  have hρLower : 7 / 10 ≤ ρ.re := hσ.trans hZeroMem.1.1
  have hρUpper : ρ.re ≤ 1 := hZeroMem.1.2.1
  have haLower : -(1 / 2 : ℝ) ≤ 1 / 2 - ρ.re := by linarith
  have haUpper : 1 / 2 - ρ.re ≤ -(1 / 5 : ℝ) := by linarith
  have hGammaInt : Integrable gammaWeight := by
    simpa [gammaWeight] using
      (integrable_typeII_Gamma_horizontal haLower haUpper).norm
  have hg : Integrable g := by
    exact hGammaInt.integrableOn.integrable_indicator measurableSet_Icc
  have hFCont : Continuous F := by
    exact (continuous_criticalTwistedNorm T).comp (by fun_prop)
  have hGammaCont : Continuous gammaWeight := by
    exact (continuous_typeII_Gamma_horizontal haLower haUpper).norm
  have hGF4On : IntegrableOn (fun v => gammaWeight v * F v ^ 4) S := by
    exact (hGammaCont.mul (hFCont.pow 4)).continuousOn.integrableOn_Icc
  have hgF4 : Integrable (fun v => g v * F v ^ 4) := by
    have hInd := hGF4On.integrable_indicator measurableSet_Icc
    apply hInd.congr
    filter_upwards with v
    change S.indicator (fun x => gammaWeight x * F x ^ 4) v = g v * F v ^ 4
    by_cases hv : v ∈ S
    · simp only [Set.indicator_of_mem hv, g]
    · simp only [Set.indicator_of_notMem hv, g, zero_mul]
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    by_cases hv : v ∈ S
    · simp only [g, Set.indicator_of_mem hv]
      exact norm_nonneg _
    · simp only [g, Set.indicator_of_notMem hv]
      exact le_rfl
  have hHolder := integral_mul_fourth_holder
    (g := g) (F := F)
    hg0
    (fun v => norm_nonneg _) hg hgF4
  have hGNonneg : 0 ≤ ∫ v, g v := integral_nonneg hg0
  have hGF4Nonneg : 0 ≤ ∫ v, g v * F v ^ 4 := integral_nonneg fun v =>
    mul_nonneg (hg0 v)
      (pow_nonneg (norm_nonneg _) 4)
  have hGLe : ∫ v, g v ≤ 30 := by
    calc
      ∫ v, g v = ∫ v in S, gammaWeight v := by
        rw [← integral_indicator measurableSet_Icc]
      _ ≤ ∫ v, gammaWeight v := by
        rw [← integral_add_compl measurableSet_Icc hGammaInt]
        exact le_add_of_nonneg_right (integral_nonneg fun _ => norm_nonneg _)
      _ ≤ 30 := integral_norm_typeII_Gamma_le_thirty haLower haUpper
  have hCube : (∫ v, g v) ^ 3 ≤ 30 ^ 3 := by
    exact pow_le_pow_left₀ hGNonneg hGLe 3
  have hScaled := mul_le_mul_of_nonneg_right hCube hGF4Nonneg
  have hRewriteGF : ∫ v, g v * F v = ∫ v in S, gammaWeight v * F v := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with v
    change g v * F v = S.indicator (fun x => gammaWeight x * F x) v
    by_cases hv : v ∈ S
    · simp only [g, Set.indicator_of_mem hv]
    · simp only [g, Set.indicator_of_notMem hv, zero_mul]
  have hRewriteGF4 : ∫ v, g v * F v ^ 4 =
      ∫ v in S, gammaWeight v * F v ^ 4 := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with v
    change g v * F v ^ 4 = S.indicator (fun x => gammaWeight x * F x ^ 4) v
    by_cases hv : v ∈ S
    · simp only [g, Set.indicator_of_mem hv]
    · simp only [g, Set.indicator_of_notMem hv, zero_mul]
  rw [hRewriteGF, hRewriteGF4] at hHolder
  rw [hRewriteGF4] at hScaled
  simpa [ρ, S, gammaWeight, F] using hHolder.trans hScaled

theorem representative_gamma_window_fourth_le {σ T u H : ℝ}
    (hu : u ∈ contourTypeIIOrdinates σ T) (hσ : 7 / 10 ≤ σ) :
    ∫ v : ℝ in Set.Icc (-H) H,
        ‖Complex.Gamma
          (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
            (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ^ 4 ≤
      14 * ∫ t : ℝ in Set.Icc (u - H) (u + H),
        twistedZetaMomentIntegrand T t := by
  let ρ := contourTypeIIRepresentative σ T u
  let gammaWeight : ℝ → ℝ := fun v =>
    ‖Complex.Gamma (((1 / 2 - ρ.re : ℝ) : ℂ) + (v : ℂ) * I)‖
  let F : ℝ → ℝ := fun v => criticalTwistedNorm T (u + v)
  have hRep := contourTypeIIRepresentative_spec hu
  have hZeroMem : ρ ∈ dyadicZetaZeros σ T :=
    (Finset.mem_filter.mp hRep.1).1
  rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, mem_ZeroRectangle] at hZeroMem
  have hρLower : 7 / 10 ≤ ρ.re := hσ.trans hZeroMem.1.1
  have hρUpper : ρ.re ≤ 1 := hZeroMem.1.2.1
  have haLower : -(1 / 2 : ℝ) ≤ 1 / 2 - ρ.re := by linarith
  have haUpper : 1 / 2 - ρ.re ≤ -(1 / 5 : ℝ) := by linarith
  have hFCont : Continuous F :=
    (continuous_criticalTwistedNorm T).comp (by fun_prop)
  have hGammaCont : Continuous gammaWeight :=
    (continuous_typeII_Gamma_horizontal haLower haUpper).norm
  have hLeft : IntegrableOn (fun v => gammaWeight v * F v ^ 4)
      (Set.Icc (-H) H) :=
    (hGammaCont.mul (hFCont.pow 4)).continuousOn.integrableOn_Icc
  have hRight : IntegrableOn (fun v => 14 * F v ^ 4) (Set.Icc (-H) H) :=
    (continuous_const.mul (hFCont.pow 4)).continuousOn.integrableOn_Icc
  calc
    ∫ v : ℝ in Set.Icc (-H) H, gammaWeight v * F v ^ 4
        ≤ ∫ v : ℝ in Set.Icc (-H) H, 14 * F v ^ 4 := by
          apply integral_mono_ae hLeft hRight
          filter_upwards with v
          exact mul_le_mul_of_nonneg_right
            (typeII_Gamma_norm_le_fourteen haLower haUpper)
            (pow_nonneg (norm_nonneg _) 4)
    _ = 14 * ∫ v : ℝ in Set.Icc (-H) H, F v ^ 4 := by
      rw [integral_const_mul]
    _ = 14 * ∫ t : ℝ in Set.Icc (u - H) (u + H),
        twistedZetaMomentIntegrand T t := by
      rw [setIntegral_comp_add_Icc (fun t => criticalTwistedNorm T t ^ 4) u H]
      congr 1

theorem separated_windows_fourthMoment_le {σ T G H : ℝ} {W : Finset ℝ}
    (hWU : W ⊆ contourTypeIIOrdinates σ T)
    (hSeparated : IsSeparated G W) (hGap : 2 * H < G)
    (hHT : H ≤ T / 2) (hT : 8 ≤ T) :
    ∑ u ∈ W, ∫ t : ℝ in Set.Icc (u - H) (u + H),
        twistedZetaMomentIntegrand T t ≤ twistedZetaFourthMoment T := by
  let F : ℝ → ℝ := fun t => twistedZetaMomentIntegrand T t
  let target : Set ℝ := Set.Icc (T / 2) (3 * T)
  let window : ℝ → Set ℝ := fun u => Set.Icc (u - H) (u + H)
  have hTpos : 0 < T := by linarith
  have hFCont : Continuous F := by
    change Continuous (fun t => criticalTwistedNorm T t ^ 4)
    exact (continuous_criticalTwistedNorm T).pow 4
  have hF0 : ∀ t, 0 ≤ F t := fun t => by
    dsimp [F, twistedZetaMomentIntegrand]
    positivity
  have hWindowInt : ∀ u ∈ W, Integrable ((window u).indicator F) := by
    intro u hu
    exact hFCont.continuousOn.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hTargetInt : Integrable (target.indicator F) :=
    hFCont.continuousOn.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hMemWindow : ∀ u t, t ∈ window u ↔ dist u t ≤ H := by
    intro u t
    dsimp [window]
    rw [Set.mem_Icc, Real.dist_eq]
    constructor
    · intro ht
      rw [abs_le]
      constructor <;> linarith
    · intro ht
      rw [abs_le] at ht
      constructor <;> linarith
  have hPoint : ∀ t, ∑ u ∈ W, (window u).indicator F t ≤ target.indicator F t := by
    intro t
    let near := W.filter (fun u => dist u t ≤ H)
    have hNearCard : near.card ≤ 1 := by
      exact separated_window_card_le_one W hSeparated hGap t
    have hSumEq : ∑ u ∈ W, (window u).indicator F t = (near.card : ℝ) * F t := by
      calc
        ∑ u ∈ W, (window u).indicator F t =
            ∑ u ∈ W, if dist u t ≤ H then F t else 0 := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases hut : t ∈ window u
              · rw [Set.indicator_of_mem hut, if_pos ((hMemWindow u t).mp hut)]
              · rw [Set.indicator_of_notMem hut, if_neg]
                exact fun hdist => hut ((hMemWindow u t).mpr hdist)
        _ = ∑ _u ∈ near, F t := by
          rw [Finset.sum_filter]
        _ = (near.card : ℝ) * F t := by simp
    rw [hSumEq]
    by_cases htTarget : t ∈ target
    · rw [Set.indicator_of_mem htTarget]
      have hCardReal : (near.card : ℝ) ≤ 1 := by exact_mod_cast hNearCard
      simpa using mul_le_mul_of_nonneg_right hCardReal (hF0 t)
    · rw [Set.indicator_of_notMem htTarget]
      have hNearEmpty : near = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro u huW hdist
        have huU := hWU huW
        have hRep := (contourTypeIIRepresentative_spec huU).1
        have hZeroMem : contourTypeIIRepresentative σ T u ∈ dyadicZetaZeros σ T :=
          (Finset.mem_filter.mp hRep).1
        rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
          Set.mem_inter_iff, mem_ZeroRectangle,
          (contourTypeIIRepresentative_spec huU).2] at hZeroMem
        have hdt : |u - t| ≤ H := by simpa [Real.dist_eq] using hdist
        rw [abs_le] at hdt
        apply htTarget
        change t ∈ Set.Icc (T / 2) (3 * T)
        rw [Set.mem_Icc]
        constructor
        · linarith [hZeroMem.1.2.2.1]
        · linarith [hZeroMem.1.2.2.2]
      rw [hNearEmpty]
      simp
  calc
    ∑ u ∈ W, ∫ t : ℝ in window u, F t =
        ∑ u ∈ W, ∫ t : ℝ, (window u).indicator F t := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [integral_indicator measurableSet_Icc]
    _ = ∫ t : ℝ, ∑ u ∈ W, (window u).indicator F t := by
      rw [integral_finsetSum W hWindowInt]
    _ ≤ ∫ t : ℝ, target.indicator F t := by
      apply integral_mono_ae (integrable_finsetSum W hWindowInt) hTargetInt
      filter_upwards with t
      exact hPoint t
    _ = ∫ t : ℝ in target, F t := integral_indicator measurableSet_Icc
    _ = twistedZetaFourthMoment T := by
      rw [twistedZetaFourthMoment, intervalIntegral.integral_of_le (by linarith)]
      rw [← integral_Icc_eq_integral_Ioc]

/-- The separated representative set has the exact scaled fourth-moment
bound.  All constants are absolute and the exponent is `1 - 2σ`. -/
theorem separated_typeII_card_le_fourthMoment {σ T G H : ℝ} {W : Finset ℝ}
    (hWU : W ⊆ contourTypeIIOrdinates σ T)
    (hSeparated : IsSeparated G W) (hGap : 2 * H < G)
    (hHT : H ≤ T / 2) (hσ : 7 / 10 ≤ σ) (hT : 8 ≤ T)
    (hTail : ∀ u ∈ W,
      ∫ v : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ≤
        1 / (12 * Real.pi)) :
    (W.card : ℝ) ≤
      ((12 * Real.pi) ^ 4 * 30 ^ 3 * 14) *
        T ^ (1 - 2 * σ) * twistedZetaFourthMoment T := by
  let B : ℝ := (12 * Real.pi) * T ^ ((1 / 2 - σ) / 2)
  let windowFourth : ℝ → ℝ := fun u =>
    ∫ v : ℝ in Set.Icc (-H) H,
      ‖Complex.Gamma
        (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
          (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ^ 4
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hEach : ∀ u ∈ W,
      (1 : ℝ) ≤ B ^ 4 * 30 ^ 3 * windowFourth u := by
    intro u hu
    have huU := hWU hu
    have hNear := one_le_representative_gamma_window huU hσ hT (hTail u hu)
    change 1 ≤ B * ∫ v : ℝ in Set.Icc (-H) H,
      ‖Complex.Gamma
        (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
          (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) at hNear
    have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hNear 4
    have hHolder := representative_gamma_window_holder (H := H) huU hσ
    have hScale0 : 0 ≤ B ^ 4 := pow_nonneg hB0 4
    calc
      (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (B * ∫ v : ℝ in Set.Icc (-H) H,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v)) ^ 4 := hPow
      _ = B ^ 4 * (∫ v : ℝ in Set.Icc (-H) H,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v)) ^ 4 := by
            rw [mul_pow]
      _ ≤ B ^ 4 * (30 ^ 3 * windowFourth u) :=
        mul_le_mul_of_nonneg_left hHolder hScale0
      _ = B ^ 4 * 30 ^ 3 * windowFourth u := by ring
  have hSum : (W.card : ℝ) ≤
      B ^ 4 * 30 ^ 3 * ∑ u ∈ W, windowFourth u := by
    calc
      (W.card : ℝ) = ∑ _u ∈ W, (1 : ℝ) := by simp
      _ ≤ ∑ u ∈ W, B ^ 4 * 30 ^ 3 * windowFourth u := by
        exact Finset.sum_le_sum hEach
      _ = B ^ 4 * 30 ^ 3 * ∑ u ∈ W, windowFourth u := by
        rw [Finset.mul_sum]
  have hFourth : ∑ u ∈ W, windowFourth u ≤
      14 * twistedZetaFourthMoment T := by
    calc
      ∑ u ∈ W, windowFourth u ≤
          ∑ u ∈ W, 14 * ∫ t : ℝ in Set.Icc (u - H) (u + H),
            twistedZetaMomentIntegrand T t := by
              apply Finset.sum_le_sum
              intro u hu
              exact representative_gamma_window_fourth_le (hWU hu) hσ
      _ = 14 * ∑ u ∈ W, ∫ t : ℝ in Set.Icc (u - H) (u + H),
          twistedZetaMomentIntegrand T t := by
            rw [Finset.mul_sum]
      _ ≤ 14 * twistedZetaFourthMoment T := by
        exact mul_le_mul_of_nonneg_left
          (separated_windows_fourthMoment_le hWU hSeparated hGap hHT hT)
          (by norm_num)
  have hCoeff0 : 0 ≤ B ^ 4 * 30 ^ 3 := by positivity
  calc
    (W.card : ℝ) ≤ B ^ 4 * 30 ^ 3 * ∑ u ∈ W, windowFourth u := hSum
    _ ≤ B ^ 4 * 30 ^ 3 * (14 * twistedZetaFourthMoment T) :=
      mul_le_mul_of_nonneg_left hFourth hCoeff0
    _ = ((12 * Real.pi) ^ 4 * 30 ^ 3 * 14) *
        T ^ (1 - 2 * σ) * twistedZetaFourthMoment T := by
      have hTpos : 0 < T := by linarith
      dsimp [B]
      rw [mul_pow]
      rw [show (T ^ ((1 / 2 - σ) / 2)) ^ 4 =
          T ^ (1 - 2 * σ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
        congr 1
        ring]
      ring

/-- Native Maynard--Pratt Lemma 24 for the project's multiplicity-weighted
dyadic zeta-zero family. -/
theorem typeIIFourthMomentReduction_native :
    TypeIIFourthMomentReductionProp dyadicZetaZeros
      (analyticVanishingOrder riemannZeta) zetaIsContourTypeII := by
  intro σ hσLower hσUpper ε hε
  obtain ⟨CJ, hCJ, hJensen⟩ := zeroUnitJensenCeil_le_log
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hδEps : δ ≤ ε / 4 := min_le_left _ _
  have hδHalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨n, hn, hTailEventually⟩ :=
    eventually_representative_typeII_gamma_tail_small δ hδ
  let C0 : ℝ := (12 * Real.pi) ^ 4 * 30 ^ 3 * 14
  let Q : ℝ := (ε / 4)⁻¹ ^ 2
  let C : ℝ := 10 * CJ * Q * C0
  apply IsBigO.of_bound C
  filter_upwards [hTailEventually, eventually_ge_atTop (Real.exp 2),
    eventually_ge_atTop (16 : ℝ)] with T hTailT hTExp hTSixteen
  have hTEight : 8 ≤ T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hLogOne : 1 ≤ Real.log T := by
    have hLogTwo : 2 ≤ Real.log T := by
      have h := Real.log_le_log (Real.exp_pos 2) hTExp
      simpa using h
    linarith
  let H : ℝ := T ^ δ
  let G : ℝ := 3 * H
  have hHOne : 1 ≤ H := Real.one_le_rpow hTOne hδ.le
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hHOne
  have hGOne : 1 ≤ G := by dsimp [G]; linarith
  have hGap : 2 * H < G := by dsimp [G]; linarith
  have hHT : H ≤ T / 2 := by
    have hPowHalf : H ≤ T ^ (1 / 2 : ℝ) := by
      dsimp [H]
      exact Real.rpow_le_rpow_of_exponent_le hTOne hδHalf
    have hSqrt : T ^ (1 / 2 : ℝ) = Real.sqrt T := by
      rw [Real.sqrt_eq_rpow]
    have hSq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
    have hSqrtNonneg := Real.sqrt_nonneg T
    rw [hSqrt] at hPowHalf
    have hSqrtLe : Real.sqrt T ≤ T / 2 := by nlinarith
    exact hPowHalf.trans hSqrtLe
  obtain ⟨W, hWU, hSeparated, hCount⟩ :=
    exists_scaled_separated_contourTypeII_ordinates σ T G
      (by linarith) hTEight hGOne
  have hTailW : ∀ u ∈ W,
      ∫ v : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖Complex.Gamma
            (((1 / 2 - (contourTypeIIRepresentative σ T u).re : ℝ) : ℂ) +
              (v : ℂ) * I)‖ * criticalTwistedNorm T (u + v) ≤
        1 / (12 * Real.pi) := by
    intro u hu
    simpa [H] using hTailT hTEight σ u hσLower (hWU hu)
  have hCard := separated_typeII_card_le_fourthMoment hWU hSeparated hGap
    hHT hσLower hTEight hTailW
  have hJ : (zeroUnitJensenCeil T : ℝ) ≤ CJ * Real.log T := hJensen T hTExp
  have hCeil : (⌈G⌉₊ : ℝ) < G + 1 :=
    Nat.ceil_lt_add_one (by positivity : 0 ≤ G)
  have hCeilFactor : ((⌈G⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * H := by
    push_cast
    dsimp [G] at hCeil ⊢
    linarith
  have hCeilFactor' : (⌈G⌉₊ : ℝ) + 1 ≤ 5 * H := by
    simpa only [Nat.cast_add, Nat.cast_one] using hCeilFactor
  have hLoss :
      ((2 * ((⌈G⌉₊ + 1) * zeroUnitJensenCeil T) : ℕ) : ℝ) ≤
        10 * CJ * H * Real.log T := by
    push_cast
    calc
      2 * (((⌈G⌉₊ : ℝ) + 1) * (zeroUnitJensenCeil T : ℝ))
          ≤ 2 * ((5 * H) * (CJ * Real.log T)) := by gcongr
      _ = 10 * CJ * H * Real.log T := by ring
  have hCountReal :
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T ≤
        (10 * CJ * H * Real.log T) * (W.card : ℝ) := by
    calc
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T
          ≤ ((2 * ((⌈G⌉₊ + 1) * zeroUnitJensenCeil T) * W.card : ℕ) : ℝ) := hCount
      _ = ((2 * ((⌈G⌉₊ + 1) * zeroUnitJensenCeil T) : ℕ) : ℝ) *
          (W.card : ℝ) := by push_cast; ring
      _ ≤ (10 * CJ * H * Real.log T) * (W.card : ℝ) := by
        gcongr
  have hMomentNonneg : 0 ≤ twistedZetaFourthMoment T := by
    rw [twistedZetaFourthMoment, intervalIntegral.integral_of_le (by linarith)]
    apply integral_nonneg
    intro t
    dsimp [twistedZetaMomentIntegrand]
    positivity
  have hBaseNonneg : 0 ≤ T ^ (1 - 2 * σ) * twistedZetaFourthMoment T :=
    mul_nonneg (Real.rpow_nonneg hTpos.le _) hMomentNonneg
  have hRaw :
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T ≤
        (10 * CJ * H * Real.log T) *
          (C0 * T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) :=
    hCountReal.trans (mul_le_mul_of_nonneg_left hCard (by positivity))
  have hLogSq : Real.log T ≤ (Real.log T) ^ 2 := by nlinarith
  have hHLoss : H * Real.log T ≤ Q * T ^ ε := by
    have hLossEps := rpow_mul_log_sq_le_epsilon ε δ T hε hδEps hTOne
    change H * (Real.log T) ^ 2 ≤ Q * T ^ ε at hLossEps
    have hFirst : H * Real.log T ≤ H * (Real.log T) ^ 2 :=
      mul_le_mul_of_nonneg_left hLogSq (by positivity)
    exact hFirst.trans hLossEps
  have hFinal :
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T ≤
        C * T ^ ε *
          (T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) := by
    calc
      weightedCount dyadicZetaZeros (analyticVanishingOrder riemannZeta)
          zetaIsContourTypeII σ T
          ≤ (10 * CJ * H * Real.log T) *
              (C0 * T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) := hRaw
      _ = (10 * CJ * (H * Real.log T)) * C0 *
          (T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) := by ring
      _ ≤ (10 * CJ * (Q * T ^ ε)) * C0 *
          (T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) := by
            gcongr
      _ = C * T ^ ε *
          (T ^ (1 - 2 * σ) * twistedZetaFourthMoment T) := by
            dsimp [C]
            ring
  have hCountNonneg : 0 ≤ weightedCount dyadicZetaZeros
      (analyticVanishingOrder riemannZeta) zetaIsContourTypeII σ T := by
    unfold weightedCount
    positivity
  have hPowEpsNonneg : 0 ≤ T ^ ε := Real.rpow_nonneg hTpos.le _
  have hPowSigmaNonneg : 0 ≤ T ^ (1 - 2 * σ) := Real.rpow_nonneg hTpos.le _
  simpa [Real.norm_eq_abs, mul_assoc, abs_of_nonneg hCountNonneg,
    abs_of_nonneg hPowEpsNonneg, abs_of_nonneg hPowSigmaNonneg,
    abs_of_nonneg hMomentNonneg,
    abs_of_nonneg hBaseNonneg,
    abs_of_nonneg (mul_nonneg hPowEpsNonneg hBaseNonneg)] using hFinal

end RiemannZeta.GuthMaynard
