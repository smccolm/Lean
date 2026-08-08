import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import RiemannZeta.GuthMaynard.Pigeonhole
import RiemannZeta.GuthMaynard.DirichletPolynomial
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ZeroDetector

open Complex Finset
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- Number of Type I zeros in the rectangle, counted with analytic multiplicity. -/
noncomputable def typeIZeroCount (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => IsTypeIZero ρ T),
    analyticVanishingOrder riemannZeta s

/-- Total zero count is the sum of Type I and residual zeros. -/
lemma typeI_add_residual_eq_total (σ T1 T2 T : ℝ) :
    typeIZeroCount σ T1 T2 T + residualZeroCount σ T1 T2 T =
      zeroCountRect σ 1 T1 T2 := by
  have hResidual : residualZeroCount σ T1 T2 T =
      ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => ¬ IsTypeIZero ρ T),
        analyticVanishingOrder riemannZeta s := by
    unfold residualZeroCount IsResidualZero
    apply Finset.sum_congr
    · ext x
      simp only [Finset.mem_filter]
      tauto
    · intros
      rfl
  rw [hResidual]
  unfold typeIZeroCount zeroCountRect
  exact Finset.sum_filter_add_sum_filter_not
    (zerosInRect σ 1 T1 T2) (fun ρ => IsTypeIZero ρ T)
      (fun s => analyticVanishingOrder riemannZeta s)

/-- The finite set of Type I zeros in the dyadic height slab. -/
noncomputable def typeIZeroSet (σ T : ℝ) : Finset ℂ :=
  (zerosInRect σ 1 T (2 * T)).filter (fun ρ => IsTypeIZero ρ T)

/-- Choose one admissible detecting scale for a Type I point. -/
noncomputable def chosenTypeIScale (ρ : ℂ) (T : ℝ) : ℕ :=
  if h : IsTypeIZero ρ T then Classical.choose h else 0

lemma chosenTypeIScale_spec (ρ : ℂ) (T : ℝ) (hρ : IsTypeIZero ρ T) :
    IsTypeIZeroAtScale ρ T (chosenTypeIScale ρ T) := by
  rw [chosenTypeIScale, dif_pos hρ]
  exact Classical.choose_spec hρ

lemma chosenTypeIScale_mem (ρ : ℂ) (T : ℝ) (hρ : IsTypeIZero ρ T) :
    chosenTypeIScale ρ T ∈ admissibleDyadicIndices T :=
  (chosenTypeIScale_spec ρ T hρ).1

/-- Type I zeros assigned to one chosen dyadic scale. -/
noncomputable def assignedTypeIZeroSet (σ T : ℝ) (j : ℕ) : Finset ℂ :=
  (typeIZeroSet σ T).filter (fun ρ => chosenTypeIScale ρ T = j)

/-- Aggregate analytic multiplicities over equal values of a chosen ordinate map. -/
noncomputable def shiftedMultiplicity (S : Finset ℂ) (shift : ℂ → ℝ) (t : ℝ) : ℕ :=
  ∑ ρ ∈ S.filter (fun z => shift z = t), analyticVanishingOrder riemannZeta ρ

/-- Fiber decomposition preserves the complete weighted count. -/
lemma sum_shiftedMultiplicity (S : Finset ℂ) (shift : ℂ → ℝ) :
    ∑ t ∈ S.image shift, shiftedMultiplicity S shift t =
      ∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ := by
  have hAll : S.filter (fun ρ => shift ρ ∈ S.image shift) = S := by
    apply Finset.filter_eq_self.mpr
    intro ρ hρ
    exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter
    S (S.image shift) shift (analyticVanishingOrder riemannZeta)
  rw [hAll] at hFiber
  exact hFiber

/--
A displacement by at most `H` turns one shifted unit bin into at most
`2 * ceil H + 1` original unit bins.  This is the finite covering step needed
to keep the analytic hypothesis about unshifted zero ordinates.
-/
theorem shifted_bin_weight_le_of_unit_bin_weight {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate shift : α → ℝ) (H : ℝ) (L : ℕ)
    (hShift : ∀ x ∈ S, |ordinate x - shift x| ≤ H)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L)
    (z : ℤ) :
    ∑ t ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ S.filter (fun y => shift y = t), weight x ≤
      (2 * ⌈H⌉₊ + 1) * L := by
  let A := S.filter (fun x => (z : ℝ) ≤ shift x ∧ shift x < (z : ℝ) + 1)
  let k : ℕ := ⌈H⌉₊
  let J : Finset ℤ := Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))
  have hShiftFiber :
      ∑ t ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
          ∑ x ∈ S.filter (fun y => shift y = t), weight x =
        ∑ x ∈ A, weight x := by
    have hFiber := Finset.sum_fiberwise_eq_sum_filter S
      ((S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1)) shift weight
    have hFilter : S.filter (fun x =>
        shift x ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1)) = A := by
      apply Finset.filter_congr
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · exact fun h => h.2
      · exact fun hz => ⟨⟨x, hx, rfl⟩, hz⟩
    rw [hFilter] at hFiber
    exact hFiber
  have hFloors : ∀ x ∈ A, ⌊ordinate x⌋ ∈ J := by
    intro x hx
    have hxData := Finset.mem_filter.mp hx
    have hDisp := hShift x hxData.1
    rw [abs_le] at hDisp
    have hk : H ≤ (k : ℝ) := by
      exact Nat.le_ceil H
    change ⌊ordinate x⌋ ∈ Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      have hCast : ((z - (k : ℤ) : ℤ) : ℝ) = (z : ℝ) - (k : ℝ) := by
        norm_num
      rw [hCast]
      linarith [hxData.2.1, hDisp.1]
    · have hFloorLt : ⌊ordinate x⌋ < z + (k : ℤ) + 1 := by
        rw [Int.floor_lt]
        have hCast : ((z + (k : ℤ) + 1 : ℤ) : ℝ) = (z : ℝ) + (k : ℝ) + 1 := by
          norm_num
        rw [hCast]
        linarith [hxData.2.2, hDisp.2]
      omega
  have hAll : A.filter (fun x => ⌊ordinate x⌋ ∈ J) = A :=
    Finset.filter_eq_self.mpr hFloors
  have hFloorFiber := Finset.sum_fiberwise_eq_sum_filter A J
    (fun x => ⌊ordinate x⌋) weight
  rw [hAll] at hFloorFiber
  rw [hShiftFiber, ← hFloorFiber]
  calc
    ∑ j ∈ J, ∑ x ∈ A.filter (fun y => ⌊ordinate y⌋ = j), weight x
        ≤ ∑ _j ∈ J, L := by
      apply Finset.sum_le_sum
      intro j hj
      apply le_trans (Finset.sum_le_sum_of_subset ?_) (hLocal j)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨(Finset.mem_filter.mp hx.1).1, ?_⟩
      exact Int.floor_eq_iff.mp hx.2
    _ = J.card * L := by simp
    _ = (2 * k + 1) * L := by
      congr 1
      change (Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))).card = 2 * k + 1
      rw [Int.card_Icc]
      omega

/-- Exact weighted pigeonholing over a nonempty finite family of fibers. -/
theorem weighted_finite_pigeonhole {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (J : Finset κ) (weight : α → ℕ) (scale : α → κ)
    (hS : S.Nonempty) (hScale : ∀ x ∈ S, scale x ∈ J) :
    ∃ j ∈ J,
      ∑ x ∈ S, weight x ≤ J.card * ∑ x ∈ S.filter (fun y => scale y = j), weight x := by
  have hJ : J.Nonempty := by
    rcases hS with ⟨x, hx⟩
    exact ⟨scale x, hScale x hx⟩
  let fiberWeight (j : κ) : ℕ :=
    ∑ x ∈ S.filter (fun y => scale y = j), weight x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J fiberWeight hJ
  refine ⟨j, hj, ?_⟩
  have hAll : S.filter (fun x => scale x ∈ J) = S :=
    Finset.filter_eq_self.mpr hScale
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S J scale weight
  rw [hAll] at hFiber
  rw [← hFiber]
  calc
    ∑ k ∈ J, fiberWeight k ≤ ∑ _k ∈ J, fiberWeight j := by
      apply Finset.sum_le_sum
      intro k hk
      exact hmax k hk
    _ = J.card * fiberWeight j := by simp

/--
The exact finite extraction step. It contains the real combinatorial deduction:
dyadic pigeonholing, aggregation of multiplicities over shifted ordinates, and
weighted one-dimensional separated selection.
-/
theorem finite_weighted_extract_separated {α κ : Type*}
    [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (J : Finset κ) (weight : α → ℕ) (scale : α → κ)
    (shift : κ → α → ℝ) (large : κ → ℝ → Prop) (inInterval : ℝ → Prop)
    (L : ℕ) (hS : S.Nonempty) (hScale : ∀ x ∈ S, scale x ∈ J)
    (hLocal : ∀ j ∈ J, ∀ z : ℤ,
      ∑ t ∈ (S.filter (fun x => scale x = j)).image (shift j) |>.filter
        (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ (S.filter (fun y => scale y = j)).filter (fun y => shift j y = t), weight x ≤ L)
    (hLarge : ∀ j ∈ J, ∀ x ∈ S, scale x = j → large j (shift j x))
    (hInterval : ∀ j ∈ J, ∀ x ∈ S, scale x = j → inInterval (shift j x)) :
    ∃ j ∈ J, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, large j t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤ 2 * J.card * L * W.card := by
  obtain ⟨j, hj, hPigeon⟩ :=
    weighted_finite_pigeonhole S J weight scale hS hScale
  let A := S.filter (fun x => scale x = j)
  let shiftedWeight (t : ℝ) : ℕ :=
    ∑ x ∈ A.filter (fun y => shift j y = t), weight x
  have hSelectLocal : ∀ z : ℤ,
      ∑ t ∈ (A.image (shift j)).filter
        (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1), shiftedWeight t ≤ L := by
    intro z
    exact hLocal j hj z
  obtain ⟨W, hWA, hSeparated, hWeight⟩ :=
    weighted_separated_selection (A.image (shift j)) shiftedWeight L hSelectLocal
  refine ⟨j, hj, W, hSeparated, ?_, ?_, ?_⟩
  · intro t ht
    have htA := hWA ht
    rw [Finset.mem_image] at htA
    rcases htA with ⟨x, hx, rfl⟩
    exact hLarge j hj x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro t ht
    have htA := hWA ht
    rw [Finset.mem_image] at htA
    rcases htA with ⟨x, hx, rfl⟩
    exact hInterval j hj x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · have hFiber : ∑ t ∈ A.image (shift j), shiftedWeight t = ∑ x ∈ A, weight x := by
      have hAll : A.filter (fun x => shift j x ∈ A.image (shift j)) = A := by
        apply Finset.filter_eq_self.mpr
        intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hFiberwise := Finset.sum_fiberwise_eq_sum_filter A (A.image (shift j)) (shift j) weight
      rw [hAll] at hFiberwise
      exact hFiberwise
    rw [hFiber] at hWeight
    calc
      ∑ x ∈ S, weight x ≤ J.card * ∑ x ∈ A, weight x := hPigeon
      _ ≤ J.card * (2 * L * W.card) := Nat.mul_le_mul_left _ hWeight
      _ = 2 * J.card * L * W.card := by ring

/--
Pointwise beta-removal input. It is strictly upstream of extraction: it supplies
one nearby fixed-line large value for each Type I zero, but performs no counting
or separated selection.
-/
def DetectorBetaShiftProp : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      ∀ ρ ∈ typeIZeroSet σ T,
        ∃ γ' : ℝ,
          |ρ.im - γ'| ≤ T ^ δ ∧
          1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale ρ T) (σ + I * γ') T‖

/-- Detector coefficients after restricting the real part to the line `Re s = σ`. -/
noncomputable def detectorLineCoeffs (σ T : ℝ) (n : ℕ) : ℂ :=
  detectorCoeff n T * (n : ℂ) ^ (-(σ : ℂ))

/-- Evaluation on a vertical line is an interval-indexed Dirichlet polynomial. -/
theorem detectPoly_eq_dirichletPoly (N : ℕ) (σ t T : ℝ) :
    detectPoly N (σ + I * t) T = dirichletPoly N (detectorLineCoeffs σ T) t := by
  unfold detectPoly dirichletPoly detectorLineCoeffs dyadicInterval
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    rw [Finset.mem_Ioc] at hn
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  ring

/-- Coefficients after translating the ordinate by `c`. -/
noncomputable def translatedDetectorCoeffs (σ T c : ℝ) : ℕ → ℂ :=
  phaseShiftCoeffs c (detectorLineCoeffs σ T)

/-- The detector value is preserved by simultaneous ordinate and coefficient translation. -/
theorem detectPoly_translate (N : ℕ) (σ T c u : ℝ) :
    detectPoly N (σ + I * ((u + c : ℝ) : ℂ)) T =
      dirichletPoly N (translatedDetectorCoeffs σ T c) u := by
  rw [detectPoly_eq_dirichletPoly, dirichletPoly_translate]
  rfl

/-- Translation changes only the phases of the fixed-line detector coefficients. -/
theorem norm_translatedDetectorCoeffs (σ T c : ℝ) (n : ℕ) :
    ‖translatedDetectorCoeffs σ T c n‖ = ‖detectorLineCoeffs σ T n‖ := by
  exact norm_phaseShiftCoeffs c (detectorLineCoeffs σ T) n

/--
The analytic local-zero input: multiplicity in every ordinary unit interval of
the original Type I ordinates is `O(log T)`.  It knows nothing about a chosen
detector scale or a beta-removal displacement.
-/
def LocalZeroMultiplicityBoundProp : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      ∃ L : ℕ, (L : ℝ) ≤ C * Real.log T ∧
        ∀ z : ℤ,
          ∑ ρ ∈ (typeIZeroSet σ T).filter
            (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
            analyticVanishingOrder riemannZeta ρ ≤ L

/-- Membership in the enlarged interval forced by beta removal. -/
def InShiftedTargetInterval (T H : ℝ) (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, t ∈ Set.Icc (T - H) (2 * T + H)

/-- Two logarithmic losses and a smaller displacement power fit inside `T^ε`. -/
theorem rpow_mul_log_sq_le_epsilon (ε δ T : ℝ) (hε : 0 < ε)
    (hδLe : δ ≤ ε / 4) (hT : 1 ≤ T) :
    T ^ δ * (Real.log T) ^ 2 ≤ (ε / 4)⁻¹ ^ 2 * T ^ ε := by
  let q := ε / 4
  have hq : 0 < q := div_pos hε (by norm_num)
  have hTPos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTNonneg : 0 ≤ T := le_trans (by norm_num) hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hPowQNonneg : 0 ≤ T ^ q := Real.rpow_nonneg hTNonneg _
  have hLog : Real.log T ≤ T ^ q / q := Real.log_le_rpow_div hTNonneg hq
  have hQuotNonneg : 0 ≤ T ^ q / q := div_nonneg hPowQNonneg hq.le
  have hLogSq : (Real.log T) ^ 2 ≤ (T ^ q / q) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLog) (add_nonneg hQuotNonneg hLogNonneg)]
  have hExponent : δ + q + q ≤ ε := by
    dsimp [q] at hδLe ⊢
    linarith
  have hPowExponent : T ^ (δ + q + q) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hT hExponent
  calc
    T ^ δ * (Real.log T) ^ 2 ≤ T ^ δ * (T ^ q / q) ^ 2 := by
      gcongr
    _ = q⁻¹ ^ 2 * T ^ (δ + q + q) := by
      rw [div_eq_mul_inv]
      calc
        T ^ δ * (T ^ q * q⁻¹) ^ 2 = q⁻¹ ^ 2 * ((T ^ δ * T ^ q) * T ^ q) := by
          ring
        _ = q⁻¹ ^ 2 * T ^ (δ + q + q) := by
          rw [← Real.rpow_add hTPos δ q, ← Real.rpow_add hTPos (δ + q) q]
    _ ≤ q⁻¹ ^ 2 * T ^ ε := by gcongr
    _ = (ε / 4)⁻¹ ^ 2 * T ^ ε := by rfl

/-- Raw F-05 output before translation and epsilon-loss absorption. -/
def RawExtractSeparatedTarget : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      typeIZeroCount σ T (2 * T) T = 0 ∨
        ∃ (W : Finset ℝ) (j : ℕ),
          j ∈ admissibleDyadicIndices T ∧
          IsSeparated 1 W ∧
          InShiftedTargetInterval T (T ^ δ) W ∧
          (∀ γ' ∈ W,
            1 / (4 * Real.log T) ≤ ‖detectPoly (2 ^ j) (σ + I * γ') T‖) ∧
          (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            C * T ^ δ * (W.card : ℝ) * (Real.log T) ^ 2

/--
The raw F-05 bound follows from pointwise beta removal and the unshifted
unit-zero input.  The shifted occupancy estimate is proved here by finite
covering rather than assumed.
-/
theorem rawExtractSeparated_of_beta_shift_and_local_multiplicity
    (hBeta : DetectorBetaShiftProp) (hLocal : LocalZeroMultiplicityBoundProp) :
    RawExtractSeparatedTarget := by
  intro δ hδ
  obtain ⟨Tβ, hTβBase, hBetaAll⟩ := hBeta δ hδ
  obtain ⟨CL, TL, hCL, hTLBase, hLocalAll⟩ := hLocal
  let K : ℝ := (5 / 2 : ℝ) / Real.log 2 + 1 / 2
  refine ⟨10 * K * CL, max Tβ TL, ?_, ?_, ?_⟩
  · have hK : 0 < K := by
      dsimp [K]
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    positivity
  · exact le_max_of_le_left hTβBase
  · intro σ T hσLower hσUpper hT
    have hTβ : Tβ ≤ T := le_trans (le_max_left _ _) hT
    have hTL : TL ≤ T := le_trans (le_max_right _ _) hT
    have hTBase : Real.exp 2 ≤ T := le_trans hTLBase hTL
    have hTOne : 1 ≤ T := by
      have : (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      exact (this.trans_le hTBase).le
    have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
    let S := typeIZeroSet σ T
    by_cases hSEmpty : S = ∅
    · left
      change typeIZeroSet σ T = ∅ at hSEmpty
      unfold typeIZeroCount
      change ∑ ρ ∈ typeIZeroSet σ T, analyticVanishingOrder riemannZeta ρ = 0
      rw [hSEmpty]
      simp
    · right
      have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
      have hBetaPoint : ∀ ρ ∈ S, ∃ γ' : ℝ,
          |ρ.im - γ'| ≤ T ^ δ ∧
          1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale ρ T) (σ + I * γ') T‖ := by
        intro ρ hρ
        exact hBetaAll σ T hσLower hσUpper hTβ ρ hρ
      let shift (ρ : ℂ) : ℝ :=
        if hρ : ρ ∈ S then Classical.choose (hBetaPoint ρ hρ) else ρ.im
      have hShift (ρ : ℂ) (hρ : ρ ∈ S) : |ρ.im - shift ρ| ≤ T ^ δ := by
        simp only [shift, dif_pos hρ]
        exact (Classical.choose_spec (hBetaPoint ρ hρ)).1
      have hShiftLarge (ρ : ℂ) (hρ : ρ ∈ S) :
          1 / (4 * Real.log T) ≤
            ‖detectPoly (2 ^ chosenTypeIScale ρ T) (σ + I * shift ρ) T‖ := by
        simp only [shift, dif_pos hρ]
        exact (Classical.choose_spec (hBetaPoint ρ hρ)).2
      obtain ⟨L₀, hL₀Size, hUnitBins⟩ :=
        hLocalAll σ T hσLower hσUpper hTL
      let k : ℕ := ⌈T ^ δ⌉₊
      let L : ℕ := (2 * k + 1) * L₀
      have hPowNonneg : 0 ≤ T ^ δ := Real.rpow_nonneg (le_trans (by norm_num) hTOne) _
      have hPowOne : 1 ≤ T ^ δ := Real.one_le_rpow hTOne hδ.le
      have hkLt : (k : ℝ) < T ^ δ + 1 := by
        exact Nat.ceil_lt_add_one hPowNonneg
      have hCoverFactor : ((2 * k + 1 : ℕ) : ℝ) ≤ 5 * T ^ δ := by
        push_cast
        linarith
      have hLSize : (L : ℝ) ≤ 5 * CL * T ^ δ * Real.log T := by
        change (((2 * k + 1) * L₀ : ℕ) : ℝ) ≤ 5 * CL * T ^ δ * Real.log T
        calc
          (((2 * k + 1) * L₀ : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) * (L₀ : ℝ) := by
            norm_num
          _ ≤ (5 * T ^ δ) * (L₀ : ℝ) :=
            mul_le_mul_of_nonneg_right hCoverFactor (Nat.cast_nonneg L₀)
          _ ≤ (5 * T ^ δ) * (CL * Real.log T) := by gcongr
          _ = 5 * CL * T ^ δ * Real.log T := by ring
      have hScale : ∀ ρ ∈ S, chosenTypeIScale ρ T ∈ admissibleDyadicIndices T := by
        intro ρ hρ
        exact chosenTypeIScale_mem ρ T (Finset.mem_filter.mp hρ).2
      have hLocalGeneric : ∀ j ∈ admissibleDyadicIndices T, ∀ z : ℤ,
          ∑ t ∈ (S.filter (fun ρ => chosenTypeIScale ρ T = j)).image shift |>.filter
            (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
            ∑ ρ ∈ (S.filter (fun y => chosenTypeIScale y T = j)).filter
              (fun y => shift y = t), analyticVanishingOrder riemannZeta ρ ≤ L := by
        intro j hj z
        let A := S.filter (fun ρ => chosenTypeIScale ρ T = j)
        have hShiftA : ∀ ρ ∈ A, |ρ.im - shift ρ| ≤ T ^ δ := by
          intro ρ hρ
          exact hShift ρ (Finset.mem_filter.mp hρ).1
        have hUnitA : ∀ u : ℤ,
            ∑ ρ ∈ A.filter (fun y => (u : ℝ) ≤ y.im ∧ y.im < (u : ℝ) + 1),
              analyticVanishingOrder riemannZeta ρ ≤ L₀ := by
          intro u
          apply le_trans (Finset.sum_le_sum_of_subset ?_) (hUnitBins u)
          intro ρ hρ
          rw [Finset.mem_filter] at hρ ⊢
          exact ⟨(Finset.mem_filter.mp hρ.1).1, hρ.2⟩
        exact shifted_bin_weight_le_of_unit_bin_weight A
          (analyticVanishingOrder riemannZeta) Complex.im shift (T ^ δ) L₀
          hShiftA hUnitA z
      have hLargeGeneric : ∀ j ∈ admissibleDyadicIndices T, ∀ ρ ∈ S,
          chosenTypeIScale ρ T = j →
          1 / (4 * Real.log T) ≤ ‖detectPoly (2 ^ j) (σ + I * shift ρ) T‖ := by
        intro j hj ρ hρ hScaleEq
        simpa [hScaleEq] using hShiftLarge ρ hρ
      have hIntervalGeneric : ∀ j ∈ admissibleDyadicIndices T, ∀ ρ ∈ S,
          chosenTypeIScale ρ T = j → shift ρ ∈ Set.Icc (T - T ^ δ) (2 * T + T ^ δ) := by
        intro j hj ρ hρ hScaleEq
        have hZeroMem : ρ ∈ zerosInRect σ 1 T (2 * T) := (Finset.mem_filter.mp hρ).1
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hZeroMem
        have hRect := hZeroMem.1
        rw [mem_ZeroRectangle] at hRect
        have hDisplacement := hShift ρ hρ
        rw [abs_le] at hDisplacement
        constructor <;> linarith
      obtain ⟨j, hj, W, hSep, hLargeW, hIntervalW, hCount⟩ :=
        finite_weighted_extract_separated S (admissibleDyadicIndices T)
          (analyticVanishingOrder riemannZeta) (fun ρ => chosenTypeIScale ρ T)
          (fun _j ρ => shift ρ)
          (fun j t => 1 / (4 * Real.log T) ≤ ‖detectPoly (2 ^ j) (σ + I * t) T‖)
          (fun t => t ∈ Set.Icc (T - T ^ δ) (2 * T + T ^ δ)) L hS hScale
          hLocalGeneric hLargeGeneric hIntervalGeneric
      refine ⟨W, j, hj, hSep, ?_, hLargeW, ?_⟩
      · intro t ht
        exact hIntervalW t ht
      · have hScaleCardNat := admissibleDyadicIndices_card_le T
        have hScaleCountReal : ((admissibleDyadicIndices T).card : ℝ) ≤ K * Real.log T := by
          calc
            ((admissibleDyadicIndices T).card : ℝ)
                ≤ (dyadicScaleIndexCount T : ℝ) := by exact_mod_cast hScaleCardNat
            _ ≤ K * Real.log T := dyadicScaleIndexCount_le_log T hTBase
        have hCountReal : (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            2 * ((admissibleDyadicIndices T).card : ℝ) * (L : ℝ) * (W.card : ℝ) := by
          exact_mod_cast hCount
        calc
          (typeIZeroCount σ T (2 * T) T : ℝ)
              ≤ 2 * ((admissibleDyadicIndices T).card : ℝ) * (L : ℝ) * (W.card : ℝ) :=
            hCountReal
          _ ≤ 2 * (K * Real.log T) * (5 * CL * T ^ δ * Real.log T) * (W.card : ℝ) := by
            gcongr
          _ = (10 * K * CL) * T ^ δ * (W.card : ℝ) * (Real.log T) ^ 2 := by ring

/--
Downstream-ready F-05 target.  The selected ordinates have been translated to
`[0, 3T]`, the detector has been rewritten with phase-twisted coefficients,
and every logarithmic loss has been absorbed into the requested epsilon.
-/
def ExtractSeparatedTarget : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      typeIZeroCount σ T (2 * T) T = 0 ∨
        ∃ (W : Finset ℝ) (j : ℕ) (H c : ℝ),
          j ∈ admissibleDyadicIndices T ∧
          0 ≤ H ∧ H ≤ T ^ (ε / 4) ∧ H ≤ T ∧ c = T - H ∧
          IsSeparated 1 W ∧
          InBaseInterval (3 * T) W ∧
          (∀ u ∈ W,
            1 / (4 * Real.log T) ≤
              ‖dirichletPoly (2 ^ j) (translatedDetectorCoeffs σ T c) u‖) ∧
          (∀ n, ‖translatedDetectorCoeffs σ T c n‖ = ‖detectorLineCoeffs σ T n‖) ∧
          (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            C * T ^ ε * (W.card : ℝ)

/--
The normalized F-05 theorem from the two genuine upstream analytic inputs.
Its proof performs shifted-bin covering, finite extraction, translation of the
set and coefficients, and epsilon-loss absorption.
-/
theorem extractSeparated_of_beta_shift_and_local_multiplicity
    (hBeta : DetectorBetaShiftProp) (hLocal : LocalZeroMultiplicityBoundProp) :
    ExtractSeparatedTarget := by
  have hRaw := rawExtractSeparated_of_beta_shift_and_local_multiplicity hBeta hLocal
  intro ε hε
  let δ := min (ε / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hδEps : δ ≤ ε / 4 := min_le_left _ _
  have hδOne : δ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨CR, T₀, hCR, hT₀Base, hRawAll⟩ := hRaw δ hδ
  let q := ε / 4
  refine ⟨CR * q⁻¹ ^ 2, T₀, ?_, hT₀Base, ?_⟩
  · have hq : 0 < q := div_pos hε (by norm_num)
    positivity
  · intro σ T hσLower hσUpper hT
    have hTBase : Real.exp 2 ≤ T := le_trans hT₀Base hT
    have hTOne : 1 ≤ T := by
      have : (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      exact (this.trans_le hTBase).le
    rcases hRawAll σ T hσLower hσUpper hT with hZero | hExtract
    · exact Or.inl hZero
    · right
      rcases hExtract with ⟨W₀, j, hj, hSeparated, hInterval, hLarge, hCount⟩
      let H := T ^ δ
      let c := T - H
      let W := translateSet c W₀
      have hTNonneg : 0 ≤ T := le_trans (by norm_num) hTOne
      have hHNonneg : 0 ≤ H := Real.rpow_nonneg hTNonneg _
      have hHEps : H ≤ T ^ (ε / 4) := by
        exact Real.rpow_le_rpow_of_exponent_le hTOne hδEps
      have hHT : H ≤ T := by
        simpa [H, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hTOne hδOne
      refine ⟨W, j, H, c, hj, hHNonneg, hHEps, hHT, rfl,
        isSeparated_translate 1 c W₀ hSeparated, ?_, ?_, ?_, ?_⟩
      · intro u hu
        change u ∈ translateSet c W₀ at hu
        rw [translateSet, Finset.mem_image] at hu
        rcases hu with ⟨t, ht, rfl⟩
        have htInterval := hInterval t ht
        rw [Set.mem_Icc] at htInterval ⊢
        dsimp [c]
        constructor <;> linarith
      · intro u hu
        change u ∈ translateSet c W₀ at hu
        rw [translateSet, Finset.mem_image] at hu
        rcases hu with ⟨t, ht, rfl⟩
        rw [← detectPoly_translate]
        simpa only [sub_add_cancel] using hLarge t ht
      · intro n
        exact norm_translatedDetectorCoeffs σ T c n
      · have hLoss := rpow_mul_log_sq_le_epsilon ε δ T hε hδEps hTOne
        calc
          (typeIZeroCount σ T (2 * T) T : ℝ)
              ≤ CR * (T ^ δ * (Real.log T) ^ 2) * (W₀.card : ℝ) := by
                calc
                  (typeIZeroCount σ T (2 * T) T : ℝ)
                      ≤ CR * T ^ δ * (W₀.card : ℝ) * (Real.log T) ^ 2 := hCount
                  _ = CR * (T ^ δ * (Real.log T) ^ 2) * (W₀.card : ℝ) := by ring
          _ ≤ CR * ((ε / 4)⁻¹ ^ 2 * T ^ ε) * (W₀.card : ℝ) := by
            gcongr
          _ = (CR * q⁻¹ ^ 2) * T ^ ε * (W.card : ℝ) := by
            change CR * ((ε / 4)⁻¹ ^ 2 * T ^ ε) * (W₀.card : ℝ) =
              (CR * q⁻¹ ^ 2) * T ^ ε * ((translateSet c W₀).card : ℝ)
            rw [translateSet_card]
            dsimp [q]
            ring

end RiemannZeta.GuthMaynard
