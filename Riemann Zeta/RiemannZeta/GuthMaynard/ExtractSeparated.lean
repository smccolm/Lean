import Mathlib.Data.Finset.Max
import RiemannZeta.GuthMaynard.Pigeonhole
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

/--
Local multiplicity input after a displacement of at most `T^δ`. It records only
unit-bin occupancy; the final Type I count and separated set do not occur in it.
-/
def LocalZeroMultiplicityBoundProp : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      ∀ shift : ℂ → ℝ,
        (∀ ρ ∈ typeIZeroSet σ T, |ρ.im - shift ρ| ≤ T ^ δ) →
        ∃ L : ℕ, (L : ℝ) ≤ C * T ^ δ * Real.log T ∧
          ∀ j ∈ admissibleDyadicIndices T, ∀ z : ℤ,
            ∑ t ∈ (assignedTypeIZeroSet σ T j).image shift |>.filter
              (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
              shiftedMultiplicity (assignedTypeIZeroSet σ T j) shift t ≤ L

/-- Membership in the enlarged interval forced by beta removal. -/
def InShiftedTargetInterval (T H : ℝ) (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, t ∈ Set.Icc (T - H) (2 * T + H)

/--
Corrected F-05 target. Constants are uniform in `T`, the statement is eventual,
and beta-shifted ordinates lie in the enlarged interval actually justified by
the source argument. The zero-count-zero branch handles an empty scale range.
-/
def ExtractSeparatedTarget : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C T₀ : ℝ, 0 < C ∧ Real.exp 2 ≤ T₀ ∧
    ∀ (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 → T₀ ≤ T →
      typeIZeroCount σ T (2 * T) T = 0 ∨
        ∃ (W : Finset ℝ) (j : ℕ),
          j ∈ admissibleDyadicIndices T ∧
          IsSeparated 1 W ∧
          InShiftedTargetInterval T (T ^ (ε / 4)) W ∧
          (∀ γ' ∈ W,
            1 / (4 * Real.log T) ≤ ‖detectPoly (2 ^ j) (σ + I * γ') T‖) ∧
          (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            C * T ^ ε * (W.card : ℝ) * (Real.log T) ^ 2

/--
F-05 follows from the explicit beta-shift and local-multiplicity inputs. The
proof uses `finite_weighted_extract_separated`; neither input contains the final
zero-count bound or a separated-set conclusion.
-/
theorem extractSeparated_of_beta_shift_and_local_multiplicity
    (hBeta : DetectorBetaShiftProp) (hLocal : LocalZeroMultiplicityBoundProp) :
    ExtractSeparatedTarget := by
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨Tβ, hTβBase, hBetaAll⟩ := hBeta δ hδ
  obtain ⟨CL, TL, hCL, hTLBase, hLocalAll⟩ := hLocal δ hδ
  let K : ℝ := (5 / 2 : ℝ) / Real.log 2 + 1 / 2
  refine ⟨2 * K * CL, max Tβ TL, ?_, ?_, ?_⟩
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
      obtain ⟨L, hLSize, hBins⟩ :=
        hLocalAll σ T hσLower hσUpper hTL shift hShift
      have hScale : ∀ ρ ∈ S, chosenTypeIScale ρ T ∈ admissibleDyadicIndices T := by
        intro ρ hρ
        exact chosenTypeIScale_mem ρ T (Finset.mem_filter.mp hρ).2
      have hLocalGeneric : ∀ j ∈ admissibleDyadicIndices T, ∀ z : ℤ,
          ∑ t ∈ (S.filter (fun ρ => chosenTypeIScale ρ T = j)).image shift |>.filter
            (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
            ∑ ρ ∈ (S.filter (fun y => chosenTypeIScale y T = j)).filter
              (fun y => shift y = t), analyticVanishingOrder riemannZeta ρ ≤ L := by
        intro j hj z
        exact hBins j hj z
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
        have hTOne : 1 ≤ T := by
          have : (1 : ℝ) < Real.exp 2 := by
            rw [← Real.exp_zero]
            exact Real.exp_lt_exp.mpr (by norm_num)
          exact (this.trans_le hTBase).le
        have hPow : T ^ δ ≤ T ^ ε := by
          apply Real.rpow_le_rpow_of_exponent_le hTOne
          dsimp [δ]
          linarith
        have hCountReal : (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            2 * ((admissibleDyadicIndices T).card : ℝ) * (L : ℝ) * (W.card : ℝ) := by
          exact_mod_cast hCount
        have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
        calc
          (typeIZeroCount σ T (2 * T) T : ℝ)
              ≤ 2 * ((admissibleDyadicIndices T).card : ℝ) * (L : ℝ) * (W.card : ℝ) :=
            hCountReal
          _ ≤ 2 * (K * Real.log T) * (CL * T ^ δ * Real.log T) * (W.card : ℝ) := by
            gcongr
          _ ≤ 2 * (K * Real.log T) * (CL * T ^ ε * Real.log T) * (W.card : ℝ) := by
            gcongr
          _ = (2 * K * CL) * T ^ ε * (W.card : ℝ) * (Real.log T) ^ 2 := by ring

end RiemannZeta.GuthMaynard
