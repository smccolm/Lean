import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PrimeNumberTheoremAnd.SmoothExistence
import RiemannZeta.GuthMaynard.DFISourceCutoffs

open Set
open scoped ContDiff Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The smooth height cutoff in Hughes--Young

The sharp interval used by Maynard--Pratt is first dominated by a fixed
smooth cutoff after dilation.  This file constructs that cutoff and records
the scale-uniform derivative estimates used by the integrations by parts in
Hughes--Young Section 3.
-/

/-- A fixed source cutoff which is one on `[1/2,3]` and vanishes outside
`[1/4,4]`. -/
structure HughesYoungCutoff where
  /-- The `toFun` component of `HughesYoungCutoff`. -/
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  bounded : ∀ x, toFun x ≤ 1
  support : Function.support toFun ⊆ Set.Icc (1 / 4 : ℝ) 4
  equals_one : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 3, toFun x = 1

instance : CoeFun HughesYoungCutoff (fun _ => ℝ → ℝ) :=
  ⟨HughesYoungCutoff.toFun⟩

/-- Smooth Urysohn supplies the fixed height cutoff required by the source. -/
theorem exists_hughesYoungCutoff : Nonempty HughesYoungCutoff := by
  obtain ⟨w, hwSmooth, _hwCompact, hwLower, hwUpper, hwSupport⟩ :=
    smooth_urysohn_support_Ioo (a := (1 / 4 : ℝ)) (b := 1 / 2)
      (c := 3) (d := 4) (by norm_num) (by norm_num)
  refine ⟨{
    toFun := w
    smooth := hwSmooth
    nonneg := ?_
    bounded := ?_
    support := ?_
    equals_one := ?_ }⟩
  · intro x
    have hzero : 0 ≤ Set.indicator (Set.Icc (1 / 2 : ℝ) 3)
        (1 : ℝ → ℝ) x := by
      rw [Set.indicator]
      split <;> simp
    exact hzero.trans (hwLower x)
  · intro x
    exact (hwUpper x).trans (by
      rw [Set.indicator]
      split <;> norm_num)
  · rw [hwSupport]
    exact Set.Ioo_subset_Icc_self
  · intro x hx
    have hxOpen : x ∈ Set.Ioo (1 / 4 : ℝ) 4 := by
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hLower := hwLower x
    have hUpper := hwUpper x
    rw [Set.indicator_of_mem hx] at hLower
    rw [Set.indicator_of_mem hxOpen] at hUpper
    exact le_antisymm hUpper hLower

/-- One canonical cutoff, fixed once and for all before the height varies. -/
noncomputable def hughesYoungCutoff : HughesYoungCutoff :=
  Classical.choice exists_hughesYoungCutoff

/-- Dilation of the fixed cutoff to height `T`. -/
noncomputable def hughesYoungHeightWeight (T t : ℝ) : ℝ :=
  hughesYoungCutoff (T⁻¹ * t)

theorem hughesYoungHeightWeight_nonneg (T t : ℝ) :
    0 ≤ hughesYoungHeightWeight T t :=
  hughesYoungCutoff.nonneg _

theorem hughesYoungHeightWeight_le_one (T t : ℝ) :
    hughesYoungHeightWeight T t ≤ 1 :=
  hughesYoungCutoff.bounded _

/-- The smooth weight exactly majorizes the Maynard--Pratt interval. -/
theorem hughesYoungHeightWeight_eq_one {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Set.Icc (T / 2) (3 * T)) :
    hughesYoungHeightWeight T t = 1 := by
  apply hughesYoungCutoff.equals_one
  rw [Set.mem_Icc] at ht ⊢
  constructor
  · rw [inv_mul_eq_div]
    exact (le_div_iff₀ hT).2 (by nlinarith [ht.1])
  · rw [inv_mul_eq_div]
    exact (div_le_iff₀ hT).2 ht.2

/-- The dilated cutoff is supported inside `[T/4,4T]`. -/
theorem hughesYoungHeightWeight_support {T t : ℝ} (hT : 0 < T)
    (ht : hughesYoungHeightWeight T t ≠ 0) :
    t ∈ Set.Icc (T / 4) (4 * T) := by
  have hs := hughesYoungCutoff.support ht
  rw [Set.mem_Icc] at hs ⊢
  rw [inv_mul_eq_div] at hs
  constructor
  · exact (by nlinarith [(le_div_iff₀ hT).1 hs.1])
  · exact (div_le_iff₀ hT).1 hs.2

theorem contDiff_hughesYoungHeightWeight (T : ℝ) :
    ContDiff ℝ ∞ (hughesYoungHeightWeight T) := by
  exact hughesYoungCutoff.smooth.comp (contDiff_const.mul contDiff_id)

/-- Constants for all derivatives of the fixed cutoff are selected before
the height is introduced. -/
theorem exists_hughesYoungCutoff_derivativeProfile :
    ∃ C : ℕ → ℝ, ∀ k : ℕ, 0 < C k ∧
      ∀ x : ℝ, ‖iteratedDeriv k hughesYoungCutoff x‖ ≤ C k := by
  have hcompact : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      hughesYoungCutoff.support
  choose C hC hBound using fun k =>
    exists_scaled_iteratedDeriv_bound hughesYoungCutoff.smooth hcompact
      (A := (1 : ℝ)) zero_lt_one k
  refine ⟨C, fun k => ⟨hC k, fun x => ?_⟩⟩
  simpa using hBound k x

/-- The `k`-th derivative of the physical cutoff costs exactly `T⁻ᵏ`, with
a constant independent of `T`. -/
theorem exists_uniform_hughesYoungHeightWeight_derivativeProfile :
    ∃ C : ℕ → ℝ, ∀ k : ℕ, 0 < C k ∧ ∀ (T : ℝ), 0 < T → ∀ t : ℝ,
      ‖iteratedDeriv k (hughesYoungHeightWeight T) t‖ ≤ C k * T⁻¹ ^ k := by
  obtain ⟨C, hC⟩ := exists_hughesYoungCutoff_derivativeProfile
  refine ⟨C, fun k => ⟨(hC k).1, fun T hT t => ?_⟩⟩
  have hkSmooth : ContDiff ℝ k (hughesYoungCutoff : ℝ → ℝ) :=
    hughesYoungCutoff.smooth.of_le (by exact_mod_cast le_top)
  have hFormula := congrFun
    (iteratedDeriv_comp_const_mul
      hkSmooth T⁻¹) t
  change ‖iteratedDeriv k (fun x : ℝ => hughesYoungCutoff (T⁻¹ * x)) t‖ ≤ _
  rw [hFormula, norm_mul, Real.norm_eq_abs, abs_pow,
    abs_inv, abs_of_pos hT]
  calc
    T⁻¹ ^ k * ‖iteratedDeriv k hughesYoungCutoff (T⁻¹ * t)‖ ≤
        T⁻¹ ^ k * C k := by
      exact mul_le_mul_of_nonneg_left ((hC k).2 _) (by positivity)
    _ = C k * T⁻¹ ^ k := by ring

end RiemannZeta.GuthMaynard
