import Mathlib

/-! DUB-17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
construct a meromorphic function with the prescribed divisor. The local
integer-residue expansion gives finite polar products on an exhaustion
by disks; analytic primitives of the regular part are exponentiated and
normalized to agree on overlaps. Local residue expansions remain an
explicit upstream analytic obligation, not a function-existence premise.
Adapted from anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean,
Apache-2.0; retained LICENSE and NOTICE. -/

namespace Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive
open scoped Topology
open Filter Set Metric

section Products

variable (T : Finset ℂ) (n : ℂ → ℤ)

/-- Finite product of actual integer-order zero and pole factors. -/
noncomputable def zprod (z : ℂ) : ℂ := ∏ s ∈ T, (z - s) ^ (n s)

/-- Finite sum of the actual integer simple-pole terms. -/
noncomputable def polarPart (z : ℂ) : ℂ := ∑ s ∈ T, (n s : ℂ) / (z - s)

theorem zprod_ne_zero {z : ℂ} (hz : z ∉ T) : zprod T n z ≠ 0 := by
  unfold zprod
  refine Finset.prod_ne_zero_iff.mpr fun s hs => zpow_ne_zero _ (sub_ne_zero.mpr ?_)
  rintro rfl; exact hz hs

theorem zprod_eq_zero {z : ℂ} (hz : z ∈ T) (hn : n z ≠ 0) : zprod T n z = 0 := by
  unfold zprod
  exact Finset.prod_eq_zero hz (by rw [sub_self, zero_zpow _ hn])

theorem analyticAt_zprod {z : ℂ} (hz : z ∉ T) : AnalyticAt ℂ (zprod T n) z := by
  have : zprod T n = fun w => ∏ s ∈ T, (w - s) ^ (n s) := rfl
  rw [this]
  refine Finset.analyticAt_fun_prod T fun s hs => ?_
  refine ((analyticAt_id).sub analyticAt_const).zpow ?_
  exact sub_ne_zero.mpr (by rintro rfl; exact hz hs)

theorem analyticAt_polarPart {z : ℂ} (hz : z ∉ T) : AnalyticAt ℂ (polarPart T n) z := by
  have : polarPart T n = fun w => ∑ s ∈ T, (n s : ℂ) / (w - s) := rfl
  rw [this]
  refine Finset.analyticAt_fun_sum T fun s hs => ?_
  refine analyticAt_const.div ((analyticAt_id).sub analyticAt_const) ?_
  exact sub_ne_zero.mpr (by rintro rfl; exact hz hs)

theorem hasDerivAt_zprod {z : ℂ} (hz : z ∉ T) :
    HasDerivAt (zprod T n) (zprod T n z * polarPart T n z) z := by
  classical
  unfold zprod polarPart
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | @insert a T haT ih =>
    have hza : z ≠ a := by rintro rfl; exact hz (Finset.mem_insert_self _ _)
    have hzT : z ∉ T := fun h => hz (Finset.mem_insert_of_mem h)
    have hza' : (z - a) ≠ 0 := sub_ne_zero.mpr hza
    have ih' := ih hzT
    have hfa : HasDerivAt (fun w : ℂ => (w - a) ^ (n a))
        ((n a : ℂ) * (z - a) ^ (n a - 1)) z := by
      have := (hasDerivAt_zpow (n a) (z - a) (Or.inl hza')).comp z
        ((hasDerivAt_id z).sub_const a)
      simp at this
      exact this
    have hprod := hfa.mul ih'
    have heq : (fun w : ℂ => ∏ s ∈ insert a T, (w - s) ^ n s) =
        fun w : ℂ => (w - a) ^ n a * ∏ s ∈ T, (w - s) ^ n s := by
      funext w; rw [Finset.prod_insert haT]
    rw [heq]
    refine hprod.congr_deriv (Eq.symm ?_)
    rw [Finset.prod_insert haT, Finset.sum_insert haT, zpow_sub_one₀ hza']
    field_simp

variable {T n}

theorem meromorphicOrderAt_zprod [DecidableEq ℂ] (z : ℂ) :
    meromorphicOrderAt (zprod T n) z = ((if z ∈ T then n z else 0 : ℤ) : WithTop ℤ) := by
  have hzp : zprod T n = ∏ s ∈ T, fun w : ℂ => (w - s) ^ (n s) := by
    funext w; simp [zprod, Finset.prod_apply]
  rw [hzp, meromorphicOrderAt_prod (fun s _ => by fun_prop)]
  have hterm : ∀ s ∈ T, meromorphicOrderAt (fun w : ℂ => (w - s) ^ (n s)) z =
      ((if z = s then n s else 0 : ℤ) : WithTop ℤ) := by
    intro s _
    by_cases hzs : z = s
    · subst hzs
      rw [if_pos rfl]
      exact fun_meromorphicOrderAt_zpow_id_sub_const
    · rw [if_neg hzs]
      have han : AnalyticAt ℂ (fun w : ℂ => (w - s) ^ (n s)) z :=
        ((analyticAt_id).sub analyticAt_const).zpow (sub_ne_zero.mpr hzs)
      rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero.mpr
        (zpow_ne_zero _ (sub_ne_zero.mpr hzs)))]
      rfl
  rw [Finset.sum_congr rfl hterm, ← WithTop.coe_sum]
  congr 1
  rw [Finset.sum_ite_eq]

end Products

end Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive
