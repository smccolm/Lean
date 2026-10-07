import Dubon2026.WeightedLogResidue
import Dubon2026.RectangleZeroCount

/-! # The rectangle argument principle with analytic weights and actual zero multiplicities -/

namespace Dubon2026

open Complex Set
open scoped BigOperators

noncomputable section

theorem sumResiduesIn_eq_finite_sum {f : ℂ → ℂ} {S : Set ℂ} (hS : S.Finite) :
    sumResiduesIn f S = ∑ s ∈ hS.toFinset, residue f s := by
  let Sfin := hS.toFinset
  change sumResiduesIn f S = ∑ s ∈ Sfin, residue f s
  rw [sumResiduesIn, show S = (Sfin : Set ℂ) from hS.coe_toFinset.symm,
    tsum_fintype, ← Finset.sum_coe_sort Sfin]
  rfl

theorem rectangleIntegral_weighted_logDeriv_eq_zero_sum {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Rectangle (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ))) :
    RectangleIntegral' (fun s => g s * logDeriv (dirichletSum a N) s)
        (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u T, g s * (zeroMultiplicity a N s : ℂ) := by
  let R := Rectangle (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ)
  let F := fun s => g s * logDeriv (dirichletSum a N) s
  let Z := zerosInOpenRectangleFinset a N hN ha l u T
  have hZR {s : ℂ} (hs : s ∈ Z) : s ∈ R := by
    have hz := (finite_zerosInOpenRectangle hN ha l u T).mem_toFinset.mp hs
    rw [mem_Rect hlu (neg_le_self hT)]
    exact ⟨hz.1.le, hz.2.1.le, (abs_lt.mp hz.2.2.1).1.le, (abs_lt.mp hz.2.2.1).2.le⟩
  have hF : MeromorphicOn F R := by
    intro s hs
    exact (hg s hs).meromorphicAt.mul
      ((analyticAt_dirichletSum a N s).deriv.meromorphicAt.div
        (analyticAt_dirichletSum a N s).meromorphicAt)
  have hsubset : R ∩ {s | meromorphicOrderAt F s < 0} ⊆ (Z : Set ℂ) := by
    rintro s ⟨hsR, hsneg⟩
    have hz : dirichletSum a N s = 0 := by
      by_contra hn
      exact not_lt_of_ge (analyticAt_weighted_dirichlet_logDeriv
        (hg s hsR) hn).meromorphicOrderAt_nonneg hsneg
    have hbn : s ∉ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) := fun h => hb s h hz
    have hc := rectangle_interior_coordinates hlu (neg_le_self hT) hsR hbn
    exact (finite_zerosInOpenRectangle hN ha l u T).mem_toFinset.mpr
      ⟨hc.1, hc.2.1, abs_lt.mpr hc.2.2, hz⟩
  have hfinite : (R ∩ {s | meromorphicOrderAt F s < 0}).Finite := Z.finite_toSet.subset hsubset
  have hborder : Disjoint (RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ))
      {s | meromorphicOrderAt F s < 0} := by
    rw [Set.disjoint_left]
    intro s hs hn
    have hsR := rectangleBorder_subset_rectangle (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) hs
    exact not_lt_of_ge (analyticAt_weighted_dirichlet_logDeriv
      (hg s hsR) (hb s hs)).meromorphicOrderAt_nonneg hn
  have hsimple : HasSimplePolesOn F R := fun s hs =>
    weighted_dirichlet_logDeriv_simple hN ha (hg s hs)
  rw [RectangleIntegral'_eq_sumResiduesIn hlu (neg_le_self hT) hF hborder hfinite hsimple,
    sumResiduesIn_eq_finite_sum hfinite]
  calc
    ∑ s ∈ hfinite.toFinset, residue F s = ∑ s ∈ Z, residue F s := by
      apply Finset.sum_subset
      · intro s hs
        exact hsubset (hfinite.mem_toFinset.mp hs)
      · intro s hs hn
        have hnp : 0 ≤ meromorphicOrderAt F s := by
          by_contra hp
          exact hn (hfinite.mem_toFinset.mpr ⟨hZR hs, lt_of_not_ge hp⟩)
        exact residue_eq_zero_of_not_pole_of_meromorphicAt (hF s (hZR hs)) hnp
    _ = ∑ s ∈ Z, g s * (zeroMultiplicity a N s : ℂ) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact residue_weighted_dirichlet_logDeriv hN ha (hg s (hZR hs))

theorem rectangleIntegral_power_logDeriv_eq_zero_power_sum {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0)
    (k : ℕ) :
    RectangleIntegral' (fun s => s ^ k * logDeriv (dirichletSum a N) s)
        (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u T,
        s ^ k * (zeroMultiplicity a N s : ℂ) :=
  rectangleIntegral_weighted_logDeriv_eq_zero_sum hN ha hlu hT hb
    (fun _ _ => analyticAt_id.pow k)

end

end Dubon2026
