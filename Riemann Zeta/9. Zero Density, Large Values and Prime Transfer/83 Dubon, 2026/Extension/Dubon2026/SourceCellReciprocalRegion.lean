import Dubon2026.SourceCellBoundaryGeometry
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! DUB-17/18 -> original Abel-Jacobi -> exterior cells of the actual dissection.
Reciprocal radial regions turn the exterior of the finite grid window into
bounded pole-chart regions, with exact reversed arc indexing and images.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Native inverse-order equivalences and existing radial periodicity are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
noncomputable section
open Set
open scoped Real
variable (R : RadialRegion)

theorem loop_two_pi_sub (x : ℝ) : R.loop (2 * Real.pi - x) = R.loop (-x) := by
  simpa only [show -x + 2 * Real.pi = 2 * Real.pi - x by ring] using R.loop_periodic (-x)

/- As constructed below. -/
/-- The reciprocal radial region with reversed boundary orientation. -/
noncomputable def recip : RadialRegion where
  q := 0
  r := (fun φ => (R.r (-φ))⁻¹)
  hcont := ((R.hcont.comp continuous_neg).inv₀ fun φ => (R.hpos _).ne')
  hper := by
    intro φ
    show (R.r (-(φ + 2 * Real.pi)))⁻¹ = (R.r (-φ))⁻¹
    congr 1
    have h1 : -(φ + 2 * Real.pi) = -φ - 2 * Real.pi := by ring
    rw [h1, R.hper.sub_eq]
  hpos := (fun φ => inv_pos.mpr (R.hpos _))
  N := R.N
  φs := (fun k => 2 * Real.pi - R.φs (Fin.rev k))
  hφ0 := by
    show 2 * Real.pi - R.φs (Fin.rev 0) = 0
    rw [Fin.rev_zero, R.hφN]
    ring
  hφN := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.last R.N)) = 2 * Real.pi
    rw [Fin.rev_last, R.hφ0]
    ring
  hmono := by
    intro k l hkl
    have h1 : Fin.rev l < Fin.rev k := by
      rw [Fin.lt_def, Fin.val_rev, Fin.val_rev]
      rw [Fin.lt_def] at hkl
      omega
    have h2 := R.hmono h1
    show 2 * Real.pi - R.φs (Fin.rev k) < 2 * Real.pi - R.φs (Fin.rev l)
    linarith
  hC2 := by
    intro k'
    have hicc : Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc))
        (2 * Real.pi - R.φs (Fin.rev k'.succ))
        = Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc)) := by
      rw [Fin.rev_castSucc, Fin.rev_succ]
    show ContDiffOn ℝ 2 (fun φ => (R.r (-φ))⁻¹)
      (Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc)) (2 * Real.pi - R.φs (Fin.rev k'.succ)))
    rw [hicc]
    have hmaps : Set.MapsTo (fun φ => 2 * Real.pi - φ)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc)))
        (Set.Icc (R.φs ((Fin.rev k').castSucc)) (R.φs ((Fin.rev k').succ))) := by
      intro φ hφ
      obtain ⟨h1, h2⟩ := hφ
      exact ⟨by linarith, by linarith⟩
    have h1 : ContDiffOn ℝ 2 (fun φ => R.r (2 * Real.pi - φ))
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      (R.hC2 (Fin.rev k')).comp ((contDiff_const.sub contDiff_id).contDiffOn) hmaps
    have h2 : ContDiffOn ℝ 2 (fun φ => (R.r (2 * Real.pi - φ))⁻¹)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      h1.inv fun φ _ => (R.hpos _).ne'
    refine h2.congr ?_
    intro φ _
    show (R.r (-φ))⁻¹ = (R.r (2 * Real.pi - φ))⁻¹
    congr 1
    have h3 : -φ = (2 * Real.pi - φ) - 2 * Real.pi := by ring
    rw [h3, R.hper.sub_eq]

theorem recip_q : (recip R).q = 0 := rfl

theorem recip_N : (recip R).N = R.N := rfl

/- As constructed below. -/
/-- The unchanged finite index type after taking a reciprocal region. -/
def idx (k : Fin R.N) : Fin (recip R).N := k

/- As constructed below. -/
/-- The reverse type conversion for a reciprocal region arc index. -/
def unidx (k : Fin (recip R).N) : Fin R.N := k

theorem loop_recip (hq : R.q = 0) (φ : ℝ) : ((recip R).loop φ)⁻¹ = R.loop (-φ) := by
  show ((0 : ℂ) + (((R.r (-φ))⁻¹ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))⁻¹ =
    R.q + (R.r (-φ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I)
  rw [hq]
  simp only [zero_add, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul, Complex.exp_neg, mul_inv,
    inv_inv]

theorem loop_recip_eq (hq : R.q = 0) (θ : ℝ) :
    (recip R).loop θ = (R.loop (2 * Real.pi - θ))⁻¹ := by
  rw [loop_two_pi_sub R θ, ← loop_recip R hq θ, inv_inv]

theorem zero_mem_Kint : (0 : ℂ) ∈ (recip R).Kint := by
  show ‖(0 : ℂ) - 0‖ < (R.r (-Complex.arg ((0 : ℂ) - 0)))⁻¹
  rw [sub_zero, norm_zero]
  exact inv_pos.mpr (R.hpos _)


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
