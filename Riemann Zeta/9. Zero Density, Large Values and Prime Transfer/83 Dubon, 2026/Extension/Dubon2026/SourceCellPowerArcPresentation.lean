import Dubon2026.SourceCellArcAffineEndpoints

/-! DUB-17/18 -> original Abel-Jacobi -> C1 reversal of branch-cell arcs.
The existing exact power-lap geometry supplies a positive affine parameter
on every arc, with exact endpoints, boundary evaluation and full side image.
Native periodicity removes the complete-turn offset.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open Set
open scoped Real

theorem PowerGeometry.arc_presentation {R R' : RadialRegion} {e : ℕ}
    (hgeom : PowerGeometry R e R') (a : Fin R'.N) :
    ∃ (k : Fin R.N) (m c : ℝ), 0 < m ∧
      m * R'.φs a.castSucc + c = R.φs k.castSucc ∧
      m * R'.φs a.succ + c = R.φs k.succ ∧
      (∀ t : ℝ, R.q + R'.loop t ^ e = R.loop (m * t + c)) ∧
      (fun u : ℂ => R.q + u ^ e) '' R'.arcSet a = R.arcSet k := by
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero hgeom.exponent_ne_zero
  obtain ⟨_, _, _, _, hloop, lap, hbij, harc, himg, _, _⟩ := hgeom
  obtain ⟨⟨j, k⟩, ha⟩ := hbij.2 a
  change lap j k = a at ha
  subst a
  have hIcc : Icc (R'.φs (lap j k).castSucc) (R'.φs (lap j k).succ) =
      (fun t : ℝ => (1 / (e : ℝ)) * t + 2 * π * (j : ℕ) / (e : ℝ)) ''
        Icc (R.φs k.castSucc) (R.φs k.succ) := by
    rw [← RadialRegion.arcIcc, harc j k]
    congr 1
    funext t
    field_simp
    ring
  obtain ⟨hstart, hstop⟩ := ArcAffine.endpoints_of_image_mono (by positivity)
    (R.hmono Fin.castSucc_lt_succ).le hIcc
  refine ⟨k, e, -(2 * π * (j : ℕ)), he, ?_, ?_, ?_, himg j k⟩
  · rw [hstart]
    field_simp
    ring
  · rw [hstop]
    field_simp
    ring
  · intro t
    rw [hloop]
    have harg : (e : ℝ) * t = ((e : ℝ) * t + -(2 * π * (j : ℕ))) +
        ((j : ℕ) : ℤ) * (2 * π) := by push_cast; ring
    conv_lhs => rw [harg]
    exact R.loop_periodic.int_mul ((j : ℕ) : ℤ) _

end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
