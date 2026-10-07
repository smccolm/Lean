import Dubon2026.LatticeCuspResidue

/-! # The actual integrated lattice functional equation and removal of its two poles -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The true rectangular lattice-cusp integral inherits the literal self-dual lattice functional equation. -/
theorem rectangularLatticeCuspCompleted_functional_equation {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    rectangularLatticeCuspCompleted f a b ha hb (1 - s) = rectangularLatticeCuspCompleted f a b ha hb s := by
  simp only [rectangularLatticeCuspCompleted, latticeCompletedMellin_functional_equation]

/-- The actual entire lattice regular part obeys the same reflection symmetry. -/
theorem latticeCompletedMellinRegular_functional_equation (z : ℍ) (s : ℂ) :
    latticeCompletedMellinRegular z (1 - s) = latticeCompletedMellinRegular z s := by
  rw [latticeCompletedMellinRegular_eq_tails, latticeCompletedMellinRegular_eq_tails,
    sub_sub_cancel, add_comm]

/-- The true regularized rectangular cusp integral is symmetric under s↦1−s. -/
theorem rectangularLatticeCuspRegular_functional_equation {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    rectangularLatticeCuspRegular f a b ha hb (1 - s) = rectangularLatticeCuspRegular f a b ha hb s := by
  simp only [rectangularLatticeCuspRegular, latticeCompletedMellinRegular_functional_equation]

/-- The entire completion obtained by cancelling the two actual lattice-cusp poles. -/
def rectangularLatticeCuspEntire {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) : ℂ :=
  s * (s - 1) * rectangularLatticeCuspRegular f a b ha hb s + cuspPetersson f f / 2

/-- The constructed pole-cleared actual lattice-cusp function is entire. -/
theorem differentiable_rectangularLatticeCuspEntire {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Differentiable ℂ (rectangularLatticeCuspEntire f a b ha hb) := by
  have hR := differentiable_rectangularLatticeCuspRegular f a b ha hb
  unfold rectangularLatticeCuspEntire
  fun_prop

/-- Away from the two poles the entire function is the literal product s(s−1) times the actual completed cusp integral. -/
theorem rectangularLatticeCuspEntire_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rectangularLatticeCuspEntire f a b ha hb s = s * (s - 1) * rectangularLatticeCuspCompleted f a b ha hb s := by
  rw [rectangularLatticeCuspEntire, rectangularLatticeCuspCompleted,
    rectangular_lattice_cusp_integral_eq_regular]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- The genuine entire completion has the exact self-dual reflection symmetry. -/
theorem rectangularLatticeCuspEntire_functional_equation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    rectangularLatticeCuspEntire f a b ha hb (1 - s) = rectangularLatticeCuspEntire f a b ha hb s := by
  simp only [rectangularLatticeCuspEntire, rectangularLatticeCuspRegular_functional_equation]
  ring

end
end Dubon2026
