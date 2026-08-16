import RiemannZeta.GuthMaynard.HughesYoungDFIWeight

open Complex Finset
open scoped BigOperators ContDiff Topology
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Coprime reduction for the Hughes--Young off-diagonal

The DFI quadratic-divisor theorem is stated for coprime coefficients, while
the two mollifier indices in the Hughes--Young expansion are arbitrary.  This
file performs the exact gcd reduction.  No term is estimated or discarded:
after writing `h = d * a` and `k = d * b`, the original shift is exactly `d`
times the reduced shift and the physical source weight is dilated by `d`.
-/

/-- The common divisor removed from the two Hughes--Young mollifier indices. -/
def hughesYoungCommonDivisor (h k : ℕ) : ℕ := Nat.gcd h k

/-- The left coprime coefficient after gcd reduction. -/
def hughesYoungReducedLeft (h k : ℕ) : ℕ :=
  h / hughesYoungCommonDivisor h k

/-- The right coprime coefficient after gcd reduction. -/
def hughesYoungReducedRight (h k : ℕ) : ℕ :=
  k / hughesYoungCommonDivisor h k

theorem hughesYoungCommonDivisor_pos {h k : ℕ} (hh : 0 < h) :
    0 < hughesYoungCommonDivisor h k := by
  exact Nat.gcd_pos_of_pos_left k hh

theorem hughesYoungCommonDivisor_mul_reducedLeft (h k : ℕ) :
    hughesYoungCommonDivisor h k * hughesYoungReducedLeft h k = h := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left h k)

theorem hughesYoungCommonDivisor_mul_reducedRight (h k : ℕ) :
    hughesYoungCommonDivisor h k * hughesYoungReducedRight h k = k := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right h k)

theorem hughesYoungReducedLeft_pos {h k : ℕ} (hh : 0 < h) :
    0 < hughesYoungReducedLeft h k := by
  rw [hughesYoungReducedLeft]
  exact Nat.div_pos (Nat.gcd_le_left k hh) (hughesYoungCommonDivisor_pos hh)

theorem hughesYoungReducedRight_pos {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < hughesYoungReducedRight h k := by
  rw [hughesYoungReducedRight]
  exact Nat.div_pos (Nat.gcd_le_right h hk) (hughesYoungCommonDivisor_pos hh)

/-- The reduced coefficients are genuinely coprime, as required by DFI. -/
theorem hughesYoungReduced_coprime {h k : ℕ} (hh : 0 < h) :
    (hughesYoungReducedLeft h k).Coprime
      (hughesYoungReducedRight h k) := by
  exact Nat.coprime_div_gcd_div_gcd (hughesYoungCommonDivisor_pos hh)

/-- Exact factorization of every Hughes--Young determinant shift by the gcd. -/
theorem quadraticDivisorShift_eq_commonDivisor_mul_reduced
    (h k m n : ℕ) :
    quadraticDivisorShift h k m n =
      (hughesYoungCommonDivisor h k : ℤ) *
        quadraticDivisorShift
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) m n := by
  have hleft := hughesYoungCommonDivisor_mul_reducedLeft h k
  have hright := hughesYoungCommonDivisor_mul_reducedRight h k
  have hleftZ :
      (hughesYoungCommonDivisor h k : ℤ) *
          (hughesYoungReducedLeft h k : ℤ) = (h : ℤ) := by
    exact_mod_cast hleft
  have hrightZ :
      (hughesYoungCommonDivisor h k : ℤ) *
          (hughesYoungReducedRight h k : ℤ) = (k : ℤ) := by
    exact_mod_cast hright
  unfold quadraticDivisorShift
  push_cast
  calc
    (h : ℤ) * m - (k : ℤ) * n =
        ((hughesYoungCommonDivisor h k : ℕ) : ℤ) *
          ((hughesYoungReducedLeft h k : ℕ) : ℤ) * m -
        ((hughesYoungCommonDivisor h k : ℕ) : ℤ) *
          ((hughesYoungReducedRight h k : ℕ) : ℤ) * n := by
      rw [hleftZ, hrightZ]
    _ = (hughesYoungCommonDivisor h k : ℤ) *
          ((hughesYoungReducedLeft h k : ℤ) * m -
            (hughesYoungReducedRight h k : ℤ) * n) := by ring

theorem quadraticDivisorShift_eq_zero_iff_reduced
    {h k m n : ℕ} (hh : 0 < h) :
    quadraticDivisorShift h k m n = 0 ↔
      quadraticDivisorShift
        (hughesYoungReducedLeft h k)
        (hughesYoungReducedRight h k) m n = 0 := by
  rw [quadraticDivisorShift_eq_commonDivisor_mul_reduced]
  have hd : (hughesYoungCommonDivisor h k : ℤ) ≠ 0 := by
    exact_mod_cast (hughesYoungCommonDivisor_pos hh).ne'
  exact mul_eq_zero.trans (or_iff_right hd)

/-- Dilation of a natural-valued source weight by the removed gcd. -/
noncomputable def hughesYoungGCDScaledNatWeight
    (h k : ℕ) (f : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  f (hughesYoungCommonDivisor h k * x)
    (hughesYoungCommonDivisor h k * y)

/-- Exact off-diagonal gcd reduction before any shift partition or estimate. -/
theorem finiteQuadraticDivisorOffDiagonal_eq_gcdReduced
    {h k M N : ℕ} (hh : 0 < h) (f : ℕ → ℕ → ℂ) :
    finiteQuadraticDivisorOffDiagonal h k M N f =
      finiteQuadraticDivisorOffDiagonal
        (hughesYoungReducedLeft h k)
        (hughesYoungReducedRight h k) M N
        (hughesYoungGCDScaledNatWeight h k f) := by
  unfold finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  have hz := quadraticDivisorShift_eq_zero_iff_reduced
    (h := h) (k := k) (m := m) (n := n) hh
  have hleft := hughesYoungCommonDivisor_mul_reducedLeft h k
  have hright := hughesYoungCommonDivisor_mul_reducedRight h k
  have hleftMul : hughesYoungCommonDivisor h k *
      (hughesYoungReducedLeft h k * m) = h * m := by
    rw [← Nat.mul_assoc, hleft]
  have hrightMul : hughesYoungCommonDivisor h k *
      (hughesYoungReducedRight h k * n) = k * n := by
    rw [← Nat.mul_assoc, hright]
  by_cases hzero : quadraticDivisorShift h k m n = 0
  · have hzero' := hz.mp hzero
    simp [hzero, hzero']
  · have hzero' : quadraticDivisorShift
        (hughesYoungReducedLeft h k)
        (hughesYoungReducedRight h k) m n ≠ 0 := by
      exact mt hz.mpr hzero
    simp only [hzero, hzero', if_false]
    unfold hughesYoungGCDScaledNatWeight
    rw [hleftMul, hrightMul]

/-- Dilation of a real-physical DFI weight by the removed gcd. -/
noncomputable def hughesYoungGCDScaledWeight
    (h k : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  F ((hughesYoungCommonDivisor h k : ℝ) * x)
    ((hughesYoungCommonDivisor h k : ℝ) * y)

theorem hughesYoungGCDScaledNatWeight_ofReal
    (h k : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℕ) :
    hughesYoungGCDScaledNatWeight h k
        (fun u v => F (u : ℝ) (v : ℝ)) x y =
      hughesYoungGCDScaledWeight h k F (x : ℝ) (y : ℝ) := by
  unfold hughesYoungGCDScaledNatWeight hughesYoungGCDScaledWeight
  push_cast
  rfl

/-- Exact source-facing reduction: the arbitrary-index Hughes--Young
off-diagonal is a shift sum for the coprime DFI coefficients. -/
theorem finiteQuadraticDivisorOffDiagonal_eq_sum_gcdReduced_dfiShifts
    {h k M N : ℕ} (hh : 0 < h) (F : ℝ → ℝ → ℂ) :
    finiteQuadraticDivisorOffDiagonal h k M N
        (fun x y => F (x : ℝ) (y : ℝ)) =
      ∑ r ∈ Finset.Icc
          (-(hughesYoungReducedRight h k * N : ℤ))
          (hughesYoungReducedLeft h k * M : ℤ),
        if r = 0 then 0 else
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDScaledWeight h k F)
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) M N r := by
  rw [finiteQuadraticDivisorOffDiagonal_eq_gcdReduced hh]
  rw [finiteQuadraticDivisorOffDiagonal_eq_sum_shifts]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr : r = 0
  · simp [hr]
  · simp only [hr, if_false]
    rw [← finiteQuadraticDivisorSum_ofReal_eq_dfiDyadic]
    unfold finiteQuadraticDivisorSum
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    rw [hughesYoungGCDScaledNatWeight_ofReal]

/-! ## The actual localized weight after coprime reduction -/

/-- The literal Hughes--Young Mellin summand written in the coprime DFI
coordinates.  Its scalar still contains the original mollifier indices
`h,k`; only the two physical variables and their logarithmic powers use the
reduced coefficients. -/
noncomputable def hughesYoungReducedLocalizedMellinWeight
    (T t c u X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  hughesYoungMellinScalar T t c u h k *
    hughesYoungLocalizedLogKernel X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      (afeCriticalPoint t + w) (afeCriticalPoint (-t) + w) x y

theorem contDiff_uncurry_hughesYoungReducedLocalizedMellinWeight
    (T t c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  exact contDiff_const.mul
    (contDiff_uncurry_hughesYoungLocalizedLogKernel hX hY
      (hughesYoungReducedLeft_pos hh)
      (hughesYoungReducedRight_pos hh hk)
      (afeCriticalPoint t + w) (afeCriticalPoint (-t) + w))

theorem support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
    (T t c u : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) :
    Function.support (Function.uncurry
      (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hkernel : hughesYoungLocalizedLogKernel X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))
      (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    change hughesYoungMellinScalar T t c u h k *
      hughesYoungLocalizedLogKernel X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))
        (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) p.1 p.2 = 0
    rw [hz, mul_zero]
  exact support_uncurry_hughesYoungLocalizedLogKernel_subset
    hX hY _ _ _ _ hkernel

/-- The coprime-coordinate source summand satisfies literal DFI equation
(2), with no source-weight assumption. -/
theorem hughesYoungReducedLocalizedMellinWeight_equation2
    (T t c u : ℝ) {P X Y : ℝ}
    (hP : 1 ≤ P) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    DFIEquation2
      (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
      P X Y := by
  apply DFIEquation2.of_smooth_dyadicBox hP hX hY
    (contDiff_uncurry_hughesYoungReducedLocalizedMellinWeight
      T t c u (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) hh hk)
  exact ⟨support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
    T t c u (lt_of_lt_of_le (by norm_num) hX)
      (lt_of_lt_of_le (by norm_num) hY) h k⟩

/-- Exact equality between dilation of the original physical summand and
the coprime-coordinate summand.  The original box scales are `dX,dY`, while
the DFI scales after removing `d = gcd(h,k)` are `X,Y`. -/
theorem hughesYoungGCDScaledWeight_localized_eq_reduced
    (T t c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (x y : ℝ) :
    hughesYoungGCDScaledWeight h k
        (hughesYoungLocalizedMellinWeight T t c u
          ((hughesYoungCommonDivisor h k : ℝ) * X)
          ((hughesYoungCommonDivisor h k : ℝ) * Y) h k) x y =
      hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y := by
  let d : ℝ := hughesYoungCommonDivisor h k
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (hughesYoungCommonDivisor_pos hh).ne'
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (hughesYoungReducedLeft_pos hh).ne'
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast (hughesYoungReducedRight_pos hh hk).ne'
  have hleft : d * a = (h : ℝ) := by
    dsimp [d, a]
    exact_mod_cast hughesYoungCommonDivisor_mul_reducedLeft h k
  have hright : d * b = (k : ℝ) := by
    dsimp [d, b]
    exact_mod_cast hughesYoungCommonDivisor_mul_reducedRight h k
  have hscaleX : d * x / (d * X) = x / X := by
    field_simp
  have hscaleY : d * y / (d * Y) = y / Y := by
    field_simp
  have hargX : d * x / (h : ℝ) = x / a := by
    rw [← hleft]
    field_simp
  have hargY : d * y / (k : ℝ) = y / b := by
    rw [← hright]
    field_simp
  unfold hughesYoungGCDScaledWeight
  unfold hughesYoungLocalizedMellinWeight
  unfold hughesYoungReducedLocalizedMellinWeight
  unfold hughesYoungLocalizedLogKernel hughesYoungDyadicCutoffAt
  change hughesYoungMellinScalar T t c u h k *
      ((hughesYoungDyadicCutoff (d * x / (d * X)) : ℂ) *
        (hughesYoungDyadicCutoff (d * y / (d * Y)) : ℂ) *
        hughesYoungLogPower
          (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))
          (d * x / h) *
        hughesYoungLogPower
          (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))
          (d * y / k)) = _
  rw [hscaleX, hscaleY, hargX, hargY]

end RiemannZeta.GuthMaynard
