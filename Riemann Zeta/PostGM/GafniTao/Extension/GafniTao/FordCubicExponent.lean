import GafniTao.FordDyadicExponent

/-!
# Unimodality of Ford's cubic exponent

The source's sum-to-integral step depends on the actual cubic, not an
unspecified unimodal majorant.  We isolate its two positive coefficients and
prove the exact turning point algebraically.
-/

open Set

namespace GafniTao

noncomputable section

def fordCubicA (sigma : ℝ) : ℝ :=
  (1 - sigma) * Real.log 2

def fordCubicB (D t : ℝ) : ℝ :=
  Real.log 2 ^ 3 / (D * Real.log t ^ 2)

def fordCubicExponent (D sigma t x : ℝ) : ℝ :=
  fordCubicA sigma * x - fordCubicB D t * x ^ 3

def fordCubicTurningPoint (D sigma t : ℝ) : ℝ :=
  Real.sqrt (fordCubicA sigma / (3 * fordCubicB D t))

theorem fordDyadicExponent_eq_cubic
    (D sigma t : ℝ) (j : ℕ) :
    fordDyadicExponent D sigma t j =
      fordCubicExponent D sigma t j := by
  unfold fordDyadicExponent fordCubicExponent fordCubicA fordCubicB
  ring

theorem fordCubicA_nonneg
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    0 ≤ fordCubicA sigma := by
  unfold fordCubicA
  exact mul_nonneg (sub_nonneg.mpr hsigma) (Real.log_pos (by norm_num)).le

theorem fordCubicB_pos
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    0 < fordCubicB D t := by
  unfold fordCubicB
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : 0 < Real.log t := Real.log_pos ht
  positivity

theorem fordCubicTurningPoint_nonneg
    (D sigma t : ℝ) :
    0 ≤ fordCubicTurningPoint D sigma t := by
  exact Real.sqrt_nonneg _

theorem fordCubicTurningPoint_sq
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    fordCubicTurningPoint D sigma t ^ 2 =
      fordCubicA sigma / (3 * fordCubicB D t) := by
  unfold fordCubicTurningPoint
  rw [Real.sq_sqrt]
  exact div_nonneg (fordCubicA_nonneg hsigma)
    (mul_nonneg (by norm_num) (fordCubicB_pos hD ht).le)

theorem fordCubicExponent_sub
    (D sigma t x y : ℝ) :
    fordCubicExponent D sigma t y -
        fordCubicExponent D sigma t x =
      (y - x) *
        (fordCubicA sigma - fordCubicB D t *
          (y ^ 2 + y * x + x ^ 2)) := by
  unfold fordCubicExponent
  ring

theorem fordCubicExponent_turningPoint
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    fordCubicExponent D sigma t
        (fordCubicTurningPoint D sigma t) =
      (2 / 3 : ℝ) * fordCubicA sigma *
        fordCubicTurningPoint D sigma t := by
  have hB := fordCubicB_pos hD ht
  have hsq := fordCubicTurningPoint_sq hsigma hD ht
  have hBx :
      fordCubicB D t * fordCubicTurningPoint D sigma t ^ 2 =
        fordCubicA sigma / 3 := by
    rw [hsq]
    field_simp [hB.ne']
  unfold fordCubicExponent
  rw [show fordCubicB D t * fordCubicTurningPoint D sigma t ^ 3 =
      fordCubicTurningPoint D sigma t *
        (fordCubicB D t * fordCubicTurningPoint D sigma t ^ 2) by ring,
    hBx]
  ring

theorem fordCubicExponent_monotoneOn_left
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    MonotoneOn (fordCubicExponent D sigma t)
      (Set.Icc 0 (fordCubicTurningPoint D sigma t)) := by
  intro x hx y hy hxy
  have hB := fordCubicB_pos hD ht
  have hx0 := hx.1
  have hyTurn := hy.2
  have hturn0 := fordCubicTurningPoint_nonneg D sigma t
  have hsq := fordCubicTurningPoint_sq hsigma hD ht
  have hsum :
      y ^ 2 + y * x + x ^ 2 ≤
        3 * fordCubicTurningPoint D sigma t ^ 2 := by
    nlinarith [sq_nonneg (y - x), sq_nonneg
      (fordCubicTurningPoint D sigma t - y)]
  have hcoefficient :
      0 ≤ fordCubicA sigma - fordCubicB D t *
        (y ^ 2 + y * x + x ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hsum hB.le
    rw [hsq] at hmul
    field_simp [hB.ne'] at hmul
    linarith
  rw [← sub_nonneg, fordCubicExponent_sub]
  exact mul_nonneg (sub_nonneg.mpr hxy) hcoefficient

theorem fordCubicExponent_antitoneOn_right
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    AntitoneOn (fordCubicExponent D sigma t)
      (Set.Ici (fordCubicTurningPoint D sigma t)) := by
  intro x hx y hy hxy
  have hB := fordCubicB_pos hD ht
  have hturn0 := fordCubicTurningPoint_nonneg D sigma t
  have hsq := fordCubicTurningPoint_sq hsigma hD ht
  have hxTurn : fordCubicTurningPoint D sigma t ≤ x := hx
  have hyTurn : fordCubicTurningPoint D sigma t ≤ y := hy
  have hx0 : 0 ≤ x := hturn0.trans hxTurn
  have hy0 : 0 ≤ y := hturn0.trans hyTurn
  have hxSq : fordCubicTurningPoint D sigma t ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxTurn)
      (add_nonneg hx0 hturn0)]
  have hySq : fordCubicTurningPoint D sigma t ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyTurn)
      (add_nonneg hy0 hturn0)]
  have hxyProd : fordCubicTurningPoint D sigma t ^ 2 ≤ y * x := by
    have := mul_le_mul hyTurn hxTurn hturn0 hy0
    nlinarith
  have hsum :
      3 * fordCubicTurningPoint D sigma t ^ 2 ≤
        y ^ 2 + y * x + x ^ 2 := by
    linarith
  have hcoefficient :
      fordCubicA sigma - fordCubicB D t *
        (y ^ 2 + y * x + x ^ 2) ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hsum hB.le
    rw [hsq] at hmul
    field_simp [hB.ne'] at hmul
    linarith
  have hprod :
      (y - x) * (fordCubicA sigma - fordCubicB D t *
        (y ^ 2 + y * x + x ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hcoefficient
  rw [← sub_nonneg]
  linarith [fordCubicExponent_sub D sigma t x y]

theorem fordCubicExp_monotoneOn_left
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    MonotoneOn (fun x => Real.exp (fordCubicExponent D sigma t x))
      (Set.Icc 0 (fordCubicTurningPoint D sigma t)) := by
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr
    (fordCubicExponent_monotoneOn_left hsigma hD ht hx hy hxy)

theorem fordCubicExp_antitoneOn_right
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    AntitoneOn (fun x => Real.exp (fordCubicExponent D sigma t x))
      (Set.Ici (fordCubicTurningPoint D sigma t)) := by
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr
    (fordCubicExponent_antitoneOn_right hsigma hD ht hx hy hxy)

theorem fordCubicExponent_le_turningPoint
    {D sigma t x : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (hx : 0 ≤ x) :
    fordCubicExponent D sigma t x ≤
      fordCubicExponent D sigma t
        (fordCubicTurningPoint D sigma t) := by
  by_cases hleft : x ≤ fordCubicTurningPoint D sigma t
  · exact fordCubicExponent_monotoneOn_left hsigma hD ht
      ⟨hx, hleft⟩
      ⟨fordCubicTurningPoint_nonneg D sigma t, le_rfl⟩ hleft
  · have hRight : fordCubicTurningPoint D sigma t ≤ x :=
      (lt_of_not_ge hleft).le
    exact fordCubicExponent_antitoneOn_right hsigma hD ht
      (by simp) hRight hRight

theorem fordCubicExp_le_turningPoint
    {D sigma t x : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (hx : 0 ≤ x) :
    Real.exp (fordCubicExponent D sigma t x) ≤
      Real.exp (fordCubicExponent D sigma t
        (fordCubicTurningPoint D sigma t)) :=
  Real.exp_le_exp.mpr
    (fordCubicExponent_le_turningPoint hsigma hD ht hx)

#print axioms fordCubicTurningPoint_sq
#print axioms fordCubicExponent_turningPoint
#print axioms fordCubicExponent_monotoneOn_left
#print axioms fordCubicExponent_antitoneOn_right
#print axioms fordCubicExponent_le_turningPoint

end

end GafniTao
