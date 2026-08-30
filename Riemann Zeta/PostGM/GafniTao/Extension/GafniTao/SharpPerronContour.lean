import GafniTao.SharpPerronBounds

/-!
# Rectangle entry for the sharp Perron kernel

The meromorphic function `q^s / s` has residue one at the origin.  This file
proves that statement on an arbitrary finite rectangle crossing the origin,
using the frozen foundation's kernel-checked rectangle residue theorem.
-/

open Complex Set Filter Asymptotics

namespace GafniTao

/-- The scalar form of the finite Perron kernel, with ratio `q` exposed. -/
noncomputable def sharpPerronRatioKernel (c T q : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-T)..T,
      (q : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)

/-- The scalar kernel is exactly the normalized right vertical edge used by
the rectangle residue theorem. -/
theorem sharpPerronRatioKernel_eq_VIntegral'
    (c T q : ℝ) :
    sharpPerronRatioKernel c T q =
      VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c (-T) T := by
  rw [sharpPerronRatioKernel]
  simp only [VIntegral', VIntegral, smul_eq_mul]
  have hscalar :
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
        1 / (2 * (Real.pi : ℂ)) := by
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [← mul_assoc, hscalar]

/-- Passing from the two physical variables `x,n` to their positive ratio
does not change the exact kernel. -/
theorem sharpPerronKernel_eq_ratioKernel
    {c T x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) :
    sharpPerronKernel c T x n =
      sharpPerronRatioKernel c T (x / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hratio : 0 ≤ x / (n : ℝ) := (div_pos hx hnpos).le
  have hnnonneg : 0 ≤ (n : ℝ) := hnpos.le
  rw [sharpPerronKernel, sharpPerronRatioKernel]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  let s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  have hnpow : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast hnpos.ne')
  have hmul : (x : ℂ) = ((x / (n : ℝ) : ℝ) : ℂ) * (n : ℂ) := by
    exact_mod_cast (div_mul_cancel₀ x hnpos.ne').symm
  have hncast : (n : ℂ) = (((n : ℝ) : ℂ)) := by norm_num
  change (x : ℂ) ^ s / (n : ℂ) ^ s / s =
    ((x / (n : ℝ) : ℝ) : ℂ) ^ s / s
  rw [hmul, hncast, Complex.mul_cpow_ofReal_nonneg hratio hnnonneg]
  field_simp [hnpow]

private theorem sharpPerronMonomial_near_zero
    {q : ℝ} (hq : 0 < q) :
    ((fun s : ℂ => (q : ℂ) ^ s / s) - (fun s : ℂ => 1 / (s - 0)))
      =O[nhdsWithin (0 : ℂ) {0}ᶜ] (1 : ℂ → ℂ) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hderiv : HasDerivAt (fun s : ℂ => (q : ℂ) ^ s)
      (deriv (fun s : ℂ => (q : ℂ) ^ s) 0) 0 :=
    (differentiableAt_fun_id.const_cpow (.inl hq0)).hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hlim : Tendsto
      (fun s : ℂ => (q : ℂ) ^ s / s - 1 / s)
      (nhdsWithin (0 : ℂ) {0}ᶜ)
      (nhds (deriv (fun z : ℂ => (q : ℂ) ^ z) 0)) := by
    convert hslope using 1
    ext s
    rw [slope_def_field]
    simp only [sub_zero, Complex.cpow_zero]
    ring
  simpa only [Pi.sub_apply, sub_zero] using hlim.isBigO_one ℂ

/-- The exact normalized boundary integral of `q^s/s` is one on every
axis-parallel rectangle whose interior contains the origin. -/
theorem sharpPerron_rectangleIntegral_eq_one
    {q left right T : ℝ} (hq : 0 < q) (hleft : left < 0)
    (hright : 0 < right) (hT : 0 < T) :
    RectangleIntegral'
        (fun s : ℂ => (q : ℂ) ^ s / s)
        ((left : ℂ) - (T : ℂ) * Complex.I)
        ((right : ℂ) + (T : ℂ) * Complex.I) = 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole'
      (p := 0) (A := 1)
  · simp only [sub_re, ofReal_re, mul_re, ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_re]
    linarith
  · simp only [sub_im, ofReal_im, mul_im, Complex.I_im, ofReal_re,
      Complex.I_re, mul_zero, zero_add, add_im]
    linarith
  · rw [rectangle_mem_nhds_iff]
    rw [mem_reProdIm]
    have hreLeft : ((left : ℂ) - (T : ℂ) * Complex.I).re = left := by simp
    have hreRight : ((right : ℂ) + (T : ℂ) * Complex.I).re = right := by simp
    have himLeft : ((left : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
    have himRight : ((right : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
    rw [hreLeft, hreRight, himLeft, himRight]
    simp only [Complex.zero_re, Complex.zero_im]
    rw [Set.uIoo_of_le (hleft.le.trans hright.le),
      Set.uIoo_of_le (by linarith : -T ≤ T)]
    exact ⟨⟨hleft, hright⟩, ⟨neg_lt_zero.mpr hT, hT⟩⟩
  · have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    apply DifferentiableOn.div
    · exact differentiableOn_id.const_cpow (.inl hq0)
    · exact differentiableOn_id
    · intro s hs
      simpa only [Set.mem_diff, Set.mem_singleton_iff] using hs.2
  · simpa using sharpPerronMonomial_near_zero hq

/-- Exact finite-height Perron decomposition for `q > 0`: the desired right
vertical edge is the residue plus the other three oriented rectangle edges.
No limiting contour or asymptotic notation is hidden in this identity. -/
theorem sharpPerronRatioKernel_eq_residue_add_edges
    {q left c T : ℝ} (hq : 0 < q) (hleft : left < 0)
    (hc : 0 < c) (hT : 0 < T) :
    sharpPerronRatioKernel c T q =
      1 - HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c (-T) +
        HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left c T +
          VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) left (-T) T := by
  rw [sharpPerronRatioKernel_eq_VIntegral']
  have hrect := sharpPerron_rectangleIntegral_eq_one
    (q := q) (left := left) (right := c) (T := T) hq hleft hc hT
  have hreLeft : ((left : ℂ) - (T : ℂ) * Complex.I).re = left := by simp
  have hreRight : ((c : ℂ) + (T : ℂ) * Complex.I).re = c := by simp
  have himLeft : ((left : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
  have himRight : ((c : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

/-- If the rectangle stays in the positive half-plane, there is no enclosed
pole.  The left vertical Perron kernel is therefore exactly the sum of the
other three oriented edges.  This is the contour identity used when `q < 1`.
-/
theorem sharpPerronRatioKernel_eq_edges_of_right_shift
    {q c right T : ℝ} (hq : 0 < q) (hc : 0 < c)
    (hcr : c < right) (hT : 0 < T) :
    sharpPerronRatioKernel c T q =
      HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right (-T) -
        HIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) c right T +
          VIntegral' (fun s : ℂ => (q : ℂ) ^ s / s) right (-T) T := by
  rw [sharpPerronRatioKernel_eq_VIntegral']
  let z : ℂ := (c : ℂ) - (T : ℂ) * Complex.I
  let w : ℂ := (right : ℂ) + (T : ℂ) * Complex.I
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hzeroNot : (0 : ℂ) ∉ Rectangle z w := by
    intro hzero
    have hre := hzero.1
    have hreEndpoints : z.re = c ∧ w.re = right := by
      constructor <;> simp [z, w]
    rw [hreEndpoints.1, hreEndpoints.2, Set.uIcc_of_le hcr.le] at hre
    have hc0 : c ≤ 0 := by simpa using hre.1
    linarith
  have hholo : HolomorphicOn
      (fun s : ℂ => (q : ℂ) ^ s / s) (Rectangle z w) := by
    apply DifferentiableOn.div
    · exact differentiableOn_id.const_cpow (.inl hq0)
    · exact differentiableOn_id
    · intro s hs
      intro hs0
      exact hzeroNot (hs0 ▸ hs)
  have hrect : RectangleIntegral'
      (fun s : ℂ => (q : ℂ) ^ s / s) z w = 0 := by
    rw [RectangleIntegral']
    rw [hholo.vanishesOnRectangle (by rfl), smul_zero]
  have hreLeft : z.re = c := by simp [z]
  have hreRight : w.re = right := by simp [w]
  have himLeft : z.im = -T := by simp [z]
  have himRight : w.im = T := by simp [w]
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  have hscalar : (1 / (2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    exact one_div_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)
  have hraw := (mul_eq_zero.mp hrect).resolve_left hscalar
  linear_combination -(1 / (2 * (Real.pi : ℂ) * Complex.I)) * hraw

end GafniTao
