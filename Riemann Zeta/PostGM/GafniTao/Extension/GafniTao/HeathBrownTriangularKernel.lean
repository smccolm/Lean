import GafniTao.HeathBrownRefinedCount

/-!
# The triangular periodic kernel in Heath-Brown's refined count

Section 3 of arXiv:1601.04493v3 replaces the two sharp nearest-integer
conditions by a product of triangular periodic weights.  This file records
the literal weight and proves the pointwise majorization, support, bounds,
and positivity of the source Fourier coefficients.  The Fourier-series
identity is deliberately a later theorem: coefficient positivity by itself
is not that identity.
-/

namespace GafniTao

noncomputable section

/-- The one-dimensional periodic triangular weight. -/
noncomputable def heathBrownHat (B x : ℝ) : ℝ :=
  max (1 - B⁻¹ * heathBrownDistanceToInteger x) 0

theorem heathBrownHat_add_intCast (B x : ℝ) (q : ℤ) :
    heathBrownHat B (x + q) = heathBrownHat B x := by
  simp [heathBrownHat, heathBrownDistanceToInteger_add_intCast]

/-- The source two-dimensional weight `phi(x,y)`. -/
noncomputable def heathBrownTriangularKernel
    (B C x y : ℝ) : ℝ :=
  heathBrownHat B x * heathBrownHat C y

theorem heathBrownHat_nonneg (B x : ℝ) :
    0 ≤ heathBrownHat B x := by
  exact le_max_right _ _

theorem heathBrownHat_le_one
    {B x : ℝ} (hB : 0 ≤ B) :
    heathBrownHat B x ≤ 1 := by
  unfold heathBrownHat
  apply max_le
  · have hinv : 0 ≤ B⁻¹ := inv_nonneg.mpr hB
    have hdist := heathBrownDistanceToInteger_nonneg x
    nlinarith [mul_nonneg hinv hdist]
  · norm_num

theorem heathBrownHat_eq_zero_of_le_distance
    {B x : ℝ} (hB : 0 < B)
    (hx : B ≤ heathBrownDistanceToInteger x) :
    heathBrownHat B x = 0 := by
  unfold heathBrownHat
  rw [max_eq_right]
  rw [sub_nonpos]
  calc
    1 = B⁻¹ * B := by field_simp
    _ ≤ B⁻¹ * heathBrownDistanceToInteger x :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hB.le)

/-- A sharp condition at half the kernel width receives weight at least
`1/2`; this is the exact one-dimensional loss in the source majorant. -/
theorem one_half_le_heathBrownHat
    {B x : ℝ} (hB : 0 < B)
    (hx : heathBrownDistanceToInteger x ≤ B / 2) :
    (1 : ℝ) / 2 ≤ heathBrownHat B x := by
  unfold heathBrownHat
  apply (show (1 : ℝ) / 2 ≤ 1 - B⁻¹ * heathBrownDistanceToInteger x by
    have hprod : B⁻¹ * heathBrownDistanceToInteger x ≤ (1 : ℝ) / 2 := by
      calc
        B⁻¹ * heathBrownDistanceToInteger x ≤ B⁻¹ * (B / 2) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hB.le)
        _ = 1 / 2 := by field_simp
    linarith).trans
  exact le_max_left _ _

theorem one_quarter_le_heathBrownTriangularKernel
    {B C x y : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hx : heathBrownDistanceToInteger x ≤ B / 2)
    (hy : heathBrownDistanceToInteger y ≤ C / 2) :
    (1 : ℝ) / 4 ≤ heathBrownTriangularKernel B C x y := by
  unfold heathBrownTriangularKernel
  nlinarith [one_half_le_heathBrownHat hB hx,
    one_half_le_heathBrownHat hC hy,
    heathBrownHat_nonneg B x, heathBrownHat_nonneg C y]

theorem heathBrownTriangularKernel_nonneg (B C x y : ℝ) :
    0 ≤ heathBrownTriangularKernel B C x y := by
  exact mul_nonneg (heathBrownHat_nonneg B x) (heathBrownHat_nonneg C y)

theorem heathBrownTriangularKernel_le_one
    {B C x y : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    heathBrownTriangularKernel B C x y ≤ 1 := by
  unfold heathBrownTriangularKernel
  nlinarith [heathBrownHat_nonneg B x, heathBrownHat_nonneg C y,
    heathBrownHat_le_one (x := x) hB, heathBrownHat_le_one (x := y) hC]

/-- Removable-singularity version of `sin(pi r B)/(pi r B)`. -/
noncomputable def heathBrownSincCoefficient (B : ℝ) (r : ℤ) : ℝ :=
  if r = 0 then 1
  else Real.sin (Real.pi * (r : ℝ) * B) /
    (Real.pi * (r : ℝ) * B)

/-- The nonnegative one-dimensional coefficient appearing in the Fourier
series of the periodic triangular weight. -/
noncomputable def heathBrownHatFourierCoefficient
    (B : ℝ) (r : ℤ) : ℝ :=
  B * (heathBrownSincCoefficient B r) ^ 2

/-- The source coefficient `c_{r,s}`. -/
noncomputable def heathBrownTriangularFourierCoefficient
    (B C : ℝ) (r s : ℤ) : ℝ :=
  heathBrownHatFourierCoefficient B r *
    heathBrownHatFourierCoefficient C s

theorem heathBrownHatFourierCoefficient_zero (B : ℝ) :
    heathBrownHatFourierCoefficient B 0 = B := by
  simp [heathBrownHatFourierCoefficient, heathBrownSincCoefficient]

theorem heathBrownHatFourierCoefficient_nonneg
    {B : ℝ} (hB : 0 ≤ B) (r : ℤ) :
    0 ≤ heathBrownHatFourierCoefficient B r := by
  exact mul_nonneg hB (sq_nonneg _)

theorem heathBrownTriangularFourierCoefficient_nonneg
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (r s : ℤ) :
    0 ≤ heathBrownTriangularFourierCoefficient B C r s := by
  exact mul_nonneg (heathBrownHatFourierCoefficient_nonneg hB r)
    (heathBrownHatFourierCoefficient_nonneg hC s)

/-- The literal triangular weight attached to a pair of source indices. -/
noncomputable def heathBrownPairKernel
    (k H : ℕ) (f : ℝ → ℝ) (p : ℕ × ℕ) : ℝ :=
  heathBrownTriangularKernel
    (4 * (((H : ℝ) ^ (k - 2))⁻¹))
    (4 * (((H : ℝ) ^ (k - 1))⁻¹))
    (heathBrownDerivativeCoordinate f (k - 2) p.1 -
      heathBrownDerivativeCoordinate f (k - 2) p.2)
    (heathBrownDerivativeCoordinate f (k - 1) p.1 -
      heathBrownDerivativeCoordinate f (k - 1) p.2)

theorem one_quarter_le_heathBrownPairKernel_of_mem
    {N k H : ℕ} {f : ℝ → ℝ} {p : ℕ × ℕ}
    (hH : 0 < H) (hp : p ∈ heathBrownPairCountOne N k H f) :
    (1 : ℝ) / 4 ≤ heathBrownPairKernel k H f p := by
  rw [mem_heathBrownPairCountOne] at hp
  unfold heathBrownPairKernel
  have hpowPos (j : ℕ) : 0 < (((H : ℝ) ^ j)⁻¹) := by positivity
  apply one_quarter_le_heathBrownTriangularKernel
    (by positivity : 0 < 4 * (((H : ℝ) ^ (k - 2))⁻¹))
    (by positivity : 0 < 4 * (((H : ℝ) ^ (k - 1))⁻¹))
  · have hwidth :
        (4 * (((H : ℝ) ^ (k - 2))⁻¹)) / 2 =
          2 * (((H : ℝ) ^ (k - 2))⁻¹) := by ring
    rw [hwidth]
    exact hp.2.2.2.2.1
  · have hwidth :
        (4 * (((H : ℝ) ^ (k - 1))⁻¹)) / 2 =
          2 * (((H : ℝ) ^ (k - 1))⁻¹) := by ring
    rw [hwidth]
    exact hp.2.2.2.2.2

theorem heathBrownPairKernel_nonneg
    (k H : ℕ) (f : ℝ → ℝ) (p : ℕ × ℕ) :
    0 ≤ heathBrownPairKernel k H f p := by
  unfold heathBrownPairKernel
  exact heathBrownTriangularKernel_nonneg _ _ _ _

/-- Exact finite form of the source majorization
`mathcal N_1 \ll sum_{m,n} phi(...)`; the displayed source normalization
gives the explicit constant four. -/
theorem heathBrownPairCountOne_quarter_le_kernel_sum
    {N k H : ℕ} {f : ℝ → ℝ} (hH : 0 < H) :
    ((heathBrownPairCountOne N k H f).card : ℝ) / 4 ≤
      ∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        heathBrownPairKernel k H f p := by
  classical
  calc
    ((heathBrownPairCountOne N k H f).card : ℝ) / 4 =
        ∑ _p ∈ heathBrownPairCountOne N k H f, (1 : ℝ) / 4 := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ p ∈ heathBrownPairCountOne N k H f,
        heathBrownPairKernel k H f p := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_quarter_le_heathBrownPairKernel_of_mem hH hp
    _ ≤ ∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        heathBrownPairKernel k H f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp _
        exact heathBrownPairKernel_nonneg k H f p

#print axioms heathBrownHat_nonneg
#print axioms heathBrownHat_le_one
#print axioms heathBrownHat_eq_zero_of_le_distance
#print axioms one_half_le_heathBrownHat
#print axioms one_quarter_le_heathBrownTriangularKernel
#print axioms heathBrownTriangularKernel_nonneg
#print axioms heathBrownTriangularKernel_le_one
#print axioms heathBrownHatFourierCoefficient_zero
#print axioms heathBrownHatFourierCoefficient_nonneg
#print axioms heathBrownTriangularFourierCoefficient_nonneg
#print axioms one_quarter_le_heathBrownPairKernel_of_mem
#print axioms heathBrownPairKernel_nonneg
#print axioms heathBrownPairCountOne_quarter_le_kernel_sum

end

end GafniTao
