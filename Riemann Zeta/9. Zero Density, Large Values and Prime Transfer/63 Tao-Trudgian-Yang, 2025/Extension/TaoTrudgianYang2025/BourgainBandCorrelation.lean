import TaoTrudgianYang2025.BourgainBandOccupancy

/-!
# Physical normalization of actual band occupancy

The correlation parameter is a ratio of the actual occupancy integral
to the square roots of the actual band measure and integer-set size.
Its bounds follow from the two proved occupancy estimates.
-/

open MeasureTheory
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual normalized occupancy, corresponding to the source's
second level parameter before small-power losses are absorbed. -/
def bourgainZetaBandCorrelation (D : Finset ℤ) (H T V : ℝ) : ℝ :=
  bourgainZetaBandMass D H T V /
    (Real.sqrt (volume.real (bourgainZetaBand T V))*Real.sqrt (D.card : ℝ))

/-- Positive occupancy defines a positive normalized parameter with
an exact mass identity and finite physical versions of the source's
measure/cardinality comparisons. -/
theorem bourgainZetaBandCorrelation_bounds (D : Finset ℤ) {H T V : ℝ}
    (hH : 0 < H) (hmass : 0 < bourgainZetaBandMass D H T V) :
    let r := bourgainZetaBandCorrelation D H T V
    let μ := volume.real (bourgainZetaBand T V)
    let R := (D.card : ℝ)
    let K := (2*Nat.ceil H+1 : ℕ)
    0 < r ∧ 0 < μ ∧ 0 < R ∧
    bourgainZetaBandMass D H T V = r*Real.sqrt μ*Real.sqrt R ∧
    r^2 ≤ 2*H*(K : ℝ) ∧
    r^2*μ ≤ 4*H^2*R ∧
    r^2*R ≤ (K : ℝ)^2*μ := by
  let M := bourgainZetaBandMass D H T V
  let μ := volume.real (bourgainZetaBand T V)
  let R := (D.card : ℝ)
  let K := (2*Nat.ceil H+1 : ℕ)
  let r := bourgainZetaBandCorrelation D H T V
  have hcard : M ≤ 2*H*R := (bourgainZetaBandMass_bounds D hH.le T V).2
  have hoverlap : M ≤ (K : ℝ)*μ := bourgainZetaBandMass_le_measure D hH.le T V
  have hR : 0 < R := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*H) (le_of_not_gt h)
    linarith
  have hμ : 0 < μ := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg K) (le_of_not_gt h)
    linarith
  have hd : 0 < Real.sqrt μ*Real.sqrt R :=
    mul_pos (Real.sqrt_pos.mpr hμ) (Real.sqrt_pos.mpr hR)
  have hr : 0 < r := div_pos hmass hd
  have heq : M = r*Real.sqrt μ*Real.sqrt R := by
    dsimp only [r, bourgainZetaBandCorrelation]
    rw [mul_assoc, div_mul_cancel₀ _ hd.ne']
  have hsμ : (Real.sqrt μ)^2 = μ := Real.sq_sqrt hμ.le
  have hsR : (Real.sqrt R)^2 = R := Real.sq_sqrt hR.le
  have hs : M^2 = r^2*μ*R := by rw [heq, mul_pow, mul_pow, hsμ, hsR]
  have hprod : M^2 ≤ (2*H*R)*((K : ℝ)*μ) := by
    simpa only [pow_two] using mul_le_mul hcard hoverlap hmass.le (by positivity)
  have hsqcard : M^2 ≤ (2*H*R)^2 := pow_le_pow_left₀ hmass.le hcard 2
  have hsqmeasure : M^2 ≤ ((K : ℝ)*μ)^2 := pow_le_pow_left₀ hmass.le hoverlap 2
  refine ⟨hr, hμ, hR, heq, ?_, ?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hμ hR)).mp
    nlinarith [hprod]
  · apply (mul_le_mul_iff_of_pos_right hR).mp
    nlinarith [hsqcard]
  · apply (mul_le_mul_iff_of_pos_right hμ).mp
    nlinarith [hsqmeasure]

end TaoTrudgianYang2025
