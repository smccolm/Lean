import TaoTrudgianYang2025.BourgainDyadicBands

/-!
# Selecting a genuine band from local zeta-square mass

The finite pigeonhole step keeps its low-amplitude remainder. A later
consumer chooses the floor from the actual positive mass; no selector or
zeta distribution estimate is supplied as an assumption.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Integrated finite amplitude partition on the actual translated
integer windows. The low floor costs their full total length. -/
theorem bourgainZetaBand_mass_partition (D : Finset ℤ)
    {H T a : ℝ} (hH : 0 ≤ H) {J : ℕ}
    (hrange : ∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T, zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ) ≤
      2*H*a^2*(D.card : ℝ) +
        ∑ j ∈ Finset.range J, (2*(a*(2 : ℝ)^j))^2 *
          bourgainZetaBandMass D H T (a*(2 : ℝ)^j) := by
  let g := fun (ℓ : ℤ) (j : ℕ) (u : ℝ) => (2*(a*(2 : ℝ)^j))^2 *
    (bourgainZetaBand T (a*(2 : ℝ)^j)).indicator (fun _ => (1 : ℝ)) ((ℓ : ℝ)+u)
  have hgi (ℓ : ℤ) (j : ℕ) : IntervalIntegrable (g ℓ j) volume (-H) H :=
    (bourgain_indicator_intervalIntegrable
      (measurableSet_bourgainZetaBand T (a*(2 : ℝ)^j)) ℓ (-H) H).const_mul _
  have hgs (ℓ : ℤ) : IntervalIntegrable (fun u => ∑ j ∈ Finset.range J, g ℓ j u)
      volume (-H) H := by
    convert IntervalIntegrable.sum (Finset.range J) (fun j _ => hgi ℓ j) using 1
    ext u
    simp only [Finset.sum_apply]
  have hlocal (ℓ : ℤ) (hℓ : ℓ ∈ D) :
      bourgainLocalZetaSquare H ℓ ≤ 2*H*a^2 +
        ∑ j ∈ Finset.range J, ∫ u in -H..H, g ℓ j u := by
    have hi : IntervalIntegrable
        (fun u => zetaMomentCriticalNorm ((ℓ : ℝ)+u)^2) volume (-H) H :=
      ((continuous_zetaMomentCriticalNorm.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable _ _
    calc
      _ ≤ ∫ u in -H..H, a^2 + ∑ j ∈ Finset.range J, g ℓ j u := by
        apply intervalIntegral.integral_mono_on (by linarith) hi
          (IntervalIntegrable.add intervalIntegrable_const (hgs ℓ))
        intro u hu
        have ht : (ℓ : ℝ)+u ∈ Icc (-T) T := by
          obtain ⟨hl, hr⟩ := hrange ℓ hℓ
          constructor <;> linarith [hu.1, hu.2]
        exact bourgainZetaBand_square_partition ht (hterminal _ ht)
      _ = _ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hgs ℓ),
          intervalIntegral.integral_finsetSum (fun j _ => hgi ℓ j),
          intervalIntegral.integral_const, smul_eq_mul]
        ring
  calc
    _ ≤ ∑ ℓ ∈ D, (2*H*a^2 + ∑ j ∈ Finset.range J, ∫ u in -H..H, g ℓ j u) :=
      Finset.sum_le_sum hlocal
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm (D.card : ℝ)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bourgainZetaBandMass_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      exact intervalIntegral.integral_const_mul _ _

/-- Finite maximization gives a real band carrying a share of the mass
above the low floor, with the exact number of bands retained. -/
theorem bourgainZetaBand_select (D : Finset ℤ)
    {H T a : ℝ} (hH : 0 ≤ H) {J : ℕ} (hJ : 0 < J)
    (hrange : ∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H)
    (hterminal : ∀ t ∈ Icc (-T) T, zetaMomentCriticalNorm t < a*(2 : ℝ)^J) :
    ∃ j ∈ Finset.range J,
      (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ) ≤ 2*H*a^2*(D.card : ℝ) +
        (J : ℝ)*(2*(a*(2 : ℝ)^j))^2*bourgainZetaBandMass D H T (a*(2 : ℝ)^j) := by
  let mass := fun j => (2*(a*(2 : ℝ)^j))^2*bourgainZetaBandMass D H T (a*(2 : ℝ)^j)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr hJ.ne')
  refine ⟨j, hj, (bourgainZetaBand_mass_partition D hH hrange hterminal).trans ?_⟩
  have hs : (∑ i ∈ Finset.range J, mass i) ≤ (J : ℝ)*mass j := by
    calc
      _ ≤ ∑ _i ∈ Finset.range J, mass j := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  dsimp only [mass] at hs
  nlinarith

/-- A positive mass defines a positive floor whose integrated low-value
contribution is exactly one half of that mass. -/
theorem bourgainZetaBand_half_floor {L H R : ℝ} (hL : 0 < L) (hH : 0 < H) (hR : 0 < R) :
    0 < Real.sqrt (L/(4*H*R)) ∧
      2*H*(Real.sqrt (L/(4*H*R)))^2*R = L/2 := by
  have hden : 0 < 4*H*R := by positivity
  constructor
  · exact Real.sqrt_pos.mpr (div_pos hL hden)
  · rw [Real.sq_sqrt (div_pos hL hden).le]
    field_simp
    ring

end TaoTrudgianYang2025
