import TaoTrudgianYang2025.EnergyPoweredPatterns
import TaoTrudgianYang2025.GuthMaynardBridge
import GuthMaynard.LargeValuesEnergy
import GuthMaynard.LargeValuesLanguage

/-!
# Finite Heath--Brown energy inequality on the actual source patterns

The native second and fourth moments give the required cardinality factor
in the mixed fourth-moment term. This derivation does not use the discrepant
finite inequality printed in the pinned Tao--Trudgian--Yang proof.
-/

open Complex Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Exact bridge between indexed quadruples and the native ordered-pair
quadruples. Both sides count unit-tolerance approximate equalities. -/
theorem finsetAdditiveEnergy_eq_native (W : Finset ℝ) :
    finsetAdditiveEnergy W = ApproxAddEnergy 1 W := by
  classical
  unfold finsetAdditiveEnergy approximateAdditiveEnergyOf ApproxAddEnergy
  apply Finset.card_bij (fun q _ => ((((q 0 : ↥W) : ℝ), ((q 1 : ↥W) : ℝ)),
    (((q 2 : ↥W) : ℝ), ((q 3 : ↥W) : ℝ))))
  · intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨(q 0).2, (q 1).2⟩,
        Finset.mem_product.mpr ⟨(q 2).2, (q 3).2⟩⟩,
      (Finset.mem_filter.mp hq).2⟩
  · intro q hq r hr heq
    have h0 := congrArg (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.1) heq
    have h1 := congrArg (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.2) heq
    have h2 := congrArg (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.2.1) heq
    have h3 := congrArg (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.2.2) heq
    funext i
    fin_cases i <;> apply Subtype.ext <;> assumption
  · intro q hq
    simp only [approximateAdditiveQuadruples, mem_filter, mem_product] at hq
    refine ⟨![⟨q.1.1, hq.1.1.1⟩, ⟨q.1.2, hq.1.1.2⟩,
      ⟨q.2.1, hq.1.2.1⟩, ⟨q.2.2, hq.1.2.2⟩], ?_, ?_⟩
    · simpa using hq.2
    · rfl

/-- Reflecting the ordinate interval preserves the actual energy exactly. -/
theorem LargeValuePattern.reflectedOrdinates_energy (P : LargeValuePattern) :
    ApproxAddEnergy 1 P.reflectedOrdinates = finsetAdditiveEnergy P.ordinates := by
  rw [finsetAdditiveEnergy_eq_native]
  have heq : P.reflectedOrdinates = gmAffineImage (-1) P.intervalRight P.ordinates := by
    unfold LargeValuePattern.reflectedOrdinates gmAffineImage
    congr 1
    funext t
    ring
  rw [heq]
  simpa using approxAddEnergy_affine 1 (-1) P.intervalRight (by norm_num) P.ordinates

/-- Exact reflected polynomial identity on half-open native support. -/
theorem LargeValuePattern.reflectedHalfOpenPolynomial_eq
    (P : LargeValuePattern) (t : ℝ) :
    sourceDirichletPoly P.scale P.reflectedCoeffs (P.intervalRight - t) =
      dirichletPoly P.scale P.coeff t := by
  unfold sourceDirichletPoly dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnclosed : n ∈ publishedDyadicInterval P.scale := by
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
  convert P.reflectedTerm_eq hnclosed t using 1
  simp only [dirichletPhase]
  congr 2
  ring

/-- The source threshold survives the support and phase bridge with just
the explicitly accounted one-point endpoint loss. -/
theorem LargeValuePattern.reflectedHalfOpen_large (P : LargeValuePattern) :
    ∀ t ∈ P.reflectedOrdinates,
      P.V - 1 ≤ ‖sourceDirichletPoly P.scale P.reflectedCoeffs t‖ := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  rw [P.reflectedHalfOpenPolynomial_eq]
  simpa only [dirichletPoly, dyadicInterval, zero_add, neg_mul, mul_comm I] using
    P.halfOpen_large hu

/-- A squared finite Heath--Brown inequality, uniform before the pattern
is chosen. The physical height may be enlarged to `max N T`; this will be
removed exactly at the exponent level. -/
theorem heathBrown_largeValuePattern_energy_squared :
    ∀ ε : ℝ, 0 < ε → ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
      ∀ (P : LargeValuePattern) (H : ℝ), H₀ ≤ H → P.N ≤ H → P.T ≤ H →
        1 < P.V →
        ((finsetAdditiveEnergy P.ordinates : ℝ) * (P.V - 1) ^ 2) ^ 2 ≤
          C * H ^ ε *
            ((P.ordinates.card : ℝ) ^ 2 * P.N +
              (P.ordinates.card : ℝ) * P.N ^ 2 +
              (P.ordinates.card : ℝ) ^ (5 / 4 : ℝ) * H ^ (1 / 2 : ℝ) * P.N) *
            ((P.ordinates.card : ℝ) ^ 4 * P.N +
              (finsetAdditiveEnergy P.ordinates : ℝ) * P.N ^ 2 +
              (finsetAdditiveEnergy P.ordinates : ℝ) ^ (3 / 4 : ℝ) *
                (P.ordinates.card : ℝ) * H ^ (1 / 2 : ℝ) * P.N) := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨C₁, H₁, hC₁, hH₁, henergy⟩ := gmApproxAddEnergy_largeValues_native (ε / 4) hquarter
  obtain ⟨C₂, H₂, hC₂, hH₂, hsecond⟩ := gmDiscreteRatioSecondMoment_native (ε / 4) hquarter
  obtain ⟨C₄, H₄, hC₄, hH₄, hfourth⟩ := gmDiscreteFourthMoment_native (ε / 4) hquarter
  refine ⟨C₁ ^ 2 * C₂ * C₄, max H₁ (max H₂ H₄), by positivity,
    hH₁.trans (le_max_left _ _), ?_⟩
  intro P H hH hNH hTH hV
  have hHpos : 0 < H := zero_lt_one.trans_le (hH₁.trans ((le_max_left _ _).trans hH))
  have hN : (P.scale : ℝ) ≤ H := by simpa only [P.N_eq_scale] using hNH
  have hbase : InBaseInterval H P.reflectedOrdinates := by
    intro t ht
    exact ⟨(P.reflectedOrdinates_inBaseInterval t ht).1,
      (P.reflectedOrdinates_inBaseInterval t ht).2.trans hTH⟩
  have hcoeff : ∀ n ∈ dyadicInterval P.scale, ‖P.reflectedCoeffs n‖ ≤ 1 := by
    intro n hn
    exact P.reflectedCoeffs_one_bounded n
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
  have hE := henergy P.scale H (P.V - 1) P.reflectedOrdinates P.reflectedCoeffs
    P.scale_pos ((le_max_left _ _).trans hH) hN (by linarith)
    P.reflectedOrdinates_isSeparated hcoeff P.reflectedHalfOpen_large
  have h₂ := hsecond P.scale H P.reflectedOrdinates P.scale_pos
    ((le_max_left _ _).trans ((le_max_right _ _).trans hH))
    P.reflectedOrdinates_isSeparated hbase
  have h₄ := hfourth P.scale H P.reflectedOrdinates P.scale_pos
    ((le_max_right _ _).trans ((le_max_right _ _).trans hH)) hN
    P.reflectedOrdinates_isSeparated hbase
  have hCS := gmDiscreteThirdMoment_sq_le_second_mul_fourth P.scale P.reflectedOrdinates
  have hm (p : ℕ) : 0 ≤ gmDiscreteRatioMoment p P.scale P.reflectedOrdinates := by
    unfold gmDiscreteRatioMoment
    positivity
  have hprod := mul_le_mul h₂ h₄ (hm 4) (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤
    (ApproxAddEnergy 1 P.reflectedOrdinates : ℝ) * (P.V - 1) ^ 2) hE 2
  have hscaled := mul_le_mul_of_nonneg_left (hCS.trans hprod) (sq_nonneg (C₁ * H ^ (ε / 4)))
  have hbound := hsq.trans (by simpa only [mul_pow] using hscaled)
  rw [P.reflectedOrdinates_energy, P.reflectedOrdinates_card, ← P.N_eq_scale] at hbound
  convert hbound using 1
  have hp : (H ^ (ε / 4)) ^ 2 * H ^ (ε / 4) * H ^ (ε / 4) = H ^ ε := by
    rw [pow_two, ← Real.rpow_add hHpos, ← Real.rpow_add hHpos, ← Real.rpow_add hHpos]
    congr 1
    ring
  ring_nf at hp ⊢
  rw [← hp]

end TaoTrudgianYang2025
