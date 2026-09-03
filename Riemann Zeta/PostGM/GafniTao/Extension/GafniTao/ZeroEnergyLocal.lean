import GafniTao.LocalZeroCount

/-!
# The elementary local-zero comparison between `A*` and `A`

Gafni--Tao use the standard estimate `A*(sigma) <= 3 A(sigma)`.  Once the
first three zeros are fixed, the tolerance-one condition confines the fourth
ordinate to an interval of length two.  Three half-open integer unit bins
cover this interval, and the multiplicity in each bin is `O(log T)`.
-/

open scoped BigOperators
open Asymptotics Filter

namespace GafniTao

private theorem finset_sum_union_le
    {α : Type*} [DecidableEq α] (f : α → ℕ) (A B : Finset α) :
    (∑ x ∈ A ∪ B, f x) ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  let C := B \ A
  have hDisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    exact (Finset.mem_sdiff.mp hxC).2 hxA
  have hUnion : A ∪ C = A ∪ B := by
    ext x
    simp only [Finset.mem_union, C, Finset.mem_sdiff]
    tauto
  calc
    (∑ x ∈ A ∪ B, f x) = (∑ x ∈ A, f x) + ∑ x ∈ C, f x := by
      rw [← hUnion, Finset.sum_union hDisjoint]
    _ ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x :=
      Nat.add_le_add_left
        (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _

/-- The possible fourth distinct zero after fixing the first three entries of
a tolerance-one additive-energy quadruple. -/
noncomputable def resonantFourthZeroFiber
    (sigma T : ℝ) (rho₁ rho₂ rho₃ : ℂ) : Finset ℂ :=
  (zeroSet sigma T).filter fun rho₄ =>
    |rho₁.im + rho₂.im - rho₃.im - rho₄.im| ≤ 1

/-- The left integer index of the three-bin cover for a fourth-zero fiber. -/
noncomputable def resonantFourthZeroFloor
    (rho₁ rho₂ rho₃ : ℂ) : ℤ :=
  ⌊rho₁.im + rho₂.im - rho₃.im - 1⌋

theorem resonantFourthZeroFiber_subset_three_bins
    {sigma T : ℝ} {rho₁ rho₂ rho₃ : ℂ} :
    resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃ ⊆
      zeroLocalUnitBin sigma T (resonantFourthZeroFloor rho₁ rho₂ rho₃) ∪
        zeroLocalUnitBin sigma T (resonantFourthZeroFloor rho₁ rho₂ rho₃ + 1) ∪
          zeroLocalUnitBin sigma T (resonantFourthZeroFloor rho₁ rho₂ rho₃ + 2) := by
  classical
  intro rho₄ hrho₄
  rw [resonantFourthZeroFiber, Finset.mem_filter] at hrho₄
  rcases hrho₄ with ⟨hrho₄Set, hrho₄Res⟩
  have hLower :
      rho₁.im + rho₂.im - rho₃.im - 1 ≤ rho₄.im := by
    rw [abs_le] at hrho₄Res
    linarith
  have hUpper :
      rho₄.im ≤ rho₁.im + rho₂.im - rho₃.im + 1 := by
    rw [abs_le] at hrho₄Res
    linarith
  let z := resonantFourthZeroFloor rho₁ rho₂ rho₃
  have hzLower : (z : ℝ) ≤ rho₁.im + rho₂.im - rho₃.im - 1 := by
    exact Int.floor_le _
  have hzUpper :
      rho₁.im + rho₂.im - rho₃.im - 1 < (z : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hrhoLower : (z : ℝ) ≤ rho₄.im := hzLower.trans hLower
  have hrhoUpper : rho₄.im < (z : ℝ) + 3 := by linarith
  change rho₄ ∈ zeroLocalUnitBin sigma T z ∪
    zeroLocalUnitBin sigma T (z + 1) ∪ zeroLocalUnitBin sigma T (z + 2)
  simp only [Finset.mem_union]
  by_cases h₀ : rho₄.im < (z : ℝ) + 1
  · left
    left
    rw [zeroLocalUnitBin, Finset.mem_filter]
    exact ⟨hrho₄Set, hrhoLower, h₀⟩
  · by_cases h₁ : rho₄.im < (z : ℝ) + 2
    · left
      right
      rw [zeroLocalUnitBin, Finset.mem_filter]
      constructor
      · exact hrho₄Set
      constructor <;> push_cast <;> linarith
    · right
      rw [zeroLocalUnitBin, Finset.mem_filter]
      constructor
      · exact hrho₄Set
      constructor <;> push_cast <;> linarith

/-- The multiplicity mass of a fourth-zero fiber is bounded by three local
Jensen bins. -/
theorem resonantFourthZeroFiber_multiplicity_le
    {sigma T : ℝ} (rho₁ rho₂ rho₃ : ℂ)
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T) :
    ((∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
        zeroMultiplicity rho₄ : ℕ) : ℝ) ≤
      3 * globalLocalZeroLogConstant * Real.log T := by
  classical
  let z := resonantFourthZeroFloor rho₁ rho₂ rho₃
  let B₀ := zeroLocalUnitBin sigma T z
  let B₁ := zeroLocalUnitBin sigma T (z + 1)
  let B₂ := zeroLocalUnitBin sigma T (z + 2)
  have hSubset : resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃ ⊆
      B₀ ∪ B₁ ∪ B₂ := resonantFourthZeroFiber_subset_three_bins
  have hNat :
      (∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
          zeroMultiplicity rho₄) ≤
        (∑ rho₄ ∈ B₀, zeroMultiplicity rho₄) +
          (∑ rho₄ ∈ B₁, zeroMultiplicity rho₄) +
            ∑ rho₄ ∈ B₂, zeroMultiplicity rho₄ := by
    calc
      (∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
          zeroMultiplicity rho₄) ≤
          ∑ rho₄ ∈ B₀ ∪ B₁ ∪ B₂, zeroMultiplicity rho₄ :=
        Finset.sum_le_sum_of_subset hSubset
      _ ≤ (∑ rho₄ ∈ B₀, zeroMultiplicity rho₄) +
          (∑ rho₄ ∈ B₁, zeroMultiplicity rho₄) +
            ∑ rho₄ ∈ B₂, zeroMultiplicity rho₄ := by
        exact (finset_sum_union_le _ (B₀ ∪ B₁) B₂).trans
          (Nat.add_le_add_right (finset_sum_union_le _ B₀ B₁) _)
  have hReal :
      ((∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
          zeroMultiplicity rho₄ : ℕ) : ℝ) ≤
        ((∑ rho₄ ∈ B₀, zeroMultiplicity rho₄ : ℕ) : ℝ) +
          ((∑ rho₄ ∈ B₁, zeroMultiplicity rho₄ : ℕ) : ℝ) +
            ((∑ rho₄ ∈ B₂, zeroMultiplicity rho₄ : ℕ) : ℝ) := by
    exact_mod_cast hNat
  have h₀ := zeroLocalUnitBin_multiplicity_le_global_log sigma T z hsigma hT
  have h₁ := zeroLocalUnitBin_multiplicity_le_global_log sigma T (z + 1) hsigma hT
  have h₂ := zeroLocalUnitBin_multiplicity_le_global_log sigma T (z + 2) hsigma hT
  calc
    ((∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
        zeroMultiplicity rho₄ : ℕ) : ℝ) ≤
        ((∑ rho₄ ∈ B₀, zeroMultiplicity rho₄ : ℕ) : ℝ) +
          ((∑ rho₄ ∈ B₁, zeroMultiplicity rho₄ : ℕ) : ℝ) +
            ((∑ rho₄ ∈ B₂, zeroMultiplicity rho₄ : ℕ) : ℝ) := hReal
    _ ≤ globalLocalZeroLogConstant * Real.log T +
          globalLocalZeroLogConstant * Real.log T +
            globalLocalZeroLogConstant * Real.log T := by
      gcongr
    _ = 3 * globalLocalZeroLogConstant * Real.log T := by ring

/-- Exact Fubini expansion of `N*` into the fourth-zero fibers. -/
theorem zeroAdditiveEnergyCount_eq_sum_resonantFourthZeroFiber
    (sigma T : ℝ) :
    zeroAdditiveEnergyCount sigma T =
      ∑ rho₁ ∈ zeroSet sigma T,
        ∑ rho₂ ∈ zeroSet sigma T,
          ∑ rho₃ ∈ zeroSet sigma T,
            zeroMultiplicity rho₁ * zeroMultiplicity rho₂ *
              zeroMultiplicity rho₃ *
                ∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
                  zeroMultiplicity rho₄ := by
  classical
  simp only [zeroAdditiveEnergyCount, resonantZeroQuadruples,
    zeroQuadruples, zeroQuadrupleWeight, resonantFourthZeroFiber,
    Finset.sum_filter, Finset.sum_product]
  simp only [IsResonantZeroQuadruple]
  simp [Finset.mul_sum, mul_assoc]

/-- Exact finite form of the elementary comparison: the fourth-zero fiber
costs one local logarithm and the first three entries cost `N(sigma,T)^3`.
All zero counts retain analytic multiplicity. -/
theorem zeroAdditiveEnergyCount_le_three_local_mul_zeroCount_cube
    {sigma T : ℝ} (hsigma : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    (zeroAdditiveEnergyCount sigma T : ℝ) ≤
      (3 * globalLocalZeroLogConstant * Real.log T) *
        (zeroCount sigma T : ℝ) ^ 3 := by
  rw [zeroAdditiveEnergyCount_eq_sum_resonantFourthZeroFiber]
  push_cast
  calc
    ∑ rho₁ ∈ zeroSet sigma T,
        ∑ rho₂ ∈ zeroSet sigma T,
          ∑ rho₃ ∈ zeroSet sigma T,
            (zeroMultiplicity rho₁ : ℝ) * (zeroMultiplicity rho₂ : ℝ) *
              (zeroMultiplicity rho₃ : ℝ) *
                (∑ rho₄ ∈ resonantFourthZeroFiber sigma T rho₁ rho₂ rho₃,
                    (zeroMultiplicity rho₄ : ℝ)) ≤
      ∑ rho₁ ∈ zeroSet sigma T,
        ∑ rho₂ ∈ zeroSet sigma T,
          ∑ rho₃ ∈ zeroSet sigma T,
            (zeroMultiplicity rho₁ : ℝ) * (zeroMultiplicity rho₂ : ℝ) *
              (zeroMultiplicity rho₃ : ℝ) *
                (3 * globalLocalZeroLogConstant * Real.log T) := by
      apply Finset.sum_le_sum
      intro rho₁ _
      apply Finset.sum_le_sum
      intro rho₂ _
      apply Finset.sum_le_sum
      intro rho₃ _
      gcongr
      have hFiber :=
        resonantFourthZeroFiber_multiplicity_le rho₁ rho₂ rho₃ hsigma hT
      push_cast at hFiber
      exact hFiber
    _ = (3 * globalLocalZeroLogConstant * Real.log T) *
        (zeroCount sigma T : ℝ) ^ 3 := by
      rw [zeroCount_eq_weighted_sum]
      push_cast
      simp_rw [← Finset.sum_mul]
      rw [pow_three]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho₁ _
      apply Finset.sum_congr rfl
      intro rho₂ _
      apply Finset.sum_congr rfl
      intro rho₃ _
      ring

/-- Source-level envelope comparison `A*(sigma) <= 3 A(sigma)`.  The one
local logarithm is absorbed by half of the requested epsilon, while the
ordinary density estimate is invoked with epsilon divided by six before
cubing. -/
theorem zeroAdditiveEnergyEnvelope_three_mul_of_zeroDensityEnvelope
    {sigma a : ℝ} (hsigma : 0 ≤ sigma)
    (hDensity : ZeroDensityEnvelope sigma a) :
    ZeroAdditiveEnergyEnvelope sigma (3 * a) := by
  unfold ZeroDensityEnvelope EpsilonExponentBound at hDensity
  unfold ZeroAdditiveEnergyEnvelope EpsilonExponentBound
  intro eps heps
  have hepsHalf : 0 < eps / 2 := by positivity
  have hepsSixth : 0 < eps / 6 := by positivity
  have hLog :
      (fun T : ℝ => |Real.log T|) =O[atTop]
        (fun T : ℝ => T ^ (eps / 2)) := by
    simpa only [Real.norm_eq_abs] using
      (isLittleO_log_rpow_atTop hepsHalf).isBigO.norm_left
  have hDensityCube := (hDensity (eps / 6) hepsSixth).pow 3
  have hProduct :
      (fun T : ℝ => |Real.log T| * |(zeroCount sigma T : ℝ)| ^ 3) =O[atTop]
        (fun T : ℝ => T ^ (eps / 2) *
          (T ^ (eps / 6) * |T ^ (a * (1 - sigma))|) ^ 3) :=
    hLog.mul hDensityCube
  have hProductTarget :
      (fun T : ℝ => |Real.log T| * |(zeroCount sigma T : ℝ)| ^ 3) =O[atTop]
        (fun T : ℝ => T ^ eps * |T ^ ((3 * a) * (1 - sigma))|) := by
    refine hProduct.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [abs_of_nonneg (Real.rpow_nonneg hT.le _),
      abs_of_nonneg (Real.rpow_nonneg hT.le _)]
    calc
      T ^ (eps / 2) * (T ^ (eps / 6) * T ^ (a * (1 - sigma))) ^ 3 =
          T ^ (eps / 2 + 3 * (eps / 6 + a * (1 - sigma))) := by
        rw [← Real.rpow_add hT, ← Real.rpow_mul_natCast hT.le]
        rw [← Real.rpow_add hT]
        congr 1
        ring
      _ = T ^ eps * T ^ ((3 * a) * (1 - sigma)) := by
        rw [← Real.rpow_add hT]
        congr 1
        ring
  have hFinite :
      (fun T : ℝ => |(zeroAdditiveEnergyCount sigma T : ℝ)|) =O[atTop]
        (fun T : ℝ => |Real.log T| * |(zeroCount sigma T : ℝ)| ^ 3) := by
    apply IsBigO.of_bound (3 * globalLocalZeroLogConstant)
    filter_upwards [eventually_ge_atTop (max (Real.exp 2) 8)] with T hT
    have hLogNonneg : 0 ≤ Real.log T := by
      apply Real.log_nonneg
      exact le_trans (by norm_num : (1 : ℝ) ≤ 8) (le_trans (le_max_right _ _) hT)
    have hCountNonneg : 0 ≤ (zeroCount sigma T : ℝ) := by positivity
    have hEnergyNonneg : 0 ≤ (zeroAdditiveEnergyCount sigma T : ℝ) := by positivity
    calc
      ‖|(zeroAdditiveEnergyCount sigma T : ℝ)|‖ =
          (zeroAdditiveEnergyCount sigma T : ℝ) := by
        rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hEnergyNonneg]
      _ ≤ (3 * globalLocalZeroLogConstant * Real.log T) *
          (zeroCount sigma T : ℝ) ^ 3 :=
        zeroAdditiveEnergyCount_le_three_local_mul_zeroCount_cube hsigma hT
      _ = (3 * globalLocalZeroLogConstant) *
          (|Real.log T| * |(zeroCount sigma T : ℝ)| ^ 3) := by
        rw [abs_of_nonneg hLogNonneg, abs_of_nonneg hCountNonneg]
        ring
      _ = (3 * globalLocalZeroLogConstant) *
          ‖|Real.log T| * |(zeroCount sigma T : ℝ)| ^ 3‖ := by
        rw [Real.norm_eq_abs]
        congr 1
        symm
        exact abs_of_nonneg
          (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
  exact hFinite.trans hProductTarget

/-- Extended-real formulation of the paper's elementary inequality
`A*(sigma) <= 3 A(sigma)` for every admissible ordinary envelope. -/
theorem zeroAdditiveEnergyExponent_le_three_mul_of_zeroDensityEnvelope
    {sigma a : ℝ} (hsigma : 0 ≤ sigma)
    (hDensity : ZeroDensityEnvelope sigma a) :
    zeroAdditiveEnergyExponent sigma ≤ ((3 * a : ℝ) : EReal) :=
  zeroAdditiveEnergyExponent_le
    (zeroAdditiveEnergyEnvelope_three_mul_of_zeroDensityEnvelope
      hsigma hDensity)

#print axioms resonantFourthZeroFiber_subset_three_bins
#print axioms resonantFourthZeroFiber_multiplicity_le
#print axioms zeroAdditiveEnergyCount_eq_sum_resonantFourthZeroFiber
#print axioms zeroAdditiveEnergyCount_le_three_local_mul_zeroCount_cube
#print axioms zeroAdditiveEnergyEnvelope_three_mul_of_zeroDensityEnvelope
#print axioms zeroAdditiveEnergyExponent_le_three_mul_of_zeroDensityEnvelope

end GafniTao
