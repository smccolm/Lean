import GafniTao.Pintz2023ShellLimit
import RiemannZeta.GuthMaynard.DyadicTransfer

/-!
# Pintz (2023): dyadic shells to the symmetric zero count

The source shell uses a strict lower ordinate cutoff.  A zero on the lower
endpoint of the positive slab is therefore assigned to the preceding shell.
This file proves that endpoint bridge explicitly and then applies the frozen
multiplicity-preserving dyadic transfer.
-/

open Asymptotics Filter
open scoped BigOperators Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A closed positive dyadic slab is contained in the union of its current
strict shell and the preceding strict shell.  The second summand is needed
only for a zero whose ordinate is exactly the shared endpoint. -/
theorem pintz2023_positive_slab_le_two_shells
    {eta T : ℝ} (hT : 0 < T) :
    zeroCountRect (1 - eta) 1 T (2 * T) ≤
      (∑ rho ∈ pintz2023DyadicHeightShell eta T,
        zeroMultiplicity rho) +
      ∑ rho ∈ pintz2023DyadicHeightShell eta (2 * T),
        zeroMultiplicity rho := by
  let R := zerosInRect (1 - eta) 1 T (2 * T)
  let S₁ := pintz2023DyadicHeightShell eta T
  let S₂ := pintz2023DyadicHeightShell eta (2 * T)
  have hsubset : R ⊆ S₁ ∪ S₂ := by
    intro rho hrho
    have hrhoData : rho ∈ ZeroRectangle (1 - eta) 1 T (2 * T) ∩
        {s | riemannZeta s = 0} := by
      simpa only [R, zerosInRect, Set.Finite.mem_toFinset] using hrho
    rcases hrhoData with ⟨hrect, hzero⟩
    rw [mem_ZeroRectangle] at hrect
    have himNonneg : 0 ≤ rho.im := hT.le.trans hrect.2.2.1
    have himAbs : |rho.im| = rho.im := abs_of_nonneg himNonneg
    by_cases hstrict : T < |rho.im|
    · apply Finset.mem_union_right
      change rho ∈ pintz2023DyadicHeightShell eta (2 * T)
      rw [pintz2023DyadicHeightShell, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · change rho ∈ zerosInRect (1 - eta) 1 (-(2 * T)) (2 * T)
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
          mem_ZeroRectangle]
        exact ⟨⟨hrect.1, hrect.2.1, by linarith, hrect.2.2.2⟩, hzero⟩
      · rw [show (2 * T) / 2 = T by ring]
        exact hstrict
    · apply Finset.mem_union_left
      change rho ∈ pintz2023DyadicHeightShell eta T
      rw [pintz2023DyadicHeightShell, Finset.mem_filter]
      have himUpper : rho.im ≤ T := by
        rw [← himAbs]
        exact le_of_not_gt hstrict
      have himEq : rho.im = T := le_antisymm himUpper hrect.2.2.1
      refine ⟨?_, ?_⟩
      · change rho ∈ zerosInRect (1 - eta) 1 (-T) T
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
          mem_ZeroRectangle]
        exact ⟨⟨hrect.1, hrect.2.1, by linarith, himUpper⟩, hzero⟩
      · rw [himAbs, himEq]
        linarith
  unfold zeroCountRect
  have hUnion :
      ∑ rho ∈ R, analyticVanishingOrder riemannZeta rho ≤
        ∑ rho ∈ S₁ ∪ S₂, analyticVanishingOrder riemannZeta rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro rho _ _
    exact Nat.zero_le _
  change (∑ rho ∈ R, zeroMultiplicity rho) ≤
    ∑ rho ∈ S₁ ∪ S₂, zeroMultiplicity rho at hUnion
  have hUnionIdentity :
      (∑ rho ∈ S₁ ∪ S₂, zeroMultiplicity rho) +
          ∑ rho ∈ S₁ ∩ S₂, zeroMultiplicity rho =
        (∑ rho ∈ S₁, zeroMultiplicity rho) +
          ∑ rho ∈ S₂, zeroMultiplicity rho :=
    Finset.sum_union_inter
  dsimp only [R, S₁, S₂] at hUnion hUnionIdentity ⊢
  exact hUnion.trans (by omega)

/-- Epsilon-exponent bounds are stable under the fixed dilation `T ↦ 2T`.
The dilation cost is retained as the explicit constant `2^(epsilon+a)`. -/
theorem EpsilonExponentBound.two_mul_arg
    {f : ℝ → ℝ} {a : ℝ} (h : EpsilonExponentBound f a) :
    EpsilonExponentBound (fun T => f (2 * T)) a := by
  unfold EpsilonExponentBound EpsilonPowerBound at h ⊢
  intro eps heps
  have H := (h eps heps).comp_tendsto
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  apply H.trans
  apply IsBigO.of_bound (2 ^ eps * |2 ^ a|)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  have hTNonneg : 0 ≤ T := hT.le
  change ‖(2 * T) ^ eps * |(2 * T) ^ a|‖ ≤
    2 ^ eps * |2 ^ a| * ‖T ^ eps * |T ^ a|‖
  rw [Real.mul_rpow hTwo hTNonneg, Real.mul_rpow hTwo hTNonneg]
  rw [abs_mul]
  have hTwoEps : 0 ≤ (2 : ℝ) ^ eps := Real.rpow_nonneg (by norm_num) _
  have hTEps : 0 ≤ T ^ eps := Real.rpow_nonneg hTNonneg _
  simp only [Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg hTwoEps, abs_of_nonneg hTEps]
  ring_nf
  exact le_rfl

theorem pintzTheoremOneCoefficient_pos
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    0 < pintzTheoremOneCoefficient eta k ell := by
  have hkDen : 0 < (k : ℝ) * (1 - ((k : ℝ) - 1) * eta) := by
    simpa [pintzKDenominator] using
      (pintzCell_k_base_denominator_pos hcell)
  have hkTerm : 0 < 4 / ((k : ℝ) * (1 - ((k : ℝ) - 1) * eta)) :=
    div_pos (by norm_num) hkDen
  unfold pintzTheoremOneCoefficient
  exact hkTerm.trans_le (le_max_right _ _)

/-- Pintz's exact near-one density exponent, obtained from the source shells
with analytic multiplicity and the frozen dyadic-to-symmetric transfer. -/
theorem pintz2023_nearOneDensity_native
    {eta : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hetaUpper : eta < 1 / 24) :
    EpsilonExponentBound
      (fun T => (zeroCount (1 - eta) T : ℝ))
      (eta * pintzTheoremOneCoefficient eta k ell) := by
  have hShell := pintz2023_dyadicHeightShell_native hcell hetaUpper
  have hShellTwo := hShell.two_mul_arg
  have hSum := hShell.add hShellTwo
  have hSlab : EpsilonExponentBound
      (fun T => (zeroCountRect (1 - eta) 1 T (2 * T) : ℝ))
      (eta * pintzTheoremOneCoefficient eta k ell) := by
    unfold EpsilonExponentBound EpsilonPowerBound at hSum ⊢
    intro eps heps
    have H := hSum eps heps
    obtain ⟨C, hC⟩ := H.bound
    apply IsBigO.of_bound C
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with T hCT hT
    have hPoint : (zeroCountRect (1 - eta) 1 T (2 * T) : ℝ) ≤
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ pintz2023DyadicHeightShell eta (2 * T),
          zeroMultiplicity rho : ℕ) : ℝ) := by
      exact_mod_cast pintz2023_positive_slab_le_two_shells (eta := eta) hT
    have hSumNonneg : 0 ≤
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ pintz2023DyadicHeightShell eta (2 * T),
          zeroMultiplicity rho : ℕ) : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hSumNonneg] at hCT
    rw [Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (show 0 ≤ (zeroCountRect (1 - eta) 1 T (2 * T) : ℝ) by
        positivity)]
    exact hPoint.trans hCT
  exact dyadicToGlobalZeroCount (1 - eta)
    (eta * pintzTheoremOneCoefficient eta k ell)
    (mul_nonneg (pintzCell_eta_pos hcell).le
      (pintzTheoremOneCoefficient_pos hcell).le) hSlab

#print axioms pintz2023_positive_slab_le_two_shells
#print axioms EpsilonExponentBound.two_mul_arg
#print axioms pintz2023_nearOneDensity_native

end

end GafniTao
