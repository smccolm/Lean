import GafniTao.HeathBrownEP1LargeOrder
import GafniTao.HeathBrownEP1LargeSelection

/-!
# Uniform assembly of Heath--Brown EP1 for `tau ≥ 13/3`

Only finitely many derivative orders occur below the explicit cutoff
`13/3 + epsilon⁻¹`; their positive constants are dominated by a finite sum.
Above the cutoff, the elementary cardinality estimate is already at most the
EP1 target.  This makes the final constant independent of `tau`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownEP1LargeOrderConstant
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (k : ℕ) : ℝ :=
  if hk : 6 ≤ k then
    Classical.choose
      (norm_pintz2023ExponentialBlock_le_EP1_large_order
        k epsilon hk hepsilon)
  else 1

theorem heathBrownEP1LargeOrderConstant_pos
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (k : ℕ) :
    0 < heathBrownEP1LargeOrderConstant epsilon hepsilon k := by
  unfold heathBrownEP1LargeOrderConstant
  split_ifs with hk
  · exact (Classical.choose_spec
      (norm_pintz2023ExponentialBlock_le_EP1_large_order
        k epsilon hk hepsilon)).1
  · norm_num

theorem norm_pintz2023ExponentialBlock_le_EP1_large_orderConstant
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {k : ℕ} (hk : 6 ≤ k) :
    ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      heathBrownEP1StripLower k ≤ tau →
      tau ≤ heathBrownEP1StripUpper k →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        heathBrownEP1LargeOrderConstant epsilon hepsilon k *
          (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  unfold heathBrownEP1LargeOrderConstant
  rw [dif_pos hk]
  exact (Classical.choose_spec
    (norm_pintz2023ExponentialBlock_le_EP1_large_order
      k epsilon hk hepsilon)).2

/-- Uniform large-range estimate below the explicit triviality cutoff. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_large_compact
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      13 / 3 ≤ tau → tau ≤ 13 / 3 + epsilon⁻¹ →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  let K : ℕ := Nat.floor (13 / 3 + epsilon⁻¹) + 2
  let C : ℝ := 1 + ∑ k ∈ Finset.Icc 6 K,
    heathBrownEP1LargeOrderConstant epsilon hepsilon k
  have hsumNonneg :
      0 ≤ ∑ k ∈ Finset.Icc 6 K,
        heathBrownEP1LargeOrderConstant epsilon hepsilon k :=
    Finset.sum_nonneg (fun k _hk =>
      (heathBrownEP1LargeOrderConstant_pos epsilon hepsilon k).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  let k : ℕ := heathBrownEP1LargeOrder tau
  obtain ⟨hkSix, hkLower, hkUpper⟩ :=
    heathBrownEP1LargeOrder_mem_strip htauLow
  have hfloorMono : Nat.floor tau ≤ Nat.floor (13 / 3 + epsilon⁻¹) :=
    Nat.floor_mono htauHigh
  have hkBound : k ≤ K := by
    dsimp only [k, K, heathBrownEP1LargeOrder]
    split_ifs <;> omega
  have hkMem : k ∈ Finset.Icc 6 K := Finset.mem_Icc.mpr ⟨hkSix, hkBound⟩
  have htermLe :
      heathBrownEP1LargeOrderConstant epsilon hepsilon k ≤
        ∑ j ∈ Finset.Icc 6 K,
          heathBrownEP1LargeOrderConstant epsilon hepsilon j := by
    exact Finset.single_le_sum
      (fun j _hj =>
        (heathBrownEP1LargeOrderConstant_pos epsilon hepsilon j).le)
      hkMem
  have hraw :=
    norm_pintz2023ExponentialBlock_le_EP1_large_orderConstant
      epsilon hepsilon hkSix N R tau hN hNR hR hkLower hkUpper
  have hpowNonneg :
      0 ≤ (N : ℝ) ^ heathBrownEP1Target epsilon tau := by positivity
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        heathBrownEP1LargeOrderConstant epsilon hepsilon k *
          (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
    _ ≤ (∑ j ∈ Finset.Icc 6 K,
          heathBrownEP1LargeOrderConstant epsilon hepsilon j) *
          (N : ℝ) ^ heathBrownEP1Target epsilon tau :=
      mul_le_mul_of_nonneg_right htermLe hpowNonneg
    _ ≤ C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      dsimp only [C]
      linarith

/-- Beyond the explicit cutoff, the trivial length bound implies EP1. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_large_trivial
    {N R : ℕ} {tau epsilon : ℝ}
    (hN : 0 < N) (hR : R ≤ 2 * N) (hepsilon : 0 < epsilon)
    (htau : 13 / 3 + epsilon⁻¹ ≤ tau) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  have hinvPos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have htauPos : 0 < tau := by linarith
  have hInv : epsilon⁻¹ ≤ tau := by linarith
  have heTau : 1 ≤ epsilon * tau := by
    have hmul := mul_le_mul_of_nonneg_left hInv hepsilon.le
    calc
      1 = epsilon * epsilon⁻¹ := (mul_inv_cancel₀ hepsilon.ne').symm
      _ ≤ epsilon * tau := hmul
  have htauOne : 1 ≤ tau := by linarith
  have hsave : 49 / (80 * tau ^ 2) ≤ epsilon := by
    rw [div_le_iff₀ (by positivity : 0 < 80 * tau ^ 2)]
    have haux : 1 ≤ epsilon * tau ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr heTau)
        (sub_nonneg.mpr htauOne)]
    nlinarith
  have htarget : 1 ≤ heathBrownEP1Target epsilon tau := by
    unfold heathBrownEP1Target
    linarith
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow_of_exponent_le hNOne htarget
  have htrivial :
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤ (N : ℝ) := by
    rw [pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
      ((N : ℝ) ^ tau) hN]
    exact norm_fordShiftedExponentialSum_le_N hR 0 ((N : ℝ) ^ tau)
  exact htrivial.trans (by simpa only [Real.rpow_one] using hpow)

/-- Uniform EP1 estimate on the complete source range `tau ≥ 13/3`. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_large
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N → 13 / 3 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_large_compact epsilon hepsilon
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau
  by_cases hcut : tau ≤ 13 / 3 + epsilon⁻¹
  · exact (hcompact N R tau hN hNR hR htau hcut).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by positivity) _))
  · have htrivial := norm_pintz2023ExponentialBlock_le_EP1_large_trivial
      hN hR hepsilon (le_of_not_ge hcut)
    exact htrivial.trans
      (by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (le_max_right C₀ 1)
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) _)))

#print axioms norm_pintz2023ExponentialBlock_le_EP1_large_compact
#print axioms norm_pintz2023ExponentialBlock_le_EP1_large_trivial
#print axioms norm_pintz2023ExponentialBlock_le_EP1_large

end

end GafniTao
