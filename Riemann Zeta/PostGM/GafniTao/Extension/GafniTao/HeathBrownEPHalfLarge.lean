import GafniTao.HeathBrownEPHalfFixed

/-!
# Uniform variable-order logarithmic derivative estimate

For `tau ≥ 4` the derivative order is `ceil tau + 1`.  On the bounded
nontrivial range we dominate the finitely many order-dependent constants by
their finite sum.  Beyond that range the elementary cardinality bound is
already stronger than the requested exponent.  Thus the final constant is
uniform in `tau`.
-/

namespace GafniTao

noncomputable section

/-- A fixed derivative order controls every `tau` for which it is the chosen
ceiling order. -/
theorem norm_pintz2023ExponentialBlock_le_half_large_order
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N → 4 ≤ tau →
      heathBrownHalfOrder tau = k →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      k (epsilon / 2) hk hepsilonHalf
      (fun tau : ℝ => 4 ≤ tau ∧ heathBrownHalfOrder tau = k)
      (heathBrownHalfTarget epsilon)
      (by
        intro tau htau
        have hsave := (heathBrown_half_large_first_second htau.1).1
        rw [htau.2] at hsave
        unfold heathBrownLogFirstExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := (heathBrown_half_large_first_second htau.1).2
        rw [htau.2] at hsave
        unfold heathBrownLogSecondExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := heathBrown_half_large_third htau.1
        rw [htau.2] at hsave
        unfold heathBrownLogThirdExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        linarith)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau hkTau
  exact hbound N R tau hN hNR hR ⟨htau, hkTau⟩

/-- Chosen positive constant for one derivative order.  For irrelevant
orders below three it is set to one; no theorem uses that branch. -/
noncomputable def heathBrownHalfLargeOrderConstant
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (k : ℕ) : ℝ :=
  if hk : 3 ≤ k then
    Classical.choose
      (norm_pintz2023ExponentialBlock_le_half_large_order
        k epsilon hk hepsilon)
  else 1

theorem heathBrownHalfLargeOrderConstant_pos
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (k : ℕ) :
    0 < heathBrownHalfLargeOrderConstant epsilon hepsilon k := by
  unfold heathBrownHalfLargeOrderConstant
  split_ifs with hk
  · exact (Classical.choose_spec
      (norm_pintz2023ExponentialBlock_le_half_large_order
        k epsilon hk hepsilon)).1
  · norm_num

theorem norm_pintz2023ExponentialBlock_le_half_large_orderConstant
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {k : ℕ} (hk : 3 ≤ k) :
    ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N → 4 ≤ tau →
      heathBrownHalfOrder tau = k →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        heathBrownHalfLargeOrderConstant epsilon hepsilon k *
          (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  unfold heathBrownHalfLargeOrderConstant
  rw [dif_pos hk]
  exact (Classical.choose_spec
    (norm_pintz2023ExponentialBlock_le_half_large_order
      k epsilon hk hepsilon)).2

/-- Uniform constant on `4 ≤ tau ≤ 4 + epsilon⁻¹`, obtained as an explicit
finite sum of all possible chosen-order constants. -/
theorem norm_pintz2023ExponentialBlock_le_half_large_compact
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      4 ≤ tau → tau ≤ 4 + epsilon⁻¹ →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  let K : ℕ := Nat.ceil (4 + epsilon⁻¹) + 1
  let C : ℝ := 1 + ∑ k ∈ Finset.Icc 3 K,
    heathBrownHalfLargeOrderConstant epsilon hepsilon k
  have hsumNonneg :
      0 ≤ ∑ k ∈ Finset.Icc 3 K,
        heathBrownHalfLargeOrderConstant epsilon hepsilon k :=
    Finset.sum_nonneg (fun k _hk =>
      (heathBrownHalfLargeOrderConstant_pos epsilon hepsilon k).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  let k : ℕ := heathBrownHalfOrder tau
  have hkFive : 5 ≤ k := by
    dsimp only [k]
    exact (heathBrownHalfOrder_bounds htauLow).1
  have hkUpper : k ≤ K := by
    dsimp only [k, K, heathBrownHalfOrder]
    have hceil := Nat.ceil_mono htauHigh
    omega
  have hkMem : k ∈ Finset.Icc 3 K := Finset.mem_Icc.mpr ⟨by omega, hkUpper⟩
  have htermLe :
      heathBrownHalfLargeOrderConstant epsilon hepsilon k ≤
        ∑ j ∈ Finset.Icc 3 K,
          heathBrownHalfLargeOrderConstant epsilon hepsilon j := by
    exact Finset.single_le_sum
      (fun j _hj =>
        (heathBrownHalfLargeOrderConstant_pos epsilon hepsilon j).le)
      hkMem
  have hraw :=
    norm_pintz2023ExponentialBlock_le_half_large_orderConstant
      epsilon hepsilon (show 3 ≤ k by omega)
      N R tau hN hNR hR htauLow rfl
  have hpowNonneg :
      0 ≤ (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by positivity
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        heathBrownHalfLargeOrderConstant epsilon hepsilon k *
          (N : ℝ) ^ heathBrownHalfTarget epsilon tau := hraw
    _ ≤ (∑ j ∈ Finset.Icc 3 K,
          heathBrownHalfLargeOrderConstant epsilon hepsilon j) *
          (N : ℝ) ^ heathBrownHalfTarget epsilon tau :=
      mul_le_mul_of_nonneg_right htermLe hpowNonneg
    _ ≤ C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      dsimp only [C]
      linarith

/-- Beyond the finite-order cutoff, the trivial cardinality estimate has
the desired exponent. -/
theorem norm_pintz2023ExponentialBlock_le_half_large_trivial
    {N R : ℕ} {tau epsilon : ℝ}
    (hN : 0 < N) (hR : R ≤ 2 * N) (hepsilon : 0 < epsilon)
    (htau : 4 + epsilon⁻¹ ≤ tau) :
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
      (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  have htauPos : 0 < tau := by
    have hinvPos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
    linarith
  have heTau : 1 ≤ epsilon * tau := by
    have hInv : epsilon⁻¹ ≤ tau := by linarith
    have := mul_le_mul_of_nonneg_left hInv hepsilon.le
    calc
      1 = epsilon * epsilon⁻¹ := (mul_inv_cancel₀ hepsilon.ne').symm
      _ ≤ epsilon * tau := this
  have hsave : 1 / (2 * tau ^ 2) ≤ epsilon := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * tau ^ 2)).2
    have htauFour : 4 ≤ tau := by
      have hinvPos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr heTau) (show 0 ≤ tau by positivity)]
  have htarget : 1 ≤ heathBrownHalfTarget epsilon tau := by
    unfold heathBrownHalfTarget
    linarith
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow_of_exponent_le hNOne htarget
  have htrivial :
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤ (N : ℝ) := by
    rw [pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
      ((N : ℝ) ^ tau) hN]
    exact norm_fordShiftedExponentialSum_le_N hR 0 ((N : ℝ) ^ tau)
  exact htrivial.trans (by simpa only [Real.rpow_one] using hpow)

/-- Uniform coefficient-one-half estimate over the entire large logarithmic
range. -/
theorem norm_pintz2023ExponentialBlock_le_half_large
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N → 4 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    norm_pintz2023ExponentialBlock_le_half_large_compact epsilon hepsilon
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau
  by_cases hcut : tau ≤ 4 + epsilon⁻¹
  · exact (hcompact N R tau hN hNR hR htau hcut).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by positivity) _))
  · have htrivial := norm_pintz2023ExponentialBlock_le_half_large_trivial
      hN hR hepsilon (le_of_not_ge hcut)
    exact htrivial.trans
      (by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (le_max_right C₀ 1)
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) _)))

#print axioms norm_pintz2023ExponentialBlock_le_half_large_order
#print axioms norm_pintz2023ExponentialBlock_le_half_large_compact
#print axioms norm_pintz2023ExponentialBlock_le_half_large_trivial
#print axioms norm_pintz2023ExponentialBlock_le_half_large

end

end GafniTao
