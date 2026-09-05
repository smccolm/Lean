import GafniTao.Pintz2023HalaszEnergy

/-!
# Pintz (2023), equation (4.19): diagonal Gram estimate

The estimate is finite-cutoff and exact.  Its only logarithmic factor is the
harmonic sum; the later cutoff and epsilon ledger absorb that factor.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023HalaszFiniteGram
    (N M : ℕ) (eta etaJ etaK gamma delta : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M,
    ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
      (n : ℂ) ^
        (-(((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
          I * ((delta - gamma : ℝ) : ℂ)))

/-- The diagonal term in Pintz (4.19), with individual `etaJ ≤ eta`. -/
theorem norm_pintz2023HalaszFiniteGram_diagonal_le
    {N M : ℕ} {eta etaJ gamma : ℝ}
    (hN : 0 < N) (heta : 0 ≤ eta) (hetaJ : etaJ ≤ eta) :
    ‖pintz2023HalaszFiniteGram N M eta etaJ etaJ gamma gamma‖ ≤
      (M : ℝ) ^ (6 * eta) * (harmonic M : ℝ) := by
  unfold pintz2023HalaszFiniteGram
  simp only [sub_self, ofReal_zero, mul_zero, add_zero]
  calc
    ‖∑ n ∈ Finset.Icc 1 M,
        ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
          (n : ℂ) ^
            (-((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ))‖ ≤
      ∑ n ∈ Finset.Icc 1 M,
        ‖((pintz2023HalaszKernel N n : ℝ) : ℂ) *
          (n : ℂ) ^
            (-((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        (M : ℝ) ^ (6 * eta) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnNat : 0 < n :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnM : (n : ℝ) ≤ M := by
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      have hnReal : (0 : ℝ) < n := zero_lt_one.trans_le hnOne
      have hkernelPos := pintz2023HalaszKernel_pos hN hnNat
      have hkernelLe := pintz2023HalaszKernel_le_one (N := N) (n := n) hN
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hkernelPos]
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnReal]
      have hexponent :
          (-((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ)).re =
            -1 + 2 * etaJ + 4 * eta := by norm_num; ring
      rw [hexponent]
      have hexponentLe : -1 + 2 * etaJ + 4 * eta ≤ -1 + 6 * eta := by
        linarith
      have hrpowExponent :
          (n : ℝ) ^ (-1 + 2 * etaJ + 4 * eta) ≤
            (n : ℝ) ^ (-1 + 6 * eta) :=
        Real.rpow_le_rpow_of_exponent_le hnOne hexponentLe
      have hrpowM : (n : ℝ) ^ (6 * eta) ≤ (M : ℝ) ^ (6 * eta) :=
        Real.rpow_le_rpow hnReal.le hnM (by positivity)
      have hsplit :
          (n : ℝ) ^ (-1 + 6 * eta) =
            (n : ℝ) ^ (6 * eta) * (n : ℝ)⁻¹ := by
        rw [show -1 + 6 * eta = 6 * eta + (-1) by ring,
          Real.rpow_add hnReal, Real.rpow_neg_one]
      calc
        pintz2023HalaszKernel N n *
            (n : ℝ) ^ (-1 + 2 * etaJ + 4 * eta) ≤
          1 * (n : ℝ) ^ (-1 + 6 * eta) := by
            gcongr
        _ = (n : ℝ) ^ (6 * eta) * (n : ℝ)⁻¹ := by
          rw [one_mul, hsplit]
        _ ≤ (M : ℝ) ^ (6 * eta) * (n : ℝ)⁻¹ := by
          gcongr
    _ = (M : ℝ) ^ (6 * eta) * (harmonic M : ℝ) := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast
      congr 2

#print axioms norm_pintz2023HalaszFiniteGram_diagonal_le

end

end GafniTao
