import Tao2026.BurgessWeilPrimeKummerLiteralWeilOnly

/-!
# Amplification of eventual Kummer square-root bounds

An eventual power-sum bound with any fixed constant bounds every spectral
root. The exact literal Kummer power sums then give sharp bounds in all degrees.
-/

namespace Tao2026
open Finset Polynomial Filter
open scoped BigOperators Topology
noncomputable section

theorem complexMultiset_norm_le_one_of_eventually_bounded_powerSums
    (A : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ᶠ k : ℕ in atTop, ‖(A.map fun z => z ^ k).sum‖ ≤ M) :
    ∀ a ∈ A, ‖a‖ ≤ 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hp
  intro a ha
  by_contra hnot
  have ha1 : 1 < ‖a‖ := lt_of_not_ge hnot
  let K : NNReal := complexNewtonCauchyBound M A.card
  have hpowBound : ∀ n : ℕ, N ≤ n → 0 < n → ‖a‖ ^ n < (K : ℝ) := by
    intro n hnN hn
    let B : Multiset ℂ := A.map fun z => z ^ n
    let Q : Polynomial ℂ := (B.map fun z => Polynomial.X - Polynomial.C z).prod
    have hBcard : B.card = A.card := by simp [B]
    have hBpow : ∀ k : ℕ, 0 < k → ‖(B.map fun z => z ^ k).sum‖ ≤ M := by
      intro k hk
      change ‖((A.map fun z => z ^ n).map fun z => z ^ k).sum‖ ≤ _
      rw [Multiset.map_map]
      simpa [pow_mul] using hN (n * k) (hnN.trans (Nat.le_mul_of_pos_right n hk))
    have hc : Polynomial.cauchyBound Q ≤ K := by
      have h := cauchyBound_multiset_prod_le_complexNewtonCauchyBound B M hM hBpow
      simpa [K, hBcard, Q] using h
    have hroot : Q.IsRoot (a ^ n) := by
      apply (Polynomial.mem_roots (Polynomial.monic_multisetProd_X_sub_C B).ne_zero).mp
      change a ^ n ∈ (B.map fun z => Polynomial.X - Polynomial.C z).prod.roots
      rw [Polynomial.roots_multiset_prod_X_sub_C]
      exact Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    have hlt := hroot.norm_lt_cauchyBound (Polynomial.monic_multisetProd_X_sub_C B).ne_zero
    have hlt' : ‖a ^ n‖₊ < K := hlt.trans_le hc
    have hr : ‖a ^ n‖ < (K : ℝ) := by exact_mod_cast hlt'
    simpa [norm_pow] using hr
  have ht : Tendsto (fun n : ℕ => ‖a‖ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ha1
  have hev : ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ ‖a‖ ^ n := tendsto_atTop.1 ht (K : ℝ)
  obtain ⟨n, hnK, hnN, hnpos⟩ :=
    (hev.and ((eventually_ge_atTop N).and (eventually_gt_atTop 0))).exists
  exact (not_lt_of_ge hnK) (hpowBound n hnN hnpos)

theorem complexMultiset_norm_le_of_eventually_powerSum_bound
    (A : Multiset ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hp : ∀ᶠ n : ℕ in atTop, ‖(A.map fun z => z ^ n).sum‖ ≤ M * R ^ n) :
    ∀ a ∈ A, ‖a‖ ≤ R := by
  let B : Multiset ℂ := A.map fun a => a / (R : ℂ)
  have hB : ∀ᶠ n : ℕ in atTop, ‖(B.map fun a => a ^ n).sum‖ ≤ M := by
    filter_upwards [hp] with n hn
    change ‖((A.map fun a => a / (R : ℂ)).map fun a => a ^ n).sum‖ ≤ _
    rw [Multiset.map_map]
    simp only [Function.comp_apply, div_pow]
    rw [Multiset.sum_map_div, norm_div]
    rw [show ‖((R : ℂ) ^ n)‖ = R ^ n by simp [norm_pow, abs_of_pos hR]]
    exact (div_le_iff₀ (pow_pos hR n)).2 hn
  have hunit := complexMultiset_norm_le_one_of_eventually_bounded_powerSums B M hM hB
  intro a ha
  have hb := hunit (a / (R : ℂ)) (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)
  rw [norm_div, show ‖(R : ℂ)‖ = R by simp [abs_of_pos hR]] at hb
  exact (div_le_one hR).mp hb

theorem primeRootMultisetExtensionWeilBounds_of_eventually_norm_le
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (r₀ : ZMod p) (hr₀ : r₀ ∈ R) (hcount : R.count r₀ < orderOf χ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᶠ q : ℕ in atTop,
      ‖primeRootMultisetExtensionCorrelation p χ R q‖ ≤ M * Real.sqrt p ^ (q + 1)) :
    PrimeRootMultisetExtensionWeilBounds p χ R := by
  have hrec := primeRootMultisetNewtonPowerSum_characteristic_recurrence p χ R r₀ hr₀ hcount
  apply (primeRootMultisetCanonicalWeight_iff_extensionWeilBounds_of_recurrence p χ R hrec).1
  apply complexMultiset_norm_le_of_eventually_powerSum_bound _ _ M
    (Real.sqrt_pos.2 (by exact_mod_cast (NeZero.pos p))) hM
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  filter_upwards [eventually_ge_atTop (N + 1)] with d hd
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  rw [← primeRootMultisetNewtonPowerSum_eq_canonical p χ R r₀ hr₀ hcount,
    primeRootMultisetNewtonPowerSum, norm_neg]
  exact hN q (by omega)

end
end Tao2026
