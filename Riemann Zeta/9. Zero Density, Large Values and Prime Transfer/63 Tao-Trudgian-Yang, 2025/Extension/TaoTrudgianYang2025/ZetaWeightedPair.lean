import TaoTrudgianYang2025.ZetaLogarithmicPair
import GuthMaynard.WeylZeta

/-! Finite Abel summation with the literal n^(-sigma-it) weights. -/

noncomputable section
open Expdb
namespace TaoTrudgianYang2025

theorem cpow_neg_eq_rpow_smul {n : ℕ} (hn : 0 < n) (σ t : ℝ) :
    (n : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I)) =
      (n : ℝ)^(-σ) • (n : ℂ)^(-((t : ℂ)*Complex.I)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.real_smul,Complex.ofReal_cpow hnp.le,Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ hnz]
  congr 1
  push_cast
  ring

theorem norm_weighted_dirichlet_block_le {a M : ℕ} (ha : 0 < a)
    {σ t B : ℝ} (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hprefix : ∀ j : ℕ, j ≤ M →
      ‖∑ i ∈ Finset.range j,
        ((a+i : ℕ) : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤ B) :
    ‖∑ i ∈ Finset.range M,
      ((a+i : ℕ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))‖ ≤ (a : ℝ)^(-σ)*B := by
  by_cases hM : M = 0
  · subst M
    simp only [Finset.sum_range_zero,norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
  have hm : 0 < M := Nat.pos_of_ne_zero hM
  have he : (∑ i ∈ Finset.range M,
      ((a+i : ℕ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))) =
      ∑ i ∈ Finset.range M,
        ((a+i : ℕ) : ℝ)^(-σ) • ((a+i : ℕ) : ℂ)^(-((t : ℂ)*Complex.I)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact cpow_neg_eq_rpow_smul (by omega) σ t
  rw [he]
  have h := RiemannZeta.GuthMaynard.norm_weighted_sum_le_of_antitone
    (fun i => ((a+i : ℕ) : ℝ)^(-σ))
    (fun i => ((a+i : ℕ) : ℂ)^(-((t : ℂ)*Complex.I))) M B hm
    (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun i _ => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < a+i by omega))
      (by exact_mod_cast (show a+i ≤ a+(i+1) by omega)) (by linarith))
    hprefix
  simpa only [Nat.add_zero] using h

theorem ExponentPair.weighted_logarithmic_sum_bound {k l ε σ : ℝ}
    (h : ExponentPair k l) (hε : 0 < ε) (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (a M : ℕ),
      0 < t → 0 < a → M ≤ a →
      ‖∑ i ∈ Finset.range M,
        ((a+i : ℕ) : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))‖ ≤
        C*((a : ℝ)^(-σ)*
          ((t/a)^(k+ε)*(a : ℝ)^(l+ε)+2*Real.pi*a/t)) := by
  obtain ⟨C,hC,hbound⟩ := h.logarithmic_sum_bound hε
  refine ⟨C,hC,?_⟩
  intro t a M ht ha hM
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hone : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hB : 0 ≤ C*((t/a)^(k+ε)*(a : ℝ)^(l+ε)+2*Real.pi*a/t) := by positivity
  have hh := norm_weighted_dirichlet_block_le (M:=M) ha hσ hB (t:=t) (by
    intro j hj
    cases j with
    | zero => simpa only [Finset.sum_range_zero,norm_zero] using hB
    | succ j =>
      have he : (∑ n ∈ Finset.Icc a (a+j), (n : ℂ)^(-((t : ℂ)*Complex.I))) =
          ∑ i ∈ Finset.range (j+1), ((a+i : ℕ) : ℂ)^(-((t : ℂ)*Complex.I)) := by
        rw [RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range _ a (a+j) (by omega)]
        simp only [Nat.add_sub_cancel_left]
      rw [← he]
      exact hbound t a a (a+j) ht hone le_rfl
        (by exact_mod_cast (show a+j ≤ 2*a by omega)))
  convert hh using 1
  ring

theorem zeta_weighted_exponentPair_scale_identity {t N : ℝ}
    (ht : 0 < t) (hN : 0 < N) (k l ε : ℝ) :
    N^(-(l-k))*((t/N)^(k+ε)*N^(l+ε)) = t^(k+ε) := by
  have he : N^(l+ε) = N^(l-k)*N^(k+ε) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [Real.div_rpow ht.le hN.le,he,Real.rpow_neg hN.le]
  have h1 := (Real.rpow_pos_of_pos hN (l-k)).ne'
  have h2 := (Real.rpow_pos_of_pos hN (k+ε)).ne'
  field_simp [h1,h2]

/-- Exact critical weight sigma=l-k cancels the dyadic length. The
low-frequency remainder is uniformly bounded throughout a<=6t. -/
theorem ExponentPair.zeta_weighted_dyadic_bound {k l ε : ℝ}
    (h : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (a M : ℕ),
      1 ≤ t → 0 < a → (a : ℝ) ≤ 6*t → M ≤ a →
      ‖∑ i ∈ Finset.range M,
        ((a+i : ℕ) : ℂ)^(-(((l-k : ℝ) : ℂ)+(t : ℂ)*Complex.I))‖ ≤ C*t^(k+ε) := by
  have hσ : 0 ≤ l-k := by linarith [h.inTriangle.2.1,h.inTriangle.2.2.1]
  obtain ⟨B,hB,hbound⟩ := h.weighted_logarithmic_sum_bound hε hσ
  let C := B*(1+12*Real.pi)
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [Real.pi_pos]
  refine ⟨C,hC,?_⟩
  intro t a M ht ha hat hM
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hw : (a : ℝ)^(-(l-k)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
  have hr : 2*Real.pi*a/t ≤ 12*Real.pi := by
    apply (div_le_iff₀ htp).mpr
    nlinarith [Real.pi_pos]
  have hh := hbound t a M htp ha hM
  rw [mul_add,zeta_weighted_exponentPair_scale_identity htp hap] at hh
  have hu : 1 ≤ t^(k+ε) :=
    Real.one_le_rpow ht (by linarith [h.inTriangle.1])
  have hrem : (a : ℝ)^(-(l-k))*(2*Real.pi*a/t) ≤ 12*Real.pi := by
    exact (mul_le_mul_of_nonneg_right hw (by positivity)).trans (by simpa using hr)
  calc
    _ ≤ B*(t^(k+ε)+(a : ℝ)^(-(l-k))*(2*Real.pi*a/t)) := hh
    _ ≤ B*(t^(k+ε)+12*Real.pi*t^(k+ε)) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hB)
      nlinarith [Real.pi_pos]
    _ = C*t^(k+ε) := by dsimp [C]; ring

end TaoTrudgianYang2025
