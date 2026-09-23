import TaoTrudgianYang2025.SargosQuarticResidues

/-! Literal source prefixes and their exact finite Fourier indexing. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticSample {N : ℕ} [NeZero N] (z : ℤ → ℂ) (α γ : ℝ) (k : ZMod N) : ℂ :=
  z (sargosSourceLift k)*
    fordAdditiveCharacter ((sargosSourceLift k : ℝ)^2*α+(sargosSourceLift k : ℝ)^4*γ)

def sargosQuarticPrefix (N H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
    z n*fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ)

def sargosQuarticPrefixMaximum (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) : ℝ :=
  (Finset.range (N+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
    (fun H => ‖sargosQuarticPrefix N H z α γ‖)

theorem sargosFinitePrefix_eq_quartic {N H : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α γ : ℝ) (hH : H ≤ N) :
    sargosFinitePrefix (sargosQuarticSample (N := N) z α γ) H = sargosQuarticPrefix N H z α γ := by
  unfold sargosFinitePrefix sargosQuarticPrefix
  refine Finset.sum_bij (fun j _ => (N : ℤ)+j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    dsimp only
    rw [Finset.mem_Ioc]
    constructor <;> omega
  · intro j hj l hl he
    dsimp only at he
    omega
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 ≤ n-(N : ℤ)-1 := by omega
    have hc := Int.toNat_of_nonneg hn0
    refine ⟨(n-(N : ℤ)-1).toNat,Finset.mem_range.mpr (by omega), ?_⟩
    dsimp only
    omega
  · intro j hj
    have hjN : j < N := lt_of_lt_of_le (Finset.mem_range.mp hj) hH
    unfold sargosQuarticSample sargosSourceLift
    rw [ZMod.val_cast_of_lt hjN]

theorem sargosQuarticPrefixMaximum_eq_finite {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticPrefixMaximum N z α γ =
      sargosFinitePrefixMaximum (sargosQuarticSample (N := N) z α γ) := by
  unfold sargosQuarticPrefixMaximum sargosFinitePrefixMaximum
  apply Finset.sup'_congr _ rfl
  intro H hH
  rw [sargosFinitePrefix_eq_quartic z α γ
    (Nat.le_of_lt_succ (Finset.mem_range.mp hH))]

theorem sargosQuarticPrefixMaximum_pow_four_le {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α γ : ℝ) :
    (sargosQuarticPrefixMaximum N z α γ)^4 ≤
      sargosFourierFourthMajorant (sargosQuarticSample (N := N) z α γ) := by
  rw [sargosQuarticPrefixMaximum_eq_finite]
  exact sargosFinitePrefixMaximum_pow_four_le _

theorem sargosQuarticPrefix_full (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticPrefix N N z α γ = sargosQuarticSum N z α γ := by
  unfold sargosQuarticPrefix sargosQuarticSum sargosPlanarSum sargosSourceInterval
  congr 2
  omega

theorem sargosQuarticPrefix_zero (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticPrefix N 0 z α γ = 0 := by
  simp [sargosQuarticPrefix]

theorem continuous_sargosQuarticPrefixMaximum (N : ℕ) (z : ℤ → ℂ) :
    Continuous (fun p : ℝ × ℝ => sargosQuarticPrefixMaximum N z p.1 p.2) := by
  unfold sargosQuarticPrefixMaximum
  apply Continuous.finset_sup'_apply
  intro H hH
  unfold sargosQuarticPrefix fordAdditiveCharacter
  fun_prop

end TaoTrudgianYang2025
