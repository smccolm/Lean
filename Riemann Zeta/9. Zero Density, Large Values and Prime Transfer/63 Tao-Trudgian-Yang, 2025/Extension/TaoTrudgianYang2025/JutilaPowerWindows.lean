import TaoTrudgianYang2025.JutilaSubdivision
import TaoTrudgianYang2025.PointMeanLemmaThreeEdges

/-!
# Physical power windows for Jutila subdivision

The local height is linked to N by L=N^ℓ. The source endpoint subtraction
is absorbed only after a proved positive gap between value exponents.
-/

open Filter

noncomputable section

namespace TaoTrudgianYang2025

theorem eventually_rpow_add_one_le_rpow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ N : ℝ in atTop, N^a+1 ≤ N^b := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (D := 2) hab,
    eventually_ge_atTop (1 : ℝ)] with N hN hN1
  have hone := Real.one_le_rpow hN1 ha
  linarith

/-- Exact powers of the source scale in the local three-term bound. -/
theorem jutila_local_power_identity (k : ℕ) {N : ℝ} (hN : 0 < N) (s ℓ : ℝ) :
    N^2/(N^s)^2+(N^ℓ)^k*N^(2*k)/(N^s)^(4*k)+N^ℓ*N^(6*k)/(N^s)^(8*k) =
      N^(2-2*s)+N^((k : ℝ)*ℓ+2*k-4*k*s)+N^(ℓ+6*k-8*k*s) := by
  have hpow (a : ℝ) (m : ℕ) : (N^a)^m = N^(a*(m : ℝ)) :=
    (Real.rpow_mul_natCast hN.le a m).symm
  rw [hpow, hpow, hpow, hpow]
  rw [← Real.rpow_natCast N (2*k), ← Real.rpow_natCast N (6*k),
    ← Real.rpow_two, ← Real.rpow_sub hN, ← Real.rpow_add hN,
    ← Real.rpow_sub hN, ← Real.rpow_add hN, ← Real.rpow_sub hN]
  push_cast
  have h1 : (2 : ℝ)-s*2 = 2-2*s := by ring
  have h2 : ℓ*(k : ℝ)+2*k-s*(4*k) = (k : ℝ)*ℓ+2*k-4*k*s := by ring
  have h3 : ℓ+6*(k : ℝ)-s*(8*k) = ℓ+6*k-8*k*s := by ring
  rw [h1, h2, h3]

/-- A single common exponent bounds all local terms when ℓ lies below
the two exact source optimization thresholds. -/
theorem jutila_local_power_terms_le (k : ℕ) {N σ δ ℓ : ℝ}
    (hk : 0 < k) (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hfirst : (k : ℝ)*ℓ+2*k-4*k*σ ≤ 2-2*σ)
    (hsecond : ℓ+6*k-8*k*σ ≤ 2-2*σ) :
    N^2/(N^(σ-2*δ))^2+
        (N^ℓ)^k*N^(2*k)/(N^(σ-2*δ))^(4*k)+
        N^ℓ*N^(6*k)/(N^(σ-2*δ))^(8*k) ≤
      3*N^(2-2*σ+16*k*δ) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [jutila_local_power_identity k hNp]
  have h1 : N^(2-2*(σ-2*δ)) ≤ N^(2-2*σ+16*k*δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have h2 : N^((k : ℝ)*ℓ+2*k-4*k*(σ-2*δ)) ≤ N^(2-2*σ+16*k*δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have h3 : N^(ℓ+6*k-8*k*(σ-2*δ)) ≤ N^(2-2*σ+16*k*δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  linarith

/-- The subdivision count retains its genuine gain T/N^ℓ. -/
theorem jutila_subdivision_power_factor {N T τ δ ℓ : ℝ}
    (hN : 1 ≤ N) (hT : T ≤ N^(τ+δ)) (hδ : 0 ≤ δ) :
    1+T/N^ℓ ≤ 2*N^(max 0 (τ-ℓ)+δ) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp : 0 < N^ℓ := Real.rpow_pos_of_pos hNp _
  have h1 : 1 ≤ N^(max 0 (τ-ℓ)+δ) :=
    Real.one_le_rpow hN (by linarith [le_max_left (0 : ℝ) (τ-ℓ)])
  have h2 : T/N^ℓ ≤ N^(max 0 (τ-ℓ)+δ) := by
    calc
      T/N^ℓ ≤ N^(τ+δ)/N^ℓ := div_le_div_of_nonneg_right hT hp.le
      _ = N^(τ+δ-ℓ) := (Real.rpow_sub hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN
        (by linarith [le_max_right (0 : ℝ) (τ-ℓ)])
  linarith

end TaoTrudgianYang2025
