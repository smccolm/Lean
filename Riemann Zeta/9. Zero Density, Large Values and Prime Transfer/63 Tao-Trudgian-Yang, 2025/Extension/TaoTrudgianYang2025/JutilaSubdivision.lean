import TaoTrudgianYang2025.LargeValueSubdivision
import TaoTrudgianYang2025.JutilaLocalUniform

/-!
# Subdivision of the actual local Jutila estimate

The original height is unrestricted. A chosen local height dominates N,
and every actual localized source pattern consumes the proved local bound.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual local Jutila estimate transferred to an arbitrary original
height. The local scale and absorption hypotheses remain explicit. -/
theorem jutila_subdivided_cardinality (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ L → P.N ≤ L →
        C*L^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*L^ε*(1+P.T/L)*
          (P.N^2/(P.V-1)^2 +
            L^k*P.N^(2*k)/(P.V-1)^(4*k) +
            L*P.N^(6*k)/(P.V-1)^(8*k)) := by
  obtain ⟨C, T₀, hC, hT₀, hp⟩ := jutila_local_cardinality_uniform cutoff k hk hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro P L hN hV hL hNL hvalue
  have hLp : 0 < L := by linarith [hT₀.trans hL]
  have hTp := P.T_pos
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let X := P.N^2/(P.V-1)^2 +
    L^k*P.N^(2*k)/(P.V-1)^(4*k) +
    L*P.N^(6*k)/(P.V-1)^(8*k)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hlocal (j : ℕ) : ((P.localized L hLp j).ordinates.card : ℝ) ≤ C*L^ε*X :=
    hp (P.localized L hLp j) hN hV hL hNL hvalue
  have hc := P.card_le_of_localized hLp (C*L^ε*X) (fun j _ => hlocal j)
  have hbins : ((Nat.floor (P.T/L)+1 : ℕ) : ℝ) ≤ 1+P.T/L := by
    have hf := Nat.floor_le (div_nonneg hTp.le hLp.le)
    push_cast
    linarith
  calc
    _ ≤ ((Nat.floor (P.T/L)+1 : ℕ) : ℝ)*(C*L^ε*X) := hc
    _ ≤ (1+P.T/L)*(C*L^ε*X) := mul_le_mul_of_nonneg_right hbins (by positivity)
    _ = _ := by dsimp [X]; ring

/-- Removing the abstract cutoff parameter uses the already constructed
smooth cutoff, not an additional analytic assumption. -/
theorem jutila_subdivided_cardinality_native
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ (P : LargeValuePattern) (L : ℝ),
        30 ≤ P.scale → 1 < P.V → T₀ ≤ L → P.N ≤ L →
        C*L^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*L^ε*(1+P.T/L)*
          (P.N^2/(P.V-1)^2 +
            L^k*P.N^(2*k)/(P.V-1)^(4*k) +
            L*P.N^(6*k)/(P.V-1)^(8*k)) :=
  jutila_subdivided_cardinality (Classical.choice exists_gmSmoothCutoff) k hk hε

end TaoTrudgianYang2025
