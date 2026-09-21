import TaoTrudgianYang2025.JutilaSmoothingLosses

/-!
# Source-pattern Jutila bounds with arbitrarily small smoothing losses

All constants precede the actual pattern. The present theorem applies
when N ≤ T; the complementary height range and the final local/global
Jutila optimization remain separate obligations.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Native integer smoothing gives the explicit thinning cost. -/
theorem jutila_smoothing_thinning_le {θ T : ℝ}
    (hθ : 0 ≤ θ) (hT : 1 ≤ T) :
    (6 : ℝ)*(2*(Nat.ceil (4*(heathBrownSmoothingHeight T θ : ℝ)) : ℝ)+1) ≤
      108*T^θ := by
  let H := heathBrownSmoothingHeight T θ
  have hp : 0 < H := heathBrownSmoothingHeight_pos T θ
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hp
  have hH := heathBrownSmoothingHeight_le_two_rpow hT hθ
  have hceil : Nat.ceil (4*(H : ℝ)) = 4*H := by
    rw [show (4 : ℝ)*(H : ℝ) = ((4*H : ℕ) : ℝ) by push_cast; rfl, Nat.ceil_natCast]
  change (6 : ℝ)*(2*(Nat.ceil (4*(H : ℝ)) : ℝ)+1) ≤ _
  rw [hceil]
  push_cast
  dsimp [H] at hH1
  nlinarith

/-- The complete actual-pattern powered Gram bound after reflection,
error control and loss absorption. Both witness bounds cost only T^ν.
The physical hypothesis N ≤ T is retained explicitly. -/
theorem jutila_smoothed_pattern_bound (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          0 < Q ∧ P.N/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2*P.N ∧
          IsSeparated 1 W ∧ InBaseInterval P.T W ∧
          ((W.card : ℝ)*((P.V-1)/3)^2 ≤ 2*(Q : ℝ)^2 ∨
            (W.card : ℝ)^2*((P.V-1)/3)^(4*k) ≤
              B*P.T^ν*(2*(Q : ℝ))^(2*k)*jutilaMomentCore k Q P.T W) := by
  let d : ℝ := 16*(k : ℝ)+4
  let θ : ℝ := min 1 (ν/d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; have hk0 := Nat.cast_nonneg (α := ℝ) k; linarith
  have hθ : 0 < θ := lt_min zero_lt_one (div_pos hν hd)
  have hθOne : θ ≤ 1 := min_le_left _ _
  have hbudget : d*θ ≤ ν := by
    have hh : θ ≤ ν/d := min_le_right _ _
    nlinarith [(le_div_iff₀ hd).mp hh]
  have hθν : θ ≤ ν := by nlinarith
  have hexp : ((16*k : ℕ) : ℝ)*θ+3*θ ≤ ν := by
    push_cast
    dsimp [d] at hbudget
    nlinarith
  let q := heathBrownReflectionDerivativeOrder 0 θ
  obtain ⟨E, F, A, C, K, L, D, Ta, hE, hF, hA, hC, hK, hL, hD, hTa, hp⟩ :=
    jutila_physical_pattern_bound cutoff q k
      (heathBrownReflectionDerivativeOrder_two_le 0 θ) hk hθ hθ
  obtain ⟨B₀, Tb, hB₀, hTb, hb⟩ :=
    jutila_smoothing_coefficient_uniform k (C := C)
      hθ hθOne hE.le hF.le hA.le hK.le hL.le hD.le
  let B := max 108 B₀
  have hB : 0 < B := lt_of_lt_of_le hB₀ (le_max_right _ _)
  refine ⟨B, max Ta Tb, hB, hTb.trans (le_max_right _ _), ?_⟩
  intro P hN hV hT hNT
  have hT1 : 1 ≤ P.T := hTa.trans ((le_max_left _ _).trans hT)
  have hTp : 0 < P.T := by linarith
  let H := heathBrownSmoothingHeight P.T θ
  let δ : ℝ := 4*(H : ℝ)
  have hH : 0 < H := heathBrownSmoothingHeight_pos P.T θ
  have hδ : 4 ≤ δ := by
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    dsimp [δ]
    linarith
  obtain ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, hg⟩ :=
    hp P δ hN hV ((le_max_left _ _).trans hT) hδ
  refine ⟨W, Q, hsub, ?_, hQ, hlow, hhigh, ?_, hbase, ?_⟩
  · have hc : (P.ordinates.card : ℝ) ≤
        (6 : ℝ)*(2*(Nat.ceil δ : ℝ)+1)*(W.card : ℝ) := by exact_mod_cast hcard
    have hs := jutila_smoothing_thinning_le hθ.le hT1
    have hrpow := Real.rpow_le_rpow_of_exponent_le hT1 hθν
    have h108 : (108 : ℝ) ≤ B := le_max_left _ _
    calc
      _ ≤ (6 : ℝ)*(2*(Nat.ceil δ : ℝ)+1)*(W.card : ℝ) := hc
      _ ≤ 108*P.T^θ*(W.card : ℝ) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ B*P.T^ν*(W.card : ℝ) := by gcongr
  · intro x hx y hy hxy
    exact le_trans (by linarith : (1 : ℝ) ≤ δ) (hsep x hx y hy hxy)
  · rcases hg H hH (le_refl _) with hsmall | hlarge
    · exact Or.inl hsmall
    right
    have hQT : (Q : ℝ) ≤ 2*P.T := hhigh.trans (by linarith)
    have henv := jutila_physical_envelope_smoothing_le k Q P.T W
      (E := E) (A := A) (C := C) (ε := θ) (η := θ)
      hθ hθOne hT1 hQ hQT hF.le hK.le hL.le hD.le
    have hcoef := hb P.T ((le_max_right _ _).trans hT)
    have hcore : 0 ≤ jutilaMomentCore k Q P.T W := by
      unfold jutilaMomentCore
      positivity
    have hcoeffinal :
        ((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
          jutilaSmoothingCoefficient k P.T θ E F A C K L D θ θ ≤ B*P.T^ν := by
      calc
        _ ≤ B₀*P.T^(((16*k : ℕ) : ℝ)*θ+3*θ) := hcoef
        _ ≤ B*P.T^ν := mul_le_mul (le_max_right 108 B₀)
          (Real.rpow_le_rpow_of_exponent_le hT1 hexp) (by positivity) hB.le
    calc
      _ ≤ (2*(Q : ℝ))^(2*k) *
          (((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
            jutilaPhysicalEnvelope q k Q H P.T W E F A C K L D θ θ) := hlarge
      _ ≤ (2*(Q : ℝ))^(2*k) *
          (((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
            (jutilaSmoothingCoefficient k P.T θ E F A C K L D θ θ *
              jutilaMomentCore k Q P.T W)) := by gcongr
      _ ≤ (2*(Q : ℝ))^(2*k)*(B*P.T^ν*jutilaMomentCore k Q P.T W) := by
        rw [← mul_assoc _ _ (jutilaMomentCore k Q P.T W)]
        gcongr
      _ = _ := by ring

end TaoTrudgianYang2025
