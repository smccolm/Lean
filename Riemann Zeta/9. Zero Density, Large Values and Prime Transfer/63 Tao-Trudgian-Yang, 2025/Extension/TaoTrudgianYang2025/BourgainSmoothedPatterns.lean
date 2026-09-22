import TaoTrudgianYang2025.BourgainSmoothingErrors
import TaoTrudgianYang2025.JutilaSmoothedPatterns

/-!
# Actual source-pattern retained-zeta bounds after loss absorption

All constants and the smoothing exponent precede the actual pattern.
The physical range N ≤ T remains explicit. The zeta moment and its
integer smoothing radius are not replaced by a numerical estimate.
-/

open Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Including the retained moment's extra integration-length factor still
costs an arbitrarily small power of the physical height. -/
theorem bourgain_smoothing_coefficient_uniform
    (k : ℕ) {θ E F A C K L D : ℝ}
    (hθ : 0 < θ) (hθOne : θ ≤ 1)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
          (4*((heathBrownSmoothingHeight T θ : ℝ)+1)) *
          jutilaSmoothingCoefficient k T θ E F A C K L D θ θ ≤
            B*T^(((16*k : ℕ) : ℝ)*θ+4*θ) := by
  obtain ⟨B,T₀,hB,hT₀,hb⟩ := jutila_smoothing_coefficient_uniform k (C := C)
    hθ hθOne hE hF hA hK hL hD
  refine ⟨12*B,T₀,by positivity,hT₀,?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [hT₀.trans hT]
  have hTp : 0 < T := by linarith
  have hheight := heathBrownSmoothingHeight_le_two_rpow hT1 hθ.le
  have hpow := Real.one_le_rpow hT1 hθ.le
  have hh : 4*((heathBrownSmoothingHeight T θ : ℝ)+1) ≤ 12*T^θ := by linarith
  have hcoef : 0 ≤ ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
      jutilaSmoothingCoefficient k T θ E F A C K L D θ θ := by
    unfold jutilaSmoothingCoefficient jutilaMomentLoss
    positivity
  calc
    _ = (4*((heathBrownSmoothingHeight T θ : ℝ)+1)) *
        (((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) *
          jutilaSmoothingCoefficient k T θ E F A C K L D θ θ) := by ring
    _ ≤ (12*T^θ)*(B*T^(((16*k : ℕ) : ℝ)*θ+3*θ)) :=
      mul_le_mul hh (hb T hT) hcoef (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hTp]
      congr 2
      ring

/-- The complete actual-pattern powered Gram bound after reflection,
error control and loss absorption. Both witness bounds cost only T^ν.
The physical hypothesis N ≤ T is retained explicitly. -/
theorem bourgain_smoothed_pattern_retained (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ν : ℝ} (hν : 0 < ν) :
    ∃ θ B T₀ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ ν ∧ 0 < B ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        ∃ (W : Finset ℝ) (Q : ℕ),
          W ⊆ P.reflectedOrdinates ∧
          (P.ordinates.card : ℝ) ≤ B*P.T^ν*(W.card : ℝ) ∧
          0 < Q ∧ P.N/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ 2*P.N ∧
          IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          ((W.card : ℝ)*((P.V-1)/3)^2 ≤ 2*(Q : ℝ)^2 ∨
            (W.card : ℝ)^2*((P.V-1)/3)^(4*k) ≤
              B*P.T^ν*(2*(Q : ℝ))^(2*k)*bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W) := by
  let d : ℝ := 16*(k : ℝ)+5
  let θ : ℝ := min 1 (ν/d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; have hk0 := Nat.cast_nonneg (α := ℝ) k; linarith
  have hθ : 0 < θ := lt_min zero_lt_one (div_pos hν hd)
  have hθOne : θ ≤ 1 := min_le_left _ _
  have hbudget : d*θ ≤ ν := by
    have hh : θ ≤ ν/d := min_le_right _ _
    nlinarith [(le_div_iff₀ hd).mp hh]
  have hθν : θ ≤ ν := by nlinarith
  have hexp : ((16*k : ℕ) : ℝ)*θ+4*θ ≤ ν := by
    push_cast
    dsimp [d] at hbudget
    nlinarith
  let q := heathBrownReflectionDerivativeOrder 0 θ
  obtain ⟨E, F, A, C, K, L, D, hE, hF, hA, hC, hK, hL, hD, hp⟩ :=
    bourgain_physical_pattern_retained cutoff q k
      (heathBrownReflectionDerivativeOrder_two_le 0 θ) hk hθ
  obtain ⟨B₀, Tb, hB₀, hTb, hb⟩ :=
    bourgain_smoothing_coefficient_uniform k (C := C)
      hθ hθOne hE.le hF.le hA.le hK.le hL.le hD.le
  let B := max 108 B₀
  have hB : 0 < B := lt_of_lt_of_le hB₀ (le_max_right _ _)
  refine ⟨θ, B, Tb, hθ, hθOne, hθν, hB, hTb, ?_⟩
  intro P hN hV hT hNT
  have hT1 : 1 ≤ P.T := by linarith [hTb.trans hT]
  have hTp : 0 < P.T := by linarith
  let H := heathBrownSmoothingHeight P.T θ
  let δ : ℝ := 4*(H : ℝ)
  have hH : 0 < H := heathBrownSmoothingHeight_pos P.T θ
  have hδ : 4 ≤ δ := by
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    dsimp [δ]
    linarith
  obtain ⟨W, Q, hsub, hcard, hQ, hlow, hhigh, hsep, hbase, hg⟩ :=
    hp P δ hN hV hT1 hδ
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
    exact le_trans (by linarith : (2 : ℝ) ≤ δ) (hsep x hx y hy hxy)
  · rcases hg H hH (le_refl _) with hsmall | hlarge
    · exact Or.inl hsmall
    right
    have hQT : (Q : ℝ) ≤ 2*P.T := hhigh.trans (by linarith)
    have henv := bourgain_physical_envelope_smoothing_le k Q P.T W
      (E := E) (A := A) (C := C)
      hθ hθOne hT1 hQ hQT hF.le hA.le hK.le hL.le hD.le
    have hcoef := hb P.T hT
    have hcore : 0 ≤ bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W :=
      bourgainRetainedMomentCore_nonneg k Q hTp.le (Nat.cast_nonneg _) W
    have hcoeffinal :
        ((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
          (4*((H : ℝ)+1)) * jutilaSmoothingCoefficient k P.T θ E F A C K L D θ θ ≤ B*P.T^ν := by
      calc
        _ ≤ B₀*P.T^(((16*k : ℕ) : ℝ)*θ+4*θ) := hcoef
        _ ≤ B*P.T^ν := mul_le_mul (le_max_right 108 B₀)
          (Real.rpow_le_rpow_of_exponent_le hT1 hexp) (by positivity) hB.le
    calc
      _ ≤ (2*(Q : ℝ))^(2*k) *
          (((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
            bourgainPhysicalEnvelope q k Q H P.T W E F A C K L D θ) := hlarge
      _ ≤ (2*(Q : ℝ))^(2*k) *
          (((Nat.log 2 (Nat.floor P.T)+1 : ℕ) : ℝ) *
            ((4*((H : ℝ)+1))*jutilaSmoothingCoefficient k P.T θ E F A C K L D θ θ *
              bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W)) := by gcongr
      _ ≤ (2*(Q : ℝ))^(2*k)*(B*P.T^ν*bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W) := by
        rw [← mul_assoc _ _ (bourgainRetainedMomentCore k Q P.T (heathBrownSmoothingHeight P.T θ) W),
          ← mul_assoc _ _ (jutilaSmoothingCoefficient k P.T θ E F A C K L D θ θ)]
        gcongr
      _ = _ := by ring

end TaoTrudgianYang2025
