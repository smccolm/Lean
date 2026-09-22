import TaoTrudgianYang2025.ExponentPairCorrelationAllHeights

/-! Normalization of the actual compressed physical scales. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem compressedHeight_main_le
    {q p σ T N r : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p)
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hr : 0 < r) (hrN : r ≤ N/2) :
    ((σ*T*r/N)/(N-r))^q*(N-r)^p ≤
      (2*σ)^q*((T/N^2)^q*N^p*r^q) := by
  have hNr : 0 < N-r := by linarith
  have hdual : 0 < σ*T*r/N := by positivity
  have hratio : (σ*T*r/N)/(N-r) ≤ (2*σ)*(T/N^2)*r := by
    calc
      _ ≤ (σ*T*r/N)/(N/2) :=
        div_le_div_of_nonneg_left hdual.le (by positivity) (by linarith)
      _ = _ := by field_simp
  have hpow := Real.rpow_le_rpow (div_nonneg hdual.le hNr.le) hratio hq
  have hscale := Real.rpow_le_rpow hNr.le (show N-r ≤ N by linarith) hp
  calc
    _ ≤ ((2*σ)*(T/N^2)*r)^q*N^p :=
      mul_le_mul hpow hscale (Real.rpow_nonneg hNr.le _) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hr.le,
        Real.mul_rpow (by positivity) (by positivity)]
      ring

theorem compressedHeight_inverse_le
    {σ T N r : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hN : 0 < N) (hr : 0 < r) :
    (N-r)/(σ*T*r/N) ≤ (1/σ)*(N^2/(T*r)) := by
  have hdual : 0 < σ*T*r/N := by positivity
  calc
    _ ≤ N/(σ*T*r/N) := div_le_div_of_nonneg_right (by linarith) hdual.le
    _ = _ := by field_simp

theorem sourceShiftCorrelation_normalized_bound
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/2 ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N : ℝ) (a L r : ℕ),
          0 < T → 2 ≤ N → 0 < r → (r : ℝ) ≤ η₀*N →
          N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖sourceShiftCorrelation F T N a L r‖ ≤
            C*((T/N^2)^(k+ε)*N^(l+ε)*(r : ℝ)^(k+ε)+N^2/(T*r)) := by
  obtain ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,B,hB,hbound⟩ :=
    sourceShiftCorrelation_bound_allHeights hkl hσ hε
  let M := (2*σ)^(k+ε)
  let D := 1+M+1/σ
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hiσ : 0 < 1/σ := by positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hMD : M ≤ D := by dsimp [D]; linarith
  have hiD : 1/σ ≤ D := by dsimp [D]; linarith
  refine ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,B*D,by nlinarith,?_⟩
  intro F T N a L r hT hN hr hrN ha hb hF
  have hNpos : 0 < N := by linarith
  have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hhalf : (r : ℝ) ≤ N/2 := hrN.trans (by nlinarith)
  have hbnd := hbound F T N a L r hT hN hr hrN ha hb hF
  have hmain := compressedHeight_main_le
    (show 0 ≤ k+ε by linarith [hkl.inTriangle.1])
    (show 0 ≤ l+ε by linarith [hkl.inTriangle.2.2.1]) hσ hT hNpos hrpos hhalf
  have hinv := compressedHeight_inverse_le hσ hT hNpos hrpos
  have hx : 0 ≤ (T/N^2)^(k+ε)*N^(l+ε)*(r : ℝ)^(k+ε) := by positivity
  have hy : 0 ≤ N^2/(T*r) := by positivity
  calc
    _ ≤ B*(((σ*T*r/N)/(N-r))^(k+ε)*(N-r)^(l+ε)+(N-r)/(σ*T*r/N)) := hbnd
    _ ≤ B*(M*((T/N^2)^(k+ε)*N^(l+ε)*(r : ℝ)^(k+ε))+
        (1/σ)*(N^2/(T*r))) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain hinv) (zero_le_one.trans hB)
    _ ≤ B*(D*((T/N^2)^(k+ε)*N^(l+ε)*(r : ℝ)^(k+ε))+D*(N^2/(T*r))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hMD hx) (mul_le_mul_of_nonneg_right hiD hy))
        (zero_le_one.trans hB)
    _ = _ := by ring

end TaoTrudgianYang2025
