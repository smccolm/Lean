import TaoTrudgianYang2025.JutilaPowerWindows
import TaoTrudgianYang2025.ClassicalLargeValueRegions

/-!
# Uniform classical mean-square large-value bound

The exact finite Montgomery--Halasz--Huxley source estimate supplies its
mean-square branch. The actual height padding and endpoint loss are removed.
-/

open Filter

noncomputable section

namespace TaoTrudgianYang2025

theorem IsLargeValueBound.mono {σ τ ρ ρ' : ℝ}
    (h : IsLargeValueBound σ τ ρ) (hρ : ρ ≤ ρ') : IsLargeValueBound σ τ ρ' := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hp⟩ := h ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  exact (hp P hN hTl hTu hVl hVu).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)) (zero_le_one.trans hC))

/-- The source L² mean-value theorem in the uniform large-value interface. -/
theorem meanSquare_largeValueBound {σ τ : ℝ} (hσ : 0 < σ) :
    IsLargeValueBound σ τ (max (2-2*σ) (1+τ-2*σ)) := by
  intro ε hε
  let m : ℝ := max 1 τ
  have hm : 1 ≤ m := le_max_left _ _
  let δ : ℝ := min (σ/4) (min 1 (ε/40))
  let η : ℝ := ε/(8*(m+1))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδσ : δ ≤ σ/4 := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/40 := (min_le_right _ _).trans (min_le_right _ _)
  have hs : 0 ≤ σ-2*δ := by linarith
  obtain ⟨Nv, hNv⟩ := eventually_atTop.mp
    (eventually_rpow_add_one_le_rpow hs (by linarith : σ-2*δ < σ-δ))
  obtain ⟨C₀, hC₀, hp⟩ := classical_largeValuePattern_estimate η hη
  let C : ℝ := max 1 (max Nv (2*C₀))
  have hC : 1 ≤ C := le_max_left _ _
  have hCv : Nv ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCc : 2*C₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN _ hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN1 : 1 ≤ P.N := P.one_lt_N.le
  have hVlow : P.N^(σ-2*δ) ≤ P.V-1 := by
    have hh := (hNv P.N (hCv.trans hN)).trans hVl
    linarith
  have hV : 1 < P.V := by
    have hh := Real.rpow_pos_of_pos hNp (σ-2*δ)
    linarith
  let H := max P.N P.T
  have hH1 : 1 ≤ H := hN1.trans (le_max_left _ _)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hHu : H ≤ P.N^(m+δ) := by
    apply max_le
    · calc
        P.N = P.N^(1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    · exact hTu.trans (Real.rpow_le_rpow_of_exponent_le hN1
        (by dsimp [m]; linarith [le_max_right (1 : ℝ) τ]))
  have hRaw := hp P H hH1 (le_max_left _ _) (le_max_right _ _) hV
  have hMean : (P.ordinates.card : ℝ) ≤ C₀*H^η*
      (P.N^2/(P.V-1)^2+H*(P.N/(P.V-1)^2)) := by
    exact hRaw.trans (by gcongr; exact min_le_left _ _)
  let ρ := max (2-2*σ) (1+τ-2*σ)
  have hmρ : m+1-2*σ = ρ := by
    dsimp [m, ρ]
    by_cases ht : τ ≤ 1
    · rw [max_eq_left ht, max_eq_left (by linarith : 1+τ-2*σ ≤ 2-2*σ)]
      ring
    · rw [max_eq_right (by linarith : (1 : ℝ) ≤ τ),
        max_eq_right (by linarith : 2-2*σ ≤ 1+τ-2*σ)]
      ring
  have hA : P.N^2/(P.V-1)^2 ≤ P.N^(ρ+5*δ) := by
    calc
      _ ≤ P.N^2/(P.N^(σ-2*δ))^2 := by gcongr
      _ = P.N^(2-2*σ+4*δ) := by
        rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_two, ← Real.rpow_sub hNp]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1
        (by dsimp [ρ]; linarith [le_max_left (2-2*σ) (1+τ-2*σ)])
  have hB : H*(P.N/(P.V-1)^2) ≤ P.N^(ρ+5*δ) := by
    calc
      _ ≤ P.N^(m+δ)*(P.N/(P.N^(σ-2*δ))^2) := by gcongr
      _ = P.N^(m+1-2*σ+5*δ) := by
        rw [← Real.rpow_mul_natCast hNp.le]
        conv_lhs => rhs; lhs; rw [← Real.rpow_one P.N]
        rw [← Real.rpow_sub hNp, ← Real.rpow_add hNp]
        congr 1
        push_cast
        ring
      _ = _ := by rw [hmρ]
  have hpow : H^η ≤ P.N^((m+δ)*η) := by
    calc
      _ ≤ (P.N^(m+δ))^η := Real.rpow_le_rpow hHp.le hHu hη.le
      _ = _ := (Real.rpow_mul hNp.le _ _).symm
  have hηloss : (m+1)*η = ε/8 := by dsimp [η]; field_simp
  have hloss : (m+δ)*η+5*δ ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right (show m+δ ≤ m+1 by linarith) hη.le
    nlinarith
  calc
    _ ≤ C₀*H^η*(P.N^2/(P.V-1)^2+H*(P.N/(P.V-1)^2)) := hMean
    _ ≤ C₀*P.N^((m+δ)*η)*(P.N^(ρ+5*δ)+P.N^(ρ+5*δ)) := by gcongr
    _ = (2*C₀)*P.N^((m+δ)*η+(ρ+5*δ)) := by
      rw [show C₀*P.N^((m+δ)*η)*(P.N^(ρ+5*δ)+P.N^(ρ+5*δ)) =
        (2*C₀)*(P.N^((m+δ)*η)*P.N^(ρ+5*δ)) by ring, ← Real.rpow_add hNp]
    _ ≤ C*P.N^(ρ+ε) := mul_le_mul hCc
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity) (zero_le_one.trans hC)

end TaoTrudgianYang2025
