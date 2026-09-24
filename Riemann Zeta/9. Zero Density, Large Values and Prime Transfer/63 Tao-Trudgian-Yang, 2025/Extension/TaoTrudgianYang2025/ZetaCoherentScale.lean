import TaoTrudgianYang2025.ZetaCoherentLattice

/-! Integer support lengths and real height powers for genuine zeta patterns. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_coherentZetaPowerPattern (N : ℕ) (hN : 2 ≤ N)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hrange : σ+τ ≤ 1) :
    ∃ P : ZetaLargeValuePattern, P.N = (N : ℝ) ∧ P.T = (N : ℝ)^τ/8 ∧
      (1/4)*(N : ℝ)^σ ≤ P.V ∧ P.V ≤ (1/2)*(N : ℝ)^σ ∧
      (1/8)*(N : ℝ)^τ ≤ (P.ordinates.card : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hσ1 : σ ≤ 1 := by linarith
  let L := Nat.floor ((N : ℝ)^σ)
  have hx : 1 ≤ (N : ℝ)^σ := Real.one_le_rpow hN1 hσ
  have hL1 : 1 ≤ L := (Nat.one_le_floor_iff _).mpr hx
  have hLp : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
  have hLlo : (N : ℝ)^σ/2 ≤ (L : ℝ) := by
    have hlo : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hhi : (N : ℝ)^σ < (L : ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have hLhi : (L : ℝ) ≤ (N : ℝ)^σ := Nat.floor_le (zero_le_one.trans hx)
  have hLN : L ≤ N := by
    have hb : (L : ℝ) ≤ N := calc
      _ ≤ (N : ℝ)^σ := hLhi
      _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hσ1
      _ = N := Real.rpow_one _
    exact_mod_cast hb
  have hproduct : (N : ℝ)^τ*(L : ℝ) ≤ N := calc
    _ ≤ (N : ℝ)^τ*(N : ℝ)^σ :=
      mul_le_mul_of_nonneg_left hLhi (Real.rpow_nonneg hNp.le _)
    _ = (N : ℝ)^(τ+σ) := (Real.rpow_add hNp _ _).symm
    _ ≤ (N : ℝ)^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ = N := Real.rpow_one _
  have hh : 2*((N : ℝ)^τ/8) ≤ (N : ℝ)/(2*(L : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(L : ℝ))).mpr
    nlinarith [mul_nonneg (Real.rpow_nonneg hNp.le τ) hLr.le]
  obtain ⟨P,hscale,hT,hV,hcard⟩ := exists_coherentZetaLatticePattern N L
    (by omega) hLp hLN ((N : ℝ)^τ/8) (by positivity) hh
  refine ⟨P,hscale,hT,?_,?_,?_⟩
  · rw [hV]
    linarith
  · rw [hV]
    linarith
  · linarith

end TaoTrudgianYang2025

