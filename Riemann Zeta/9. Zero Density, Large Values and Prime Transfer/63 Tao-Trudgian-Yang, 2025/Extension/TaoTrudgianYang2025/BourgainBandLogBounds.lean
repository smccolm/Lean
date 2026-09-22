import TaoTrudgianYang2025.BourgainSharedFloor

/-!
# Logarithmic bounds for the shared amplitude grid

A polynomial spatial radius and the common inverse-power floor give a
genuine logarithmic band count. All parameter dependencies are explicit.
-/

open Filter RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual spatial enlargement fits a common polynomial height cap. -/
theorem bourgain_shared_band_radius_le (P : LargeValuePattern) {τ ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ 1) (hT : P.T ≤ P.N^(τ+δ)) :
    P.T+P.N^(ε/8)+1 ≤ 3*P.N^(|τ|+ε+1) := by
  have hN1 := P.one_lt_N.le
  have ht : P.T ≤ P.N^(|τ|+ε+1) :=
    hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self τ]))
  have hh : P.N^(ε/8) ≤ P.N^(|τ|+ε+1) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg τ])
  have hone : 1 ≤ P.N^(|τ|+ε+1) := Real.one_le_rpow hN1 (by positivity)
  linarith

/-- A ceiling-logarithmic count on the fixed floor retains only a linear
logarithmic loss in N, even with the actual ceiling and terminal band. -/
theorem bourgainZetaBandCount_power_log_bound {B N U A u : ℝ}
    (hB : 0 < B) (hN : 1 ≤ N) (hU : 0 ≤ U) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hcap : U ≤ 3*N^u) :
    (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤
      2+(Real.log (4*B+1)+(u+A)*Real.log N)/Real.log 2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let M := Nat.ceil (B*(1+U)/(N^(-A)))
  have hX : 0 < B*(1+U)/(N^(-A)) := by positivity
  have hMpos : 0 < M := Nat.ceil_pos.mpr hX
  have hM : 1 ≤ M := hMpos
  have hMp : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hp : 1 ≤ N^(u+A) := Real.one_le_rpow hN (by positivity)
  have hpu : 1 ≤ N^u := Real.one_le_rpow hN hu
  have hinput : B*(1+U)/(N^(-A)) ≤ 4*B*N^(u+A) := by
    calc
      _ = B*(1+U)*N^A := by rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
      _ ≤ B*(4*N^u)*N^A := by gcongr; linarith
      _ = _ := by rw [Real.rpow_add hNp]; ring
  have hceil := Nat.ceil_lt_add_one hX.le
  have hbound : (M : ℝ) ≤ (4*B+1)*N^(u+A) := by
    dsimp only [M]
    nlinarith
  have hlog : Real.log (M : ℝ) ≤ Real.log (4*B+1)+(u+A)*Real.log N := by
    calc
      _ ≤ Real.log ((4*B+1)*N^(u+A)) := Real.log_le_log hMp hbound
      _ = _ := by
        rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hNp _).ne',
          Real.log_rpow hNp]
  have hc := heathBrown_natCast_clog_two_le_one_add_log M hM
  have hd := div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [bourgainZetaBandCount, Nat.cast_add, Nat.cast_one]
  change (Nat.clog 2 M : ℝ)+1 ≤ _
  linarith

/-- For fixed grid exponents the logarithmic band count costs an arbitrary
small positive power, with constants chosen before N and the radius. -/
theorem bourgainZetaBandCount_uniform_power {B A u η : ℝ}
    (hB : 0 < B) (hA : 0 ≤ A) (hu : 0 ≤ u) (hη : 0 < η) :
    ∃ C N₀ : ℝ, 1 ≤ C ∧ 2 ≤ N₀ ∧ ∀ N U : ℝ, N₀ ≤ N → 0 ≤ U → U ≤ 3*N^u →
      (bourgainZetaBandCount B U (N^(-A)) : ℝ) ≤ C*N^η := by
  obtain ⟨Nlog, hlog⟩ := eventually_atTop.mp (heathBrown_eventually_log_le_rpow η hη)
  let D := 2+(Real.log (4*B+1)+(u+A))/Real.log 2
  let C := max 1 D
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (4*B+1) := Real.log_nonneg (by linarith)
  have hD0 : 0 ≤ 2+Real.log (4*B+1)/Real.log 2 := by positivity
  have hE0 : 0 ≤ (u+A)/Real.log 2 := by positivity
  refine ⟨C, max 2 Nlog, le_max_left _ _, le_max_left _ _, ?_⟩
  intro N U hN hU hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hone : 1 ≤ N^η := Real.one_le_rpow hN1 hη.le
  have hl : Real.log N ≤ N^η := hlog N ((le_max_right _ _).trans hN)
  calc
    _ ≤ 2+(Real.log (4*B+1)+(u+A)*Real.log N)/Real.log 2 :=
      bourgainZetaBandCount_power_log_bound hB hN1 hU hA hu hcap
    _ = (2+Real.log (4*B+1)/Real.log 2)+((u+A)/Real.log 2)*Real.log N := by ring
    _ ≤ (2+Real.log (4*B+1)/Real.log 2)*N^η+((u+A)/Real.log 2)*N^η := by
      exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hl hE0)
    _ = D*N^η := by dsimp only [D]; ring
    _ ≤ C*N^η := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (by linarith) _)

end TaoTrudgianYang2025
