import TaoTrudgianYang2025.ClassicalDirectSourceIndexed

/-!
# Physical subpower radius for the direct source

A single derivative order is chosen before the source line and threshold
loss. The fixed profile seminorm and global logarithmic factor affect
only the eventual height threshold, not that order.
-/

noncomputable section
open scoped FourierTransform
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirectFourier_source_base_le
    (Q A k : ℕ) (s u T : ℝ) (hQ : 1 ≤ Q) (hQT : (Q : ℝ) ≤ T)
    (hs : 0 ≤ s) (hk : 1 < k) :
    let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
    1 + 4*((Q : ℝ)^(-s)*(Finset.Ioc (Q/2) (2*Q)).card)*
      SchwartzMap.seminorm ℝ k 0 (𝓕 (typeIInteriorLogProfileSchwartz s)) /
      (((k : ℝ)-1)*V) ≤
    1 + ((64/3)*SchwartzMap.seminorm ℝ k 0
      (𝓕 (typeIInteriorLogProfileSchwartz s))/((k : ℝ)-1))*
      (Nat.clog 2 A+1 : ℕ)*T^(u+1) := by
  dsimp only
  let c := (Q : ℝ)^(-s)
  let C := SchwartzMap.seminorm ℝ k 0 (𝓕 (typeIInteriorLogProfileSchwartz s))
  let q := (k : ℝ)-1
  let L : ℝ := (Nat.clog 2 A+1 : ℕ)
  let V := ((3/4)*(T^(-u)/2))/L
  have hQReal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hT : 0 < T := (zero_lt_one.trans_le hQReal).trans_le hQT
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg Q) _
  have hcOne : c ≤ 1 := by
    calc
      c ≤ (Q : ℝ)^0 :=
        Real.rpow_le_rpow_of_exponent_le hQReal (by linarith)
      _ = 1 := Real.rpow_zero _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : 0 < q := by
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    dsimp [q]
    linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hCardNat : (Finset.Ioc (Q/2) (2*Q)).card ≤ 2*Q := by
    simp only [Nat.card_Ioc]
    omega
  have hCard : ((Finset.Ioc (Q/2) (2*Q)).card : ℝ) ≤ 2*T := by
    have hCast : ((Finset.Ioc (Q/2) (2*Q)).card : ℝ) ≤ 2*(Q : ℝ) := by
      exact_mod_cast hCardNat
    linarith
  have hProduct : c*(Finset.Ioc (Q/2) (2*Q)).card ≤ 2*T := by
    calc
      _ ≤ 1*(2*T) := mul_le_mul hcOne hCard (Nat.cast_nonneg _) (by norm_num)
      _ = _ := one_mul _
  change 1+4*(c*(Finset.Ioc (Q/2) (2*Q)).card)*C/(q*V) ≤
    1+((64/3)*C/q)*L*T^(u+1)
  apply add_le_add le_rfl
  calc
    4*(c*(Finset.Ioc (Q/2) (2*Q)).card)*C/(q*V) ≤
        4*(2*T)*C/(q*V) := by gcongr
    _ = ((64/3)*C/q)*L*T^(u+1) := by
      rw [Real.rpow_add hT,Real.rpow_one]
      dsimp [V]
      rw [Real.rpow_neg hT.le]
      field_simp
      ring

theorem exists_order_eventually_classicalDirectFourierRadius_le_rpow
    (d : ℝ) (hd : 0 < d) :
    ∃ k : ℕ, 1 < k ∧ ∀ s u : ℝ, 0 ≤ s → u ≤ 1 →
      ∀ᶠ T : ℝ in Filter.atTop, ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ T →
        let A := ⌊sharpZetaCutoff T⌋₊
        let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
        finiteFourierRadius (typeIInteriorLogProfileSchwartz s)
          (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V ≤ T^d := by
  obtain ⟨k,hk,horder⟩ := exists_classicalTypeIFourier_order 3 d hd
  have horderFour : 4 ≤ d*((k : ℝ)-1) := by linarith
  refine ⟨k,hk,?_⟩
  intro s u hs hu
  let C : ℝ := (64/3)*SchwartzMap.seminorm ℝ k 0
    (𝓕 (typeIInteriorLogProfileSchwartz s))/((k : ℝ)-1)
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow
    (2*C) 1 (by positivity) (by norm_num),
    Filter.eventually_ge_atTop (8 : ℝ)] with T hLog hT
  intro Q hQ hQT
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let V := ((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hA : 1 < A := by
    dsimp [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hClog : (1 : ℝ) ≤ Nat.clog 2 A := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
  have hLogBound : C*(Nat.clog 2 A+1 : ℕ) ≤ T := by
    have hNatCast : ((Nat.clog 2 A+1 : ℕ) : ℝ) = (Nat.clog 2 A : ℝ)+1 := by norm_num
    rw [hNatCast]
    have hLog' : (2*C)*(Nat.clog 2 A : ℝ) ≤ T := by
      simpa only [A,Real.rpow_one] using hLog
    calc
      C*((Nat.clog 2 A : ℝ)+1) ≤ C*((Nat.clog 2 A : ℝ)+(Nat.clog 2 A : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hClog) hC
      _ = (2*C)*(Nat.clog 2 A : ℝ) := by ring
      _ ≤ T := hLog'
  have hV : 0 < V := by dsimp [V]; positivity
  apply finiteFourierRadius_le_rpow_of_base_growth
    (typeIInteriorLogProfileSchwartz s) (Finset.Ioc (Q/2) (2*Q)) k
    ((Q : ℝ)^(-s)) V T 4 d (Real.rpow_nonneg (Nat.cast_nonneg Q) _) hV hk hTOne horderFour
  have hBase := classicalDirectFourier_source_base_le Q A k s u T hQ hQT hs hk
  calc
    _ ≤ 1+C*(Nat.clog 2 A+1 : ℕ)*T^(u+1) := hBase
    _ ≤ 1+T*T^(2 : ℝ) := by
      apply add_le_add le_rfl
      exact mul_le_mul hLogBound
        (Real.rpow_le_rpow_of_exponent_le hTOne (by linarith))
        (Real.rpow_nonneg hTPos.le _) hTPos.le
    _ ≤ T^(4 : ℝ) := by
      rw [Real.rpow_two,Real.rpow_ofNat]
      have hCube : 1 ≤ T^3 := one_le_pow₀ hTOne
      have hTimes := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ T)
        (by positivity : 0 ≤ T^3)
      nlinarith

end TaoTrudgianYang2025
