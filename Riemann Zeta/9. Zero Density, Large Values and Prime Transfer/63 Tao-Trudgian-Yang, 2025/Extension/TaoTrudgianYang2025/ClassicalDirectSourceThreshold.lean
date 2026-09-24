import TaoTrudgianYang2025.ClassicalDirectSourceGeometry

/-!
# Normalization of the actual two-block direct-source threshold

The fixed Fourier mass and the global smooth-label count are absorbed
uniformly in both physical dyadic lengths. The source line remains an
explicit parameter and is not identified with the target zeta line.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalDirect_normalized_sourceThreshold_eq
    (A Q : ℕ) (s T u : ℝ) (hQ : 0 < Q) (hT : 0 < T) :
    (((3/4)*(T^(-u)/2))/(Nat.clog 2 A+1 : ℕ)) /
        (8*(Q : ℝ)^(-s)*finiteFourierMass (typeIInteriorLogProfileSchwartz s)) =
      (Q : ℝ)^s / ((64/3)*finiteFourierMass (typeIInteriorLogProfileSchwartz s)*
        (Nat.clog 2 A+1 : ℕ)*T^u) := by
  have hQPos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hL : (0 : ℝ) < (Nat.clog 2 A+1 : ℕ) := by positivity
  have hMass := finiteFourierMass_pos (typeIInteriorLogProfileSchwartz s)
  have hTpow := Real.rpow_pos_of_pos hT u
  have hQpow := Real.rpow_pos_of_pos hQPos s
  rw [Real.rpow_neg hT.le,Real.rpow_neg hQPos.le]
  field_simp
  ring

theorem eventually_classicalDirect_normalized_sourceThreshold_lower
    (s a ε u : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hε : 0 < ε)
    (hu : u ≤ a*ε/2) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N Q : ℕ,
      N ≤ Q → T^a ≤ (N : ℝ) →
      (N : ℝ)^(s-ε) ≤
        (((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ)) /
          (8*(Q : ℝ)^(-s)*finiteFourierMass (typeIInteriorLogProfileSchwartz s)) := by
  let K : ℝ := (64/3)*finiteFourierMass (typeIInteriorLogProfileSchwartz s)
  have hK : 0 < K := mul_pos (by norm_num) (finiteFourierMass_pos _)
  have hη : 0 < a*ε/2 := by positivity
  filter_upwards [eventually_const_mul_classicalTypeI_clog_le_rpow
    (2*K) (a*ε/2) (by positivity) hη,
    Filter.eventually_ge_atTop (8 : ℝ)] with T hLog hT
  intro N Q hNQ hScale
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hNPos : (0 : ℝ) < N := (Real.rpow_pos_of_pos hTPos a).trans_le hScale
  have hQPos : 0 < Q := by
    have hN : 0 < N := by exact_mod_cast hNPos
    exact hN.trans_le hNQ
  let A := ⌊sharpZetaCutoff T⌋₊
  let L : ℝ := (Nat.clog 2 A+1 : ℕ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 1 < A := by
    dsimp [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hClog : (1 : ℝ) ≤ Nat.clog 2 A := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
  have hLogBound : K*L ≤ T^(a*ε/2) := by
    change K*((Nat.clog 2 A+1 : ℕ) : ℝ) ≤ _
    push_cast
    calc
      K*((Nat.clog 2 A : ℝ)+1) ≤ K*((Nat.clog 2 A : ℝ)+(Nat.clog 2 A : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hClog) hK.le
      _ = (2*K)*(Nat.clog 2 A : ℝ) := by ring
      _ ≤ T^(a*ε/2) := hLog
  have hDenPos : 0 < K*L*T^u := by positivity
  have hDen : K*L*T^u ≤ (N : ℝ)^ε := by
    calc
      K*L*T^u ≤ T^(a*ε/2)*T^u :=
        mul_le_mul_of_nonneg_right hLogBound (Real.rpow_nonneg hTPos.le _)
      _ = T^(a*ε/2+u) := (Real.rpow_add hTPos _ _).symm
      _ ≤ T^(a*ε) := Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
      _ = (T^a)^ε := Real.rpow_mul hTPos.le _ _
      _ ≤ (N : ℝ)^ε := Real.rpow_le_rpow (Real.rpow_nonneg hTPos.le _) hScale hε.le
  rw [classicalDirect_normalized_sourceThreshold_eq _ Q s T u hQPos hTPos]
  calc
    (N : ℝ)^(s-ε) = (N : ℝ)^s/(N : ℝ)^ε := Real.rpow_sub hNPos _ _
    _ ≤ (N : ℝ)^s/(K*L*T^u) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNPos.le _) hDenPos hDen
    _ ≤ (Q : ℝ)^s/(K*L*T^u) :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow hNPos.le (by exact_mod_cast hNQ) hs) hDenPos.le
    _ = _ := rfl

end TaoTrudgianYang2025
