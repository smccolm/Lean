import TaoTrudgianYang2025.AtkinsonPairPowerAlgebra

/-! Physical cutoff cancellation for a general exponent pair. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem atkinsonPhysical_pair_scale_identity {H G ℓ L : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) (k l : ℝ) :
    (L^k*H^(-k/2))*
      (G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(l+1/2-k/2)) =
      (74:ℝ)^(l+1/2-k/2)*ℓ^(2*l+1-k)*
        (L^k*H^(l-k)*G^(1+k-2*l)) := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  have he : (-k/2)+(l+1/2-k/2-1/2) = l-k := by ring
  have hh : H^(-k/2)*H^(l+1/2-k/2-1/2) = H^(l-k) := by
    rw [← Real.rpow_add hH,he]
  have hℓe : 2*(l+1/2-k/2) = 2*l+1-k := by ring
  have hGe : 2-2*(l+1/2-k/2) = 1+k-2*l := by ring
  rw [hGe,hℓe]
  calc
    _ = (74:ℝ)^(l+1/2-k/2)*ℓ^(2*l+1-k)*
        (L^k*(H^(-k/2)*H^(l+1/2-k/2-1/2))*G^(1+k-2*l)) := by ring
    _ = _ := by rw [hh]

theorem atkinsonPhysical_pair_scale_le {H G ℓ L k l : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 1 ≤ ℓ) (hL : 0 ≤ L)
    (hpair : InExponentPairTriangle k l) :
    (L^k*H^(-k/2))*
      (G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(l+1/2-k/2)) ≤
      5476*ℓ^3*(L^k*H^(l-k)*G^(1+k-2*l)) := by
  rw [atkinsonPhysical_pair_scale_identity hH hG (by linarith)]
  have hp : l+1/2-k/2 ≤ 2 := by
    rcases hpair with ⟨hk,_,_,hl,_⟩
    linarith
  have hc : (74:ℝ)^(l+1/2-k/2) ≤ 5476 := by
    calc
      _ ≤ (74:ℝ)^(2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
      _ = _ := by norm_num
  have he : 2*l+1-k ≤ 3 := by
    rcases hpair with ⟨hk,_,_,hl,_⟩
    linarith
  have hlp : ℓ^(2*l+1-k) ≤ ℓ^3 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hℓ he
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hc hlp (by positivity) (by norm_num)

theorem atkinson_pair_harmonic_le_height_log {H G L : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hLH : L ≤ H)
    (hlog : 1 ≤ Real.log (2*H)) :
    (harmonic (Nat.ceil (L/G)) : ℝ) ≤ 2*Real.log (2*H) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hq : L/G ≤ H := (div_le_iff₀ hG0).2 (by nlinarith)
  have hm := atkinson_harmonic_mono (Nat.ceil_mono hq)
  have hc : (Nat.ceil H:ℝ) ≤ 2*H := by
    have hh := Nat.ceil_lt_add_one hH0.le
    linarith
  have hc0 : (0:ℝ) < Nat.ceil H := hH0.trans_le (Nat.le_ceil H)
  have hl := Real.log_le_log hc0 hc
  have hb := harmonic_le_one_add_log (Nat.ceil H)
  linarith

end TaoTrudgianYang2025
