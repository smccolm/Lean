import TaoTrudgianYang2025.AtkinsonPhysicalLogs

/-!
# Exact cancellation of the physical cutoff scale

Ceiling rounding is inherited from the actual source cutoff theorem.
The three powers are simplified without weakening their physical scales.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem atkinsonPhysicalCutoff_le_natural {H G : ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hupper : G ≤ Real.sqrt (2*H))
    (hlog : 1 ≤ Real.log (2*H)) :
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤
      74*H*(Real.log (2*H))^2/G^2 := by
  exact (atkinsonSourceCutoff_le_natural (by linarith : 1 ≤ 2*H) hG hupper hlog).trans_eq
    (by ring)

theorem atkinsonPhysical_cutoff_scale_identity {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) (q : ℝ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^(q-1/2)*ℓ^(2*q)*G^(2-2*q) := by
  have hbase : (74*H*ℓ^2/G^2)^q =
      (74:ℝ)^q*H^q*ℓ^(2*q)/G^(2*q) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity : 0 ≤ 74*H) (sq_nonneg ℓ),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 74) hH.le,
      ← Real.rpow_natCast,← Real.rpow_mul hℓ.le,
      ← Real.rpow_natCast,← Real.rpow_mul hG.le]
    norm_num
  rw [hbase,Real.rpow_sub hH,Real.rpow_sub hG,Real.rpow_neg hH.le,Real.rpow_two]
  ring

theorem atkinsonPhysical_diagonal_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/2:ℝ) ≤
      5476*(H/G)*ℓ^3 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (3/2:ℝ)-1/2 = 1 by norm_num,
    show 2*(3/2:ℝ) = 3 by norm_num,show 2-2*(3/2:ℝ) = -1 by norm_num,
    Real.rpow_one,Real.rpow_neg_one,Real.rpow_ofNat]
  have hc : (74:ℝ)^(3/2:ℝ) ≤ 5476 := by
    calc
      _ ≤ (74:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _ ≤ 5476*H*ℓ^3*G⁻¹ := by gcongr
    _ = _ := by ring

theorem atkinsonPhysical_near_scale {H G ℓ : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 0 < ℓ) :
    (Real.sqrt H/G)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(1:ℝ)) =
      74*(H/G)*ℓ^2 := by
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ]
  norm_num only [show (1:ℝ)-1/2 = 1/2 by norm_num,
    show 2*(1:ℝ) = 2 by norm_num,show 2-2*(1:ℝ) = 0 by norm_num,
    Real.rpow_one,Real.rpow_zero,Real.rpow_two,mul_one]
  rw [← Real.sqrt_eq_rpow]
  calc
    _ = 74*(Real.sqrt H)^2/G*ℓ^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hH.le]; ring

theorem atkinsonPhysical_far_scale {H G ℓ L : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hℓ : 1 ≤ ℓ) :
    (H^(-(1/4:ℝ))*Real.sqrt L)*(G^2*H^(-(1/2:ℝ))*(74*H*ℓ^2/G^2)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*L)*ℓ^3 := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [atkinsonPhysical_cutoff_scale_identity hH hG hℓ0]
  norm_num only [show (3/4:ℝ)-1/2 = 1/4 by norm_num,
    show 2*(3/4:ℝ) = 3/2 by norm_num,show 2-2*(3/4:ℝ) = 1/2 by norm_num]
  have hh : H^(-(1/4:ℝ))*H^(1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hH]; norm_num
  have he : (H^(-(1/4:ℝ))*Real.sqrt L)*
      ((74:ℝ)^(3/4:ℝ)*H^(1/4:ℝ)*ℓ^(3/2:ℝ)*G^(1/2:ℝ)) =
      (74:ℝ)^(3/4:ℝ)*Real.sqrt (G*L)*ℓ^(3/2:ℝ) := by
    rw [Real.sqrt_mul hG.le,Real.sqrt_eq_rpow G]
    calc
      _ = (H^(-(1/4:ℝ))*H^(1/4:ℝ))*
        ((74:ℝ)^(3/4:ℝ)*(G^(1/2:ℝ)*Real.sqrt L)*ℓ^(3/2:ℝ)) := by ring
      _ = _ := by rw [hh,one_mul]
  rw [he]
  have hc : (74:ℝ)^(3/4:ℝ) ≤ 74 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 74) (by norm_num : (3/4:ℝ) ≤ 1)
  have hl : ℓ^(3/2:ℝ) ≤ ℓ^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le
      hℓ (by norm_num : (3/2:ℝ) ≤ 3)
  gcongr

end TaoTrudgianYang2025
