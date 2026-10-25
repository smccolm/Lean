import Dubon2026.SourceModularCharTwoCensus
import Dubon2026.SourceModularCharTwoFourteen
import Dubon2026.SourceModularWildDerivativeOrders
import Dubon2026.SourceModularCoefficientJDegreeSums

/-! DUB-17/18 -> characteristic-two genus/Picard. The actual weighted
modular census and proved local differential orders give precisely the
finite contribution required by the existing wild genus criterion. The
order-twelve case uses the proved bound fourteen; no local bound is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2]

theorem coeff_char_two_weighted_local_bound (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K))
    (hv : v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3 ∨
      v.ord (jCoeff N K) = 4 ∨ v.ord (jCoeff N K) = 6 ∨ v.ord (jCoeff N K) = 12) :
    7 * v.ord (jCoeff N K) -
        3 * ((if v.ord (jCoeff N K) = 1 then 1 else 0) +
          3 * (if v.ord (jCoeff N K) = 3 then 1 else 0) +
          2 * (if v.ord (jCoeff N K) = 6 then 1 else 0)) -
        4 * ((if v.ord (jCoeff N K) = 1 then 1 else 0) +
          (if v.ord (jCoeff N K) = 4 then 1 else 0)) ≤
      6 * v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  rcases hv with h | h | h | h | h
  · have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    rw [h] at hd
    norm_num [h]
    omega
  · have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    rw [h] at hd
    norm_num [h]
    omega
  · have hd := coeff_place_four_le_D_j_of_char_two N K v h
    norm_num [h]
    omega
  · have hd := coeff_place_six_le_D_j_of_char_two N K v h
    norm_num [h]
    omega
  · have hd := coeff_place_fourteen_le_D_j_of_char_two N K hNK v h
    norm_num [h]
    omega

theorem coeff_char_two_differential_contribution (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    7 * (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ) - 4 * (nuThree N : ℤ) ≤
      6 * (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K))) := by
  classical
  obtain ⟨hsize, htwo, hthree⟩ := coeff_char_two_order_census N K hNK S hS
  have hdeg : (∑ v ∈ S, v.ord (jCoeff N K)) = (dedekindPsi N : ℤ) := by
    simpa only [map_zero, sub_zero] using sum_coeff_j_fiber_orders_finset N K hNK 0 S
      (fun v => by simpa only [map_zero, sub_zero] using hS v)
  have hs := Finset.sum_le_sum (s := S) fun v hv =>
    coeff_char_two_weighted_local_bound N K hNK v (hsize v hv)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, hdeg] at hs
  have h2 : ((S.filter fun v => v.ord (jCoeff N K) = 1).card : ℤ) +
      3 * ((S.filter fun v => v.ord (jCoeff N K) = 3).card : ℤ) +
      2 * ((S.filter fun v => v.ord (jCoeff N K) = 6).card : ℤ) = (nuTwo N : ℤ) := by
    exact_mod_cast htwo
  have h3 : ((S.filter fun v => v.ord (jCoeff N K) = 1).card : ℤ) +
      ((S.filter fun v => v.ord (jCoeff N K) = 4).card : ℤ) = (nuThree N : ℤ) := by
    exact_mod_cast hthree
  rwa [h2, h3] at hs

end
end Dubon2026.SourceFunctionField
