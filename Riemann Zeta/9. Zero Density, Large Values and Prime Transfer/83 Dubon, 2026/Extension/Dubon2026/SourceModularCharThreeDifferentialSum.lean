import Dubon2026.SourceModularCharThreeCensus
import Dubon2026.SourceModularCharThreeSeven
import Dubon2026.SourceModularWildDerivativeOrders
import Dubon2026.SourceModularCoefficientJDegreeSums

/-! The actual characteristic-three weighted differential contribution.
The exact modular census, local wild bounds and j-fiber degree are
derived inputs. This discharges the finite-sum hypothesis of the
DUB-17/18 wild genus criterion in characteristic three. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective KaehlerDifferential
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K] [CharP K 3]

theorem coeff_char_three_weighted_local_bound (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K))
    (hv : v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 2 ∨
      v.ord (jCoeff N K) = 3 ∨ v.ord (jCoeff N K) = 6) :
    7 * v.ord (jCoeff N K) -
        3 * (if v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3 then 1 else 0) -
        4 * (if v.ord (jCoeff N K) = 1 then 1 else 0) -
        8 * (if v.ord (jCoeff N K) = 2 then 1 else 0) ≤
      6 * v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  rcases hv with h | h | h | h
  · have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    rw [h] at hd
    norm_num [h]
    omega
  · have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    rw [h] at hd
    norm_num [h]
    omega
  · have hd := coeff_place_three_le_D_j_of_char_three N K v h
    norm_num [h]
    omega
  · have hd := coeff_place_seven_le_D_j_of_char_three N K hNK v h
    norm_num [h]
    omega

theorem coeff_char_three_differential_contribution (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoeff N K)) :
    7 * (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ) - 4 * (nuThree N : ℤ) ≤
      6 * (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K))) := by
  classical
  obtain ⟨hsize, hodd, hsmall⟩ := coeff_char_three_order_census N K hNK S hS
  have hdeg : (∑ v ∈ S, v.ord (jCoeff N K)) = (dedekindPsi N : ℤ) := by
    simpa only [map_zero, sub_zero] using sum_coeff_j_fiber_orders_finset N K hNK 0 S
      (fun v => by simpa only [map_zero, sub_zero] using hS v)
  have hs := Finset.sum_le_sum (s := S) fun v hv =>
    coeff_char_three_weighted_local_bound N K hNK v (hsize v hv)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, hdeg] at hs
  have ho : ((S.filter fun v => v.ord (jCoeff N K) = 1 ∨ v.ord (jCoeff N K) = 3).card : ℤ) =
      (nuTwo N : ℤ) := by exact_mod_cast hodd
  have hh : ((S.filter fun v => v.ord (jCoeff N K) = 1).card : ℤ) +
      2 * ((S.filter fun v => v.ord (jCoeff N K) = 2).card : ℤ) = (nuThree N : ℤ) := by
    exact_mod_cast hsmall
  rw [ho] at hs
  linarith

end
end Dubon2026.SourceFunctionField
