import TaoTrudgianYang2025.RobertSargosWeightedBoundary

/-! Exact separation of the diagonal, coordinate axes and nonzero shift rectangle. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_signed_shift_axes (F : ℤ → ℤ → ℝ) (Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, F q r) =
      F 0 0+(∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, F q 0)+
        (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, F 0 r)+
          ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
            ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, F q r := by
  have hq0 : (0:ℤ) ∈ Finset.Ioo (-(Q:ℤ)) Q := by
    simp only [Finset.mem_Ioo]
    constructor <;> omega
  have hr0 : (0:ℤ) ∈ Finset.Ioo (-(R:ℤ)) R := by
    simp only [Finset.mem_Ioo]
    constructor <;> omega
  have he (q : ℤ) : (∑ r ∈ Finset.Ioo (-(R:ℤ)) R, F q r) =
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, F q r)+F q 0 :=
    (Finset.sum_erase_add _ _ hr0).symm
  rw [← Finset.sum_erase_add (Finset.Ioo (-(Q:ℤ)) Q)
    (fun q => ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, F q r) hq0]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  ring

def robertSargosNonzeroShiftSum (f : ℝ → ℝ) (M H Q R : ℕ) : ℝ :=
  ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
    ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H q r).re

theorem robertSargos_weighted_zero_shift_decomposition
    (f : ℝ → ℝ) (M H Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H q r).re) =
    (robertSargosTrimmedCorrelation f M H 0 0).re+
      (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
        (1-|(q:ℝ)|/Q)*(robertSargosTrimmedCorrelation f M H q 0).re)+
      (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        (1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H 0 r).re)+
      robertSargosNonzeroShiftSum f M H Q R := by
  simpa only [robertSargosNonzeroShiftSum,Int.cast_zero,abs_zero,zero_div,
    sub_zero,mul_one,one_mul] using sum_signed_shift_axes
      (fun q r => (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
        (robertSargosTrimmedCorrelation f M H q r).re) Q R hQ hR

end TaoTrudgianYang2025
