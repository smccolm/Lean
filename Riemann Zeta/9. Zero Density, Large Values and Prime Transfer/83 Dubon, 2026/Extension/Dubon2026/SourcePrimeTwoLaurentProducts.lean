import Dubon2026.SourcePrimeTwoLaurentNormalForms

/-! Finite Laurent coefficient comparison for the actual prime-two integral
modular polynomial. This identifies the explicit cubic used by the degree-two
quotient product, required for the actual cyclic-quotient root interpretation
and elliptic inertia census on the DUB-17 / DUB-18 good-reduction chain.
Adapted from the selected phi_eq_phiTwo proof, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the existing
coefficient-list operations; degree bounds come from actual Laurent poles,
without polynomial symmetry or abstract modular-polynomial data. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PowerSeries JCoeff
open Dubon2026.SourcePrimeTwoPolynomial
namespace PhiTwoCalc
theorem nf_AB : NF (qExpand ℚ 4 jq * jq) (-5) [1, 744, 196884, 21493760, 864300714, 20246409792, 333349122296] :=
  (nf_qExpand_four_jq.mul nf_jq).congr (by decide)
theorem nf_ACm : NF (qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq) (-5)
    [-1, 744, -196884, 21493760, -864300714, 20246409792, -333349122296] :=
  (nf_qExpand_four_jq.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_BCm : NF (jq * qTwist (-1 : ℚˣ) jq) (-2) [-1, 0, 159768, 0, -8509194516, 0, 151107477178368] :=
  (nf_jq.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_ABCm : NF (qExpand ℚ 4 jq * jq * qTwist (-1 : ℚˣ) jq) (-6)
    [-1, 0, 159768, 0, -8509195260, 0, 151107596045760] :=
  (nf_AB.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_J22 : NF (qExpand ℚ 2 jq * qExpand ℚ 2 jq) (-4) [1, 0, 1488, 0, 947304, 0, 335950912] :=
  (nf_qExpand_two_jq.mul nf_qExpand_two_jq).congr (by decide)
theorem nf_J23 : NF (qExpand ℚ 2 jq * qExpand ℚ 2 jq * qExpand ℚ 2 jq) (-6) [1, 0, 2232, 0, 2251260, 0, 1355202240] :=
  (nf_J22.mul nf_qExpand_two_jq).congr (by decide)


end PhiTwoCalc
end
end Dubon2026.SourceFunctionField
