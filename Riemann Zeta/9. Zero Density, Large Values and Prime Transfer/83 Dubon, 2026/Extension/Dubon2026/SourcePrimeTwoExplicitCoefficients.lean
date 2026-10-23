import Dubon2026.SourcePrimeTwoLaurentProducts
import Dubon2026.SourceOriginalFieldFinite

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
theorem eval₂_qExpand_two_jq (P : Polynomial ℤ) :
    Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℚ)) (qExpand ℚ 2 jq) P = qExpand ℚ 2 (evalAtJ P) := by
  have : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (qExpand ℚ 2 jq))
      = (qExpand ℚ 2).comp evalAtJ := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply, evalAtJ_X]
  exact congrArg (fun f => f P) (congrArg DFunLike.coe this)

theorem phiTwo_coeff :
    phiTwo.coeff 0 = phiTwoC0 ∧ phiTwo.coeff 1 = phiTwoC1 ∧ phiTwo.coeff 2 = phiTwoC2 ∧ phiTwo.coeff 3 = 1 ∧
      ∀ n, 4 ≤ n → phiTwo.coeff n = 0 := by
  have hdeg : phiTwo.natDegree ≤ 3 := by unfold phiTwo; compute_degree!
  refine ⟨?_, ?_, ?_, ?_, fun n hn => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩ <;>
    simp [phiTwo, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]

theorem natDegree_phiTwoC : phiTwoC0.natDegree ≤ 3 ∧ phiTwoC1.natDegree ≤ 3 ∧ phiTwoC2.natDegree ≤ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold phiTwoC0; compute_degree!
  · unfold phiTwoC1; compute_degree!
  · unfold phiTwoC2; compute_degree!

theorem qExpand_evalAtJ_phiTwoC :
    qExpand ℚ 2 (evalAtJ phiTwoC2)
      = -(qExpand ℚ 2 jq * qExpand ℚ 2 jq) + HahnSeries.C (1488 : ℚ) * qExpand ℚ 2 jq - HahnSeries.C (162000 : ℚ) ∧
    qExpand ℚ 2 (evalAtJ phiTwoC1)
      = HahnSeries.C (1488 : ℚ) * (qExpand ℚ 2 jq * qExpand ℚ 2 jq) + HahnSeries.C (40773375 : ℚ) * qExpand ℚ 2 jq
        + HahnSeries.C (8748000000 : ℚ) ∧
    qExpand ℚ 2 (evalAtJ phiTwoC0)
      = qExpand ℚ 2 jq * qExpand ℚ 2 jq * qExpand ℚ 2 jq - HahnSeries.C (162000 : ℚ) * (qExpand ℚ 2 jq * qExpand ℚ 2 jq)
        + HahnSeries.C (8748000000 : ℚ) * qExpand ℚ 2 jq - HahnSeries.C (157464000000000 : ℚ) := by
  simp only [map_ofNat]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rw [← eval₂_qExpand_two_jq]
    simp only [phiTwoC2, phiTwoC1, phiTwoC0, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_neg]
    ring

theorem coeff_C_mul' (r : ℚ) (x : LaurentSeries ℚ) (m : ℤ) : (HahnSeries.C r * x).coeff m = r * x.coeff m := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_C' (r : ℚ) (m : ℤ) : (HahnSeries.C r : LaurentSeries ℚ).coeff m = if m = 0 then r else 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem coeff_eq_coeff_qExpand_two (f : LaurentSeries ℚ) (m : ℤ) : f.coeff m = (qExpand ℚ 2 f).coeff (2 * m) := by
  have h := qExpand_coeff_mul (R := ℚ) 2 f m
  rw [Nat.cast_ofNat] at h
  exact h.symm


end PhiTwoCalc
end
end Dubon2026.SourceFunctionField
