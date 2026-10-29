import Dubon2026.SourceSiegelPolynomialFactors
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
The actual stabilized coefficient belongs to the integral closure because
it is already a coefficient of a finite product of integral linear
factors. No infinite-product integrality or closedness premise is needed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
noncomputable section
open Polynomial

theorem coeff_one_sub_C_mul_X (u : ℂ) (j : ℕ) :
    ((1 : ℂ[X]) - C u * X).coeff j = if j = 0 then 1 else if j = 1 then -u else 0 := by
  rcases j with _ | _ | j <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]

/-- Every coefficient of the actual finite polynomial lies in the integral closure of Z. -/
def CoeffInt (p : ℂ[X]) : Prop := ∀ j, p.coeff j ∈ integralClosure ℤ ℂ

theorem CoeffInt.one : CoeffInt (1 : ℂ[X]) := fun j => by
  rw [Polynomial.coeff_one]; split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem CoeffInt.mul {p q : ℂ[X]} (hp : CoeffInt p) (hq : CoeffInt q) : CoeffInt (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hp _) (hq _)

theorem CoeffInt.expand {p : ℂ[X]} (hp : CoeffInt p) {m : ℕ} (hm : 0 < m) :
    CoeffInt (Polynomial.expand ℂ m p) := fun j => by
  rw [Polynomial.coeff_expand hm]; split_ifs
  · exact hp _
  · exact Subalgebra.zero_mem _

theorem CoeffInt.one_sub_C_mul_X {u : ℂ} (hu : IsIntegral ℤ u) : CoeffInt (1 - C u * X) := fun j => by
  rw [coeff_one_sub_C_mul_X]; split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.neg_mem _ hu
  · exact Subalgebra.zero_mem _

theorem CoeffInt.ite (p : Prop) [Decidable p] {a b : ℂ[X]} (ha : CoeffInt a) (hb : CoeffInt b) :
    CoeffInt (if p then a else b) := by
  split_ifs <;> assumption

theorem coeffInt_Pc (N r : ℕ) {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (k : ℕ) :
    CoeffInt (Pc N r u v k) :=
  (CoeffInt.ite _ (CoeffInt.one_sub_C_mul_X hu) CoeffInt.one).mul
    (CoeffInt.ite _ (CoeffInt.one_sub_C_mul_X hv) CoeffInt.one)

theorem coeffInt_pp (N r : ℕ) {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (n : ℕ) :
    CoeffInt (pp (Pc N r u v) n) := by
  induction n with
  | zero => rw [pp_zero]; exact CoeffInt.one
  | succ n ih => rw [pp_succ]; exact ih.mul ((coeffInt_Pc N r hu hv n).expand (Nat.succ_pos n))


theorem isIntegral_stableCoeff (N r : ℕ) {u v : ℂ}
    (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (m : ℕ) :
    IsIntegral ℤ (stableCoeff (Pc N r u v) m) :=
  coeffInt_pp N r hu hv m m

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
