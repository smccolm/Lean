import Dubon2026.SourceHeckeBadPrimeCosets
import Dubon2026.SourceWeightTwoHeckeCosetTrace

/-! DUB-17/18 -> rank-two full Hecke algebra realization -> all-prime
analytic Hecke comparison. The p translation cosets at a prime dividing
the level give exactly the original U_p average. Combining this with the
existing good-prime trace supplies the genuine quotient-coset identity
at every prime, with the source normalization unchanged.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
variable {N p : ℕ} [NeZero p]

theorem heckeUpperMatrix_translation (N p : ℕ) [NeZero p] (x : ℕ) :
    heckeTriangularMatrix 1 p 0 * mapGL ℝ (heckeUpperTranslation N (x : ℤ)).val =
      heckeTriangularMatrix 1 p x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeUpperTranslation, heckeTriangularMatrix_val,
      mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N p) :=
  sourceHeckeUpperFintype N p

theorem sourceWeightTwoHeckeCoset_sum_bad [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (f : CuspForm (Gamma0 N) 2) :
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p, sourceWeightTwoHeckeCoset hp f q) =
      ⇑(cuspHeckePrime hp f) := by
  rw [← (heckeBadUpperCosetEquiv hp hpN).sum_comp]
  change (∑ x : ZMod p, sourceWeightTwoHeckeCoset hp f
    (QuotientGroup.mk (heckeUpperTranslation N (x.val : ℤ))⁻¹)) = classicalHeckeFunction N 2 p f
  simp only [sourceWeightTwoHeckeCoset_mk, Subgroup.coe_inv, inv_inv,
    ← SlashAction.slash_mul, heckeUpperMatrix_translation]
  have hc : ¬ Nat.Coprime p N := fun h => (hp.coprime_iff_not_dvd.mp h) hpN
  rw [classicalHeckeFunction_prime N 2 hp, if_neg hc, add_zero]
  unfold heckeTriangularSum
  rw [← Fin.sum_univ_eq_sum_range, ← (ZMod.finEquiv p).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hx : ((ZMod.finEquiv p) x).val = x.val := by
    cases p with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  change (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p ((ZMod.finEquiv p) x).val) =
    (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p x.val)
  rw [hx]

theorem sourceWeightTwoHeckeCoset_sum_all [NeZero N] (hp : p.Prime)
    (f : CuspForm (Gamma0 N) 2) :
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p, sourceWeightTwoHeckeCoset hp f q) =
      ⇑(cuspHeckePrime hp f) := by
  by_cases h : Nat.Coprime p N
  · exact sourceWeightTwoHeckeCoset_sum hp h f
  · have hd : p ∣ N := by
      by_contra hn
      exact h (hp.coprime_iff_not_dvd.mpr hn)
    exact sourceWeightTwoHeckeCoset_sum_bad hp hd f

end
end Dubon2026
