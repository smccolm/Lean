import Dubon2026.SourceLaurentReindex


/-! DUB-17/18 -> cusp-form lower dimension bound -> original regular
differential realization -> finite function-field extension -> monic relations.
This is the literal finite conjugate product and its coefficient descent.
SourcePrimeCoefficientPolynomialDescent proves analytic invariance and
polynomial descent, and SourcePrimeMonicRelation assembles the monic relation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_PhiGen.lean, selected QTwist section.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries HahnSeries Polynomial

section QTwist

variable {R : Type*} [CommRing R]

/-- Multiply each Laurent coefficient by the corresponding integral power of a unit. -/
def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R where
  coeff k := (u ^ k : Rˣ) * f.coeff k
  isPWO_support' := f.isPWO_support'.mono fun k hk => by
    simp only [Function.mem_support] at hk ⊢
    exact fun h => hk (by rw [h, mul_zero])

@[simp]
theorem qTwistFun_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwistFun u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

theorem support_qTwistFun (u : Rˣ) (f : LaurentSeries R) :
    (qTwistFun u f).support = f.support := by
  ext k
  rw [HahnSeries.mem_support, HahnSeries.mem_support, qTwistFun_coeff]
  exact not_congr (Units.mul_right_eq_zero _)

/-- The ring homomorphism induced by substituting the unit multiple of q. -/
def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R where
  toFun := qTwistFun u
  map_one' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [mul_zero]
  map_mul' f g := by
    ext k

    have hset : Finset.addAntidiagonal (qTwistFun u f).isPWO_support
        (qTwistFun u g).isPWO_support k =
        Finset.addAntidiagonal f.isPWO_support g.isPWO_support k := by
      ext ij
      simp only [Finset.mem_addAntidiagonal, support_qTwistFun]
    rw [qTwistFun_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, hset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.mp hij
    rw [qTwistFun_coeff, qTwistFun_coeff, mul_mul_mul_comm, ← Units.val_mul, ← zpow_add,
      hsum]
  map_zero' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_zero, mul_zero]
  map_add' f g := by
    ext k
    rw [HahnSeries.coeff_add]
    show (qTwistFun u (f + g)).coeff k = (qTwistFun u f).coeff k + (qTwistFun u g).coeff k
    rw [qTwistFun_coeff, qTwistFun_coeff, qTwistFun_coeff, HahnSeries.coeff_add, mul_add]

@[simp]
theorem qTwist_coeff (u : Rˣ) (f : LaurentSeries R) (k : ℤ) :
    (qTwist u f).coeff k = (u ^ k : Rˣ) * f.coeff k := rfl

theorem support_qTwist (u : Rˣ) (f : LaurentSeries R) : (qTwist u f).support = f.support :=
  support_qTwistFun u f

theorem qTwist_one_apply (f : LaurentSeries R) : qTwist (1 : Rˣ) f = f := by
  ext k
  rw [qTwist_coeff, one_zpow, Units.val_one, one_mul]

theorem qTwist_qTwist (u v : Rˣ) (f : LaurentSeries R) :
    qTwist u (qTwist v f) = qTwist (u * v) f := by
  ext k
  rw [qTwist_coeff, qTwist_coeff, qTwist_coeff, ← mul_assoc, ← Units.val_mul, ← mul_zpow]

theorem qTwist_qExpand (v : Rˣ) (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    qTwist v (qExpand R N f) = qExpand R N (qTwist (v ^ (N : ℤ)) f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qTwist_coeff, qExpand_coeff_mul, qExpand_coeff_mul, qTwist_coeff, ← zpow_mul]
  · rw [qTwist_coeff, qExpand_coeff_of_not_dvd N f hk, mul_zero,
      qExpand_coeff_of_not_dvd N _ hk]

end QTwist

end
end Dubon2026.SourceFunctionField
