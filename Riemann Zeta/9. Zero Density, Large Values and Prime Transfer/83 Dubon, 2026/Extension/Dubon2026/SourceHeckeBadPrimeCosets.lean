import Dubon2026.HeckeUpperCosets

/-! DUB-17/18 -> rank-two original Hecke algebra realization -> Hecke
period compatibility at primes dividing the level. In this case every
Gamma0 matrix has invertible lower-right entry modulo p, so the actual
upper subgroup has exactly the p translation cosets. This extends the
existing good-prime transversal only where the full Hecke route needs it.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual inverse translation coset at a prime dividing the level. -/
def heckeBadUpperCoset (N p : ℕ) (x : ZMod p) :
    Gamma0 N ⧸ heckeUpperSubgroup N p :=
  QuotientGroup.mk (heckeUpperTranslation N (x.val : ℤ))⁻¹

theorem heckeBadUpperCoset_injective (N p : ℕ) [NeZero p] :
    Function.Injective (heckeBadUpperCoset N p) := by
  intro x y he
  have hm := QuotientGroup.eq.mp he
  change ((heckeUpperTranslation N (x.val : ℤ))⁻¹)⁻¹ *
    (heckeUpperTranslation N (y.val : ℤ))⁻¹ ∈ heckeUpperSubgroup N p at hm
  rw [inv_inv] at hm
  change (((((heckeUpperTranslation N (x.val : ℤ)).val) *
    ((heckeUpperTranslation N (y.val : ℤ)).val)⁻¹) 0 1 : ℤ) : ZMod p) = 0 at hm
  have hsub : x - y = 0 := by
    simpa [heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm] using hm
  exact sub_eq_zero.mp hsub

theorem heckeBadUpperCoset_surjective {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    Function.Surjective (heckeBadUpperCoset N p) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro q
  induction q using Quotient.inductionOn with | h γ => ?_
  have hc : ((γ.val 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ((Int.natCast_dvd_natCast.mpr hpN).trans
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.property)))
  have hd : ((γ.val 1 1 : ℤ) : ZMod p) ≠ 0 := by
    intro hd
    have he := congrArg (Int.cast : ℤ → ZMod p) (HeckePrimeReindex.sl2z_fin_two_det_eq_one γ.val)
    push_cast at he
    simp only [hc, hd, mul_zero, sub_zero] at he
    exact zero_ne_one he
  let x : ZMod p := -((γ.val 0 1 : ℤ) : ZMod p) / ((γ.val 1 1 : ℤ) : ZMod p)
  refine ⟨x, QuotientGroup.eq.mpr ?_⟩
  change ((heckeUpperTranslation N (x.val : ℤ))⁻¹)⁻¹ * γ ∈ heckeUpperSubgroup N p
  rw [inv_inv]
  change (((((heckeUpperTranslation N (x.val : ℤ)).val) * γ.val) 0 1 : ℤ) : ZMod p) = 0
  simp [heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, x, hd]

/-- Exact p-element transversal for the actual upper subgroup at a bad prime. -/
def heckeBadUpperCosetEquiv {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    ZMod p ≃ Gamma0 N ⧸ heckeUpperSubgroup N p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact Equiv.ofBijective (heckeBadUpperCoset N p)
    ⟨heckeBadUpperCoset_injective N p, heckeBadUpperCoset_surjective hp hpN⟩

end
end Dubon2026
