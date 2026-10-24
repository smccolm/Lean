import Dubon2026.SourceCurveReductionKummerData
import Dubon2026.SourceCurvePrincipalGlobalConstants

/-! DUB-17/18 -> original Frobenius/inertia -> Picard torsion injectivity ->
Kummer power lifting. The reduced normalized function really is an m-th
power: its quotient by the divisor witness has order zero everywhere, so
the already proved global-constant theorem and algebraic closure supply
the missing constant root. This does not yet lift the root to the original
function field. Adapted from the Kummer section of
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero. -/
namespace Dubon2026.SourceCurve.ConstantReduction
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_residue_power_of_torsion_kernel [IsAlgClosed (ResidueField A)]
    (R : ConstantReduction A F Fbar)
    (hconst : LSpace (0 : Divisor (ResidueField A) Fbar) =
      LinearMap.range (Algebra.linearMap (ResidueField A) Fbar))
    (z : Pic0 L F) (m : ℕ) (hm : 0 < m)
    (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    ∃ D : Divisor.degZero (K := L) (F := F), Pic0.mk D = z ∧
      ∃ f : R.integers, R.residue f ≠ 0 ∧
        (∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (f : F)) ∧
        ∃ w : Fbar, w ≠ 0 ∧ w ^ m = R.residue f := by
  obtain ⟨D, hDz, f, hf, hDf, g, hg, _, hord⟩ :=
    R.exists_kummer_divisor_data z m hmz hz
  have hu : R.residue f * (g ^ m)⁻¹ ∈ LSpace (0 : Divisor (ResidueField A) Fbar) := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro Q
    rw [Finsupp.zero_apply, neg_zero, Q.ord_mul hf (inv_ne_zero (pow_ne_zero _ hg)),
      Q.ord_inv, hord Q, ← zpow_natCast, Q.ord_zpow]
    omega
  rw [hconst] at hu
  obtain ⟨c, hc⟩ := hu
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq c hm
  have heq : (algebraMap (ResidueField A) Fbar e * g) ^ m = R.residue f := by
    rw [mul_pow, ← map_pow, he]
    change algebraMap (ResidueField A) Fbar c = _ at hc
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg), mul_one]
  refine ⟨D, hDz, f, hf, hDf, algebraMap (ResidueField A) Fbar e * g, ?_, heq⟩
  intro hzero
  rw [hzero, zero_pow hm.ne'] at heq
  exact hf heq.symm

end
end Dubon2026.SourceCurve.ConstantReduction
