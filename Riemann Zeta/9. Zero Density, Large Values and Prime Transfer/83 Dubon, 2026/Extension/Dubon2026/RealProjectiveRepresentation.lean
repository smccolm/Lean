import Dubon2026.RealProjectiveL2Embedding

/-! # The actual projective cyclic representation preserves the genuine L2 inner product -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- The original right-translation representation factors through its actual trivial central action. -/
def realProjectiveCyclicRepresentation {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    Representation ℂ PSL(2, ℝ) (realLiftCyclicRepresentation k f).toSubmodule :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ))
    (realLiftCyclicRepresentation k f).toRepresentation (by
      intro a ha
      change (realLiftCyclicRepresentation k f).toRepresentation a = 1
      ext v g
      change v.val (g * a) = v.val g
      rcases (realSL2_center_eq_signs a).mp ha with rfl | rfl
      · rw [mul_one]
      · rw [mul_neg, mul_one, realLiftCyclic_neg f v.property])

/-- The factored representation is still the literal original right translation at every quotient representative. -/
theorem realProjectiveCyclicRepresentation_apply {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (a q : PSL(2, ℝ)) (v : (realLiftCyclicRepresentation k f).toSubmodule) :
    realProjectiveCyclicVector f (realProjectiveCyclicRepresentation f a v) q =
      realProjectiveCyclicVector f v (q * a) := by
  induction a using Quotient.inductionOn with | h g => ?_
  induction q using Quotient.inductionOn with | h h => rfl

/-- The actual L2 inner product is precisely the genuine cyclic quotient Petersson pairing. -/
theorem realProjectiveCyclicToL2_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    inner ℂ (realProjectiveCyclicToL2 f v) (realProjectiveCyclicToL2 f w) =
      realProjectiveCyclicPairing f v w := by
  change (∫ q, inner ℂ (realProjectiveCyclicToL2 f v q)
    (realProjectiveCyclicToL2 f w q) ∂(realProjectiveMeasure.restrict
      (realProjectiveGamma0Domain Q))) = _
  apply integral_congr_ae
  filter_upwards [(realProjectiveCyclicVector_memLp_two f v).coeFn_toLp,
    (realProjectiveCyclicVector_memLp_two f w).coeFn_toLp] with q hv hw
  change inner ℂ (((realProjectiveCyclicVector_memLp_two f v).toLp _) q)
    (((realProjectiveCyclicVector_memLp_two f w).toLp _) q) = _
  rw [hv, hw, RCLike.inner_apply, mul_comm]

/-- Every actual projective group element preserves the faithful quotient L2 inner product. -/
theorem realProjectiveCyclicRepresentation_inner {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (a : PSL(2, ℝ)) (v w : (realLiftCyclicRepresentation k f).toSubmodule) :
    inner ℂ (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a v))
      (realProjectiveCyclicToL2 f (realProjectiveCyclicRepresentation f a w)) =
        inner ℂ (realProjectiveCyclicToL2 f v) (realProjectiveCyclicToL2 f w) := by
  rw [realProjectiveCyclicToL2_inner, realProjectiveCyclicToL2_inner]
  change (∫ q in realProjectiveGamma0Domain Q,
    conj (realProjectiveCyclicVector f (realProjectiveCyclicRepresentation f a v) q) *
      realProjectiveCyclicVector f (realProjectiveCyclicRepresentation f a w) q
        ∂realProjectiveMeasure) = _
  simp_rw [realProjectiveCyclicRepresentation_apply]
  exact realProjectiveCyclicPairing_right f v w a

end
end Dubon2026
