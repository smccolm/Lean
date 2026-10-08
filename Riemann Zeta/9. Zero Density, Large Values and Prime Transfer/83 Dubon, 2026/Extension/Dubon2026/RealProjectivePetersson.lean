import Dubon2026.RealProjectivePairing

/-! # The original Petersson pairing on a genuine projective arithmetic fundamental domain -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- The original cusp form itself, descended through its proved central invariance. -/
def realProjectiveCuspLift {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) : PSL(2, ℝ) → ℂ :=
  realProjectiveCyclicVector f ⟨realWeightLift k f, realWeightLift_mem_cyclic k f⟩

/-- Every representative gives exactly the original slash-evaluated cusp lift. -/
theorem realProjectiveCuspLift_mk {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (g : SL(2, ℝ)) :
    realProjectiveCuspLift f (QuotientGroup.mk g) = realWeightLift k f g := rfl

/-- The exact original Petersson density is the product of the two actual quotient lifts. -/
theorem realProjectiveCuspLift_pairing {Q : ℕ} {k : ℤ}
    (f f' : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (q : PSL(2, ℝ)) :
    conj (realProjectiveCuspLift f q) * realProjectiveCuspLift f' q =
      petersson k f f' (realProjectiveOrbit q) := by
  induction q using Quotient.inductionOn with | h g => ?_
  exact realWeightLift_pairing k f f' g

/-- The actual quotient pairing has precisely the original classical Petersson normalization. -/
theorem cuspPetersson_eq_projectiveGroup_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f f' : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspPetersson f f' = ∫ q in realProjectiveGamma0Domain Q,
      conj (realProjectiveCuspLift f q) * realProjectiveCuspLift f' q ∂realProjectiveMeasure := by
  have hS : MeasurableSet (gamma0FundamentalDomain Q) := by
    apply IsOpen.measurableSet
    exact isOpen_iUnion (fun q : SL(2, ℤ) ⧸ Gamma0 Q =>
      ModularGroup.isOpen_fdo.smul ((q.out : SL(2, ℤ))⁻¹))
  have hm := realProjectiveOrbit_measurePreserving.restrict_preimage hS
  have he := integral_map
    (μ := realProjectiveMeasure.restrict (realProjectiveOrbit ⁻¹' gamma0FundamentalDomain Q))
    hm.measurable.aemeasurable
    (petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable
  rw [hm.map_eq] at he
  rw [cuspPetersson_eq_gamma0Domain_integral Q]
  simp_rw [realProjectiveCuspLift_pairing]
  exact he

end
end Dubon2026
