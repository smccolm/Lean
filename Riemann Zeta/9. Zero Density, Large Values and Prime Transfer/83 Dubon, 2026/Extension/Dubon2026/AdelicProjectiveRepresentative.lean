import Dubon2026.AdelicUnipotentJetVectors

/-! # Actual full adelic representatives of the original projective realization -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- An actual full adelic matrix representing the original real and finite projective coordinates. -/
def adelicProjectiveRepresentative (p : AdelicProjectiveGroup) : RationalAdelicGL2 :=
  rationalAdelicGL2RealFiniteEquiv.symm
    (toGL (Classical.choose (QuotientGroup.mk_surjective p.1)),
      Classical.choose (ProjGenLinGroup.mk_surjective p.2))

/-- Every original algebraic cyclic vector retains its literal value at its actual full adelic representative. -/
theorem adelicCyclicProjectiveFunction_representative (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f v p = v.val (adelicProjectiveRepresentative p) := by
  let r := Classical.choose (QuotientGroup.mk_surjective p.1)
  let a := Classical.choose (ProjGenLinGroup.mk_surjective p.2)
  have hr : QuotientGroup.mk r = p.1 := Classical.choose_spec (QuotientGroup.mk_surjective p.1)
  have ha : ProjGenLinGroup.mk a = p.2 := Classical.choose_spec (ProjGenLinGroup.mk_surjective p.2)
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  change adelicCyclicProjectiveFunction N f v p =
    v.val (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a))
  rw [hp, adelicCyclicProjectiveFunction_mk]

/-- Every original translated generator is its actual full adelic value at the same representative, for every group element. -/
theorem adelicCyclicGenerator_projective_orbit_representative (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (b : RationalAdelicGL2)
    (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation b (adelicCyclicGenerator N f)) p =
      canonicalAdelicGL2CuspLift N k f (adelicProjectiveRepresentative p * b) := by
  rw [adelicCyclicProjectiveFunction_representative]
  rfl

/-- The original real projective orbit is realized by the same genuine adelic representative for every parameter and real curve. -/
theorem adelicProjectiveRealOrbit_representative_eq (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (t : ℝ) (p : AdelicProjectiveGroup) :
    adelicProjectiveRealOrbit N f c t p = canonicalAdelicGL2CuspLift N k f
      (adelicProjectiveRepresentative p * adelicRealSL2Embedding (c t)) :=
  adelicCyclicGenerator_projective_orbit_representative N f _ p

end
end Dubon2026
