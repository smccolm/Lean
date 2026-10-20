import Dubon2026.PolarizedAdjointSwitch
import Dubon2026.InvolutionComponentHom
import Dubon2026.PolarizedGaloisGroup

/-! The actual full adjoint representation of the disconnected polarized
target. This is CHT Section 2.1's coefficient module, needed to transfer the
existing first-order deformation and cohomology arguments to the source
fixed-similitude deformation problem on the DUB-17 automorphy route. -/

namespace Dubon2026
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original identity-component conjugation, as invertible linear operators. -/
def polarizedAdjointIdentity : GeneralLinearGroup ι R × Rˣ →*
    (Module.End R (Matrix ι ι R))ˣ :=
  (matrixAdjointRepresentation (MonoidHom.fst _ _)).asGroupHom

/-- The order-two component acts by the actual negative-transpose involution. -/
def polarizedAdjointComponent : Multiplicative (ZMod 2) →*
    (Module.End R (Matrix ι ι R))ˣ :=
  involutionComponentHom polarizedAdjointInvolutionUnit polarizedAdjointInvolutionUnit_sq

/-- The source switching action is compatible with the original full adjoint operators. -/
theorem polarizedAdjoint_compatibility (z : Multiplicative (ZMod 2)) :
    polarizedAdjointIdentity.comp (polarizedSwitchAction (ι := ι) (R := R) z).toMonoidHom =
      (MulAut.conj (polarizedAdjointComponent z)).toMonoidHom.comp polarizedAdjointIdentity := by
  by_cases hz : z = 1
  · subst z
    apply MonoidHom.ext
    intro x
    simp
  · have hz' : z = Multiplicative.ofAdd (1 : ZMod 2) := by
      apply Multiplicative.toAdd.injective
      have h0 : z.toAdd ≠ 0 := fun h => hz (Multiplicative.toAdd.injective h)
      generalize z.toAdd = x at h0 ⊢
      fin_cases x
      · exact (h0 rfl).elim
      · rfl
    subst z
    apply MonoidHom.ext
    intro x
    apply Units.ext
    apply LinearMap.ext
    intro X
    have hj : polarizedAdjointComponent (ι := ι) (R := R)
        (Multiplicative.ofAdd (1 : ZMod 2)) = polarizedAdjointInvolutionUnit :=
      involutionComponentHom_generator _ _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hj]
    change ((polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) x).1.val * X *
      (polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) x).1.inv) =
        -((x.1.val * (-X.transpose) * x.1.inv).transpose)
    have hs : polarizedSwitchAction (Multiplicative.ofAdd (1 : ZMod 2)) x = polarizedSwitch x := by
      change (if (1 : ZMod 2) = 0 then x else polarizedSwitch x) = polarizedSwitch x
      norm_num
    rw [hs]
    exact polarizedAdjoint_switch x X

/-- The full adjoint representation of the original source polarized group. -/
def polarizedAdjointRepresentation :
    Representation R (PolarizedGaloisGroup ι R) (Matrix ι ι R) :=
  (Units.coeHom _).comp
    (SemidirectProduct.lift polarizedAdjointIdentity polarizedAdjointComponent
      polarizedAdjoint_compatibility)

/-- On the original identity component the action is literal matrix conjugation. -/
theorem polarizedAdjointRepresentation_identity (x : GeneralLinearGroup ι R × Rˣ)
    (X : Matrix ι ι R) :
    polarizedAdjointRepresentation (polarizedIdentityComponent x) X =
      x.1.val * X * x.1.inv := by
  change ((SemidirectProduct.lift polarizedAdjointIdentity polarizedAdjointComponent
    polarizedAdjoint_compatibility (SemidirectProduct.inl x)).val) X = _
  rw [SemidirectProduct.lift_inl]
  rfl

/-- On the source element j the action is negative transpose on all matrices. -/
theorem polarizedAdjointRepresentation_j (X : Matrix ι ι R) :
    polarizedAdjointRepresentation polarizedComplexConjugation X = -X.transpose := by
  change ((SemidirectProduct.lift polarizedAdjointIdentity polarizedAdjointComponent
    polarizedAdjoint_compatibility
      (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))).val) X = _
  rw [SemidirectProduct.lift_inr]
  change ((involutionComponentHom polarizedAdjointInvolutionUnit
    polarizedAdjointInvolutionUnit_sq (Multiplicative.ofAdd (1 : ZMod 2))).val) X = _
  rw [involutionComponentHom_generator]
  rfl

/-- The full original action separates its matrix conjugation and exact component action. -/
theorem polarizedAdjointRepresentation_apply (g : PolarizedGaloisGroup ι R)
    (X : Matrix ι ι R) :
    polarizedAdjointRepresentation g X = g.left.1.val *
      polarizedAdjointRepresentation (SemidirectProduct.inr g.right) X * g.left.1.inv := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  simp only [map_mul, Module.End.mul_apply]
  exact polarizedAdjointRepresentation_identity _ _

end Dubon2026
