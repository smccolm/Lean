import Dubon2026.PolarizedInvolution
import Dubon2026.InvolutionComponentHom

/-! The original symmetric polarization matrix supplies the full source
component action, including its precise matrix conjugation and odd
similitude. This is consumed by the CM residual extension for DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The actual polarization involution defines the real-place component action. -/
def polarizedInvolutionAction (B : GeneralLinearGroup ι R) (hB : B.val.transpose = B.val) :
    Multiplicative (ZMod 2) →* PolarizedGaloisGroup ι R :=
  involutionComponentHom (polarizedInvolution B) (polarizedInvolution_sq B hB)

/-- The component action retains the original polarization matrix. -/
theorem polarizedInvolutionAction_generator (B : GeneralLinearGroup ι R)
    (hB : B.val.transpose = B.val) :
    polarizedInvolutionAction B hB (Multiplicative.ofAdd (1 : ZMod 2)) = polarizedInvolution B :=
  involutionComponentHom_generator _ _

/-- The constructed action has precisely the original source component. -/
theorem polarizedInvolutionAction_component (B : GeneralLinearGroup ι R)
    (hB : B.val.transpose = B.val) (z : Multiplicative (ZMod 2)) :
    polarizedComponent (polarizedInvolutionAction B hB z) = z := by
  by_cases hz : z.toAdd = 0
  · have hz' : z = 1 := hz
    subst z
    rw [map_one, map_one]
  · have hz' : z = Multiplicative.ofAdd (1 : ZMod 2) := by
      change z.toAdd = (1 : ZMod 2)
      generalize z.toAdd = x at hz ⊢
      fin_cases x
      · exact (hz rfl).elim
      · rfl
    rw [hz', polarizedInvolutionAction_generator, polarizedInvolution_component]

/-- The exact source conjugation is matrix-conjugated inverse transpose with its original multiplier. -/
theorem polarizedInvolution_conjugate (B : GeneralLinearGroup ι R)
    (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedInvolution B * polarizedIdentityComponent x * (polarizedInvolution B)⁻¹ =
      polarizedIdentityComponent ((B, 1) * polarizedSwitch x * (B, 1)⁻¹) := by
  have he : polarizedInvolution B =
      polarizedIdentityComponent (B, 1) * polarizedComplexConjugation :=
    SemidirectProduct.mk_eq_inl_mul_inr _ _
  rw [he]
  calc
    _ = polarizedIdentityComponent (B, 1) *
        (polarizedComplexConjugation * polarizedIdentityComponent x * polarizedComplexConjugation⁻¹) *
          (polarizedIdentityComponent (B, 1))⁻¹ := by group
    _ = _ := by rw [polarizedComplexConjugation_conjugate, ← map_inv, ← map_mul, ← map_mul]

end Dubon2026
