import Dubon2026.SourceEllipticAbscissaVariableX
import Dubon2026.SourceEllipticCyclicVariableQuotient
import Dubon2026.SourceEllipticPrimeAbscissaHomX

/-! The exact intrinsic abscissa formula for the specific prime quotient
respects the original change of model. This is the coordinate input to
image-subgroup transport and the all-level cyclic-root/inertia argument. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]

/-- The intrinsic prime quotient abscissa commutes with the actual coordinate change. -/
theorem primeAbscissaQuotientX_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime]
    (hpF : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) (x : F) :
    primeAbscissaQuotientX (C • W) p (cyclicKernelVariableChange C W p H) (vcXInv C x) =
      vcXInv C (primeAbscissaQuotientX W p H x) := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  have he := cyclicAbscissae_variableChange C W H.1
  simp only [primeAbscissaQuotientX, cyclicKernelVariableChange]
  split_ifs with hp2
  · rw [he]
    exact variableChange_twoAbscissaQuotientX C W _ (by simpa only [hp2] using hpF) x
  · rw [he]
    exact variableChange_abscissaQuotientX C W _ x

end
end Dubon2026.SourceEllipticVelu
