import Dubon2026.SourceGammaOneBinaryParabolicH1
import Dubon2026.SourceGammaOneHeckeFinite

/-! DUB17/18 -> original all-weight association -> finite Gamma1
parabolic character descent. Restrict the independently defined native
operators using their proved parabolic stability. This is their literal
finite operator image, with every original homogeneous coefficient
action retained. Character descent still requires a kernel comparison. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup groupCohomology
variable (Q N w : ℕ) [NeZero Q] [NeZero N] (hlevel : 4 ≤ Q * N ^ 2)

/-- The actual good-prime operators restricted to original parabolic binary H1. -/
def binaryParabolicPrimeOperators : sourceBinaryHeckePrime (Q * N) →
    Module.End (ZMod N) (binaryParabolicH1 Q N w) := fun ell =>
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  (sourceGammaOnePrimeOperators Q N w ell).restrict (fun _ hx =>
    binaryParabolicH1_hecke_mem Q N w hlevel ell.val
      (homogeneousMatrixAction w (Matrix.diagonal ![(ell.val : ZMod N), 1])) hx)

/-- The literal image of all integral words acting on actual parabolic H1. -/
def binaryParabolicHeckeAlgebra :=
  (FreeAlgebra.lift ℤ (binaryParabolicPrimeOperators Q N w hlevel)).range

theorem binaryParabolicWord_val
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N)))
    (x : binaryParabolicH1 Q N w) :
    (FreeAlgebra.lift ℤ (binaryParabolicPrimeOperators Q N w hlevel) a x).val =
      FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w) a x.val := by
  exact sourceHeckeWord_intertwine_addHom _ _
    (binaryParabolicH1 Q N w).subtype.toAddMonoidHom (fun _ _ => rfl) a x

theorem binaryParabolicHeckeAlgebra_finite :
    Finite (binaryParabolicHeckeAlgebra Q N w hlevel) := by
  letI := sourceGammaOneConstantH1_finite Q N w
  letI : Finite (binaryParabolicH1 Q N w) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (Module.End (ZMod N) (binaryParabolicH1 Q N w)) :=
    Finite.of_injective (fun T : Module.End (ZMod N) (binaryParabolicH1 Q N w) =>
      (T : binaryParabolicH1 Q N w → binaryParabolicH1 Q N w)) DFunLike.coe_injective
  exact Finite.of_injective
    (fun T : binaryParabolicHeckeAlgebra Q N w hlevel => T.val) Subtype.val_injective

theorem binaryParabolicWord_eq_zero_iff
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N))) :
    FreeAlgebra.lift ℤ (binaryParabolicPrimeOperators Q N w hlevel) a = 0 ↔
      ∀ x : binaryParabolicH1 Q N w,
        FreeAlgebra.lift ℤ (sourceGammaOnePrimeOperators Q N w) a x.val = 0 := by
  constructor
  · intro ha x
    rw [← binaryParabolicWord_val Q N w hlevel, ha, LinearMap.zero_apply]
    rfl
  · intro ha
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [binaryParabolicWord_val]
    exact ha x

end
end Dubon2026.SourceFunctionField.GammaOne
