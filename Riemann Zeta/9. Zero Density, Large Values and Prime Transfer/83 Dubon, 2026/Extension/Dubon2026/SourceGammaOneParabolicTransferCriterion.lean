import Dubon2026.SourceGammaOneParabolicOperatorAlgebra
import Dubon2026.SourceParabolicCohomology

/-! DUB17/18 -> original all-weight association -> finite parabolic
character descent. Isolate the exact geometric input still required:
parabolic preimages of coefficient-reduced integral parabolic classes
under the existing native transfer. This proposition is an unresolved
input, not a proved comparison. The word-kernel implication below uses
the existing independently proved transfer and coefficient identities. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceFunctionField.GammaOne
variable (Q N w : ℕ) [NeZero Q] [NeZero N]

/-- The precise unresolved parabolic lifting input for the actual native transfer. -/
def sourceGammaOneIntegralParabolicTransfer : Prop :=
  ∀ x : H1 (sourceBinaryCoefficientRep ℤ Q w),
    x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w) →
    ∃ y : binaryParabolicH1 Q N w,
      sourceGammaOneConstantH1Transfer Q N w y.val =
        sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w x

theorem sourceGammaOneParabolicTransfer_word_kernel
    (hlevel : 4 ≤ Q * N ^ 2) (hlift : sourceGammaOneIntegralParabolicTransfer Q N w)
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N)))
    (ha : FreeAlgebra.lift ℤ (binaryParabolicPrimeOperators Q N w hlevel) a = 0)
    (x : H1 (sourceBinaryCoefficientRep ℤ Q w))
    (hx : x ∈ sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w
      ((sourceGammaOneOriginalHeckeWord Q N w a).val x) = 0 := by
  obtain ⟨y, hy⟩ := hlift x hx
  have hz := (binaryParabolicWord_eq_zero_iff Q N w hlevel a).mp ha y
  rw [sourceGammaOneOriginalHeckeWord_change, ← hy,
    ← sourceGammaOneHeckeWord_transfer, hz, map_zero]

end
end Dubon2026
