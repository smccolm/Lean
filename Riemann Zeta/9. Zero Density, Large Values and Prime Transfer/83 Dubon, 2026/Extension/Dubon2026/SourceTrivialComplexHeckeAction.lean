import Dubon2026.SourceTrivialHeckeAlgebra
import Dubon2026.SourceTrivialComplexIntegralSpan
import Dubon2026.SourceHeckeWordTransport

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two eigencharacter lifting -> faithful action of the actual integral
Hecke algebra on full complex H1. Existing integral-word transport and the
proved full complex spanning theorem discharge well-definedness; integral
coefficient-change injectivity discharges faithfulness.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (Q : ℕ) [NeZero Q]

/-- Every relation among the original integral Hecke operators is a
relation on the entire original complex H1. -/
theorem sourceTrivialComplexHecke_relation
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (ha : FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators ℤ Q) a = 0) :
    FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators ℂ Q) a = 0 := by
  apply sourceTrivialComplexH1_end_zero_of_integer
  intro x
  have h := sourceHeckeWord_intertwine (sourceTrivialRingHeckeOperators ℤ Q)
    (sourceTrivialRingHeckeOperators ℂ Q) (sourceTrivialH1IntegerChange ℂ Q).toAddMonoidHom
    (fun ell y => sourceTrivialH1IntegerChange_hecke ℂ Q ell y) a x
  rw [ha, LinearMap.zero_apply, map_zero] at h
  exact h.symm

/-- The actual integral Hecke algebra acts on full complex H1 by the
original complex prime correspondences. -/
def sourceTrivialComplexHeckeAction :
    sourceTrivialHeckeAlgebra Q →+* Module.End ℂ (H1 (Rep.trivial ℂ (Gamma0 Q) ℂ)) := by
  let f := (sourceTrivialIntegralHeckeWord Q).toRingHom
  let φ := (FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators ℂ Q)).toRingHom
  have hf : Function.Surjective f := sourceTrivialIntegralHeckeWord_surjective Q
  have hk : RingHom.ker f ≤ RingHom.ker φ := by
    intro a ha
    apply sourceTrivialComplexHecke_relation Q
    have h := congrArg Subtype.val (show sourceTrivialIntegralHeckeWord Q a = 0 from ha)
    exact h
  exact RingHom.liftOfRightInverse f (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨φ, hk⟩

/-- The complex action of each actual integral Hecke word is its original
full complex operator value. -/
theorem sourceTrivialComplexHeckeAction_word
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q)) :
    sourceTrivialComplexHeckeAction Q (sourceTrivialIntegralHeckeWord Q a) =
      FreeAlgebra.lift ℤ (sourceTrivialRingHeckeOperators ℂ Q) a := by
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ a

/-- The full actual integral-algebra action intertwines the original
integral and complex H1 coefficient maps. -/
theorem sourceTrivialComplexHeckeAction_integer
    (t : sourceTrivialHeckeAlgebra Q) (x : H1 (Rep.trivial ℤ (Gamma0 Q) ℤ)) :
    sourceTrivialComplexHeckeAction Q t (sourceTrivialH1IntegerChange ℂ Q x) =
      sourceTrivialH1IntegerChange ℂ Q (t.val x) := by
  obtain ⟨a, rfl⟩ := sourceTrivialIntegralHeckeWord_surjective Q t
  rw [sourceTrivialComplexHeckeAction_word, sourceTrivialIntegralHeckeWord_coe]
  exact (sourceHeckeWord_intertwine (sourceTrivialRingHeckeOperators ℤ Q)
    (sourceTrivialRingHeckeOperators ℂ Q) (sourceTrivialH1IntegerChange ℂ Q).toAddMonoidHom
    (fun ell y => sourceTrivialH1IntegerChange_hecke ℂ Q ell y) a x).symm

/-- The actual integral Hecke algebra acts faithfully on the entire
original complex H1; faithfulness is not a lifting premise. -/
theorem sourceTrivialComplexHeckeAction_injective :
    Function.Injective (sourceTrivialComplexHeckeAction Q) := by
  intro t u h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply sourceTrivialH1IntegerChange_injective ℂ Q
  exact (sourceTrivialComplexHeckeAction_integer Q t x).symm.trans
    ((congrArg (fun T => T (sourceTrivialH1IntegerChange ℂ Q x)) h).trans
      (sourceTrivialComplexHeckeAction_integer Q u x))

end
end Dubon2026
