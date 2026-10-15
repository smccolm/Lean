import Dubon2026.ArithmeticTorsionClassStageLifting
import Dubon2026.ArithmeticSourceClassColimitInjection

/-! # Actual prime-torsion lifting in the arithmetic class comparison

Direct-limit zero detection reduces actual q-torsion to a larger finite
arithmetic stage. The original Kummer correction there supplies the original
source class. This is the surjectivity on q-torsion needed for the prime-field
Hom comparison in DUB-17; full comparison surjectivity is not asserted.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- Every actual q-torsion class in the full-class quotient colimit has an original source-class preimage, at the same exceptional support. -/
theorem arithmeticTorsionClassColimit_exists_source
    (x : arithmeticClassesModOutsideColimitRep K Ω a ha) (hx : q • x = 0) :
    ∃ z : arithmeticSPlaceClassColimitRep K Ω a ha,
      (arithmeticSourceClassColimitComparison K Ω a ha).hom z = x := by
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
  have hx' : Module.DirectLimit.of ℤ _
      (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
      E (q • y) = 0 := by
    rw [map_nsmul]
    exact hx
  obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx'
  have hqF : q • arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF y = 0 :=
    (map_nsmul (arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF) q y).symm.trans hF
  obtain ⟨P, hFP, z, hz⟩ := arithmeticTorsionClass_exists_source_stage K Ω a ha q hqa F _ hqF
  refine ⟨(coefficientRepresentationColimitOf _
    (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P).hom z, ?_⟩
  rw [arithmeticSourceClassColimitComparison_of K Ω a ha P z, hz]
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticClassesModOutsideStageRep K Ω a ha F)
    (arithmeticClassesModOutsideTransitionMap K Ω a ha) P
      (arithmeticClassesModOutsideTransitionMap K Ω a ha F P hFP
        (arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF y)) = _
  rw [Module.DirectLimit.of_f (hij := hFP), Module.DirectLimit.of_f (hij := hEF)]
  rfl

end
end Dubon2026
