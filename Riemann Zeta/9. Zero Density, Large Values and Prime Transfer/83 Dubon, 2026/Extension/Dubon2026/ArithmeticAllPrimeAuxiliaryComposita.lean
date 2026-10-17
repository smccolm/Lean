import Dubon2026.ArithmeticTwoPowerCyclicSubfield
import Dubon2026.OriginalCyclicAuxiliaryComposita

/-! # Construct the actual auxiliary cyclic field tower

Choose a sufficiently large cyclic subfield inside the fixed arithmetic
union. Its two literal composita supply all relative Galois, cyclicity,
positive prime-power degree and divisibility conditions for DUB-17's
original class-generator transfer. The given extension need not be
cyclic or normal over the rationals.
-/
namespace Dubon2026
noncomputable section
open IntermediateField
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- Every actual finite Galois prime-power stage in the fixed arithmetic union admits the required pair of auxiliary cyclic composita in that same union. -/
theorem rationalArithmetic_exists_allPrime_cyclic_auxiliary_composita
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    (hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E)
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    ∃ D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
    ∃ r s : ℕ,
      let L := K ⊔ D.toIntermediateField
      let M := E ⊔ D.toIntermediateField
      letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      letI : Algebra K L := (IntermediateField.inclusion (show K ≤ L from le_sup_left)).toAlgebra
      letI : Module K L := Algebra.toModule
      letI : Algebra E M := (IntermediateField.inclusion (show E ≤ M from le_sup_left)).toAlgebra
      letI : Module E M := Algebra.toModule
      letI : Algebra K M := (IntermediateField.inclusion (hKE.trans le_sup_left : K ≤ M)).toAlgebra
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = q ^ (r + 1) ∧
      IsGalois E M ∧ IsCyclic Gal(M/E) ∧ Module.finrank E M = q ^ (s + 1) ∧
      IsGalois K M ∧ Module.finrank K E ∣ q ^ (r + 1) := by
  obtain ⟨D, hcyclicD, hD⟩ := rationalArithmetic_exists_cyclic_allPrimePower_subfield
    a q (Module.finrank ℚ E + t) hq hqa
  letI : IsCyclic Gal(D.toIntermediateField/ℚ) := hcyclicD
  exact ⟨D, originalCyclicAuxiliaryComposita_exists_degrees (hcycD := hcyclicD)
    (rationalUnramifiedExtension a) K E D.toIntermediateField hKE hGalKE q t hq hD hdegreeKE⟩

end
end Dubon2026