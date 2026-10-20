import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Instances.ZMod

/-! The original quadratic Galois quotient gives the component character
required by the source polarized CM deformation problem in DUB-17. Its
kernel is proved to be the actual fixing subgroup of the quadratic field. -/

namespace Dubon2026
open Algebra
noncomputable section

/-- The Galois group of the original characteristic-zero quadratic extension
is the two-element component group. -/
def quadraticGaloisComponentEquiv (F K : Type*) [Field F] [Field K] [CharZero F]
    [Algebra F K] [IsQuadraticExtension F K] : Gal(K/F) ≃* Multiplicative (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply mulEquivOfPrimeCardEq (p := 2)
  · exact (IsGalois.card_aut_eq_finrank F K).trans (IsQuadraticExtension.finrank_eq_two F K)
  · simp

/-- The quadratic Galois identification is continuous in the original Krull topology. -/
theorem quadraticGaloisComponentEquiv_continuous (F K : Type*) [Field F] [Field K] [CharZero F]
    [Algebra F K] [IsQuadraticExtension F K] :
    Continuous (quadraticGaloisComponentEquiv F K) :=
  continuous_of_discreteTopology

variable {F Ω : Type*} [Field F] [Field Ω] [CharZero F] [Algebra F Ω]
  (K : IntermediateField F Ω) [IsQuadraticExtension F K]

/-- The original quadratic-field restriction defines the actual component character. -/
def quadraticGaloisComponent : Gal(Ω/F) →* Multiplicative (ZMod 2) :=
  (quadraticGaloisComponentEquiv F K).toMonoidHom.comp (AlgEquiv.restrictNormalHom K)

/-- The actual quadratic component character is continuous. -/
theorem quadraticGaloisComponent_continuous : Continuous (quadraticGaloisComponent K) :=
  (quadraticGaloisComponentEquiv_continuous F K).comp
    (InfiniteGalois.restrictNormalHom_continuous K)

/-- The original quadratic component vanishes precisely on the actual fixing subgroup. -/
theorem quadraticGaloisComponent_ker : (quadraticGaloisComponent K).ker = K.fixingSubgroup := by
  rw [← K.restrictNormalHom_ker]
  ext g
  change quadraticGaloisComponentEquiv F K (AlgEquiv.restrictNormalHom K g) = 1 ↔
    AlgEquiv.restrictNormalHom K g = 1
  exact (quadraticGaloisComponentEquiv F K).map_eq_one_iff

/-- Every component is attained by the original Galois restriction when the ambient extension is normal. -/
theorem quadraticGaloisComponent_surjective [Normal F Ω] :
    Function.Surjective (quadraticGaloisComponent K) :=
  (quadraticGaloisComponentEquiv F K).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K) (E := Ω))

end
end Dubon2026
