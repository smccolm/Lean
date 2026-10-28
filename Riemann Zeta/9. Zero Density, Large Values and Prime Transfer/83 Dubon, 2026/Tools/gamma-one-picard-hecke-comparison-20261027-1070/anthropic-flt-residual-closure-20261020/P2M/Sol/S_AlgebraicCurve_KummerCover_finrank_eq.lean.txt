import Mathlib.FieldTheory.KummerExtension
import P2M.Util
namespace P2MW.S_AlgebraicCurve_KummerCover_finrank_eq
set_option Elab.async false

open Polynomial IntermediateField
namespace AlgebraicCurve
namespace KummerCover
section Pure
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}
private theorem irreducible_X_pow_sub_C (hf : ∀ g : F, g ^ p ≠ f) : Irreducible (X ^ p - C f) :=
  X_pow_sub_C_irreducible_of_prime hp.out hf
end Pure
end AlgebraicCurve.KummerCover

open Polynomial AlgebraicCurve.KummerCover in
theorem solution {F L : Type*} [Field F] [Field L] [Algebra F L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p ≠ f) :
    Module.finrank F L = p :=
  finrank_of_isSplittingField_X_pow_sub_C hζ (irreducible_X_pow_sub_C hf) L

#print axioms solution
