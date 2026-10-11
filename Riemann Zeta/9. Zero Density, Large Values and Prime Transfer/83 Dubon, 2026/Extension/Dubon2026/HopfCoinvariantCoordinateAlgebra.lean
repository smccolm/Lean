import Dubon2026.HopfCoinvariantComulAlgebra
import Dubon2026.BialgebraInjectiveDescent
import Dubon2026.HopfCoinvariantAntipode
import Dubon2026.HopfInjectiveAntipodeDescent

/-! # Genuine finite free Hopf structure on the actual invariant coordinates -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [CommRing B] [HopfAlgebra R B] [Module.Free R B]

/-- Choose the genuine invariant-coordinate comultiplication whose existence was derived from the original PID kernel retraction and original cocommutative Hopf structure. -/
def hopfCoinvariantComul (q : A →ₐc[R] B) :
    hopfSubgroupCoinvariants q →ₐ[R]
      hopfSubgroupCoinvariants q ⊗[R] hopfSubgroupCoinvariants q :=
  (hopfCoinvariant_exists_comulAlgHom q).choose

/-- The chosen invariant-coordinate map retains the proved exact original comultiplication diagram. -/
theorem hopfCoinvariantComul_coordinate (q : A →ₐc[R] B) :
    (Algebra.TensorProduct.map (hopfSubgroupCoinvariants q).val
      (hopfSubgroupCoinvariants q).val).comp (hopfCoinvariantComul q) =
      (Bialgebra.comulAlgHom R A).comp (hopfSubgroupCoinvariants q).val :=
  (hopfCoinvariant_exists_comulAlgHom q).choose_spec

/-- Every original bialgebra identity restricts to the actual invariant-coordinate subalgebra, through its genuine free coordinate inclusion. -/
abbrev hopfCoinvariantBialgebra (q : A →ₐc[R] B) :
    Bialgebra R (hopfSubgroupCoinvariants q) := by
  letI : Module.Free R (hopfSubgroupCoinvariants q) :=
    (hopfSubgroupCoinvariants_finite_free q).2
  exact bialgebraInjectiveDescent (hopfSubgroupCoinvariants q).val Subtype.val_injective
    (hopfCoinvariantComul q) ((Bialgebra.counitAlgHom R A).comp (hopfSubgroupCoinvariants q).val)
    (hopfCoinvariantComul_coordinate q) rfl

/-- The actual invariant-coordinate inclusion is a genuine bialgebra map for the constructed structure. -/
def hopfCoinvariantBialgebraInclusion (q : A →ₐc[R] B) :
    letI := hopfCoinvariantBialgebra q
    hopfSubgroupCoinvariants q →ₐc[R] A := by
  letI := hopfCoinvariantBialgebra q
  exact BialgHom.ofAlgHom (hopfSubgroupCoinvariants q).val rfl
    (hopfCoinvariantComul_coordinate q)

/-- Construct the actual invariant-coordinate Hopf algebra by restricting the original antipode and deriving both original Hopf identities through the genuine inclusion. -/
abbrev hopfCoinvariantHopfAlgebra (q : A →ₐc[R] B) :
    HopfAlgebra R (hopfSubgroupCoinvariants q) := by
  letI := hopfCoinvariantBialgebra q
  exact hopfInjectiveAntipodeDescent (hopfCoinvariantBialgebraInclusion q)
    Subtype.val_injective (hopfCoinvariantAntipode q) (hopfCoinvariantAntipode_coordinate q)

/-- The constructed original invariant-coordinate Hopf algebra is finite free and retains the original comultiplication and antipode diagrams. These identities consume its actual constructed Hopf operations. -/
theorem hopfCoinvariantHopfAlgebra_finite_free (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    Module.Finite R (hopfSubgroupCoinvariants q) ∧ Module.Free R (hopfSubgroupCoinvariants q) ∧
      (Algebra.TensorProduct.map (hopfSubgroupCoinvariants q).val
        (hopfSubgroupCoinvariants q).val).comp
        (Bialgebra.comulAlgHom R (hopfSubgroupCoinvariants q)) =
        (Bialgebra.comulAlgHom R A).comp (hopfSubgroupCoinvariants q).val ∧
      (hopfSubgroupCoinvariants q).val.toLinearMap.comp (HopfAlgebra.antipode R) =
        (HopfAlgebra.antipode R).comp (hopfSubgroupCoinvariants q).val.toLinearMap := by
  letI := hopfCoinvariantHopfAlgebra q
  exact ⟨(hopfSubgroupCoinvariants_finite_free q).1,
    (hopfSubgroupCoinvariants_finite_free q).2, hopfCoinvariantComul_coordinate q, rfl⟩

end
end Dubon2026
