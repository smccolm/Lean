import Dubon2026.OriginalCoinducedFunctionCoefficients
import Mathlib.RepresentationTheory.Invariants

/-! # Original invariant functions are functions on the actual quotient group -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [S.Normal]

private theorem originalInvariantFunction_coset
    (f : (originalCoinducedFunctionRep A).quotientToInvariants S)
    (g h : G) (hgh : QuotientGroup.leftRel S g h) : f.val.val g = f.val.val h := by
  let s : S := ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh⟩
  have hf := congrArg (fun v : originalCoinducedFunctionRep A => v.val g) (f.property s)
  change f.val.val (g * (g⁻¹ * h)) = f.val.val g at hf
  simpa only [mul_inv_cancel_left] using hf.symm

/-- Descend the actual subgroup-invariant function along the original
quotient map, preserving every original coefficient value. -/
def originalInvariantFunctionDescend
    (f : (originalCoinducedFunctionRep A).quotientToInvariants S) :
    originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A) :=
  originalCoinducedFunction _ (fun q => Quotient.liftOn' q (fun g => f.val.val g)
    (originalInvariantFunction_coset A S f))

/-- Pull back the original quotient-group function to its original
invariant function on the group. -/
def originalInvariantFunctionLift
    (f : originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A)) :
    (originalCoinducedFunctionRep A).quotientToInvariants S :=
  ⟨originalCoinducedFunction A (fun g => f.val (QuotientGroup.mk g)), by
    intro s
    apply Subtype.ext
    funext g
    change f.val (QuotientGroup.mk (g * (s : G))) = f.val (QuotientGroup.mk g)
    rw [QuotientGroup.mk_mul_of_mem g s.property]⟩

/-- The genuine invariant representation is isomorphic to the original
function representation of the actual quotient group. -/
def originalCoinducedInvariantQuotientIso :
    (originalCoinducedFunctionRep A).quotientToInvariants S ≅
      originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A) :=
  Rep.mkIso {
    toFun := originalInvariantFunctionDescend A S
    invFun := originalInvariantFunctionLift A S
    left_inv f := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv f := by
      apply Subtype.ext
      funext q
      induction q using QuotientGroup.induction_on with
      | H g => rfl
    map_add' f h := by
      apply Subtype.ext
      funext q
      induction q using QuotientGroup.induction_on with
      | H g => rfl
    map_smul' r f := by
      apply Subtype.ext
      funext q
      induction q using QuotientGroup.induction_on with
      | H g => rfl
    isIntertwining' h := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext q
      induction h using QuotientGroup.induction_on with
      | H h =>
        induction q using QuotientGroup.induction_on with
        | H g => rfl }

/-- The original invariant representation and the actual quotient-group
function representation are isomorphic by the explicit inverse maps above. -/
theorem originalCoinducedInvariantQuotient_isomorphic :
    Nonempty ((originalCoinducedFunctionRep A).quotientToInvariants S ≅
      originalCoinducedFunctionRep (Rep.trivial k (G ⧸ S) A)) := by
  exact ⟨originalCoinducedInvariantQuotientIso A S⟩

end
end Dubon2026
