import Dubon2026.RepresentationUnderlyingGroupAction
import Dubon2026.MatrixAdjointSchur
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Exact original coefficient maps on the additive groups of matrix representations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B]

/-- The original matrix representation acts on precisely its original column-vector additive group, in the multiplicative notation of Hopf points. -/
def matrixUnderlyingGroupAction (ρ : G →* GeneralLinearGroup ι A) :
    G →* MulAut (Multiplicative (ι → A)) :=
  representationUnderlyingGroupAction (matrixStandardRepresentation ρ)

/-- Every original column vector is acted on by the original matrix multiplication. -/
theorem matrixUnderlyingGroupAction_apply
    (ρ : G →* GeneralLinearGroup ι A) (g : G) (v : ι → A) :
    matrixUnderlyingGroupAction ρ g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((ρ g).val *ᵥ v) := by
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The original coefficient homomorphism acts on every original vector coordinate. -/
def matrixCoefficientVectorMap (f : A →+* B) :
    Multiplicative (ι → A) →* Multiplicative (ι → B) :=
  AddMonoidHom.toMultiplicative {
    toFun := fun v i => f (v i)
    map_zero' := by ext i; exact map_zero f
    map_add' := by intro v w; ext i; exact map_add f (v i) (w i) }

omit [Fintype ι] [DecidableEq ι] in
/-- The coefficient vector map retains the actual original coordinate values. -/
theorem matrixCoefficientVectorMap_apply (f : A →+* B) (v : ι → A) :
    matrixCoefficientVectorMap f (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (fun i => f (v i)) := by
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- An injective original coefficient map is injective on the same original vector group. -/
theorem matrixCoefficientVectorMap_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (matrixCoefficientVectorMap (ι := ι) f) := by
  intro v w h
  change Multiplicative.toAdd v = Multiplicative.toAdd w
  funext i
  apply hf
  exact congrArg (fun x : Multiplicative (ι → B) => Multiplicative.toAdd x i) h

omit [Fintype ι] [DecidableEq ι] in
/-- A surjective original coefficient map is surjective on the same original vector group, by lifting each original coordinate. -/
theorem matrixCoefficientVectorMap_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (matrixCoefficientVectorMap (ι := ι) f) := by
  intro w
  choose v hv using fun i => hf (Multiplicative.toAdd w i)
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  change (fun i => f (v i)) = Multiplicative.toAdd w
  exact funext hv

/-- Actual change of original matrix coefficients intertwines the same original column-vector actions. The pinned matrix-vector identity preserves every original finite sum and product. -/
theorem matrixCoefficientVectorMap_equivariant (f : A →+* B)
    (ρ : G →* GeneralLinearGroup ι A) (g : G) (v : Multiplicative (ι → A)) :
    matrixCoefficientVectorMap f (matrixUnderlyingGroupAction ρ g v) =
      matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ) g
        (matrixCoefficientVectorMap f v) := by
  exact congrArg Multiplicative.ofAdd
    (funext (RingHom.map_mulVec f (ρ g).val (Multiplicative.toAdd v)))

end
end Dubon2026
