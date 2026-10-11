import Dubon2026.MatrixCoefficientPointActions
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! # A genuine equivariant spanning map for finite target coefficients -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped BigOperators

variable {G ι A B : Type*} [Group G] [CommRing A] [CommRing B]
  [Fintype B]

/-- The actual finite target coefficients span their original vector representation from copies of the original source vectors. -/
def finiteCoefficientVectorSpanningMap (f : A →+* B) :
    (B → Multiplicative (ι → A)) →* Multiplicative (ι → B) where
  toFun v := Multiplicative.ofAdd (fun i => ∑ b : B, b * f (Multiplicative.toAdd (v b) i))
  map_one' := by
    change (fun i => ∑ b : B, b * f (0 : A)) = (0 : ι → B)
    ext i
    simp only [map_zero, mul_zero, Finset.sum_const_zero, Pi.zero_apply]
  map_mul' v w := by
    change (fun i => ∑ b : B, b * f (Multiplicative.toAdd (v b) i +
      Multiplicative.toAdd (w b) i)) = _
    ext i
    change (∑ b : B, b * f (Multiplicative.toAdd (v b) i +
      Multiplicative.toAdd (w b) i)) =
      (∑ b : B, b * f (Multiplicative.toAdd (v b) i)) +
        (∑ b : B, b * f (Multiplicative.toAdd (w b) i))
    simp only [map_add, mul_add, Finset.sum_add_distrib]

/-- Each actual target vector lifts using its own coordinate values as members of the finite coefficient index set. -/
theorem finiteCoefficientVectorSpanningMap_surjective (f : A →+* B) :
    Function.Surjective (finiteCoefficientVectorSpanningMap (ι := ι) f) := by
  classical
  intro w
  refine ⟨fun b => Multiplicative.ofAdd (fun i =>
    if Multiplicative.toAdd w i = b then (1 : A) else 0), ?_⟩
  change (fun i => ∑ b : B, b * f (if Multiplicative.toAdd w i = b then 1 else 0)) =
    Multiplicative.toAdd w
  ext i
  simp

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The original matrix action commutes with the actual coefficient spanning sum; both finite indices and every original matrix entry are preserved. -/
theorem finiteCoefficientVectorSpanning_mulVec (f : A →+* B)
    (M : Matrix ι ι A) (v : B → ι → A) :
    (fun i => ∑ b : B, b * f ((M *ᵥ v b) i)) =
      M.map f *ᵥ (fun i => ∑ b : B, b * f (v b i)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The actual surjective spanning map intertwines the original matrix action on every source copy with its genuine target coefficient change. -/
theorem finiteCoefficientVectorSpanningMap_equivariant (f : A →+* B)
    (ρ : G →* GeneralLinearGroup ι A) (g : G) (v : B → Multiplicative (ι → A)) :
    finiteCoefficientVectorSpanningMap f (fun b => matrixUnderlyingGroupAction ρ g (v b)) =
      matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ) g
        (finiteCoefficientVectorSpanningMap f v) := by
  exact congrArg Multiplicative.ofAdd
    (finiteCoefficientVectorSpanning_mulVec f (ρ g).val (fun b => Multiplicative.toAdd (v b)))

end
end Dubon2026
