import Dubon2026.SourceOriginalInertiaGaussAction

/-! DUB-17/18 -> original inertia on Picard classes -> actual reduction
place compatibility. The original arithmetic action preserves the two
integral charts used in the proved reduction-place construction. Native
adjoin induction and IsIntegral.map_of_comp_eq transport the monic equation;
no additional integral-closure or divisor-rigidity framework is introduced. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) (τ : Qbar ≃ₐ[ℚ] Qbar)
local notation "F" => modularFunctionFieldCoeff N Qbar

theorem coefficientArithmeticRingAut_constants (a : Qbar) :
    coefficientArithmeticRingAut N τ (algebraMap Qbar F a) =
      algebraMap Qbar F (τ a) := by
  apply Subtype.ext
  exact coeffMap_original_constants τ a

theorem coefficientArithmeticRingAut_j :
    coefficientArithmeticRingAut N τ (jCoeff N Qbar) = jCoeff N Qbar := by
  apply Subtype.ext
  exact map_jqModC (τ : Qbar →+* Qbar)

theorem coefficientArithmeticRingAut_mem_adjoin
    (y : F) (hy : coefficientArithmeticRingAut N τ y = y)
    {f : F} (hf : f ∈ Algebra.adjoin Qbar ({y} : Set F)) :
    coefficientArithmeticRingAut N τ f ∈ Algebra.adjoin Qbar ({y} : Set F) := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [hy]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap a =>
    rw [coefficientArithmeticRingAut_constants]
    exact (Algebra.adjoin Qbar ({y} : Set F)).algebraMap_mem _
  | add x z _ _ hx hz => simpa only [map_add] using add_mem hx hz
  | mul x z _ _ hx hz => simpa only [map_mul] using mul_mem hx hz

/-- Restriction of the actual arithmetic action to a fixed-coordinate chart algebra. -/
def coefficientArithmeticChartHom (y : F) (hy : coefficientArithmeticRingAut N τ y = y) :
    Algebra.adjoin Qbar ({y} : Set F) →+* Algebra.adjoin Qbar ({y} : Set F) where
  toFun f := ⟨coefficientArithmeticRingAut N τ f.val,
    coefficientArithmeticRingAut_mem_adjoin N τ y hy f.property⟩
  map_one' := Subtype.ext (map_one (coefficientArithmeticRingAut N τ))
  map_mul' f g := Subtype.ext (map_mul (coefficientArithmeticRingAut N τ) f.val g.val)
  map_zero' := Subtype.ext (map_zero (coefficientArithmeticRingAut N τ))
  map_add' f g := Subtype.ext (map_add (coefficientArithmeticRingAut N τ) f.val g.val)

theorem coefficientArithmeticRingAut_isIntegral
    (y : F) (hy : coefficientArithmeticRingAut N τ y = y)
    {f : F} (hf : IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) f) :
    IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) (coefficientArithmeticRingAut N τ f) :=
  IsIntegral.map_of_comp_eq (coefficientArithmeticChartHom N τ y hy)
    (coefficientArithmeticRingAut N τ).toRingHom (by ext x; rfl) hf

theorem coefficientArithmetic_integral_charts (f : F) :
    (IsIntegral (Algebra.adjoin Qbar ({jCoeff N Qbar} : Set F)) f →
      IsIntegral (Algebra.adjoin Qbar ({jCoeff N Qbar} : Set F)) (coefficientArithmeticRingAut N τ f)) ∧
    (IsIntegral (Algebra.adjoin Qbar ({(jCoeff N Qbar)⁻¹} : Set F)) f →
      IsIntegral (Algebra.adjoin Qbar ({(jCoeff N Qbar)⁻¹} : Set F)) (coefficientArithmeticRingAut N τ f)) := by
  refine ⟨coefficientArithmeticRingAut_isIntegral N τ _ (coefficientArithmeticRingAut_j N τ),
    coefficientArithmeticRingAut_isIntegral N τ _ ?_⟩
  rw [map_inv₀, coefficientArithmeticRingAut_j]

end
end Dubon2026.SourceFunctionField.GaussReduction
