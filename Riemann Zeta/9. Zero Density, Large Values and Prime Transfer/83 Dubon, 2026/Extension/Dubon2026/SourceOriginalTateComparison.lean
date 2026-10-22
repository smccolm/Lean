import Dubon2026.SourceTateFunctor
import Dubon2026.SourceOriginalTorsionComparison

/-! DUB-17/18 -> original Jacobian Tate realization -> arithmetic/complex
comparison. The literal arithmetic Picard map contains every finite-order
complex class by the proved torsion descent. It therefore gives a p-adic
linear equivalence on the actual compatible sequences. No comparison premise,
finite-rank premise or genus identification is supplied.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem finite_order_mem_complexPicardMap_range (x : Pic0 ℂ FC)
    (hx : IsOfFinAddOrder x) : x ∈ (complexPicardMap N).range := by
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  obtain ⟨y, _, hy⟩ := exists_original_torsion_preimage N n (Nat.ne_of_gt hn) x
    (Pic0.mem_torsion_iff.mpr hnx)
  exact ⟨y, hy⟩

/-- The p-adic comparison induced by the literal constant-field Picard map. -/
def originalTateComplexEquiv (p : ℕ) [Fact p.Prime] :
    TateModule p (originalJZero N) ≃ₗ[ℤ_[p]] TateModule p (Pic0 ℂ FC) :=
  TateModule.tateEquivOfInjective (complexPicardMap N) (complexPicardMap_injective N)
    (finite_order_mem_complexPicardMap_range N)

theorem originalTateComplexEquiv_apply (p : ℕ) [Fact p.Prime]
    (x : TateModule p (originalJZero N)) (n : ℕ) :
    ((originalTateComplexEquiv N p x : TateModule p (Pic0 ℂ FC)) : ℕ → Pic0 ℂ FC) n =
      complexPicardMap N ((x : ℕ → originalJZero N) n) := rfl

theorem originalTateComplexEquiv_naturality (p : ℕ) [Fact p.Prime]
    (S : originalJZero N →+ originalJZero N) (T : Pic0 ℂ FC →+ Pic0 ℂ FC)
    (h : ∀ x, complexPicardMap N (S x) = T (complexPicardMap N x))
    (x : TateModule p (originalJZero N)) :
    originalTateComplexEquiv N p (TateModule.tateMap p S x) =
      TateModule.tateMap p T (originalTateComplexEquiv N p x) :=
  TateModule.tateMap_naturality (complexPicardMap N) S T h x

end
end Dubon2026.SourceFunctionField.OriginalConstantField
