import Dubon2026.SourceHeckeCoefficientMorphism
import Dubon2026.SourceIntegralHeckePrime
import Dubon2026.HeckeTransversalTrace

/-! The existing integral symbol action over the genuine Hecke cosets.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
compatibility. Reuse the proved integral diagonal factorization and the
existing genuine transversal to compare the cohomological coset trace
with the already proved original analytic Hecke operator.
-/

namespace Dubon2026.SourceModularSymbols
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open MvPolynomial TensorProduct
open scoped MatrixGroups

variable (R : Type) [CommRing R] (w Q : ℕ) {p : ℕ} [NeZero p]

/-- The actual diagonal symbol map is invariant under the original upper subgroup. -/
theorem sourceHeckeDiagonalSymbol_invariant (hp : Nat.Prime p)
    (γ : heckeUpperSubgroup Q p) :
    triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w γ.val.val =
      triangularSymbolMap R w (Gamma0 Q) 1 p 0 :=
  triangularSymbolMap_factor (Gamma0 Q) 0 0 γ.val.val
    ⟨(sourceHeckeConjugation hp γ).val, (sourceHeckeConjugation hp γ).property,
      sourceHeckeConjugation_matrix hp γ⟩

/-- The genuine diagonal symbol translate descends to each original Hecke coset. -/
def sourceHeckeSymbolCoset (hp : Nat.Prime p) :
    (Gamma0 Q ⧸ heckeUpperSubgroup Q p) →
      (degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        SourceModularSymbols R (Gamma0 Q) w) :=
  Quotient.lift
    (fun γ => triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w γ.val⁻¹)
    (by
      intro γ δ h
      have hs : γ⁻¹ * δ ∈ heckeUpperSubgroup Q p := QuotientGroup.leftRel_apply.mp h
      have hi := sourceHeckeDiagonalSymbol_invariant R w Q hp
        ⟨(γ⁻¹ * δ)⁻¹, (heckeUpperSubgroup Q p).inv_mem hs⟩
      have he : δ.val⁻¹ = ((γ⁻¹ * δ)⁻¹ : Gamma0 Q).val * γ.val⁻¹ := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      change triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w γ.val⁻¹ =
        triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w δ.val⁻¹
      rw [he, map_mul]
      change _ = _ ∘ₗ (symbolRep R w ((γ⁻¹ * δ)⁻¹ : Gamma0 Q).val ∘ₗ symbolRep R w γ.val⁻¹)
      rw [← LinearMap.comp_assoc, hi])

/-- Evaluation at any representative is the literal original symbol translate. -/
theorem sourceHeckeSymbolCoset_mk (hp : Nat.Prime p) (γ : Gamma0 Q) :
    sourceHeckeSymbolCoset R w Q hp (QuotientGroup.mk γ) =
      triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w γ.val⁻¹ := rfl

/-- The chosen representative gives the same original diagonal symbol translate. -/
theorem sourceHeckeSymbolCoset_out (hp : Nat.Prime p)
    (q : Gamma0 Q ⧸ heckeUpperSubgroup Q p) :
    sourceHeckeSymbolCoset R w Q hp q =
      triangularSymbolMap R w (Gamma0 Q) 1 p 0 ∘ₗ symbolRep R w q.out.val⁻¹ := by
  simpa only [Quotient.out_eq] using sourceHeckeSymbolCoset_mk R w Q hp q.out

end
end Dubon2026.SourceModularSymbols
