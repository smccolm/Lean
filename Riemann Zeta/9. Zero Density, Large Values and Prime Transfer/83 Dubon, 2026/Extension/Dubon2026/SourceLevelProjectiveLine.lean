import Dubon2026.SourceFiniteCuspBoundary
import Mathlib.Tactic

/-! DUB-17/18 -> residual modular Galois association -> parabolic
Hecke realization -> matching period dimension bounds -> actual level index.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Definitions/Def_ModularCurve_ProjectiveLine.lean
and P2M/Sol/S_ModularCurve_Gamma0_index.lean. Pinned IsCoprime and the
already proved integral SL2 reduction replace the external duplicate
unimodularity predicate and coprime-lifting proof.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section
open Matrix CongruenceSubgroup Finset
open scoped MatrixGroups

section ProjectiveLine
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Primitive pairs with the pinned coprimality predicate. -/
abbrev UnimodularRow (R : Type*) [CommRing R] := { v : R × R // IsCoprime v.1 v.2 }

/-- Unit scaling identifies representatives of a primitive projective point. -/
instance unimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R) where
  r v w := ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
  iseqv := by
    refine ⟨fun v => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro v w z ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩
      exact ⟨u' * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩

/-- Primitive pairs modulo actual unit scaling over the coefficient ring. -/
def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)

instance instFiniteProjectiveLine [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

/-- Map primitive projective points along the original coefficient homomorphism. -/
def ProjectiveLine.map (f : R →+* S) : ProjectiveLine R → ProjectiveLine S :=
  Quotient.lift (fun v => (⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ : ProjectiveLine S)) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Quotient.sound ⟨⟨f u, f ↑u⁻¹, ?_, ?_⟩, ?_, ?_⟩
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [← map_mul, Units.inv_mul, map_one]
    · show f ↑u * f v.1.1 = f w.1.1
      rw [← map_mul, h1]
    · show f ↑u * f v.1.2 = f w.1.2
      rw [← map_mul, h2]

@[simp]
theorem ProjectiveLine.map_mk (f : R →+* S) (v : UnimodularRow R) :
    ProjectiveLine.map f ⟦v⟧ = ⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ :=
  rfl

end ProjectiveLine

section Borel

variable {R : Type*} [CommRing R]

/-- The actual upper triangular subgroup of the special linear group. -/
def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
  one_mem' := by
    show (1 : SpecialLinearGroup (Fin 2) R).1 1 0 = 0
    simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    show (A * B).1 1 0 = 0
    change (A.val * B.val) 1 0 = 0
    rw [(Matrix.two_mul_expl A.1 B.1).2.2.1, hA, hB]
    ring
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    show (A⁻¹).1 1 0 = 0
    rw [SpecialLinearGroup.SL2_inv_expl A]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, neg_eq_zero]
    exact hA

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel


end
end Dubon2026.SourceLevelProjective
