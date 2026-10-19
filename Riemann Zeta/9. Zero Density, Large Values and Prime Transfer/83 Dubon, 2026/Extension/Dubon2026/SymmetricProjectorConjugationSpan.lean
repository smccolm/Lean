import Dubon2026.SymmetricProjectorOrbit
import Dubon2026.FiniteSymmetricAbsoluteIrreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Conjugates of the extremal projector span the original symmetric
matrix algebra. This supplies the nondegenerate regular commuting
trace test in DUB-17, using the existing Burnside descent and weight
projection rather than a separate Lie-module decomposition. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups BigOperators

/-- Matrix units are literal eigenvectors for conjugation by a diagonal
original representation matrix. -/
theorem matrixAdjoint_single_of_diagonal
    {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
    (ρ : G →* GeneralLinearGroup ι K) (g : G) (w : ι → K)
    (hw : (ρ g).val = Matrix.diagonal w) (i j : ι) :
    matrixAdjointRepresentation ρ g (Matrix.single i j 1) =
      (w i * (w j)⁻¹) • Matrix.single i j 1 := by
  have hunit : IsUnit w := Matrix.isUnit_diagonal.mp (hw ▸ (ρ g).isUnit)
  have hiw (k : ι) : Ring.inverse w k = (w k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (congrFun (Ring.inverse_mul_cancel w hunit) k)
  change (ρ g).val * Matrix.single i j 1 * (ρ g⁻¹).val = _
  rw [map_inv, GeneralLinearGroup.coe_inv, hw, Matrix.inv_diagonal]
  ext a b
  by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single, hi, hj,
      Matrix.smul_apply, hiw]

/-- Invariance under the actual symmetric SL2 image and the extremal
projector give every original matrix unit in its first column. -/
theorem symmetricProjector_invariant_contains_column
    {K : Type} [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hfact : (n.factorial : K) ≠ 0)
    (S : Submodule K (Matrix (Fin (n + 1)) (Fin (n + 1)) K))
    (hS : ∀ g : SL(2, K), ∀ X ∈ S,
      matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g X ∈ S)
    (hE : Matrix.single (0 : Fin (n + 1)) 0 1 ∈ S) :
    ∀ i : Fin (n + 1), Matrix.single i 0 1 ∈ S := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  let w := fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)
  have hw0 : w 0 ≠ 0 := by
    change (u : K) ^ 0 * (↑u⁻¹ : K) ^ (n - 0) ≠ 0
    simpa only [pow_zero, Nat.sub_zero, one_mul] using pow_ne_zero n u⁻¹.ne_zero
  have hμ : Function.Injective (fun i => w i * (w 0)⁻¹) := by
    intro i j he
    exact symmetric_unit_weights_injective u n hu (mul_right_cancel₀ (inv_ne_zero hw0) he)
  have he (i : Fin (n + 1)) :
      matrixAdjointRepresentation ψ (ringSL2UnitDiagonal u) (Matrix.single i 0 1) =
        (w i * (w 0)⁻¹) • Matrix.single i 0 1 :=
    matrixAdjoint_single_of_diagonal ψ (ringSL2UnitDiagonal u) w
      (homogeneousSymmetricGL_unitDiagonal u n) i 0
  have hsum : (∑ i : Fin (n + 1), (n.choose i.val : K) • Matrix.single i 0 1) ∈ S := by
    have h := hS (ringUpperUnipotent 1) _ hE
    change (ψ (ringUpperUnipotent 1)).val * Matrix.single 0 0 1 *
      (ψ (ringUpperUnipotent 1)⁻¹).val ∈ S at h
    rwa [symmetricProjector_upper_conjugate] at h
  intro i
  have h := distinctWeight_component_mem (matrixAdjointRepresentation ψ (ringSL2UnitDiagonal u))
    (fun j : Fin (n + 1) => Matrix.single j 0 1) (fun j => w j * (w 0)⁻¹) hμ he
    S (hS (ringSL2UnitDiagonal u)) Finset.univ (fun j => (n.choose j.val : K))
    hsum i (Finset.mem_univ i)
  exact (S.smul_mem_iff (choose_cast_ne_zero_of_factorial n hfact i)).mp h

/-- The actual finite symmetric SL2 conjugation orbit of the extremal
projector has full matrix span, under the explicit image-size and
characteristic bounds already used for residual absolute irreducibility. -/
theorem finiteSymmetric_projector_invariant_eq_top
    {K : Type} [Field K] [Finite K] (q n : ℕ) [Fact q.Prime] [CharP K q]
    (hsize : 2 * n < Nat.card K - 1) (hchar : n < q)
    (S : Submodule K (Matrix (Fin (n + 1)) (Fin (n + 1)) K))
    (hS : ∀ g : SL(2, K), ∀ X ∈ S,
      matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g X ∈ S)
    (hE : Matrix.single (0 : Fin (n + 1)) 0 1 ∈ S) : S = ⊤ := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  have hcol := symmetricProjector_invariant_contains_column n u (hu ▸ hsize)
    (factorial_cast_ne_zero_of_lt_char (K := K) q n hchar) S hS hE
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure K) ψ)) :=
    finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image q n hsize hchar ψ le_rfl
  exact conjugationStable_eq_top_of_column ψ S hS 0 hcol
    (matrixRepresentation_span_eq_top_of_extension (L := AlgebraicClosure K) ψ)

end
end Dubon2026
