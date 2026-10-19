import Dubon2026.FiniteSymmetricMonomialOrbit
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-! Finite-characteristic irreducibility of the actual symmetric SL2
model. Distinct-weight extraction is reused from the existing repository;
two unipotent orbits supply every basis vector. This removes a residual
irreducibility input on the DUB-17 dual-Selmer dependency chain. -/

namespace Dubon2026
noncomputable section
open MvPolynomial Module Matrix
open scoped MatrixGroups

/-- Invertibility of the degree factorial implies that every relevant
binomial coefficient is nonzero in the original coefficient field. -/
theorem choose_cast_ne_zero_of_factorial {K : Type*} [Field K]
    (n : ℕ) (hn : (n.factorial : K) ≠ 0) (i : Fin (n + 1)) :
    (n.choose i.val : K) ≠ 0 := by
  intro hz
  have he := congrArg (Nat.cast : ℕ → K)
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ i.isLt))
  push_cast at he
  rw [hz, zero_mul, zero_mul] at he
  exact hn he.symm

/-- The actual diagonal and two unipotents suffice for irreducibility.
The three explicit stability conditions also apply after coefficient
extension from a finite field, where the group itself stays unchanged. -/
theorem symmetricThreeOperators_submodule_eq_top
    {K : Type*} [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hn : (n.factorial : K) ≠ 0)
    (p : Submodule K (homogeneousSubmodule (Fin 2) K n)) (hpne : p ≠ ⊥)
    (hpDiagonal : ∀ w ∈ p, homogeneousMatrixAction n (ringSL2UnitDiagonal u).val w ∈ p)
    (hpLower : ∀ w ∈ p, homogeneousMatrixAction n (ringLowerUnipotent (1 : K)).val w ∈ p)
    (hpUpper : ∀ w ∈ p, homogeneousMatrixAction n (ringUpperUnipotent (1 : K)).val w ∈ p) : p = ⊤ := by
  classical
  let b := binaryHomogeneousMonomialBasis (R := K) n
  let μ := fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)
  let D := homogeneousMatrixAction n (ringSL2UnitDiagonal u).val
  have hμ : Function.Injective μ := symmetric_unit_weights_injective u n hu
  have hD : ∀ i, D (b i) = μ i • b i := by
    intro i
    have he : (ringSL2UnitDiagonal u).val = Matrix.diagonal ![(u : K), (↑u⁻¹ : K)] := by
      ext j k
      fin_cases j <;> fin_cases k <;> rfl
    change homogeneousMatrixAction n (ringSL2UnitDiagonal u).val (b i) = _
    rw [he]
    exact binaryHomogeneousMonomialBasis_diagonal_ring (u : K) (↑u⁻¹ : K) n i
  have hpD : ∀ w ∈ p, D w ∈ p := hpDiagonal
  have hcomponent (w : homogeneousSubmodule (Fin 2) K n) (hw : w ∈ p)
      (i : Fin (n + 1)) (hi : b.repr w i ≠ 0) : b i ∈ p := by
    have hs : ∑ j, b.repr w j • b j ∈ p := by rwa [b.sum_repr]
    have hm := distinctWeight_component_mem D b μ hμ hD p hpD Finset.univ (b.repr w) hs
    exact (p.smul_mem_iff hi).mp (hm i (Finset.mem_univ i))
  obtain ⟨w, hw, hwn⟩ := p.ne_bot_iff.mp hpne
  obtain ⟨i, hi, _⟩ := distinctWeight_exists_mem D b μ hμ hD p hpD w hw hwn
    (by rw [b.span_eq]; exact Submodule.mem_top)
  have hzero : b 0 ∈ p := by
    apply hcomponent (homogeneousMatrixAction n (ringLowerUnipotent (1 : K)).val (b i))
      (hpLower _ hi) 0
    rw [homogeneous_lowerUnipotent_basis_repr_zero]
    exact one_ne_zero
  have hall : ∀ i, b i ∈ p := by
    intro i
    apply hcomponent (homogeneousMatrixAction n (ringUpperUnipotent (1 : K)).val (b 0))
      (hpUpper _ hzero) i
    rw [homogeneous_upperUnipotent_basis_zero_repr]
    exact choose_cast_ne_zero_of_factorial n hn i
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)

/-- A sufficiently large-order torus element and nonzero degree factorial
make the actual homogeneous SL2 action irreducible over its original field. -/
theorem finiteSymmetricSL2_submodule_eq_top
    {K : Type*} [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hn : (n.factorial : K) ≠ 0)
    (p : Submodule K (homogeneousSubmodule (Fin 2) K n)) (hpne : p ≠ ⊥)
    (hp : ∀ g : SL(2, K), ∀ w ∈ p, homogeneousMatrixAction n g.val w ∈ p) : p = ⊤ :=
  symmetricThreeOperators_submodule_eq_top n u hu hn p hpne
    (hp (ringSL2UnitDiagonal u)) (hp (ringLowerUnipotent 1)) (hp (ringUpperUnipotent 1))

/-- The degree bound discharges the factorial hypothesis in the actual
residual characteristic, including any coefficient-field extension. -/
theorem factorial_cast_ne_zero_of_lt_char
    {K : Type*} [Field K] (q n : ℕ) [Fact q.Prime] [CharP K q] (hn : n < q) :
    (n.factorial : K) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff K q n.factorial).mp hz
  exact (Nat.not_le_of_lt hn) ((Fact.out : q.Prime).dvd_factorial.mp hd)

/-- For a sufficiently large prime field the actual symmetric SL2 action
has no proper nonzero invariant subspace; all numerical witnesses are derived. -/
theorem primeField_symmetricSL2_submodule_eq_top
    (q n : ℕ) [Fact q.Prime] (hn : 2 * n < q - 1)
    (p : Submodule (ZMod q) (homogeneousSubmodule (Fin 2) (ZMod q) n)) (hpne : p ≠ ⊥)
    (hp : ∀ g : SL(2, ZMod q), ∀ w ∈ p, homogeneousMatrixAction n g.val w ∈ p) : p = ⊤ := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  rw [Nat.card_units, Nat.card_zmod] at hu
  apply finiteSymmetricSL2_submodule_eq_top n u _
    (factorial_cast_ne_zero_of_lt_char q n (by omega)) p hpne hp
  rwa [hu]

end
end Dubon2026
