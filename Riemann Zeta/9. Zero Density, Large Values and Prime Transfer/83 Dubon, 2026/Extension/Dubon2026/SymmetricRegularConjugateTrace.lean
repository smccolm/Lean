import Dubon2026.SymmetricRegularCommutingTrace

/-! Retain the constructed regular torus conjugacy in the commuting
trace test. This is the precise information needed to give DUB-17's
same Selmer-detecting primes their original local dimension. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- The original regular symmetric matrix admits a commuting trace-zero
test pairing nontrivially with every supplied nonzero trace-zero matrix.
Both the regular element and the test are constructed. -/
theorem finiteSymmetric_exists_regular_conjugate_commuting_trace
    {K : Type} [Field K] [Finite K] (q n : ℕ) [Fact q.Prime] [CharP K q]
    (hsize : 2 * n < Nat.card K - 1) (hchar : n + 1 < q)
    (X : matrixTraceZeroSubmodule (Fin (n + 1)) K) (hX : X ≠ 0) :
    ∃ u : Kˣ, orderOf u = Nat.card K - 1 ∧
      ∃ h : SL(2, K),
        let g := h * ringSL2UnitDiagonal u * h⁻¹
      ((homogeneousSymmetricGL n (SpecialLinearGroup.toGL g)).val.charpoly).Separable ∧
      ∃ M : matrixTraceZeroSubmodule (Fin (n + 1)) K,
        (homogeneousSymmetricGL n (SpecialLinearGroup.toGL g)).val * M.val =
          M.val * (homogeneousSymmetricGL n (SpecialLinearGroup.toGL g)).val ∧
        Matrix.trace (X.val * M.val) ≠ 0 := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  let T := matrixAdjointRepresentation ψ
  let E := Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : K)
  have hn : n < q := by omega
  obtain ⟨h, hh⟩ := finiteSymmetric_exists_projector_trace_ne_zero q n hsize hn X.val
    (fun hz => hX (Subtype.ext hz))
  let P := T h E
  have hdim : (Fintype.card (Fin (n + 1)) : K) ≠ 0 := by
    rw [Fintype.card_fin]
    exact fun hz => (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hchar)
      ((CharP.cast_eq_zero_iff K q (n + 1)).mp hz)
  let M : matrixTraceZeroSubmodule (Fin (n + 1)) K :=
    ⟨matrixTraceFreePart P, matrixTraceFreePart_trace hdim P⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  let d := ringSL2UnitDiagonal u
  have hregular : (ψ d).val.charpoly.Separable :=
    homogeneousSymmetricGL_unitDiagonal_separable u n (hu ▸ hsize)
  have hDE : (ψ d).val * E = E * (ψ d).val := by
    rw [show (ψ d).val = Matrix.diagonal
      (fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)) from
        homogeneousSymmetricGL_unitDiagonal u n]
    dsimp only [E]
    rw [← Matrix.diagonal_single]
    exact (Matrix.commute_diagonal _ _).eq
  have hconj : (ψ (h * d * h⁻¹)).val = T h (ψ d).val := by
    change (ψ (h * d * h⁻¹)).val = (ψ h).val * (ψ d).val * (ψ h⁻¹).val
    rw [map_mul, map_mul]
    rfl
  have hcomm : (ψ (h * d * h⁻¹)).val * P = P * (ψ (h * d * h⁻¹)).val := by
    rw [hconj]
    change T h (ψ d).val * T h E = T h E * T h (ψ d).val
    rw [← matrixAdjointRepresentation_mul, hDE, matrixAdjointRepresentation_mul]
  refine ⟨u, hu, h, ?_, M, ?_, ?_⟩
  · change (ψ (h * d * h⁻¹)).val.charpoly.Separable
    rw [hconj]
    change ((ψ h).val * (ψ d).val * (ψ h⁻¹).val).charpoly.Separable
    rw [map_inv, GeneralLinearGroup.coe_inv, Matrix.charpoly_units_conj]
    exact hregular
  · change (ψ (h * d * h⁻¹)).val * matrixTraceFreePart P =
      matrixTraceFreePart P * (ψ (h * d * h⁻¹)).val
    rw [matrixTraceFreePart, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, one_mul, hcomm]
  · change Matrix.trace (X.val * matrixTraceFreePart P) ≠ 0
    rw [matrixTraceZero_traceFreePart_pairing]
    exact hh

end
end Dubon2026
