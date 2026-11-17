import Dubon2026.SourceSubfieldProjectorSpan
import Dubon2026.SymmetricRegularConjugateTrace

/-! DUB-17/18 -> regular auxiliary primes -> a regular element from the
actual finite subfield with a nonzero commuting trace test over the ambient
field. Reuse the native regular diagonal and the extended projector span. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- A regular symmetric element of the actual finite subfield detects each
nonzero ambient trace-zero matrix by an ambient commuting trace-zero test. -/
theorem finiteSymmetric_exists_regular_conjugate_commuting_trace_extension
    {K L : Type} [Field K] [Finite K] [Field L]
    (p n : ℕ) [Fact p.Prime] [CharP K p] (θ : K →+* L)
    (hsize : 2 * n < Nat.card K - 1) (hchar : n + 1 < p)
    (X : matrixTraceZeroSubmodule (Fin (n + 1)) L) (hX : X ≠ 0) :
    ∃ u : Kˣ, orderOf u = Nat.card K - 1 ∧
      ∃ h : SL(2, K),
        let g := h * ringSL2UnitDiagonal u * h⁻¹
        let A := GeneralLinearGroup.map θ
          (homogeneousSymmetricGL n (SpecialLinearGroup.toGL g))
        A.val.charpoly.Separable ∧
        ∃ M : matrixTraceZeroSubmodule (Fin (n + 1)) L,
          A.val * M.val = M.val * A.val ∧ Matrix.trace (X.val * M.val) ≠ 0 := by
  letI : CharP L p := charP_of_injective_ringHom θ.injective p
  let ψK := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  let ψ := (GeneralLinearGroup.map θ).comp ψK
  let T := matrixAdjointRepresentation ψ
  let EK := Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : K)
  let E := Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : L)
  have hn : n < p := by omega
  obtain ⟨h, hh⟩ := finiteSymmetric_exists_projector_trace_ne_zero_extension
    p n θ hsize hn X.val (fun hz => hX (Subtype.ext hz))
  have hmap (g : SL(2, K)) : (matrixAdjointRepresentation ψK g EK).map θ = T g E := by
    change ((ψK g).val * EK * (ψK g⁻¹).val).map θ =
      (ψK g).val.map θ * E * (ψK g⁻¹).val.map θ
    simp only [Matrix.map_mul, EK, E, Matrix.map_single, map_one]
  change Matrix.trace (X.val * (matrixAdjointRepresentation ψK h EK).map θ) ≠ 0 at hh
  rw [hmap] at hh
  let P := T h E
  have hdim : (Fintype.card (Fin (n + 1)) : L) ≠ 0 := by
    rw [Fintype.card_fin]
    exact fun hz => (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hchar)
      ((CharP.cast_eq_zero_iff L p (n + 1)).mp hz)
  let M : matrixTraceZeroSubmodule (Fin (n + 1)) L :=
    ⟨matrixTraceFreePart P, matrixTraceFreePart_trace hdim P⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  let d := ringSL2UnitDiagonal u
  have hregularK : (ψK d).val.charpoly.Separable :=
    homogeneousSymmetricGL_unitDiagonal_separable u n (hu ▸ hsize)
  have hregular : (ψ d).val.charpoly.Separable := by
    change ((ψK d).val.map θ).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hregularK.map
  have hDEK : (ψK d).val * EK = EK * (ψK d).val := by
    rw [show (ψK d).val = Matrix.diagonal
      (fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)) from
        homogeneousSymmetricGL_unitDiagonal u n]
    dsimp only [EK]
    rw [← Matrix.diagonal_single]
    exact (Matrix.commute_diagonal _ _).eq
  have hDE : (ψ d).val * E = E * (ψ d).val := by
    have he := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) K => A.map θ) hDEK
    simpa only [Matrix.map_mul, EK, E, Matrix.map_single, map_one] using he
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
