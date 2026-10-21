import Dubon2026.SourceLevelProjectiveLine
import Dubon2026.SL2Reduction

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

section QuotientBorel
variable {R : Type*} [CommRing R]

private theorem isUnimodularRow_firstCol (A : SpecialLinearGroup (Fin 2) R) :
    IsCoprime (A.1 0 0) (A.1 1 0) := by
  refine ⟨A.1 1 1, -A.1 0 1, ?_⟩
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have h := A.2; rwa [Matrix.det_fin_two] at h
  linear_combination hdet

private def firstColumnClass (A : SpecialLinearGroup (Fin 2) R) : ProjectiveLine R :=
  ⟦⟨(A.1 0 0, A.1 1 0), isUnimodularRow_firstCol A⟩⟧

private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
  constructor
  · intro hAB
    obtain ⟨u, h1, h2⟩ := Quotient.exact hAB
    have h1' : (u : R) * A.1 0 0 = B.1 0 0 := h1
    have h2' : (u : R) * A.1 1 0 = B.1 1 0 := h2
    show (A⁻¹ * B).1 1 0 = 0
    change ((A⁻¹).val * B.val) 1 0 = 0
    rw [SpecialLinearGroup.SL2_inv_expl A,
      (Matrix.two_mul_expl _ B.1).2.2.1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← h1', ← h2']; ring
  · intro hAB
    have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
    have hC10 : (A⁻¹ * B).1 1 0 = 0 := hAB
    have hCdet : (A⁻¹ * B).1 0 0 * (A⁻¹ * B).1 1 1 = 1 := by
      have h := (A⁻¹ * B).2; rw [Matrix.det_fin_two, hC10] at h; linear_combination h
    have hB00 : B.1 0 0 = A.1 0 0 * (A⁻¹ * B).1 0 0 + A.1 0 1 * (A⁻¹ * B).1 1 0 := by
      calc
        B.val 0 0 = (A * (A⁻¹ * B)).val 0 0 := congrArg (fun M : SL(2, R) => M.val 0 0) hB
        _ = _ := (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).1
    have hB10 : B.1 1 0 = A.1 1 0 * (A⁻¹ * B).1 0 0 + A.1 1 1 * (A⁻¹ * B).1 1 0 := by
      calc
        B.val 1 0 = (A * (A⁻¹ * B)).val 1 0 := congrArg (fun M : SL(2, R) => M.val 1 0) hB
        _ = _ := (Matrix.two_mul_expl A.1 (A⁻¹ * B).1).2.2.1
    refine Quotient.sound ⟨⟨(A⁻¹ * B).1 0 0, (A⁻¹ * B).1 1 1, hCdet,
      (mul_comm _ _).trans hCdet⟩, ?_, ?_⟩
    · show (A⁻¹ * B).1 0 0 * A.1 0 0 = B.1 0 0; rw [hB00, hC10]; ring
    · show (A⁻¹ * B).1 0 0 * A.1 1 0 = B.1 1 0; rw [hB10, hC10]; ring

private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
  have hwd : ∀ A B : SpecialLinearGroup (Fin 2) R, QuotientGroup.leftRel (borel R) A B →
      firstColumnClass A = firstColumnClass B := by
    intro A B hAB
    rw [QuotientGroup.leftRel_apply] at hAB
    exact (firstColumnClass_eq_iff A B).mpr hAB
  refine Nat.card_eq_of_bijective (fun q => Quotient.liftOn' q firstColumnClass hwd) ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂' q q' ?_
    intro A B hAB
    have hAB' : firstColumnClass A = firstColumnClass B := hAB
    exact (QuotientGroup.eq).mpr ((firstColumnClass_eq_iff A B).mp hAB')
  · intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, y, hxy⟩ := v.2
    refine ⟨QuotientGroup.mk ⟨!![v.1.1, -y; v.1.2, x], by
      rw [Matrix.det_fin_two_of]; linear_combination hxy⟩, ?_⟩
    show firstColumnClass _ = ⟦v⟧
    refine Quotient.sound ⟨1, ?_, ?_⟩
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 0 0 = v.1.1; simp
    · show (1 : R) * !![v.1.1, -y; v.1.2, x] 1 0 = v.1.2; simp

end QuotientBorel

private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
  constructor
  · intro hA
    show (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0; simpa using hA
  · intro hA
    have hA' : (Int.castRingHom (ZMod N)).mapMatrix A.1 1 0 = 0 := hA; simpa using hA'

/-- The actual level index is the cardinality of primitive residue points modulo units. -/
theorem gamma0_index_projective (N : ℕ) [NeZero N] :
    (Gamma0 N).index = Nat.card (ProjectiveLine (ZMod N)) := by
  have h1 : (Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _ (SL2Reduction.SL2_reduction_surjective N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel]

end
end Dubon2026.SourceLevelProjective
