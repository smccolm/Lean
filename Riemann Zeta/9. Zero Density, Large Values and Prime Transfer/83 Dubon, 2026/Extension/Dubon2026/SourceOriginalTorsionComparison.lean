import Dubon2026.SourceOriginalTorsionDivisorDescent

/-! DUB-17/18 -> exact original arithmetic torsion -> original Tate module.
The actual arithmetic-to-complex Picard map is bijective on n-torsion for
every nonzero n. Support descent supplies preimages and the proved Picard
injectivity reflects torsion. Consequently the arithmetic count equals the
proved complex n^(2g) count. Here g is explicitly the original complex genus;
any arithmetic-genus identification remains a separate assertion.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem exists_original_torsion_preimage (n : ℕ) (hn : n ≠ 0)
    (x : Pic0 ℂ FC) (hx : x ∈ Pic0.torsion n) :
    ∃ y : originalJZero N, y ∈ Pic0.torsion n ∧ complexPicardMap N y = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨E, f, hf0, hE⟩ := exists_original_torsion_divisor_descent N n hn D hx
  have he0 : Divisor.degree E = 0 := by
    rw [← degree_conorm N E, hE, map_add, degree_originalPrincipalDivisor, add_zero]
    exact D.property
  let E0 : Divisor.degZero (K := Qbar) (F := FQ) := ⟨E, he0⟩
  have hy : complexPicardMap N (Pic0.mk E0) = Pic0.mk D := by
    have heq : conormDegZero N E0 = D +
        ⟨originalPrincipalDivisor N ℂ f, degree_originalPrincipalDivisor N ℂ f⟩ := Subtype.ext hE
    rw [complexPicardMap_mk, heq, map_add, originalPic0_principal_eq_zero N ℂ f hf0, add_zero]
  refine ⟨Pic0.mk E0, ?_, hy⟩
  rw [Pic0.mem_torsion_iff] at hx ⊢
  apply complexPicardMap_injective N
  rw [map_nsmul, hy, hx, map_zero]

theorem original_torsion_cardinality_eq_complex (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion (K := Qbar) (F := FQ) n) =
      Nat.card (Pic0.torsion (K := ℂ) (F := FC) n) := by
  let f : Pic0.torsion (K := Qbar) (F := FQ) n → Pic0.torsion (K := ℂ) (F := FC) n :=
    fun y => ⟨complexPicardMap N y.val, complexPicardMap_mem_torsion N y.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (complexPicardMap_injective N (congrArg Subtype.val h))
    · intro x
      obtain ⟨y, hy, he⟩ := exists_original_torsion_preimage N n hn x.val x.property
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem original_arithmetic_torsion_cardinality_complex_genus (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion (K := Qbar) (F := FQ) n) = n ^ (2 * originalGenus N ℂ) := by
  rw [original_torsion_cardinality_eq_complex N n hn]
  exact OriginalChart.original_complex_torsion_cardinality N n hn

end
end Dubon2026.SourceFunctionField.OriginalConstantField
