import Dubon2026.SourceModularJointGenusInequality

/-! DUB-17/18 -> prime-to-characteristic Picard torsion injectivity ->
original-field Kummer power lifting. The actual q modular residue copies
have total genus at most the original Kummer field genus. Their regular
reductions, finite overlap, common constants, joint pole-space comparison,
degree equality and genus identification are all derived in this consumer.
The contradiction with the unramified genus identity remains to assemble. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra, with no unrelated tower search. -/
local instance jointGenusBoundResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_genus_inequality
    (hNk : (N : kk) ≠ 0) {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fbar} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    q * genusFF kk Fbar ≤ genusFF Qbar E := by
  classical
  letI : NeZero q := ⟨hqp.out.ne_zero⟩
  letI : NeZero (q : Qbar) := ⟨Nat.cast_ne_zero.mpr hqp.out.ne_zero⟩
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C (f : FF))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar q
  have hroots : (primitiveRoots q FF).Nonempty :=
    ⟨algebraMap Qbar FF ζ, (mem_primitiveRoots hqp.out.pos).mpr
      (hζ.map_of_injective (algebraMap Qbar FF).injective)⟩
  have hdegree : Module.finrank FF E = q := finrank_of_isSplittingField_X_pow_sub_C hroots
    (X_pow_sub_C_irreducible_of_prime hqp.out hf) E
  obtain ⟨S, hSinj, hS, hconst⟩ :=
    modular_kummer_joint_chart_constants A N hNk hq f hf hw0 hw E
  exact joint_genus_inequality_of_common_constants A N hNk q E hdegree S hSinj hS hconst

end
end Dubon2026.SourceFunctionField.GaussReduction
