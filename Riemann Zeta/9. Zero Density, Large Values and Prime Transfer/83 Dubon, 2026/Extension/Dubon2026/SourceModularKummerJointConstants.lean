import Dubon2026.SourceModularKummerFiniteOverlap
import Dubon2026.SourceModularKummerConstantsOfFiniteOverlap

/-! DUB-17/18 -> Kummer power lifting -> sum-of-residue-genera inequality.
The intersection of the two actual joint residue charts consists of common
constants. Finite overlap generation is now proved from the actual Kummer
chart basis and is consumed by the existing idempotent-gluing theorem.
No finite-overlap, torsion-annihilator or common-constant certificate is an
input. The subsequent genus inequality and original-field power lifting
remain to be assembled. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra, with no unrelated tower search. -/
local instance jointProvedConstantsResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_chart_constants
    (hNk : (N : kk) ≠ 0) {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fbar} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    ∃ S : Fin q → RegularProlongation A E Fbar,
      Function.Injective (fun i => (S i).integers) ∧
      (∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
        ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
          (S i).residue x =
            modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y) ∧
      ∀ h : Fin q → Fbar,
          h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) →
          h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹ →
          ∃ c : kk, ∀ i, h i = algebraMap kk Fbar c := by
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
  obtain ⟨S, hSinj, hS, ht, hti, hfinite⟩ :=
    modular_kummer_joint_finite_overlap A N hNk hq f hf hw0 hw E
  exact ⟨S, hSinj, hS,
    joint_chart_constants_of_modular_reductions_of_finite_overlap
      A N hNk q E hdegree S hSinj hS ht hti hfinite⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
