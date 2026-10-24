import Dubon2026.SourceCurveKummerUnramified
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceModularCoefficientCurve
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual association -> original Frobenius/inertia ->
Picard torsion injectivity -> original-field power lifting. A nontrivial
prime Kummer cover of the actual arithmetic modular field, defined by a
function whose orders are divisible by that prime, has the exact prime
degree and ramification index one at every place. Actual finite-coordinate
residue theorems discharge both residue-field hypotheses. The genus and
extending-reduction comparison remain necessary for the lifting argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial IntermediateField
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar

theorem modular_kummer_degree_and_unramified
    {q : ℕ} [hq : Fact q.Prime] {f : FF} (hf : ∀ g : FF, g ^ q ≠ f)
    (hdvd : ∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C f)] :
    letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C f)
    Module.finrank FF E = q ∧ ∀ w : Place Qbar E, w.ramificationIndex (F := FF) = 1 := by
  letI : CharZero FF := charZero_of_injective_algebraMap (algebraMap Qbar FF).injective
  letI : NeZero q := ⟨hq.out.ne_zero⟩
  letI : NeZero (q : Qbar) := ⟨Nat.cast_ne_zero.mpr hq.out.ne_zero⟩
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C f)
  letI hdim : FiniteDimensional Qbar⟮jCoeff N Qbar⟯ FF := finiteDimensional_coeff_field N Qbar
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar q
  have hroots : (primitiveRoots q FF).Nonempty :=
    ⟨algebraMap Qbar FF ζ, (mem_primitiveRoots hq.out.pos).mpr
      (hζ.map_of_injective (algebraMap Qbar FF).injective)⟩
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hq.out hf
  have hdegree : Module.finrank FF E = q := finrank_of_isSplittingField_X_pow_sub_C hroots hirr E
  let α : E := rootOfSplitsXPowSubC (NeZero.pos q) f E
  have hα : α ^ q = algebraMap FF E f := rootOfSplitsXPowSubC_pow f E
  have hαtop : FF⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hroots hirr hα
  letI hdimE : FiniteDimensional Qbar⟮algebraMap FF E (jCoeff N Qbar)⟯ E :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_algebraMap_mul, hdegree]
      exact Nat.mul_pos Module.finrank_pos hq.out.pos)
  refine ⟨hdegree, fun w => ?_⟩
  exact w.ramificationIndex_eq_one_of_kummer_orders hf hα hαtop hdvd
    (fun P => place_residue_bijective_of_finite_coordinate (jCoeff N Qbar) P)
    (fun Q => place_residue_bijective_of_finite_coordinate (algebraMap FF E (jCoeff N Qbar)) Q)

end
end Dubon2026.SourceFunctionField
