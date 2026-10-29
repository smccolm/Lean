import Dubon2026.SourceCurveKummerUnramified
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceGammaOneCurveGeometry
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> original Gamma1 Frobenius/inertia -> injectivity of
prime-to-residue Picard specialization -> Kummer power lifting. Reuse the
native Kummer degree and local-order theorems on the actual Gamma1 field.
A function with prime-divisible orders gives a cover of that prime degree
which is unramified at every actual place. This is the input to its genus
formula, not an assumption of torsion injectivity or good reduction. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve Polynomial IntermediateField
local notation "Qbar" => AlgebraicClosure ℚ
variable (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "FF" => functionFieldOver Δ Qbar

theorem gammaOne_kummer_degree_and_unramified
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
  letI : FiniteDimensional Qbar⟮jCoordinateOver Δ Qbar⟯ FF :=
    finiteDimensional_jCoordinateOver
      (by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]) Qbar
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar q
  have hroots : (primitiveRoots q FF).Nonempty :=
    ⟨algebraMap Qbar FF ζ, (mem_primitiveRoots hq.out.pos).mpr
      (hζ.map_of_injective (algebraMap Qbar FF).injective)⟩
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hq.out hf
  have hdegree : Module.finrank FF E = q := finrank_of_isSplittingField_X_pow_sub_C hroots hirr E
  let α : E := rootOfSplitsXPowSubC (NeZero.pos q) f E
  have hα : α ^ q = algebraMap FF E f := rootOfSplitsXPowSubC_pow f E
  have hαtop : FF⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hroots hirr hα
  letI : FiniteDimensional Qbar⟮algebraMap FF E (jCoordinateOver Δ Qbar)⟯ E :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_algebraMap_mul, hdegree]
      exact Nat.mul_pos Module.finrank_pos hq.out.pos)
  refine ⟨hdegree, fun w => ?_⟩
  exact w.ramificationIndex_eq_one_of_kummer_orders hf hα hαtop hdvd
    (place_residue_bijective_of_finite_coordinate (jCoordinateOver Δ Qbar))
    (place_residue_bijective_of_finite_coordinate (algebraMap FF E (jCoordinateOver Δ Qbar)))

end
end Dubon2026.SourceFunctionField.GammaOne
