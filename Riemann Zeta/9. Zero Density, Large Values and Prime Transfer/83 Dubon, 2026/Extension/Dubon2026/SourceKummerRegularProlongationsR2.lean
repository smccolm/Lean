import Dubon2026.SourceKummerExtendingValuations
import Dubon2026.SourceReductionValuationIncomparability
import Dubon2026.SourceValuationResidueDegreeOneR2
import Dubon2026.SourceReductionResidueExtension

/-! DUB-17/18 -> Picard torsion injectivity -> original-field power lifting.
The prime Kummer cover has q distinct actual regular reductions with the
original residue field and compatible residue maps. Native Kummer degree,
finite valuation approximation, and constant normalization discharge the
residue-degree and incomparability conditions. The genus inequality remains
the next mathematical obligation. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open Polynomial IsLocalRing
variable {L F Fbar : Type*} [Field L] [IsAlgClosed L] [CharZero L]
  {A : ValuationSubring L} [Field F] [Algebra L F]
  [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_kummer_regular_prolongations (R : RegularProlongation A F Fbar)
    {q : ℕ} [hqp : Fact q.Prime] (f : R.integers) (hf : ∀ g : F, g ^ q ≠ (f : F))
    (hq : (q : ResidueField A) ≠ 0) {w : Fbar} (hw0 : w ≠ 0) (hw : w ^ q = R.residue f)
    (E : Type*) [Field E] [Algebra F E] [Algebra L E] [IsScalarTower L F E]
    [IsSplittingField F E (X ^ q - C (f : F))] :
    ∃ S : Fin q → RegularProlongation A E Fbar,
      Function.Injective (fun i => (S i).integers) ∧
      ∀ i, (S i).integers.comap (algebraMap F E) = R.integers ∧
        ∀ (x : (S i).integers) (y : R.integers), algebraMap F E y = x →
          (S i).residue x = R.residue y := by
  classical
  letI : NeZero q := ⟨hqp.out.ne_zero⟩
  letI : NeZero (q : L) := ⟨Nat.cast_ne_zero.mpr hqp.out.ne_zero⟩
  letI : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ q - C (f : F))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
  have hroots : (primitiveRoots q F).Nonempty :=
    ⟨algebraMap L F ζ, (mem_primitiveRoots hqp.out.pos).mpr
      (hζ.map_of_injective (algebraMap L F).injective)⟩
  have hdeg : Module.finrank F E = q := finrank_of_isSplittingField_X_pow_sub_C hroots
    (X_pow_sub_C_irreducible_of_prime hqp.out hf) E
  obtain ⟨V, hinj, hV⟩ := R.exists_kummer_extending_valuations f hf hq hw0 hw E
  have hinc : ∀ i j, V i ≤ V j → i = j := fun i j hij =>
    hinj (R.extending_valuation_eq_of_le (hV i).1 (hV j).1 hij)
  have hf1 (i : Fin q) (x : E) (hx : x ∈ V i) :
      ∃ y ∈ R.integers, x - algebraMap F E y ∈ (V i).nonunits :=
    ValuationApproximation.residue_degree_one_of_finrank_le_card R.integers V hinc
      (fun j => (hV j).1) (by simp [hdeg]) i x hx
  choose S hSV hS using fun i => R.exists_regularProlongation_of_residue_degree_one
    (V i) (hV i).1 (hf1 i)
  refine ⟨S, fun i j hij => hinj ?_, fun i => ⟨?_, hS i⟩⟩
  · exact (hSV i).symm.trans (hij.trans (hSV j))
  · rw [hSV]
    exact (hV i).1

end
end Dubon2026.SourceCurve.RegularProlongation
