import Dubon2026.SourceKummerCenterExtensions
import Dubon2026.SourceReductionAlgebraicNormalization
import Dubon2026.SourceValuationResidueAlgClosed
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
extending regular reductions. The q distinct reduced roots produce q
distinct actual extending valuations, each with proved constant-field
normalization. The residue-field identifications needed to turn these
valuations into regular prolongations remain a separate obligation. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open Polynomial IsLocalRing
variable {L F Fbar : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_kummer_extending_valuations (R : RegularProlongation A F Fbar)
    {q : ℕ} [hqp : Fact q.Prime] (f : R.integers) (hf : ∀ g : F, g ^ q ≠ (f : F))
    (hq : (q : ResidueField A) ≠ 0) {w : Fbar} (hw0 : w ≠ 0) (hw : w ^ q = R.residue f)
    (E : Type*) [Field E] [Algebra F E] [Algebra L E] [IsScalarTower L F E]
    [IsSplittingField F E (X ^ q - C (f : F))] :
    ∃ V : Fin q → ValuationSubring E, Function.Injective V ∧
      ∀ i, (V i).comap (algebraMap F E) = R.integers ∧
        ∀ x : E, x ≠ 0 → ∃ c : L, (V i).valuation (c • x) = 1 := by
  classical
  letI : NeZero q := ⟨hqp.out.ne_zero⟩
  letI : NeZero (q : ResidueField A) := ⟨hq⟩
  letI : IsAlgClosed (ResidueField A) := SourceEllipticReduction.residueField_isAlgClosed A
  letI : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ q - C (f : F))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) q
  let ξ := algebraMap (ResidueField A) Fbar ζ
  have hξ : IsPrimitiveRoot ξ q := hζ.map_of_injective (algebraMap (ResidueField A) Fbar).injective
  let s : Fin q → Fbar := fun i => ξ ^ (i : ℕ) * w
  have hs (i : Fin q) : s i ^ q = R.residue f := by
    change (ξ ^ (i : ℕ) * w) ^ q = _
    rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) q, pow_mul, hξ.pow_eq_one, one_pow, one_mul, hw]
  have hinj : Function.Injective s := by
    intro i j hij
    exact Fin.ext (hξ.pow_inj i.isLt j.isLt (mul_right_cancel₀ hw0 hij))
  let α : E := rootOfSplitsXPowSubC hqp.out.pos (f : F) E
  have hα : α ^ q = algebraMap F E (f : F) := rootOfSplitsXPowSubC_pow (f : F) E
  choose V hV using fun i : Fin q => R.exists_kummerCenter f hf hα (hs i)
  refine ⟨V, ?_, fun i => ⟨(hV i).comap_eq, fun x hx => ?_⟩⟩
  · intro i j hij
    by_contra hne
    exact (hV i).ne_of_residue_ne (hV j) (fun h => hne (hinj h)) hij
  · exact R.exists_smul_valuation_eq_one_of_isIntegral (V i) (hV i).comap_eq hx
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

end
end Dubon2026.SourceCurve.RegularProlongation
