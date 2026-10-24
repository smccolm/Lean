import Dubon2026.SourceKummerRegularProlongationsR2
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> Picard torsion injectivity -> original-field power lifting.
The literal arithmetic modular Kummer cover supplies q distinct regular
reductions to the literal residue modular field. Restriction and residue
compatibility are proved. No valuation or residue-isomorphism data is supplied. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

/-- The literal coefficient-field algebra avoids irrelevant tower searches. -/
local instance kummerResidueModularAlgebra : Algebra kk Fb :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_regular_reductions
    (hNk : (N : kk) ≠ 0) {q : ℕ} [Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fb} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    ∃ S : Fin q → SourceCurve.RegularProlongation A E Fb,
      Function.Injective (fun i => (S i).integers) ∧
      ∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
        ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
          (S i).residue x =
            modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y := by
  exact SourceCurve.RegularProlongation.exists_kummer_regular_prolongations
    (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) f hf hq hw0 hw E

end
end Dubon2026.SourceFunctionField.GaussReduction
