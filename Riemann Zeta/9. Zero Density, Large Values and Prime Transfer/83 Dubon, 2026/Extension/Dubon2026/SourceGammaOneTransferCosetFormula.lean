import Dubon2026.SourceGammaOneConstantH1Realization
import Dubon2026.SourceShapiroH1CosetTrace

/-! DUB-17/18 -> original all-weight adic association -> Gamma1 geometric
Hecke comparison. Apply the exact native/coset-trace convention bridge to
the already proved surjective Gamma1 transfer on the original binary module.
The transfer has a literal trace formula, not a chosen surrogate map. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
open scoped Classical

/-- Identify the original restricted coefficient H1 with constant-coefficient
H1 of the actual Gamma1 source, using the proved triviality and range isomorphism. -/
def sourceGammaOneSubgroupH1Iso (Q N w : ℕ) [NeZero N] :
    groupCohomology.H1
      (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
        (sourceBinaryCoefficientRep (ZMod N) Q w)) ≅
    groupCohomology.H1
      (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
        (sourceBinaryCoefficientRep (ZMod N) Q w)) :=
  (groupCohomology.functor (ZMod N) (sourceGammaOneDiagonalHom Q N).range 1).mapIso
      (sourceGammaOneCoefficientTrivialIso Q N w) ≪≫
    originalCohomologyReindex
      (Rep.trivial (ZMod N) (sourceGammaOneDiagonalHom Q N).range
        (sourceBinaryCoefficientRep (ZMod N) Q w))
      (sourceGammaOneRangeEquiv Q N) 1

/-- The already used native isomorphism factors through the same actual
subgroup H1, with no new comparison data. -/
theorem sourceGammaOneConstantH1Iso_factor (Q N w : ℕ) [NeZero N] :
    sourceGammaOneConstantH1Iso Q N w =
      groupCohomology.coindIso
        (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
          (sourceBinaryCoefficientRep (ZMod N) Q w)) 1 ≪≫
        sourceGammaOneSubgroupH1Iso Q N w := rfl

/-- The original surjective Gamma1 transfer is exactly the literal H1
coset trace after the actual subgroup identification. -/
theorem sourceGammaOneConstantH1Transfer_eq_trace (Q N w : ℕ) [NeZero Q] [NeZero N] :
    let H := (sourceGammaOneDiagonalHom Q N).range
    letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
    letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
    sourceGammaOneConstantH1Transfer Q N w =
      (sourceHeckeH1Trace (sourceBinaryCoefficientRep (ZMod N) Q w) H).comp
        (sourceGammaOneSubgroupH1Iso Q N w).toLinearEquiv.symm.toLinearMap := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  dsimp only
  unfold sourceGammaOneConstantH1Transfer
  dsimp only
  rw [sourceNativeCoinductionCounit_eq_cosetTrace,
    sourceHeckeH1Trace_eq_subgroupTrace, sourceGammaOneConstantH1Iso_factor]
  rfl

end
end Dubon2026
