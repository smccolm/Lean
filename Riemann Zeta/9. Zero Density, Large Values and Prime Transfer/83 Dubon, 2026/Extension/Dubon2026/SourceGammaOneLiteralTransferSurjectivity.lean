import Dubon2026.SourceGammaOneTransferCosetFormula

/-! DUB-17/18 -> all-weight adic association -> Gamma1 geometric Hecke
comparison. Consume the exact native/literal transfer identity and the
already proved binary H1 lifting theorem on the same actual source. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
open scoped Classical

/-- The literal trace from the exact constant-coefficient Gamma1 source
is surjective, as a consequence of the proved original native transfer. -/
theorem sourceGammaOne_literalTrace_surjective
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    let H := (sourceGammaOneDiagonalHom Q N).range
    letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
    letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
    Function.Surjective
      ((sourceHeckeH1Trace (sourceBinaryCoefficientRep (ZMod N) Q w) H).comp
        (sourceGammaOneSubgroupH1Iso Q N w).toLinearEquiv.symm.toLinearMap) := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  dsimp only
  rw [← sourceGammaOneConstantH1Transfer_eq_trace]
  exact sourceGammaOneConstantH1Transfer_surjective Q N w h6

end
end Dubon2026
