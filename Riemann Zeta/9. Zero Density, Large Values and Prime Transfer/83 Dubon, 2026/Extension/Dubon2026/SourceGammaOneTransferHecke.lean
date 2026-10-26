import Dubon2026.SourceGammaOneSubgroupTraceHecke

/-! DUB-17/18 -> original all-weight adic association -> genuine Gamma1
realization -> surjective-transfer Hecke compatibility. Consume the full
native correspondence square and the original literal-transfer formula
to prove commutation for the actual linear operators. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

/-- The already constructed surjective Gamma1 H1 transfer intertwines the
actual full Hecke correspondences at every prime coprime to the original
level and coefficient modulus. The original homogeneous coefficient action
is retained, and no compatibility premise is assumed. -/
theorem sourceGammaOneConstantH1Transfer_hecke
    (Q N ell w : ℕ) [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    (sourceBinaryHeckeH1 (ZMod N) hell w).comp (sourceGammaOneConstantH1Transfer Q N w) =
      (sourceGammaOneConstantH1Transfer Q N w).comp
        (sourceGammaOneConstantHeckeH1 (ZMod N)
          (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
          (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))) := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  letI : Fintype (Gamma0 Q ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  have h := congrArg (fun z => (sourceGammaOneSubgroupH1Iso Q N w).inv ≫ z)
    (sourceGammaOneSubgroupTrace_hecke_square Q N ell w hell hcop)
  simp only [Iso.inv_hom_id_assoc] at h
  rw [sourceGammaOneConstantH1Transfer_eq_trace]
  unfold sourceBinaryHeckeH1 sourceGammaOneConstantHeckeH1
  rw [sourceHeckeH1Trace_eq_subgroupTrace, sourceHeckeH1Trace_eq_subgroupTrace,
    sourceHeckeH1Trace_eq_subgroupTrace]
  simp only [LinearMap.comp_assoc]
  exact congrArg ModuleCat.Hom.hom h

end
end Dubon2026
