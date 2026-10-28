import Dubon2026.SourcePeriodParabolicClass
import Dubon2026.SourcePrimitiveH1HeckeRelations

/-! DUB17/18 -> original all-weight association -> original parabolic
finite character. The actual original primitive period class, with the
original homogeneous coefficients, is nonzero and parabolic and has
every original integral Hecke-word eigenvalue. This is a source entry
theorem over C; integral parabolic spanning and finite character descent
are not inferred from it. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
variable {Q : ℕ} [NeZero Q] {k : ℤ}

theorem sourcePrimitive_originalParabolicHeckeWordEigensystem
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ x : sourceParabolicH1 (Gamma0 Q) (sourceBinaryCoefficientRep ℂ Q (k - 2).toNat),
      x ≠ 0 ∧ ∀ a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q),
        FreeAlgebra.lift ℤ (sourceBinaryH1PrimeOperators ℂ Q (k - 2).toNat) a x.val =
          FreeAlgebra.lift ℤ
            (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val) a • x.val := by
  let x := sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm
  obtain ⟨hne, heig⟩ := sourcePrimitive_nonzero_integralModelComplexEigensystem f hk
  refine ⟨⟨x, sourceOriginalBinaryPeriodCohomology_parabolic Q k hk f.toCuspForm⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · intro a
    exact sourceHeckeWord_eigenvector (sourceBinaryH1PrimeOperators ℂ Q (k - 2).toNat)
      (fun p : sourceBinaryHeckePrime Q => cuspCoefficients f.toCuspForm p.val) x
      (fun p => heig p.val p.property.1 p.property.2) a

end
end Dubon2026
