import Dubon2026.SourceBinaryPermutationHeckeWords

/-! DUB-17/18 -> original all-weight adic association -> finite geometric
Hecke realization. Derive finiteness for the actual permutation H1 and
its actual Hecke operator image using existing finite group-cohomology
infrastructure and native finite generation of Gamma0. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups

/-- The original prime-power permutation H1 is finite over its actual
coefficient ring at every positive source level. -/
theorem sourceBinaryPrimePowerPermutationH1_finite
    (p n Q w : ℕ) (hp : p.Prime) [NeZero Q] :
    Finite (groupCohomology.H1 (sourceCoefficientPermutationRep
      (sourceBinaryCoefficientRep (ZMod (p ^ (n + 1))) Q w))) := by
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI := sourceBinaryPrimePowerPermutation_finite p n Q w hp
  letI := sourceH1Finite (sourceCoefficientPermutationRep
    (sourceBinaryCoefficientRep (ZMod (p ^ (n + 1))) Q w))
  exact Module.finite_of_finite (ZMod (p ^ (n + 1)))

/-- The actual full prime-word Hecke image on prime-power permutation H1
is finite, with no finite-presentation assumption on the operator algebra. -/
theorem sourceBinaryPrimePowerPermutationHeckeAlgebra_finite
    (p n Q w : ℕ) (hp : p.Prime) [NeZero Q] :
    Finite (sourceBinaryPermutationHeckeAlgebra (ZMod (p ^ (n + 1))) Q w) := by
  let R := ZMod (p ^ (n + 1))
  let M := groupCohomology.H1 (sourceCoefficientPermutationRep
    (sourceBinaryCoefficientRep R Q w))
  letI : Finite M := sourceBinaryPrimePowerPermutationH1_finite p n Q w hp
  letI : Finite (Module.End R M) :=
    Finite.of_injective (fun T : Module.End R M => (T : M → M)) DFunLike.coe_injective
  exact Finite.of_injective
    (fun T : sourceBinaryPermutationHeckeAlgebra R Q w => T.val) Subtype.val_injective

end
end Dubon2026
