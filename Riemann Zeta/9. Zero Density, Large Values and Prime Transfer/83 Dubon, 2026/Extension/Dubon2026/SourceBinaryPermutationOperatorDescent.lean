import Dubon2026.SourceBinaryPermutationOperatorKernel
import Dubon2026.SourceFiniteOperatorCharacterDescent

/-! DUB-17/18 -> original all-weight adic association -> finite geometric
Hecke realization. The actual permutation Hecke image surjects onto the
actual original finite tensor-operator image. Native ring-map descent
uses the proved operator relation, retaining every prime word. -/
namespace Dubon2026
noncomputable section

/-- The actual permutation-word quotient kernel is contained in the
kernel of the original finite tensor-operator word action. -/
theorem sourceBinaryPermutationHeckeWord_modulus_kernel
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    RingHom.ker (FreeAlgebra.lift ℤ
      (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w)).rangeRestrict.toRingHom ≤
    RingHom.ker (((sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))).rangeRestrict).comp
      (sourceBinaryH1HeckeWord Q w)).toRingHom := by
  intro a ha
  apply RingHom.mem_ker.mpr
  apply Subtype.ext
  exact sourceBinaryPermutationHeckeWord_modulus_zero p n Q w hp hlarge a
    (congrArg Subtype.val (RingHom.mem_ker.mp ha))

/-- The canonical comparison from actual finite permutation H1 Hecke
operators to the original finite tensor-operator image. -/
def sourceBinaryPermutationToModulus
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    sourceBinaryPermutationHeckeAlgebra (ZMod (p ^ (n + 1))) Q w →+*
      sourceBinaryH1ModulusOperatorAlgebra Q w (p ^ (n + 1)) := by
  have hker := sourceBinaryPermutationHeckeWord_modulus_kernel p n Q w hp hlarge
  exact sourceFiniteOperatorCharacterDescend
    (A := FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (B := sourceBinaryPermutationHeckeAlgebra (ZMod (p ^ (n + 1))) Q w)
    (C := sourceBinaryH1ModulusOperatorAlgebra Q w (p ^ (n + 1)))
    (FreeAlgebra.lift ℤ
      (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w)).rangeRestrict.toRingHom
    (FreeAlgebra.lift ℤ
      (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w)).rangeRestrict_surjective
    (((sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))).rangeRestrict).comp
      (sourceBinaryH1HeckeWord Q w)).toRingHom hker

/-- The canonical comparison preserves the whole original prime-word action. -/
theorem sourceBinaryPermutationToModulus_comp
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    (sourceBinaryPermutationToModulus p n Q w hp hlarge).comp
      (FreeAlgebra.lift ℤ
        (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w)).rangeRestrict.toRingHom =
      (((sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))).rangeRestrict).comp
        (sourceBinaryH1HeckeWord Q w)).toRingHom :=
  sourceFiniteOperatorCharacterDescend_comp _ _ _ _

/-- Every original finite tensor operator is realized by an actual
permutation H1 Hecke operator, with no extra presentation hypothesis. -/
theorem sourceBinaryPermutationToModulus_surjective
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    Function.Surjective (sourceBinaryPermutationToModulus p n Q w hp hlarge) := by
  intro T
  obtain ⟨S, hS⟩ :=
    (sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))).rangeRestrict_surjective T
  obtain ⟨a, ha⟩ := sourceBinaryH1HeckeWord_surjective Q w S
  refine ⟨(FreeAlgebra.lift ℤ
    (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w)).rangeRestrict a, ?_⟩
  have h := RingHom.congr_fun (sourceBinaryPermutationToModulus_comp p n Q w hp hlarge) a
  change sourceBinaryPermutationToModulus p n Q w hp hlarge _ =
    (sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))).rangeRestrict
      (sourceBinaryH1HeckeWord Q w a) at h
  exact h.trans (by rw [ha, hS])

end
end Dubon2026
