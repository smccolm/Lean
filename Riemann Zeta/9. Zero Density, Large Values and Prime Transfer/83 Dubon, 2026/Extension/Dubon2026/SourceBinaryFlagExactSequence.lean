import Dubon2026.SourceBinaryFlagQuotientRepresentation
import Dubon2026.SourceNativeH1EigenExactSequence

/-! The exact native representation sequence of the original residual binary flag.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> Hecke eigenvalue descent through the coefficient flag. The actual inclusion
and coefficient extraction give the short exact sequence, so its native H1
exactness is a proved consequence of the pinned long exact sequence.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- The actual next-step inclusion and coefficient quotient form the original
residual flag short complex of representations. -/
def sourceBinaryFlagShortComplex : ShortComplex (Rep F (Gamma0 Q)) where
  X₁ := sourceBinaryFlagRep F p Q hpQ n (j + 1)
  X₂ := sourceBinaryFlagRep F p Q hpQ n j
  X₃ := sourceBinaryFlagQuotientRep F p Q hpQ n j
  f := sourceBinaryFlagInclusion F p Q hpQ n j
  g := sourceBinaryFlagQuotientMap F p Q hpQ n j
  zero := by
    ext P
    exact (sourceBinaryFlagGraded_eq_zero_iff F n j _).mpr P.property

/-- Every nonterminal step of the actual residual coefficient flag is a short
exact sequence of native representations; exactness is not supplied as a premise. -/
theorem sourceBinaryFlagShortComplex_shortExact (hj : j ≤ n) :
    (sourceBinaryFlagShortComplex F p Q hpQ n j).ShortExact where
  exact := (forget₂ (Rep F (Gamma0 Q)) (ModuleCat F)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      (sourceBinaryFlagCoefficient_exact F p Q hpQ n j)
  mono_f := (Rep.mono_iff_injective _).mpr (sourceBinaryFlagInclusion_injective F p Q hpQ n j)
  epi_g := (Rep.epi_iff_surjective _).mpr (sourceBinaryFlagQuotientMap_surjective F p Q hpQ n j hj)

/-- The original coefficient-flag inclusion and quotient induce an exact
sequence on actual native H1, with all coefficient exactness conditions proved. -/
theorem sourceBinaryFlagH1_exact (hj : j ≤ n) :
    (groupCohomology.mapShortComplex₂ (sourceBinaryFlagShortComplex F p Q hpQ n j) 1).Exact :=
  groupCohomology.mapShortComplex₂_exact (sourceBinaryFlagShortComplex_shortExact F p Q hpQ n j hj) 1

end
end Dubon2026
