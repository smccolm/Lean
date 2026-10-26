import Dubon2026.SourceGammaOneCohomologyTransfer
import Dubon2026.SourceBinaryCohomologyChange
import Dubon2026.OriginalGroupCohomologyReindex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-cohomology realization. Native Shapiro, the proved triviality on
the actual Gamma1 image and existing group-cohomology reindexing identify
the coinduced source with constant-coefficient H1 of the exact Gamma1
group. The resulting transfer is onto without an assumed comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
open scoped Classical

/-- The concrete injective Gamma1 map identifies its actual source group
with its image in the original Gamma0 group. -/
def sourceGammaOneRangeEquiv (Q N : ℕ) [NeZero N] :
    Gamma1 (Q * N ^ 2) ≃* (sourceGammaOneDiagonalHom Q N).range :=
  MulEquiv.ofBijective (sourceGammaOneDiagonalHom Q N).rangeRestrict
    ⟨fun _ _ h => sourceGammaOneDiagonalHom_injective Q N (congrArg Subtype.val h),
      (sourceGammaOneDiagonalHom Q N).rangeRestrict_surjective⟩

/-- The actual coinduced binary coefficient H1 is the constant-coefficient
H1 of the explicit Gamma1 cover, on the same original vector space. -/
def sourceGammaOneConstantH1Iso (Q N w : ℕ) [NeZero N] :
    groupCohomology.H1
      (Rep.coind (sourceGammaOneDiagonalHom Q N).range.subtype
        (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
          (sourceBinaryCoefficientRep (ZMod N) Q w))) ≅
    groupCohomology.H1
      (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
        (sourceBinaryCoefficientRep (ZMod N) Q w)) :=
  groupCohomology.coindIso
      (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
        (sourceBinaryCoefficientRep (ZMod N) Q w)) 1 ≪≫
    (groupCohomology.functor (ZMod N) (sourceGammaOneDiagonalHom Q N).range 1).mapIso
      (sourceGammaOneCoefficientTrivialIso Q N w) ≪≫
    originalCohomologyReindex
      (Rep.trivial (ZMod N) (sourceGammaOneDiagonalHom Q N).range
        (sourceBinaryCoefficientRep (ZMod N) Q w))
      (sourceGammaOneRangeEquiv Q N) 1

/-- The actual constant-coefficient Gamma1 H1 transfer onto the original
finite binary coefficient H1. -/
def sourceGammaOneConstantH1Transfer
    (Q N w : ℕ) [NeZero Q] [NeZero N] :
    groupCohomology.H1
      (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
        (sourceBinaryCoefficientRep (ZMod N) Q w)) →ₗ[ZMod N]
      groupCohomology.H1 (sourceBinaryCoefficientRep (ZMod N) Q w) := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  exact ((groupCohomology.functor (ZMod N) (Gamma0 Q) 1).map
    ((Rep.coindResAdjunction (ZMod N) H).counit.app
      (sourceBinaryCoefficientRep (ZMod N) Q w))).hom.comp
        (sourceGammaOneConstantH1Iso Q N w).toLinearEquiv.symm.toLinearMap

/-- All finite binary H1 classes lift to actual constant-coefficient H1
at the explicit Gamma1 level; surjectivity is derived from native maps. -/
theorem sourceGammaOneConstantH1Transfer_surjective
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    Function.Surjective (sourceGammaOneConstantH1Transfer Q N w) :=
  (sourceGammaOne_coindH1_surjective Q N w h6).comp
    (sourceGammaOneConstantH1Iso Q N w).toLinearEquiv.symm.surjective

/-- Every original integral binary H1 class, at every positive power of a
prime greater than three, has a constant-coefficient realization on the
actual Gamma1 cover Q*p^(2*(n+1)). -/
theorem sourceIntegralBinary_exists_gammaOneH1Realization
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) [NeZero Q] :
    let N := p ^ (n + 1)
    letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
    ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
      ∃ y : groupCohomology.H1
        (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
          (sourceBinaryCoefficientRep (ZMod N) Q w)),
        sourceGammaOneConstantH1Transfer Q N w y =
          sourceBinaryH1Change (Int.castRingHom (ZMod N)) Q w x := by
  let N := p ^ (n + 1)
  letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
  dsimp only
  intro x
  exact sourceGammaOneConstantH1Transfer_surjective Q N w
    (sourcePrimePower_six_isUnit p n hp hlarge) _

end
end Dubon2026
