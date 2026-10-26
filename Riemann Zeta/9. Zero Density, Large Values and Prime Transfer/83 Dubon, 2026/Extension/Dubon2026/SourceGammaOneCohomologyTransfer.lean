import Dubon2026.SourceGammaOneCoverFiniteIndex
import Dubon2026.SourceGamma0H1Surjection
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! DUB-17/18 -> original all-weight adic association -> arithmetic
finite-cohomology realization -> transfer from the actual Gamma1 cover.
Native coinduction is left adjoint to faithful restriction at finite
index, so its counit is onto. Existing Gamma0 H2 vanishing makes the
same actual counit surjective on H1. No trace-surjectivity premise is
supplied, and no new cohomological exact-sequence theory is developed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
open scoped Classical

/-- The actual Gamma1 image gives a coinduced coefficient surjection
onto the original finite binary H1 whenever six is invertible. -/
theorem sourceGammaOne_coindH1_surjective
    (Q N w : ℕ) [NeZero Q] [NeZero N] (h6 : IsUnit (6 : ZMod N)) :
    let H := (sourceGammaOneDiagonalHom Q N).range
    letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
    Function.Surjective
      ((groupCohomology.functor (ZMod N) (Gamma0 Q) 1).map
        ((Rep.coindResAdjunction (ZMod N) H).counit.app
          (sourceBinaryCoefficientRep (ZMod N) Q w))) := by
  let H := (sourceGammaOneDiagonalHom Q N).range
  letI : H.FiniteIndex := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  let ε := (Rep.coindResAdjunction (ZMod N) H).counit.app
    (sourceBinaryCoefficientRep (ZMod N) Q w)
  haveI : Epi ε := inferInstance
  exact sourceGamma0H1_map_surjective Q h6 ε ((Rep.epi_iff_surjective ε).mp inferInstance)

/-- The restriction to the actual Gamma1 image is literally a trivial
coefficient system on the same original binary vectors. -/
def sourceGammaOneCoefficientTrivialIso
    (Q N w : ℕ) [NeZero N] :
    Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
      (sourceBinaryCoefficientRep (ZMod N) Q w) ≅
    Rep.trivial (ZMod N) (sourceGammaOneDiagonalHom Q N).range
      (sourceBinaryCoefficientRep (ZMod N) Q w) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk (LinearEquiv.refl (ZMod N) _) ?_
  intro g
  apply LinearMap.ext
  intro x
  obtain ⟨γ, hγ⟩ := g.property
  change (sourceBinaryCoefficientRep (ZMod N) Q w).ρ g.val x = x
  rw [← hγ, sourceGammaOneDiagonalHom_binary_trivial]
  rfl

end
end Dubon2026
