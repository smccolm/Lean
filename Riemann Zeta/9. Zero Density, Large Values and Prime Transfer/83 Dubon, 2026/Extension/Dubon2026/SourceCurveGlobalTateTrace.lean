import Dubon2026.SourceCurveFiberTateTrace
import Dubon2026.SourceCurveFiberResidueConstants
import Dubon2026.SourceCurveResidueFiberSum

/-! Reindex the finite global Tate residue sum by actual restriction
fibers and apply the proved fiber trace identity. Base residue rationality
is derived by lying over. This is the finite-extension transfer needed to
reduce the DUB-17/18 global residue theorem to its rational-field case. -/

noncomputable section

namespace Dubon2026.SourceCurve

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The finite global residue sum transfers along the literal field trace. -/
theorem tateResidue_global_trace
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (f : E) (g : F)
    (hfinite : (Function.support
      (fun w : Place K E => w.tateResidue f (algebraMap F E g))).Finite) :
    (∑ᶠ w : Place K E, w.tateResidue f (algebraMap F E g)) =
      ∑ᶠ v : Place K F, v.tateResidue (Algebra.trace F E f) g := by
  calc
    _ = ∑ᶠ v : Place K F, ∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.tateResidue f (algebraMap F E g) :=
      finsum_eq_fiber_finsum (fun w : Place K E => w.restrict F) _ hfinite
    _ = _ := finsum_congr fun v =>
      (v.tateResidue_trace_fiber (v.residue_bijective_of_all_upper htop) htop f g).symm

end Dubon2026.SourceCurve
