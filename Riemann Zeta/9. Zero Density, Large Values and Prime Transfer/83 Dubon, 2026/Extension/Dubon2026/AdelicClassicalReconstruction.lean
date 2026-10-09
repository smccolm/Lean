import Dubon2026.AdelicInvariantReconstruction
import Dubon2026.AdelicFiniteClassicalCusp

/-! # Original fixed-level algebraic vectors are the full adelic lifts of genuine classical cusp forms -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every original fixed-level algebraic vector is exactly the full adelic lift of its actual classical restriction. -/
theorem adelicCyclic_classical_reconstruction
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f)
    (F : ℍ → ℂ) (hF : realWeightLiftLinear k F = adelicCyclicRealRestriction f v) :
    v.val = canonicalAdelicGL2CuspLift N k F :=
  adelicFunction_full_reconstruction N k v.val F
    (adelicLiftCyclic_rational_invariant N f v.property)
    (adelicLiftCyclic_scalar_invariant N f v.property)
    (adelicCyclic_level_pointwise f v hv)
    (fun g => (congrFun hF g).symm)

/-- Every genuine finite-adelic combination fixed at the original level is precisely one original-level classical cusp form's full adelic lift. -/
theorem adelicAlgebraicFiniteSpan_classical_full
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f)
    (hlevel : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f) :
    ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
      v.val = canonicalAdelicGL2CuspLift N k F := by
  obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_classical_cusp f v hv hlevel
  have he := adelicCyclic_classical_reconstruction f v hlevel F hF
  exact ⟨F, he, fun G hG => canonicalAdelicGL2CuspLift_injective N k (hG.symm.trans he)⟩

end
end Dubon2026
