import Dubon2026.SourceCurveTateCommutatorFinite
import Dubon2026.SourceModularCoefficientLocalResidues

/-! DUB-17/18 -> modular good reduction -> reverse genus bound -> canonical
degree -> global residues -> local residue/trace compatibility. The literal
modular coefficient field supplies rational residues, so its actual local
Tate commutators have finite rank with no local finiteness premise. Agreement
with differential residues and the global trace comparison remain to prove. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve SourceCurve.ResidueTrace

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- All local Tate commutators of the literal coefficient field have finite rank. -/
theorem coeff_finite_range_tate_commutator (v : Place K (modularFunctionFieldCoeff N K))
    (f g : modularFunctionFieldCoeff N K) :
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict v.tateProj
        (Algebra.lmul K (modularFunctionFieldCoeff N K) f)
        (Algebra.lmul K (modularFunctionFieldCoeff N K) g))) :=
  v.finite_range_tate_commutator (coeff_place_residue_algebraMap_bijective N K v).surjective f g

end Dubon2026.SourceFunctionField
