import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_residue_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Finite ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (a : ∀ i, Fb i) :
    ∃ z : F, ∀ i, ∃ h : z ∈ (R i).integers, (R i).residue ⟨z, h⟩ = a i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq.solution
