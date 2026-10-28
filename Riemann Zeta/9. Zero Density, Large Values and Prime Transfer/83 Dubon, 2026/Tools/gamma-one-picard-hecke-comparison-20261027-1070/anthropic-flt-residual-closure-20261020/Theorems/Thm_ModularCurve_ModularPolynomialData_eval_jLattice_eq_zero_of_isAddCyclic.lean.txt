import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane
theorem ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.solution
