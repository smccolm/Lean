import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : c k ∈ Algebra.adjoin ℚ {jq} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.solution
