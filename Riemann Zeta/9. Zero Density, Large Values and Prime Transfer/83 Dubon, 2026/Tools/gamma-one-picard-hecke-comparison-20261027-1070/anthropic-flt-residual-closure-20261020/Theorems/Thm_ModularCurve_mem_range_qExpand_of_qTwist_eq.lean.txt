import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_range_qExpand_of_qTwist_eq

theorem ModularCurve.mem_range_qExpand_of_qTwist_eq {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : ModularCurve.qTwist ζ f = f) : f ∈ Set.range (ModularCurve.qExpand K n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_range_qExpand_of_qTwist_eq.solution
