import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_exists_phiGenDescends

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.exists_phiGenDescends {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_exists_phiGenDescends.solution
