import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_exists_galoisPerm

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.exists_galoisPerm {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) : ∃ e : Fin ℓ ≃ Fin ℓ, ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_exists_galoisPerm.solution
