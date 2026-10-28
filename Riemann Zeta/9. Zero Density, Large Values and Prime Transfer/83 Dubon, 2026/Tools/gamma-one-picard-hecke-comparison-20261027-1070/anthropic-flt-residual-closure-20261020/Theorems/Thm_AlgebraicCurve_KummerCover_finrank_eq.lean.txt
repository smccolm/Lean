import Mathlib.FieldTheory.KummerExtension
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_KummerCover_finrank_eq

open Polynomial
theorem AlgebraicCurve.KummerCover.finrank_eq {F L : Type*} [Field F] [Field L] [Algebra F L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p ≠ f) :
    Module.finrank F L = p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_KummerCover_finrank_eq.solution
