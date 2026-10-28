import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))) = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)))) * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.solution
