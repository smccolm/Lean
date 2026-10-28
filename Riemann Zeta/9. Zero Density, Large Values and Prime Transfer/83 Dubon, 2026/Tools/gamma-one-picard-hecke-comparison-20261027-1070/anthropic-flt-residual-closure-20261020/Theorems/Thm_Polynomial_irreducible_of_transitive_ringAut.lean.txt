import Mathlib.Algebra.Polynomial.Splits
import P2M.Util
import P2M.Sol.S_Polynomial_irreducible_of_transitive_ringAut

theorem Polynomial.irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L] [Algebra F L] (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L) (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ) (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r) (hnodup : (P.map (algebraMap F L)).roots.Nodup) (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n)) (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_of_transitive_ringAut.solution
