import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Separable
import P2M.Util
import P2M.Sol.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq

theorem Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] (p : ℕ) [Fact p.Prime] [CharP F p] (hdeg : Module.finrank (frobenius F p).fieldRange F = p) (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) : Algebra.IsSeparable E F := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.solution
