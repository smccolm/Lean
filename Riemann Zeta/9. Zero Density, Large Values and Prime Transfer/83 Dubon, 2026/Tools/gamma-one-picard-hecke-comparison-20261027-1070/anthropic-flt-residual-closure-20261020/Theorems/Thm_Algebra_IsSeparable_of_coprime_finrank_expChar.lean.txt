import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import P2M.Util
import P2M.Sol.S_Algebra_IsSeparable_of_coprime_finrank_expChar

theorem Algebra.IsSeparable.of_coprime_finrank_expChar (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsSeparable_of_coprime_finrank_expChar.solution
