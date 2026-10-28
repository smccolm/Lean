import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_chordMatrix_transpose_eq_neg

theorem ZMod.chordMatrix_transpose_eq_neg {m : ℕ} [NeZero m]
    (a b : Fin m → ZMod (2 * m))
    (hdist : Function.Injective (fun p : Fin m × Bool => bif p.2 then a p.1 else b p.1)) :
    let P : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      (if a j ≠ a i ∧ (a j - a i).val < (b i - a i).val then (1 : ℤ) else 0) -
      (if b j ≠ a i ∧ (b j - a i).val < (b i - a i).val then (1 : ℤ) else 0)
    P.transpose = -P := by p2m_exact_reverting @_root_.P2MW.S_ZMod_chordMatrix_transpose_eq_neg.solution
