import Dubon2026.SourceModularIrrationalAction

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier correction -> integral parabolic-character lifting -> the actual
PSL2(Z) free-product presentation. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.
Native Mathlib ping-pong, modular generators and scalar center are reused.
This module discharges only its named presentation dependency. -/
namespace Dubon2026.SourceModularFreeProduct
open Matrix MatrixGroups ModularGroup
open scoped Pointwise
open scoped IrrationalPt
/-- Positive irrational points. -/
def Pos : Set IrrationalPt := {x | 0 < (x : ℝ)}

/-- Negative irrational points. -/
def Neg : Set IrrationalPt := {x | (x : ℝ) < 0}

theorem pos_nonempty : Pos.Nonempty := ⟨IrrationalPt.sqrtTwo, IrrationalPt.sqrtTwo_pos⟩

theorem neg_nonempty : Neg.Nonempty := ⟨IrrationalPt.negSqrtTwo, IrrationalPt.negSqrtTwo_neg⟩

theorem disjoint_pos_neg : Disjoint Pos Neg := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : (0 : ℝ) < (x : ℝ) := hx
  have h2 : (x : ℝ) < 0 := hx'
  linarith

theorem S_smul_coe (x : IrrationalPt) : ((S • x : IrrationalPt) : ℝ) = -1 / (x : ℝ) := by
  rw [smul_coe, moebius]
  norm_num [show (S 0 0 : ℤ) = 0 from rfl, show (S 0 1 : ℤ) = -1 from rfl,
    show (S 1 0 : ℤ) = 1 from rfl, show (S 1 1 : ℤ) = 0 from rfl]

theorem ST_smul_coe (x : IrrationalPt) :
    (((S * T) • x : IrrationalPt) : ℝ) = -1 / ((x : ℝ) + 1) := by
  rw [smul_coe, moebius]
  norm_num [show ((S * T) 0 0 : ℤ) = 0 from rfl, show ((S * T) 0 1 : ℤ) = -1 from rfl,
    show ((S * T) 1 0 : ℤ) = 1 from rfl, show ((S * T) 1 1 : ℤ) = 1 from rfl]

theorem ST_sq_smul_coe (x : IrrationalPt) :
    ((((S * T) * (S * T)) • x : IrrationalPt) : ℝ) = (-(x : ℝ) - 1) / (x : ℝ) := by
  rw [smul_coe, moebius]
  norm_num [show (((S * T) * (S * T)) 0 0 : ℤ) = -1 from rfl,
    show (((S * T) * (S * T)) 0 1 : ℤ) = -1 from rfl,
    show (((S * T) * (S * T)) 1 0 : ℤ) = 1 from rfl,
    show (((S * T) * (S * T)) 1 1 : ℤ) = 0 from rfl]
  ring

theorem neg_one_smul_eq (x : IrrationalPt) : ((-1 : SL(2, ℤ)) • x) = x := by
  apply IrrationalPt.ext
  rw [smul_coe, moebius]
  norm_num [show ((-1 : SL(2, ℤ)) 0 0 : ℤ) = -1 from rfl,
    show ((-1 : SL(2, ℤ)) 0 1 : ℤ) = 0 from rfl,
    show ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 from rfl,
    show ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 from rfl]

theorem S_smul_neg_mem_pos {x : IrrationalPt} (hx : x ∈ Neg) : S • x ∈ Pos := by
  show (0 : ℝ) < ((S • x : IrrationalPt) : ℝ)
  rw [S_smul_coe]
  exact div_pos_of_neg_of_neg (by norm_num) hx

theorem ST_smul_pos_mem_neg {x : IrrationalPt} (hx : x ∈ Pos) : (S * T) • x ∈ Neg := by
  show (((S * T) • x : IrrationalPt) : ℝ) < 0
  rw [ST_smul_coe]
  apply div_neg_of_neg_of_pos (by norm_num)
  have : (0 : ℝ) < (x : ℝ) := hx
  linarith

theorem ST_sq_smul_pos_mem_neg {x : IrrationalPt} (hx : x ∈ Pos) :
    ((S * T) * (S * T)) • x ∈ Neg := by
  show ((((S * T) * (S * T)) • x : IrrationalPt) : ℝ) < 0
  rw [ST_sq_smul_coe]
  have : (0 : ℝ) < (x : ℝ) := hx
  apply div_neg_of_neg_of_pos (by linarith) this

/-- The permutation representation given by the actual Mobius action on irrational reals. -/
noncomputable def toPerm : SL(2, ℤ) →* Equiv.Perm IrrationalPt :=
  MulAction.toPermHom SL(2, ℤ) IrrationalPt

theorem toPerm_apply (γ : SL(2, ℤ)) (x : IrrationalPt) : toPerm γ x = γ • x := rfl

/-- The permutation induced by the standard matrix S. -/
noncomputable def permS : Equiv.Perm IrrationalPt := toPerm S

/-- The permutation induced by the standard matrix S times T. -/
noncomputable def permU : Equiv.Perm IrrationalPt := toPerm (S * T)

theorem toPerm_neg_one : toPerm (-1) = 1 := by
  apply Equiv.ext
  intro x
  exact neg_one_smul_eq x

theorem permS_sq : permS ^ 2 = 1 := by
  rw [permS, ← map_pow, show S ^ 2 = -1 from by decide, toPerm_neg_one]

theorem permU_pow_three : permU ^ 3 = 1 := by
  rw [permU, ← map_pow, show (S * T) ^ 3 = -1 from by decide, toPerm_neg_one]


end Dubon2026.SourceModularFreeProduct
