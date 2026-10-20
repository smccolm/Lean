import Dubon2026.CMAdelicTraceDualUniformContainment
import Dubon2026.NumberFieldAdelicLatticeRationalBasis
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! # The original dual basis and its uniform integral multiple

The scaled original trace form is nondegenerate. The native bilinear
dual basis therefore has integral traces against the actual lattice;
the proved uniform containment puts one fixed multiple of every such
dual basis vector back in that lattice. This provides the integer
matrix needed for DUB-17's Gram determinant bound.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original positively scaled rational trace form is nondegenerate. -/
theorem cmHermitianScaledTraceForm_nondegenerate (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) (d : ℤ) (hd : 0 < d) :
    ((d : ℚ) • cmHermitianRationalTraceForm K H).Nondegenerate := by
  have hp (x : ι → K) (hx : x ≠ 0) :
      0 < ((d : ℚ) • cmHermitianRationalTraceForm K H) x x :=
    mul_pos (by exact_mod_cast hd) (cmHermitianRationalTraceForm_posDef K H hH x hx)
  exact ⟨fun x hx => by_contradiction fun hn => (ne_of_gt (hp x hn)) (hx x),
    fun x hx => by_contradiction fun hn => (ne_of_gt (hp x hn)) (hx x)⟩

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The native dual basis pairs with an actual lattice vector by its original integer coordinate. -/
theorem cmAdelicTraceDualBasis_pairing (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) (d : ℤ) (hd : 0 < d)
    (g : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (j : κ) (y : numberFieldAdelicLattice K ι g.val) :
    let B := (d : ℚ) • cmHermitianRationalTraceForm K H
    B (B.dualBasis (cmHermitianScaledTraceForm_nondegenerate K H hH d hd)
      (numberFieldAdelicLatticeRationalBasis K ι g.val b) j) y.val = (b.repr y j : ℚ) := by
  dsimp only
  let B := (d : ℚ) • cmHermitianRationalTraceForm K H
  let q := numberFieldAdelicLatticeRationalBasis K ι g.val b
  have he : B (B.dualBasis (cmHermitianScaledTraceForm_nondegenerate K H hH d hd) q j)
      y.val = q.repr y.val j := by
    conv_lhs => rhs; rw [← q.sum_repr y.val]
    simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact he.trans (numberFieldAdelicLatticeRationalBasis_repr K ι g.val b y j)

/-- The uniform trace-dual containment applies to every original dual basis vector. -/
theorem cmAdelicTraceDualBasis_scaled_mem (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) (d : ℤ) (hd : 0 < d)
    (m : ℤ) (hm : ∀ (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K),
      (∀ y : numberFieldAdelicLattice K ι g.val,
        IsIntegral ℤ (d • cmHermitianRationalTraceForm K H x y.val)) →
      m • x ∈ numberFieldAdelicLattice K ι g.val)
    (g : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)) (j : κ) :
    m • (((d : ℚ) • cmHermitianRationalTraceForm K H).dualBasis
      (cmHermitianScaledTraceForm_nondegenerate K H hH d hd)
        (numberFieldAdelicLatticeRationalBasis K ι g.val b) j) ∈
      numberFieldAdelicLattice K ι g.val := by
  apply hm
  intro y
  have he := cmAdelicTraceDualBasis_pairing K H hH d hd g b j y
  have hi : IsIntegral ℤ (b.repr y j : ℚ) := isIntegral_algebraMap
  rw [← he] at hi
  simpa only [LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul] using hi

end
end Dubon2026
