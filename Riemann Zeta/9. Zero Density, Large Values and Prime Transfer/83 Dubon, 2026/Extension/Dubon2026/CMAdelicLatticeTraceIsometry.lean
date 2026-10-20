import Dubon2026.CMAdelicLatticeFieldEquiv

/-! # Recovering the original rational trace isometry from equal Gram invariants

Equality of the original integral Gram matrices cancels the fixed
nonzero trace scaling and extends from the actual integral basis to the
entire original rational vector space. This is the trace-isometry input
for DUB-17's recovery of the original Hermitian unitary transformation.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Equal original integral Gram matrices recover the original rational trace isometry. -/
theorem cmAdelicLatticeRationalEquiv_trace (H : Matrix ι ι K)
    (d : ℤ) (hd : d ≠ 0) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (hGram : toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) =
      toMatrix c (cmAdelicLatticeIntegralTraceForm K H d hIntegral h)) (x y : ι → K) :
    cmHermitianRationalTraceForm K H
      (numberFieldAdelicLatticeRationalEquiv K g.val h.val b c x)
      (numberFieldAdelicLatticeRationalEquiv K g.val h.val b c y) =
        cmHermitianRationalTraceForm K H x y := by
  let e := numberFieldAdelicLatticeRationalEquiv K g.val h.val b c
  let B := cmHermitianRationalTraceForm K H
  have hb (i j : κ) : B (c i).val (c j).val = B (b i).val (b j).val := by
    have hi := congrArg (fun A : Matrix κ κ ℤ => (A i j : ℚ)) hGram
    simp only [toMatrix_apply, cmAdelicLatticeIntegralTraceForm_cast] at hi
    exact (mul_left_cancel₀ (show (d : ℚ) ≠ 0 by exact_mod_cast hd) hi).symm
  have he : B.compl₁₂ e.toLinearMap e.toLinearMap = B := by
    apply (numberFieldAdelicLatticeRationalBasis K ι g.val b).ext
    intro i
    apply (numberFieldAdelicLatticeRationalBasis K ι g.val b).ext
    intro j
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      numberFieldAdelicLatticeRationalBasis_apply, e,
      numberFieldAdelicLatticeRationalEquiv_basis]
    exact hb i j
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

end
end Dubon2026
