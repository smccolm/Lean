/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-! # Finite sublevel sets of the original integral Gram forms

Adapted from TauCeti/LinearAlgebra/QuadraticForm/PosDef.lean at commit
51d586d1cdfd170cd66989af5fda3e6a9e07ca4d, Apache-2.0. The pinned
Cauchy-Schwarz theorem directly handles the symmetric bilinear form,
so the additional polar-form construction is unnecessary here.
This bounds the images of an integral basis under the original CM
action, the next dependency after DUB-17's finite trace Gram classes.
-/

namespace Dubon2026

noncomputable section

/-- A symmetric positive integral bilinear form has finitely many vectors below any fixed bound. -/
theorem integralBilinForm_finite_sublevel {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (B : LinearMap.BilinForm ℤ M)
    (hB : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) (n : ℤ) :
    {x : M | B x x ≤ n}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  let T : M →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M → ℤ) :=
    LinearMap.pi fun i => B.flip (b i)
  have hTapply (x : M) (i : Module.Free.ChooseBasisIndex ℤ M) : T x i = B x (b i) := rfl
  have hTinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun x hx => ?_
    have hzero : B x = 0 := b.ext fun i => by
      simpa only [hTapply, Pi.zero_apply, LinearMap.zero_apply] using congrFun hx i
    apply hPos.anisotropic x
    change B x x = 0
    rw [hzero, LinearMap.zero_apply]
  let C : Module.Free.ChooseBasisIndex ℤ M → ℤ := fun i => n * B (b i) (b i)
  refine (Set.Finite.preimage hTinj.injOn
    (Set.Finite.pi' fun i => Set.finite_Icc (-(C i)) (C i))).subset ?_
  intro x hx i
  have hcs := B.apply_sq_le_of_symm (fun x => hPos.nonneg x)
    (LinearMap.BilinForm.isSymm_iff.mp hB) x (b i)
  have hle : (T x i) ^ 2 ≤ C i :=
    hcs.trans (mul_le_mul_of_nonneg_right hx (hPos.nonneg (b i)))
  have habs : |T x i| ≤ (T x i) ^ 2 := by
    by_cases hz : T x i = 0
    · simp [hz]
    · have h1 : 1 ≤ |T x i| := by
        rcases lt_or_gt_of_ne hz with h | h
        · rw [abs_of_neg h]; omega
        · rw [abs_of_pos h]; omega
      calc |T x i| ≤ |T x i| * |T x i| := le_mul_of_one_le_left (abs_nonneg _) h1
        _ = (T x i) ^ 2 := by rw [← sq, sq_abs]
  exact abs_le.mp (habs.trans hle)

end
end Dubon2026
