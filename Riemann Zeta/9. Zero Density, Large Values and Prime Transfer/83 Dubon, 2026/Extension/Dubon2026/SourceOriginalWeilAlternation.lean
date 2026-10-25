import Dubon2026.SourceOriginalWeilBilinearity

/-! DUB-17/18 -> original Tate pairing. At odd torsion orders, skew
symmetry and the proved root-of-unity value force alternation. This is
the odd-prime branch used for the residual determinant; no assertion
about even torsion follows from this argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]

theorem originalWeilPairing_self_of_odd (hn : Odd n)
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilPairing N L n x x = 1 := by
  let w := originalWeilPairing N L n x x
  have hpow : w ^ n = 1 := Subtype.ext ((mem_rootsOfUnity n w.val).mp w.property)
  have hsq : w ^ 2 = 1 := by
    rw [pow_two]
    calc
      w * w = w⁻¹ * w := congrArg (fun z => z * w) (originalWeilPairing_symm N L n x x)
      _ = 1 := inv_mul_cancel w
  obtain ⟨k, hk⟩ := hn
  have h2k : w ^ (2 * k) = 1 := by rw [pow_mul, hsq, one_pow]
  have hw : w ^ n = w := by
    calc
      w ^ n = w ^ (2 * k + 1) := congrArg (fun j : ℕ => w ^ j) hk
      _ = w := by rw [pow_succ, h2k, one_mul]
  exact hw.symm.trans hpow

/-- The actual root-valued pairing as an additive homomorphism in both arguments. -/
def originalWeilBilinear :
    Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n →+
      Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n →+
        Additive (rootsOfUnity n L) where
  toFun x := {
    toFun y := Additive.ofMul (originalWeilPairing N L n x y)
    map_zero' := congrArg Additive.ofMul (originalWeilPairing_zero_right N L n x)
    map_add' y y' := congrArg Additive.ofMul (originalWeilPairing_add_right N L n x y y') }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul (originalWeilPairing_zero_left N L n y)
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    exact congrArg Additive.ofMul (originalWeilPairing_add_left N L n x x' y)

theorem originalWeilBilinear_self_of_odd (hn : Odd n)
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    originalWeilBilinear N L n x x = 0 :=
  congrArg Additive.ofMul (originalWeilPairing_self_of_odd N L n hn x)

end
end Dubon2026.SourceFunctionField
