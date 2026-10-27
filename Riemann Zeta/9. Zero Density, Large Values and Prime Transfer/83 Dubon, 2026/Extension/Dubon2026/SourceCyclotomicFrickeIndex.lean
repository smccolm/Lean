import Dubon2026.SourceFrickeCyclotomicLaurent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> cyclotomic coefficient conjugation. The actual cyclotomic
root determines a unit modulo N, acting on the second torsion coordinate.
This is the generator permutation needed to realize conjugated Laurent
series as actual Fricke functions; no analytic conjugation is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem isPrimitiveRoot_zetaK (N : ℕ) [NeZero N] : IsPrimitiveRoot (zetaK N) N := by
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp (isPrimitiveRoot_zetaN (NeZero.ne N))

theorem exists_cyclotomic_aut_exponent (N : ℕ) [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N) :
    ∃ s : ℕ, s.Coprime N ∧ σ (zetaK N) = zetaK N ^ s := by
  have hμ := isPrimitiveRoot_zetaK N
  refine ⟨((hμ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N).val,
    ZMod.val_coe_unit_coprime _, ?_⟩
  exact (hμ.autToPow_spec ℚ σ).symm

/-- The nonzero torsion index induced by the cyclotomic exponent. -/
def cyclotomicFrickeIndex {N : ℕ} (s : ℕ) (hs : s.Coprime N) (i : FrickeIdx N) :
    FrickeIdx N := ⟨![i.1 0, (s : ZMod N) * i.1 1], by
  intro hz
  have h0 : i.1 0 = 0 := by simpa using congrFun hz 0
  have h1 : (s : ZMod N) * i.1 1 = 0 := by simpa using congrFun hz 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : i.1 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  exact i.2 (by funext j; fin_cases j <;> simp [h0, h1'])⟩

theorem cyclotomicFrickeIndex_val_zero {N : ℕ} (s : ℕ) (hs : s.Coprime N)
    (i : FrickeIdx N) : ((cyclotomicFrickeIndex s hs i).1 0).val = (i.1 0).val := rfl

theorem cyclotomicFrickeIndex_val_one {N : ℕ} [NeZero N] (s : ℕ) (hs : s.Coprime N)
    (i : FrickeIdx N) : ((cyclotomicFrickeIndex s hs i).1 1).val = s * (i.1 1).val % N := by
  change ((s : ZMod N) * i.1 1).val = _
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]

end
end Dubon2026.SourceFricke
