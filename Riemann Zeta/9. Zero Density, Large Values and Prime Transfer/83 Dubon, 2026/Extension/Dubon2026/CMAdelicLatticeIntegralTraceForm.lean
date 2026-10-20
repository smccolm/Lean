import Dubon2026.CMAdelicLatticePairingIntegral
import Dubon2026.CMHermitianTracePositive
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The actual integral trace form on an attached unitary adelic lattice

The fixed rational trace pairing is restricted using its proved integral
values and the native bilinear restriction construction. Its integer
values retain a proved equality with the original rational trace, rather
than a new unrelated form. This supplies DUB-17's integral form-class
consumer; the uniform determinant and finite CM action classes remain.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scaled original rational trace pairing is integral on every actual attached unitary lattice. -/
theorem cmAdelicLattice_trace_integral (H : Matrix ι ι K) (d : ℤ)
    (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H)
    (x y : numberFieldAdelicLattice K ι g.val) :
    IsIntegral ℤ (d • cmHermitianRationalTraceForm K H x.val y.val) := by
  have h := Algebra.isIntegral_trace (L := ℚ) (F := K)
    (cmAdelicLattice_pairing_integral K H d hH g x y)
  rw [(Algebra.trace ℚ K).map_smul_of_tower] at h
  exact h

/-- The actual integer-valued restriction of the fixed scaled rational trace form. -/
def cmAdelicLatticeIntegralTraceForm (H : Matrix ι ι K) (d : ℤ)
    (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H) :
    LinearMap.BilinForm ℤ (numberFieldAdelicLattice K ι g.val) :=
  LinearMap.restrictScalarsRange₂
    ((numberFieldAdelicLattice K ι g.val).subtype.restrictScalars ℤ)
    ((numberFieldAdelicLattice K ι g.val).subtype.restrictScalars ℤ)
    (Algebra.linearMap ℤ ℚ) Int.cast_injective
    ((d : ℚ) • cmHermitianRationalTraceForm K H) (by
      intro x y
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp
        (cmAdelicLattice_trace_integral K H d hH g x y)
      refine ⟨z, ?_⟩
      simpa only [LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul] using hz)

/-- Casting the actual integral form recovers precisely the fixed scaled source trace pairing. -/
theorem cmAdelicLatticeIntegralTraceForm_cast (H : Matrix ι ι K) (d : ℤ)
    (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H)
    (x y : numberFieldAdelicLattice K ι g.val) :
    (cmAdelicLatticeIntegralTraceForm K H d hH g x y : ℚ) =
      (d : ℚ) * cmHermitianRationalTraceForm K H x.val y.val := by
  unfold cmAdelicLatticeIntegralTraceForm
  change (Algebra.linearMap ℤ ℚ) _ = _
  rw [LinearMap.restrictScalarsRange₂_apply]
  rfl

/-- The original integral trace restriction is symmetric. -/
theorem cmAdelicLatticeIntegralTraceForm_isSymm (H : Matrix ι ι K) (hHerm : H.IsHermitian)
    (d : ℤ) (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H) :
    (cmAdelicLatticeIntegralTraceForm K H d hH g).IsSymm := by
  apply LinearMap.BilinForm.isSymm_def.mpr
  intro x y
  apply Int.cast_injective (α := ℚ)
  rw [cmAdelicLatticeIntegralTraceForm_cast, cmAdelicLatticeIntegralTraceForm_cast,
    LinearMap.BilinForm.isSymm_def.mp (cmHermitianRationalTraceForm_isSymm K H hHerm) x.val y.val]

/-- Positivity of the original source form makes its positive integral multiple positive on the actual lattice. -/
theorem cmAdelicLatticeIntegralTraceForm_posDef (H : Matrix ι ι K)
    (hPos : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (d : ℤ) (hd : 0 < d) (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H) :
    (cmAdelicLatticeIntegralTraceForm K H d hH g).toQuadraticMap.PosDef := by
  intro x hx
  have hxv : x.val ≠ 0 := by
    intro h
    exact hx (Subtype.ext h)
  have hp := cmHermitianRationalTraceForm_posDef K H hPos x.val hxv
  change 0 < cmHermitianRationalTraceForm K H x.val x.val at hp
  have hmul := mul_pos (show (0 : ℚ) < (d : ℚ) by exact_mod_cast hd) hp
  rw [← cmAdelicLatticeIntegralTraceForm_cast K H d hH g x x] at hmul
  change 0 < cmAdelicLatticeIntegralTraceForm K H d hH g x x
  exact_mod_cast hmul

end
end Dubon2026
