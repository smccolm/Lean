import Dubon2026.SourceToricFieldDivisionIdentities

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> marked-point chart. Construct an actual point of exact order N
on the literal Tate curve over an algebraically closed Laurent-field
extension. Its unit multiples have exactly the previously constructed
toric abscissae. Native ordinate existence and division-polynomial
coprimality discharge point existence and exclusion of all smaller orders;
no point, order or coordinate certificate is assumed. -/
namespace Dubon2026.SourceFunctionField.ToricAnalytic
noncomputable section
open WeierstrassCurve HahnSeries GammaOne.ToricFourier SourceEllipticExceptional
open SourceEllipticDivisionField

theorem exists_exactOrder_toric_point (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (hN : 2 ≤ N)
    (K L : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] [Field L] [IsAlgClosed L] [DecidableEq L]
    [Algebra (LaurentSeries K) L] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    ∃ P : ((tateLaurent K).baseChange L).toAffine.Point,
      addOrderOf P = N ∧ ∀ t : (ZMod N)ˣ,
        xco (((t : ZMod N).val : ℕ) • P) =
          some (seriesToField K L (xS (ζ ^ (t : ZMod N).val))) := by
  classical
  haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (by omega)
  let E := (tateLaurent K).baseChange L
  let x := seriesToField K L (xS (ζ ^ (1 : ZMod N).val))
  obtain ⟨y, hy⟩ := SourceEllipticVelu.exists_equation_y E x
  have h : E.toAffine.Nonsingular x y :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero E.isUnit_Δ.ne_zero).mp hy
  let P : E.toAffine.Point := .some x y h
  refine ⟨P, ?_, ?_⟩
  · apply (addOrderOf_eq_iff (show 0 < N by omega)).mpr
    constructor
    · exact (nsmul_eq_zero_iff_division_eval E h N).mpr
        (tateField_eval_ΨSq N ℓ hℓN K L hζ 1 one_ne_zero)
    · intro m hlt hm he
      have hmc : (m : ZMod N) * 1 ≠ 0 := by
        rw [mul_one]
        exact fun hz => Nat.not_dvd_of_pos_of_lt hm hlt
          ((CharP.cast_eq_zero_iff (ZMod N) N m).mp hz)
      exact tateField_eval_ΨSq_ne_zero N ℓ hℓN K L hζ 1 one_ne_zero m hm hmc
        ((nsmul_eq_zero_iff_division_eval E h m).mp he)
  · intro t
    let m := (t : ZMod N).val
    have hm : 0 < m := Nat.pos_of_ne_zero (fun he =>
      t.ne_zero ((ZMod.val_eq_zero (t : ZMod N)).mp he))
    have hmc : (m : ZMod N) * 1 ≠ 0 := by
      simpa only [m, ZMod.natCast_zmod_val, mul_one] using t.ne_zero
    have hΨ := tateField_eval_ΨSq_ne_zero N ℓ hℓN K L hζ 1 one_ne_zero m hm hmc
    have hne : m • Affine.Point.some x y h ≠ 0 := fun he =>
      hΨ ((nsmul_eq_zero_iff_division_eval E h m).mp he)
    have hc := (nsmul_xco_eq_div E m h hne).2
    rw [natCast_zsmul] at hc
    change xco (m • P) = _
    rw [hc]
    congr 1
    apply (div_eq_iff hΨ).mpr
    have he := tateField_mul_eval N ℓ hℓN K L hζ 1 one_ne_zero m hmc
    simpa only [m, ZMod.natCast_zmod_val, mul_one] using he.symm

end
end Dubon2026.SourceFunctionField.ToricAnalytic
