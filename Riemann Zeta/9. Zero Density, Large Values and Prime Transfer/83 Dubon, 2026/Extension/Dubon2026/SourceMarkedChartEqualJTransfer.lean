import Dubon2026.SourceTateOriginalJCoordinate
import Dubon2026.SourceMarkedChartVariableInvariants
import Dubon2026.SourceToricMarkedPointCoordinates
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original
Gamma1/full-torsion chart. Transfer the constructed exact-order Tate point
to an actual elliptic curve with the same j coordinate. Native equal-j
isomorphisms and the native additive variable-change equivalence preserve
the point and its order; the two proved invariant identities transport the
actual functions in the original Gamma1 field, including in small characteristic. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticVariableChange ToricAnalytic
open GammaOne GammaOne.ToricCoordinates IntegralSlash

theorem exists_originalField_markedPoint_of_j_eq
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hN : 2 ≤ N)
    (K L : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] [Field L] [IsAlgClosed L]
    [DecidableEq L] [Algebra (LaurentSeries K) L] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (E : WeierstrassCurve L) [E.IsElliptic]
    (hj : E.j = algebraMap (LaurentSeries K) L (jqModC K)) :
    ∃ P : E.toAffine.Point, addOrderOf P = N ∧ ∀ t : (ZMod N)ˣ,
      ∃ (x y : L) (h : E.toAffine.Nonsingular x y),
        (t : ZMod N).val • P = Affine.Point.some x y h ∧
        algebraMap (LaurentSeries K) L ((w₁ N K ζ t : qExpFunctionFieldC K
          (CongruenceSubgroup.Gamma1 N)) : LaurentSeries K) =
            E.c₄ * (12 * x + E.b₂) / E.c₆ ∧
        algebraMap (LaurentSeries K) L ((w₂ N K ζ t : qExpFunctionFieldC K
          (CongruenceSubgroup.Gamma1 N)) : LaurentSeries K) =
            (6 * x ^ 2 + E.b₂ * x + E.b₄) / E.c₄ := by
  let T := (tateLaurent K).baseChange L
  have hTj : T.j = E.j := by
    rw [hj]
    exact (WeierstrassCurve.map_j (tateLaurent K) (algebraMap (LaurentSeries K) L)).trans
      (congrArg (algebraMap (LaurentSeries K) L) (j_tateLaurent K))
  have hc4 : T.c₄ ≠ 0 := by
    change ((tateLaurent K).map (algebraMap (LaurentSeries K) L)).c₄ ≠ 0
    rw [WeierstrassCurve.map_c₄]
    apply (map_ne_zero (algebraMap (LaurentSeries K) L)).mpr
    rw [c4_tateLaurent]
    exact intSeriesC_eisenstein4_ne_zero K
  have hc6 : T.c₆ ≠ 0 := by
    change ((tateLaurent K).map (algebraMap (LaurentSeries K) L)).c₆ ≠ 0
    rw [WeierstrassCurve.map_c₆]
    apply (map_ne_zero (algebraMap (LaurentSeries K) L)).mpr
    rw [c6_tateLaurent, neg_ne_zero]
    exact intSeriesC_eisenstein6_ne_zero K
  have hb2 : T.b₂ = 1 := by
    simp [T, WeierstrassCurve.b₂, WeierstrassCurve.baseChange, tateLaurent, tatePowerSeries]
  have hb4 : T.b₄ = 2 * T.a₄ := by
    simp [T, WeierstrassCurve.b₄, WeierstrassCurve.baseChange, tateLaurent, tatePowerSeries]
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq T E hTj
  subst E
  let e := variableChangeAddEquiv C T.toAffine
  obtain ⟨PT, hPT, hcoord⟩ := exists_originalField_markedToricCoordinates N ℓ hℓN hN K L hζ
  refine ⟨e.symm PT, (AddEquiv.addOrderOf_eq e.symm PT).trans hPT, fun t => ?_⟩
  obtain ⟨tx, ty, ht, hpt, hw1, hw2⟩ := hcoord t
  have he : e ((t : ZMod N).val • e.symm PT) = Affine.Point.some tx ty ht := by
    rw [map_nsmul, e.apply_symm_apply, hpt]
  cases hp : (t : ZMod N).val • e.symm PT with
  | zero =>
      rw [hp] at he
      change Affine.Point.zero = Affine.Point.some tx ty ht at he
      cases he
  | some x y h =>
      have hx : (C.u : L) ^ 2 * x + C.r = tx := by
        rw [hp] at he
        change Affine.Point.some (vcX C x) (vcY C x y) _ = Affine.Point.some tx ty ht at he
        exact (Affine.Point.some.inj he).1
      refine ⟨x, y, h, rfl, ?_, ?_⟩
      · rw [variableChange_first_invariant T C hc6, hx, hb2]
        simpa only [add_comm] using hw1
      · rw [variableChange_second_invariant T C hc4, hx, hb2, hb4, one_mul]
        convert hw2 using 1
        ring

end
end Dubon2026.SourceFunctionField.MarkedChart
