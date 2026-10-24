import Dubon2026.SourceEllipticSubfieldPointLift
import Dubon2026.SourceEllipticVariableAddEquiv

/-! Transfer actual residue-curve points through the proved constant-field
identification and coordinate change to the prescribed elliptic curve.
Existing native point maps, coordinate lifting and variable-change group
equivalences supply the bijection. This is the next map in the DUB-17/18
finite Galois specialization and exceptional-fiber census chain. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {k K : Type*} [Field k] [Field K] [DecidableEq k] [DecidableEq K]

theorem pointMapHom_surjective_of_equiv (e : k ≃+* K) (V : WeierstrassCurve k) :
    Function.Surjective (pointMapHom e.toRingHom V) := by
  intro P
  exact exists_pointMapHom_of_coordinates e.toRingHom V P
    (e.surjective _) (e.surjective _)

/-- The actual field equivalence acts bijectively on the native elliptic point group. -/
def pointFieldEquiv (e : k ≃+* K) (V : WeierstrassCurve k) :
    V.toAffine.Point ≃+ (V.map e.toRingHom).toAffine.Point :=
  AddEquiv.ofBijective (pointMapHom e.toRingHom V)
    ⟨pointMapHom_injective e.toRingHom V, pointMapHom_surjective_of_equiv e V⟩

/-- The actual point-group identification with the prescribed residue curve. -/
def residueCurvePointEquiv (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) : V.toAffine.Point ≃+ E₀.toAffine.Point :=
  (pointFieldEquiv e V).trans ((variableChangeAddEquiv γ (V.map e.toRingHom).toAffine).symm.trans
    (AddEquiv.cast (M := fun W : WeierstrassCurve K => W.toAffine.Point) hγ))

theorem residueCurvePointEquiv_some (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) {x y : k} (h : V.toAffine.Nonsingular x y) :
    HEq (residueCurvePointEquiv e V E₀ γ hγ (Point.some x y h))
      (vcInvFun γ (V.map e.toRingHom).toAffine
        (Point.some (e x) (e y) ((V.toAffine.map_nonsingular e.injective x y).mpr h))) := by
  subst E₀
  rfl

theorem residueCurvePointEquiv_some_coordinates (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) {x y : k} (h : V.toAffine.Nonsingular x y) :
    ∃ h', residueCurvePointEquiv e V E₀ γ hγ (Point.some x y h) =
      Point.some (vcXInv γ (e x)) (vcYInv γ (e x) (e y)) h' := by
  subst E₀
  refine ⟨(nonsingular_variableChange_iff _ _).mpr ?_,
    eq_of_heq (residueCurvePointEquiv_some e V _ γ rfl h)⟩
  rw [vcX_vcXInv, vcY_vcYInv]
  exact (V.toAffine.map_nonsingular e.injective x y).mpr h

end
end Dubon2026.SourceEllipticReduction
