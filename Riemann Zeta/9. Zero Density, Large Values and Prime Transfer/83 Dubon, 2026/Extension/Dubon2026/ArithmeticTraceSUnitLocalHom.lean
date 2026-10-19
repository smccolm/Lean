import Dubon2026.ArithmeticSUnitLocalMap
import Dubon2026.ArithmeticTraceSUnitCohomology
import Dubon2026.RationalPrimeTraceUnitCohomology
import Dubon2026.RationalTraceCoherentCartierValue

/-! Map the actual global trace S-unit Hom coefficient to original local
unit Hom. Its normalized value is the same coherent Cartier value already
used by the finite relation construction. These are the coefficient and
normalization edges in DUB-17's prescribed local H1 recovery. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

private theorem unitHomPostcomposition_equivariant
    {G H V U W : Type} [Group G] [Group H]
    [AddCommGroup V] [Module ℤ V] [AddCommGroup U] [Module ℤ U]
    [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ G V) (ρ' : Representation ℤ H V)
    (τ : Representation ℤ G U) (τ' : Representation ℤ H W)
    (j : H →* G) (m : U →ₗ[ℤ] W)
    (hρ : ∀ g x, ρ (j g) x = ρ' g x)
    (hm : ∀ g u, m (τ (j g) u) = τ' g (m u))
    (g : H) (f : V →ₗ[ℤ] U) :
    m.comp (Representation.linHom ρ τ (j g) f) =
      Representation.linHom ρ' τ' g (m.comp f) := by
  apply LinearMap.ext
  intro x
  change m (τ (j g) (f (ρ (j g)⁻¹ x))) = τ' g (m (f (ρ' g⁻¹ x)))
  have hi : ρ (j g)⁻¹ x = ρ' g⁻¹ x :=
    (congrArg (fun u => ρ u x) (map_inv j g).symm).trans (hρ g⁻¹ x)
  exact (hm g (f (ρ (j g)⁻¹ x))).trans (congrArg (fun z => τ' g (m (f z))) hi)

attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticUnitMapAlgebra
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (p : ℕ) (hp : p.Prime)

/-- Postcompose the actual global trace S-unit Hom with the literal
arithmetic S-unit map to the original local field units. -/
def rationalTraceSUnitLocalHomMap :
    rationalArithmeticTraceSUnitHomRep a ha q σ →ₗ[ℤ]
      rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)) where
  toFun f := (rationalArithmeticSUnitLocalMap a ha p hp).comp f
  map_add' f g := by
    apply LinearMap.ext
    intro x
    let f' : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha := f
    let g' : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha := g
    exact map_add (rationalArithmeticSUnitLocalMap a ha p hp) (f' x) (g' x)
  map_smul' r f := by
    apply LinearMap.ext
    intro x
    let f' : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ]
      originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha := f
    exact map_smul (rationalArithmeticSUnitLocalMap a ha p hp) r (f' x)

/-- Exact equivariance for the original local Hom coefficient map. -/
abbrev RationalTraceSUnitLocalHomEquivariant : Prop :=
    ∀ (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (f : rationalArithmeticTraceSUnitHomRep a ha q σ),
    rationalTraceSUnitLocalHomMap a ha q σ p hp
      ((rationalArithmeticTraceSUnitHomRep a ha q σ).ρ
        (rationalPrimeArithmeticRestriction a p hp g) f) =
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ g
        (rationalTraceSUnitLocalHomMap a ha q σ p hp f)

/-- The actual Hom coefficient map intertwines the original arithmetic
restriction and prime-local Hom actions. -/
theorem rationalTraceSUnitLocalHomMap_equivariant :
    RationalTraceSUnitLocalHomEquivariant a ha q σ p hp := by
  unfold RationalTraceSUnitLocalHomEquivariant
  intro g f
  exact unitHomPostcomposition_equivariant
    (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
    (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ
    (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha).ρ
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ
    (rationalPrimeArithmeticRestriction a p hp) (rationalArithmeticSUnitLocalMap a ha p hp)
    (fun u x => DFunLike.congr_fun
      (DFunLike.congr_fun (matrixTraceZeroAdjointRepresentation_comp σ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) u) x)
    (rationalArithmeticSUnitLocalMap_equivariant a ha p hp) g f

/-- The literal local image of the global S-unit-valued trace dual is
the previously constructed coherent local Cartier value, with its proved
normalization scalar retained. -/
theorem rationalTraceSUnitLocalHomMap_coherent_value
    (hqa : (q : 𝓞 ℚ) ∣ a) (hn : (Fintype.card ι : ZMod q) ≠ 0)
    (X Y : matrixTraceZeroSubmodule ι (ZMod q)) :
    (show rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)) →ₗ[ℤ]
      Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) from
        rationalTraceSUnitLocalHomMap a ha q σ p hp
          (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X)) Y =
      rationalPrimeTraceUnitDualEquiv p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn
        (rationalArithmeticLocalNormalizationScalar a q hqa p hp • X) Y := by
  change rationalArithmeticSUnitLocalMap a ha p hp
    (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn X Y) = _
  have hglobal := rationalArithmeticTraceSUnitDualEquiv_apply a ha q σ hqa hn X Y
  have hroot := rationalArithmeticSUnitLocalMap_kummer a ha p hp q hqa
    (rationalArithmeticRootCoefficientEquiv a q hqa (Matrix.trace (X.val * Y.val)))
  simp only [rationalArithmeticRootLocalEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply] at hroot
  have hlocal := rationalPrimeTraceUnitDualEquiv_coherent_value a q hqa p hp
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn X Y
  exact (congrArg (rationalArithmeticSUnitLocalMap a ha p hp) hglobal).trans
    (hroot.trans hlocal.symm)

end
end Dubon2026
