import Dubon2026.CoefficientFiberProductRepresentation
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Genuine continuity and unique gluing of original coefficient representations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B C : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]
  [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]

omit [Group G] in
/-- Actual gluing of compatible continuous invertible-matrix families is continuous in the genuine original coefficient-subtype topology. -/
theorem generalLinearCoefficientFiberProduct_continuous
    (f : A →+* C) (g : B →+* C)
    (U : G → GeneralLinearGroup ι A) (V : G → GeneralLinearGroup ι B)
    (hU : Continuous U) (hV : Continuous V)
    (h : ∀ x, GeneralLinearGroup.map f (U x) = GeneralLinearGroup.map g (V x)) :
    Continuous (fun x => generalLinearCoefficientFiberProduct f g (U x) (V x) (h x)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact (((continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix ι ι A)).comp hU)).prodMk
      ((continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix ι ι B)).comp hV))).subtype_mk _
  · apply continuous_matrix
    intro i j
    exact (((continuous_apply_apply i j).comp ((Units.continuous_coe_inv (M := Matrix ι ι A)).comp hU)).prodMk
      ((continuous_apply_apply i j).comp ((Units.continuous_coe_inv (M := Matrix ι ι B)).comp hV))).subtype_mk _

/-- The original entire glued coefficient representation is genuinely continuous whenever the two actual original representations are continuous. -/
theorem coefficientFiberProductRepresentation_continuous
    (f : A →+* C) (g : B →+* C)
    (ρA : G →* GeneralLinearGroup ι A) (ρB : G →* GeneralLinearGroup ι B)
    (hA : Continuous ρA) (hB : Continuous ρB)
    (h : (GeneralLinearGroup.map f).comp ρA = (GeneralLinearGroup.map g).comp ρB) :
    Continuous (coefficientFiberProductRepresentation f g ρA ρB h) :=
  generalLinearCoefficientFiberProduct_continuous f g ρA ρB hA hB (DFunLike.congr_fun h)

/-- Compatible original continuous whole representations glue uniquely to an actual continuous representation over the genuine coefficient fiber product. -/
theorem continuousCoefficientFiberProductRepresentation_existsUnique
    (f : A →+* C) (g : B →+* C)
    (ρA : G →ₜ* GeneralLinearGroup ι A) (ρB : G →ₜ* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA.toMonoidHom =
      (GeneralLinearGroup.map g).comp ρB.toMonoidHom) :
    ∃! ρ : G →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom = ρA.toMonoidHom ∧
      (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom = ρB.toMonoidHom := by
  let ρ : G →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g) :=
    ⟨coefficientFiberProductRepresentation f g ρA.toMonoidHom ρB.toMonoidHom h,
      coefficientFiberProductRepresentation_continuous f g ρA.toMonoidHom ρB.toMonoidHom
        ρA.continuous ρB.continuous h⟩
  refine ⟨ρ, coefficientFiberProductRepresentation_projections f g ρA.toMonoidHom ρB.toMonoidHom h, ?_⟩
  intro τ hτ
  have heq : τ.toMonoidHom = ρ.toMonoidHom :=
    (coefficientFiberProductRepresentation_existsUnique f g ρA.toMonoidHom ρB.toMonoidHom h).unique
      hτ (coefficientFiberProductRepresentation_projections f g ρA.toMonoidHom ρB.toMonoidHom h)
  apply ContinuousMonoidHom.ext
  intro x
  exact DFunLike.congr_fun heq x

end
end Dubon2026
