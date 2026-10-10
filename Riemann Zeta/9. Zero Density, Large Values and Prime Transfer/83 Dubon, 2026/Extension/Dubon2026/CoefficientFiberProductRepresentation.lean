import Dubon2026.MatrixCoefficientFiberProduct

/-! # Exact gluing of the original whole representations over a coefficient fiber product -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B C : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

/-- The actual whole representation glued from compatible original coefficient representations. -/
def coefficientFiberProductRepresentation (f : A →+* C) (g : B →+* C)
    (ρA : G →* GeneralLinearGroup ι A) (ρB : G →* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA = (GeneralLinearGroup.map g).comp ρB) :
    G →* GeneralLinearGroup ι (CoefficientFiberProduct f g) where
  toFun x := generalLinearCoefficientFiberProduct f g (ρA x) (ρB x) (DFunLike.congr_fun h x)
  map_one' := by
    apply generalLinearCoefficientFiberProduct_ext f g
    · simpa only [map_one] using
        (generalLinearCoefficientFiberProduct_projections f g (ρA 1) (ρB 1)
          (DFunLike.congr_fun h 1)).1
    · simpa only [map_one] using
        (generalLinearCoefficientFiberProduct_projections f g (ρA 1) (ρB 1)
          (DFunLike.congr_fun h 1)).2
  map_mul' x y := by
    apply generalLinearCoefficientFiberProduct_ext f g
    · rw [(generalLinearCoefficientFiberProduct_projections f g (ρA (x * y)) (ρB (x * y))
        (DFunLike.congr_fun h (x * y))).1]
      simp only [map_mul,
        (generalLinearCoefficientFiberProduct_projections f g (ρA x) (ρB x)
          (DFunLike.congr_fun h x)).1,
        (generalLinearCoefficientFiberProduct_projections f g (ρA y) (ρB y)
          (DFunLike.congr_fun h y)).1]
    · rw [(generalLinearCoefficientFiberProduct_projections f g (ρA (x * y)) (ρB (x * y))
        (DFunLike.congr_fun h (x * y))).2]
      simp only [map_mul,
        (generalLinearCoefficientFiberProduct_projections f g (ρA x) (ρB x)
          (DFunLike.congr_fun h x)).2,
        (generalLinearCoefficientFiberProduct_projections f g (ρA y) (ρB y)
          (DFunLike.congr_fun h y)).2]

/-- The same entire glued representation retains both supplied original representations under the actual coefficient projections. -/
theorem coefficientFiberProductRepresentation_projections (f : A →+* C) (g : B →+* C)
    (ρA : G →* GeneralLinearGroup ι A) (ρB : G →* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA = (GeneralLinearGroup.map g).comp ρB) :
    (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp
      (coefficientFiberProductRepresentation f g ρA ρB h) = ρA ∧
    (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp
      (coefficientFiberProductRepresentation f g ρA ρB h) = ρB := by
  constructor
  · apply MonoidHom.ext
    intro x
    exact (generalLinearCoefficientFiberProduct_projections f g (ρA x) (ρB x)
      (DFunLike.congr_fun h x)).1
  · apply MonoidHom.ext
    intro x
    exact (generalLinearCoefficientFiberProduct_projections f g (ρA x) (ρB x)
      (DFunLike.congr_fun h x)).2

/-- Compatible original whole representations glue uniquely to a whole representation over the genuine original coefficient fiber product. -/
theorem coefficientFiberProductRepresentation_existsUnique (f : A →+* C) (g : B →+* C)
    (ρA : G →* GeneralLinearGroup ι A) (ρB : G →* GeneralLinearGroup ι B)
    (h : (GeneralLinearGroup.map f).comp ρA = (GeneralLinearGroup.map g).comp ρB) :
    ∃! ρ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ = ρA ∧
      (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ = ρB := by
  refine ⟨coefficientFiberProductRepresentation f g ρA ρB h,
    coefficientFiberProductRepresentation_projections f g ρA ρB h, ?_⟩
  intro ρ hρ
  apply MonoidHom.ext
  intro x
  apply generalLinearCoefficientFiberProduct_ext f g
  · exact DFunLike.congr_fun
      (hρ.1.trans (coefficientFiberProductRepresentation_projections f g ρA ρB h).1.symm) x
  · exact DFunLike.congr_fun
      (hρ.2.trans (coefficientFiberProductRepresentation_projections f g ρA ρB h).2.symm) x

end
end Dubon2026
