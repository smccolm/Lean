import Dubon2026.PolarizedTargetEquations

/-! Constructing an actual polarized group representation from explicit
equations on the original matrix representation. Faithfulness proves its
group law; the polarized representation and its compatibility are not
supplied as extra data. This is the consumer needed after imposing the
source equations on the framed coefficient ring for DUB-17. -/

namespace Dubon2026
open Matrix

variable {G R ι : Type*} [Group G] [CommRing R] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [Nontrivial R]

/-- The explicit original matrix equations defining fixed component and similitude. -/
def PolarizedMatrixEquations (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ) : Prop :=
  ∀ g, (polarizedComponentNormalization (τ g) (χ g)).val.toBlocks₁₂ = 0 ∧
    (polarizedComponentNormalization (τ g) (χ g)).val.toBlocks₂₁ = 0 ∧
    (polarizedComponentNormalization (τ g) (χ g)).val.toBlocks₁₁.transpose *
      (polarizedComponentNormalization (τ g) (χ g)).val.toBlocks₂₂ =
        Matrix.scalar ι (↑(ν g * (polarizedComponentSign (R := R) (χ g))⁻¹) : R)

/-- Original matrix equations construct the actual source polarized representation. -/
noncomputable def polarizedRepresentationOfEquations
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (h : PolarizedMatrixEquations τ χ ν) : G →* PolarizedGaloisGroup ι R := by
  let w := fun g => (polarizedBlockRepresentation_image_iff (τ g) (χ g) (ν g)).mpr (h g)
  have hw (g) : polarizedBlockRepresentation (Classical.choose (w g)) = τ g :=
    (Classical.choose_spec (w g)).2.2
  refine { toFun := fun g => Classical.choose (w g), map_one' := ?_, map_mul' := ?_ }
  · apply polarizedBlockRepresentation_injective
    rw [hw, map_one, map_one]
  · intro g k
    apply polarizedBlockRepresentation_injective
    calc
      polarizedBlockRepresentation (Classical.choose (w (g * k))) = τ (g * k) := hw _
      _ = τ g * τ k := τ.map_mul _ _
      _ = polarizedBlockRepresentation (Classical.choose (w g)) *
          polarizedBlockRepresentation (Classical.choose (w k)) :=
        congrArg₂ (· * ·) (hw g).symm (hw k).symm
      _ = polarizedBlockRepresentation (Classical.choose (w g) * Classical.choose (w k)) :=
        (map_mul polarizedBlockRepresentation _ _).symm

/-- The constructed representation has the exact original doubled matrices. -/
theorem polarizedRepresentationOfEquations_block
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (h : PolarizedMatrixEquations τ χ ν) (g : G) :
    polarizedBlockRepresentation (polarizedRepresentationOfEquations τ χ ν h g) = τ g :=
  (Classical.choose_spec ((polarizedBlockRepresentation_image_iff (τ g) (χ g) (ν g)).mpr (h g))).2.2

/-- The constructed representation has the original prescribed component character. -/
theorem polarizedRepresentationOfEquations_component
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (h : PolarizedMatrixEquations τ χ ν) (g : G) :
    polarizedComponent (polarizedRepresentationOfEquations τ χ ν h g) = χ g :=
  (Classical.choose_spec ((polarizedBlockRepresentation_image_iff (τ g) (χ g) (ν g)).mpr (h g))).1

/-- The constructed representation has the original prescribed similitude character. -/
theorem polarizedRepresentationOfEquations_similitude
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (χ : G →* Multiplicative (ZMod 2)) (ν : G →* Rˣ)
    (h : PolarizedMatrixEquations τ χ ν) (g : G) :
    polarizedSimilitude (polarizedRepresentationOfEquations τ χ ν h g) = ν g :=
  (Classical.choose_spec ((polarizedBlockRepresentation_image_iff (τ g) (χ g) (ν g)).mpr (h g))).2.1

end Dubon2026
