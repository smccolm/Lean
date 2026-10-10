import Dubon2026.MatrixCoefficientFiberProduct
import Dubon2026.MatrixRepresentationStabilizerLifting
import Dubon2026.CoefficientFiberProductStrictConjugacy

/-! # Aligning genuine original coefficient conjugators by lifting actual stabilizers -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B C L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

omit [Group G] in
/-- Both original projections of any actual invertible matrix over the coefficient fiber product have the same genuine common reduction. -/
theorem coefficientFiberProductMatrix_common_reduction
    (f : A →+* C) (g : B →+* C)
    (W : GeneralLinearGroup ι (CoefficientFiberProduct f g)) :
    GeneralLinearGroup.map f (GeneralLinearGroup.map (coefficientFiberProductFst f g) W) =
      GeneralLinearGroup.map g (GeneralLinearGroup.map (coefficientFiberProductSnd f g) W) := by
  apply Units.ext
  ext i j
  exact (W.val i j).property

variable [IsLocalRing B] [IsLocalRing C] [Field L]
  [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]

/-- Lift the discrepancy between actual original coefficient conjugators as a genuine stabilizer of the original second representation. Correcting that conjugator preserves its whole conjugacy and makes both actual common reductions agree. -/
theorem coefficientFiberProduct_conjugators_align
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g)
    (ρ σ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue C)).comp
          ((GeneralLinearGroup.map g).comp
            ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ)))))]
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (hA : ∀ x, GeneralLinearGroup.map (coefficientFiberProductFst f g) (σ x) =
      U * GeneralLinearGroup.map (coefficientFiberProductFst f g) (ρ x) * U⁻¹)
    (hB : ∀ x, GeneralLinearGroup.map (coefficientFiberProductSnd f g) (σ x) =
      V * GeneralLinearGroup.map (coefficientFiberProductSnd f g) (ρ x) * V⁻¹) :
    ∃ V' : GeneralLinearGroup ι B,
      GeneralLinearGroup.map g V' = GeneralLinearGroup.map f U ∧
      ∀ x, GeneralLinearGroup.map (coefficientFiberProductSnd f g) (σ x) =
        V' * GeneralLinearGroup.map (coefficientFiberProductSnd f g) (ρ x) * V'⁻¹ := by
  let ρB := (GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ
  let Uc := GeneralLinearGroup.map f U
  let Vc := GeneralLinearGroup.map g V
  let W := Vc⁻¹ * Uc
  have hW : ∀ x, W * GeneralLinearGroup.map g (ρB x) =
      GeneralLinearGroup.map g (ρB x) * W := by
    intro x
    have hAc := congrArg (GeneralLinearGroup.map f) (hA x)
    have hBc := congrArg (GeneralLinearGroup.map g) (hB x)
    simp only [map_mul, map_inv,
      coefficientFiberProductMatrix_common_reduction f g] at hAc
    simp only [map_mul, map_inv] at hBc
    have he : Vc * GeneralLinearGroup.map g (ρB x) * Vc⁻¹ =
        Uc * GeneralLinearGroup.map g (ρB x) * Uc⁻¹ := hBc.symm.trans hAc
    have ht := congrArg (fun X => Vc⁻¹ * X * Uc) he
    simpa only [W, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht.symm
  obtain ⟨N, hN, hcN⟩ := matrixRepresentation_stabilizer_lifts (L := L) g hg ρB W hW
  refine ⟨V * N, ?_, ?_⟩
  · rw [map_mul, hN]
    change Vc * (Vc⁻¹ * Uc) = Uc
    simp only [mul_inv_cancel_left]
  · intro x
    have he : N * ρB x * N⁻¹ = ρB x := by
      rw [hcN x]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [hB x]
    change V * ρB x * V⁻¹ = (V * N) * ρB x * (V * N)⁻¹
    calc
      _ = V * (N * ρB x * N⁻¹) * V⁻¹ := by rw [he]
      _ = _ := by simp only [_root_.mul_inv_rev, mul_assoc]

/-- Strict conjugacy of both actual projected whole representations gives strict conjugacy over the original coefficient fiber product, by deriving compatible conjugators from actual residual irreducibility and stabilizer lifting. -/
theorem matrixStrictlyConjugate_fiberProduct_of_projections {K : Type} [CommRing K]
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g)
    (ρ σ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue C)).comp
          ((GeneralLinearGroup.map g).comp
            ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ)))))]
    (rA : A →+* K) (rB : B →+* K)
    (hA : MatrixStrictlyConjugate rA
      ((GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ)
      ((GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp σ))
    (hB : MatrixStrictlyConjugate rB
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ)
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp σ)) :
    MatrixStrictlyConjugate (rA.comp (coefficientFiberProductFst f g)) ρ σ := by
  obtain ⟨U, hU, hA⟩ := hA
  obtain ⟨V, _, hB⟩ := hB
  obtain ⟨V', hV', hconj⟩ := coefficientFiberProduct_conjugators_align (L := L)
    f g hg ρ σ U V hA hB
  exact matrixStrictlyConjugate_fiberProduct_of_compatible_conjugators
    f g rA ρ σ U V' hV'.symm hU hA hconj

end
end Dubon2026
