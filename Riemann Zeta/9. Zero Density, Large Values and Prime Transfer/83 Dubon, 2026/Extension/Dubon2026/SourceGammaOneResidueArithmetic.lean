import Dubon2026.SourceGammaOneDecompositionGauss

/-! DUB-17/18 -> original Gamma1 geometric Frobenius/inertia -> equivariant
residue field. The native decomposition action preserves the actual residue
image by surjectivity of its constructed reduction. Inertia fixes this field
and reduction of arithmetic Frobenius acts on Laurent coefficients by the
residue power map. This is coefficient Frobenius, not the absolute power map
on the function field; place comparison and Picard torsion injectivity remain.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem coeffMap_decomposition_mem_residueImage (d : A.decompositionSubgroup ℚ)
    {x : LaurentSeries kk} (hx : x ∈ residueImage A Γ) :
    coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d) x ∈
      residueImage A Γ := by
  obtain ⟨f, hf⟩ := residueToImage_surjective A Γ ⟨x, hx⟩
  have he : resHom A Γ f = x := congrArg Subtype.val hf
  rw [← he, ← decompositionGaussHom_resHom]
  exact resHom_mem_residueImage A Γ _

/-- The literal coefficient action on the original Gamma1 residue image. -/
def decompositionResidueAut (d : A.decompositionSubgroup ℚ) : Fb ≃+* Fb where
  toFun x := ⟨coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d) x.val,
    coeffMap_decomposition_mem_residueImage A Γ d x.property⟩
  invFun x := ⟨coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d⁻¹) x.val,
    coeffMap_decomposition_mem_residueImage A Γ d⁻¹ x.property⟩
  left_inv x := by
    apply Subtype.ext
    ext n
    change d⁻¹ • (d • x.val.coeff n) = x.val.coeff n
    exact inv_smul_smul d _
  right_inv x := by
    apply Subtype.ext
    ext n
    change d • (d⁻¹ • x.val.coeff n) = x.val.coeff n
    exact smul_inv_smul d _
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

theorem decompositionGaussHom_residueToImage (d : A.decompositionSubgroup ℚ)
    (f : coefficientGaussRing Γ A) :
    residueToImage A Γ (decompositionGaussHom A Γ d f) =
      decompositionResidueAut A Γ d (residueToImage A Γ f) :=
  Subtype.ext (decompositionGaussHom_resHom A Γ d f)

theorem decompositionResidueAut_eq_one_of_inertia (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) : decompositionResidueAut A Γ d = 1 := by
  ext x n
  change d • x.val.coeff n = x.val.coeff n
  have h := MonoidHom.mem_ker.mp hd
  exact congrArg (fun e : RingAut kk => e (x.val.coeff n)) h

theorem residueToImage_arithmetic_inertia (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) (f : coefficientGaussRing Γ A) :
    residueToImage A Γ (decompositionGaussHom A Γ d f) = residueToImage A Γ f := by
  rw [decompositionGaussHom_residueToImage, decompositionResidueAut_eq_one_of_inertia A Γ d hd]
  rfl

theorem residueToImage_arithmetic_frobenius_coeff (p : ℕ)
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p)
    (f : coefficientGaussRing Γ A) (n : ℤ) :
    ((residueToImage A Γ (decompositionGaussHom A Γ d f) : Fb) : LaurentSeries kk).coeff n =
      (((residueToImage A Γ f : Fb) : LaurentSeries kk).coeff n) ^ p := by
  rw [decompositionGaussHom_residueToImage]
  exact hd _

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
