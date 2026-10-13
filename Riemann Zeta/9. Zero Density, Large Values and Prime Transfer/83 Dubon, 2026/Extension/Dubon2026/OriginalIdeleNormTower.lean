import Dubon2026.OriginalIdeleRestrictScalars
import Dubon2026.GaloisTowerKernelCohomology
import Dubon2026.OriginalIdeleClassNorm

/-! # Transitivity of the literal original idele and class norms

Original quotient representatives partition the original Galois product.
The existing restriction-kernel equivalence and proved original tower
embeddings identify its inner and outer products with the two original
norms. This proves the norm transitivity needed for coprime cyclotomic
descent and cyclic tower induction in DUB-17's class-field dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois E L] [IsGalois K L]

/-- The original idele norm is transitive in the actual Galois tower. -/
theorem originalIdeleNorm_tower (a : (AdeleRing (𝓞 L) L)ˣ) :
    originalIdeleNorm K E (originalIdeleNorm E L a) = originalIdeleNorm K L a := by
  let f : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  let Q := Gal(L/K) ⧸ f.ker
  letI : Fintype Q := Fintype.ofFinite Q
  let eQ : Q ≃* Gal(E/K) :=
    QuotientGroup.quotientKerEquivOfSurjective f (AlgEquiv.restrictNormalHom_surjective L)
  let eN := galoisTowerKernelEquiv K E L
  have hInner : (∏ g : f.ker, numberFieldIdeleGaloisMap K L g.val a) =
      originalIdeleBaseChangeMap E L (originalIdeleNorm E L a) := by
    rw [originalIdeleBaseChangeMap_norm]
    exact Fintype.prod_equiv eN.toEquiv _ _ (fun _ => rfl)
  have hQuot (q : Q) : f q.out = eQ q := by
    change eQ (QuotientGroup.mk' f.ker q.out) = eQ q
    exact congrArg eQ (Quotient.out_eq' q)
  have hOut (q : Q) : QuotientGroup.mk' f.ker q.out = q := Quotient.out_eq' q
  have hBij : Function.Bijective (fun x : Q × f.ker => x.1.out * x.2.val) := by
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ he
      have hg : QuotientGroup.mk' f.ker g.val = 1 := (QuotientGroup.eq_one_iff _).mpr g.property
      have hh : QuotientGroup.mk' f.ker h.val = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
      have hqr : q = r := by
        have hx := congrArg (QuotientGroup.mk' f.ker) he
        simpa only [map_mul, hOut, hg, hh, mul_one] using hx
      subst r
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))
    · intro σ
      let q : Q := QuotientGroup.mk' f.ker σ
      have hMem : q.out⁻¹ * σ ∈ f.ker := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' f.ker (q.out⁻¹ * σ) = 1
        rw [map_mul, map_inv, hOut]
        exact inv_mul_cancel q
      exact ⟨(q, ⟨q.out⁻¹ * σ, hMem⟩), mul_inv_cancel_left q.out σ⟩
  have hProduct : (∏ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a) =
      ∏ q : Q, numberFieldIdeleGaloisMap K L q.out
        (originalIdeleBaseChangeMap E L (originalIdeleNorm E L a)) := by
    calc
      _ = ∏ x : Q × f.ker, numberFieldIdeleGaloisMap K L (x.1.out * x.2.val) a := by
        exact (Fintype.prod_equiv (Equiv.ofBijective _ hBij)
          (fun x : Q × f.ker => numberFieldIdeleGaloisMap K L (x.1.out * x.2.val) a)
          (fun σ : Gal(L/K) => numberFieldIdeleGaloisMap K L σ a) (fun _ => rfl)).symm
      _ = ∏ q : Q, ∏ g : f.ker, numberFieldIdeleGaloisMap K L (q.out * g.val) a :=
        Fintype.prod_prod_type _
      _ = ∏ q : Q, numberFieldIdeleGaloisMap K L q.out
          (∏ g : f.ker, numberFieldIdeleGaloisMap K L g.val a) := by
        simp_rw [numberFieldIdeleGaloisMap_mul, map_prod]
      _ = _ := by rw [hInner]
  apply originalIdeleBaseChangeMap_injective K L
  rw [originalIdeleBaseChangeMap_norm, ← originalIdeleBaseChangeMap_tower K E L,
    originalIdeleBaseChangeMap_norm, map_prod, hProduct]
  simp_rw [originalIdeleBaseChangeMap_restrictNormal K E L]
  symm
  apply Fintype.prod_equiv eQ.toEquiv
  intro q
  change originalIdeleBaseChangeMap E L
    (numberFieldIdeleGaloisMap K E (f q.out) (originalIdeleNorm E L a)) = _
  rw [hQuot]
  rfl

/-- The literal original class norm is transitive in the actual Galois tower. -/
theorem originalIdeleClassNorm_tower (a : OriginalNumberFieldIdeleClassGroup L) :
    originalIdeleClassNorm K E (originalIdeleClassNorm E L a) =
      originalIdeleClassNorm K L a := by
  induction a using QuotientGroup.induction_on
  rename_i a
  change originalIdeleClassNorm K E
    (originalIdeleClassNorm E L (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a)) =
      originalIdeleClassNorm K L (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a)
  rw [originalIdeleClassNorm_mk, originalIdeleClassNorm_mk, originalIdeleClassNorm_mk,
    originalIdeleNorm_tower]

end
end Dubon2026
