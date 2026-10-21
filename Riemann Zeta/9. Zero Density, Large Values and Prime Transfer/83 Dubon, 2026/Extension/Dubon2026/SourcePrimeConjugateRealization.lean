import Dubon2026.SourcePrimeLaurentTranslates
import Dubon2026.SourcePrimeCyclotomicEmbedding
import Dubon2026.SourcePrimeConjugateDescent


/-! DUB-17/18 -> original differential realization -> finite function-field
extension -> monic relations. Identify each literal formal prime conjugate with
the actual analytic translate, using the already proved native Hecke matrices.
This retains the full upper-half-plane convergence and coefficient embeddings.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean, original conjugate sum and coefficient realization.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

section Translates

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
  (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

/-- The actual complex coefficient image of the original formal conjugate. -/
def conjC (i : Fin (ℓ + 1)) : LaurentSeries ℂ := coeffMap (sigma ℓ ζ hζ) (PhiGen.conj ℓ ζ i)

/-- The already proved native upper and diagonal prime Hecke representatives. -/
def rep (i : Fin (ℓ + 1)) : GL (Fin 2) ℝ :=
  Fin.cases (heckeTriangularMatrix ℓ 1 0) (fun b : Fin ℓ => heckeTriangularMatrix 1 ℓ (b : ℕ)) i

@[scoped simp] lemma rep_zero : rep ℓ 0 = heckeTriangularMatrix ℓ 1 0 := by simp [rep]
@[scoped simp] lemma rep_succ (b : Fin ℓ) : rep ℓ b.succ = heckeTriangularMatrix 1 ℓ (b : ℕ) := by simp [rep]

lemma realL_conjC_zero : RealL ℓ (conjC ℓ ζ hζ 0) (fun τ => jt (heckeTriangularMatrix ℓ 1 0 • τ)) := by
  intro τ
  have h := Realized.hasSum_qParam_heckeDiagMatrix_smul ℓ jqC jt realL_jqC τ
  have hconj : conjC ℓ ζ hζ 0 = qExpand ℂ (ℓ * ℓ) jqC := by
    rw [conjC, PhiGen.conj_zero, coeffMap_qExpand]
    congr 1
    ext m
    simp [jqC_coeff, map_ratCast]
  rw [hconj]
  exact h

omit hℓ in
lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

lemma realL_conjC_succ (b : Fin ℓ) :
    RealL ℓ (conjC ℓ ζ hζ b.succ) (fun τ => jt (heckeTriangularMatrix 1 ℓ (b : ℕ) • τ)) := by
  intro τ
  have h := Realized.hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) jqC jt realL_jqC τ
  refine h.congr_fun fun m => ?_
  congr 1
  rw [conjC, PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, Units.val_pow_eq_pow_val, map_pow, sigma_zeta, expRoot_pow_zpow]
  congr 1
  simp [jqC_coeff, map_ratCast]

lemma realL_conjC (i : Fin (ℓ + 1)) : RealL ℓ (conjC ℓ ζ hζ i) (fun τ => jt (rep ℓ i • τ)) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · simpa only [rep_zero] using realL_conjC_zero ℓ ζ hζ
  · simpa only [rep_succ] using realL_conjC_succ ℓ ζ hζ b

lemma map_phiProd : (PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ)) =
    ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjC ℓ ζ hζ i)) := by
  rw [PhiGen.phiProd, ← Polynomial.coe_mapRingHom, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conjC]

lemma realL_phiProd_coeff (k : ℕ) :
    RealL ℓ (((PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ))).coeff k)
      (fun τ => (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))).coeff k) := by
  rw [map_phiProd]
  exact RealL.coeff_prod_X_sub_C (by exact_mod_cast hℓ.out.pos) Finset.univ
    (fun i _ => realL_conjC ℓ ζ hζ i) k

lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL ℓ (qExpand ℂ ℓ x) F) :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap (sigma ℓ ζ hζ) (coeffEmb (CyclotomicField ℓ ℚ) x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

include hζ in

theorem hasSum_coeff_of_phiGenDescends (c : ℕ → LaurentSeries ℚ) (hc : PhiGen.PhiGenDescends ℓ ζ c)
    (k : ℕ) (τ : ℍ) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.E₄ (heckeTriangularMatrix ℓ 1 0 • τ) ^ 3 /
          ModularForm.discriminant (heckeTriangularMatrix ℓ 1 0 • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (heckeTriangularMatrix 1 ℓ (b : ℕ) • τ) ^ 3 /
          ModularForm.discriminant (heckeTriangularMatrix 1 ℓ (b : ℕ) • τ)))).coeff k) := by
  have h1 := realL_phiProd_coeff ℓ ζ hζ k
  rw [Polynomial.coeff_map, hc k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1 τ
  have hprod : (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))) =
      (Polynomial.X - Polynomial.C (jt (heckeTriangularMatrix ℓ 1 0 • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (jt (heckeTriangularMatrix 1 ℓ (b : ℕ) • τ))) := by
    rw [Fin.prod_univ_succ]; simp only [rep_zero, rep_succ]
  rw [hprod] at h2
  exact h2

end Translates

end
end Dubon2026.SourceFunctionField
