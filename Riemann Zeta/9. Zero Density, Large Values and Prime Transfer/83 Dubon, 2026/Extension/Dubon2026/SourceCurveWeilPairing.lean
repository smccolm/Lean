import Dubon2026.SourceCurveWeilAction
import Dubon2026.SourceCurveDivisorDimensionGrowth

/-! DUB-17/18 -> actual cusp-form dimension -> regular differential
dimension -> Riemann--Roch -> residue duality. The proved global index
formula forces any two bounded global-annihilating functionals to be
function-field multiples. This is the necessary rank-one step for the
residue pairing; constructing the canonical residue functional remains
separate. Selected source: Def_AlgebraicCurve_AdelicIndex and
S_AlgebraicCurve_omegaSpace_finite_of_genusReached, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
/-- The source pairing induced by a bounded global-annihilating functional. -/
def residuePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) :
    LSpace (W - D) →ₗ[K] omegaSpace D where
  toFun g := ⟨weilSmul K F (g : F) φ, weilSmul_mem_omegaSpace_of_mem_lSpace hφ g.2⟩
  map_add' g₁ g₂ := by
    refine Subtype.ext ?_
    show weilSmul K F ((g₁ : F) + (g₂ : F)) φ
      = weilSmul K F (g₁ : F) φ + weilSmul K F (g₂ : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.add_apply]
    rw [← map_add]; congr 1
    exact Subtype.ext (funext fun v => by simp [add_mul])
  map_smul' c g := by
    refine Subtype.ext ?_
    show weilSmul K F (c • (g : F)) φ = c • weilSmul K F (g : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.smul_apply]
    rw [← map_smul]; congr 1
    exact Subtype.ext (funext fun v => by simp [Algebra.smul_def]; ring)

@[simp]
theorem residuePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (g : LSpace (W - D)) :
    (residuePairing K F W D hφ g : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ := rfl

theorem residuePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    Function.Injective (residuePairing K F W D hφ) := by
  have hsub : ∀ g₁ g₂ : F, adeleSpaceMul K F (g₁ - g₂)
      = adeleSpaceMul K F g₁ - adeleSpaceMul K F g₂ := fun g₁ g₂ => by
    refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
    simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.sub_apply,
      Submodule.coe_sub, Pi.sub_apply, sub_mul]
  intro g₁ g₂ hg
  have hg' : weilSmul K F ((g₁ : F) - (g₂ : F)) φ = 0 := by
    have h := congrArg Subtype.val hg
    simp only [residuePairing_apply_coe] at h
    ext α
    simp only [weilSmul_apply, hsub, LinearMap.sub_apply, map_sub, LinearMap.zero_apply,
      sub_eq_zero]
    exact LinearMap.congr_fun h α
  rcases eq_or_ne ((g₁ : F) - (g₂ : F)) 0 with hd | hd
  · exact Subtype.ext (sub_eq_zero.mp hd)
  · exact absurd (weilSmul_injective hd (by rw [hg', map_zero])) hφ0

theorem ell_sub_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)] :
    ell (W - D) ≤ indexOfSpecialty D := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact LinearMap.finrank_le_finrank_of_injective (residuePairing_injective W D hφ hφ0)
theorem adeleSpaceMul_add [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f + g) = adeleSpaceMul K F f + adeleSpaceMul K F g := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.add_apply, Submodule.coe_add,
    Pi.add_apply, add_mul]

theorem adeleSpaceMul_zero [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (0 : F) = 0 := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply]

theorem weilSmul_add_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f + g) φ = weilSmul K F f φ + weilSmul K F g φ := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_add, LinearMap.add_apply, map_add]

theorem weilSmul_zero_left [HasPrincipalDivisors K F]
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (0 : F) φ = 0 := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_zero, LinearMap.zero_apply, map_zero]

theorem weilSmul_neg_left [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (-f) φ = -weilSmul K F f φ := by
  have h := weilSmul_add_left (K := K) (F := F) f (-f) φ
  rw [add_neg_cancel, weilSmul_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem weilSmul_sub_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f - g) φ = weilSmul K F f φ - weilSmul K F g φ := by
  rw [sub_eq_add_neg, weilSmul_add_left, weilSmul_neg_left, sub_eq_add_neg]

theorem weilSmul_eq_zero_iff_left [HasPrincipalDivisors K F]
    {f : F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    weilSmul K F f φ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ weilSmul_zero_left φ⟩
  by_contra hf
  exact hφ (weilSmul_injective hf (h.trans (map_zero (weilSmul K F f)).symm))

theorem weilSmul_left_injective [HasPrincipalDivisors K F]
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    Function.Injective (fun f : F => weilSmul K F f φ) := by
  intro f g hfg
  have hsub : weilSmul K F (f - g) φ = 0 := by
    rw [weilSmul_sub_left, sub_eq_zero]; exact hfg
  exact sub_eq_zero.mp ((weilSmul_eq_zero_iff_left hφ).mp hsub)

variable (K F) in

/-- The two-functional pairing used to exclude independent Weil differentials. -/
def doubleResiduePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) :
    LSpace (W - D) × LSpace (W - D) →ₗ[K] omegaSpace D :=
  (residuePairing K F W D hφ).coprod (residuePairing K F W D hμ)

theorem doubleResiduePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (g h : LSpace (W - D)) :
    (doubleResiduePairing K F W D hφ hμ (g, h) : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ + weilSmul K F (h : F) μ := by
  simp only [doubleResiduePairing, LinearMap.coprod_apply, Submodule.coe_add,
    residuePairing_apply_coe]

theorem doubleResiduePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ) :
    Function.Injective (doubleResiduePairing K F W D hφ hμ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, h⟩ heq

  have heq' : weilSmul K F (g : F) φ + weilSmul K F (h : F) μ = 0 := by
    have hcoe := congrArg Subtype.val heq
    rwa [doubleResiduePairing_apply_coe, Submodule.coe_zero] at hcoe

  rcases eq_or_ne (h : F) 0 with hh0 | hh0
  ·
    rw [hh0, weilSmul_zero_left, add_zero] at heq'
    have hg0 : (g : F) = 0 := (weilSmul_eq_zero_iff_left hφ0).mp heq'
    exact Prod.ext (Subtype.ext hg0) (Subtype.ext hh0)
  ·
    exfalso

    have hμeq : weilSmul K F (h : F) μ = -weilSmul K F (g : F) φ := by
      have h2 : weilSmul K F (h : F) μ + weilSmul K F (g : F) φ = 0 := by
        rw [add_comm]; exact heq'
      exact eq_neg_of_add_eq_zero_left h2

    have hLHS : weilSmul K F (h : F)⁻¹ (weilSmul K F (h : F) μ) = μ := by
      rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hh0, weilSmul_one,
        LinearMap.id_apply]
    have hRHS : weilSmul K F (h : F)⁻¹ (-weilSmul K F (g : F) φ)
        = weilSmul K F (-(g : F) * (h : F)⁻¹) φ := by
      rw [map_neg, ← LinearMap.comp_apply, ← weilSmul_mul, neg_mul, weilSmul_neg_left]
    exact hindep (-(g : F) * (h : F)⁻¹) (by rw [← hLHS, hμeq, hRHS])

theorem two_mul_ell_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)]
    [Module.Finite K (LSpace (K := K) (F := F) (W - D))] :
    2 * ell (W - D) ≤ indexOfSpecialty D := by
  have hinj := doubleResiduePairing_injective W D hφ hμ hφ0 hindep
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, two_mul]
  exact hle

end
end Dubon2026.SourceCurve
