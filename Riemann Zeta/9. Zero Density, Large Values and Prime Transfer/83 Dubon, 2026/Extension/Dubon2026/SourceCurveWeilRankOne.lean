import Dubon2026.SourceCurveWeilPairing
import Dubon2026.SourceCurveGlobalIndex

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

theorem lSpace_eq_bot_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
theorem ell_eq_zero_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F} (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]

/-- Every nonzero Weil differential spans all Weil differentials over the function field. -/
def WeilDifferentialRankOne [HasPrincipalDivisors K F] : Prop :=
  ∀ {φ : Module.Dual K (adeleSpace K F)}, φ ∈ weilDifferentialModule K F → φ ≠ 0 →
    ∀ {μ : Module.Dual K (adeleSpace K F)}, μ ∈ weilDifferentialModule K F →
      ∃! f : F, μ = weilSmul K F f φ

theorem riemannInequality_of_genusReached [HasPrincipalDivisors K F]
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have heq := (indexOfSpecialty_eq_of_genusReached h D).2
  have hnn : (0 : ℤ) ≤ indexOfSpecialty D := Int.natCast_nonneg _
  linarith

section
variable [HasPrincipalDivisors K F] [∀ v : Place K F, Module.Finite K v.ResidueField]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]
theorem omegaSpace_finite_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  haveI := (indexOfSpecialty_eq_of_genusReached h D).1
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

variable [Nonempty (Place K F)]

theorem exists_weilSmul_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon

  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * γ.natAbs + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (Module.finrank K P.ResidueField : ℤ) := by
    rw [hD, map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (Module.finrank K P.ResidueField : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (Module.finrank K P.ResidueField : ℤ) := by exact_mod_cast (Module.finrank_pos (R := K) (M := P.ResidueField))
  have habsγ : -(|γ|) ≤ γ ∧ γ ≤ |γ| := ⟨neg_abs_le _, le_abs_self _⟩
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W ∧
      Divisor.degree W ≤ |Divisor.degree W| := ⟨neg_abs_le _, le_abs_self _⟩
  have hn_ge : 3 * |γ| + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (Module.finrank K P.ResidueField : ℤ) := by nlinarith [Int.natCast_nonneg n]

  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; nlinarith)

  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (Module.finrank K P.ResidueField : ℤ) - 1 + γ := by
    have hidx := (indexOfSpecialty_eq_of_genusReached h D).2
    rw [hellD, hdegD] at hidx; push_cast at hidx; linarith

  have hlowerWD : Divisor.degree W + (n : ℤ) * (Module.finrank K P.ResidueField : ℤ) + 1 - γ
      ≤ (ell (W - D) : ℤ) := by
    have hlow := riemannInequality_of_genusReached h (W - D)
    rw [hdegWD] at hlow; exact hlow

  haveI := omegaSpace_finite_of_genusReached h D
  haveI := finite_lSpace (K := K) (W - D)

  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith [habsγ.1, habsγ.2, habsW.1, habsW.2]

theorem weilDifferentialRankOne_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    WeilDifferentialRankOne (K := K) (F := F) := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_genusReached h hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end

theorem residuePairing_surjective_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne (K := K) (F := F))
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRankOne hφmem hφ0 hμmem
  rcases eq_or_ne f 0 with rfl | hf0
  ·
    have hμ0 : (⟨μ, hμD⟩ : omegaSpace D) = 0 :=
      Subtype.ext (hf.trans (weilSmul_zero_left φ))
    exact ⟨0, (map_zero _).trans hμ0.symm⟩
  ·

    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    have hPinv : ∀ v, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord v, v.ord_inv]
    have hinv : weilSmul K F f⁻¹ μ = φ := by
      rw [hf, ← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf0, weilSmul_one,
        LinearMap.id_apply]
    have hφD : φ ∈ omegaSpace (D + -P) := by
      rw [← hinv]; exact weilSmul_mem_omegaSpace_add (inv_ne_zero hf0) hPinv hμD
    have hDP : D + -P ≤ W := hWmax _ hφD
    have hfL : f ∈ LSpace (W - D) := by
      rw [mem_lSpace_iff_ord]; refine Or.inr fun v => ?_
      have hv := hDP v
      rw [Finsupp.add_apply, Finsupp.neg_apply, hPord v] at hv
      rw [Finsupp.sub_apply]; linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

end
end Dubon2026.SourceCurve
