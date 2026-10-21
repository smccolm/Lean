import Dubon2026.SourceCurvePolePackage
import Dubon2026.SourceCurveDivisorProducts
import Dubon2026.SourceCurveDivisorDimensionGrowth
import Dubon2026.SourceCurveLSpaceFinite

/-! DUB-17/18 -> original function-field Riemann--Roch -> bounded global
index. Count the independent polynomial multiples in the concrete pole
package, then use the proved divisor-space increment bound and a
principal-divisor shift to bound degree minus dimension for every divisor.
Adapted from the selected PoleDivisorPackage argument in
S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The original-field consumer
constructs the package and supplies finite divisor spaces from prior proofs.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual divisor-degree minus dimension function has an integer upper bound. -/
def RiemannGenusBounded (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ

namespace PoleDivisorPackage

variable (P : PoleDivisorPackage K F)

theorem pow_mul_u_mem_lSpace (j : ℕ) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace ((j + P.c) • P.B) := by
  rw [add_nsmul]
  exact mul_mem_lSpace_add (pow_mem_lSpace_nsmul P.hx_mem j) (P.hu_mem i)

theorem pow_mul_u_mem_lSpace_of_le {j m : ℕ} (hjm : j + P.c ≤ m) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace (m • P.B) := by
  refine lSpace_mono ?_ (P.pow_mul_u_mem_lSpace j i)
  intro v
  have hBv : (0 : ℤ) ≤ P.B v := P.hB_eff v
  show ((j + P.c) • P.B) v ≤ (m • P.B) v
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hBv


theorem ell_nsmul_poleDivisor_ge [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    (P.n : ℤ) * (m - P.c + 1) ≤ ell (m • P.B) := by
  haveI := finite_lSpace (K := K) (m • P.B)

  set g : Fin (m - P.c + 1) × Fin P.n → LSpace (m • P.B) :=
    fun p => ⟨P.x ^ (p.1 : ℕ) * P.u p.2,
      P.pow_mul_u_mem_lSpace_of_le (by have := p.1.isLt; omega) p.2⟩
    with hgdef

  have hsub : LinearIndependent K (fun p => (g p : F)) := by
    have heq : (fun p => (g p : F))
        = (fun p : ℕ × Fin P.n => P.x ^ p.1 * P.u p.2)
            ∘ (fun p : Fin (m - P.c + 1) × Fin P.n => ((p.1 : ℕ), p.2)) := by
      funext p; rfl
    rw [heq]
    refine P.lin_indep.comp _ ?_
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.val_injective hpq.1) hpq.2

  have hg : LinearIndependent K g := hsub.of_comp (LSpace (m • P.B)).subtype

  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hZ : ((m - P.c + 1) * P.n : ℤ) ≤ (ell (m • P.B) : ℤ) := by exact_mod_cast hcard
  have heq : (((m - P.c + 1 : ℕ) : ℤ) * P.n : ℤ) = (P.n : ℤ) * ((m : ℤ) - P.c + 1) := by
    rw [Nat.cast_add, Nat.cast_sub hm, Nat.cast_one]; ring
  linarith

theorem degree_nsmul_sub_ell_le [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    Divisor.degree (m • P.B) - ell (m • P.B) ≤ (P.n : ℤ) * (P.c - 1) := by
  have hge := P.ell_nsmul_poleDivisor_ge hm
  have hdeg : Divisor.degree (m • P.B) = (m : ℤ) * P.n := by
    rw [show m • P.B = (m : ℤ) • P.B from (natCast_zsmul _ _).symm,
      Divisor.degree.map_zsmul, smul_eq_mul, P.degB_eq]
  linarith

end PoleDivisorPackage

theorem PoleDivisorPackage.ell_nsmul_sub_pos [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) {A : Divisor K F} (hA : 0 ≤ A) {m : ℕ} (hm : P.c ≤ m)
    (hbig : Divisor.degree A < (P.n : ℤ) * (m - P.c + 1)) :
    0 < ell (m • P.B - A) := by
  haveI := finite_lSpace (K := K) (m • P.B)
  have hle : m • P.B - A ≤ m • P.B := by
    intro v
    have hAv : (0 : ℤ) ≤ A v := hA v
    rw [Finsupp.sub_apply]
    linarith

  have h48 := ell_sub_ell_le_degree_sub_degree (K := K) hle
  rw [map_sub, sub_sub_cancel] at h48

  have h412 := P.ell_nsmul_poleDivisor_ge hm

  have : (0 : ℤ) < (ell (m • P.B - A) : ℤ) := by linarith
  exact_mod_cast this


theorem PoleDivisorPackage.degree_sub_ell_le [HasPrincipalDivisors K F] [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (P.n : ℤ) * (P.c - 1) := by
  classical

  set D' : Divisor K F := D ⊔ 0 with hD'def
  have hD'eff : 0 ≤ D' := le_sup_right
  have hDD' : D ≤ D' := le_sup_left
  haveI := finite_lSpace (K := K) D'
  have hmono : Divisor.degree D - (ell D : ℤ) ≤ Divisor.degree D' - ell D' := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hDD'
    linarith

  set m : ℕ := P.c + (Divisor.degree D').toNat with hmdef
  have hcm : P.c ≤ m := Nat.le_add_right _ _
  have hdegD' : 0 ≤ Divisor.degree D' := Divisor.degree_nonneg_of_nonneg hD'eff
  have hbig : Divisor.degree D' < (P.n : ℤ) * (m - P.c + 1) := by
    have hcast : ((m : ℤ) - P.c) = Divisor.degree D' := by
      simp only [hmdef, Nat.cast_add, add_sub_cancel_left, Int.toNat_of_nonneg hdegD']
    rw [hcast]
    have hn1 : (1 : ℤ) ≤ P.n := by exact_mod_cast P.hn_pos
    nlinarith

  have hellpos := P.ell_nsmul_sub_pos hD'eff hcm hbig
  have hnebot : LSpace (m • P.B - D') ≠ ⊥ :=
    fun h => by rw [ell, h, finrank_bot] at hellpos; exact lt_irrefl 0 hellpos
  obtain ⟨z, hzL, hz0⟩ := (Submodule.ne_bot_iff _).mp hnebot

  obtain ⟨Dz, hDzord, hDzdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzmem := (mem_lSpace_iff_ord.mp hzL).resolve_left hz0
  have hD'le : D' ≤ m • P.B + Dz := by
    intro v
    have := hzmem v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, neg_sub] at this ⊢
    rw [hDzord]; linarith

  have hellshift : ell (m • P.B + Dz) = ell (m • P.B) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • P.B) hz0 hDzord)).symm
  have hdegshift : Divisor.degree (m • P.B + Dz) = Divisor.degree (m • P.B) := by
    rw [map_add, hDzdeg, add_zero]

  haveI := finite_lSpace (K := K) (m • P.B + Dz)
  have hmono' : Divisor.degree D' - (ell D' : ℤ)
      ≤ Divisor.degree (m • P.B + Dz) - ell (m • P.B + Dz) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hD'le
    linarith
  rw [hellshift, hdegshift] at hmono'
  have h412 := P.degree_nsmul_sub_ell_le hcm
  linarith

theorem riemannGenusBounded_of_poleDivisorPackage [HasPrincipalDivisors K F] [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    RiemannGenusBounded K F :=
  ⟨(P.n : ℤ) * (P.c - 1), P.degree_sub_ell_le⟩


end
end Dubon2026.SourceCurve
