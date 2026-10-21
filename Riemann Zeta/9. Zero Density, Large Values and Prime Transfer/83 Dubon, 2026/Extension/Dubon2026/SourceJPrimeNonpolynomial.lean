import Dubon2026.SourceJPrimeOrbitObstruction
import Dubon2026.SourceJPositiveCoefficients
import Dubon2026.SourceLaurentCoefficientReindex
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> numerical modular genus -> exact j-map degree ->
prime lower bound. The literal q-substituted j series cannot be a polynomial
in j: its root-of-unity orbit would force a positive j coefficient to vanish.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean.
Only the coefficient obstruction is selected; field integrality is supplied
by the already proved actual monic relation, without an irreducibility input.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K]

section Ascent

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private theorem coeffMap_algebraMap' {K' : Type*} [Field K'] (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]

theorem coeffMap_aeval_jqModC {K' : Type*} [Field K'] (σ : K →+* K') (P : Polynomial K) :
    coeffMap σ (Polynomial.aeval (jqModC K) P) = Polynomial.aeval (jqModC K') (P.map σ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  have hcomp : (coeffMap σ).comp (algebraMap K (LaurentSeries K)) = (algebraMap K' (LaurentSeries K')).comp σ :=
    RingHom.ext fun c => coeffMap_algebraMap' σ c
  rw [hcomp]
  congr 1
  exact map_jqModC σ

theorem aeval_jqModC_ne_jqNModC (hpK : (p : K) ≠ 0) {m : ℕ} (hm : 0 < m) (hw : (jqModC K).coeff ((p * m : ℕ) : ℤ) ≠ 0)
    (P : Polynomial K) : Polynomial.aeval (jqModC K) P ≠ jqNModC K p := by
  intro h
  haveI : NeZero ((p : ℕ) : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  set σ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hσ
  have hzu : IsUnit z := hz.isUnit hp.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) p := by
    rw [IsUnit.unit_spec]
    exact hz
  have hpK' : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast σ]
    exact (map_ne_zero σ).mpr hpK
  have hw' : (jqModC (AlgebraicClosure K)).coeff ((p * m : ℕ) : ℤ) ≠ 0 := by
    rw [← map_jqModC σ]
    exact (map_ne_zero σ).mpr hw
  have h' : Polynomial.aeval (jqModC (AlgebraicClosure K)) (P.map σ) = jqNModC (AlgebraicClosure K) p := by
    rw [← coeffMap_aeval_jqModC, h, jqNModC, jqNModC, Dubon2026.SourceFunctionField.coeffMap_qExpand]
    congr 1
    exact map_jqModC σ
  exact aeval_jqModC_ne_jqNModC_of_isPrimitiveRoot hpK' hζ hm hw' (P.map σ) h'

end Ascent

theorem aeval_jqModC_ne_jqNModC_charZero [CharZero K]
    (p : ℕ) [hp : Fact p.Prime] (P : Polynomial K) :
    Polynomial.aeval (jqModC K) P ≠ jqNModC K p := by
  refine aeval_jqModC_ne_jqNModC (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    (m := 1) Nat.one_pos ?_ P
  have hz : (jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) ≠ 0 := by
    intro h0
    have h1 := one_le_coeff_jq (p * 1)
    have h2 : jq.coeff ((p * 1 : ℕ) : ℤ) =
        (((jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
      rw [← jqModC_rat, jqModC_eq_map_intCast]
      rfl
    rw [h2, h0] at h1
    norm_num at h1
  have h3 : (jqModC K).coeff ((p * 1 : ℕ) : ℤ) =
      (((jqModC ℤ).coeff ((p * 1 : ℕ) : ℤ) : ℤ) : K) := by
    rw [jqModC_eq_map_intCast]
    rfl
  rw [h3]
  exact Int.cast_ne_zero.mpr hz

end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
