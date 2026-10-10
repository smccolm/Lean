import Dubon2026.UnramifiedFractionValuations
import Dubon2026.PrincipalIdealValuationBridge

/-! # Actual unramified radical equations give original Selmer valuation conditions -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {R S K L : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

/-- The original radical equation at a genuine unramified extension prime forces the exact original valuation condition modulo n. -/
theorem unramified_radical_valuation_mod_one
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1)
    (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    v.valuationOfNeZeroMod n
      (QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range a) = 1 := by
  apply (valuationOfNeZeroMod_eq_one_iff v n a).mpr
  have h := congrArg w.valuationOfNeZero hβ
  rw [map_pow, unramified_valuationOfNeZero_algebraMap v w he] at h
  have hadd := congrArg Multiplicative.toAdd h
  refine ⟨(w.valuationOfNeZero β).toAdd, ?_⟩
  simpa only [Int.toAdd_pow, mul_comm] using hadd.symm

/-- If the original radical extension is unramified at an actual prime above every prime outside S, its original base-field power class lies in the genuine pinned Selmer group. -/
theorem unramified_radical_mem_selmer
    (T : Set (HeightOneSpectrum R))
    (hunram : ∀ v : HeightOneSpectrum R, v ∉ T →
      ∃ w : HeightOneSpectrum S, w.asIdeal.LiesOver v.asIdeal ∧
        v.asIdeal.ramificationIdx w.asIdeal = 1)
    (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range a ∈
      IsDedekindDomain.selmerGroup (R := R) (K := K) (S := T) (n := n) := by
  intro v hv
  obtain ⟨w, hlie, he⟩ := hunram v hv
  letI := hlie
  exact unramified_radical_valuation_mod_one v w he n a β hβ

end
end Dubon2026
