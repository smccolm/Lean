import Dubon2026.OriginalCyclicCompositumLargeDegree
import Dubon2026.OriginalRelativeGaloisCompositum

/-! # Construct the actual auxiliary cyclic field tower

Choose a sufficiently large cyclic subfield inside the fixed arithmetic
union. Its two literal composita supply all relative Galois, cyclicity,
positive prime-power degree and divisibility conditions for DUB-17's
original class-generator transfer. The given extension need not be
cyclic or normal over the rationals.
-/
namespace Dubon2026
noncomputable section
open IntermediateField
attribute [-instance] SubfieldClass.instSMulRat

/-- A sufficiently large actual cyclic rational subfield supplies both auxiliary prime-power degrees and the required top Galois condition for the given finite Galois prime-power stage. -/
theorem originalCyclicAuxiliaryComposita_exists_degrees
    (U : Type) [Field U] [Algebra ℚ U]
    (K E D : IntermediateField ℚ U)
    [FiniteDimensional ℚ D] [hGalD : IsGalois ℚ D] [hcycD : IsCyclic Gal(D/ℚ)]
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    (hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E)
    (q t : ℕ) (hq : q.Prime)
    (hD : Module.finrank ℚ D = q ^ (Module.finrank ℚ E + t))
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    ∃ r s : ℕ,
      let L := K ⊔ D
      let M := E ⊔ D
      letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      letI : Algebra K L := (IntermediateField.inclusion (show K ≤ L from le_sup_left)).toAlgebra
      letI : Module K L := Algebra.toModule
      letI : Algebra E M := (IntermediateField.inclusion (show E ≤ M from le_sup_left)).toAlgebra
      letI : Module E M := Algebra.toModule
      letI : Algebra K M := (IntermediateField.inclusion (hKE.trans le_sup_left : K ≤ M)).toAlgebra
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = q ^ (r + 1) ∧
      IsGalois E M ∧ IsCyclic Gal(M/E) ∧ Module.finrank E M = q ^ (s + 1) ∧
      IsGalois K M ∧ Module.finrank K E ∣ q ^ (r + 1) := by
  let L := K ⊔ D
  let M := E ⊔ D
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : Algebra K L := (IntermediateField.inclusion (show K ≤ L from le_sup_left)).toAlgebra
  letI : Module K L := Algebra.toModule
  letI : Algebra E M := (IntermediateField.inclusion (show E ≤ M from le_sup_left)).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans le_sup_left : K ≤ M)).toAlgebra
  have hbase := IntermediateField.finrank_le_of_le_right hKE
  obtain ⟨hGalKL, hcyclicKL, r, htr, hdegreeKL⟩ :=
    originalCyclicCompositum_exists_large_primePower_degree U K D
      q (Module.finrank ℚ E + t) t hq hD (Nat.add_le_add_right hbase t)
  obtain ⟨hGalEM, hcyclicEM, s, _, hdegreeEM⟩ :=
    originalCyclicCompositum_exists_large_primePower_degree U E D
      q (Module.finrank ℚ E + t) t hq hD le_rfl
  have hGalKM : IsGalois K M := by
    have h := originalRelativeGaloisCompositum_isGalois U K E L hKE le_sup_left hGalKE hGalKL
    have heq : E ⊔ L = M := by
      dsimp only [L, M]
      rw [← sup_assoc, sup_eq_left.mpr hKE]
    letI : Algebra K (E ⊔ L : IntermediateField ℚ U) :=
      (IntermediateField.inclusion (hKE.trans le_sup_left)).toAlgebra
    letI : IsGalois K (E ⊔ L : IntermediateField ℚ U) := h
    let e : (E ⊔ L : IntermediateField ℚ U) ≃ₐ[K] M := {
      __ := (IntermediateField.equivOfEq heq).toRingEquiv
      commutes' _ := rfl }
    exact IsGalois.of_algEquiv e
  refine ⟨r, s, hGalKL, hcyclicKL, hdegreeKL, hGalEM, hcyclicEM, hdegreeEM, hGalKM, ?_⟩
  rw [hdegreeKE]
  exact pow_dvd_pow q (by omega : t ≤ r + 1)

end
end Dubon2026
