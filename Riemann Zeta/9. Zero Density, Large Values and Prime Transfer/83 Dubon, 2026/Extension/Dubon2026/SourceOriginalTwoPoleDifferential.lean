import Dubon2026.SourceOriginalTwoPoleDimensions

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
prescribed third-kind residues. Existing original Riemann--Roch and the
proved negative-degree vanishing give a differential with exactly two
simple poles. No Riemann--Roch or degree hypothesis is supplied externally.
Adapted from S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

private theorem exists_mem_not_mem_not_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A B C : Submodule R M} (hA : A < C) (hB : B < C) :
    ∃ x ∈ C, x ∉ A ∧ x ∉ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haC, haA⟩ := SetLike.exists_of_lt hA
  obtain ⟨b, hbC, hbB⟩ := SetLike.exists_of_lt hB
  have haB : a ∈ B := hcon a haC haA
  have hbA : b ∈ A := by
    by_contra h
    exact hbB (hcon b hbC h)
  rcases em (a + b ∈ A) with hab | hab
  · exact haA (by simpa using A.sub_mem hab hbA)
  · have habB : a + b ∈ B := hcon (a + b) (C.add_mem haC hbC) hab
    exact hbB (by simpa using B.sub_mem habB haB)

variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_two_pole_function {ω₀ : Ω[F⁄ℂ]} (hω₀ : ω₀ ≠ 0)
    (P Q : Place ℂ F) :
    let K₀ := originalCanonicalDivisor N ℂ hω₀
    let P1 : Divisor ℂ F := Finsupp.single P 1
    let Q1 : Divisor ℂ F := Finsupp.single Q 1
    ∃ h ∈ LSpace (K₀ + P1 + Q1), h ∉ LSpace (K₀ + P1) ∧ h ∉ LSpace (K₀ + Q1) := by
  classical
  set K₀ := originalCanonicalDivisor N ℂ hω₀
  set P1 : Divisor ℂ F := Finsupp.single P 1 with hP1
  set Q1 : Divisor ℂ F := Finsupp.single Q 1 with hQ1
  obtain ⟨hellP, hellQ⟩ := original_two_pole_dimensions N hω₀ P Q
  have hP1nn : 0 ≤ P1 := fun v => by
    rw [hP1, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  have hQ1nn : 0 ≤ Q1 := fun v => by
    rw [hQ1, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  have hAle : LSpace (K₀ + P1) ≤ LSpace (K₀ + P1 + Q1) :=
    lSpace_mono (le_add_of_nonneg_right hQ1nn)
  have hBle : LSpace (K₀ + Q1) ≤ LSpace (K₀ + P1 + Q1) :=
    lSpace_mono (by rw [add_right_comm]; exact le_add_of_nonneg_right hP1nn)
  have hAlt : LSpace (K₀ + P1) < LSpace (K₀ + P1 + Q1) := by
    refine lt_of_le_of_ne hAle fun heq => ?_
    have : ell (K₀ + P1) = ell (K₀ + P1 + Q1) := congrArg (fun S : Submodule ℂ F => Module.finrank ℂ S) heq
    rw [this] at hellP
    linarith
  have hBlt : LSpace (K₀ + Q1) < LSpace (K₀ + P1 + Q1) := by
    refine lt_of_le_of_ne hBle fun heq => ?_
    have : ell (K₀ + Q1) = ell (K₀ + P1 + Q1) := congrArg (fun S : Submodule ℂ F => Module.finrank ℂ S) heq
    rw [this] at hellQ
    linarith
  exact exists_mem_not_mem_not_mem hAlt hBlt


theorem exists_original_two_pole_differential {P Q : Place ℂ F} (hPQ : P ≠ Q) :
    ∃ ω : Ω[F⁄ℂ], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place ℂ F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by
  classical
  haveI : HasPrincipalDivisors ℂ F := hasPrincipalDivisors_original N ℂ
  haveI : ∀ v : Place ℂ F, v.DCoordGenerates := original_place_dCoordGenerates N ℂ
  haveI : Nontrivial Ω[F⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄ℂ])
  have hsmul {h : F} (hh : h ≠ 0) (v : Place ℂ F) :
      v.ordDifferential (h • ω₀) = v.ord h + originalCanonicalDivisor N ℂ hω₀ v := by
    have hc : v.differentialCoeff ω₀ ≠ 0 := by
      intro h0
      apply hω₀
      rw [← v.differentialCoeff_smul_dCoord ω₀, h0, zero_smul]
    rw [originalCanonicalDivisor_apply, v.ordDifferential_smul hh hc]
  set K₀ : Divisor ℂ F := originalCanonicalDivisor N ℂ hω₀
  set P1 : Divisor ℂ F := Finsupp.single P 1 with hP1
  set Q1 : Divisor ℂ F := Finsupp.single Q 1 with hQ1
  obtain ⟨h, hC, hA, hB⟩ := exists_original_two_pole_function N hω₀ P Q

  have hh0 : h ≠ 0 := fun h0 => hA (h0 ▸ (LSpace (K₀ + P1)).zero_mem)
  have hCord : ∀ v : Place ℂ F, -(K₀ + P1 + Q1) v ≤ v.ord h :=
    (mem_lSpace_iff_ord.mp hC).resolve_left hh0
  have hAord : ∃ v, v.ord h < -(K₀ + P1) v := by
    by_contra hcon
    push Not at hcon
    exact hA (mem_lSpace_iff_ord.mpr (Or.inr hcon))
  have hBord : ∃ v, v.ord h < -(K₀ + Q1) v := by
    by_contra hcon
    push Not at hcon
    exact hB (mem_lSpace_iff_ord.mpr (Or.inr hcon))

  have eP1P : P1 P = 1 := by rw [hP1, Finsupp.single_eq_same]
  have eQ1Q : Q1 Q = 1 := by rw [hQ1, Finsupp.single_eq_same]
  have eP1 : ∀ v, v ≠ P → P1 v = 0 := fun v hv => by rw [hP1, Finsupp.single_eq_of_ne hv]
  have eQ1 : ∀ v, v ≠ Q → Q1 v = 0 := fun v hv => by rw [hQ1, Finsupp.single_eq_of_ne hv]

  have hQord : Q.ord h + K₀ Q = -1 := by
    obtain ⟨v, hv⟩ := hAord
    by_cases hvQ : v = Q
    · subst hvQ
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hPQ.symm, eQ1Q] at h1 hv
      linarith
    · exfalso
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eQ1 v hvQ] at h1 hv
      linarith

  have hPord : P.ord h + K₀ P = -1 := by
    obtain ⟨v, hv⟩ := hBord
    by_cases hvP : v = P
    · subst hvP
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eQ1 v hPQ, eP1P] at h1 hv
      linarith
    · exfalso
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hvP] at h1 hv
      linarith

  refine ⟨h • ω₀, smul_ne_zero hh0 hω₀, ?_, ?_, fun v hvP hvQ => ?_⟩
  · exact (hsmul hh0 P).trans hPord
  · exact (hsmul hh0 Q).trans hQord
  · rw [hsmul hh0]
    have h1 := hCord v
    simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hvP, eQ1 v hvQ] at h1
    linarith

end
end Dubon2026.SourceFunctionField
