import Dubon2026.SourceCupThreeNormLift

/-! The explicit characteristic-three cup primitive required by the odd twist.
DUB-17/18 -> residual modular Galois association -> weight-two reduction in
every prime characteristic -> characteristic-three odd twist -> a primitive
for the actual upper-right/lower-right character cup an original homomorphism.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
Existing actual entry formulas, permutation coordinates, coset transitions
and native SL2(Z) cocycle existence replace the duplicated source foundations.
-/

namespace Dubon2026.SourceCupThree
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

section Affine

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ] [CharP κ 3]
variable (x : Additive (Gamma0 M) →+ κ)

/-- An actual native SL2(Z) cocycle whose affine coefficient is the original normalized induced cocycle. -/
theorem exists_affine_cocycle :
    ∃ z : SL(2, ℤ) → ZMod 3 → Q M → κ, z ∈ cocycles₁ (Rep.of (rhoX M h3M κ)) ∧
      ∀ g : SL(2, ℤ), ∃ K : Q M → κ, z g = fun i y => cst κ i * zY' M κ x g y + K y := by
  set u'' : Q M → κ := zY' M κ x R with hu''def
  have hu'' : ∀ y : Q M, u'' y + u'' (R⁻¹ • y) + u'' (R⁻¹ • R⁻¹ • y) = 0 := norm_zY'_R_apply M κ x
  set u := uu M κ u'' with hudef
  have hx0 : (0 : ZMod 3 → Q M → κ) + rhoX M h3M κ ModularGroup.S 0 = 0 := by simp
  have hu : u + rhoX M h3M κ (ModularGroup.S * ModularGroup.T) u
      + rhoX M h3M κ (ModularGroup.S * ModularGroup.T) (rhoX M h3M κ (ModularGroup.S * ModularGroup.T) u) = 0 :=
    norm_uu M h3M κ u'' hu''
  obtain ⟨zc, hzS, hzR⟩ :=
    sourceSL2Cocycle_exists (rhoX M h3M κ) 0 u hx0 hu
  let z : SL(2, ℤ) → ZMod 3 → Q M → κ := fun g => zc g
  have hz : z ∈ cocycles₁ (Rep.of (rhoX M h3M κ)) := zc.property
  change z ModularGroup.S = 0 at hzS
  change z (ModularGroup.S * ModularGroup.T) = u at hzR
  have hz' := zY'_mem M κ x
  refine ⟨z, hz, ?_⟩

  let P : SL(2, ℤ) → Prop := fun g => ∃ K : Q M → κ, (z : SL(2, ℤ) → ZMod 3 → Q M → κ) g
    = fun i y => cst κ i * zY' M κ x g y + K y
  have hP1 : P 1 := ⟨0, by
    funext i y
    rw [cocycle_one hz, cocycle_one hz']
    simp⟩
  have hPmul : ∀ g h, P g → P h → P (g * h) := by
    rintro g h ⟨Kg, hKg⟩ ⟨Kh, hKh⟩
    refine ⟨fun y => Kg y + cst κ (cc M g y) * zY' M κ x h (g⁻¹ • y) + Kh (g⁻¹ • y), ?_⟩
    funext i y
    rw [cocycle_mul hz g h, Pi.add_apply, Pi.add_apply, rhoX_apply, hKg, hKh, cocycle_mul hz' g h]
    simp only [Pi.add_apply, permRep_apply, map_add]
    ring
  have hPinv : ∀ g, P g → P g⁻¹ := by
    rintro g ⟨Kg, hKg⟩
    refine ⟨fun y => -(cst κ (cc M g⁻¹ y) * zY' M κ x g (g • y) + Kg (g • y)), ?_⟩
    funext i y
    rw [cocycle_inv hz g, cocycle_inv hz' g]
    simp only [Pi.neg_apply, rhoX_apply, permRep_apply, inv_inv, hKg, map_add]
    ring
  have hPS : P ModularGroup.S := ⟨0, by
    funext i y
    change (z : SL(2, ℤ) → ZMod 3 → Q M → κ) ModularGroup.S i y = cst κ i * zY' M κ x ModularGroup.S y + 0
    rw [hzS, ← S_def, zY'_S]; simp⟩
  have hPR : P (ModularGroup.S * ModularGroup.T) := ⟨kk M κ u'', by
    funext i y
    change (z : SL(2, ℤ) → ZMod 3 → Q M → κ) (ModularGroup.S * ModularGroup.T) i y = _
    rw [hzR]
    rfl⟩
  have hPT : P ModularGroup.T := by
    have : (ModularGroup.T : SL(2, ℤ)) = (ModularGroup.S)⁻¹ * (ModularGroup.S * ModularGroup.T) := by
      rw [inv_mul_cancel_left]
    rw [this]
    exact hPmul _ _ (hPinv _ hPS) hPR
  intro g
  have hg : g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hg using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | rfl
    · exact hPS
    · exact hPT
  | one => exact hP1
  | mul a b _ _ iha ihb => exact hPmul a b iha ihb
  | inv a _ ih => exact hPinv a ih

end Affine

end
end Dubon2026.SourceCupThree
