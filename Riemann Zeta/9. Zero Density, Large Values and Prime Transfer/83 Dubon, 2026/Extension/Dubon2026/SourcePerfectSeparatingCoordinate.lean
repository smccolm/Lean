import Dubon2026.SourcePerfectCoordinateFrobenius
import Mathlib.Algebra.CharP.Algebra

/-! DUB-17/18 -> original Frobenius/inertia -> residue curve differentials ->
separability over the literal j coordinate. Over perfect constants in
characteristic p, a coordinate without a pth root separates every finite
extension inside the field. The degree comparison proves this criterion;
the actual j coordinate discharges its no-pth-root premise downstream.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_isCurveOver_modularFunctionFieldFullC.lean,
W5EC2.isSeparable_of_forall_pow_ne. The proof is rechecked on the local pin.
No resource-limit or linter overrides are retained. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IntermediateField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p]

theorem isSeparable_of_forall_pow_ne {x : L} (hx : ∀ u : L, u ^ p ≠ x)
    {y : L} (hy : IsIntegral K⟮x⟯ y) : IsSeparable K⟮x⟯ y := by
  classical
  by_contra hsep
  set E : IntermediateField K L := K⟮x⟯ with hE
  haveI : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  have hp : p.Prime := Fact.out

  have hirr : Irreducible (minpoly E y) := minpoly.irreducible hy
  obtain hs | ⟨-, g, hg, hgm⟩ := Polynomial.separable_or p hirr
  · exact hsep hs
  set z : L := y ^ p with hz
  have hgz : aeval z g = 0 := by
    rw [hz, ← expand_aeval p g y, hgm, minpoly.aeval]
  have hgmonic : g.Monic := by
    have h := minpoly.monic hy
    rw [← hgm] at h
    exact (monic_expand_iff hp.pos).mp h
  have hgmin : g = minpoly E z := minpoly.eq_of_irreducible_of_monic hg hgz hgmonic
  have hzint : IsIntegral E z := hy.pow p
  set r : ℕ := g.natDegree with hr
  have hrpos : 0 < r := by rw [hr, hgmin]; exact minpoly.natDegree_pos hzint
  have hdegm : (minpoly E y).natDegree = r * p := by rw [← hgm, natDegree_expand]

  let φ : L →+* L := frobenius L p
  set SE : Subfield L := E.toSubfield with hSE
  set SM : Subfield L := (restrictScalars K E⟮y⟯).toSubfield with hSM
  set SM₁ : Subfield L := (restrictScalars K E⟮z⟯).toSubfield with hSM₁
  set SE' : Subfield L := SE.map φ with hSE'
  set SM' : Subfield L := SM.map φ with hSM'

  have h1 : SE.relfinrank SM = r * p := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮y⟯) = r * p
    rw [relfinrank_adjoin_simple E hy, hdegm]

  have h2 : SE.relfinrank SM₁ = r := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮z⟯) = r
    rw [relfinrank_adjoin_simple E hzint, ← hgmin]

  have h3 : SE'.relfinrank SM' = r * p := by
    rw [hSE', hSM', Subfield.relfinrank_map_map, h1]

  have hE' : SE' = (K⟮x ^ p⟯).toSubfield := by
    rw [hSE', hSE, hE, map_frobenius_adjoin_toSubfield p, Set.image_singleton, frobenius_def]
  have hxpE : IsIntegral K⟮x ^ p⟯ x := by
    refine ⟨X ^ p - C (AdjoinSimple.gen K (x ^ p)), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    simp
  have hEeq : restrictScalars K (K⟮x ^ p⟯)⟮x⟯ = E := by
    rw [adjoin_simple_adjoin_simple, hE]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro u (rfl | rfl)
      · exact pow_mem (mem_adjoin_simple_self K x) p
      · exact mem_adjoin_simple_self K u
    · exact adjoin.mono K _ _ (Set.subset_insert _ _)
  have h4 : SE'.relfinrank SE ≤ p := by
    rw [hE', hSE, ← hEeq]
    change IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯) ≤ p
    rw [relfinrank_adjoin_simple _ hxpE]
    have hdvd : minpoly K⟮x ^ p⟯ x ∣ X ^ p - C (AdjoinSimple.gen K (x ^ p)) :=
      minpoly.dvd _ _ (by simp)
    calc (minpoly K⟮x ^ p⟯ x).natDegree
        ≤ (X ^ p - C (AdjoinSimple.gen K (x ^ p))).natDegree :=
          natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero hp.pos _)
      _ = p := natDegree_X_pow_sub_C
  have h4' : 0 < SE'.relfinrank SE := by
    rw [hE', hSE, ← hEeq]
    change 0 < IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯)
    rw [relfinrank_adjoin_simple _ hxpE]
    exact minpoly.natDegree_pos hxpE

  have hE'E : SE' ≤ SE := by
    rw [hSE']
    rintro _ ⟨u, hu, rfl⟩
    exact pow_mem hu p
  have hEM₁ : SE ≤ SM₁ := le_restrictScalars_adjoin E {z}
  have hEM : SE ≤ SM := le_restrictScalars_adjoin E {y}
  have hM'M₁ : SM' ≤ SM₁ := by
    rw [hSM', hSM]
    have hM : restrictScalars K E⟮y⟯ = adjoin K {x, y} := by
      rw [hE, adjoin_simple_adjoin_simple]
    rw [hM]
    refine (map_frobenius_adjoin_toSubfield_le p _).trans ?_
    change adjoin K (frobenius L p '' {x, y}) ≤ restrictScalars K E⟮z⟯
    rw [adjoin_le_iff]
    rintro u ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl
    · exact pow_mem (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K v)) p
    · change frobenius L p _ ∈ E⟮z⟯
      rw [frobenius_def, ← hz]
      exact mem_adjoin_simple_self E z
  have hE'M' : SE' ≤ SM' := by
    rw [hSE', hSM']
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hEM hu, rfl⟩

  have h5 : SE'.relfinrank SM₁ = SE'.relfinrank SE * r := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'E hEM₁, h2]
  have h6 : SE'.relfinrank SM₁ = r * p * SM'.relfinrank SM₁ := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'M' hM'M₁, h3]
  have hne : SE'.relfinrank SM₁ ≠ 0 := by
    rw [h5]; exact Nat.mul_ne_zero h4'.ne' hrpos.ne'
  have hone : SM'.relfinrank SM₁ = 1 := by
    have hle : SE'.relfinrank SE * r ≤ p * r := Nat.mul_le_mul_right r h4
    rw [← h5, h6] at hle
    have hk : SM'.relfinrank SM₁ ≠ 0 := fun h => hne (by rw [h6, h]; ring)
    have hk1 : SM'.relfinrank SM₁ ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : r * p * 2 ≤ r * p * SM'.relfinrank SM₁ := Nat.mul_le_mul_left _ hcon
      have hrp : 0 < r * p := Nat.mul_pos hrpos hp.pos
      nlinarith
    omega

  have hxM' : x ∈ SM' := by
    have hM₁M' : SM₁ ≤ SM' := Subfield.relfinrank_eq_one_iff.mp hone
    exact hM₁M' (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K x))
  rw [hSM'] at hxM'
  obtain ⟨u, -, hu⟩ := hxM'
  exact hx u hu

end
end Dubon2026.SourceCurve
