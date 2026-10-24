import Dubon2026.SourceEllipticIntegralInertiaCocycle

/-! Multiplication of the actual integral Galois coordinate cocycle
reduces to multiplication of residue coordinate changes on inertia.
This is the homomorphism law required to identify the inertia image with
the elliptic stabilizer in the DUB-17/18 exceptional-fiber census.
Native variable-change map homomorphisms and the proved trivial residue
action supply the law; no abstract action certificate is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite inertia reduction proof. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section

theorem residue_cocycle_mul
    {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
    (κ : VariableChange M) (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    (g h gh : VariableChange A)
    (hg : g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹)
    (hh : h.map A.subtype = κ * (κ.map (τ : M →+* M))⁻¹)
    (hgh : gh.map A.subtype = κ * (κ.map ((σ * τ : M ≃ₐ[F] M) : M →+* M))⁻¹) :
    gh.map (residue A) = g.map (residue A) * h.map (residue A) := by
  have hcomp : ((σ * τ : M ≃ₐ[F] M) : M →+* M) =
      (σ : M →+* M).comp (τ : M →+* M) := RingHom.ext fun _ => rfl
  have hmulA : (g * h.map (decompRingHom σ hσ)).map A.subtype =
      g.map A.subtype * (h.map (decompRingHom σ hσ)).map A.subtype :=
    (VariableChange.mapHom A.subtype).map_mul _ _
  have hmulM : (κ * (κ.map (τ : M →+* M))⁻¹).map (σ : M →+* M) =
      κ.map (σ : M →+* M) * ((κ.map (τ : M →+* M))⁻¹).map (σ : M →+* M) :=
    (VariableChange.mapHom (σ : M →+* M)).map_mul _ _
  have hinvM : ((κ.map (τ : M →+* M))⁻¹).map (σ : M →+* M) =
      ((κ.map (τ : M →+* M)).map (σ : M →+* M))⁻¹ :=
    map_inv (VariableChange.mapHom (σ : M →+* M)) _
  have hM : gh.map A.subtype = (g * h.map (decompRingHom σ hσ)).map A.subtype := by
    rw [hmulA, VariableChange.map_map, subtype_comp_decompRingHom,
      ← VariableChange.map_map, hgh, hg, hh, hmulM, hinvM, VariableChange.map_map, hcomp]
    group
  have hA : gh = g * h.map (decompRingHom σ hσ) :=
    VariableChange.map_injective Subtype.val_injective hM
  rw [hA]
  change VariableChange.mapHom (residue A) (g * h.map (decompRingHom σ hσ)) = _
  rw [map_mul]
  change g.map (residue A) * (h.map (decompRingHom σ hσ)).map (residue A) = _
  rw [VariableChange.map_map, residue_comp_decompRingHom σ hσ hI]

end
end Dubon2026.SourceEllipticReduction
