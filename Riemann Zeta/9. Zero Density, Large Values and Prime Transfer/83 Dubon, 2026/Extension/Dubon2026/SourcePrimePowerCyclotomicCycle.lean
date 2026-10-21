import Dubon2026.SourcePrimePowerRootOrbit

/-! DUB-17/18 -> numerical modular genus -> composite j-map degree
-> prime-power extension lower degree. A generator of the nonzero residue
classes is realized by the actual cyclotomic Galois group and cycles the
nontrivial twisted roots. Coefficient automorphisms fix rational Laurent
series. SourcePrimePowerExactFieldDegree uses this action to prove the
step degree under the explicit next-series nonmembership condition.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section

theorem exists_cyclotomic_root_cycle (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {p} ℚ K]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (e : ℕ) [NeZero e] :
    ∃ (g : (ZMod p)ˣ) (τ : K ≃ₐ[ℚ] K),
      (∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) ∧
      ∀ i : ℕ, coeffMapEquiv τ (rUnit e ζ g i) =
        rUnit e ζ g ((i + 1) % (p - 1)) := by
  have hirrcyc : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hp.out.pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units p]
  have hg1 : g ^ (p - 1) = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one g
  have hgmod : ∀ a : ℕ, g ^ a = g ^ (a % (p - 1)) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a (p - 1)]
    rw [pow_add, pow_mul, hg1, one_pow, one_mul]
  have hsurj : Function.Surjective (hζ.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨hζ.autToPow_injective (K := ℚ),
        Nat.card_congr (IsCyclotomicExtension.autEquivPow K hirrcyc).toEquiv⟩).2
  obtain ⟨τ, hτ⟩ := hsurj g
  have hτζ : τ (ζ : K) = (ζ : K) ^ ((g : ZMod p)).val := by
    have h := hζ.autToPow_spec ℚ τ
    rw [hτ] at h
    exact h.symm
  have hτζu : Units.map (τ : K →ₐ[ℚ] K).toRingHom.toMonoidHom ζ =
      ζ ^ ((g : ZMod p)).val :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hτζ)
  have hζp : ζ ^ p = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hζmod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % p) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a p]
    rw [pow_add, pow_mul, hζp, one_pow, one_mul]
  have hstep : ∀ i : ℕ, coeffMapEquiv τ (rUnit e ζ g i) = rUnit e ζ g (i + 1) := by
    intro i
    rw [rUnit, rUnit, coeffMapEquiv_apply]
    calc
      _ = TS K e (Units.map (τ : K →ₐ[ℚ] K).toRingHom.toMonoidHom
          (ζ ^ ((g ^ i : (ZMod p)ˣ) : ZMod p).val)) :=
        coeffMap_TS (τ : K →ₐ[ℚ] K) e _
      _ = TS K e (ζ ^ ((g ^ (i + 1) : (ZMod p)ˣ) : ZMod p).val) := by
        congr 1
        rw [map_pow, hτζu, ← pow_mul,
          hζmod (((g : ZMod p)).val * ((g ^ i : (ZMod p)ˣ) : ZMod p).val)]
        congr 1
        rw [pow_succ', Units.val_mul, ZMod.val_mul]
  refine ⟨g, τ, hg, fun i => ?_⟩
  rw [hstep i, rUnit, rUnit]
  exact congrArg (fun u : (ZMod p)ˣ => TS K e (ζ ^ ((u : ZMod p)).val)) (hgmod (i + 1))

end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
