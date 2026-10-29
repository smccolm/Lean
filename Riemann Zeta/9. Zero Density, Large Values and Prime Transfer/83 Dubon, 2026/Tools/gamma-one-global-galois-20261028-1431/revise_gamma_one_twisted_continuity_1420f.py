from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedContinuity1420e.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('variable (Q p n w : ℕ)', '''private theorem eventually_one_of_open_controls {G A B R W : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid A]
    [Monoid B] [TopologicalSpace B] [DiscreteTopology B]
    [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : G →* A) (χ : G →ₜ* B) (τ : G →* Module.End R W) (U : Submodule R W)
    (ho : IsOpen {σ : G | ∀ x : W, τ σ x - x ∈ U})
    (hk : ∀ σ : G, χ σ = 1 → (∀ x : W, τ σ⁻¹ x - x ∈ U) → ρ σ = 1) :
    ∀ᶠ σ in 𝓝 (1 : G), ρ σ = 1 := by
  have hi := ho.preimage (continuous_inv : Continuous (fun σ : G => σ⁻¹))
  have hχ : IsOpen {σ : G | χ σ = 1} :=
    χ.continuous.isOpen_preimage {a | a = 1} (isOpen_discrete _)
  have hm : (1 : G) ∈ (fun σ : G => σ⁻¹) ⁻¹' {σ : G | ∀ x : W, τ σ x - x ∈ U} := by
    simpa only [Set.mem_preimage, inv_one, Set.mem_setOf_eq] using one_congruence τ U
  filter_upwards [hi.mem_nhds hm, hχ.mem_nhds χ.map_one] with σ hσ hc
  exact hk σ hc hσ

variable (Q p n w : ℕ)''')
start=s.index('  let U : Set G :=');end=s.index('\ntheorem binaryArithmeticTateGaloisRep_continuous',start)
s=s[:start]+'''  exact eventually_one_of_open_controls (binaryArithmeticTateGaloisRep Q p n w)
    (sourceAbsoluteCyclotomicCharacter N) (arithmeticTateGaloisRep M p)
    ((maximalIdeal ℤ_[p] ^ (n + 1)) • (⊤ : Submodule ℤ_[p] T))
    (arithmeticTateGalois_uniform_congruence_isOpen M p (n + 1))
    (binaryArithmeticTateGaloisRep_eq_one_of_congruence Q p n w)
'''+s[end:]
t=p/'SourceGammaOneTwistedContinuity1420f.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_continuity_1420e.ps1').read_text(encoding='utf-8').replace('1420e','1420f')
t=p/'build_gamma_one_twisted_continuity_1420f.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
