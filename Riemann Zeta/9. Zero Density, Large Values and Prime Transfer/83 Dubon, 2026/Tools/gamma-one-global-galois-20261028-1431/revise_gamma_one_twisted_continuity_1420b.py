from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedContinuity1420a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('variable (Q p n w : ℕ)', '''private theorem continuous_discrete_of_eventually_one {G A : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Monoid A] (ρ : G →* A)
    (h : ∀ᶠ σ in 𝓝 (1 : G), ρ σ = 1) : @Continuous G A _ ⊥ ρ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  exact h.mono (fun _ he => he.symm)

variable (Q p n w : ℕ)''')
s=s.replace('''    letI : TopologicalSpace (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) := ⊥
    Continuous (binaryArithmeticTateGaloisRep Q p n w) := by
  letI : TopologicalSpace (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) := ⊥
  letI : DiscreteTopology (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) := ⟨rfl⟩''','''    @Continuous G (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) _ ⊥
      (binaryArithmeticTateGaloisRep Q p n w) := by''')
s=s.replace('''  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  filter_upwards''','''  apply continuous_discrete_of_eventually_one
  filter_upwards''')
s=s.replace('  exact (hs hc hσ).symm','  exact hs hc hσ')
t=p/'SourceGammaOneTwistedContinuity1420b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_continuity_1420.ps1').read_text(encoding='utf-8').replace('1420a','1420b')
t=p/'build_gamma_one_twisted_continuity_1420b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
