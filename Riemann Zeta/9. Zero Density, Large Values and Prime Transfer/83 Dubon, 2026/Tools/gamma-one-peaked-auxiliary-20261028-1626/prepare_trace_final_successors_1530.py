from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralTraceDegenerateCusp1527b.lean';b=s/'SourceIntegralTraceDegenerateCusp1527c.lean';assert not b.exists()
t=a.read_text(encoding='utf-8')
start=t.index('  rw [SlashInvariantForm.slash_action_eqn G _');end=t.index('  have hper',start)
t=t[:start]+'''  have hGS' := hGS.trans (slash_eq_of_mem_or_neg_mem G hk (ModularGroup.T ^ j)⁻¹
    (Or.inl (Γ.inv_mem (Γ.zpow_mem hT1 j))))
  rw [hGS']
'''+t[end:]
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
a=s/'SourceIntegralTraceDecomposition1526a.lean';b=s/'SourceIntegralTraceDecomposition1526b.lean';assert not b.exists()
t=a.read_text(encoding='utf-8')
start=t.index('    refine Asymptotics.IsBigO.fun_sum');end=t.index('  have hC0',start)
t=t[:start]+'''    have hterm : ∀ x ∈ C,
        ((⇑X : ℍ → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) =O[atImInfty]
          fun τ : ℍ => Real.exp (-(2 * Real.pi * ((r : ℝ) * ((m₀ : ℝ) + δ))) * τ.im) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hXslash x]
      exact isBigO_mul_pow_exp _ _ (isBoundedAtImInfty_slash G x) _
        (hdecay x (hrest x hx.1 hx.2.1 hx.2.2).1 (hrest x hx.1 hx.2.1 hx.2.2).2) r
    exact (Asymptotics.IsBigO.sum hterm).congr'
      (Filter.Eventually.of_forall fun _ => rfl) Filter.EventuallyEq.rfl
'''+t[end:]
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
f=s/'SourceEvenWeightPeakedTraceIntegrality1529a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('import SourceIntegralTraceDecomposition1526a','import SourceIntegralTraceDecomposition1526b').replace('import SourceIntegralTraceDegenerateCusp1527b','import SourceIntegralTraceDegenerateCusp1527c'),encoding='utf-8')
