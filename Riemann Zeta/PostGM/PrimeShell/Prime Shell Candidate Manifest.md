# Prime Shell Candidate Manifest

Candidate date: 2026-08-30

This manifest identifies the corrected terminal-B candidate independently of an owner-created Git commit. The containing repository HEAD was `db7863ca9a2add22efd501907965f04c6e5e180c` with a dirty worktree; that commit is **not** claimed to contain the candidate. Commit and push remain owner-controlled actions.

## Immutable boundaries

- Frozen GM: `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`.
- Zeta23: `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, tag `v1.0`, Lean `v4.33.0-rc2`.
- Zeta23 Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.

## Candidate source hashes

The format is `SHA-256  path`. This list includes every Lean source in the isolated production tree.

```text
1CDEE44CCC9DB10EAD6111D23780A6FB386FE2F895D289DD613A0A4A4DF141BC  Extension/lakefile.toml
C5923579A204B3142B7EED3B8F3A8086BC5743FF7FFF4C55152AEDBC17411CDA  Extension/lake-manifest.json
0D3C76CCD8772D8BCBE207241421A760312B71A6AA82F84194391FDF5CB026D6  Extension/lean-toolchain
832BD8946502392FB7FD463D23CB5A3D16EEAEA24293D89D9E53565FD94BE7C6  Extension/PrimeShell.lean
ABA95165A012220880D99CB233292434E84B18E3F057016218AC37B640BCA017  Extension/PrimeShell/Admissible.lean
EB2823022B2A62A82044F8E52D6C0752E8085CA7F4267F68059113FCD358FD2B  Extension/PrimeShell/AmplitudeFamily.lean
F44B7941ED24A0380465044728F3528CFD210A8E9CB1E415B3E3939F168352FE  Extension/PrimeShell/AmplitudeNoGain.lean
3D9F2817B8FAD4217EE935AB265C8142D42F9D84AD6792038E822D79B5BE202D  Extension/PrimeShell/ArithmeticCoverage.lean
4F21FA5D0C8826893D402440D29FD836DAEFA4EA781B64366C4D248A7759E875  Extension/PrimeShell/Audit.lean
52E7E97BA68045EB857F2810448A497A5B35F319909552BFAE167E39F2E0E651  Extension/PrimeShell/CandidateConsumer.lean
99788167D226AEEB3DFE1C2B283F651716440B4BEED1A948D41A507B258D025C  Extension/PrimeShell/ConcreteAmplitudeNoGain.lean
FC01282DB1EDA8AC615DC64BE14F13E80353B5E668902CBFD63C082A6E7A90EF  Extension/PrimeShell/ConcreteF1.lean
88D4D4E09A6F92A26AD0DA4E53CB59A98BA45D2A8CA46EAC50F45AC2D307AF16  Extension/PrimeShell/ExtendedCertificate.lean
D7F0367CF4BEA4AC91EAEBB0368E2CC219CA1A95917F5538DC9F583E142EF25A  Extension/PrimeShell/ExtendedCertificateNumeric.lean
1B6FC96675E90B00D6F736F4F5BC709BAB508C2B6D6AA16D892076FEF19BBD39  Extension/PrimeShell/ExtendedFamilyHyps.lean
A7D2DDF80D3FC5FDF6DC0FCDE92C7705EFFF96F6C1EE93F8976E9A2531785A08  Extension/PrimeShell/ExtendedXiEF.lean
0D1F53A11B7094FDAEF20AE344D081E69CD28C87DD7466760818C361EC8ECC49  Extension/PrimeShell/ExtendedZeroSide.lean
EB31BCEC1370A62A750251ADF071B97590E01588131BEEE550213697B6877A98  Extension/PrimeShell/F1Verdict.lean
57F004F18F1515E9E304A0F9F54A9489FDE30FD6B233A70F00C5AC164CF60238  Extension/PrimeShell/GlobalBlock.lean
33B5B8AFDDB44A57B59B821284D7155FD12E42258DDBF8A4BEF002A279E08E48  Extension/PrimeShell/GMGridConsumer.lean
6DE0B3CB5EE7C504C0F3FC2AB733BDAE11558DA99D742FBE100712EC22FD56FF  Extension/PrimeShell/GMInterface.lean
9F375283EFB16B5A336DF4BE0E2EF8129278765356BA47902051D0080521EDFC  Extension/PrimeShell/KernelLocalization.lean
BA93AB00EA58103B6DEA19F1D51BC1AF0BBD653266AE5090FE74C5FA7521DDE6  Extension/PrimeShell/KernelSymmetry.lean
C73B821E59DAE971748845FBB441B47BD3F68CB1A46D4B20EAACEC2CCF830532  Extension/PrimeShell/LocalizedCorrelation.lean
D8EBA41892BA817EFD7065B541573B2DED49BB33E3B162ACE34C44B441C4F17F  Extension/PrimeShell/MRTInterface.lean
F040DF8497591C299279777BAD1AAFC75C0A4BA99A41C56FB878309877A9C24F  Extension/PrimeShell/PrimeTerm.lean
75E726CA2E6E07BA718EDDEC24D5EFA6182D41261058619654A03FA6659A28EF  Extension/PrimeShell/RowwiseTransfer.lean
E42006722D02BD86704684B00B80E584D46A6099ECC6EAA9CB444CF9AA9AA4D7  Extension/PrimeShell/ShellDensity.lean
E6FD5F9679447CDA9881CD7554332E3DFCAFE90176E9713E7BD9E2136D2EA0F8  Extension/PrimeShell/ShiftBlock.lean
C142B6409788C475BACB97ADCD5AEC6E9357DE158944B6FE041B31E9EB1721FF  Extension/PrimeShell/ShiftGrid.lean
0A25000B469BF3D362E0E9FC312F61677F68C7B6B017F1AA4E26C051AE2A0FE4  Extension/PrimeShell/ShiftKernel.lean
3A5EE26348D8D06265FB73EA98F58B56AC0BD36DD1CB8683C2AEB86A2D6C6473  Extension/PrimeShell/TwoBandAmplitude.lean
0E8A2581AE2A7CFA3E7874331979D9C899731BDDF13B5E08ECD9AFCFDF4A4024  Extension/PrimeShell/TwoBandSourceSplit.lean
482510A68D74D919B69B4E5790F783E1E740F631532E1831BE5CC7C0355E8C6B  Extension/PrimeShell/XiPrimeOracleConsumer.lean
F069DE4B0C1F217AEC23235C853AE33082C2BEBC0A1DECECAAE6E645196B454B  Extension/PrimeShell/XiShiftKernel.lean
EE5C9593448E538E8271519A0A36BB41D95115102ABD7F398F0C395C07709F47  Extension/PrimeShell/XiSourceBoundary.lean
```

## Fresh reproduction performed

A clean copy excluding `.lake` was created at:

```text
C:\Users\Naraphim\AppData\Local\Temp\PrimeShellRepro_20260830_034951
```

It ran:

```powershell
lake update
lake build
lake env lean PrimeShell\Audit.lean
```

All three commands exited `0`. `lake update` checked out the exact Zeta23 and Mathlib revisions recorded above. After the root-import closure check, the fresh build completed all 8984 jobs. It replayed warnings and informational linter output from the unchanged pinned Zeta23 dependency; those diagnostics are disclosed and were not filtered. Every `PrimeShell.*` build line succeeded without a Prime Shell warning, every one of the 31 non-audit submodules has a fresh `.olean`, and direct Prime Shell root/audit elaboration succeeded. The audit reported only `propext`, `Classical.choice`, and `Quot.sound`.

The terminal replay output is preserved verbatim in:

- `reproduction-logs/14-terminal-clean-copy-build.log`, SHA-256 `A7994C286ACCDB36D8A5D801CE03149DFF6788800394E92C9FEBD04BBC14CACB`
- `reproduction-logs/15-terminal-clean-copy-audit.log`, SHA-256 `77C19917C5DE2955135B818FC2FFD3A3F11536FC462EDDB66E545B8C766CAED3`

The final audit contains 145 declaration records, zero warnings, zero errors, and exactly the axiom set `{propext, Classical.choice, Quot.sound}`.

The frozen GM verifier separately returned `FINAL RESULT: PASS` under Lean `v4.30.0`. Evidence:

- `logs/foundation_freeze_20260830_040456.log`
- `logs/foundation_freeze_20260830_040456.json`

No Git push was run.
