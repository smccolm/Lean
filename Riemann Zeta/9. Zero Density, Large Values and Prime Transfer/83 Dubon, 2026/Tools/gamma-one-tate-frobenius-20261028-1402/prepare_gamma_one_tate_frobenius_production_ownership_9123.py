from pathlib import Path
import json
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=json.loads((r/'Tools/source-gamma-one-tate-frobenius.json').read_text())['modules']
s=''.join('import '+m+'\n' for m in mods)+'import Lean\n\nopen Lean\n\n'
s+='private def inspectOwnership : CoreM Unit := do\n  let env ← getEnv\n'
s+='  let mods : Array Name := #['+', '.join('`'+m for m in mods)+']\n'
s+='''  for (name, info) in env.constants.toList do
    if info.isTheorem then
      if let some idx := env.getModuleIdxFor? name then
        let m := env.allImportedModuleNames[idx.toNat]!
        if mods.contains m then
          logInfo m!"OWNER {m}: {name}"
          match info with
          | .thmInfo th => logInfo m!"FINGERPRINT {name}: {hash th.type} {hash th.value}"
          | _ => throwError "Expected theorem"

#eval inspectOwnership
'''
assert not (p/'SourceGammaOneTateFrobeniusOwnership9123.lean').exists()
(p/'SourceGammaOneTateFrobeniusOwnership9123.lean').write_text(s,encoding='utf-8')
