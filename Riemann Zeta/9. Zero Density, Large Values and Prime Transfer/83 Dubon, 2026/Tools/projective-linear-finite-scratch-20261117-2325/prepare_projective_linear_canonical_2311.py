from pathlib import Path
import json, hashlib, re
s = Path(__file__).parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
pairs = [
 ('SourceDicksonProjectiveConjugacy2300b', 'SourceDicksonProjectiveConjugacy'),
 ('SourceDicksonMatrixAlternatives2303a', 'SourceDicksonMatrixAlternatives'),
 ('SourceGammaOneProjectiveMatrixResidual2304a', 'SourceGammaOneProjectiveMatrixResidual'),
 ('SourceProjectivePerfectLift2305b', 'SourceProjectivePerfectLift'),
 ('SourceProjectiveSL2Lift2306a', 'SourceProjectiveSL2Lift'),
 ('SourceProjectiveSubfieldBounds2307c', 'SourceProjectiveSubfieldBounds'),
 ('SourceResidualLinearAlternatives2309b', 'SourceResidualLinearAlternatives'),
 ('SourceGammaOneProjectiveLinearResidual2310a', 'SourceGammaOneProjectiveLinearResidual'),
]
c = json.loads((s / 'source-projective-classification-audit-config-2302.json').read_text())
for version, name in pairs:
 source = s / (version + '.lean')
 assert (s / (version + '.exit')).read_text().strip() == '0'
 assert (s / (version + '.log')).stat().st_size == 0
 t = source.read_text('utf-8')
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|set_option|nolint)\b', t)
 for old, new in pairs:
  t = re.sub(r'(?m)^import ' + re.escape(old) + r'$', 'import ' + new, t)
 out = s / (name + '.lean')
 assert not out.exists()
 out.write_text(t, encoding='utf-8')
 strip = lambda v: re.sub(r'(?m)^import .+\n', '', v)
 assert strip(t) == strip(source.read_text('utf-8'))
 c['files'].append(dict(version=version, module=name, sourceSha256=sha(source),
                        canonicalSha256=sha(out), mathematicalBodyIdentical=True))
 c['modules'].append(name)
c['roots'] = ['Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_projective_linear_residual']
new_edges = [
 'psl_conjugate_to_standard', 'index_two_subgroup_eq_standardPSL',
 'pgl_subgroup_eq_standardPSL_of_card', 'card_PSL2_of_five_le',
 'hasProjectiveMatrixAlternatives_of_dickson', 'residual_projective_matrix_classification',
 'perfect_subgroup_le_of_center_quotient_map_le', 'subfieldSL2_projective_image',
 'subfieldSL2_le_of_projective_image', 'scalar_subfield_matrix_of_projective_mem',
 'projective_image_conjugate', 'exists_linear_subfield_bounds_of_projective_conjugacy',
 'small_projective_image_or_linear_subfield_bounds', 'residual_small_image_or_linear_bounds']
c['proofEdges'] += ['Dubon2026.SourceDickson.' + n for n in new_edges]
c['proofEdges'] += [c['roots'][0],
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_projective_matrix_residual',
 'Dubon2026.fieldSL2_isPerfect', 'Dubon2026.fieldSL2_mem_of_unipotents',
 'Dubon2026.fieldUpperUnipotent_commutator', 'Dubon2026.fieldLowerUnipotent_commutator']
c['scope'] = 'Original-form projective classification, explicit matrix conjugacy and linear subfield bounds; scratch only.'
c['routeAssessment'] = 'DUB-17 source Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power continuation -> automorphy -> residual large image. Reuse the complete pinned Dickson classification, extract its intermediate matrix equalities, and reuse native perfect SL2 to lift PSL2/PGL2 alternatives to literal linear subfield bounds. Six small-image alternatives, arithmetic coefficient-field comparison, local regularity and the final automorphy/continuation gates remain open.'
out = s / 'source-projective-linear-preparation-2311.json'
assert not out.exists()
out.write_text(json.dumps(c, indent=2) + '\n', encoding='utf-8')
enumerator = (s / 'SourceProjectiveClassificationDeclarations2301a.lean').read_text('utf-8')
enumerator = enumerator.replace('import SourceGammaOneProjectiveResidual',
                               'import SourceGammaOneProjectiveLinearResidual')
enumerator = re.sub(r'let mods : Array Name := #\[.*\]',
 'let mods : Array Name := #[' + ', '.join('`' + n for n in c['modules']) + ']', enumerator)
(s / 'SourceProjectiveLinearDeclarations2311.lean').write_text(enumerator, encoding='utf-8')
print(json.dumps(dict(modules=len(c['modules']), newModules=len(pairs),
                     requiredProofEdges=len(c['proofEdges']), preparationSha256=sha(out))))
