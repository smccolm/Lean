from pathlib import Path
p=Path(__file__).parent
s=(p/'record_original_kummer_cell_calculus_529.py').read_text(encoding='utf-8-sig')
s=s.replace('source-original-kummer-cell-calculus-7','source-original-coefficient-weil-6').replace('SourceOriginalKummerCellCalculusAudit7','SourceOriginalCoefficientWeilAudit6').replace('SourceOriginalKummerCellCalculusDependencyAudit7','SourceOriginalCoefficientWeilDependencyAudit6')
s=s.replace('==(7,7,13)','==(6,11,18)').replace('KUMMER CELL CALCULUS','COEFFICIENT WEIL').replace('count==18','count==13').replace('all 13 required','all 18 required')
s=s.replace("==7\ncount=","==6\ncount=").replace('linterScopes=7','linterScopes=6')
s=s.replace('kummer-cell-calculus-route-529','coefficient-weil-route-560').replace('requiredProofValueEdges=13','requiredProofValueEdges=18').replace('modules=7,queries=7','modules=6,queries=11').replace('proofEdges=13','proofEdges=18')
start=s.index("discharged='");end=s.index('\nremaining=',start)
s=s[:start]+"discharged='Native finite-source Hom base change and flat tensor injection prove injectivity of the actual original Weil pairing after arbitrary coefficient-field extension, retaining its literal root-valued tensor target. The actual rational Tate finiteness theorem discharges the finite-source input. Alternation, adjointness at primes away from the level and the actual cyclotomic multiplier are preserved. No coefficient-extension nondegeneracy or pairing-law premise remains. Separate supporting lemmas prove adjointness of the precise sum of squared shifted operators and its polynomial, and injectivity on the image of a self-adjoint idempotent. Those generic lemmas retain explicit operator conditions until the actual Tate projector supplies them; they do not yet identify the required nonzero rank-two component.'"+s[end:]
s=s.replace('source-original-kummer-coordinate-inverse-2-scratch-receipt','source-original-rational-weil-6-scratch-receipt').replace('CD6E89C1F3C8D4D8A0E8DCC2CE69E909B4D51FDF3971049293B2A84A4CED3BA3','E8418D11FCD1A6F09D2178342758A698D5CB16FEEB2711EC89C13F9D6D413738')
exec(compile(s,str(__file__)+' generated','exec'))
