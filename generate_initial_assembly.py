"""Assemble actual kernel tangent checks with the original proved GNNW theorem."""
import json
from pathlib import Path

def main():
    manifest=json.loads(Path('lean/Kernel/InitialTangents/manifest.json').read_text())
    chunks=manifest['chunks']
    source='import InitialUniform\nimport Ramsey3683Bootstrap.Certificate\n'
    source+=''.join('import '+c['module'].replace('/','.')+'\n' for c in chunks)
    source+='namespace Compact3684.InitialProfile\n'
    source+='open RamseyLean Ramsey3683Bootstrap Elementary\n'
    source+='def chunks : List InitialChunk := [\n'
    source+=',\n'.join('InitialChunk.mk '+str(c['count'])+' Compact3684.InitialTangents.'+c['module'].rsplit('/',1)[1]+'.payload' for c in chunks)+']\n'
    source+='theorem chunks_checked : chunks.all InitialChunk.guard = true := by\n'
    rules=['chunks','List.all_cons','List.all_nil','InitialChunk.guard']
    rules+=['Compact3684.InitialTangents.'+c['module'].rsplit('/',1)[1]+'.checked' for c in chunks]
    rules+=['show decide (0 < ('+str(n)+' : Nat)) = true by decide' for n in sorted({c['count'] for c in chunks})]
    rules+=['Bool.and_self']
    source+='  simp only ['+', '.join(rules)+']\n'
    source+=f'theorem chunks_length : chunks.length = {len(chunks)} := by rfl\n'
    source+=f'def chunkAt (i : Fin {len(chunks)}) : InitialChunk := chunks[i.val]'+"'(by rw [chunks_length]; exact i.isLt)\n"
    source+=f'theorem chunkAt_checked (i : Fin {len(chunks)}) : (chunkAt i).guard = true := by\n'
    source+='  exact List.all_eq_true.mp chunks_checked _ (List.getElem_mem _)\n'
    source+=f'abbrev Index := Fin {len(chunks)} × Fin 256\n'
    source+='noncomputable def lines (i : Index) : AffineLine := (chunkAt i.1).line i.2.val\n'
    source+='noncomputable def profile : ℝ → ℝ := affineProfile lines\n'
    source+='theorem valid : UniformRamseyExpBound profile := by\n'
    source+='  apply Ramsey3683Bootstrap.UniformRamseyExpBound.affine_minimum lines\n'
    source+='  intro i\n'
    source+='  exact Compact3684.initial_uniform.weakenRate ((InitialChunk.sound (chunkAt_checked i.1) i.2.val).2.2)\n'
    source+='theorem positive (i : Index) : 0 < (lines i).intercept ∧ 0 < (lines i).slope := by\n'
    source+='  have h := InitialChunk.sound (chunkAt_checked i.1) i.2.val\n'
    source+='  exact ⟨h.1,h.2.1⟩\n'
    source+='#print axioms valid\nend Compact3684.InitialProfile\n'
    target=Path('lean/InitialProfile.lean')
    if target.exists() and target.read_text()!=source:raise SystemExit('Different existing generated proof data')
    target.write_text(source)
    print('Generated complete initial-profile assembly:',len(chunks),'chunks,',manifest['entries'],'lines',flush=True)

if __name__=='__main__':main()
