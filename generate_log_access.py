"""Assemble checked packed log chunks into a total logarithm lookup."""
import json
from pathlib import Path
from generate_profile_kernel import branch,emit

def main():
    data=json.loads(Path('lean/Kernel/PackedLogCatalog/manifest.json').read_text())
    code='import Kernel.CheckedLogChunk\n'
    code+=''.join('import '+c['module'].replace('/','.')+'\n' for c in data['chunks'])
    code+='namespace Compact3684.Log18.CheckedCatalog\n'
    names=[]
    for i,c in enumerate(data['chunks']):
        old='Compact3684.Log18.Packed.'+c['module'].rsplit('/',1)[1]
        name=f'chunk{i:03d}';names.append(name)
        code+=f'def {name} : CheckedChunk := ⟨{c["count"]}, {old}.payload, by decide, {old}.checked⟩\n'
    code+='def chunks (i : Nat) : CheckedChunk := '+branch(names)+'\n'
    code+='def entry (i : Nat) : CatalogEntry := (chunks (i/1024)).entry (i%1024)\n'
    code+='#print axioms entry\nend Compact3684.Log18.CheckedCatalog\n'
    emit(Path('lean/Kernel/CheckedCatalog.lean'),code)
    print('Generated checked access for',data['entries'],'logs in',len(names),'chunks',flush=True)

if __name__=='__main__':main()
