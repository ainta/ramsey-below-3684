"""Generate the real-soundness assembly for checked catalog chunks.

This is proof-data generation only: the emitted theorem must still compile.
The full assembly is the default; --count supports bounded import benchmarks.
"""
import argparse
import json
from pathlib import Path

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--count',type=int)
    parser.add_argument('--manifest',type=Path,default=Path('lean/Kernel/LogCatalog/manifest.json'))
    parser.add_argument('--output',type=Path,default=Path('lean/Kernel/LogCatalogSound.lean'))
    args=parser.parse_args()
    manifest=json.loads(args.manifest.read_text())
    chunks=manifest['chunks'][:args.count]
    names=[c['module'].rsplit('/',1)[1] for c in chunks]
    namespace=manifest.get('namespace','Compact3684.Log18.Catalog')
    guard='guards' if manifest.get('packed') else 'checked'
    source='import Kernel.LogInterval\n'
    source+=''.join('import '+c['module'].replace('/','.')+'\n' for c in chunks)
    source+='set_option maxRecDepth 100000\n'
    source+='namespace Compact3684.Log18.AssembledCatalog\n'
    source+='def chunks : List (List CatalogEntry) := [\n'
    source+=',\n'.join(namespace+'.'+name+'.entries' for name in names)+']\n'
    source+='theorem checked : chunks.all (fun entries => entries.all catalogGuard) = true := by\n'
    source+='  simp only [chunks, List.all_cons, List.all_nil, '+', '.join(namespace+'.'+name+'.'+guard for name in names)+', Bool.and_self]\n'
    source+='theorem sound : ∀ entries ∈ chunks, ∀ entry ∈ entries,\n'
    source+='    Contains (entry.lo,entry.hi) (Real.log ((entry.argument : ℝ)/scale)) := by\n'
    source+='  intro entries he\n'
    source+='  exact catalogAll_sound entries (List.all_eq_true.mp checked entries he)\n'
    source+='#print axioms sound\nend Compact3684.Log18.AssembledCatalog\n'
    if args.output.exists() and args.output.read_text()!=source:
        raise SystemExit('Refusing to overwrite different proof data: '+str(args.output))
    args.output.write_text(source)
    print('Generated',len(chunks),'chunks,',sum(c['count'] for c in chunks),'entries:',args.output)

if __name__=='__main__':
    main()
