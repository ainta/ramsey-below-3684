"""Assemble all checked guards into actual uniform Ramsey profile theorems."""
import json
from pathlib import Path
from generate_profile_kernel import emit

def main():
    modules=[]
    for rnd in range(8):
        info=json.loads(Path(f'certificates/reflected/round_{rnd:02d}.json').read_text())
        chain=json.loads(Path(f'lean/Kernel/ChainChecks/R{rnd:02d}.json').read_text())
        outer=json.loads(Path(f'lean/Kernel/OuterChecks/R{rnd:02d}.json').read_text())
        N=info['N'];C=f'CheckedChain.R{rnd:02d}';O=f'CheckedOuter.R{rnd:02d}'
        ns=f'Compact3684.CertifiedRound.R{rnd:02d}'
        source='import Ramsey3683Bootstrap.CheckedRoundInterface\nimport CheckedCatalogSound\n'
        source+=''.join('import '+m.replace('/','.')+'\n' for m in chain['finals']+outer['finals'])
        source+='set_option maxRecDepth 10000\nset_option maxHeartbeats 1000000\n'
        source+=f'namespace {ns}\nopen RamseyLean Ramsey3683Bootstrap\n'
        source+=f'theorem chain_guards : Chain.Guards {C}.data :=\n'
        source+=f'  Chain.guards_of_checks {C}.all_nodeGuard {C}.all_blockGuard {C}.all_runGuard\n'
        source+=f'    (fun i _ => Reflected.R{rnd:02d}.all_regions i)\n'
        source+=f'theorem outer_guards : Outer.Guards {O}.data :=\n'
        source+=f'  Outer.guards_of_checks (by decide) {O}.initial {O}.all_step\n'
        source+=f'    Reflected.R{rnd+1:02d}.all_shapes {O}.all_cover {O}.boundary\n'
        source+=f'theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R{rnd:02d}.lines Reflected.R{rnd:02d}.last)) :\n'
        source+=f'    UniformRamseyExpBound (ProfileCheck.profile Reflected.R{rnd+1:02d}.lines Reflected.R{rnd+1:02d}.last) :=\n'
        source+=f'  Outer.guards_sound (d := {O}.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards\n'
        source+=f'#print axioms valid\nend {ns}\n'
        module=f'CertifiedRound/R{rnd:02d}'
        emit(Path('lean')/(module+'.lean'),source);modules.append(module)
    Path('lean/CertifiedRound/manifest.json').write_text(json.dumps(dict(modules=modules),indent=2)+'\n')
    print('Generated 8 closed-per-round theorem assemblies',flush=True)

if __name__=='__main__':main()
