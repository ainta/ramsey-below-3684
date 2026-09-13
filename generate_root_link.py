import json
import hashlib
from pathlib import Path
from generate_profile_kernel import emit
from generate_profile_access import cases

def main():
    count=len(json.loads(Path('certificates/reflected/profile_00.json').read_text())['lines'])
    chunks=[]
    for start in range(0,count,512):
        size=min(512,count-start);name=f'C{start//512:04d}'
        source='import Kernel.RootLink\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
        source+='namespace Compact3684.ReflectedRoot.'+name+'\n'
        source+=f'theorem checked : (List.range {size}).all (fun i => guard ({start}+i)) = true := by decide +kernel\n'
        source+='#print axioms checked\nend Compact3684.ReflectedRoot.'+name+'\n'
        module='Kernel/RootLinks/'+name
        emit(Path('lean')/(module+'.lean'),source)
        chunks.append(dict(module=module,start=start,count=size,source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    manifest=dict(kind='ROOT_PROFILE_LINK',entries=count,base_modules=['Kernel/RootLink'],chunks=chunks)
    Path('lean/Kernel/RootLinks/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    source=''.join('import '+c['module'].replace('/','.')+'\n' for c in chunks)
    source+='namespace Compact3684.ReflectedRoot\n'
    source+='theorem all_checked (i : Nat) (hi : i ≤ Reflected.R00.last) : guard i = true := by\n'
    source+=f'  change i ≤ {count-1} at hi\n'+cases(chunks,'Compact3684.ReflectedRoot')
    source+='#print axioms all_checked\nend Compact3684.ReflectedRoot\n'
    emit(Path('lean/Kernel/RootLinksSound.lean'),source)
    print('Generated',count,'root equality checks',flush=True)

if __name__=='__main__':main()
