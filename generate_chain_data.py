"""Generate bounded packed Lean data modules for an exact reflected round."""
import argparse
from array import array
import gzip
import hashlib
import json
from pathlib import Path
import struct
from generate_profile_kernel import branch,emit

def pack(values,width):
    assert all(0<=x<2**width for x in values)
    return int.from_bytes(b''.join(x.to_bytes(width//8,'little') for x in values),'little')

def selector(name,names,typ,grouped=False,legacy=False):
    small_nodes=not legacy and typ=='Chain.Packed.NodeBlob'
    threshold=128 if small_nodes else 512
    group_size=16 if small_nodes else 128
    if not grouped or len(names)<=threshold:
        return f'def {name} (i : Nat) : {typ} := '+branch(names)+'\n'
    # Named groups keep beta substitution local. An inlined 14,000-leaf
    # selector can traverse much more than the selected branch in the kernel.
    helpers=[];code=''
    for start in range(0,len(names),group_size):
        helper=f'{name}Group{start//group_size:04d}';helpers.append(helper)
        code+=f'def {helper} (i : Nat) : {typ} := '+branch(names[start:start+group_size],start)+'\n'
    code+=f'def {name}Groups (i : Nat) : Nat → {typ} := '+branch(helpers)+'\n'
    code+=f'def {name} (i : Nat) : {typ} := {name}Groups (i/{group_size}) i\n'
    return code

def refresh_selectors(rnd):
    assert rnd>=5
    info=json.loads(Path(f'certificates/reflected/round_{rnd:02d}.json').read_text())
    data=json.loads(Path(f'lean/Kernel/ChainData/R{rnd:02d}.json').read_text())
    specs=[('nodeBlobs','nodeBlob',(data['records']+1023)//1024,'Chain.Packed.NodeBlob'),
           ('runBlobs','runBlob',(data['runs']+1023)//1024,'Chain.Packed.RunBlob'),
           ('lookupBlobs','lookupBlob',((info['N']+1)*512+1023)//1024,'Nat')]
    old='';previous='';new=''
    for name,prefix,count,typ in specs:
        names=[f'{prefix}{i:05d}' for i in range(count)]
        old+=selector(name,names,typ)
        previous+=selector(name,names,typ,True,legacy=True)
        new+=selector(name,names,typ,True)
    path=Path(f'lean/Kernel/ChainData/R{rnd:02d}.lean')
    source=path.read_text()
    if new in source:return
    variants=[v for v in [old,previous] if source.count(v)==1]
    assert len(variants)==1,'Unexpected generated header; preserve it'
    path.write_text(source.replace(variants[0],new))
    print('REFRESHED SELECTORS ONLY',rnd,'literal data modules unchanged',flush=True)

def generate(rnd):
    folder=Path('certificates/reflected');paths=Path('certificates/reflected_paths')
    meta=json.loads((folder/f'round_{rnd:02d}.json').read_text())
    pathreport=json.loads((paths/'manifest.json').read_text())['rounds'][rnd]
    blocks=json.loads((paths/f'blocks_{rnd:02d}.json').read_text())
    N=meta['N'];count=meta['record_count'];offset=meta['record_start']
    ns=f'Compact3684.ChainData.R{rnd:02d}'
    prefix=f'Kernel/ChainData/R{rnd:02d}'
    modules=['Kernel/PackedChain',f'Kernel/ProfileAccess/R{rnd:02d}']
    imports=[];node_names=[];run_names=[];lookup_names=[]
    lookup=array('I',[0])*((N+1)*512)
    def data_file(kind,number,decls):
        module=prefix+f'{kind}{number:04d}'
        source='import Kernel.PackedChain\nnamespace '+ns+'\n'+''.join(decls)+'end '+ns+'\n'
        emit(Path('lean')/(module+'.lean'),source)
        modules.append(module);imports.append(module)
    with gzip.open(folder/f'records_{rnd:02d}.jsonl.gz','rt') as records, \
         gzip.open(paths/f'columns_{rnd:02d}.bin.gz','rb') as columns, \
         gzip.open(paths/f'path_index_{rnd:02d}.bin.gz','rb') as pindex:
        buffers=[[] for _ in range(7)];decls=[]
        def flush_nodes():
            nonlocal buffers,decls
            if not buffers[0]:return
            name=f'nodeBlob{len(node_names):05d}';node_names.append(name)
            values=[pack(v,256 if k==6 else 128) for k,v in enumerate(buffers)]
            decls.append('def '+name+' : Chain.Packed.NodeBlob := ⟨'+','.join(hex(x) for x in values)+'⟩\n')
            buffers=[[] for _ in range(7)]
            if len(decls)==16:
                data_file('N',(len(node_names)-1)//16,decls);decls=[]
        for i,text in enumerate(records):
            r=json.loads(text);assert r['id']==offset+i
            colbytes=columns.read(20);idxbytes=pindex.read(12)
            assert len(colbytes)==20 and len(idxbytes)==12
            block=int.from_bytes(colbytes[:4],'little');pref=int.from_bytes(colbytes[4:],'little')
            pathstart,pathcount=struct.unpack('<QI',idxbytes)
            basekind,base=r.get('base',[0,0]);base=base-offset if basekind==1 else base
            region=r.get('support',0)
            entries=[(r['row'],13),(r['col'],9),(r['start'],13),(r['kind'],1),(basekind,1),
                     (base,19),(region,14),(block,11),(pathstart,24),(pathcount,13)]
            word=shift=0
            for value,width in entries:
                assert 0<=value<2**width,(rnd,i,value,width)
                word+=value<<shift;shift+=width
            assert shift==118
            assert 0<r['cost']<2**48 and 0<r['p']<2**40 and r['log_blue']<2**19
            blue=r['cost']+(r['p']<<48)+(r['log_blue']<<88)
            controls=0
            if r['kind']==1:
                a,b,theta,mu,pi=r['seed'];lm,lone,lpi=r['logs']
                assert [meta['supports'][region]['a'],meta['supports'][region]['b']]==[a,b]
                assert 0<theta<2**64 and 0<mu<2**40 and 0<pi<2**40
                assert all(0<=x<2**19 for x in [lm,lone,lpi])
                controls=theta+(mu<<64)+(pi<<104)+(lm<<144)+(lone<<163)+(lpi<<182)
            for buf,value in zip(buffers,[word,r['v'],r['end'],r['u'],pref,blue,controls]):buf.append(value)
            lookup[r['row']*512+r['col']]=i
            if len(buffers[0])==1024:flush_nodes()
        flush_nodes()
        if decls:data_file('N',(len(node_names)-1)//16,decls)
        assert i+1==count and not columns.read(1) and not pindex.read(1)
    print('PACKED NODES',rnd,count,flush=True)
    with gzip.open(paths/f'runs_{rnd:02d}.bin.gz','rb') as source:
        decls=[];nr=0
        while True:
            data=source.read(28*1024)
            if not data:break
            assert len(data)%28==0
            words=[];ends=[]
            for start in range(0,len(data),28):
                owner,upper,lower=struct.unpack_from('<III',data,start)
                assert max(owner,upper,lower)<count<2**19
                words.append(owner+(upper<<19)+(lower<<38))
                ends.append(int.from_bytes(data[start+12:start+28],'little'))
            name=f'runBlob{len(run_names):05d}';run_names.append(name);nr+=len(words)
            decls.append('def '+name+' : Chain.Packed.RunBlob := ⟨'+hex(pack(words,64))+','+hex(pack(ends,128))+'⟩\n')
            if len(decls)==64:
                data_file('P',(len(run_names)-1)//64,decls);decls=[]
        if decls:data_file('P',(len(run_names)-1)//64,decls)
        assert nr==pathreport['runs']
    print('PACKED RUNS',rnd,nr,flush=True)
    decls=[]
    for start in range(0,len(lookup),1024):
        name=f'lookupBlob{len(lookup_names):05d}';lookup_names.append(name)
        decls.append('def '+name+' : Nat := '+hex(pack(lookup[start:start+1024],32))+'\n')
        if len(decls)==256:
            data_file('L',(len(lookup_names)-1)//256,decls);decls=[]
    if decls:data_file('L',(len(lookup_names)-1)//256,decls)
    block_words=[]
    for lo,hi,col,increasing in blocks:
        upper=lookup[hi*512+col]
        assert 0<lo<=hi<2**13 and col<2**9 and upper<2**19
        block_words.append(lo+(hi<<13)+(col<<26)+(upper<<35)+(increasing<<54))
    source='import '+f'Kernel.ProfileAccess.R{rnd:02d}'+'\n'
    source+=''.join('import '+m.replace('/','.')+'\n' for m in imports)
    source+='namespace '+ns+'\n'
    source+=selector('nodeBlobs',node_names,'Chain.Packed.NodeBlob',rnd>=5)
    source+=selector('runBlobs',run_names,'Chain.Packed.RunBlob',rnd>=5)
    source+=selector('lookupBlobs',lookup_names,'Nat',rnd>=5)
    source+='def blockBlob : Nat := '+hex(pack(block_words,64))+'\n'
    source+=f'def data : Chain.Data :=\n  {{ N := {N}, nodeCount := {count}, blockCount := {len(blocks)}, runCount := {nr},\n'
    source+=f'    regionCount := {len(meta["supports"])}, oldLast := Reflected.R{rnd:02d}.last,\n'
    source+=f'    node := fun i => Chain.Packed.nodeAt (nodeBlobs (i/1024)) (i%1024) Reflected.R{rnd:02d}.region,\n'
    source+='    run := fun i => Chain.Packed.runAt (runBlobs (i/1024)) (i%1024),\n'
    source+='    block := fun i => Chain.Packed.blockAt blockBlob i,\n'
    source+='    lookup := fun row col => Chain.Packed.lookupAt (lookupBlobs ((row*512+col)/1024)) ((row*512+col)%1024),\n'
    source+=f'    region := Reflected.R{rnd:02d}.region, oldLine := Reflected.R{rnd:02d}.lines, log := fun _ => ⟨0,0,0⟩ }}\n'
    source+='end '+ns+'\n'
    module=prefix
    emit(Path('lean')/(module+'.lean'),source);modules.append(module)
    result=dict(status='GENERATED_DATA_NOT_KERNEL_CHECKED',round=rnd,records=count,runs=nr,
                namespace=ns,module=module,modules=modules)
    Path(f'lean/Kernel/ChainData/R{rnd:02d}.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Generated round',rnd,'in',len(modules),'modules',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--round',type=int,nargs='+',required=True)
    parser.add_argument('--refresh-selectors-only',action='store_true')
    args=parser.parse_args()
    for rnd in args.round:
        (refresh_selectors if args.refresh_selectors_only else generate)(rnd)
