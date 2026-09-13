"""Read-only test for cheaper exact range-max certificate representations."""
import gzip
import json
from pathlib import Path

def main():
    folder=Path('certificates/quantized')
    header=json.loads((folder/'bellman.json').read_text())
    grids={p['round']:p['N'] for p in header['profiles']}
    current=None
    columns={}
    def finish():
        adjacent=negative=zero=positive=turns=0
        for rows in columns.values():
            rows.sort()
            old_sign=0
            for left,right in zip(rows,rows[1:]):
                if right[0]!=left[0]+1:
                    old_sign=0
                    continue
                adjacent+=1
                delta=right[1]-left[1]-left[2]*10**18
                sign=(delta>0)-(delta<0)
                negative+=sign<0
                zero+=sign==0
                positive+=sign>0
                turns+=old_sign!=0 and sign!=0 and sign!=old_sign
                if sign:old_sign=sign
        print(json.dumps(dict(round=current,columns=len(columns),adjacent=adjacent,
                              negative=negative,zero=zero,positive=positive,sign_changes=turns)),flush=True)
    with gzip.open(folder/header['record_file'],'rt') as source:
        for line in source:
            record=json.loads(line)
            rnd,row,col=record['rank']
            if rnd!=current:
                if current is not None:finish()
                columns={}
                current=rnd
            numerator,denominator=record['v']
            scaled,remainder=divmod(numerator*grids[rnd]*10**30,denominator)
            assert remainder==0
            columns.setdefault(col,[]).append((row,scaled,record['cost']))
    finish()

if __name__=='__main__':main()
