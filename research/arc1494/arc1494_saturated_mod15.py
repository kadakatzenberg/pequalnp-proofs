"""Exact finite check for saturated OR capacity with no completion units."""
from pathlib import Path
from collections import Counter
import json,time
t=time.monotonic()
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
N=[[a for a in A if not a&l] for l in L]
hist=Counter();tested=0
for s in range(8192):
 if s.bit_count()<2:continue
 w=[sum(not a&s for a in n) for n in N]
 c=sum(w[i] for i,l in enumerate(L) if s&l==l)
 if c:continue
 if sum(w[i] for i,l in enumerate(L) if (s&l).bit_count()>=2)<60:continue
 a=(s-1)&s
 while a:
  b=s^a
  if a<b:
   v=[w[i] if a&l and b&l else 0 for i,l in enumerate(L)]
   tested+=1
   if sum(v)==60:
    assert all(x%15==0 for x in v),(s,a,b,v)
    hist[tuple(sorted(x for x in v if x))]+=1
  a=(a-1)&s
assert hist=={(30,30):702,(15,15,30):1404,(15,15,15,15):702}
# Every line gets 162 events; one exact-line OR gives 54, r
# proper collinear gates give 54 each, and all remaining contributions
# are multiples of 15. Thus necessarily r=2 on every line.
assert [r for r in range(3) if (162-54-54*r)%15==0]==[2]
out={"status":"EXACT_ENUMERATION","partitions_tested":tested,"patterns":{str(k):v for k,v in hist.items()},"required_proper_gates_per_line":2,"required_total_proper_gates":26,"seconds":round(time.monotonic()-t,3)}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent.parent/"data"/"arc1494_saturated_mod15.json").write_text(json.dumps(out,indent=2))
