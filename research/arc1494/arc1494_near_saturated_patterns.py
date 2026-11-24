"""Exact high-capacity patterns used in the 5/6-seed obstruction."""
from collections import Counter
from pathlib import Path
import json,time
t=time.monotonic()
L=[sum(1<<((w+d)%13) for d in (0,1,3,9)) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
N=[[a for a in A if not a&l] for l in L]
hist=Counter();tested=0
for s in range(1,8192):
 if not 3<=s.bit_count()<=5 or any(s&l==s for l in L):continue
 full=[i for i,l in enumerate(L) if s&l==l]
 w=[sum(not a&s for a in n) for n in N]
 c=sum(w[i] for i in full)
 ub=10*sum(w[i] for i,l in enumerate(L) if (s&l).bit_count()>=2)+c
 if ub<540:continue
 a=(s-1)&s
 while a:
  b=s^a
  if a<b:
   v=[w[i] if a&l and b&l else 0 for i,l in enumerate(L)]
   tested+=1
   cap=10*sum(v)+c
   if cap>=540:
    assert cap==600,(s,a,b,cap)
    if not full:
     assert c==0 and all(x%15==0 for x in v)
     hist[("plain",*sorted(x for x in v if x))]+=1
    else:
     assert len(full)==1 and c==30 and v[full[0]]==30
     assert sorted(x for i,x in enumerate(v) if i!=full[0] and x)==[9,9,9]
     hist[("extra",30,9,9,9)]+=1
  a=(a-1)&s
assert sum(hist.values())==3276
out={"status":"EXACT_ENUMERATION","partitions_tested":tested,"patterns":{str(k):v for k,v in hist.items()},"seconds":round(time.monotonic()-t,3)}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent.parent/"data"/"arc1494_near_saturated_patterns.json").write_text(json.dumps(out,indent=2))
