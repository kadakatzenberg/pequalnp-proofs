"""Exact strengthened OR charge: 10 merge units plus 1 full-line unit.
The full-line unit may be counted even when no merge occurs.
"""
import json,time
from pathlib import Path
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
N=[[a for a in A if not a&l] for l in L]
assert len(A)==234 and all(len(a)==54 for a in N)
mmax=0; witness=None; coarse=0; tested=0;t=time.monotonic()
for s in range(8192):
 W=[sum(not a&s for a in n) for n in N]
 c=sum(W[i] for i,l in enumerate(L) if s&l==l)
 ub=10*sum(W[i] for i,l in enumerate(L) if (s&l).bit_count()>=2)+c
 if ub<=600:
  coarse+=1
  mmax=max(mmax,ub)
  continue
 a=(s-1)&s
 while a:
  b=s^a
  if a<b:
   m=sum(W[i] for i,l in enumerate(L) if a&l and b&l)
   z=10*m+c;tested+=1
   assert z<=600,(s,a,b,z)
  a=(a-1)&s
assert 10*60==600
# 13 lines, 54 negative arcs, 3 merge units and 1 completion unit per pair.
demand=13*54*(10*3+1)
assert demand==21762 and 36*600<demand<=37*600
out={"status":"EXACT_BOUND_VERIFIED","masks":8192,"coarse_masks":coarse,"partition_tests":tested,"weighted_capacity":600,"weighted_demand":demand,"minimum_OR_gates":37,"seconds":round(time.monotonic()-t,3)}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent.parent/"data"/"arc1494_completion_charge.json").write_text(json.dumps(out,indent=2))
