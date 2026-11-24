"""Exact gate-charge calculation for the 13-output PG(2,3) arc line-OR task.
All tests are finite integers; no SAT, randomized or floating-point search.
"""
from pathlib import Path
import json,sys,time
from collections import Counter
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(1<<13) if all((a&l).bit_count()<=2 for l in L)]
N=[[a for a in A if a.bit_count()==4 and not(a&l)] for l in L]
assert len(A)==560 and len(set(L))==13
assert all(len(a)==54 for a in N)
assert all((a&b).bit_count()==1 for i,a in enumerate(L) for b in L[i+1:])
def weight(s,ws):
 return sum(w for i,w in enumerate(ws) if (s&L[i]).bit_count()>=2)
max_by_size=Counter()
maximum=0; witness=None; checked=0; support_masks=0; coarse=0
start=time.monotonic()
for s in range(8192):
 if s.bit_count()<2:continue
 support_masks+=1
 W=[sum(not(a&s) for a in n) for n in N]
 ub=weight(s,W)
 # The coarse bound already covers all partitions, even overlapping children.
 if ub<=60:
  coarse+=1
 else:
  a=(s-1)&s
  while a:
   b=s^a
   if a<b:
    n=sum(W[w] for w,l in enumerate(L) if a&l and b&l)
    max_by_size[s.bit_count()]=max(max_by_size[s.bit_count()],n)
    checked+=1
    assert n<=60,(s,a,b,n)
    if n>maximum:maximum=n;witness=(a,b,n)
   a=(a-1)&s
assert maximum==60
assert witness and witness[2]==60
# A decoder using line ORs is sensitive to each interface signal:
# for each line w, choose p on w and an arc B avoiding w but hitting
# each of the other 3 lines through p.
sep=[]
for w,l in enumerate(L):
 candidates=[]
 for p in range(13):
  if not l>>p&1:continue
  for a in N[w]:
   if all(i==w or not (L[i]>>p&1) or a&L[i] for i in range(13)):
    candidates.append((p,a))
 assert candidates
 p,a=min(candidates);sep.append({"line":w,"point":p,"arc":a})
 # Verify directly the output signatures differ in a monotone-separating way.
 sp=sum(1<<i for i,t in enumerate(L) if t>>p&1)
 sa=sum(1<<i for i,t in enumerate(L) if t&a)
 assert sp&~sa==1<<w
out={"contract":"ARC1494_LINE_OR_GATE_CHARGE_V1","status":"EXACT_BOUND_VERIFIED",
"lines":L,"arcs":len(A),"negative_four_arcs_per_line":[len(a) for a in N],
"support_masks":support_masks,"coarse_bound_masks":coarse,"partition_tests":checked,
"max_partition_charge":maximum,"max_witness":witness,"max_by_size_of_nontrivial_masks":dict(max_by_size),
"decoder_separators":sep,"seconds":round(time.monotonic()-start,3)}
print(json.dumps(out,indent=2),flush=True)
if len(sys.argv)>1:Path(sys.argv[1]).write_text(json.dumps(out,indent=2),encoding="utf8")
