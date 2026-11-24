"""Exact integer certificate for pure-side monotone interfaces in L-meta-1494.

No solver, floating-point arithmetic, random search or external dependency.
For p=0, enumerate all possible sizes of a family of supports containing p
whose reciprocal-size charge is <=1 and whose disjointness tests cover every
4-arc excluding p. Then exhaust each surviving size profile.
Cyclic translation proves the same claim for every p; duality for lines.
"""
import json,time,sys
from math import lcm
from pathlib import Path
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(1<<13) if all((a&l).bit_count()<=2 for l in L)]
assert len(A)==560
# Recover points from the sets of lines they hit.
sig=lambda a:sum(1<<i for i,l in enumerate(L) if a&l)
need=[sum(1<<w for w,l in enumerate(L) if l>>p&1) for p in range(13)]
for a in A:
 n=sig(a)
 rec=sum(1<<p for p in range(13) if n&need[p]==need[p])
 assert rec==a
assert len({sig(a) for a in A})==560
AA=[a for a in A if a.bit_count()==4 and not a&1]
U=(1<<len(AA))-1
assert len(AA)==162
M={k:[] for k in range(2,10)}
for B in range(1,8192,2):
 k=B.bit_count()
 if k not in M:continue
 cv=sum(1<<i for i,a in enumerate(AA) if not B&a)
 if cv:M[k].append((cv.bit_count(),cv,B))
for k in M:M[k].sort(reverse=True)
mx={k:max(c for c,_,_ in v) for k,v in M.items()}
Q=lcm(*range(1,10));assert Q==2520
# Supports of size >=10 cover no 4-arc; empty supports contribute no bit.
# A singleton {p} alone costs one, so the <1 case may use only sizes 2..9.
profiles=[]
def gen(k,cost,cov,sz):
 if k==10:
  if cov>=len(AA):profiles.append((cost,tuple(sz)))
  return
 for n in range((Q-cost)//(Q//k)+1):gen(k+1,cost+n*(Q//k),cov+n*mx[k],sz+[k]*n)
gen(2,0,0,[])
assert sum(c<Q for c,_ in profiles)==37
assert sum(c==Q for c,_ in profiles)==9
start=time.monotonic();nodes=0
def enumerate_covers(sz,u,chosen=(),prev=None):
 # Repeated supports are unnecessary: removing a duplicate preserves coverage
 # and strictly lowers charge. To disprove <1 it suffices to check distinct supports.
 global nodes
 nodes+=1
 if not sz:
  if not u:yield chosen
  return
 k=sz[0];tail=sz[1:];cap=sum(mx[x] for x in tail)
 if u.bit_count()>mx[k]+cap:return
 req=u.bit_count()-cap
 for j,(c,cv,b) in enumerate(M[k]):
  if c<req:break
  if prev is not None and j<=prev:continue
  v=u&~cv
  if v.bit_count()>cap:continue
  yield from enumerate_covers(tail,v,chosen+(b,),j if tail and tail[0]==k else None)
results=[];equality=[]
for cost,sz in sorted(profiles):
 before=nodes
 covers=list(enumerate_covers(sz,U))
 if cost<Q:assert not covers,(cost,sz,covers)
 else:equality.extend(covers)
 results.append({"charge":cost,"sizes":sz,"covers":len(covers),"nodes":nodes-before})
pencil=sorted(l for l in L if l&1)
assert len(equality)==1 and sorted(equality[0])==pencil
assert len(pencil)==4 and all(any(not a&l for l in pencil) for a in AA)
# The singleton is another valid equality case.
assert all(not a&1 for a in AA)
# Line-support rigidity: every arc A disjoint from line w extends to a 4-arc
# B disjoint from w, with some point of w whose other three lines all hit B.
rigidity=[]
for w,l in enumerate(L):
 good=[a for a in A if a.bit_count()==4 and not a&l and any(l>>p&1 and all(v==w or not (L[v]>>p&1) or bool(a&L[v]) for v in range(13)) for p in range(13))]
 assert len(good)==54
 for a in A:
  if not a&l:assert any(a&b==a for b in good)
 rigidity.append(len(good))
out={"contract":"ARC1494_SEPARATOR_CHARGE_EXACT_V1","status":"EXHAUSTED","arcs":len(A),"distinct_signatures":560,"four_arcs_excluding_p":len(AA),"scale":Q,"max_coverage_by_support_size":mx,"below_one_profiles":37,"equality_profiles":9,"only_nonsingleton_equality_family":pencil,"singleton_equality":True,"equality_family_count":len(equality),"rigidity_extensions":rigidity,"nodes":nodes,"profiles":results,"seconds":round(time.monotonic()-start,3)}
print(json.dumps({k:v for k,v in out.items() if k!="profiles"},indent=2),flush=True)
if len(sys.argv)>1:Path(sys.argv[1]).write_text(json.dumps(out,indent=2),encoding="utf8")
