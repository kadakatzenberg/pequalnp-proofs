"""Exhaustive four-pair seed classification and large-support reserve."""
from itertools import combinations,permutations
from pathlib import Path
import json,time
t=time.monotonic()
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
E=[s for s in range(8192) if s.bit_count()==2]
pts=lambda s:[p for p in range(13) if s>>p&1]
W={e:sum(1<<i for i,a in enumerate(A) if a&e) for e in E}
assert all(W[a]&W[b]&W[c] for a,b,c in combinations(E,3))
bad={es for es in combinations(E,4) if not W[es[0]]&W[es[1]]&W[es[2]]&W[es[3]]}
assert len(bad)==1053 and all(len(set(p for e in es for p in pts(e)))==8 for es in bad)
lf={(p,q):next(i for i,l in enumerate(L) if l>>p&1 and l>>q&1) for p in range(13) for q in range(13) if p!=q}
frame=pts(A[0]);G=set()
for a in A:
 for dst in permutations(pts(a)):
  P=dict(zip(frame,dst));Q={}
  while True:
   old=len(P)+len(Q)
   for p,q in combinations(list(P),2):
    l,m=lf[p,q],lf[P[p],P[q]]
    assert Q.get(l,m)==m
    Q[l]=m
   for l,m in combinations(list(Q),2):
    p,q=pts(L[l]&L[m])[0],pts(L[Q[l]]&L[Q[m]])[0]
    assert P.get(p,q)==q
    P[p]=q
   if len(P)+len(Q)==old:break
  assert len(P)==len(Q)==13 and len(set(P.values()))==13 and len(set(Q.values()))==13
  G.add(tuple(P[p] for p in range(13)))
assert len(G)==5616
def tr(s,p):return sum(1<<p[i] for i in pts(s))
assert all({tr(l,p) for l in L}==set(L) for p in G)
todo=set(bad);orbits=[]
while todo:
 es=min(todo)
 orbit={tuple(sorted(tr(e,p) for e in es)) for p in G}
 assert orbit<=bad
 todo-=orbit
 orbits.append({"seeds":es,"size":len(orbit)})
assert [o["size"] for o in orbits]==[936,117]
assert [o["seeds"] for o in orbits]==[(3,36,80,384),(3,36,1152,4160)]
N=[[a for a in A if not a&l] for l in L]
assert all(len(n)==54 for n in N)
assert all(sum(not a>>p&1 for a in N[i])==30 for i,l in enumerate(L) for p in range(13) if not l>>p&1)
assert all(any((a&s)==s for a in N[i]) for i,l in enumerate(L) for s in E if not s&l)
mx=0;example=None
for s in range(8192):
 if s.bit_count()<6:continue
 c=0
 for i,l in enumerate(L):
  w=sum(not a&s for a in N[i])
  if (s&l).bit_count()>=2:c+=10*w
  if s&l==l:c+=w+36
 if c>mx:mx=c;example=s
assert mx==471
out={"status":"EXACT_ENUMERATION","three_pair_sets":76076,"four_pair_sets":1426425,"bad_four_sets":len(bad),"collineations":len(G),"orbits":orbits,"large_reserve_max":mx,"large_reserve_example":example,"seconds":round(time.monotonic()-t,3)}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent.parent/"data"/"arc1494_seed_orbits.json").write_text(json.dumps(out,indent=2))
