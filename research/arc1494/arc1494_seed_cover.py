"""Necessary conditions, not full synthesis, for 14 pure OR filters.
All nontrivial pure supports must have a pair seed. Charge budget uses
the exact disjoint-partition upper bound on OR capacity, hence is relaxed.
"""
import json,time,sys,itertools
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
N=[[a for a in A if not a&l] for l in L]
budget=438
mx={}
for s in range(1,8192):
 if s.bit_count()<2:continue
 w=[sum(not(s&a) for a in n) for n in N]
 c=sum(w[i] for i,l in enumerate(L) if s&l==l)
 rel=[(l,w[i]) for i,l in enumerate(L) if w[i] and (s&l).bit_count()>=2]
 ub=10*sum(x for _,x in rel)+c
 if ub<162:continue
 m=0
 a=(s-1)&s
 while a:
  b=s^a
  if a<b:m=max(m,sum(x for l,x in rel if a&l and b&l))
  a=(a-1)&s
 cap=10*m+c
 if cap>=162:mx[s]=600-cap
supports=sorted([1<<i for i in range(13)]+list(mx))
ids={s:i+1 for i,s in enumerate(supports)}
x={s:i+1+len(supports) for i,s in enumerate(supports)}
top=2*len(supports)
clauses=[]
def count(lits,k):
 global top
 enc=CardEnc.atmost(lits,bound=k,top_id=top,encoding=EncType.seqcounter)
 clauses.extend(enc.clauses);top=enc.nv
count(list(x.values()),14)
nc=[x[s] for s in supports if not any(s&l==s for l in L)]
count([-v for v in nc],len(nc)-6)
count([ids[s] for s in supports if s.bit_count()==2],7)
count([ids[s] for s in supports if s.bit_count()>1],37)
for s in supports:
 clauses.append([-x[s],ids[s]])
 if s.bit_count()==1:clauses.append([ids[s]])
 elif s.bit_count()>2:
  ps=[ids[(1<<a)|(1<<b)] for a,b in itertools.combinations([p for p in range(13) if s>>p&1],2)]
  clauses.append([-ids[s]]+ps)
# Exact weighted budget with a carry-save circuit and no overflow.
def new():
 global top
 top+=1;return top
def xor(a,b):
 if a==b:return 0
 if not a:return b
 if not b:return a
 c=new();clauses.extend([[-a,-b,-c],[a,b,-c],[-a,b,c],[a,-b,c]])
 return c
def both(a,b):
 if not a or not b:return 0
 if a==b:return a
 c=new();clauses.extend([[-c,a],[-c,b],[c,-a,-b]])
 return c
def either(a,b):
 if not a:return b
 if not b:return a
 if a==b:return a
 c=new();clauses.extend([[c,-a],[c,-b],[-c,a,b]])
 return c
cols=[[] for _ in range(10)]
for s,w in mx.items():
 for k in range(9):
  if w>>k&1:cols[k].append(ids[s])
for k in range(9):
 while len(cols[k])>=3:
  a,b,c=cols[k].pop(),cols[k].pop(),cols[k].pop()
  ab=xor(a,b);lo=xor(ab,c);hi=either(both(a,b),both(ab,c))
  if lo:cols[k].append(lo)
  if hi:cols[k+1].append(hi)
 if len(cols[k])==2:
  a,b=cols[k].pop(),cols[k].pop()
  lo,hi=xor(a,b),both(a,b)
  if lo:cols[k].append(lo)
  if hi:cols[k+1].append(hi)
for v in cols[9]:clauses.append([-v])
for val in range(439,512):
 cl=[];possible=True
 for k in range(9):
  if not cols[k]:
   if val>>k&1:possible=False;break
  else:
   v=cols[k][0];cl.append(-v if val>>k&1 else v)
 if possible:clauses.append(cl)
# At least six noncollinear supports means some singleton is missing;
# cyclic symmetry allows it to be point 0.
clauses.append([-x[1]])
for a in A:
 for p in range(13):
  if not a>>p&1:
   clauses.append([x[s] for s in supports if s>>p&1 and not s&a])
print("CNF",top,len(clauses),"supports",len(supports),flush=True)
t=time.monotonic()
with Solver(name="cadical195",bootstrap_with=clauses) as g:
 g.conf_budget(int(sys.argv[1]) if len(sys.argv)>1 else 30000)
 r=g.solve_limited(expect_interrupt=True)
 out={"status":"SAT" if r is True else "UNSAT" if r is False else "UNKNOWN","vars":g.nof_vars(),"clauses":g.nof_clauses(),"stats":g.accum_stats(),"seconds":round(time.monotonic()-t,3)}
 if r:
  m=set(g.get_model());ss=[s for s in supports if x[s] in m];gs=[s for s in mx if ids[s] in m]
  assert len(ss)<=14 and sum(not any(s&l==s for l in L) for s in ss)>=6
  assert sum(mx[s] for s in gs)<=438
  assert sum(s.bit_count()==2 for s in gs)<=7 and len(gs)<=37
  assert all(any(s>>p&1 and not s&a for s in ss) for a in A for p in range(13) if not a>>p&1)
  assert all(any(t&s==t and t.bit_count()==2 for t in gs) for s in gs if s.bit_count()>2)
  out.update(filters=ss,active_or_supports=gs,deficit=sum(mx[s] for s in gs))
 print(json.dumps(out,indent=2),flush=True)
 (Path(__file__).resolve().parent.parent/"data"/"arc1494_seed_cover.json").write_text(json.dumps(out,indent=2))
