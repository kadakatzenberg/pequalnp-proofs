"""Two four-seed orbits: exact pure OR support-closure relaxation.
A result here is not a full circuit witness or proof of 1494.
"""
import itertools,json,sys,time
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if a.bit_count()==4 and all((a&l).bit_count()<=2 for l in L)]
cases=[[3,36,80,384],[3,36,1152,4160]]
out=[]
for seeds in (cases[:1] if '--first' in sys.argv else cases[1:] if '--second' in sys.argv else cases):
 supports=[s for s in range(1,8192) if s.bit_count()==1 or (s.bit_count()<=5 and any(s&e==e for e in seeds))]
 ids={s:i+1 for i,s in enumerate(supports)}
 x={s:i+1+len(supports) for i,s in enumerate(supports)}
 top=2*len(supports);cl=[]
 def count(v,k):
  global top
  q=CardEnc.atmost(v,bound=k,top_id=top,encoding=EncType.seqcounter)
  cl.extend(q.clauses);top=q.nv
 col=lambda s:any(s&l==s for l in L)
 count(list(x.values()),14)
 nc=[x[s] for s in supports if not col(s)]
 count([-v for v in nc],len(nc)-7)
 count([ids[s] for s in supports if 2<=s.bit_count()<=3 and col(s)],6)
 count([ids[s] for s in supports if s.bit_count()>1],37)
 for s in supports:
  cl.append([-x[s],ids[s]])
  if s.bit_count()==1 or s in seeds:
   cl.append([ids[s]])
  else:
   subs=[t for t in supports if t!=s and t&s==t]
   zs=[]
   for a,b in itertools.combinations(subs,2):
    if a|b==s:
     top+=1;zs.append(top);cl.extend([[-top,ids[a]],[-top,ids[b]],[-top,ids[s]]])
   cl.append([-ids[s]]+zs)
 for a in A:
  for p in range(13):
   if not a>>p&1:cl.append([x[s] for s in supports if s>>p&1 and not s&a])
 print("CASE",seeds,"supports",len(supports),"vars",top,"clauses",len(cl),flush=True)
 t=time.monotonic()
 with Solver(name="cadical195",bootstrap_with=cl) as g:
  g.conf_budget(int(sys.argv[1]) if len(sys.argv)>1 else 100000)
  r=g.solve_limited(expect_interrupt=True)
  q={"seeds":seeds,"status":"SAT" if r is True else "UNSAT" if r is False else "UNKNOWN","vars":g.nof_vars(),"clauses":g.nof_clauses(),"stats":g.accum_stats(),"seconds":round(time.monotonic()-t,3)}
  if r:
   m=set(g.get_model());ss=[s for s in supports if x[s] in m];gs=[s for s in supports if ids[s] in m]
   assert len(ss)<=14 and sum(not col(s) for s in ss)>=7
   assert sum(2<=s.bit_count()<=3 and col(s) for s in gs)<=6
   assert all(any(s>>p&1 and not s&a for s in ss) for a in A for p in range(13) if not a>>p&1)
   assert all(any(a|b==s and a!=s and b!=s for a,b in itertools.combinations([t for t in gs if t&s==t],2)) for s in gs if s.bit_count()>1)
   q.update(filters=ss,active_or_supports=[s for s in gs if s.bit_count()>1])
  print(json.dumps(q,indent=2),flush=True);out.append(q)
  (Path(__file__).resolve().parent.parent/"data"/"arc1494_four_seed_cases.json").write_text(json.dumps(out,indent=2))
