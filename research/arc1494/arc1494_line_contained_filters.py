"""Exact geometry facts for excluding <=3 noncollinear filters in a
14-filter line-linear L-meta-1494 counterexample. No solver or truncation."""
from pathlib import Path
import json,time
D=(0,1,3,9)
L=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
A=[a for a in range(8192) if all((a&l).bit_count()<=2 for l in L)]
A4=[a for a in A if a.bit_count()==4]
t=time.monotonic()
assert len(A)==560 and len(A4)==234
mins=[min(sum(bool(m&l) for l in L) for m in range(8192) if m.bit_count()==k) for k in range(14)]
assert mins==[0,4,7,9,10,11,11,12,12,12,13,13,13,13]
assert all(mins[k]>=k+2 for k in range(1,12))
checked=0; triple_checked=0; good_counts=set()
for l in L:
 for p in range(13):
  if not (l>>p&1):continue
  good=[a for a in A4 if not a&l and all(v==l or not (v>>p&1) or a&v for v in L)]
  good_counts.add(len(good))
  for a in A:
   if a&l or a.bit_count()>3:continue
   assert any(a&b==a for b in good),(p,l,a)
   checked+=1
   triple_checked+=a.bit_count()==3
assert checked==6136 and triple_checked==3744 and good_counts=={27}
split=[*L[1:],3,L[0]^3]
assert len(split)==14 and all(not set(L)<=set(split) for _ in [0])
assert all(any(s>>p&1 and not s&a for s in split) for a in A4 for p in range(13) if not a>>p&1)
out={"status":"EXACT_GEOMETRY_VERIFIED","minimum_line_neighborhood_by_size":mins,
"extension_tests":checked,"noncollinear_triple_tests":triple_checked,
"good_four_arcs_per_point_line":27,"noncanonical_14_cover":split,"seconds":round(time.monotonic()-t,3)}
print(json.dumps(out,indent=2))
(Path(__file__).resolve().parent.parent/"data"/"arc1494_line_contained_filters.json").write_text(json.dumps(out,indent=2))
