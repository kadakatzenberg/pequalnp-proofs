# L-meta-1494: near-saturated OR deficit budget

Status: partial mathematical result. L-meta-1494 remained unchecked at this turn's live check. No active lease for 1494 and no official upstream proof. Continuing the 14-filter line-linear case from commit aaab184. All conclusions below assume the normalization and transposition conditions of LINE_LINEAR_FILTER_OBSTRUCTION.md; no claim about arbitrary nonlinear line-dependent ANDs.

## 1. A new necessary condition

A <=63-gate normalized line-linear counterexample must have f=14 point-only filters and a=0 pure-point AND gates by the previous argument. Its reverse coefficient circuit has exactly 37 OR gates (at most 37 by the size budget, at least 37 by the weighted merge/completion demand). Let cap(g) be the maximum weighted charge available to an OR, as in the previous certificate. Every OR has cap(g)<=600, and actual charge sums to at least 21762. Therefore sum_g (600-cap(g)) <= 37*600-21762 = 438. In particular, every OR with exactly two points in its singleton support has cap(g)<=540: those two points determine a unique line, and only that line can receive a merge charge; there are 54 negative four-arcs for it and no full-support completion charge. Thus at most seven such OR gates are available in the entire reverse circuit (pure encoder included).

More generally an OR whose singleton support is a nonempty proper subset of a line of size 2 or 3 has capacity <=540, for the same reason. An OR whose support is exactly a full line has capacity <=10*54+54=594. These inequalities count all potential events, so actual capacity may be lower.

## 2. Private OR deficit of clean outputs

Call a reverse output line L dirty if an AND with singleton support of size >=2 reaches the output along only ORs (possibly zero intervening ORs); otherwise call it clean. The reverse circuit's only ANDs are the 14 reverse filter multiplications, since the pure encoder has no ANDs. If L is clean, look at its backwards OR-only cone, terminating at inputs, constants, or ANDs. All terminal supports are empty or singletons. All OR supports in the cone are contained in L. The first full-line support in that cone is an OR. Its ancestors in the OR-only cone need at least two earlier nonsingleton ORs, since four distinct singleton supports cannot merge into one using fewer than three binary unions. Take the first full-support OR and two earlier proper nonsingleton support ORs. Their aggregate deficit is at least 60+60+6=126. Such three gates from distinct clean lines are disjoint because a support of size >=2 cannot be contained in two distinct lines.

## 3. Dirty outputs and noncollinear filters

For each dirty output choose one fat reverse AND reaching it through ORs. Its singleton support is contained in that output line and has at least two points. The same AND cannot be chosen by two lines (their intersection has size one). Its singleton support is contained in its corresponding original filter's singleton support, since reverse multiplication is AND. If that filter is line-contained, its line must be the chosen output line. Because pure filters are computed using only ORs (or are direct input wires), this fat line-contained filter necessarily has a two-point OR in its pure ancestor cone, supported inside its line. For distinct dirty lines these seed ORs are distinct. They are also distinct from all the selected clean-line OR gates, whose supports belong to other lines. Each such seed costs at least 60 deficit.

Let c = number of clean outputs, l = number of dirty outputs for which the chosen AND has a line-contained filter, n = number of dirty outputs whose chosen filter is noncollinear. Then c+l+n=13 and 126c+60l<=438. Consequently c<=3 and n>=6+c. This means at least six distinct noncollinear filters are required; if there are clean lines, the lower bound rises as shown.

c | maximum l | minimum n
0 | 7 | 6
1 | 5 | 7
2 | 3 | 8
3 | 1 | 9

This repairs the earlier invalid attempted exclusion of up to three noncollinear filters by a different method: it uses unique-line gate deficit rather than assuming an arc meeting a line necessarily meets a proper subset. In particular all line-contained filters, including the split-line 14-cover, cannot yield a 63-gate line-linear circuit.

The bound is a necessary restriction, not an existence claim or proof that no 14-filter configuration survives. It is independent of the exact local separator-charge conjecture below.

## 4. A failed stronger charge route, now with a concrete counterexample

Attempted to discount the reciprocal-size separator charge by 1/5 for noncollinear supports, while retaining charge 1/size for line-contained supports. If valid locally at each point, this would imply f - n/5 >=13, hence n<=5 for f=14, contradicting the new deficit bound. It is FALSE.

Exact local enumeration at point zero found four supports, integer masks [161,1031,2817,4169], of sizes [3,4,4,4]. All contain zero. Only the first is collinear. They collectively separate point zero from every one of the 162 four-arcs excluding zero. Ordinary charge is 1/3+3/4=13/12. Discounted charge is 1/3+3*(4/5)/4=14/15<1. The local inequality with discount 1/5 is therefore refuted, not the original L-meta-1494 or earlier charge theorem. The example shows why global coupling between points, or stronger structural conditions from OR-DAG construction, are needed.

The enumeration used integer scale 12600, 490 candidate profiles, examined 206 before finding the witness, 1,749,257 recursion nodes. An exploratory combined seed/support MILP (5109 supports, 7286 constraints, 590097 nonzero entries) was interrupted by the local execution timeout before any conclusion. It was not an exhaustion, no inference based on it. The local mathematical counterexample is independently kernel checked by the Lean file.

## 5. Evidence and next obligation

Arc1494DeficitBudget.lean contains kernel-checked arithmetic for the slack budget, the clean/dirty count and the concrete discounted-charge counterexample. The circuit structure proof is mathematical, not yet formalized end-to-end against project Circuit. Previous weighted geometric certificate is unchanged. Need now to exploit the forced >=6 noncollinear filters jointly across all 13 points, e.g. exact separator cover with a pure OR-DAG deficit budget, not individual pointwise discounts. General nonlinear mixed ANDs remain open.
