# L-meta-1494: line-linear case closure by private seed families and modular saturation

Status: mathematical proof of the normalized line-linear special case, built on previous exact finite certificates. NOT a complete proof of the unrestricted L-meta-1494 statement, NOT end-to-end kernel-formalized against the project Circuit type, and NOT an upstream submission. Live lemma remains unchecked. Continue on this assigned conjecture, with nonlinear mixed ANDs as the next mathematical obstacle.

## 1. Previously established constraints

For a normalized circuit satisfying the assigned arc promise, with no AND combining two syntactically line-dependent inputs, the earlier reverse-transposition argument rules out <=63 gates except for 14 point-only filters, no pure-point ANDs, exactly 37 ORs in the reverse encoder, and the following conditions. Every pure filter is an OR of its singleton support. Every OR in the reverse encoder has singleton support of size <=5. Let p count distinct two-point seed supports in the pure encoder, r count all OR gates with proper collinear supports of size 2 or 3 in the reverse encoder, k count distinct geometric lines represented exactly by some OR support. Then 4<=p<=r<=6, k>=2r+1, at least seven filters have noncollinear support, and the weighted OR-demand is 21762 with 600 capacity per OR, total spare charge 438. See SEED_COMPLETION_RIGIDITY.md and the preceding notes.

## 2. Closing the four-seed case (no SAT required)

For p=4, no four-arc can hit all four seeds. The previous exact orbit enumeration classified all such seed sets into two orbits, representatives [3,36,80,384] and [3,36,1152,4160]. For each seed e, its private arcs are four-arcs which avoid e and hit all other seeds. In both orbits, for each e there is an extra exceptional point z so that:
- Every regular point p (outside e and different from z) is excluded by some private arc.
- For every distinct regular p,q, some private arc avoids p and contains q.
- Across the four seed groups, each point belongs to at most one exceptional set e union {z}.

The z lists in seed order are [9,11,12,10] and [9,11,8,4]. All finite premises, including the exact four-arc list, are verified by Arc1494FourSeedObstruction.lean.

Let S be the set of points with a singleton filter and s=|S|. Since at least seven filters are noncollinear and there are only 14 filters, s<=7. Let M_i be the regular points of seed group i that lack singleton filters. Every such point p needs at least one filter separating it from every private arc avoiding p, by the prior separator property. A nonsingleton pure filter necessarily contains a seed. A filter false on a private arc can contain only its one avoided seed; otherwise it is true. Thus all relevant nonsingleton filters for group i belong to a separate family F_i of filters containing seed i and no other seed.

Every p in M_i occurs in some F_i support. If it occurs in exactly one such support, that support cannot contain another point q in M_i: there exists a private arc containing q but excluding p, and the sole filter containing p would fail to separate it. Thus degree-one points occupy distinct exclusive supports, containing no other M_i point. All remaining M_i points appear in at least two supports. Every support in F_i has size <=5 and contains the two seed points, so it contains at most three points of M_i. Counting the exclusive supports separately gives 2|M_i| <= 3|F_i|. This remains valid with duplicate filters counted as separate occurrences.

Each of the 13-s missing-singleton points is regular for at least three of the four groups, hence sum_i |M_i| >=3(13-s). The F_i are disjoint and disjoint from singleton filters, so the total filter count f satisfies f >= s + sum_i |F_i| >= s+2(13-s)=26-s>=19. Contradiction with f=14. This closes both four-seed orbits independently of the earlier solver UNSAT/UNKNOWN. It is a mathematical proof with kernel-checked finite and integer premises, relying on the previously independently exhaustively verified orbit classification (not itself fully formalized in Lean).

## 3. Potential merge-vector bookkeeping

For a reverse OR gate with singleton supports U,V, define S=U union V. Replace any overlap by assigning each shared point arbitrarily to one side, obtaining a disjoint partition S=A disjoint-union B. Every actual merge has nonempty, disjoint local supports on its line; hence this assignment preserves every actual merge possibility. Define M_{g,L} as the number of negative four-arcs disjoint from both S and L if A and B each meet L, and zero otherwise. This upper bounds the actual merge events on line L for gate g. Define C_{g,L} as the same negative-arc count if S contains L, and zero otherwise. This upper bounds first full-line completion events. Total actual merge demand per line is 162; total actual first completion per line is 54. For proper collinear gates use the looser vector 54 on their unique line, zero elsewhere, with no completion; for exact line-support gates use 54 merge and 54 completion potential on their line. Those bounds suffice even if the gate's actual potential is less.

For other ORs, all of size <=5, exact enumeration gives weighted capacity 10 sum_L M_{g,L} + sum_L C_{g,L} <=600. All noncollinear supports and all disjoint partitions with capacity >=540 have capacity exactly 600 and one of these patterns:
- no contained full line: M nonzero entries [30,30], [15,15,30], or [15,15,15,15], no completion potential;
- size-five support L plus one extra point: M=30 on its own line L, exactly three other entries 9; completion potential 30 on L, no other completions.
The independent direct exact Python check tested 24921 partitions after safe coarse pruning, finding 702, 1404, 702, and 468 occurrences respectively (all masks, unordered partitions). Arc1494NearSaturated.lean checks the same property by cyclic representatives. Arc1494LineOrCharge.lean also checks the modulo-15 property of saturated no-completion partitions separately.

## 4. Unified spare-capacity inequality for r=5 or r=6

We may now assume p>=5, hence r=5 or 6. Put k=number of distinct exact line-support ORs, u=number of additional duplicate exact line-support ORs, t=number of ORs with a size-five support containing a full line, and D=sum_{g,L} M_{g,L}-2106 >=0. Every line not represented by an exact line-support OR requires at least three five-point ORs containing it, by the previous completion argument and size bound. A size-five support contains at most one full line, so t>=3(13-k).

Let delta be the sum of (600 - weighted capacity) over the noncollinear or otherwise unclassified ORs (for a support of size 0 or 1, weighted capacity is 0). The proper collinear and exact-line gates have the looser capacities 540 and 594 used above. Total potential completions are 54(k+u)+30t, because for a line plus one point exactly 30 negative arcs avoid the extra point. All actual completions total 702. Subtract actual weighted demand from potential and account for intrinsic deficits to get

10D + 60u + 30(t-3(13-k)) + delta <= 438 - 60r - 6k - 36(13-k).

For r>=5 and k<=13, the right-hand side is <=60. Thus every unclassified OR must have weighted capacity >=540, excluding supports of size <=1. By the high-capacity classification, all have capacity 600. In particular every no-full-line noncollinear OR contributes multiples of 15 on each line; every five-point full-line OR contributes 30 on its own line and 9 on exactly three other lines.

For each line L let r_L count its proper collinear ORs, a_L its exact line-support ORs, b_L five-point full-line ORs with own line L, h_L number of five-point ORs with a 9-entry on L, v_L the sum of the remaining merge contributions divided by 15, and d_L its unused merge capacity. Then

54 r_L + 54 a_L + 30 b_L + 9 h_L + 15 v_L = 162 + d_L,

with all quantities nonnegative integers; sum r_L=r, sum a_L=k+u, sum b_L=t, sum h_L=3t, sum d_L=D.

## 5. Six proper collinear gates impossible

If r=6, the prior bound k>=2r+1 forces k=13. The budget right-hand side is zero. Hence u=t=D=0, every line has a_L=1, and 54+54 r_L+15 v_L=162. Modulo 15 and nonnegativity give r_L=2 for each line. Thus r=26, contrary to r=6. This also excludes p=6. The exact modular pattern check is in arc1494_saturated_mod15.py/.json.

## 6. Five proper collinear gates impossible

For r=5, k in {11,12,13}, and budget right side 30k-330.

k=11: spare zero, u=D=0, t=6. Each missing line owns exactly three five-point ORs, so a_L=0,b_L=3 there; exact lines have a_L=1,b_L=0. For an exact line the equation 54+54r_L+9h_L+15v_L=162 implies r_L+h_L>=2. For a missing line the equation 90+54r_L+9h_L+15v_L=162 implies r_L+h_L>=3. Summing gives r+sum h_L>=11*2+2*3=28, but r+sum h_L=5+18=23, contradiction.

k=12: spare 30, u=0, t<=4, D<=3. At least seven of the twelve exact lines have r_L=0. If one of these lines has h_L=0, then its equation forces d_L≡12 mod 15. If h_L=1, it forces d_L≡6 mod 15. Neither is possible since d_L<=3. Contributions 30b_L vanish modulo 15 regardless of b_L. Hence h_L>=2 on at least seven lines, requiring sum h_L>=14, while 3t<=12, contradiction.

k=13: spare 60. If u>=1, budget forces u=1, t=D=0, and there is a line with r_L=0 and a_L=1 (at most five proper gates and one duplicate line). Its equation is 54+15v_L=162, impossible modulo 15. Otherwise u=0, t<=2, D<=6. There are at least eight exact lines with r_L=0, and each must have h_L>=1 since h_L=0 would force d_L≡12 mod15. But sum h_L=3t<=6, contradiction.

Thus r=5 and r=6 are both impossible. Together with the four-seed obstruction and prior constraints, this excludes all <=63-gate line-linear circuits.

## 7. Scope and next problem

The earlier normalization/transposition result applies to no cross ANDs (no AND with two line-dependent predecessors); every such normalized circuit satisfying the promise must have at least 64 gates. The exact baseline construction attains 64 in this class. This closes an entire architecture, NOT the original unrestricted conjecture. All circuit structural bridges and aggregate counting remain to be fully formalized end-to-end. No claims of novelty or official proof acceptance. The same argument also works after interchanging points and lines: the transposition, separator, and coefficient-encoder proofs only use zero/one-hot assignments on the coefficient side and arcs on the encoder side, all of which are available under the original promise restricted to arcs on both sides. The incidence structure is self-dual via negating indices modulo 13 and swapping sides. Consequently a counterexample needs a cross AND on each orientation (the same gate may meet both conditions). Next attack: price nonlinear cross ANDs, or find a <=63-gate counterexample that uses them. Do not restart the solved line-linear branch, and do not send an unsolicited upstream proof for an unassigned restricted claim.

Evidence: Arc1494FourSeedObstruction.lean (successful kernel check), Arc1494NearSaturated.lean and extended Arc1494LineOrCharge.lean (both kernel checks successful: ARC_NEAR_SATURATED_LEAN_EXIT=0 and ARC_LINE_OR_CHARGE_LEAN_EXIT=0), arc1494_saturated_mod15.py and arc1494_near_saturated_patterns.py (exact integer enumeration). The preliminary five-seed orbit classification (372762 bad seed sets in 98 orbits) was exploratory and is not needed for the proof.
