# L-meta-1494: seed and completion rigidity

Status: partial mathematical research, not a complete proof of the original conjecture or a desk submission. The live page remains unchecked. Work continues the line-linear 14-filter case from commit 5791853, with no current lease. All claims below refer to the normalized line-linear circuit and its reverse encoder as constructed in LINE_LINEAR_FILTER_OBSTRUCTION.md and OR_DEFICIT_BUDGET.md. The circuit-to-trace and aggregate counting arguments remain human mathematical proofs; finite geometry and arithmetic have independent Lean certificates.

## Completion deficit

The reverse encoder has exactly 37 ORs, a weighted charge demand of 21762, and capacity 600 per OR. Let M_g denote the disjoint-support merge capacity bound and C_g the sum of the potential completion counts (54 or fewer per full line contained in the gate's singleton support). Actual merge events <= M_g; assign exactly one first full-line false OR completion for each negative line/four-arc pair, as in the earlier argument. Thus actual completions for each line total exactly 54. The available aggregate deficit is 438, which includes the individual capacity deficits 600-(10M_g+C_g) and unused potential completion capacity, plus unused merge capacity.

Let r count OR gates whose singleton supports are proper collinear sets of size 2 or 3, and k count distinct geometric lines for which an OR has singleton support exactly that line. Each proper collinear OR has capacity <=540, so consumes at least 60 deficit. Choose one exact line-support OR for each of k lines; each has capacity <=594, contributing at least 6 deficit.

For a line L without an exact line-support OR, there are two cases:
1. Some OR singleton support S of size >=6 contains L. Exact coarse geometric charge calculation for all S of size >=6 gives 10M_g+C_g+36 * (# lines contained in S) <=471. Reserve 36 for each such line (even if several lines use the same gate). At least 129 additional deficit remains at each such gate after reserving for all contained lines.
2. No such large OR contains L. The only possible first-completion gates have singleton support L plus one extra point. For each extra point outside L, exactly 30 of the 54 negative four-arcs avoid it. If there are at most two such OR gates, choose a negative four-arc containing their extra point(s); it exists by exact geometry. Then no candidate completion gate is false on that arc, contradicting existence of a first false full-support OR. Hence at least three such gates, with total potential completion count at least 90; actual completion count for L is 54, so at least 36 is unused. This unused completion capacity is indexed by L and cannot be double counted across lines, nor does it overlap gate-intrinsic capacity deficits.

The chosen exact-line gates, proper collinear gates, and large-support gates are disjoint by support size/type. Reserving at least 36 for each of the 13-k absent exact-line supports therefore proves

60 r + 6 k + 36 (13-k) <= 438.

It follows that r<=6 and k>=2r+1. If r=6, k=13 and the entire deficit is exhausted. The prior clean/dirty argument gave 2c+l<=r (two distinct proper collinear ORs per clean output, one pure pair seed for each selected dirty line-contained filter, all distinct across lines), with c+l+n=13. Now n>=7+c, so there are at least seven noncollinear filter supports. This strengthens the old lower bound six. These are necessary conditions for a 63-gate line-linear counterexample.

## Seed graph and exclusion of large OR supports

Let p be the number of distinct two-point seed supports in the pure OR encoder. Each non-singleton pure support contains at least one seed, by tracing its OR ancestors down to the first non-singleton support. If an arc A of size four intersects every seed, every non-singleton pure filter is true on A. The separation property for every point outside A then forces all nine outside points to have singleton filters: otherwise no filter can distinguish that point from A monotonically. With >=7 noncollinear filters and only 14 filters total, this is impossible. Thus the seed graph has no four-arc transversal.

Any three arbitrary pairs have a four-arc transversal: fix an endpoint of the first, find an arc containing it and hitting the other two. Exact finite certificate Arc1494SeedTransversal.lean verifies the latter statement for fixed point zero and all 78^2 pairs via 72-bit masks of the arcs containing zero, and translation handles every point. The same fact gives a transversal of any four pairs sharing an endpoint between two pairs. Consequently p>=4, and if p=4 the seeds form a matching. Since p<=r<=6 and k>=2r+1, we have 4<=p<=6 and k>=9.

The reserved deficit 60r+6k+36(13-k) is at least 60*4+6*13=318. An OR of support size >=6 has at least 129 additional deficit after reserving 36 per line contained in that support. This would require >=447 >438. Therefore every OR in the reverse circuit, including the pure encoder, has singleton support size at most five. The bound is valid even for large supports containing no entire line. Arc1494LargeReserve.lean checks the maximum 471 by cyclic representative enumeration; direct Python enumeration checks every mask. In particular every nontrivial pure filter has size <=5.

## Exact four-seed orbit classification

Enumerate all 76076 triples and 1426425 four-element subsets of the 78 point pairs; represent each pair's hitting arcs by a 234-bit integer. Exactly 1053 four-pair sets have no four-arc transversal, all matchings. Generate incidence-preserving point permutations by mapping one ordered four-arc frame to each ordered four-arc (234*24=5616 choices), reconstruct remaining points and lines by joins/intersections. Verify every permutation preserves the 13 lines and every bad orbit stays within the bad sets. The bad sets partition into two orbits of sizes 936 and 117, represented by seed masks [3,36,80,384] and [3,36,1152,4160]. This is exact finite enumeration, not a formal Lean orbit theorem. Reproducible script arc1494_seed_orbits.py, result arc1494_seed_orbits.json.

## SAT support-closure model

The broad seed-cover necessary relaxation had 5109 candidate supports, 380508 variables, 874679 input clauses; UNKNOWN at 50000 conflicts (51.516s), no conclusion. A more targeted model for each four-seed orbit has 881 candidate supports: singletons or size<=5 supports containing a fixed seed. Active pure nonsingleton supports must have two strictly smaller available supports whose union equals the active support; this yields a realizable pure OR support DAG (duplicate gates may be merged). All fixed seed supports active; at most 37 active non-singleton pure supports, at most six proper collinear ORs, at most 14 selected filters of which at least seven noncollinear, all 2106 point/negative-four-arc separation clauses. The model is necessary but relaxed (no reverse circuit, no actual gate-specific charge matching). An UNSAT result excludes the corresponding four-seed orbit at solver level; SAT only gives a relaxed cover, not a witness against L-meta-1494.

Initial bounded results: first orbit UNKNOWN at 100000 conflicts; second orbit UNSAT at 73153 conflicts (6.656s). See data/arc1494_four_seed_cases_initial.json. The first orbit retry was UNKNOWN at 500000 conflicts (59.281s); data/arc1494_four_seed_cases.json contains the retry. Both computations have stopped. No DRUP certificate or Lean UNSAT bridge for the orbit search yet, so do not present it as kernel-checked.

## Verified files

Arc1494LineOrCharge.lean extended: small completion geometry, coarse capacity reserve <=600, refined deficit arithmetic. ARC_LINE_OR_CHARGE_LEAN_EXIT=0.
Arc1494SeedTransversal.lean: fixed-point hitting masks and arithmetic. ARC_SEED_TRANSVERSAL_LEAN_EXIT=0.
Arc1494LargeReserve.lean: sharper coarse capacity+reserve bound 471 (448 cyclic reps). ARC_LARGE_RESERVE_LEAN_EXIT=0.
arc1494_seed_orbits.py: exact independent enumeration.
arc1494_seed_cover.py, arc1494_four_seed_cases.py: bounded SAT relaxations, not formal proofs.

Next: close first four-seed orbit with exact solver certificate if possible; then analyze five and six seeds. Nonlinear mixed ANDs still outside this argument. No accepted proof today.
