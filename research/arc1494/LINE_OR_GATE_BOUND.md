# L-meta-1494: exact gate cost of pure arc line encoders

Status: mathematical proof with exact finite certificate and kernel-checked supporting lemmas; complete circuit-to-trace and global aggregation formalization not yet Lean-checked. L-meta-1494 itself is not solved; no upstream submission or official credit. This result works on the assigned order-three geometry, with arbitrary fan-in-at-most-two monotone gates, constants, identities, DAG sharing, and outputs for any subset of lines.

## Definitions and theorem

Let P be the 13 points of PG(2,3), with lines L_w = {w,w+1,w+3,w+9} mod 13. An arc meets each line in at most two points. A point-only monotone AND/OR circuit has outputs t_L for m distinct lines. Suppose t_L(A)=1 iff A intersects L for every point arc A. Then the circuit has at least 3m gates. This is tight: compute each line's four-point OR using three binary ORs. The result imposes no restrictions on AND gates, intermediate supports, or sharing. It strengthens the prior 13-wire interface bound by pricing the line-OR encoder.

## Merge certificates at each negative arc

For each wire g, let S(g) be its set of points p for which g is true on singleton {p}. Thus S at OR is union, at AND is intersection (unary/zero-input gates interpreted in the usual way). For each output line L and each four-arc B disjoint from L, process the gates in topological order, considering only wires false on B. Initialize a partition of the four points of L into singletons. Maintain that S(g)∩L for every processed false wire is empty or contained in one current block.

- An input wire satisfies the invariant. A constant false wire has empty singleton support. A constant true wire is never false on B.
- At a false AND gate some parent is false. The output's singleton support is a subset of that parent's singleton support; no merge is needed.
- At a false OR gate both parents are false. Their two local supports are each contained in a block; merge the two blocks if distinct and both supports nonempty. This adds at most one merge event and preserves every prior containment. A zero- or one-parent OR cannot merge two distinct blocks.
- At the output for L, the wire is false on B, and its singleton support is exactly L. All four points must now be in one block, hence there were exactly three merges.

Arc1494MergeTrace.lean proves the trace invariant, rank-change bound and full support requires at least three events. The 15 finite partitions of a four-element set are represented by block masks. Its merge-local and merge-preserve theorems cover all states and support masks, including overlapping/empty supports. It also proves that a merge event can occur only if both local supports are nonempty and disjoint. The model works on lists of false-wire masks with arbitrary sub/intersection and union steps. A circuit induces such a trace by the observations above; full project-Circuit semantics bridge is still a human proof.

## Exact capacity: at most 60 merge events per OR gate

There are 54 four-arcs disjoint from each line. For fixed global singleton supports U,V of a two-parent OR gate, put S=U∪V. If this gate contributes a merge to (L,B), both U∩L and V∩L are nonempty, their intersection on L is empty, and S∩B=∅ (by monotonicity and falsity on B).

Define W_L(S)=number of four-arcs B disjoint from both L and S. The charge of any disjoint partition S=U' ⊔ V' is sum of W_L(S) over lines meeting both sides. Overlapping U,V cannot increase the maximum: assign each shared point to either side. Every line on which a merge was possible had no overlap on L, so its contributions remain possible for the chosen disjoint partition. Thus the disjoint-partition maximum bounds arbitrary OR gates.

Exact finite calculation: for each of 8,178 support masks S of size >=2, first sum W_L(S) over lines with |S∩L|>=2. This bounds all partitions. In 7,125 cases it is <=60. For every other S, enumerate every nontrivial unordered bipartition; 7,371 tests, maximum exactly 60. A witness is U'={0,1}, V'={2}. No SAT, randomized search, floating point, or budget truncation. All 234 four-arcs enumerated from geometry. Code and exact result: arc1494_line_or_gate_charge.py/.json. Independently kernel-checked Arc1494LineOrCharge.lean verifies exact line/triple masks, exact four-arc list, 54 negatives per line, all 630 cyclic representatives of support masks of size >=2, each representative's weight bound, and tight example. Cyclic rotation preserves the line family, arcs and both disjointness conditions, so checking orbit representatives suffices. The direct Python calculation does not use rotation and provides an independent all-mask check.

Therefore with o OR gates, 162 m <=60 o, since each of the m lines has 54 negative four-arcs with three required events each.

## Closing the exact gate count even with AND gates

Let a be the AND count. If a>=3, then o>=ceil(162m/60), so a+o>=3m for m<=13 (since 3m-2.7m<=3.9, and the ceiling reduces the required integer difference to at most 3).

If a<=2, mark an output line dirty if some AND gate with singleton support of size at least two reaches it along a path consisting solely of OR gates after that AND (zero-length path allowed). Each such AND can reach at most one distinct output line through an OR-only path: its singleton support must be contained in every such output line, and two distinct lines intersect in only one point. Hence the number d of dirty output lines is at most a<=2.

For each of the m-d other outputs, explore its backward OR-only cone, stopping at inputs/constants/AND gates. All terminal singleton supports are empty or singletons, including those at AND gates. All internal OR supports are contained in L. To obtain the four-point support of the output, at least three distinct OR gates with support size >=2 in this cone are needed (same component argument, now no negative-arc conditioning). Choose three such gates for each non-dirty output. The selected gates for distinct lines are distinct. None can be charged a merge for any other line: its singleton support is contained in its own line, so intersects every different line in at most one point.

Remove these 3(m-d) selected OR gates from the pool used for dirty-line merge events. The same capacity bound on all remaining OR gates gives 162d <=60(o-3(m-d)). For d=0,1,2, ceil(162d/60)=3d. Thus o>=3m, even before charging the AND gates.

Arc1494MergeTrace.lean theorem total_gate_count kernel-checks the arithmetic combination. Result holds for every m<=13, not only all 13 lines.

## Consequence for the scalar incidence circuit L-meta-1494

Consider a circuit satisfying the assigned arc promise whose point information reaches the rest of the circuit solely via a separated, monotone 13-bit point-side interface. The prior exact separator-charge proof shows the 13-bit interface must be the identity or the line-OR map on arcs, up to permutation. If it is the line-OR map:

1. The point-only encoder costs at least 39 gates by the theorem above.
2. The remaining decoder must depend on every one of the 13 encoder signals and every one of the 13 original line inputs. For line input w, use a point incident with w and turn only y_w on/off. For the encoder signal t_w, choose p on L_w and an arc B disjoint from L_w but meeting every other line through p. At y_w=1 and other line inputs off, decoder must output 1 on {p} and 0 on B. The encoder vector for B dominates that for {p} in all coordinates except w, where B has 0 and {p} has 1. If decoder ignored t_w, monotonicity would give contradiction. The exact 13 witnesses are verified in both Python and Lean (all_decoder_separators).
3. A fan-in-two single-output DAG depending on 26 distinct inputs has at least 25 gates: restrict to the output ancestor graph, count at least 26+g-1 edges for connectivity, at most 2g operand edges. This bound remains valid with constants, unary gates, and shared subcircuits.

The encoder and decoder gate sets are disjoint in a separated interface; hence total >=39+25=64. The same proof applies to a line-only minimum-width encoder by point-line duality (the original promise includes all line subsets, so in particular line arcs).

If the minimum-width interface is identity on the allowed inputs, it can be bypassed and its pure encoder removed without changing correctness on those inputs. Therefore a hypothetical least 63-gate counterexample cannot use a nontrivial, minimum-width pure-side encoder of either side. It must exploit a wider pure interface or mixed/interleaved gates without such compression. This is a genuine restriction of the remaining problem, not a proof excluding all mixed circuits. The unrestricted scalar 64-gate conjecture remains open.

## Evidence

- proof-lab/scripts/arc1494_line_or_gate_charge.py: direct all-mask exact enumeration, 0.328 s on BRUNHILDE; verified maximum charge 60.
- proof-lab/Lean/Arc1494LineOrCharge.lean: ARC_LINE_OR_CHARGE_LEAN_EXIT=0.
- proof-lab/Lean/Arc1494MergeTrace.lean: ARC_MERGE_TRACE_LEAN_EXIT=0.
- Prior Arc1494CutCounts.lean, Arc1494OneBitObstruction.lean and separator-charge proof remain valid and separate.
- No claim of novelty or upstream acceptance. Next exact proof obligation is pricing genuinely mixed gates or a wider interface (not repeating indiscriminate SAT searches).
