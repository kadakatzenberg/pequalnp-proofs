import Init

namespace SophiaResearch.Arc1494NearSaturated

-- Same finite line and four-arc masks as the preceding certificates.
def lines : List Nat := [523,1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357]
def fourArcs : List Nat := [29,39,58,71,77,78,83,85,101,105,116,135,141,142,154,156,166,170,195,201,202,210,232,270,275,281,282,284,297,308,312,329,332,337,340,387,390,402,404,420,449,464,533,540,549,550,562,564,568,593,594,609,616,624,658,664,674,680,774,780,801,804,808,833,840,897,898,928,1037,1049,1059,1061,1065,1066,1080,1098,1100,1124,1128,1136,1155,1157,1186,1188,1218,1232,1248,1283,1297,1313,1316,1328,1348,1360,1541,1548,1553,1560,1602,1608,1616,1665,1666,1680,1793,1794,1796,1856,2055,2067,2069,2073,2074,2083,2098,2118,2122,2130,2132,2160,2181,2185,2196,2200,2248,2256,2272,2307,2310,2313,2314,2337,2372,2376,2433,2436,2464,2496,2565,2566,2593,2594,2626,2632,2656,2689,2696,2720,3082,3096,3106,3120,3204,3216,3232,3330,3332,3360,3586,3588,3592,3712,4110,4115,4131,4134,4137,4138,4146,4148,4163,4166,4193,4196,4233,4236,4244,4260,4264,4289,4320,4362,4370,4392,4400,4496,4512,4544,4614,4620,4625,4626,4628,4673,4674,4737,4744,4752,4866,4872,4928,4992,5123,5129,5130,5132,5137,5186,5188,5249,5252,5264,5312,5378,5392,5440,6153,6161,6164,6177,6192,6212,6240,6408,6432,6464,6657,6660,6664,6720,7172,7176,7184,7424]
def reps : List Nat := [7,13,15,19,21,23,25,27,29,31,35,37,39,41,43,45,47,51,53,55,57,59,61,67,69,71,73,75,77,79,81,83,85,87,89,91,93,97,99,101,103,105,107,109,113,115,117,121,131,133,135,137,139,141,143,147,149,151,153,155,157,163,165,167,169,171,173,179,181,185,195,197,199,201,203,205,209,211,213,217,225,227,229,233,241,265,267,269,271,273,275,277,279,281,283,285,291,293,295,297,299,301,305,307,309,313,323,325,327,329,331,333,337,339,341,345,355,357,361,369,391,393,395,397,401,403,405,409,419,421,425,433,453,457,465,547,549,551,553,555,557,563,565,569,581,583,585,587,589,595,597,601,611,613,617,651,653,659,661,665,675,677,681,713,793,805,809,841,1171,1173,1189]
def pop13 (a : Nat) : Nat := ((List.range 13).filter fun i => a.testBit i).length
def rotate (a k : Nat) : Nat := (a * 2^k) % 8192 + a / (2^(13-k))
def rep (a : Nat) : Nat := (List.range 13).foldl (fun s i => min s (rotate a i)) a
def collinear (a : Nat) : Bool := lines.any fun l => (a &&& l) == a
set_option maxRecDepth 65536 in
set_option maxHeartbeats 50000000 in
theorem reps_exact :
    reps = (List.range 8192).filter
      (fun s => decide (3 ≤ pop13 s ∧ pop13 s ≤ 5) && !collinear s && rep s == s) := by
  decide +kernel

def submasks (s : Nat) : List Nat :=
  (List.range 13).foldl
    (fun acc i => if s.testBit i then acc ++ acc.map (fun a => a + 2^i) else acc) [0]
def two (a : Nat) : Bool := a != 0 && (a &&& (a-1)) != 0
def weight (s l : Nat) : Nat :=
  (fourArcs.filter fun a => (a &&& (s ||| l)) == 0).length
def weights (s : Nat) : List (Nat × Nat) :=
  lines.map fun l => (l, if two (s &&& l) then weight s l else 0)
def complete (s : Nat) (ws : List (Nat × Nat)) : Nat :=
  ws.foldl (fun c lw => if (s &&& lw.1) == lw.1 then c + lw.2 else c) 0
def mv (a b : Nat) (ws : List (Nat × Nat)) : List (Nat × Nat) :=
  ws.map (fun lw => (lw.1, if (a &&& lw.1) != 0 && (b &&& lw.1) != 0 then lw.2 else 0))
def checkPartition (s a : Nat) (ws : List (Nat × Nat)) : Bool :=
  let v := mv a (s-a) ws
  let c := complete s ws
  let cap := 10 * (v.map Prod.snd).foldl (·+·) 0 + c
  if cap < 540 then true
  else cap == 600 &&
    (if c == 0 then v.all (fun lw => lw.2 % 15 == 0)
     else c == 30 &&
       (v.filter fun lw => (s &&& lw.1) == lw.1).map Prod.snd == [30] &&
       ((v.filter fun lw => (s &&& lw.1) != lw.1 && lw.2 != 0).map Prod.snd == [9,9,9]))
def check (s : Nat) : Bool :=
  let ws := weights s
  if 10 * (ws.map Prod.snd).foldl (·+·) 0 + complete s ws < 540 then true
  else (submasks s).all fun a => checkPartition s a ws

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem high_capacity_patterns : reps.all check = true := by decide +kernel

-- Arithmetic consequences of the unused-capacity budget.
theorem five_case_budget (k u t d : Nat)
    (hk : 11 ≤ k ∧ k ≤ 13)
    (ht : 3*(13-k) ≤ t)
    (h : 10*d + 60*u + 30*(t-3*(13-k)) ≤ 30*k-330) :
    (k = 11 ∧ u = 0 ∧ t = 6 ∧ d = 0) ∨
    (k = 12 ∧ u = 0 ∧ t ≤ 4 ∧ d ≤ 3) ∨
    (k = 13 ∧ u + 3*t ≤ 6 ∧ d ≤ 6) := by omega

theorem exact_line_13 (h v d : Nat)
    (hd : d ≤ 6) (he : 54+9*h+15*v = 162+d) : 1 ≤ h := by omega

theorem exact_line_12 (h v d : Nat)
    (hd : d ≤ 3) (he : 54+9*h+15*v = 162+d) : 2 ≤ h := by
  by_cases h0 : h = 0
  · subst h
    omega
  · by_cases h1 : h = 1
    · subst h
      omega
    · omega

theorem exact_line_11 (r h v : Nat)
    (he : 54+54*r+9*h+15*v = 162) : 2 ≤ r+h := by omega

theorem missing_line_11 (r h v : Nat)
    (he : 90+54*r+9*h+15*v = 162) : 3 ≤ r+h := by omega

theorem eleven_aggregate (r h : Nat)
    (hr : r = 5) (hh : h ≤ 18) (hneed : 28 ≤ r+h) : False := by omega

theorem twelve_aggregate (n h : Nat)
    (hn : 7 ≤ n) (hh : h ≤ 12) (hneed : 2*n ≤ h) : False := by omega

theorem thirteen_aggregate (n h : Nat)
    (hn : 8 ≤ n) (hh : h ≤ 6) (hneed : n ≤ h) : False := by omega

end SophiaResearch.Arc1494NearSaturated
