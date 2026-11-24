import Init

namespace SophiaResearch.Arc1494FourSeedObstruction

def lines : List Nat := [523,1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357]

def pop13 (a : Nat) : Nat :=
  ((List.range 13).filter fun i => a.testBit i).length

def fourArcs : List Nat := [29,39,58,71,77,78,83,85,101,105,116,135,141,142,154,156,166,170,195,201,202,210,232,270,275,281,282,284,297,308,312,329,332,337,340,387,390,402,404,420,449,464,533,540,549,550,562,564,568,593,594,609,616,624,658,664,674,680,774,780,801,804,808,833,840,897,898,928,1037,1049,1059,1061,1065,1066,1080,1098,1100,1124,1128,1136,1155,1157,1186,1188,1218,1232,1248,1283,1297,1313,1316,1328,1348,1360,1541,1548,1553,1560,1602,1608,1616,1665,1666,1680,1793,1794,1796,1856,2055,2067,2069,2073,2074,2083,2098,2118,2122,2130,2132,2160,2181,2185,2196,2200,2248,2256,2272,2307,2310,2313,2314,2337,2372,2376,2433,2436,2464,2496,2565,2566,2593,2594,2626,2632,2656,2689,2696,2720,3082,3096,3106,3120,3204,3216,3232,3330,3332,3360,3586,3588,3592,3712,4110,4115,4131,4134,4137,4138,4146,4148,4163,4166,4193,4196,4233,4236,4244,4260,4264,4289,4320,4362,4370,4392,4400,4496,4512,4544,4614,4620,4625,4626,4628,4673,4674,4737,4744,4752,4866,4872,4928,4992,5123,5129,5130,5132,5137,5186,5188,5249,5252,5264,5312,5378,5392,5440,6153,6161,6164,6177,6192,6212,6240,6408,6432,6464,6657,6660,6664,6720,7172,7176,7184,7424]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem four_arcs_exact : fourArcs = (List.range 8192).filter (fun a => pop13 a == 4 &&
    lines.all (fun l => decide (pop13 (a &&& l) ≤ 2))) := by decide +kernel

def privateArcs (seeds : List Nat) (e : Nat) : List Nat :=
  fourArcs.filter fun a => (a &&& e) == 0 &&
    seeds.all (fun f => f == e || (f &&& a) != 0)

def regular (e z p : Nat) : Bool :=
  !e.testBit p && p != z

def pairCheck (seeds : List Nat) (e z : Nat) : Bool :=
  let as := privateArcs seeds e
  (List.range 13).all (fun p =>
    !regular e z p || as.any (fun a => !a.testBit p)) &&
  (List.range 13).all (fun p =>
    (List.range 13).all (fun q =>
      !regular e z p || !regular e z q || p == q ||
      as.any (fun a => !a.testBit p && a.testBit q)))

def first : List Nat := [3,36,80,384]
def second : List Nat := [3,36,1152,4160]
def zfirst : List Nat := [9,11,12,10]
def zsecond : List Nat := [9,11,8,4]

-- Check using precomputed arc lists, which are independently verified
-- against the geometry.
def allCheck (seeds zs : List Nat) : Bool :=
  (seeds.zip zs).all (fun ez => pairCheck seeds ez.1 ez.2)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem first_check : allCheck first zfirst = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
theorem second_check : allCheck second zsecond = true := by
  decide +kernel

def exceptionCount (seeds zs : List Nat) (p : Nat) : Nat :=
  ((seeds.zip zs).filter fun ez => !regular ez.1 ez.2 p).length

theorem first_exceptions :
    (List.range 13).all (fun p => decide (exceptionCount first zfirst p ≤ 1)) = true := by
  decide +kernel

theorem second_exceptions :
    (List.range 13).all (fun p => decide (exceptionCount second zsecond p ≤ 1)) = true := by
  decide +kernel

-- The private-family counting argument: a degree-one regular point
-- consumes an exclusive filter; other points occur at least twice,
-- and each filter can contain at most three regular extra points.
theorem private_family_count (low high exclusive other : Nat)
    (hlow : low ≤ exclusive)
    (hhigh : 2*high ≤ 3*other) :
    2*(low+high) ≤ 3*(exclusive+other) := by omega

theorem four_seed_contradiction (s f n m total : Nat)
    (hs : s ≤ 7) (hf : f ≤ 14)
    (hm : m = 13-s) (hgroups : 3*m ≤ total)
    (hprivate : 2*total ≤ 3*n)
    (hdisjoint : s+n ≤ f) : False := by omega

end SophiaResearch.Arc1494FourSeedObstruction
