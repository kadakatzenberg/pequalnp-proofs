import Init

namespace SophiaResearch.Arc1494CutCounts

def lineMasks : List Nat := [523,1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357]
def pointMasks : List Nat := [5137,2083,4166,141,282,564,1128,2256,4512,833,1666,3332,6664]
def tripleMasks : List Nat := [522,521,515,11,1044,1042,1030,22,2088,2084,2060,44,4176,4168,4120,88,161,145,49,176,322,290,98,352,644,580,196,704,1288,1160,392,1408,2576,2320,784,2816,5152,4640,1568,5632,2113,1089,3136,3073,4226,2178,6272,6146,261,4356,4353,4101]

def pack (p : Nat → Bool) : Nat :=
  (List.range 13).foldl (fun s i => if p i then s + 2 ^ i else s) 0

def directLine (w : Nat) : Nat :=
  ([0,1,3,9] : List Nat).foldl (fun s d => s + 2 ^ ((w+d)%13)) 0

def directTriples (w : Nat) : List Nat :=
  let a := 2 ^ (w%13)
  let b := 2 ^ ((w+1)%13)
  let c := 2 ^ ((w+3)%13)
  let d := 2 ^ ((w+9)%13)
  [b+c+d, a+c+d, a+b+d, a+b+c]

theorem line_masks_exact :
    lineMasks = (List.range 13).map directLine := by decide +kernel

theorem point_masks_exact :
    pointMasks = (List.range 13).map (fun p => pack (fun w => (lineMasks[w]!).testBit p)) := by
  decide +kernel

theorem triple_masks_exact :
    tripleMasks = (List.range 13).flatMap directTriples := by decide +kernel

def arc (a : Nat) : Bool :=
  tripleMasks.all fun t => (a &&& t) != t

-- Finite lookup is independently checked against the geometric definition.
def arcBits : Nat := 0x100000000000000000000000000000000000000000000000000000000000101110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000011300000000000000000000000000000000000000000000000100000001000001010000000000000000000000000000000000000001000000110001000300130313000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000010005000000000000000100000000000100130000000000000015000000000003171f00000000000000000000000000000001000000000000000100000000000001050000000000000000000000000001010300000000000000070000000000171157000000000000000100000001000100010000000000000001000101010005050500000001000000030000011100111313000000130000005f0015075f001f575f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001150000000000000000000000000000000000000000000000000000000100000015000000000000000000000001000100110000000000000000000100050101051500000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000010300000001000001050000000700000177000000000000000100000001000000130000000000000111000000030000075f0000000100010101000000010111033300010001001505550005000f073f07ff00000000000000000000000000000000000000000000000100000000000000170000000000000000000000000001000700000000000101050000000001031137000000000000000000000000000000000000000000010011000100130003001f0000000100010005000000150001003f00010111000115150101073f0303373f000000000000000000000001000000070000000000000103000001130000115700000000000000000000010501050107000101030007010701150177113711770000000000010003000000110015005f000000000013131301110313171f575f000001010005070f00000555151577ff00110333003f77ff051507ff373f77ff

def lookup (a : Nat) : Bool := arcBits.testBit a

def signature (a : Nat) : Nat :=
  pack fun w => (a &&& lineMasks[w]!) != 0

def recover (n : Nat) : Nat :=
  pack fun p => (n &&& pointMasks[p]!) == pointMasks[p]!

set_option maxRecDepth 65536 in
set_option maxHeartbeats 30000000 in
theorem table_correct :
    (List.range 8192).all (fun a => lookup a == arc a) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 30000000 in
theorem count_arcs :
    ((List.range 8192).filter lookup).length = 560 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 30000000 in
theorem recovery_test :
    (List.range 8192).all (fun a => !lookup a || (recover (signature a) == a)) = true := by
  decide +kernel

theorem recovery (a : Fin 8192) (ha : lookup a.val = true) :
    recover (signature a.val) = a.val := by
  have hh := List.all_eq_true.mp recovery_test a.val (List.mem_range.mpr a.isLt)
  simp [ha] at hh
  exact hh

theorem signatures_injective (a b : Fin 8192)
    (ha : lookup a.val = true) (hb : lookup b.val = true)
    (h : signature a.val = signature b.val) : a = b := by
  apply Fin.ext
  rw [← recovery a ha, ← recovery b hb, h]

def pop13 (a : Nat) : Nat :=
  ((List.range 13).filter (fun i => a.testBit i)).length

def rotate (a k : Nat) : Nat :=
  (a * 2 ^ k) % 8192 + a / (2 ^ (13-k))

def representative (a : Nat) : Nat :=
  (List.range 13).foldl (fun s i => min s (rotate a i)) a

def sevenReps : List Nat := [127,191,223,239,247,251,253,319,351,367,375,379,381,415,431,439,443,445,463,471,475,477,487,491,493,499,501,505,575,607,623,631,635,637,671,687,695,699,701,719,727,731,733,743,747,749,755,757,761,799,815,823,827,829,847,855,859,861,871,875,877,883,885,889,911,919,923,925,935,939,941,947,949,953,971,973,979,981,985,997,1001,1183,1199,1207,1211,1213,1231,1239,1243,1245,1255,1259,1261,1267,1269,1327,1335,1339,1341,1359,1367,1371,1373,1383,1387,1389,1395,1397,1431,1435,1437,1447,1451,1453,1459,1461,1485,1491,1493,1639,1643,1645,1653,1691,1693,1703,1707,1709,1717,1749,1877,2731]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 30000000 in
theorem reps_exact :
    sevenReps = (List.range 8192).filter
      (fun s => pop13 s == 7 && representative s == s) := by
  decide +kernel

def submasks (s : Nat) : List Nat :=
  (List.range 13).foldl
    (fun acc i => if s.testBit i then acc ++ acc.map (fun a => a + 2 ^ i) else acc) [0]

def arcCount (s : Nat) : Nat :=
  ((submasks s).filter lookup).length

set_option maxRecDepth 65536 in
set_option maxHeartbeats 30000000 in
theorem seven_rep_minimum :
    sevenReps.all (fun s => decide (65 ≤ arcCount s)) = true ∧
    sevenReps.any (fun s => arcCount s == 65) = true := by
  decide +kernel

end SophiaResearch.Arc1494CutCounts
