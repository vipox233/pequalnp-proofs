import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_650_aux

def allOnes (N : Nat) : Nat := (1 <<< N) - 1

def mkPlaneLoop (acc shift : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => mkPlaneLoop (acc ||| (acc <<< shift)) (shift <<< 1) n

def mkPlane (idx : Nat) : Nat :=
  let half := 1 <<< idx
  let period := 1 <<< (idx + 1)
  let block := ((1 <<< half) - 1) <<< half
  mkPlaneLoop block period (16 - idx)

def listMask : List Nat → Nat
  | [] => 0
  | x :: xs => (1 <<< x) ||| listMask xs

def mkListPlane (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (x.testBit b).toNat ||| (mkListPlane b xs <<< 1)

structure Planes17 where
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p4 : Nat
  p5 : Nat
  p6 : Nat
  p7 : Nat
  p8 : Nat
  p9 : Nat
  p10 : Nat
  p11 : Nat
  p12 : Nat
  p13 : Nat
  p14 : Nat
  p15 : Nat
  p16 : Nat

def Planes17.get (a : Planes17) : Nat → Nat
  | 0 => a.p0
  | 1 => a.p1
  | 2 => a.p2
  | 3 => a.p3
  | 4 => a.p4
  | 5 => a.p5
  | 6 => a.p6
  | 7 => a.p7
  | 8 => a.p8
  | 9 => a.p9
  | 10 => a.p10
  | 11 => a.p11
  | 12 => a.p12
  | 13 => a.p13
  | 14 => a.p14
  | 15 => a.p15
  | 16 => a.p16
  | _ => 0

def Planes17.xor (a b : Planes17) : Planes17 :=
  ⟨a.p0 ^^^ b.p0, a.p1 ^^^ b.p1, a.p2 ^^^ b.p2, a.p3 ^^^ b.p3,
   a.p4 ^^^ b.p4, a.p5 ^^^ b.p5, a.p6 ^^^ b.p6, a.p7 ^^^ b.p7,
   a.p8 ^^^ b.p8, a.p9 ^^^ b.p9, a.p10 ^^^ b.p10, a.p11 ^^^ b.p11,
   a.p12 ^^^ b.p12, a.p13 ^^^ b.p13, a.p14 ^^^ b.p14, a.p15 ^^^ b.p15,
   a.p16 ^^^ b.p16⟩

def Planes17.xorConst (ones : Nat) (a : Planes17) (c : Nat) : Planes17 :=
  ⟨if c.testBit 0 then a.p0 ^^^ ones else a.p0,
   if c.testBit 1 then a.p1 ^^^ ones else a.p1,
   if c.testBit 2 then a.p2 ^^^ ones else a.p2,
   if c.testBit 3 then a.p3 ^^^ ones else a.p3,
   if c.testBit 4 then a.p4 ^^^ ones else a.p4,
   if c.testBit 5 then a.p5 ^^^ ones else a.p5,
   if c.testBit 6 then a.p6 ^^^ ones else a.p6,
   if c.testBit 7 then a.p7 ^^^ ones else a.p7,
   if c.testBit 8 then a.p8 ^^^ ones else a.p8,
   if c.testBit 9 then a.p9 ^^^ ones else a.p9,
   if c.testBit 10 then a.p10 ^^^ ones else a.p10,
   if c.testBit 11 then a.p11 ^^^ ones else a.p11,
   if c.testBit 12 then a.p12 ^^^ ones else a.p12,
   if c.testBit 13 then a.p13 ^^^ ones else a.p13,
   if c.testBit 14 then a.p14 ^^^ ones else a.p14,
   if c.testBit 15 then a.p15 ^^^ ones else a.p15,
   if c.testBit 16 then a.p16 ^^^ ones else a.p16⟩

def Planes17.rot1 (a : Planes17) : Planes17 :=
  ⟨a.p16, a.p0, a.p1, a.p2, a.p3, a.p4, a.p5, a.p6, a.p7,
   a.p8, a.p9, a.p10, a.p11, a.p12, a.p13, a.p14, a.p15⟩

def Planes17.rotIter : Nat → Planes17 → Planes17
  | 0, a => a
  | n + 1, a => Planes17.rotIter n a.rot1

def Planes17.rotN (s : Nat) (a : Planes17) : Planes17 :=
  Planes17.rotIter (s % 17) a

def Planes17.step (ones : Nat) (a : Planes17) : Planes17 :=
  ⟨a.p0 ^^^ ((ones ^^^ a.p1) &&& a.p2),
   a.p1 ^^^ ((ones ^^^ a.p2) &&& a.p3),
   a.p2 ^^^ ((ones ^^^ a.p3) &&& a.p4),
   a.p3 ^^^ ((ones ^^^ a.p4) &&& a.p5),
   a.p4 ^^^ ((ones ^^^ a.p5) &&& a.p6),
   a.p5 ^^^ ((ones ^^^ a.p6) &&& a.p7),
   a.p6 ^^^ ((ones ^^^ a.p7) &&& a.p8),
   a.p7 ^^^ ((ones ^^^ a.p8) &&& a.p9),
   a.p8 ^^^ ((ones ^^^ a.p9) &&& a.p10),
   a.p9 ^^^ ((ones ^^^ a.p10) &&& a.p11),
   a.p10 ^^^ ((ones ^^^ a.p11) &&& a.p12),
   a.p11 ^^^ ((ones ^^^ a.p12) &&& a.p13),
   a.p12 ^^^ ((ones ^^^ a.p13) &&& a.p14),
   a.p13 ^^^ ((ones ^^^ a.p14) &&& a.p15),
   a.p14 ^^^ ((ones ^^^ a.p15) &&& a.p16),
   a.p15 ^^^ ((ones ^^^ a.p16) &&& a.p0),
   a.p16 ^^^ ((ones ^^^ a.p0) &&& a.p1)⟩

def Planes17.hiZero (ones : Nat) (a : Planes17) : Nat :=
  ones ^^^ (a.p8 ||| a.p9 ||| a.p10 ||| a.p11 ||| a.p12 ||| a.p13 ||| a.p14 ||| a.p15 ||| a.p16)

def Planes17.hiEq (ones : Nat) (a : Planes17) (v : Nat) : Bool :=
  (a.p8 == if v.testBit 0 then ones else 0) &&
  (a.p9 == if v.testBit 1 then ones else 0) &&
  (a.p10 == if v.testBit 2 then ones else 0) &&
  (a.p11 == if v.testBit 3 then ones else 0) &&
  (a.p12 == if v.testBit 4 then ones else 0) &&
  (a.p13 == if v.testBit 5 then ones else 0) &&
  (a.p14 == if v.testBit 6 then ones else 0) &&
  (a.p15 == if v.testBit 7 then ones else 0) &&
  (a.p16 == if v.testBit 8 then ones else 0)

def keyPlanes : Planes17 :=
  ⟨mkPlane 0, mkPlane 1, mkPlane 2, mkPlane 3, mkPlane 4, mkPlane 5, mkPlane 6, mkPlane 7,
   mkPlane 8, mkPlane 9, mkPlane 10, mkPlane 11, mkPlane 12, mkPlane 13, mkPlane 14, mkPlane 15,
   mkPlane 16⟩

def mkListPlanes (l : List Nat) : Planes17 :=
  ⟨mkListPlane 0 l, mkListPlane 1 l, mkListPlane 2 l, mkListPlane 3 l,
   mkListPlane 4 l, mkListPlane 5 l, mkListPlane 6 l, mkListPlane 7 l,
   mkListPlane 8 l, mkListPlane 9 l, mkListPlane 10 l, mkListPlane 11 l,
   mkListPlane 12 l, mkListPlane 13 l, mkListPlane 14 l, mkListPlane 15 l,
   mkListPlane 16 l⟩

def outRound (ones : Nat) (w x : Planes17) (t : Nat) : Planes17 :=
  let c := (3 ^ (17 + (t + 1))) % 131072
  let y := x.xor (x.rotN 1) |>.xor (x.rotN 16)
  ((y.step ones).xor (w.rotN (2 * t))).xorConst ones c

def outPlanes (ones : Nat) (w : Planes17) : Planes17 :=
  let x0 := w.rotN 1
  let x1 := outRound ones w x0 0
  let x2 := outRound ones w x1 1
  let x3 := outRound ones w x2 2
  outRound ones w x3 3

def colRound (ones : Nat) (w st : Planes17) (j : Nat) : Planes17 :=
  let c := (3 ^ (17 + (4 + (j + 1)))) % 131072
  let y := st.xor (st.rotN 2) |>.xor (st.rotN 15)
  ((y.step ones).xor (w.rotN (3 * (j + 1) + 1))).xorConst ones c

def colMask (ones : Nat) (w : Planes17) (name : Nat) : Nat :=
  let s0 := (w.rotN 3).xorConst ones name
  let s1 := colRound ones w s0 0
  let s2 := colRound ones w s1 1
  let s3 := colRound ones w s2 2
  (colRound ones w s3 3).hiZero ones

def colMaskVar (ones : Nat) (w nameP : Planes17) : Nat :=
  let s0 := (w.rotN 3).xor nameP
  let s1 := colRound ones w s0 0
  let s2 := colRound ones w s1 1
  let s3 := colRound ones w s2 2
  (colRound ones w s3 3).hiZero ones

def scalarRot (s word : Nat) : Nat :=
  ((word <<< (s % 17)) ||| (word >>> (17 - s % 17))) % 2 ^ 17

def scalarStep (word : Nat) : Nat :=
  (List.range 17).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))).toNat <<< b)) 0

def scalarOut (w : Nat) : Nat :=
  ((List.range 4).foldl (fun x t =>
    scalarStep (x ^^^ scalarRot 1 x ^^^ scalarRot (17 - 1) x) ^^^ scalarRot (2 * t) w ^^^
      (3 ^ (17 + (t + 1)) % 2 ^ 17)) (scalarRot 1 w))

def scalarCol (key name : Nat) : Nat :=
  (List.range 4).foldl (fun state j =>
    scalarStep (state ^^^ scalarRot 2 state ^^^ scalarRot (17 - 2) state) ^^^
      scalarRot (3 * (j + 1) + 1) key ^^^ (3 ^ (17 + (4 + (j + 1))) % 2 ^ 17))
    (scalarRot 3 key ^^^ name)

def scalarParity (mask word : Nat) : Bool :=
  ((List.range 17).filter (fun i => mask.testBit i && word.testBit i)).length % 2 == 1

def zKeys : List Nat := [600, 1664, 1679, 2013, 3861, 4589, 4814, 4898, 5278, 6040, 6178, 6240, 6995, 8903, 9681,
  9748, 9915, 10978, 11632, 11824, 12075, 12520, 13521, 15024, 15296, 15655, 16477, 16757, 16909, 17856,
  17898, 18343, 19140, 19400, 19776, 20112, 20370, 20900, 21159, 21259, 21596, 22768, 22859, 23272, 25026,
  25826, 26534, 26739, 26759, 27159, 27997, 28860, 28994, 30241, 30484, 31133, 31948, 31998, 32661, 32663,
  33044, 33090, 33183, 33518, 34823, 36669, 37350, 37494, 40762, 41286, 41853, 42390, 42433, 42686, 43470,
  44336, 44338, 44804, 44807, 45313, 45805, 46833, 47926, 48987, 49759, 50405, 51043, 51223, 51256, 51297,
  51443, 52160, 53526, 53668, 53819, 53913, 53996, 54725, 54770, 54894, 55068, 55337, 55893, 56022, 56400,
  56402, 57135, 57217, 57336, 59433, 60642, 61836, 62296, 62429, 62932, 64261, 64939, 64944, 65676, 66245,
  66489, 66490, 68211, 68840, 69580, 69581, 69582, 71418, 71845, 71866, 72741, 73474, 73603, 74872, 75728,
  75842, 76159, 76509, 76714, 76740, 77905, 78182, 78249, 78883, 80936, 81356, 81358, 81699, 82531, 83167,
  83557, 85649, 85830, 86101, 86179, 87528, 88375, 88679, 90063, 90184, 90569, 90780, 91543, 91857, 92256,
  92297, 93301, 93398, 94488, 95016, 95197, 95349, 96655, 97705, 98342, 98493, 98718, 98936, 99731, 100075,
  100782, 101505, 102141, 102143, 102857, 102859, 102887, 103265, 104153, 104222, 104373, 104891, 105199, 105433, 105540,
  106110, 106480, 106541, 106910, 107389, 107519, 107617, 108194, 109517, 110377, 111057, 111804, 111895, 112246, 112249,
  112833, 113200, 113359, 114004, 114113, 114230, 115329, 115330, 115959, 116435, 116584, 116851, 117147, 117172, 117478,
  117748, 118598, 118946, 119285, 119286, 119371, 121023, 121205, 121597, 121599, 122724, 123471, 125265, 125342, 125763,
  126992, 127141, 127400, 127685, 127992, 128597, 129216, 129787, 129850]

def negCols : List Nat := [111586, 5546, 127090, 37393, 14954, 31207, 3881, 7711, 7918, 8514, 9614, 17079, 19566, 22823, 23103,
  28277, 33779, 35204, 35585, 36792, 38652, 49364, 63828, 90502, 64, 553, 1130, 2069, 3826, 4677,
  5011, 5404, 6288, 10483, 10770, 10975, 14129, 14778, 15049, 17261, 19412, 21307, 21713, 33155, 34555,
  40834, 71199, 125960, 84, 317, 742]

def w0Keys : List Nat := [1241, 1659, 2313, 3011, 3241, 3395, 4906, 5098, 8753, 9546, 9795, 11251, 11386, 12371, 13203,
  13489, 15560, 16411, 19528, 19883, 23130, 24384, 26907, 27952, 28923, 32834, 33816, 34530, 35672, 38410,
  38817, 40265, 40931, 41354, 41665, 42641, 44251, 44872, 47066, 47312, 48585, 48744, 50091, 50138, 52274,
  57898, 59025, 59880, 60275, 62113, 62403, 64171, 64584, 65104, 66136, 66954, 66993, 67123, 68680, 69009,
  69704, 70443, 71177, 72314, 73579, 74250, 74505, 74985, 75107, 75169, 76896, 77130, 79491, 80835, 80946,
  81451, 81779, 84179, 84194, 84721, 85643, 85754, 86545, 87240, 87563, 89443, 90488, 91938, 92706, 93657,
  94873, 95128, 96241, 96753, 96760, 99770, 100216, 101203, 102067, 103224, 103499, 104265, 104497, 104714, 106697,
  108089, 110082, 110130, 110738, 111915, 113010, 113321, 113833, 114056, 115323, 115936, 115970, 119210, 119322, 120345,
  124624, 124944, 126874, 127040, 129762]

def w0Cols : List Nat := [37393, 10770, 14954, 111586, 35204, 37393, 21307, 127090, 2069, 33779, 64, 111586, 9614, 31207, 22823,
  31207, 34555, 8514, 40834, 31207, 14954, 90502, 38652, 37393, 8514, 14954, 63828, 6288, 28277, 15049,
  4677, 553, 37393, 111586, 3826, 35204, 35585, 90502, 38652, 17079, 553, 31207, 1130, 10975, 10483,
  14954, 64, 49364, 71199, 35585, 3881, 15049, 5404, 10770, 38652, 5011, 36792, 125960, 127090, 63828,
  6288, 23103, 19412, 5546, 7711, 9614, 17079, 49364, 23103, 5011, 84, 21713, 14778, 28277, 742,
  17079, 5546, 10483, 21307, 317, 3881, 19566, 7711, 14129, 36792, 19566, 17261, 35204, 37393, 19412,
  21713, 33155, 9614, 7711, 7918, 90502, 10975, 5404, 1130, 33155, 125960, 17261, 19566, 14778, 23103,
  28277, 22823, 7918, 33779, 3881, 2069, 33779, 34555, 8514, 71199, 3826, 22823, 4677, 49364, 63828,
  7918, 40834, 36792, 35585, 14129]

def spC1 : Nat := 111586
def spW1 : Nat := 48808
def spC2 : Nat := 5546
def spW2 : Nat := 80232
def spC3 : Nat := 127090
def spW3 : Nat := 109232

def spKeys : List Nat := [11632, spW1, spW2, spW3]
def spCols : List Nat := [0, spC1, spC2, spC3]
def spProbes : List Nat := [11632 ^^^ 12, spW1 ^^^ 12, spW2 ^^^ 12, spW3 ^^^ 12]

def onesAll : Nat := allOnes 131072
def onesZ : Nat := allOnes 249
def onesW : Nat := allOnes 125
def ones4 : Nat := allOnes 4

def outZMask : Nat := (outPlanes onesAll keyPlanes).hiZero onesAll
def col0Mask : Nat := colMask onesAll keyPlanes 0
def bit2Mask : Nat := keyPlanes.p2
def nbit2Mask : Nat := onesAll ^^^ bit2Mask
def zPlanes : Planes17 := mkListPlanes zKeys
def w0Planes : Planes17 := mkListPlanes w0Keys
def c0Planes : Planes17 := mkListPlanes w0Cols
def spKeyPlanes : Planes17 := mkListPlanes spKeys
def spColPlanes : Planes17 := mkListPlanes spCols
def spProbePlanes : Planes17 := mkListPlanes spProbes

def checkGlobal : Bool :=
  (zKeys.length == 249) &&
  (w0Keys.length == 125) &&
  (w0Cols.length == 125) &&
  (zKeys.all (fun w => decide (w < 131072))) &&
  (w0Keys.all (fun w => decide (w < 131072))) &&
  (w0Cols.all (fun c => negCols.any (fun d => d == c))) &&
  (outZMask == listMask zKeys) &&
  ((bit2Mask &&& outZMask &&& col0Mask) == 0) &&
  ((nbit2Mask &&& col0Mask) == ((1 <<< 11632) ||| listMask w0Keys))

def checkNegAndPairs : Bool :=
  (negCols.all (fun c => decide (c < 131072) && (colMask onesZ zPlanes c == 0))) &&
  (colMaskVar onesW w0Planes c0Planes == onesW)

def checkSpecial : Bool :=
  (negCols.any (fun d => d == spC1)) &&
  (negCols.any (fun d => d == spC2)) &&
  (negCols.any (fun d => d == spC3)) &&
  decide (spW1 < 131072) && !(spW1.testBit 2) &&
  decide (spW2 < 131072) && !(spW2.testBit 2) &&
  decide (spW3 < 131072) && !(spW3.testBit 2) &&
  (((outPlanes ones4 spKeyPlanes).hiZero ones4).testBit 0) &&
  (colMaskVar ones4 spKeyPlanes spColPlanes == ones4) &&
  ((outPlanes ones4 spProbePlanes).hiEq ones4 203) &&
  (((spW1 ^^^ 12) ^^^ (spW2 ^^^ 12) ^^^ (spW3 ^^^ 12)) == (11632 ^^^ 12))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma checkGlobal_eq_true : checkGlobal = true := by
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma checkNegAndPairs_eq_true : checkNegAndPairs = true := by
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma checkSpecial_eq_true : checkSpecial = true := by
  rfl

lemma allOnes_eq (N : Nat) : allOnes N = 2 ^ N - 1 := by
  dsimp only [allOnes]
  rw [Nat.shiftLeft_eq, one_mul]

lemma allOnes_testBit (N j : Nat) : (allOnes N).testBit j = decide (j < N) := by
  rw [allOnes_eq, Nat.testBit_two_pow_sub_one]

lemma xor_allOnes_testBit {N a w : Nat} (hw : w < N) :
    (a ^^^ allOnes N).testBit w = !(a.testBit w) := by
  rw [Nat.testBit_xor, allOnes_testBit, decide_eq_true hw]
  cases a.testBit w <;> rfl

lemma allOnes_xor_testBit {N a w : Nat} (hw : w < N) :
    (allOnes N ^^^ a).testBit w = !(a.testBit w) := by
  rw [Nat.testBit_xor, allOnes_testBit, decide_eq_true hw]
  cases a.testBit w <;> rfl

lemma eq_of_one_shiftLeft_testBit {x w : Nat} (h : (1 <<< x).testBit w = true) : w = x := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  by_contra hne
  have hgt : 0 < w - x := by omega
  have hlt : 1 < 2 ^ (w - x) := by
    have hpow := Nat.le_self_pow (by omega : w - x ≠ 0) 2
    omega
  have hf := Nat.testBit_eq_false_of_lt hlt
  rw [hf] at h
  exact Bool.noConfusion h.2

lemma mem_of_listMask_testBit (l : List Nat) (w : Nat) :
    (listMask l).testBit w = true → w ∈ l := by
  induction l with
  | nil => simp [listMask]
  | cons x xs ih =>
    intro h
    dsimp only [listMask] at h
    rw [Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · rw [eq_of_one_shiftLeft_testBit h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem x (ih h2)

lemma exists_getD_of_mem {l : List Nat} {w : Nat} (hw : w ∈ l) :
    ∃ i < l.length, l.getD i 0 = w := by
  induction l with
  | nil => simp at hw
  | cons x xs ih =>
    simp only [List.mem_cons] at hw
    rcases hw with rfl | htl
    · exact ⟨0, by simp, rfl⟩
    · rcases ih htl with ⟨i, hi, heq⟩
      exact ⟨i + 1, by simp; omega, heq⟩

lemma getD_prop_of_all {l : List Nat} {p : Nat → Bool} (hall : l.all p = true)
    {i : Nat} (hi : i < l.length) : p (l.getD i 0) = true := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    cases i with
    | zero => exact hall.1
    | succ j =>
      simp only [List.length_cons] at hi
      exact ih hall.2 (by omega)

lemma mem_of_any_beq {l : List Nat} {c : Nat} (h : l.any (fun d => d == c) = true) : c ∈ l := by
  rcases List.any_eq_true.mp h with ⟨d, hd, hbeq⟩
  rw [beq_iff_eq] at hbeq
  subst hbeq
  exact hd

lemma mkListPlane_testBit (b : Nat) : ∀ (l : List Nat) (i : Nat),
    i < l.length → (mkListPlane b l).testBit i = (l.getD i 0).testBit b
  | [], i, hi => by simp at hi
  | x :: xs, i, hi => by
    dsimp only [mkListPlane]
    rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [Nat.not_le_of_lt Nat.zero_lt_one, decide_false, Bool.false_and, Bool.or_false]
      change ((x.testBit b).toNat).testBit 0 = x.testBit b
      cases x.testBit b <;> decide
    | succ j =>
      have hge : 1 ≤ j + 1 := by omega
      have hlt2 : (x.testBit b).toNat < 2 ^ (j + 1) := by
        have hle1 : (x.testBit b).toNat ≤ 1 := by cases x.testBit b <;> decide
        have hpow : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2
        omega
      rw [Nat.testBit_eq_false_of_lt hlt2, Bool.false_or, decide_eq_true hge, Bool.true_and,
        Nat.add_sub_cancel]
      simp only [List.length_cons] at hi
      exact mkListPlane_testBit b xs j (by omega)

lemma mkPlaneLoop_spec (fuel : Nat) :
    ∀ (acc shift : Nat), 0 < shift →
      (∀ j, shift ≤ j → acc.testBit j = false) →
      (∀ j, shift * 2 ^ fuel ≤ j → (mkPlaneLoop acc shift fuel).testBit j = false) ∧
      (∀ w < shift * 2 ^ fuel, (mkPlaneLoop acc shift fuel).testBit w = acc.testBit (w % shift)) := by
  induction fuel with
  | zero =>
    intro acc shift _ hacc
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hacc j (by simpa using hj)
    · intro w hw
      have hw' : w < shift := by simpa using hw
      simp [mkPlaneLoop, Nat.mod_eq_of_lt hw']
  | succ n ih =>
    intro acc shift hpos hacc
    let acc' := acc ||| (acc <<< shift)
    have hsh' : shift <<< 1 = 2 * shift := by
      rw [Nat.shiftLeft_eq]
      omega
    have hacc'_hi : ∀ j, 2 * shift ≤ j → acc'.testBit j = false := by
      intro j hj
      dsimp only [acc']
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hacc j (by omega)]
      have hge : shift ≤ j := by omega
      have hsub : shift ≤ j - shift := by omega
      rw [decide_eq_true hge, hacc (j - shift) hsub]
      rfl
    have hacc'_lo : ∀ r < 2 * shift, acc'.testBit r = acc.testBit (r % shift) := by
      intro r hr
      dsimp only [acc']
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
      by_cases hlt : r < shift
      · have hnot : ¬(shift ≤ r) := by omega
        rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, Nat.mod_eq_of_lt hlt]
      · have hge : shift ≤ r := by omega
        have hlt2 : r - shift < shift := by omega
        have hmod : r % shift = r - shift := by
          have h1 : r = (r - shift) + shift := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [hacc r hge, decide_eq_true hge, Bool.true_and, Bool.false_or, hmod]
    have hstep := ih acc' (shift <<< 1) (by omega) (by rw [hsh']; exact hacc'_hi)
    have hmul : shift <<< 1 * 2 ^ n = shift * 2 ^ (n + 1) := by
      rw [hsh', pow_succ]
      ring
    refine ⟨?_, ?_⟩
    · intro j hj
      dsimp only [mkPlaneLoop]
      exact hstep.1 j (by rw [hmul]; exact hj)
    · intro w hw
      dsimp only [mkPlaneLoop]
      rw [hstep.2 w (by rw [hmul]; exact hw), hsh', hacc'_lo (w % (2 * shift)) (Nat.mod_lt w (by omega))]
      have hdvd : shift ∣ 2 * shift := ⟨2, by ring⟩
      rw [Nat.mod_mod_of_dvd w hdvd]

lemma mkPlane_spec (idx : Nat) (hidx : idx < 17) :
    ∀ w < 131072, (mkPlane idx).testBit w = w.testBit idx := by
  let half := 1 <<< idx
  let period := 1 <<< (idx + 1)
  let block := ((1 <<< half) - 1) <<< half
  have hhalf : half = 2 ^ idx := by dsimp only [half]; rw [Nat.shiftLeft_eq, one_mul]
  have hperiod : period = 2 ^ (idx + 1) := by dsimp only [period]; rw [Nat.shiftLeft_eq, one_mul]
  have hp2 : period = 2 * half := by rw [hperiod, hhalf, pow_succ]; ring
  have hpos : 0 < period := by rw [hperiod]; positivity
  have hblock_eq : block = (2 ^ half - 1) <<< half := by
    dsimp only [block]
    rw [Nat.shiftLeft_eq 1 half, one_mul]
  have hblock_hi : ∀ j, period ≤ j → block.testBit j = false := by
    intro j hj
    rw [hblock_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : half ≤ j
    · rw [decide_eq_true h1, Bool.true_and, decide_eq_false (by omega)]
    · rw [decide_eq_false h1, Bool.false_and]
  have hblock_lo : ∀ r < period, block.testBit r = decide (half ≤ r) := by
    intro r hr
    rw [hblock_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : half ≤ r
    · rw [decide_eq_true h1, Bool.true_and, decide_eq_true (by omega)]
    · rw [decide_eq_false h1, Bool.false_and]
  have hpow : period * 2 ^ (16 - idx) = 131072 := by
    rw [hperiod, ← pow_add]
    have hexp : idx + 1 + (16 - idx) = 17 := by omega
    rw [hexp]
    decide
  have hloop := mkPlaneLoop_spec (16 - idx) block period hpos hblock_hi
  rw [hpow] at hloop
  intro w hw
  change (mkPlaneLoop block period (16 - idx)).testBit w = w.testBit idx
  rw [hloop.2 w hw, hblock_lo (w % period) (Nat.mod_lt w hpos)]
  rw [Nat.testBit_eq_decide_div_mod_eq, hhalf, hperiod]
  have hdiv : w % (2 ^ (idx + 1)) = 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx := by
    have h1 := Nat.div_add_mod w (2 ^ idx)
    have h2 := Nat.div_add_mod (w / 2 ^ idx) 2
    have h3 : 2 ^ (idx + 1) = 2 ^ idx * 2 := by rw [pow_succ]
    have h4 : w = 2 ^ (idx + 1) * (w / 2 ^ idx / 2) + (2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) := by
      calc
        w = 2 ^ idx * (w / 2 ^ idx) + w % 2 ^ idx := h1.symm
        _ = 2 ^ idx * (2 * (w / 2 ^ idx / 2) + (w / 2 ^ idx) % 2) + w % 2 ^ idx := by rw [h2]
        _ = 2 ^ (idx + 1) * (w / 2 ^ idx / 2) + (2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) := by
          rw [h3]; ring
    have hlt_rem : 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx < 2 ^ (idx + 1) := by
      have hm1 : (w / 2 ^ idx) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hm2 : w % 2 ^ idx < 2 ^ idx := Nat.mod_lt _ (by positivity)
      have hpow2 : 2 ^ (idx + 1) = 2 ^ idx * 2 := by rw [pow_succ]
      nlinarith
    conv_lhs => rw [h4]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_rem]
  have hm1 : (w / 2 ^ idx) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hm2 : w % 2 ^ idx < 2 ^ idx := Nat.mod_lt _ (by positivity)
  rw [hdiv]
  have hiff : (2 ^ idx ≤ 2 ^ idx * ((w / 2 ^ idx) % 2) + w % 2 ^ idx) ↔ ((w / 2 ^ idx) % 2 = 1) := by
    constructor
    · intro hge
      by_contra hne
      have hz : (w / 2 ^ idx) % 2 = 0 := by omega
      rw [hz, mul_zero, zero_add] at hge
      omega
    · intro heq
      rw [heq, mul_one]
      omega
  rw [decide_eq_decide.mpr hiff]

def RepPlanesN (N : Nat) (a : Planes17) (f : Nat → Nat) : Prop :=
  (∀ i < N, f i < 131072) ∧
  ∀ i < N, ∀ b < 17, (a.get b).testBit i = (f i).testBit b

lemma scalarRot_lt (s word : Nat) : scalarRot s word < 131072 := by
  exact Nat.mod_lt _ (by decide)

lemma scalarRot_testBit {word : Nat} (hword : word < 131072) (s b : Nat) (hb : b < 17) :
    (scalarRot s word).testBit b = word.testBit ((b + 17 - s % 17) % 17) := by
  dsimp only [scalarRot]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and,
    Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : s % 17 < 17 := Nat.mod_lt s (by omega)
  by_cases hle : s % 17 ≤ b
  · have hhi : word.testBit (17 - s % 17 + b) = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (show word < 2 ^ 17 from hword)
          (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ 17 - s % 17 + b)))
    have hidx : (b + 17 - s % 17) % 17 = b - s % 17 := by
      have h1 : b + 17 - s % 17 = (b - s % 17) + 17 := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hidx : (b + 17 - s % 17) % 17 = 17 - s % 17 + b := by
      have h1 : b + 17 - s % 17 = 17 - s % 17 + b := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hidx]

lemma scalarStep_spec (word : Nat) :
    scalarStep word < 131072 ∧
    ∀ b < 17, (scalarStep word).testBit b =
      xor (word.testBit b) (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17)) := by
  let bitFn : Nat → Bool := fun b =>
    xor (word.testBit b) (!(word.testBit ((b + 1) % 17)) && word.testBit ((b + 2) % 17))
  have htake : ∀ m ≤ 17,
      let v := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      (∀ j, m ≤ j → v.testBit j = false) ∧ (∀ b < m, v.testBit b = bitFn b) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun j _ => by simp, fun b hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hrange : List.range (m + 1) = List.range m ++ [m] := List.range_succ
      dsimp only
      rw [hrange, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      set prev := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 j (by omega)]
        have h1 : m ≤ j := by omega
        have hgt : 1 ≤ j - m := by omega
        have hlt2 : (bitFn m).toNat < 2 ^ (j - m) := by
          have hle1 : (bitFn m).toNat ≤ 1 := by cases bitFn m <;> decide
          have hpow : 2 ≤ 2 ^ (j - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true h1, Bool.true_and, Nat.testBit_eq_false_of_lt hlt2]
        rfl
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b = m
        · subst hbm
          rw [hprev.1 b le_rfl, decide_eq_true le_rfl, Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
        · have hlt : b < m := by omega
          have hnot : ¬(m ≤ b) := by omega
          rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, hprev.2 b hlt]
  have hfull := htake 17 le_rfl
  refine ⟨?_, hfull.2⟩
  by_contra hge
  have h1 : 2 ^ 17 ≤ scalarStep word := by omega
  have hlog : 17 ≤ Nat.log2 (scalarStep word) := by
    have hne : scalarStep word ≠ 0 := by omega
    exact (Nat.le_log2 hne).mpr h1
  have htrue : (scalarStep word).testBit (Nat.log2 (scalarStep word)) = true :=
    Nat.testBit_log2 (by omega)
  have hfalse : (scalarStep word).testBit (Nat.log2 (scalarStep word)) = false :=
    hfull.1 _ hlog
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

lemma keyPlanes_rep : RepPlanesN 131072 keyPlanes id := by
  refine ⟨fun w hw => hw, ?_⟩
  intro w hw b hb
  interval_cases b <;> exact mkPlane_spec _ (by omega) w hw

lemma mkListPlanes_rep {l : List Nat} {N : Nat} (hlen : l.length = N)
    (hlt : ∀ i < N, l.getD i 0 < 131072) :
    RepPlanesN N (mkListPlanes l) (fun i => l.getD i 0) := by
  refine ⟨hlt, ?_⟩
  intro i hi b hb
  have hi' : i < l.length := by omega
  interval_cases b <;> exact mkListPlane_testBit _ l i hi'

lemma xor_rep {N : Nat} {a b : Planes17} {f g : Nat → Nat}
    (ha : RepPlanesN N a f) (hb : RepPlanesN N b g) :
    RepPlanesN N (a.xor b) (fun w => f w ^^^ g w) := by
  refine ⟨fun w hw => Nat.xor_lt_two_pow (n := 17) (ha.1 w hw) (hb.1 w hw), ?_⟩
  intro w hw i hi
  have hget : (a.xor b).get i = a.get i ^^^ b.get i := by interval_cases i <;> rfl
  rw [hget, Nat.testBit_xor, Nat.testBit_xor, ha.2 w hw i hi, hb.2 w hw i hi]

lemma xorConst_rep {N : Nat} {a : Planes17} {f : Nat → Nat} {c : Nat}
    (ha : RepPlanesN N a f) (hc : c < 131072) :
    RepPlanesN N (a.xorConst (allOnes N) c) (fun w => f w ^^^ c) := by
  refine ⟨fun w hw => Nat.xor_lt_two_pow (n := 17) (ha.1 w hw) hc, ?_⟩
  intro w hw i hi
  have hget : (a.xorConst (allOnes N) c).get i =
      if c.testBit i then a.get i ^^^ allOnes N else a.get i := by
    interval_cases i <;> rfl
  rw [hget, Nat.testBit_xor, ← ha.2 w hw i hi]
  cases hci : c.testBit i
  · simp
  · simp only [↓reduceIte, xor_allOnes_testBit hw]
    cases (a.get i).testBit w <;> rfl

lemma rot1_get (a : Planes17) (b : Nat) (hb : b < 17) :
    a.rot1.get b = a.get ((b + 16) % 17) := by
  interval_cases b <;> rfl

lemma rotIter_get (n : Nat) : ∀ (a : Planes17) (b : Nat), b < 17 →
    (a.rotIter n).get b = a.get ((b + 17 - n % 17) % 17) := by
  induction n with
  | zero =>
    intro a b hb
    simp [Planes17.rotIter, Nat.mod_eq_of_lt hb]
  | succ n ih =>
    intro a b hb
    dsimp only [Planes17.rotIter]
    rw [ih a.rot1 b hb, rot1_get a _ (Nat.mod_lt _ (by omega))]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hns : n % 17 < 17 := Nat.mod_lt n (by omega)
    by_cases h16 : n % 17 = 16
    · have hmod : (n + 1) % 17 = 0 := by rw [Nat.add_mod, h16]
      rw [hmod, h16]
      have heq : b + 17 - 16 + 16 = b + 17 := by omega
      rw [heq, Nat.sub_zero]
    · have hmod : (n + 1) % 17 = n % 17 + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 17), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have heq : b + 17 - n % 17 + 16 = (b + 17 - (n % 17 + 1)) + 17 := by omega
      rw [heq, Nat.add_mod_right]

lemma rotN_rep {N : Nat} {a : Planes17} {f : Nat → Nat} (ha : RepPlanesN N a f) (s : Nat) :
    RepPlanesN N (a.rotN s) (fun w => scalarRot s (f w)) := by
  refine ⟨fun w _ => scalarRot_lt s (f w), ?_⟩
  intro w hw b hb
  dsimp only [Planes17.rotN]
  rw [rotIter_get (s % 17) a b hb, Nat.mod_mod,
    ha.2 w hw _ (Nat.mod_lt _ (by omega)),
    scalarRot_testBit (ha.1 w hw) s b hb]

lemma step_rep {N : Nat} {a : Planes17} {f : Nat → Nat} (ha : RepPlanesN N a f) :
    RepPlanesN N (a.step (allOnes N)) (fun w => scalarStep (f w)) := by
  refine ⟨fun w _ => (scalarStep_spec (f w)).1, ?_⟩
  intro w hw b hb
  have hget : (a.step (allOnes N)).get b =
      a.get b ^^^ ((allOnes N ^^^ a.get ((b + 1) % 17)) &&& a.get ((b + 2) % 17)) := by
    interval_cases b <;> rfl
  rw [hget, Nat.testBit_xor, Nat.testBit_land, allOnes_xor_testBit hw,
    ha.2 w hw b hb, ha.2 w hw _ (Nat.mod_lt _ (by omega)),
    ha.2 w hw _ (Nat.mod_lt _ (by omega)), (scalarStep_spec (f w)).2 b hb]

lemma hiZero_spec {N : Nat} {a : Planes17} {f : Nat → Nat} (ha : RepPlanesN N a f) :
    ∀ w < N, (a.hiZero (allOnes N)).testBit w = true ↔ f w < 256 := by
  intro w hw
  dsimp only [Planes17.hiZero]
  rw [allOnes_xor_testBit hw]
  simp only [Nat.testBit_lor, Bool.not_eq_true', Bool.or_eq_false_iff]
  have hrep : ∀ b, 8 ≤ b → b < 17 → (a.get b).testBit w = (f w).testBit b :=
    fun b _ hb => ha.2 w hw b hb
  change (((((((((a.get 8).testBit w = false ∧ (a.get 9).testBit w = false) ∧
    (a.get 10).testBit w = false) ∧ (a.get 11).testBit w = false) ∧
    (a.get 12).testBit w = false) ∧ (a.get 13).testBit w = false) ∧
    (a.get 14).testBit w = false) ∧ (a.get 15).testBit w = false) ∧
    (a.get 16).testBit w = false) ↔ f w < 256
  rw [hrep 8 (by omega) (by omega), hrep 9 (by omega) (by omega),
      hrep 10 (by omega) (by omega), hrep 11 (by omega) (by omega),
      hrep 12 (by omega) (by omega), hrep 13 (by omega) (by omega),
      hrep 14 (by omega) (by omega), hrep 15 (by omega) (by omega),
      hrep 16 (by omega) (by omega)]
  constructor
  · intro h
    have hdiv0 : f w / 2 ^ 8 = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.zero_testBit, Nat.testBit_div_two_pow]
      by_cases hj : j < 9
      · interval_cases j
        · exact h.1.1.1.1.1.1.1.1
        · exact h.1.1.1.1.1.1.1.2
        · exact h.1.1.1.1.1.1.2
        · exact h.1.1.1.1.1.2
        · exact h.1.1.1.1.2
        · exact h.1.1.1.2
        · exact h.1.1.2
        · exact h.1.2
        · exact h.2
      · exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (show f w < 2 ^ 17 from ha.1 w hw)
            (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ j + 8)))
    exact (Nat.div_eq_zero_iff_lt (by omega : 0 < 2 ^ 8)).mp hdiv0
  · intro hlt
    have hall : ∀ b, 8 ≤ b → (f w).testBit b = false := fun b hb =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (show f w < 2 ^ 8 from hlt) (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hb))
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hall 8 (by omega), hall 9 (by omega)⟩, hall 10 (by omega)⟩,
      hall 11 (by omega)⟩, hall 12 (by omega)⟩, hall 13 (by omega)⟩,
      hall 14 (by omega)⟩, hall 15 (by omega)⟩, hall 16 (by omega)⟩

lemma outRound_rep {N : Nat} {w x : Planes17} {fw fx : Nat → Nat} (t : Nat)
    (hw : RepPlanesN N w fw) (hx : RepPlanesN N x fx) :
    RepPlanesN N (outRound (allOnes N) w x t) (fun k =>
      scalarStep (fx k ^^^ scalarRot 1 (fx k) ^^^ scalarRot 16 (fx k)) ^^^
      scalarRot (2 * t) (fw k) ^^^ (3 ^ (17 + (t + 1)) % 131072)) := by
  dsimp only [outRound]
  exact xorConst_rep
    (xor_rep (step_rep (xor_rep (xor_rep hx (rotN_rep hx 1)) (rotN_rep hx 16))) (rotN_rep hw (2 * t)))
    (Nat.mod_lt _ (by decide))

lemma outPlanes_rep {N : Nat} {w : Planes17} {fw : Nat → Nat} (hw : RepPlanesN N w fw) :
    RepPlanesN N (outPlanes (allOnes N) w) (fun k => scalarOut (fw k)) := by
  dsimp only [outPlanes]
  have hr0 := rotN_rep hw 1
  have hr1 := outRound_rep 0 hw hr0
  have hr2 := outRound_rep 1 hw hr1
  have hr3 := outRound_rep 2 hw hr2
  exact outRound_rep 3 hw hr3

lemma colRound_rep {N : Nat} {w st : Planes17} {fw fst : Nat → Nat} (j : Nat)
    (hw : RepPlanesN N w fw) (hst : RepPlanesN N st fst) :
    RepPlanesN N (colRound (allOnes N) w st j) (fun k =>
      scalarStep (fst k ^^^ scalarRot 2 (fst k) ^^^ scalarRot 15 (fst k)) ^^^
      scalarRot (3 * (j + 1) + 1) (fw k) ^^^ (3 ^ (17 + (4 + (j + 1))) % 131072)) := by
  dsimp only [colRound]
  exact xorConst_rep
    (xor_rep (step_rep (xor_rep (xor_rep hst (rotN_rep hst 2)) (rotN_rep hst 15)))
      (rotN_rep hw (3 * (j + 1) + 1)))
    (Nat.mod_lt _ (by decide))

lemma colMask_spec {N : Nat} {w : Planes17} {fw : Nat → Nat} (hw : RepPlanesN N w fw)
    {name : Nat} (hname : name < 131072) :
    ∀ i < N, (colMask (allOnes N) w name).testBit i = true ↔ scalarCol (fw i) name < 256 := by
  dsimp only [colMask]
  have hr0 := xorConst_rep (rotN_rep hw 3) hname
  have hr1 := colRound_rep 0 hw hr0
  have hr2 := colRound_rep 1 hw hr1
  have hr3 := colRound_rep 2 hw hr2
  have hr4 := colRound_rep 3 hw hr3
  exact hiZero_spec hr4

lemma colMaskVar_spec {N : Nat} {w nameP : Planes17} {fw fname : Nat → Nat}
    (hw : RepPlanesN N w fw) (hname : RepPlanesN N nameP fname) :
    ∀ i < N, (colMaskVar (allOnes N) w nameP).testBit i = true ↔ scalarCol (fw i) (fname i) < 256 := by
  dsimp only [colMaskVar]
  have hr0 := xor_rep (rotN_rep hw 3) hname
  have hr1 := colRound_rep 0 hw hr0
  have hr2 := colRound_rep 1 hw hr1
  have hr3 := colRound_rep 2 hw hr2
  have hr4 := colRound_rep 3 hw hr3
  exact hiZero_spec hr4

lemma hiEq_spec {N : Nat} {a : Planes17} {f : Nat → Nat} {v : Nat}
    (ha : RepPlanesN N a f) (hv : v < 512) (heq : a.hiEq (allOnes N) v = true) :
    ∀ i < N, f i >>> 8 = v := by
  dsimp only [Planes17.hiEq] at heq
  simp only [Bool.and_eq_true, beq_iff_eq] at heq
  have hbit : ∀ j < 9, a.get (8 + j) = if v.testBit j then allOnes N else 0 := by
    intro j hj
    interval_cases j
    · exact heq.1.1.1.1.1.1.1.1
    · exact heq.1.1.1.1.1.1.1.2
    · exact heq.1.1.1.1.1.1.2
    · exact heq.1.1.1.1.1.2
    · exact heq.1.1.1.1.2
    · exact heq.1.1.1.2
    · exact heq.1.1.2
    · exact heq.1.2
    · exact heq.2
  intro i hi
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight]
  by_cases hj : j < 9
  · rw [← ha.2 i hi (8 + j) (by omega), hbit j hj]
    cases hvj : v.testBit j
    · simp
    · simp only [↓reduceIte, allOnes_testBit, decide_eq_true hi]
  · have h1 := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (show f i < 2 ^ 17 from ha.1 i hi)
        (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 17 ≤ 8 + j)))
    have h2 := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (show v < 2 ^ 9 from hv)
        (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 9 ≤ j)))
    rw [h1, h2]

lemma mod2_succ_beq (n : Nat) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.add_mod, h]

lemma filter_len_mod2_xor (mask a b : Nat) : ∀ l : List Nat,
    ((l.filter (fun i => mask.testBit i && (a ^^^ b).testBit i)).length % 2 == 1) =
    xor ((l.filter (fun i => mask.testBit i && a.testBit i)).length % 2 == 1)
        ((l.filter (fun i => mask.testBit i && b.testBit i)).length % 2 == 1)
  | [] => rfl
  | x :: xs => by
    have ih := filter_len_mod2_xor mask a b xs
    simp only [List.filter_cons]
    rw [Nat.testBit_xor a b x]
    cases mask.testBit x <;> cases a.testBit x <;> cases b.testBit x <;>
      simp only [Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, mod2_succ_beq, ih]
    all_goals
      generalize ((xs.filter (fun i => mask.testBit i && a.testBit i)).length % 2 == 1) = u
      generalize ((xs.filter (fun i => mask.testBit i && b.testBit i)).length % 2 == 1) = v
      cases u <;> cases v <;> rfl

lemma scalarParity_xor (mask a b : Nat) :
    scalarParity mask (a ^^^ b) = xor (scalarParity mask a) (scalarParity mask b) :=
  filter_len_mod2_xor mask a b (List.range 17)

lemma lookup_triple_of_xor (f : Bool → Bool) (mask p0 p1 p2 p3 : Nat)
    (hxor : p1 ^^^ p2 ^^^ p3 = p0)
    (h0 : f (scalarParity mask p0) = true) :
    f (scalarParity mask p1) = true ∨ f (scalarParity mask p2) = true ∨ f (scalarParity mask p3) = true := by
  have hp : scalarParity mask p0 =
      xor (xor (scalarParity mask p1) (scalarParity mask p2)) (scalarParity mask p3) := by
    rw [← hxor, scalarParity_xor, scalarParity_xor]
  rw [hp] at h0
  cases h1 : scalarParity mask p1 <;> cases h2 : scalarParity mask p2 <;> cases h3 : scalarParity mask p3 <;>
    simp_all

end PEqualNP.Outside.L_lib_650_aux

open PEqualNP.Outside.L_lib_650_aux

theorem PEqualNP.Outside.L_lib_650 : (let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
let columnPass := fun (key name : Nat) =>
  ((List.range 4).foldl (fun state j =>
    step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
      rot (3 * (j + 1) + 1) key ^^^ (3 ^ (k + (4 + (j + 1))) % 2 ^ k))
    (rot 3 key ^^^ name)) < 2 ^ 8
let keys := List.range (2 ^ k)
let edge := fun (column : Nat) => ∃ w ∈ keys, output w = 0 ∧ columnPass w column
let parity := fun (mask word : Nat) =>
  ((List.range k).filter (fun i => mask.testBit i && word.testBit i)).length % 2 == 1
∀ (query : Nat → Fin (2 ^ k)) (lookup : Nat → Bool → Bool),
  let predicted := fun (column : Nat) =>
    ∃ w ∈ keys,
      (if w.testBit 2 then output w = 0
       else
         let probe := w ^^^ 12
         let y := output probe
         lookup y (parity (query y).val probe) = true) ∧ columnPass w column
  edge 0 ∧ (¬predicted 0 ∨ ∃ c : Fin (2 ^ k), ¬edge c.val ∧ predicted c.val)) := by
  intro k rot step output columnPass keys edge parity query lookup predicted
  have hg := checkGlobal_eq_true
  dsimp only [checkGlobal] at hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  have hz_len : zKeys.length = 249 := hg.1.1.1.1.1.1.1.1
  have hw0_len : w0Keys.length = 125 := hg.1.1.1.1.1.1.1.2
  have hc0_len : w0Cols.length = 125 := hg.1.1.1.1.1.1.2
  have hz_lt_all : zKeys.all (fun w => decide (w < 131072)) = true := hg.1.1.1.1.1.2
  have hw0_lt_all : w0Keys.all (fun w => decide (w < 131072)) = true := hg.1.1.1.1.2
  have hc0_neg_all : w0Cols.all (fun c => negCols.any (fun d => d == c)) = true := hg.1.1.1.2
  have houtZ_eq : outZMask = listMask zKeys := hg.1.1.2
  have hbit2_zero : bit2Mask &&& outZMask &&& col0Mask = 0 := hg.1.2
  have hnbit2_eq : nbit2Mask &&& col0Mask = (1 <<< 11632) ||| listMask w0Keys := hg.2
  have hnp := checkNegAndPairs_eq_true
  dsimp only [checkNegAndPairs] at hnp
  simp only [Bool.and_eq_true, beq_iff_eq] at hnp
  have hneg_all : negCols.all (fun c => decide (c < 131072) && (colMask onesZ zPlanes c == 0)) = true := hnp.1
  have hpairs_pass : colMaskVar onesW w0Planes c0Planes = onesW := hnp.2
  have hsp := checkSpecial_eq_true
  dsimp only [checkSpecial] at hsp
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hsp
  have hspC1_mem : spC1 ∈ negCols := mem_of_any_beq hsp.1.1.1.1.1.1.1.1.1.1.1.1
  have hspC2_mem : spC2 ∈ negCols := mem_of_any_beq hsp.1.1.1.1.1.1.1.1.1.1.1.2
  have hspC3_mem : spC3 ∈ negCols := mem_of_any_beq hsp.1.1.1.1.1.1.1.1.1.1.2
  have hspW1_lt : spW1 < 131072 := of_decide_eq_true hsp.1.1.1.1.1.1.1.1.1.2
  have hspW1_b2 : spW1.testBit 2 = false := hsp.1.1.1.1.1.1.1.1.2
  have hspW2_lt : spW2 < 131072 := of_decide_eq_true hsp.1.1.1.1.1.1.1.2
  have hspW2_b2 : spW2.testBit 2 = false := hsp.1.1.1.1.1.1.2
  have hspW3_lt : spW3 < 131072 := of_decide_eq_true hsp.1.1.1.1.1.2
  have hspW3_b2 : spW3.testBit 2 = false := hsp.1.1.1.1.2
  have hsp_out0 : ((outPlanes ones4 spKeyPlanes).hiZero ones4).testBit 0 = true := hsp.1.1.1.2
  have hsp_cols : colMaskVar ones4 spKeyPlanes spColPlanes = ones4 := hsp.1.1.2
  have hsp_pout : (outPlanes ones4 spProbePlanes).hiEq ones4 203 = true := hsp.1.2
  have hsp_xor : (spW1 ^^^ 12) ^^^ (spW2 ^^^ 12) ^^^ (spW3 ^^^ 12) = 11632 ^^^ 12 := hsp.2
  have houtRep : RepPlanesN 131072 (outPlanes (allOnes 131072) keyPlanes) scalarOut :=
    outPlanes_rep keyPlanes_rep
  have houtZ := hiZero_spec houtRep
  have hcol0 := colMask_spec keyPlanes_rep (name := 0) (by decide)
  have hout_eq_zero_iff : ∀ w < 131072, outZMask.testBit w = true ↔ output w = 0 := by
    intro w hw
    change ((outPlanes (allOnes 131072) keyPlanes).hiZero (allOnes 131072)).testBit w = true ↔
      scalarOut w >>> 8 = 0
    rw [houtZ w hw, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_eq_zero_iff_lt (by omega : 0 < 2 ^ 8)).symm
  have hbit2_tb : ∀ w < 131072, bit2Mask.testBit w = w.testBit 2 :=
    fun w hw => mkPlane_spec 2 (by omega) w hw
  have hnbit2_tb : ∀ w < 131072, nbit2Mask.testBit w = !(w.testBit 2) := fun w hw => by
    change (allOnes 131072 ^^^ bit2Mask).testBit w = !(w.testBit 2)
    rw [allOnes_xor_testBit hw, hbit2_tb w hw]
  have hzPlanes_rep : RepPlanesN 249 zPlanes (fun i => zKeys.getD i 0) :=
    mkListPlanes_rep hz_len (fun i hi => of_decide_eq_true (getD_prop_of_all hz_lt_all (by omega)))
  have hneg_spec : ∀ c ∈ negCols, c < 131072 ∧ ¬edge c := by
    intro c hc
    have hc_ok := List.all_eq_true.mp hneg_all c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc_ok
    have hc_lt : c < 131072 := of_decide_eq_true hc_ok.1
    refine ⟨hc_lt, ?_⟩
    rintro ⟨u, hu_mem, hou, hcu⟩
    have hu_lt : u < 131072 := List.mem_range.mp hu_mem
    have hu_tb : outZMask.testBit u = true := (hout_eq_zero_iff u hu_lt).mpr hou
    rw [houtZ_eq] at hu_tb
    have hu_in_z : u ∈ zKeys := mem_of_listMask_testBit zKeys u hu_tb
    rcases exists_getD_of_mem hu_in_z with ⟨i, hi_len, hi_eq⟩
    have hi_lt : i < 249 := by omega
    have hcm_tb : (colMask (allOnes 249) zPlanes c).testBit i = true := by
      refine (colMask_spec hzPlanes_rep hc_lt i hi_lt).mpr ?_
      rw [hi_eq]
      exact hcu
    have hzero : colMask (allOnes 249) zPlanes c = 0 := hc_ok.2
    rw [hzero, Nat.zero_testBit] at hcm_tb
    exact Bool.noConfusion hcm_tb
  have hw0Planes_rep : RepPlanesN 125 w0Planes (fun i => w0Keys.getD i 0) :=
    mkListPlanes_rep hw0_len (fun i hi => of_decide_eq_true (getD_prop_of_all hw0_lt_all (by omega)))
  have hc0Planes_rep : RepPlanesN 125 c0Planes (fun i => w0Cols.getD i 0) :=
    mkListPlanes_rep hc0_len (fun i hi =>
      (hneg_spec _ (mem_of_any_beq (getD_prop_of_all hc0_neg_all (by omega)))).1)
  have hspKey_rep : RepPlanesN 4 spKeyPlanes (fun i => spKeys.getD i 0) :=
    mkListPlanes_rep rfl (fun i hi => by interval_cases i <;> decide)
  have hspCol_rep : RepPlanesN 4 spColPlanes (fun i => spCols.getD i 0) :=
    mkListPlanes_rep rfl (fun i hi => by interval_cases i <;> decide)
  have hspProbe_rep : RepPlanesN 4 spProbePlanes (fun i => spProbes.getD i 0) :=
    mkListPlanes_rep rfl (fun i hi => by interval_cases i <;> decide)
  have hsp_col_all : ∀ i < 4, scalarCol (spKeys.getD i 0) (spCols.getD i 0) < 256 := by
    intro i hi
    have htb : (colMaskVar (allOnes 4) spKeyPlanes spColPlanes).testBit i = true := by
      change (colMaskVar ones4 spKeyPlanes spColPlanes).testBit i = true
      rw [hsp_cols]
      change (allOnes 4).testBit i = true
      rw [allOnes_testBit, decide_eq_true hi]
    exact (colMaskVar_spec hspKey_rep hspCol_rep i hi).mp htb
  have hsp_pout_all : ∀ i < 4, scalarOut (spProbes.getD i 0) >>> 8 = 203 :=
    hiEq_spec (outPlanes_rep hspProbe_rep) (by decide) hsp_pout
  have h11632_out_lt : scalarOut 11632 < 256 :=
    (hiZero_spec (outPlanes_rep hspKey_rep) 0 (by decide)).mp hsp_out0
  have h11632_col0 : scalarCol 11632 0 < 256 := hsp_col_all 0 (by decide)
  have hsp1_col : scalarCol spW1 spC1 < 256 := hsp_col_all 1 (by decide)
  have hsp2_col : scalarCol spW2 spC2 < 256 := hsp_col_all 2 (by decide)
  have hsp3_col : scalarCol spW3 spC3 < 256 := hsp_col_all 3 (by decide)
  have h11632_pout : output (11632 ^^^ 12) = 203 := hsp_pout_all 0 (by decide)
  have hsp1_pout : output (spW1 ^^^ 12) = 203 := hsp_pout_all 1 (by decide)
  have hsp2_pout : output (spW2 ^^^ 12) = 203 := hsp_pout_all 2 (by decide)
  have hsp3_pout : output (spW3 ^^^ 12) = 203 := hsp_pout_all 3 (by decide)
  have hedge0 : edge 0 := by
    refine ⟨11632, List.mem_range.mpr (by decide), ?_, h11632_col0⟩
    change scalarOut 11632 >>> 8 = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_eq_zero_iff_lt (by omega : 0 < 2 ^ 8)).mpr h11632_out_lt
  refine ⟨hedge0, ?_⟩
  by_cases hpred0 : predicted 0
  · right
    rcases hpred0 with ⟨w, hw_mem, hcond, hcw0⟩
    have hw_lt : w < 131072 := List.mem_range.mp hw_mem
    cases hb2 : w.testBit 2
    · have hm0_tb : (nbit2Mask &&& col0Mask).testBit w = true := by
        dsimp only [col0Mask, onesAll]
        rw [Nat.testBit_land, hnbit2_tb w hw_lt, hb2,
          (hcol0 w hw_lt).mpr hcw0]
        rfl
      rw [hnbit2_eq, Nat.testBit_lor, Bool.or_eq_true] at hm0_tb
      rcases hm0_tb with h11632 | hin_w0
      · have hw_eq : w = 11632 := eq_of_one_shiftLeft_testBit h11632
        subst hw_eq
        rw [hb2] at hcond
        simp only [Bool.false_eq_true, ↓reduceIte, h11632_pout] at hcond
        have htri := lookup_triple_of_xor (lookup 203) (query 203).val
          (11632 ^^^ 12) (spW1 ^^^ 12) (spW2 ^^^ 12) (spW3 ^^^ 12) hsp_xor hcond
        rcases htri with h1 | h2 | h3
        · have hc := hneg_spec spC1 hspC1_mem
          refine ⟨⟨spC1, hc.1⟩, hc.2, spW1, List.mem_range.mpr hspW1_lt, ?_, hsp1_col⟩
          rw [hspW1_b2]
          simp only [Bool.false_eq_true, ↓reduceIte, hsp1_pout]
          exact h1
        · have hc := hneg_spec spC2 hspC2_mem
          refine ⟨⟨spC2, hc.1⟩, hc.2, spW2, List.mem_range.mpr hspW2_lt, ?_, hsp2_col⟩
          rw [hspW2_b2]
          simp only [Bool.false_eq_true, ↓reduceIte, hsp2_pout]
          exact h2
        · have hc := hneg_spec spC3 hspC3_mem
          refine ⟨⟨spC3, hc.1⟩, hc.2, spW3, List.mem_range.mpr hspW3_lt, ?_, hsp3_col⟩
          rw [hspW3_b2]
          simp only [Bool.false_eq_true, ↓reduceIte, hsp3_pout]
          exact h3
      · have hw_in : w ∈ w0Keys := mem_of_listMask_testBit w0Keys w hin_w0
        rcases exists_getD_of_mem hw_in with ⟨i, hi_len, hi_eq⟩
        have hi_lt : i < 125 := by omega
        have hc_mem : w0Cols.getD i 0 ∈ negCols :=
          mem_of_any_beq (getD_prop_of_all hc0_neg_all (by omega))
        have hc := hneg_spec _ hc_mem
        have hpass : columnPass w (w0Cols.getD i 0) := by
          have htb : (colMaskVar (allOnes 125) w0Planes c0Planes).testBit i = true := by
            change (colMaskVar onesW w0Planes c0Planes).testBit i = true
            rw [hpairs_pass]
            change (allOnes 125).testBit i = true
            rw [allOnes_testBit, decide_eq_true hi_lt]
          have hsc := (colMaskVar_spec hw0Planes_rep hc0Planes_rep i hi_lt).mp htb
          rw [hi_eq] at hsc
          exact hsc
        exact ⟨⟨w0Cols.getD i 0, hc.1⟩, hc.2, w, hw_mem, hcond, hpass⟩
    · rw [hb2] at hcond
      simp only [↓reduceIte] at hcond
      have htb : (bit2Mask &&& outZMask &&& col0Mask).testBit w = true := by
        dsimp only [col0Mask, onesAll]
        rw [Nat.testBit_land, Nat.testBit_land, hbit2_tb w hw_lt, hb2,
          (hout_eq_zero_iff w hw_lt).mpr hcond, (hcol0 w hw_lt).mpr hcw0]
        rfl
      rw [hbit2_zero, Nat.zero_testBit] at htb
      exact Bool.noConfusion htb
  · exact Or.inl hpred0
