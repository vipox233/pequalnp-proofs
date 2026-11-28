import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50782_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def xs (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

lemma xs_len (t : Fin 6) : (xs t).length = 7 := by simp [xs]

def twoPow : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | 9 => 512
  | 10 => 1024
  | 11 => 2048
  | 12 => 4096
  | 13 => 8192
  | 14 => 16384
  | 15 => 32768
  | 16 => 65536
  | 17 => 131072
  | 18 => 262144
  | 19 => 524288
  | 20 => 1048576
  | 21 => 2097152
  | 22 => 4194304
  | 23 => 8388608
  | 24 => 16777216
  | 25 => 33554432
  | 26 => 67108864
  | 27 => 134217728
  | 28 => 268435456
  | 29 => 536870912
  | 30 => 1073741824
  | 31 => 2147483648
  | 32 => 4294967296
  | 33 => 8589934592
  | 34 => 17179869184
  | 35 => 34359738368
  | 36 => 68719476736
  | 37 => 137438953472
  | 38 => 274877906944
  | 39 => 549755813888
  | 40 => 1099511627776
  | 41 => 2199023255552
  | 42 => 4398046511104
  | 43 => 8796093022208
  | 44 => 17592186044416
  | 45 => 35184372088832
  | 46 => 70368744177664
  | 47 => 140737488355328
  | 48 => 281474976710656
  | 49 => 562949953421312
  | 50 => 1125899906842624
  | 51 => 2251799813685248
  | 52 => 4503599627370496
  | 53 => 9007199254740992
  | 54 => 18014398509481984
  | 55 => 36028797018963968
  | 56 => 72057594037927936
  | 57 => 144115188075855872
  | 58 => 288230376151711744
  | 59 => 576460752303423488
  | 60 => 1152921504606846976
  | 61 => 2305843009213693952
  | 62 => 4611686018427387904
  | 63 => 9223372036854775808
  | n => 2 ^ n

lemma twoPow_eq (n : ℕ) : twoPow n = 2 ^ n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> rfl

lemma testBit_or_twoPow (bank v w : ℕ) :
    (bank ||| twoPow v).testBit w = (bank.testBit w || decide (v = w)) := by
  rw [Nat.testBit_or, twoPow_eq, Nat.testBit_two_pow]

def toNat6 (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  b0.toNat + 2 * (b1.toNat + 2 * (b2.toNat + 2 * (b3.toNat + 2 * (b4.toNat + 2 * b5.toNat))))

lemma toNat6_lt (b0 b1 b2 b3 b4 b5 : Bool) : toNat6 b0 b1 b2 b3 b4 b5 < 64 := by
  have h : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
  have h0 := h b0; have h1 := h b1; have h2 := h b2
  have h3 := h b3; have h4 := h b4; have h5 := h b5
  unfold toNat6; omega

lemma toNat6_testBit (b0 b1 b2 b3 b4 b5 : Bool) (t : Fin 6) :
    (toNat6 b0 b1 b2 b3 b4 b5).testBit t.val =
      match t.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5 := by
  have hbit (k : ℕ) (x : Bool) (y : ℕ) :
      (x.toNat + 2 * y).testBit (k + 1) = y.testBit k := by
    cases x <;> rw [Nat.testBit_succ]
    · simp
    · change ((1 + 2 * y) / 2).testBit k = y.testBit k
      rw [show (1 + 2 * y) / 2 = y by omega]
  have hbit0 (x : Bool) (y : ℕ) : (x.toNat + 2 * y).testBit 0 = x := by
    cases x <;> simp [Nat.testBit_zero]
  rcases (by omega : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 5) with
    h | h | h | h | h | h <;> rw [h] <;> unfold toNat6
  · exact hbit0 _ _
  · rw [hbit 0]; exact hbit0 _ _
  · rw [hbit 1, hbit 0]; exact hbit0 _ _
  · rw [hbit 2, hbit 1, hbit 0]; exact hbit0 _ _
  · rw [hbit 3, hbit 2, hbit 1, hbit 0]; exact hbit0 _ _
  · rw [hbit 4, hbit 3, hbit 2, hbit 1, hbit 0]; cases b5 <;> rfl

lemma toNat6_testBit_ge (b0 b1 b2 b3 b4 b5 : Bool) (k : ℕ) (hk : 6 ≤ k) :
    (toNat6 b0 b1 b2 b3 b4 b5).testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have hlt := toNat6_lt b0 b1 b2 b3 b4 b5
  have hp : 64 ≤ 2 ^ k := by
    calc 64 = 2 ^ 6 := by decide
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  omega

lemma toNat6_and (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    toNat6 (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) =
      toNat6 a0 a1 a2 a3 a4 a5 &&& toNat6 b0 b1 b2 b3 b4 b5 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 6
  · rw [toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩, toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩,
      toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩]
    rcases k with _ | _ | _ | _ | _ | _ | k <;> simp_all
  · have hk' : 6 ≤ k := by omega
    rw [toNat6_testBit_ge _ _ _ _ _ _ k hk', toNat6_testBit_ge _ _ _ _ _ _ k hk',
      toNat6_testBit_ge _ _ _ _ _ _ k hk']
    rfl

lemma toNat6_or (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    toNat6 (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) =
      toNat6 a0 a1 a2 a3 a4 a5 ||| toNat6 b0 b1 b2 b3 b4 b5 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or]
  by_cases hk : k < 6
  · rw [toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩, toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩,
      toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩]
    rcases k with _ | _ | _ | _ | _ | _ | k <;> simp_all
  · have hk' : 6 ≤ k := by omega
    rw [toNat6_testBit_ge _ _ _ _ _ _ k hk', toNat6_testBit_ge _ _ _ _ _ _ k hk',
      toNat6_testBit_ge _ _ _ _ _ _ k hk']
    rfl

lemma toNat6_not (a0 a1 a2 a3 a4 a5 : Bool) :
    toNat6 (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) = 63 ^^^ toNat6 a0 a1 a2 a3 a4 a5 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < 6
  · rw [toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩, toNat6_testBit _ _ _ _ _ _ ⟨k, hk⟩]
    rcases k with _ | _ | _ | _ | _ | _ | k
    · change (!a0) = (true ^^ a0); cases a0 <;> rfl
    · change (!a1) = (true ^^ a1); cases a1 <;> rfl
    · change (!a2) = (true ^^ a2); cases a2 <;> rfl
    · change (!a3) = (true ^^ a3); cases a3 <;> rfl
    · change (!a4) = (true ^^ a4); cases a4 <;> rfl
    · change (!a5) = (true ^^ a5); cases a5 <;> rfl
    · omega
  · have hk' : 6 ≤ k := by omega
    have h63 : (63 : ℕ).testBit k = false := by
      apply Nat.testBit_lt_two_pow
      have hp : 64 ≤ 2 ^ k := by
        calc 64 = 2 ^ 6 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk'
      omega
    rw [toNat6_testBit_ge _ _ _ _ _ _ k hk', toNat6_testBit_ge _ _ _ _ _ _ k hk', h63]
    rfl

def initBank : ℕ := 15060318633198616577

def masksOf (bank : ℕ) : List ℕ :=
  (List.range 64).filter (fun m => bank.testBit m)

lemma mem_masksOf {bank m : ℕ} : m ∈ masksOf bank ↔ m < 64 ∧ bank.testBit m = true := by
  simp [masksOf, List.mem_filter, List.mem_range]

def expandKey (key : ℕ) : List ℕ :=
  let bank := key / 4
  let nots := key % 4
  let ms := masksOf bank
  let notC :=
    if nots < 2 then
      ms.filterMap fun a =>
        let v := 63 ^^^ a
        if bank.testBit v then none else some ((bank ||| twoPow v) * 4 + (nots + 1))
    else []
  let andC :=
    ms.flatMap fun a =>
      ms.filterMap fun b =>
        if a < b then
          let v := a &&& b
          if bank.testBit v then none else some ((bank ||| twoPow v) * 4 + nots)
        else none
  let orC :=
    ms.flatMap fun a =>
      ms.filterMap fun b =>
        if a < b then
          let v := a ||| b
          if bank.testBit v then none else some ((bank ||| twoPow v) * 4 + nots)
        else none
  notC ++ andC ++ orC

inductive BTree where
  | leaf : BTree
  | node (key : ℕ) (dep : ℕ) (l r : BTree) : BTree

def lookupDepth : BTree → ℕ → Option ℕ
  | BTree.leaf, _ => none
  | BTree.node k d l r, q =>
    if q < k then lookupDepth l q
    else if k < q then lookupDepth r q
    else some d

def hasTarget (a b c key : ℕ) : Bool :=
  let bank := key / 4
  bank.testBit a && bank.testBit b && bank.testBit c

def hasTwoTargets (a b c bank : ℕ) : Bool :=
  decide ((if bank.testBit a then 1 else 0) + (if bank.testBit b then 1 else 0) +
    (if bank.testBit c then 1 else 0) ≥ 2)

def checkNode (T : BTree) (a b c k d : ℕ) : Bool :=
  let bank := k / 4
  let nots := k % 4
  nots ≤ 2 &&
  (bank &&& initBank == initBank) &&
  !hasTarget a b c k &&
  if d < 4 then
    (expandKey k).all fun ch =>
      match lookupDepth T ch with
      | some d' => decide (d' ≤ d + 1)
      | none => false
  else
    !hasTwoTargets a b c bank ||
    (expandKey k).all fun ch => !hasTarget a b c ch

def okTree (T : BTree) (a b c : ℕ) : BTree → Bool
  | BTree.leaf => true
  | BTree.node k d l r =>
    checkNode T a b c k d && okTree T a b c l && okTree T a b c r

def T4 : BTree := (BTree.node 60242118957724745733 4 (BTree.node 60241274670233420326 3 (BTree.node 60241274541451509814 4 (BTree.node 60241274532794615302 4 (BTree.node 60241274532794597414 2 (BTree.node 60241274532794466918 3 (BTree.node 60241274532794466821 1 (BTree.node 60241274532794466350 2 (BTree.node 60241274532794466317 1 (BTree.node 60241274532794466308 0 BTree.leaf BTree.leaf) (BTree.node 60241274532794466341 1 BTree.leaf BTree.leaf)) (BTree.node 60241274532794466366 3 (BTree.node 60241274532794466357 2 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274532794466870 3 (BTree.node 60241274532794466854 2 (BTree.node 60241274532794466830 2 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794466894 3 (BTree.node 60241274532794466885 2 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274532794467126 4 (BTree.node 60241274532794467077 2 (BTree.node 60241274532794467022 4 (BTree.node 60241274532794466934 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794467110 3 (BTree.node 60241274532794467086 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274532794467174 4 (BTree.node 60241274532794467150 4 (BTree.node 60241274532794467141 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794597390 2 (BTree.node 60241274532794597381 1 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241274532794600462 4 (BTree.node 60241274532794598414 3 (BTree.node 60241274532794598150 3 (BTree.node 60241274532794597894 2 (BTree.node 60241274532794597430 3 BTree.leaf BTree.leaf) (BTree.node 60241274532794597958 3 BTree.leaf BTree.leaf)) (BTree.node 60241274532794598405 2 (BTree.node 60241274532794598214 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274532794598918 3 (BTree.node 60241274532794598454 4 (BTree.node 60241274532794598438 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794599174 4 (BTree.node 60241274532794598982 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274532794614278 3 (BTree.node 60241274532794613774 3 (BTree.node 60241274532794613765 2 (BTree.node 60241274532794606630 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794613814 4 (BTree.node 60241274532794613798 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274532794614789 3 (BTree.node 60241274532794614534 4 (BTree.node 60241274532794614342 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794614822 4 (BTree.node 60241274532794614798 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60241274541384401734 4 (BTree.node 60241274532794679301 3 (BTree.node 60241274532794663494 4 (BTree.node 60241274532794662950 3 (BTree.node 60241274532794662917 2 (BTree.node 60241274532794646542 4 BTree.leaf BTree.leaf) (BTree.node 60241274532794662926 3 BTree.leaf BTree.leaf)) (BTree.node 60241274532794663430 3 (BTree.node 60241274532794662966 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274532794663950 4 (BTree.node 60241274532794663941 3 (BTree.node 60241274532794663686 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274532794664454 4 (BTree.node 60241274532794663974 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274541384400910 2 (BTree.node 60241274532794679814 4 (BTree.node 60241274532794679334 4 (BTree.node 60241274532794679310 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541384400901 1 (BTree.node 60241274532794680325 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274541384401414 2 (BTree.node 60241274541384400950 3 (BTree.node 60241274541384400934 2 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541384401670 3 (BTree.node 60241274541384401478 3 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241274541384663622 4 (BTree.node 60241274541384613894 4 (BTree.node 60241274541384549382 4 (BTree.node 60241274541384532998 3 (BTree.node 60241274541384531974 2 BTree.leaf BTree.leaf) (BTree.node 60241274541384548358 3 BTree.leaf BTree.leaf)) (BTree.node 60241274541384598534 4 (BTree.node 60241274541384597510 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274541384663078 3 (BTree.node 60241274541384663054 3 (BTree.node 60241274541384663045 2 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541384663558 3 (BTree.node 60241274541384663094 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274541385187342 4 (BTree.node 60241274541384795142 4 (BTree.node 60241274541384794118 3 (BTree.node 60241274541384663814 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541384859654 4 (BTree.node 60241274541384810502 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274541451509765 2 (BTree.node 60241274541418217990 4 (BTree.node 60241274541386760230 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541451509798 3 (BTree.node 60241274541451509774 3 BTree.leaf BTree.leaf) BTree.leaf)))))) (BTree.node 60241274545679630350 4 (BTree.node 60241274542458339334 4 (BTree.node 60241274541585727502 4 (BTree.node 60241274541451706374 4 (BTree.node 60241274541451640838 3 (BTree.node 60241274541451510342 4 (BTree.node 60241274541451510278 3 BTree.leaf BTree.leaf) (BTree.node 60241274541451510534 4 BTree.leaf BTree.leaf)) (BTree.node 60241274541451657222 4 (BTree.node 60241274541451641862 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274541451771942 4 (BTree.node 60241274541451771918 4 (BTree.node 60241274541451771909 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274541451902982 4 (BTree.node 60241274541451772422 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274542458143238 3 (BTree.node 60241274542458142734 3 (BTree.node 60241274542458142725 2 (BTree.node 60241274541988380710 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274542458142774 4 (BTree.node 60241274542458142758 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274542458273798 3 (BTree.node 60241274542458143494 4 (BTree.node 60241274542458143302 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274542458290182 4 (BTree.node 60241274542458274822 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241274545679368197 2 (BTree.node 60241274542525251598 4 (BTree.node 60241274542458405382 4 (BTree.node 60241274542458404878 4 (BTree.node 60241274542458404869 3 BTree.leaf BTree.leaf) (BTree.node 60241274542458404902 4 BTree.leaf BTree.leaf)) (BTree.node 60241274542525251589 3 (BTree.node 60241274542458535942 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274542525382662 4 (BTree.node 60241274542525252102 4 (BTree.node 60241274542525251622 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274544605626382 4 (BTree.node 60241274542525513733 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274545679368966 4 (BTree.node 60241274545679368246 4 (BTree.node 60241274545679368230 3 (BTree.node 60241274545679368206 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274545679368774 4 (BTree.node 60241274545679368710 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274545679515654 4 (BTree.node 60241274545679500294 4 (BTree.node 60241274545679499270 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274545679630341 3 (BTree.node 60241274545679564806 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60241274567154352142 4 (BTree.node 60241274546753110534 4 (BTree.node 60241274545746477574 4 (BTree.node 60241274545746477061 3 (BTree.node 60241274545679630854 4 (BTree.node 60241274545679630374 4 BTree.leaf BTree.leaf) (BTree.node 60241274545679761414 4 BTree.leaf BTree.leaf)) (BTree.node 60241274545746477094 4 (BTree.node 60241274545746477070 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274546753110021 3 (BTree.node 60241274545746739205 4 (BTree.node 60241274545746608134 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274546753110054 4 (BTree.node 60241274546753110030 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274567154204734 4 (BTree.node 60241274546820218885 4 (BTree.node 60241274546753372165 4 (BTree.node 60241274546753241094 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274567154204718 3 (BTree.node 60241274567154204685 2 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274567154205454 4 (BTree.node 60241274567154205262 4 (BTree.node 60241274567154205198 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274567154336782 4 (BTree.node 60241274567154335758 3 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241274580106215430 4 (BTree.node 60241274575744401422 4 (BTree.node 60241274571516280846 4 (BTree.node 60241274571449171982 3 (BTree.node 60241274567154401294 4 BTree.leaf BTree.leaf) (BTree.node 60241274571449434126 4 BTree.leaf BTree.leaf)) (BTree.node 60241274575744139278 3 (BTree.node 60241274572522913806 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274580039106566 3 (BTree.node 60241274576817881102 4 (BTree.node 60241274575811248142 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274580039368710 4 (BTree.node 60241274580039106574 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274603661426742 4 (BTree.node 60241274601513943102 4 (BTree.node 60241274601513943093 3 (BTree.node 60241274581112848390 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274601514074166 4 (BTree.node 60241274601513943606 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274670233419822 3 (BTree.node 60241274670233419813 2 (BTree.node 60241274610103877686 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274670233419838 4 (BTree.node 60241274670233419829 3 BTree.leaf BTree.leaf) BTree.leaf))))))) (BTree.node 60241277839919284742 4 (BTree.node 60241276731817722406 3 (BTree.node 60241274738952896558 4 (BTree.node 60241274678823354406 3 (BTree.node 60241274670233567270 4 (BTree.node 60241274670233550886 3 (BTree.node 60241274670233420390 4 (BTree.node 60241274670233420342 4 BTree.leaf BTree.leaf) (BTree.node 60241274670233420582 4 BTree.leaf BTree.leaf)) (BTree.node 60241274670233551910 4 (BTree.node 60241274670233550902 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274671307161654 4 (BTree.node 60241274671307161638 3 (BTree.node 60241274670233616422 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274671374270502 4 (BTree.node 60241274671307423782 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241274679897358342 4 (BTree.node 60241274678890463270 4 (BTree.node 60241274678823616550 4 (BTree.node 60241274678823354422 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274679897096230 4 (BTree.node 60241274679897096198 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274684192063494 4 (BTree.node 60241274683118321702 4 (BTree.node 60241274679964205062 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274738952896549 3 (BTree.node 60241274704593158190 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241274808209244742 4 (BTree.node 60241274748616572934 4 (BTree.node 60241274740026638374 4 (BTree.node 60241274738952897062 4 (BTree.node 60241274738952896565 4 BTree.leaf BTree.leaf) (BTree.node 60241274738953027622 4 BTree.leaf BTree.leaf)) (BTree.node 60241274747542831142 4 (BTree.node 60241274741100380198 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241274807672373862 4 (BTree.node 60241274807672373838 4 (BTree.node 60241274807672373829 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241274807672504902 4 (BTree.node 60241274807672374085 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241275632306225926 4 (BTree.node 60241275632306094862 4 (BTree.node 60241275632306094853 3 (BTree.node 60241274816262308422 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241275632306094917 4 (BTree.node 60241275632306094886 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241275907184001797 4 (BTree.node 60241275640896029446 4 (BTree.node 60241275632440312582 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241276731817722382 3 (BTree.node 60241276731817722373 2 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60241276740475027462 4 (BTree.node 60241276731817869830 4 (BTree.node 60241276731817722662 4 (BTree.node 60241276731817722470 4 (BTree.node 60241276731817722437 3 (BTree.node 60241276731817722422 4 BTree.leaf BTree.leaf) (BTree.node 60241276731817722446 4 BTree.leaf BTree.leaf)) (BTree.node 60241276731817722638 4 (BTree.node 60241276731817722629 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241276731817853510 4 (BTree.node 60241276731817853446 3 (BTree.node 60241276731817722693 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241276731817854470 4 (BTree.node 60241276731817853702 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241276740407656966 3 (BTree.node 60241276731884831302 4 (BTree.node 60241276731884831238 3 (BTree.node 60241276731817918982 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241276731885093382 4 (BTree.node 60241276731884831494 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241276740407919110 4 (BTree.node 60241276740407657222 4 (BTree.node 60241276740407657030 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241276740474765830 4 (BTree.node 60241276740474765318 3 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241277006762738182 4 (BTree.node 60241277006695629317 3 (BTree.node 60241276744769732614 4 (BTree.node 60241276741548507142 4 (BTree.node 60241276741481398790 4 BTree.leaf BTree.leaf) (BTree.node 60241276744702624262 4 BTree.leaf BTree.leaf)) (BTree.node 60241276869256675878 4 (BTree.node 60241276766177460750 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241277006695629381 4 (BTree.node 60241277006695629350 4 (BTree.node 60241277006695629326 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241277006695760390 4 (BTree.node 60241277006695629573 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241277831329350182 4 (BTree.node 60241277015352672262 4 (BTree.node 60241277015285563910 4 (BTree.node 60241277007232500230 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241277831329350158 4 (BTree.node 60241277831329350149 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241277831329481222 4 (BTree.node 60241277831329350405 4 (BTree.node 60241277831329350213 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241277831463567878 4 (BTree.node 60241277831396459014 4 BTree.leaf BTree.leaf) BTree.leaf)))))) (BTree.node 60241837482748085253 4 (BTree.node 60241556007771389957 4 (BTree.node 60241344901538791462 4 (BTree.node 60241278930841125893 4 (BTree.node 60241278930841109518 4 (BTree.node 60241278106207257093 4 (BTree.node 60241277839986393094 4 BTree.leaf BTree.leaf) (BTree.node 60241278930841109509 3 BTree.leaf BTree.leaf)) (BTree.node 60241278930841110022 4 (BTree.node 60241278930841109542 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241278939431044102 4 (BTree.node 60241278930874663942 4 (BTree.node 60241278930841175045 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241344901538791438 4 (BTree.node 60241344901538791429 3 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241349299585302533 4 (BTree.node 60241344901538856965 4 (BTree.node 60241344901538792453 4 (BTree.node 60241344901538791942 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241344910128726022 4 (BTree.node 60241344901540888582 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241556007771373606 4 (BTree.node 60241556007771373582 4 (BTree.node 60241556007771373573 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241556007771374597 4 (BTree.node 60241556007771374086 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241837482748019726 4 (BTree.node 60241837482748018726 3 (BTree.node 60241626376515551237 4 (BTree.node 60241556016361308166 4 (BTree.node 60241556007771897862 4 BTree.leaf BTree.leaf) (BTree.node 60241560405817884677 4 BTree.leaf BTree.leaf)) (BTree.node 60241837482748018702 3 (BTree.node 60241837482748018693 2 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241837482748019270 4 (BTree.node 60241837482748019206 3 (BTree.node 60241837482748018742 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241837482748019717 3 (BTree.node 60241837482748019462 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241837482748035590 4 (BTree.node 60241837482748035077 3 (BTree.node 60241837482748020230 4 (BTree.node 60241837482748019750 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241837482748035110 4 (BTree.node 60241837482748035086 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241837482748084238 4 (BTree.node 60241837482748084229 3 (BTree.node 60241837482748036101 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241837482748084742 4 (BTree.node 60241837482748084262 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60241841880794530821 4 (BTree.node 60241837491405193222 4 (BTree.node 60241837491337954310 4 (BTree.node 60241837482748297222 4 (BTree.node 60241837482748280838 3 (BTree.node 60241837482748100613 4 BTree.leaf BTree.leaf) (BTree.node 60241837482748281862 4 BTree.leaf BTree.leaf)) (BTree.node 60241837491337953286 3 (BTree.node 60241837482748346374 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241837491338084358 3 (BTree.node 60241837491338018822 4 (BTree.node 60241837491337969670 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241837491405062150 4 (BTree.node 60241837491338215430 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241837620186972198 4 (BTree.node 60241837495632920582 4 (BTree.node 60241837492411826182 4 (BTree.node 60241837492411695110 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241837517107757070 4 (BTree.node 60241837495633051654 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241841880794529806 4 (BTree.node 60241841880794529797 3 (BTree.node 60241839681771274758 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241841880794530310 4 (BTree.node 60241841880794529830 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60241907851492212741 4 (BTree.node 60241841889384595462 4 (BTree.node 60241841880794791942 4 (BTree.node 60241841880794595333 4 (BTree.node 60241841880794546181 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241841889384464390 4 (BTree.node 60241841880828084230 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60241907851492196390 4 (BTree.node 60241907851492196366 4 (BTree.node 60241907851492196357 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241907851492197381 4 (BTree.node 60241907851492196870 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60241912249538707461 4 (BTree.node 60241907851494293510 4 (BTree.node 60241907851492458502 4 (BTree.node 60241907851492261893 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60241907860082262022 4 (BTree.node 60241907860082130950 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60242118957724729382 4 (BTree.node 60242118957724729358 4 (BTree.node 60242118957724729349 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60242118957724730373 4 (BTree.node 60242118957724729862 4 BTree.leaf BTree.leaf) BTree.leaf)))))))) (BTree.node 60457447314908381702 4 (BTree.node 60254785331676578342 4 (BTree.node 60245778201141313589 4 (BTree.node 60243526341198348302 4 (BTree.node 60243526332608152334 4 (BTree.node 60242189326468907013 4 (BTree.node 60242118966314663942 4 (BTree.node 60242118957724991494 4 (BTree.node 60242118957724794885 4 BTree.leaf BTree.leaf) (BTree.node 60242118957725253638 4 BTree.leaf BTree.leaf)) (BTree.node 60242123355771240453 4 (BTree.node 60242118966314795014 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60243526332608151614 4 (BTree.node 60243526332608151598 3 (BTree.node 60243526332608151565 2 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60243526332608152142 4 (BTree.node 60243526332608152078 3 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60243526332608299022 4 (BTree.node 60243526332608233486 4 (BTree.node 60243526332608218126 4 (BTree.node 60243526332608217102 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60243526332608283662 4 (BTree.node 60243526332608282638 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60243526332608349190 4 (BTree.node 60243526332608348174 4 (BTree.node 60243526332608348166 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60243526341198086158 3 (BTree.node 60243526332608364550 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60243526470047105070 4 (BTree.node 60243526366967890446 4 (BTree.node 60243526345493053454 4 (BTree.node 60243526341265195022 4 (BTree.node 60243526341198610446 4 BTree.leaf BTree.leaf) (BTree.node 60243526342271827982 4 BTree.leaf BTree.leaf)) (BTree.node 60243526366967889966 4 (BTree.node 60243526366967889933 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60243526371262857230 4 (BTree.node 60243526366968021006 4 (BTree.node 60243526366967955470 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60243526379852791814 4 (BTree.node 60243526375557824526 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60245778132421836853 3 (BTree.node 60243807807585058822 4 (BTree.node 60243807807584927758 4 (BTree.node 60243528531631407630 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60244089282561769478 4 (BTree.node 60244089282561703950 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60245778132421869622 4 (BTree.node 60245778132421837366 4 (BTree.node 60245778132421836862 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60245778141011771446 4 (BTree.node 60245778132421967926 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60250281740641239078 4 (BTree.node 60250281732049224742 4 (BTree.node 60250281732049207846 3 (BTree.node 60250281732049207342 3 (BTree.node 60245778338580267045 4 (BTree.node 60245778269860790325 4 BTree.leaf BTree.leaf) (BTree.node 60250281732049207333 2 BTree.leaf BTree.leaf)) (BTree.node 60250281732049207358 4 (BTree.node 60250281732049207349 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60250281732049208102 4 (BTree.node 60250281732049207910 4 (BTree.node 60250281732049207862 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60250281732049223734 4 (BTree.node 60250281732049223718 3 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60250281732049355782 4 (BTree.node 60250281732049339430 4 (BTree.node 60250281732049338422 4 (BTree.node 60250281732049338406 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60250281732049354790 4 (BTree.node 60250281732049354758 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60250281740639141926 3 (BTree.node 60250281732049420294 4 (BTree.node 60250281732049403942 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60250281740639404070 4 (BTree.node 60250281740639141942 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60250281878078095398 4 (BTree.node 60250281869488160814 4 (BTree.node 60250281766408945710 4 (BTree.node 60250281741712883750 4 (BTree.node 60250281740706250790 4 BTree.leaf BTree.leaf) (BTree.node 60250281744934109222 4 BTree.leaf BTree.leaf)) (BTree.node 60250281869488160805 3 (BTree.node 60250281800768684085 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60250281869488177190 4 (BTree.node 60250281869488161318 4 (BTree.node 60250281869488160821 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60250281870561902630 4 (BTree.node 60250281869488291878 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60250844682002759718 4 (BTree.node 60250283931072463398 4 (BTree.node 60250281938207637541 4 (BTree.node 60250281879151837190 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60250352100793532422 4 (BTree.node 60250352100793401382 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60254785331676577829 3 (BTree.node 60252533531862892590 4 (BTree.node 60250844682002776070 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60254785331676577845 4 (BTree.node 60254785331676577838 4 BTree.leaf BTree.leaf) BTree.leaf)))))) (BTree.node 60385389720870519814 4 (BTree.node 60313334325855650565 4 (BTree.node 60259288939893883462 4 (BTree.node 60259288931303948869 3 (BTree.node 60254785331676725254 4 (BTree.node 60254785331676610598 4 (BTree.node 60254785331676594214 4 BTree.leaf BTree.leaf) (BTree.node 60254785331676708902 4 BTree.leaf BTree.leaf)) (BTree.node 60254785469115531301 4 (BTree.node 60254785340266512422 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60259288931303949125 4 (BTree.node 60259288931303948902 4 (BTree.node 60259288931303948878 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60259288931304079942 4 (BTree.node 60259288931303957062 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60313332126832395046 4 (BTree.node 60259291405205111301 4 (BTree.node 60259291130327204421 4 (BTree.node 60259289206181855813 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60313332126832395022 4 (BTree.node 60313332126832395013 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60313332126832526086 4 (BTree.node 60313332126832397062 4 (BTree.node 60313332126832395077 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60313333226344022789 4 (BTree.node 60313332135422329606 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60385389720870323013 4 (BTree.node 60385389720870322757 3 (BTree.node 60385389720870322702 3 (BTree.node 60331346525341876997 4 (BTree.node 60313335425367278085 4 BTree.leaf BTree.leaf) (BTree.node 60385389720870322693 2 BTree.leaf BTree.leaf)) (BTree.node 60385389720870322742 4 (BTree.node 60385389720870322726 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60385389720870322949 3 (BTree.node 60385389720870322790 4 (BTree.node 60385389720870322766 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385389720870322982 4 (BTree.node 60385389720870322958 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60385389720870454022 4 (BTree.node 60385389720870323974 4 (BTree.node 60385389720870323782 4 (BTree.node 60385389720870323718 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385389720870453830 4 (BTree.node 60385389720870453766 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60385389720870470150 4 (BTree.node 60385389720870454790 4 (BTree.node 60385389720870454278 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385389720870519302 4 (BTree.node 60385389720870470662 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 60385394118916834822 4 (BTree.node 60385391919893578245 3 (BTree.node 60385389730533999110 4 (BTree.node 60385389729460519430 4 (BTree.node 60385389729460257350 4 (BTree.node 60385389729460257286 3 BTree.leaf BTree.leaf) (BTree.node 60385389729460257542 4 BTree.leaf BTree.leaf)) (BTree.node 60385389729527366150 4 (BTree.node 60385389729493811718 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60385389858309276198 4 (BTree.node 60385389755230061070 4 (BTree.node 60385389733755224582 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385390820381950725 4 (BTree.node 60385389995748229701 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60385391919893709318 4 (BTree.node 60385391919893578309 4 (BTree.node 60385391919893578278 4 (BTree.node 60385391919893578254 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385391919893579270 4 (BTree.node 60385391919893578501 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60385391928550621190 4 (BTree.node 60385391928483512838 4 (BTree.node 60385391919960687110 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60385393019405206021 4 (BTree.node 60385392194771485189 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60403404119379812870 4 (BTree.node 60403404119379804677 3 (BTree.node 60385952670823875590 4 (BTree.node 60385952670823875078 4 (BTree.node 60385394118916965382 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60394396920125063718 4 (BTree.node 60387641520684007950 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60403404119379804741 4 (BTree.node 60403404119379804710 4 (BTree.node 60403404119379804686 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60403404119379805702 4 (BTree.node 60403404119379804933 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60457447314908250638 4 (BTree.node 60403404127969739270 4 (BTree.node 60403404119379936262 4 (BTree.node 60403404119379935750 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60457447314908250629 3 (BTree.node 60403406318403060229 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60457447314908250885 4 (BTree.node 60457447314908250693 4 (BTree.node 60457447314908250662 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60457447314908252678 4 (BTree.node 60457447314908251654 4 BTree.leaf BTree.leaf) BTree.leaf))))))) (BTree.node 62547117688037048358 4 (BTree.node 60889792879135817998 4 (BTree.node 60817735297982791694 4 (BTree.node 60817735285097890574 4 (BTree.node 60817735285097889854 4 (BTree.node 60475461713417732613 4 (BTree.node 60457447323498185222 4 (BTree.node 60457447314908382214 4 BTree.leaf BTree.leaf) (BTree.node 60457449513931506181 4 BTree.leaf BTree.leaf)) (BTree.node 60817735285097889838 3 (BTree.node 60817735285097889805 2 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60817735285097890318 3 (BTree.node 60817735285097890126 4 (BTree.node 60817735285097890062 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60817735285097890566 3 (BTree.node 60817735285097890382 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60817735285098086414 4 (BTree.node 60817735285098021902 4 (BTree.node 60817735285098020878 3 (BTree.node 60817735285097890630 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60817735285098037262 4 (BTree.node 60817735285098022926 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60817735293754933262 4 (BTree.node 60817735293688086542 4 (BTree.node 60817735293687824398 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60817735294761566222 4 (BTree.node 60817735293822042126 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 60817737484121146118 4 (BTree.node 60817735328047562766 4 (BTree.node 60817735319457628686 4 (BTree.node 60817735319457628206 4 (BTree.node 60817735319457628173 3 BTree.leaf BTree.leaf) (BTree.node 60817735319457628430 4 BTree.leaf BTree.leaf)) (BTree.node 60817735323752595470 4 (BTree.node 60817735319457759246 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60817736384609517838 4 (BTree.node 60817735422536843310 4 (BTree.node 60817735332342530054 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60817737484121145870 4 (BTree.node 60817736384609518342 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 60819987084911640590 4 (BTree.node 60819987084911575086 4 (BTree.node 60819987084911575053 3 (BTree.node 60818298235051442190 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60819987084911575566 4 (BTree.node 60819987084911575310 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 60819987093501509646 4 (BTree.node 60819987084911771654 4 (BTree.node 60819987084911706126 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 60826742484352630830 4 (BTree.node 60819987119271313421 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 62547117542008160870 4 (BTree.node 61398699637028683829 4 (BTree.node 61394196037401313846 4 (BTree.node 61394196037401313333 3 (BTree.node 60961850473173746190 4 (BTree.node 60889792879135818502 4 BTree.leaf BTree.leaf) (BTree.node 60961850473173746438 4 BTree.leaf BTree.leaf)) (BTree.node 61394196037401313462 4 (BTree.node 61394196037401313342 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 61394196106120790069 4 (BTree.node 61394196045991247926 4 (BTree.node 61394196037401444406 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 61394196243559743525 4 (BTree.node 61394196174840266805 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 62547117542008160318 4 (BTree.node 62547117542008160293 2 (BTree.node 61407706836283424805 4 (BTree.node 61403203236656054325 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62547117542008160309 3 (BTree.node 62547117542008160302 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 62547117542008160806 3 (BTree.node 62547117542008160374 4 (BTree.node 62547117542008160358 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62547117542008160838 3 (BTree.node 62547117542008160822 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 62547117551134965798 4 (BTree.node 62547117542008307750 4 (BTree.node 62547117542008291382 4 (BTree.node 62547117542008161094 4 (BTree.node 62547117542008161062 4 BTree.leaf BTree.leaf) (BTree.node 62547117542008291366 3 BTree.leaf BTree.leaf)) (BTree.node 62547117542008299558 4 (BTree.node 62547117542008292390 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 62547117550598094902 4 (BTree.node 62547117550598094886 3 (BTree.node 62547117542008356902 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62547117550665203750 4 (BTree.node 62547117550598357030 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 62547117679447113774 4 (BTree.node 62547117576367898670 4 (BTree.node 62547117554893062182 4 (BTree.node 62547117551671836710 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62547117679447113765 3 (BTree.node 62547117610727637045 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 62547117679447114278 4 (BTree.node 62547117679447113830 4 (BTree.node 62547117679447113781 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62547117680520855590 4 (BTree.node 62547117679447244838 4 BTree.leaf BTree.leaf) BTree.leaf)))))) (BTree.node 69464646569649438734 4 (BTree.node 63123578294311583790 4 (BTree.node 62556124741262901350 4 (BTree.node 62547680491961712678 4 (BTree.node 62547117816886067782 4 (BTree.node 62547117748166590501 4 (BTree.node 62547117689110790150 4 BTree.leaf BTree.leaf) (BTree.node 62547117816886067302 4 BTree.leaf BTree.leaf)) (BTree.node 62547119741031416390 4 (BTree.node 62547119741031416358 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 62556124741262901285 3 (BTree.node 62551621141635530805 4 (BTree.node 62549369341821845550 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62556124741262901301 4 (BTree.node 62556124741262901294 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 62556124878701854757 4 (BTree.node 62556124741263032358 4 (BTree.node 62556124741262917670 4 (BTree.node 62556124741262901798 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62556124749852835878 4 (BTree.node 62556124741263048710 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 62565131940517642822 4 (BTree.node 62565131940517642342 4 (BTree.node 62560628340890271781 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 62691232730084016710 4 (BTree.node 62691232730084016678 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 69464646569649242142 3 (BTree.node 63700039046615007814 4 (BTree.node 63700039046615007334 4 (BTree.node 63700039046615007278 4 (BTree.node 63700039046615007269 3 BTree.leaf BTree.leaf) (BTree.node 63700039046615007285 4 BTree.leaf BTree.leaf)) (BTree.node 63700039046615007782 4 (BTree.node 63700039046615007398 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 63700039184053960741 4 (BTree.node 63700039055204941862 4 (BTree.node 63700039046615138342 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69464646569649242125 2 (BTree.node 63709046245869748261 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 69464646569649242766 4 (BTree.node 69464646569649242174 4 (BTree.node 69464646569649242166 3 (BTree.node 69464646569649242158 3 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69464646569649242702 4 (BTree.node 69464646569649242638 3 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 69464646569649374222 4 (BTree.node 69464646569649373198 3 (BTree.node 69464646569649242894 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69464646569649405966 4 (BTree.node 69464646569649389582 4 BTree.leaf BTree.leaf) BTree.leaf))))) (BTree.node 69466898369462992910 4 (BTree.node 69464646612598915086 4 (BTree.node 69464646604008980493 3 (BTree.node 69464646579312918542 4 (BTree.node 69464646578239438862 4 (BTree.node 69464646578239176718 3 BTree.leaf BTree.leaf) (BTree.node 69464646578306285582 4 BTree.leaf BTree.leaf)) (BTree.node 69464646582534144014 4 (BTree.node 69464646580386660366 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 69464646604008981006 4 (BTree.node 69464646604008980526 4 (BTree.node 69464646604008980510 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69464646608303947790 4 (BTree.node 69464646604009111566 4 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 69464648768672498190 4 (BTree.node 69464646638368718902 4 (BTree.node 69464646638368718878 4 (BTree.node 69464646616893882374 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69464646707088195638 4 (BTree.node 69464646707088195630 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 69466898369462927390 4 (BTree.node 69466898369462927373 3 (BTree.node 69465209519602794510 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69466898369462927886 4 (BTree.node 69466898369462927406 4 BTree.leaf BTree.leaf) BTree.leaf)))) (BTree.node 70041107321952665646 4 (BTree.node 69469150169276612662 4 (BTree.node 69466898378052861966 4 (BTree.node 69466898369463123974 4 (BTree.node 69466898369463058446 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 69469150169276612638 4 (BTree.node 69466898403822665741 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 69608761757725098510 4 (BTree.node 69473653768903983158 4 (BTree.node 69473653768903983150 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 70041107321952665630 4 (BTree.node 70041107321952665613 3 BTree.leaf BTree.leaf) BTree.leaf))) (BTree.node 70041107356312403981 4 (BTree.node 70041107321952666374 4 (BTree.node 70041107321952666126 4 (BTree.node 70041107321952665870 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 70041107330542600206 4 (BTree.node 70041107321952796686 4 BTree.leaf BTree.leaf) BTree.leaf)) (BTree.node 70617568074256089142 4 (BTree.node 70617568074256089118 4 (BTree.node 70043359121766350861 4 BTree.leaf BTree.leaf) BTree.leaf) (BTree.node 71770489578862936118 4 (BTree.node 71770489578862936110 4 BTree.leaf BTree.leaf) BTree.leaf)))))))))

lemma t4_init : lookupDepth T4 (initBank * 4) = some 0 := rfl

lemma t4_ok : okTree T4 2 38 51 T4 = true := rfl

lemma lookupDepth_ok {T sub : BTree} {a b c k d : ℕ}
    (hok : okTree T a b c sub = true) (hl : lookupDepth sub k = some d) :
    checkNode T a b c k d = true := by
  induction sub with
  | leaf => simp [lookupDepth] at hl
  | node k' d' l r ihl ihr =>
    simp only [okTree, Bool.and_eq_true] at hok
    simp only [lookupDepth] at hl
    split_ifs at hl with h1 h2
    · exact ihl hok.1.2 hl
    · exact ihr hok.2 hl
    · cases hl
      have hq : k = k' := by omega
      subst hq
      exact hok.1.1

lemma checkNode_not {T : BTree} {a b c k d : ℕ} (hc : checkNode T a b c k d = true) :
    k % 4 ≤ 2 := by
  simp only [checkNode, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.1.1

lemma checkNode_init {T : BTree} {a b c k d : ℕ} (hc : checkNode T a b c k d = true)
    {v : ℕ} (hv : initBank.testBit v = true) : (k / 4).testBit v = true := by
  simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at hc
  have heq := congrArg (fun n => n.testBit v) hc.1.1.2
  rw [Nat.testBit_and, hv, Bool.and_true] at heq
  exact heq

lemma checkNode_noTarget {T : BTree} {a b c k d : ℕ} (hc : checkNode T a b c k d = true) :
    hasTarget a b c k = false := by
  simp only [checkNode, Bool.and_eq_true, Bool.not_eq_true'] at hc
  exact hc.1.2

lemma checkNode_step_lt {T : BTree} {a b c k d ch : ℕ}
    (hc : checkNode T a b c k d = true) (hd : d < 4) (hch : ch ∈ expandKey k) :
    ∃ d', lookupDepth T ch = some d' ∧ d' ≤ d + 1 := by
  simp only [checkNode, Bool.and_eq_true] at hc
  have hall := hc.2
  rw [ite_eq_left hd, List.all_eq_true] at hall
  have h1 := hall ch hch
  cases hlu : lookupDepth T ch with
  | none => rw [hlu] at h1; cases h1
  | some d' =>
    rw [hlu] at h1
    exact ⟨d', rfl, of_decide_eq_true h1⟩

lemma checkNode_step_4 {T : BTree} {a b c k d v n' : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc : checkNode T a b c k d = true) (hd : ¬ d < 4)
    (hch : ((k / 4 ||| twoPow v) * 4 + n') ∈ expandKey k) (hn' : n' < 4) :
    hasTarget a b c ((k / 4 ||| twoPow v) * 4 + n') = false := by
  simp only [checkNode, Bool.and_eq_true] at hc
  have hall := hc.2
  rw [ite_eq_right hd, Bool.or_eq_true] at hall
  rcases hall with htwo | hall
  · simp only [Bool.not_eq_true', hasTwoTargets, decide_eq_false_iff_not, Nat.not_le] at htwo
    simp only [hasTarget]
    have hdiv : ((k / 4 ||| twoPow v) * 4 + n') / 4 = k / 4 ||| twoPow v := by omega
    rw [hdiv, testBit_or_twoPow, testBit_or_twoPow, testBit_or_twoPow]
    cases hka : (k / 4).testBit a <;> cases hkb : (k / 4).testBit b <;>
      cases hkc : (k / 4).testBit c <;> simp_all
  · rw [List.all_eq_true] at hall
    have h1 := hall _ hch
    cases ht : hasTarget a b c ((k / 4 ||| twoPow v) * 4 + n') with
    | false => rfl
    | true => rw [ht] at h1; cases h1

lemma mem_expand_not {bank nots a : ℕ} (hn : nots < 2) (ha : a < 64)
    (hba : bank.testBit a = true) (hbv : bank.testBit (63 ^^^ a) = false) :
    (bank ||| twoPow (63 ^^^ a)) * 4 + (nots + 1) ∈ expandKey (bank * 4 + nots) := by
  have hk1 : (bank * 4 + nots) / 4 = bank := by omega
  have hk2 : (bank * 4 + nots) % 4 = nots := by omega
  simp only [expandKey, hk1, hk2, ite_eq_left hn, List.mem_append, List.mem_filterMap]
  left; left
  refine ⟨a, mem_masksOf.mpr ⟨ha, hba⟩, ?_⟩
  simp [hbv]

lemma mem_expand_and {bank nots a b : ℕ} (hn : nots ≤ 2) (ha : a < 64) (hb : b < 64)
    (hba : bank.testBit a = true) (hbb : bank.testBit b = true)
    (hbv : bank.testBit (a &&& b) = false) :
    (bank ||| twoPow (a &&& b)) * 4 + nots ∈ expandKey (bank * 4 + nots) := by
  have hne : a ≠ b := by
    intro h; subst h; simp [hba] at hbv
  have hk1 : (bank * 4 + nots) / 4 = bank := by omega
  have hk2 : (bank * 4 + nots) % 4 = nots := by omega
  simp only [expandKey, hk1, hk2, List.mem_append, List.mem_flatMap, List.mem_filterMap]
  left; right
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨a, mem_masksOf.mpr ⟨ha, hba⟩, b, mem_masksOf.mpr ⟨hb, hbb⟩, ?_⟩
    simp [hlt, hbv]
  · have hcomm : a &&& b = b &&& a := Nat.and_comm a b
    rw [hcomm] at hbv ⊢
    refine ⟨b, mem_masksOf.mpr ⟨hb, hbb⟩, a, mem_masksOf.mpr ⟨ha, hba⟩, ?_⟩
    simp [hlt, hbv]

lemma mem_expand_or {bank nots a b : ℕ} (hn : nots ≤ 2) (ha : a < 64) (hb : b < 64)
    (hba : bank.testBit a = true) (hbb : bank.testBit b = true)
    (hbv : bank.testBit (a ||| b) = false) :
    (bank ||| twoPow (a ||| b)) * 4 + nots ∈ expandKey (bank * 4 + nots) := by
  have hne : a ≠ b := by
    intro h; subst h; simp [hba] at hbv
  have hk1 : (bank * 4 + nots) / 4 = bank := by omega
  have hk2 : (bank * 4 + nots) % 4 = nots := by omega
  simp only [expandKey, hk1, hk2, List.mem_append, List.mem_flatMap, List.mem_filterMap]
  right
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨a, mem_masksOf.mpr ⟨ha, hba⟩, b, mem_masksOf.mpr ⟨hb, hbb⟩, ?_⟩
    simp [hlt, hbv]
  · have hcomm : a ||| b = b ||| a := Nat.or_comm a b
    rw [hcomm] at hbv ⊢
    refine ⟨b, mem_masksOf.mpr ⟨hb, hbb⟩, a, mem_masksOf.mpr ⟨ha, hba⟩, ?_⟩
    simp [hlt, hbv]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      rw [e]
      exact key

def val (D : Circuit) (t : Fin 6) (w : ℕ) : Bool :=
  (D.wires (xs t)).getD w false

lemma val_lt_7 (D : Circuit) (t : Fin 6) {w : ℕ} (hw : w < 7) :
    val D t w = (xs t).getD w false :=
  foldl_getD_lt D.gates (xs t) w (by rw [xs_len]; exact hw)

lemma val_gate (D : Circuit) (hRead : ReadsBack 7 D) (t : Fin 6) {j : ℕ} (hj : j < D.gates.length) :
    val D t (7 + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (val D t)) := by
  have h0 : val D t (7 + j) = (D.gates.foldl stepWire (xs t)).getD (7 + j) false := rfl
  have h1 := foldl_getD_gate D.gates (xs t) j hj
  rw [xs_len] at h1
  rw [h0, h1]
  simp only [gateAt, List.getD_eq_getElem?_getD, hj, getElem?_pos, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < 7 + j := hRead j hj i (by simpa [gateAt, List.getD_eq_getElem?_getD, hj] using hi)
  rw [ite_eq_left hilt]
  rfl

def wireMask (D : Circuit) (w : ℕ) : ℕ :=
  toNat6 (val D 0 w) (val D 1 w) (val D 2 w) (val D 3 w) (val D 4 w) (val D 5 w)

lemma wireMask_lt (D : Circuit) (w : ℕ) : wireMask D w < 64 := toNat6_lt _ _ _ _ _ _

lemma wireMask_testBit (D : Circuit) (w : ℕ) (t : Fin 6) :
    (wireMask D w).testBit t.val = val D t w := by
  unfold wireMask
  rw [toNat6_testBit]
  rcases t with ⟨t, ht⟩
  rcases t with _ | _ | _ | _ | _ | _ | t
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

lemma wireMask_init (D : Circuit) {w : ℕ} (hw : w < 7) :
    initBank.testBit (wireMask D w) = true := by
  rcases w with _ | _ | _ | _ | _ | _ | _ | w
  · simp only [wireMask, val_lt_7 D _ (by omega : 0 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 1 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 2 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 3 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 4 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 5 < 7)]; decide
  · simp only [wireMask, val_lt_7 D _ (by omega : 6 < 7)]; decide
  · omega

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notPrefix (D : Circuit) (k : ℕ) : ℕ :=
  ((D.gates.take k).filter fun g => isNotOp g.op).length

lemma notPrefix_zero (D : Circuit) : notPrefix D 0 = 0 := by simp [notPrefix]

lemma notPrefix_end (D : Circuit) : notPrefix D D.gates.length = notCount D := by
  unfold notPrefix notCount
  rw [List.take_length]
  congr 1
  apply congrArg (fun f => List.filter f D.gates)
  funext g
  cases g.op <;> rfl

lemma notPrefix_succ (D : Circuit) {j : ℕ} (hj : j < D.gates.length) :
    notPrefix D (j + 1) =
      notPrefix D j + if isNotOp (gateAt D j).op then 1 else 0 := by
  unfold notPrefix
  rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.length_append]
  have heq : gateAt D j = D.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [heq]
  cases h : isNotOp D.gates[j].op <;> simp [h]

lemma filter_take_le {α : Type _} (p : α → Bool) (l : List α) (k : ℕ) :
    ((l.take k).filter p).length ≤ (l.filter p).length := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.take_succ_cons, List.filter_cons]
      cases p a <;> simp [ih k]

lemma notPrefix_le_count (D : Circuit) (k : ℕ) : notPrefix D k ≤ notCount D := by
  rw [← notPrefix_end D]
  unfold notPrefix
  rw [List.take_length]
  exact filter_take_le _ D.gates k

lemma wireMask_gate_step {D : Circuit} (hFan : FanInTwo D) (hRead : ReadsBack 7 D)
    {j : ℕ} (hj : j < D.gates.length) {key d : ℕ}
    (hc : checkNode T4 2 38 51 key d = true)
    (hcov : ∀ w < 7 + j, (key / 4).testBit (wireMask D w) = true)
    (hnot : key % 4 ≤ notPrefix D j) (hnotTot : notCount D ≤ 2) :
    (key / 4).testBit (wireMask D (7 + j)) = true ∨
      ∃ v n', n' < 4 ∧
        ((key / 4 ||| twoPow v) * 4 + n') ∈ expandKey key ∧
        n' ≤ notPrefix D (j + 1) ∧
        ∀ w < 7 + (j + 1), (((key / 4 ||| twoPow v) * 4 + n') / 4).testBit (wireMask D w) = true := by
  have hjmem : gateAt D j ∈ D.gates := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  obtain ⟨hop, hlen⟩ := hFan (gateAt D j) hjmem
  have hnle : key % 4 ≤ 2 := checkNode_not hc
  have hprefix_end : notPrefix D (j + 1) ≤ notCount D := notPrefix_le_count D (j + 1)
  by_cases halready : (key / 4).testBit (wireMask D (7 + j)) = true
  · exact Or.inl halready
  · right
    have hfalse : (key / 4).testBit (wireMask D (7 + j)) = false :=
      Bool.eq_false_iff.mpr halready
    have hnot63 : (key / 4).testBit 63 = true :=
      checkNode_init hc (by decide)
    have hnot0 : (key / 4).testBit 0 = true :=
      checkNode_init hc (by decide)
    have hval (t : Fin 6) : val D t (7 + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (val D t)) :=
      val_gate D hRead t hj
    have hread_lt {i : ℕ} (hi : i ∈ (gateAt D j).inputs) : i < 7 + j := hRead j hj i hi
    have hinputs : (gateAt D j).inputs = [] ∨ (∃ x0, (gateAt D j).inputs = [x0]) ∨
        ∃ x0 x1, (gateAt D j).inputs = [x0, x1] := by
      match h : (gateAt D j).inputs with
      | [] => exact Or.inl rfl
      | [x0] => exact Or.inr (Or.inl ⟨x0, rfl⟩)
      | [x0, x1] => exact Or.inr (Or.inr ⟨x0, x1, rfl⟩)
      | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen
    have hkey : key = (key / 4) * 4 + (key % 4) := by omega
    rcases hop with hop | hop | hop
    · rcases hinputs with hin | ⟨x0, hin⟩ | ⟨x0, x1, hin⟩
      · have hm : wireMask D (7 + j) = 63 := by
          simp [wireMask, hval, hop, hin, GateOp.eval]; rfl
        rw [hm] at hfalse; rw [hnot63] at hfalse; cases hfalse
      · have hx0 : x0 < 7 + j := hread_lt (by simp [hin])
        have hm : wireMask D (7 + j) = wireMask D x0 := by
          simp [wireMask, hval, hop, hin, GateOp.eval]
        rw [hm, hcov x0 hx0] at hfalse; cases hfalse
      · have hx0 : x0 < 7 + j := hread_lt (by simp [hin])
        have hx1 : x1 < 7 + j := hread_lt (by simp [hin])
        have hm : wireMask D (7 + j) = wireMask D x0 &&& wireMask D x1 := by
          simp only [wireMask, hval, hop, hin, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, id_eq]
          exact toNat6_and _ _ _ _ _ _ _ _ _ _ _ _
        rw [hm] at hfalse
        refine ⟨wireMask D x0 &&& wireMask D x1, key % 4, by omega, ?_, ?_, ?_⟩
        · have hexp := mem_expand_and hnle (wireMask_lt D x0) (wireMask_lt D x1)
            (hcov x0 hx0) (hcov x1 hx1) hfalse
          rw [← hkey] at hexp
          exact hexp
        · rw [notPrefix_succ D hj, hop]
          simpa [isNotOp] using hnot
        · intro w hw
          have hdiv : ((key / 4 ||| twoPow (wireMask D x0 &&& wireMask D x1)) * 4 + key % 4) / 4 =
              key / 4 ||| twoPow (wireMask D x0 &&& wireMask D x1) := by omega
          rw [hdiv, testBit_or_twoPow]
          by_cases hwj : w = 7 + j
          · subst hwj; rw [hm]; simp
          · simp [hcov w (by omega)]
    · rcases hinputs with hin | ⟨x0, hin⟩ | ⟨x0, x1, hin⟩
      · have hm : wireMask D (7 + j) = 0 := by
          simp [wireMask, hval, hop, hin, GateOp.eval]; decide
        rw [hm] at hfalse; rw [hnot0] at hfalse; cases hfalse
      · have hx0 : x0 < 7 + j := hread_lt (by simp [hin])
        have hm : wireMask D (7 + j) = wireMask D x0 := by
          simp [wireMask, hval, hop, hin, GateOp.eval]
        rw [hm, hcov x0 hx0] at hfalse; cases hfalse
      · have hx0 : x0 < 7 + j := hread_lt (by simp [hin])
        have hx1 : x1 < 7 + j := hread_lt (by simp [hin])
        have hm : wireMask D (7 + j) = wireMask D x0 ||| wireMask D x1 := by
          simp only [wireMask, hval, hop, hin, List.map_cons, List.map_nil, GateOp.eval,
            List.any_cons, List.any_nil, Bool.or_false, id_eq]
          exact toNat6_or _ _ _ _ _ _ _ _ _ _ _ _
        rw [hm] at hfalse
        refine ⟨wireMask D x0 ||| wireMask D x1, key % 4, by omega, ?_, ?_, ?_⟩
        · have hexp := mem_expand_or hnle (wireMask_lt D x0) (wireMask_lt D x1)
            (hcov x0 hx0) (hcov x1 hx1) hfalse
          rw [← hkey] at hexp
          exact hexp
        · rw [notPrefix_succ D hj, hop]
          simpa [isNotOp] using hnot
        · intro w hw
          have hdiv : ((key / 4 ||| twoPow (wireMask D x0 ||| wireMask D x1)) * 4 + key % 4) / 4 =
              key / 4 ||| twoPow (wireMask D x0 ||| wireMask D x1) := by omega
          rw [hdiv, testBit_or_twoPow]
          by_cases hwj : w = 7 + j
          · subst hwj; rw [hm]; simp
          · simp [hcov w (by omega)]
    · have hsucc : notPrefix D (j + 1) = notPrefix D j + 1 := by
        rw [notPrefix_succ D hj, hop]; simp [isNotOp]
      have hn_lt : key % 4 < 2 := by omega
      have notHead (x0 : ℕ) (hx0 : x0 < 7 + j) (hm : wireMask D (7 + j) = 63 ^^^ wireMask D x0) :
          ∃ v n', n' < 4 ∧
            ((key / 4 ||| twoPow v) * 4 + n') ∈ expandKey key ∧
            n' ≤ notPrefix D (j + 1) ∧
            ∀ w < 7 + (j + 1), (((key / 4 ||| twoPow v) * 4 + n') / 4).testBit (wireMask D w) = true := by
        rw [hm] at hfalse
        refine ⟨63 ^^^ wireMask D x0, key % 4 + 1, by omega, ?_, by omega, ?_⟩
        · have hexp := mem_expand_not hn_lt (wireMask_lt D x0) (hcov x0 hx0) hfalse
          rw [← hkey] at hexp
          exact hexp
        · intro w hw
          have hdiv : ((key / 4 ||| twoPow (63 ^^^ wireMask D x0)) * 4 + (key % 4 + 1)) / 4 =
              key / 4 ||| twoPow (63 ^^^ wireMask D x0) := by omega
          rw [hdiv, testBit_or_twoPow]
          by_cases hwj : w = 7 + j
          · subst hwj; rw [hm]; simp
          · simp [hcov w (by omega)]
      rcases hinputs with hin | ⟨x0, hin⟩ | ⟨x0, x1, hin⟩
      · have hm : wireMask D (7 + j) = 63 := by
          simp only [wireMask, hval, hin]; rw [hop]; rfl
        rw [hm] at hfalse; rw [hnot63] at hfalse; cases hfalse
      · exact notHead x0 (hread_lt (by simp [hin])) (by
          simp only [wireMask, hval, hin, List.map_cons]; rw [hop]
          exact toNat6_not _ _ _ _ _ _)
      · exact notHead x0 (hread_lt (by simp [hin])) (by
          simp only [wireMask, hval, hin, List.map_cons]; rw [hop]
          exact toNat6_not _ _ _ _ _ _)

end PEqualNP.Outside.L_meta_50782_aux

theorem PEqualNP.Outside.L_meta_50782 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (51 : Nat).testBit t.val)) := by
  open PEqualNP.Outside.L_meta_50782_aux in
  rintro ⟨D, p, q, r, hFan, hRead, hNot, hSize, hOut⟩
  have hmask (w : ℕ) (m : ℕ) (hm : m < 64)
      (ht : ∀ t : Fin 6, val D t w = m.testBit t.val) : wireMask D w = m := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 6
    · rw [wireMask_testBit D w ⟨k, hk⟩, ht ⟨k, hk⟩]
    · have hk6 : 6 ≤ k := by omega
      have h1 : (wireMask D w).testBit k = false := toNat6_testBit_ge _ _ _ _ _ _ k hk6
      have h2 : m.testBit k = false := by
        apply Nat.testBit_lt_two_pow
        have hp : 64 ≤ 2 ^ k := by
          calc 64 = 2 ^ 6 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk6
        omega
      rw [h1, h2]
  have hpa : wireMask D p.val = 2 := hmask p.val 2 (by decide) fun t => (hOut t).1
  have hqb : wireMask D q.val = 38 := hmask q.val 38 (by decide) fun t => (hOut t).2.1
  have hrc : wireMask D r.val = 51 := hmask r.val 51 (by decide) fun t => (hOut t).2.2
  have hbound : ∀ k ≤ min D.gates.length 4,
      ∃ key d, lookupDepth T4 key = some d ∧ d ≤ k ∧
        key % 4 ≤ notPrefix D k ∧
        ∀ w < 7 + k, (key / 4).testBit (wireMask D w) = true := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨initBank * 4, 0, t4_init, Nat.le_refl 0, by simp [notPrefix_zero], fun w hw => ?_⟩
      have hdiv : (initBank * 4) / 4 = initBank := by omega
      rw [hdiv]
      exact wireMask_init D hw
    | succ k ih =>
      obtain ⟨key, d, hlu, hdk, hnotk, hcov⟩ := ih (by omega)
      have hc := lookupDepth_ok t4_ok hlu
      have hklen : k < D.gates.length := by omega
      rcases wireMask_gate_step hFan hRead hklen hc hcov hnotk hNot with hsame | ⟨v, n', hn', hch, hchn, hchc⟩
      · refine ⟨key, d, hlu, by omega, ?_, fun w hw => ?_⟩
        · have hle : notPrefix D k ≤ notPrefix D (k + 1) := by rw [notPrefix_succ D hklen]; omega
          omega
        · by_cases hwk : w = 7 + k
          · subst hwk; exact hsame
          · exact hcov w (by omega)
      · obtain ⟨d', hlu', hd'⟩ := checkNode_step_lt hc (by omega : d < 4) hch
        exact ⟨_, d', hlu', by omega, by omega, hchc⟩
  have hsz : D.gates.length ≤ 5 := hSize
  by_cases h4 : D.gates.length ≤ 4
  · obtain ⟨key, d, hlu, _, _, hcov⟩ := hbound D.gates.length (by omega)
    have hc := lookupDepth_ok t4_ok hlu
    have hnt := checkNode_noTarget hc
    have ha := hcov p.val (by have hp := p.isLt; change p.val < 7 + D.gates.length at hp; omega)
    have hb := hcov q.val (by have hq := q.isLt; change q.val < 7 + D.gates.length at hq; omega)
    have hc' := hcov r.val (by have hr := r.isLt; change r.val < 7 + D.gates.length at hr; omega)
    rw [hpa] at ha; rw [hqb] at hb; rw [hrc] at hc'
    unfold hasTarget at hnt; dsimp only at hnt
    rw [ha, hb, hc'] at hnt
    cases hnt
  · have hlen5 : D.gates.length = 5 := by omega
    obtain ⟨key, d, hlu, hd4, hnot4, hcov⟩ := hbound 4 (by omega)
    have hc := lookupDepth_ok t4_ok hlu
    have finalCheck : ∃ fkey, hasTarget 2 38 51 fkey = false ∧
        ∀ w < 12, (fkey / 4).testBit (wireMask D w) = true := by
      rcases wireMask_gate_step hFan hRead (by omega : 4 < D.gates.length) hc hcov hnot4 hNot with
        hsame | ⟨v, n', hn', hch, _, hchc⟩
      · refine ⟨key, checkNode_noTarget hc, fun w hw => ?_⟩
        by_cases hw11 : w = 11
        · subst hw11; exact hsame
        · exact hcov w (by omega)
      · by_cases hdlt : d < 4
        · obtain ⟨d', hlu', _⟩ := checkNode_step_lt hc hdlt hch
          exact ⟨_, checkNode_noTarget (lookupDepth_ok t4_ok hlu'), hchc⟩
        · exact ⟨_, checkNode_step_4 (by decide) (by decide) (by decide) hc hdlt hch hn', hchc⟩
    obtain ⟨fkey, hnt, hcovf⟩ := finalCheck
    have ha := hcovf p.val (by have hp := p.isLt; change p.val < 7 + D.gates.length at hp; omega)
    have hb := hcovf q.val (by have hq := q.isLt; change q.val < 7 + D.gates.length at hq; omega)
    have hc' := hcovf r.val (by have hr := r.isLt; change r.val < 7 + D.gates.length at hr; omega)
    rw [hpa] at ha; rw [hqb] at hb; rw [hrc] at hc'
    unfold hasTarget at hnt; dsimp only at hnt
    rw [ha, hb, hc'] at hnt
    cases hnt
