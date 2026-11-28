import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51308

open PEqualNP.CircuitLowerBounds

def initMask : Nat := 0xD101000100000001

def hasBit (m v : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m v) 1) 1

def setBit (m v : Nat) : Nat :=
  Nat.lor m (Nat.shiftLeft 1 v)

theorem hasBit_eq_testBit (m v : Nat) : hasBit m v = m.testBit v := by
  unfold hasBit
  change (((m >>> v) &&& 1) == 1) = m.testBit v
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  cases Nat.mod_two_eq_zero_or_one (m / 2 ^ v) with
  | inl h => simp [h]
  | inr h => simp [h]

theorem hasBit_setBit (m v x : Nat) : hasBit (setBit m v) x = (hasBit m x || Nat.beq x v) := by
  rw [hasBit_eq_testBit, hasBit_eq_testBit]
  unfold setBit
  change (m ||| (1 <<< v)).testBit x = (m.testBit x || (x == v))
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hx : x = v
  · subst hx; simp
  · have hne : (x == v) = false := beq_false_of_ne hx
    have hlt : ¬(v ≤ x ∧ (1 : Nat).testBit (x - v) = true) := by
      rintro ⟨hle, htb⟩
      have hsub : x - v ≠ 0 := by omega
      cases h : x - v with
      | zero => exact hsub h
      | succ k =>
        rw [h] at htb
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at htb
        have hp : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (Nat.succ_ne_zero k) 2
        have hd : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
        simp [hd] at htb
    simp [hne, hlt]

theorem setBit_of_hasBit {m v : Nat} (h : hasBit m v = true) : setBit m v = m := by
  apply Nat.eq_of_testBit_eq; intro x
  rw [← hasBit_eq_testBit, ← hasBit_eq_testBit, hasBit_setBit]
  by_cases hx : x = v
  · subst hx; rw [h]; rfl
  · have hne : Nat.beq x v = false := by
      cases hb : Nat.beq x v
      · rfl
      · exact absurd (Nat.beq_eq.mp hb) hx
    rw [hne]; simp

def missCount (A B C S : Nat) : Nat :=
  (if hasBit S A then 0 else 1) +
  (if hasBit S B || Nat.beq B A then 0 else 1) +
  (if hasBit S C || Nat.beq C A || Nat.beq C B then 0 else 1)

theorem missCount_setBit (A B C S v : Nat) :
    missCount A B C S ≤ missCount A B C (setBit S v) + 1 := by
  unfold missCount
  simp only [hasBit_setBit]
  have h1 : (if hasBit S A then 0 else 1) ≤
      (if (hasBit S A || Nat.beq A v) then 0 else 1) + (if A = v then 1 else 0) := by
    by_cases h : A = v <;> cases hasBit S A <;> simp_all [Nat.beq_eq]
  have h2 : (if hasBit S B || Nat.beq B A then 0 else 1) ≤
      (if (hasBit S B || Nat.beq B v) || Nat.beq B A then 0 else 1) + (if B = v ∧ B ≠ A then 1 else 0) := by
    by_cases h1 : B = v <;> by_cases h2 : B = A <;> cases hasBit S B <;> simp_all [Nat.beq_eq]
  have h3 : (if hasBit S C || Nat.beq C A || Nat.beq C B then 0 else 1) ≤
      (if (hasBit S C || Nat.beq C v) || Nat.beq C A || Nat.beq C B then 0 else 1) + (if C = v ∧ C ≠ A ∧ C ≠ B then 1 else 0) := by
    by_cases h1 : C = v <;> by_cases h2 : C = A <;> by_cases h3 : C = B <;> cases hasBit S C <;> simp_all [Nat.beq_eq]
  have hsum : (if A = v then 1 else 0) + (if B = v ∧ B ≠ A then 1 else 0) + (if C = v ∧ C ≠ A ∧ C ≠ B then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  omega

inductive CanReach (A B C : Nat) : Nat → Nat → Nat → Prop
  | hit {rem nots S} : hasBit S A = true → hasBit S B = true → hasBit S C = true → CanReach A B C rem nots S
  | noop {rem nots S} : CanReach A B C rem nots S → CanReach A B C (rem + 1) nots S
  | noopNot {rem nots S} : CanReach A B C rem nots S → CanReach A B C (rem + 1) (nots + 1) S
  | stepAnd {rem nots S a b} : a < 64 → b < 64 → hasBit S a = true → hasBit S b = true →
      CanReach A B C rem nots (setBit S (a &&& b)) → CanReach A B C (rem + 1) nots S
  | stepOr {rem nots S a b} : a < 64 → b < 64 → hasBit S a = true → hasBit S b = true →
      CanReach A B C rem nots (setBit S (a ||| b)) → CanReach A B C (rem + 1) nots S
  | stepNot {rem nots S a} : a < 64 → hasBit S a = true →
      CanReach A B C rem nots (setBit S (63 ^^^ a)) → CanReach A B C (rem + 1) (nots + 1) S

theorem canReach_miss_le {A B C rem nots S : Nat} (h : CanReach A B C rem nots S) :
    missCount A B C S ≤ rem := by
  induction h with
  | hit hA hB hC => unfold missCount; simp [hA, hB, hC]
  | noop _ ih => omega
  | noopNot _ ih => omega
  | @stepAnd _ _ S0 a b _ _ _ _ _ ih => have := missCount_setBit A B C S0 (a &&& b); omega
  | @stepOr _ _ S0 a b _ _ _ _ _ ih => have := missCount_setBit A B C S0 (a ||| b); omega
  | @stepNot _ _ S0 a _ _ _ ih => have := missCount_setBit A B C S0 (63 ^^^ a); omega

inductive NTree
  | leaf
  | node (v : Nat) (l r : NTree)

def memTree (x : Nat) : NTree → Bool
  | .leaf => false
  | .node v l r =>
    Bool.rec (Bool.rec (memTree x r) (memTree x l) (Nat.blt x v)) true (Nat.beq x v)

def allTree (f : Nat → Bool) : NTree → Bool
  | .leaf => true
  | .node v l r => f v && allTree f l && allTree f r

theorem allTree_of_mem {f : Nat → Bool} {t : NTree} (ha : allTree f t = true) {x : Nat}
    (hm : memTree x t = true) : f x = true := by
  induction t with
  | leaf => exact Bool.noConfusion hm
  | node v l r ihl ihr =>
    unfold allTree at ha
    simp only [Bool.and_eq_true] at ha
    unfold memTree at hm
    cases h1 : Nat.beq x v
    · rw [h1] at hm; dsimp only at hm
      cases h2 : Nat.blt x v
      · rw [h2] at hm; exact ihr ha.2 hm
      · rw [h2] at hm; exact ihl ha.1.2 hm
    · rw [Nat.beq_eq.mp h1]; exact ha.1.1

def bitsOfAux (m : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | k + 1, acc => bitsOfAux m k (Bool.rec acc (k :: acc) (hasBit m k))

def bitsOf (m : Nat) : List Nat := bitsOfAux m 64 []

theorem bitsOfAux_mem (m : Nat) : ∀ (n : Nat) (acc : List Nat) (x : Nat),
    x ∈ bitsOfAux m n acc ↔ (x < n ∧ hasBit m x = true) ∨ x ∈ acc := by
  intro n
  induction n with
  | zero => intro acc x; simp [bitsOfAux]
  | succ k ih =>
    intro acc x
    unfold bitsOfAux
    rw [ih]
    cases hb : hasBit m k
    · simp only [Nat.lt_succ_iff]
      constructor
      · rintro (⟨hlt, hbx⟩ | ha)
        · exact Or.inl ⟨Nat.le_of_lt hlt, hbx⟩
        · exact Or.inr ha
      · rintro (⟨hle, hbx⟩ | ha)
        · by_cases hx : x = k
          · subst hx; rw [hb] at hbx; exact Bool.noConfusion hbx
          · exact Or.inl ⟨by omega, hbx⟩
        · exact Or.inr ha
    · simp only [List.mem_cons]
      constructor
      · rintro (⟨hlt, hbx⟩ | rfl | ha)
        · exact Or.inl ⟨Nat.lt_succ_of_lt hlt, hbx⟩
        · exact Or.inl ⟨Nat.lt_succ_self _, hb⟩
        · exact Or.inr ha
      · rintro (⟨hle, hbx⟩ | ha)
        · by_cases hx : x = k
          · exact Or.inr (Or.inl hx)
          · exact Or.inl ⟨by omega, hbx⟩
        · exact Or.inr (Or.inr ha)

theorem bitsOf_mem {m x : Nat} (hx : x < 64) (hb : hasBit m x = true) : x ∈ bitsOf m :=
  (bitsOfAux_mem m 64 [] x).mpr (Or.inl ⟨hx, hb⟩)

def checkNext (A B C rem1 S v : Nat) (nextLayer : NTree) : Bool :=
  hasBit S v || Nat.blt rem1 (missCount A B C (setBit S v)) || memTree (setBit S v) nextLayer

def checkNots (A B C rem1 S : Nat) (notLayer : NTree) : List Nat → Bool
  | [] => true
  | a :: rest =>
    checkNext A B C rem1 S (Nat.xor 63 a) notLayer && checkNots A B C rem1 S notLayer rest

def checkPairsWith (A B C rem1 S a : Nat) (sameLayer : NTree) : List Nat → Bool
  | [] => true
  | b :: rest =>
    checkNext A B C rem1 S (Nat.land a b) sameLayer &&
    checkNext A B C rem1 S (Nat.lor a b) sameLayer &&
    checkPairsWith A B C rem1 S a sameLayer rest

def checkAllPairs (A B C rem1 S : Nat) (sameLayer : NTree) : List Nat → Bool
  | [] => true
  | a :: rest =>
    checkPairsWith A B C rem1 S a sameLayer rest &&
    checkAllPairs A B C rem1 S sameLayer rest

def checkState (A B C : Nat) (layers : Nat → Nat → NTree) (rem nots S : Nat) : Bool :=
  !(hasBit S A && hasBit S B && hasBit S C) &&
  (match rem with
   | 0 => true
   | rem1 + 1 =>
     Nat.blt (rem1 + 1) (missCount A B C S) ||
     let ws := bitsOf S
     checkAllPairs A B C rem1 S (layers rem1 nots) ws &&
     (match nots with
      | 0 => true
      | nots1 + 1 => checkNots A B C rem1 S (layers rem1 nots1) ws))

def checkLayer (A B C : Nat) (layers : Nat → Nat → NTree) (rem nots : Nat) : Bool :=
  allTree (checkState A B C layers rem nots) (layers rem nots)

def checkAllLayers (A B C : Nat) (layers : Nat → Nat → NTree) : Nat → Bool
  | 0 => checkLayer A B C layers 0 0 && checkLayer A B C layers 0 1 && checkLayer A B C layers 0 2
  | k + 1 =>
    checkLayer A B C layers (k + 1) 0 &&
    checkLayer A B C layers (k + 1) 1 &&
    checkLayer A B C layers (k + 1) 2 &&
    checkAllLayers A B C layers k

theorem checkNots_at {A B C rem1 S : Nat} {notLayer : NTree} {ws : List Nat}
    (h : checkNots A B C rem1 S notLayer ws = true) {a : Nat} (ha : a ∈ ws) :
    checkNext A B C rem1 S (Nat.xor 63 a) notLayer = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    unfold checkNots at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | htl
    · exact h.1
    · exact ih h.2 htl

theorem checkPairsWith_at {A B C rem1 S a : Nat} {sameLayer : NTree} {ws : List Nat}
    (h : checkPairsWith A B C rem1 S a sameLayer ws = true) {b : Nat} (hb : b ∈ ws) :
    checkNext A B C rem1 S (Nat.land a b) sameLayer = true ∧
    checkNext A B C rem1 S (Nat.lor a b) sameLayer = true := by
  induction ws with
  | nil => cases hb
  | cons x xs ih =>
    unfold checkPairsWith at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | htl
    · exact h.1
    · exact ih h.2 htl

theorem checkAllPairs_at {A B C rem1 S : Nat} {sameLayer : NTree} {ws : List Nat}
    (h : checkAllPairs A B C rem1 S sameLayer ws = true) {a b : Nat}
    (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    checkNext A B C rem1 S (Nat.land a b) sameLayer = true ∧
    checkNext A B C rem1 S (Nat.lor a b) sameLayer = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    unfold checkAllPairs at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact checkPairsWith_at h.1 hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have hp := checkPairsWith_at h.1 ha'
        have hand : Nat.land a b = Nat.land b a := Nat.and_comm a b
        have hor : Nat.lor a b = Nat.lor b a := Nat.or_comm a b
        rw [hand, hor]; exact hp
      · exact ih h.2 ha' hb'

theorem checkAllLayers_at {A B C N : Nat} {layers : Nat → Nat → NTree}
    (h : checkAllLayers A B C layers N = true) {rem nots S : Nat}
    (hr : rem ≤ N) (hn : nots ≤ 2) (hmem : memTree S (layers rem nots) = true) :
    checkState A B C layers rem nots S = true := by
  induction N with
  | zero =>
    have hrz : rem = 0 := by omega
    subst hrz
    unfold checkAllLayers at h
    simp only [Bool.and_eq_true] at h
    have hn3 : nots = 0 ∨ nots = 1 ∨ nots = 2 := by omega
    rcases hn3 with rfl | rfl | rfl
    · exact allTree_of_mem h.1.1 hmem
    · exact allTree_of_mem h.1.2 hmem
    · exact allTree_of_mem h.2 hmem
  | succ k ih =>
    unfold checkAllLayers at h
    simp only [Bool.and_eq_true] at h
    by_cases hre : rem = k + 1
    · subst hre
      have hn3 : nots = 0 ∨ nots = 1 ∨ nots = 2 := by omega
      rcases hn3 with rfl | rfl | rfl
      · exact allTree_of_mem h.1.1.1 hmem
      · exact allTree_of_mem h.1.1.2 hmem
      · exact allTree_of_mem h.1.2 hmem
    · exact ih h.2 (by omega)

theorem checkAllLayers_sound {A B C N : Nat} {layers : Nat → Nat → NTree}
    (hall : checkAllLayers A B C layers N = true) :
    ∀ r, ∀ rem nots S, rem ≤ N → nots ≤ 2 → memTree S (layers rem nots) = true →
      r ≤ rem → ∀ n, n ≤ nots → ¬CanReach A B C r n S := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro rem nots S hremN hnots2 hmem hr n hn hreach
    have hst := checkAllLayers_at hall hremN hnots2 hmem
    unfold checkState at hst
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hst
    obtain ⟨hnohit, hbody⟩ := hst
    cases hreach with
    | hit hA hB hC =>
      rw [hA, hB, hC] at hnohit; exact Bool.noConfusion hnohit
    | @noop r1 _ _ hsub =>
      exact ih r1 (by omega) rem nots S hremN hnots2 hmem (by omega) n hn hsub
    | @noopNot r1 n1 _ hsub =>
      exact ih r1 (by omega) rem nots S hremN hnots2 hmem (by omega) n1 (by omega) hsub
    | @stepAnd r1 _ _ a b ha hb hsa hsb hsub =>
      by_cases hv : hasBit S (a &&& b) = true
      · rw [setBit_of_hasBit hv] at hsub
        exact ih r1 (by omega) rem nots S hremN hnots2 hmem (by omega) n hn hsub
      · have hne : a ≠ b := by
          intro he; subst he; rw [Nat.and_self] at hv; exact hv hsa
        cases rem with
        | zero => omega
        | succ rem1 =>
          dsimp only at hbody
          simp only [Bool.or_eq_true] at hbody
          rcases hbody with hmiss | hch
          · have hm := Nat.blt_eq.mp hmiss
            have hle := canReach_miss_le (CanReach.stepAnd ha hb hsa hsb hsub)
            omega
          · simp only [Bool.and_eq_true] at hch
            have hnxt := (checkAllPairs_at hch.1 (bitsOf_mem ha hsa) (bitsOf_mem hb hsb) hne).1
            unfold checkNext at hnxt
            simp only [Bool.or_eq_true] at hnxt
            rcases hnxt with (hv2 | hmiss2) | hmem2
            · exact hv hv2
            · have hm : rem1 < missCount A B C (setBit S (a &&& b)) := Nat.blt_eq.mp hmiss2
              have hle := canReach_miss_le hsub
              omega
            · exact ih r1 (by omega) rem1 nots (setBit S (a &&& b)) (by omega) hnots2
                hmem2 (by omega) n hn hsub
    | @stepOr r1 _ _ a b ha hb hsa hsb hsub =>
      by_cases hv : hasBit S (a ||| b) = true
      · rw [setBit_of_hasBit hv] at hsub
        exact ih r1 (by omega) rem nots S hremN hnots2 hmem (by omega) n hn hsub
      · have hne : a ≠ b := by
          intro he; subst he; rw [Nat.or_self] at hv; exact hv hsa
        cases rem with
        | zero => omega
        | succ rem1 =>
          dsimp only at hbody
          simp only [Bool.or_eq_true] at hbody
          rcases hbody with hmiss | hch
          · have hm := Nat.blt_eq.mp hmiss
            have hle := canReach_miss_le (CanReach.stepOr ha hb hsa hsb hsub)
            omega
          · simp only [Bool.and_eq_true] at hch
            have hnxt := (checkAllPairs_at hch.1 (bitsOf_mem ha hsa) (bitsOf_mem hb hsb) hne).2
            unfold checkNext at hnxt
            simp only [Bool.or_eq_true] at hnxt
            rcases hnxt with (hv2 | hmiss2) | hmem2
            · exact hv hv2
            · have hm : rem1 < missCount A B C (setBit S (a ||| b)) := Nat.blt_eq.mp hmiss2
              have hle := canReach_miss_le hsub
              omega
            · exact ih r1 (by omega) rem1 nots (setBit S (a ||| b)) (by omega) hnots2
                hmem2 (by omega) n hn hsub
    | @stepNot r1 n1 _ a ha hsa hsub =>
      by_cases hv : hasBit S (63 ^^^ a) = true
      · rw [setBit_of_hasBit hv] at hsub
        exact ih r1 (by omega) rem nots S hremN hnots2 hmem (by omega) n1 (by omega) hsub
      · cases rem with
        | zero => omega
        | succ rem1 =>
          cases nots with
          | zero => omega
          | succ nots1 =>
            dsimp only at hbody
            simp only [Bool.or_eq_true] at hbody
            rcases hbody with hmiss | hch
            · have hm := Nat.blt_eq.mp hmiss
              have hle := canReach_miss_le (CanReach.stepNot ha hsa hsub)
              omega
            · simp only [Bool.and_eq_true] at hch
              have hnxt := checkNots_at hch.2 (bitsOf_mem ha hsa)
              unfold checkNext at hnxt
              simp only [Bool.or_eq_true] at hnxt
              rcases hnxt with (hv2 | hmiss2) | hmem2
              · exact hv hv2
              · have hm : rem1 < missCount A B C (setBit S (63 ^^^ a)) := Nat.blt_eq.mp hmiss2
                have hle := canReach_miss_le hsub
                omega
              · exact ih r1 (by omega) rem1 nots1 (setBit S (63 ^^^ a)) (by omega) (by omega)
                  hmem2 (by omega) n1 (by omega) hsub

def inRow (t : Nat) : List Bool :=
  [Nat.blt 0 t, Nat.blt 1 t, Nat.blt 2 t, Nat.blt 3 t, Nat.blt 4 t, false, true]

theorem inRow_eq (t : Fin 6) :
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] = inRow t.val := by
  fin_cases t <;> rfl

def pack6 (b0 b1 b2 b3 b4 b5 : Bool) : Nat :=
  (if b0 then 1 else 0) +
  (if b1 then 2 else 0) +
  (if b2 then 4 else 0) +
  (if b3 then 8 else 0) +
  (if b4 then 16 else 0) +
  (if b5 then 32 else 0)

theorem pack6_lt (b0 b1 b2 b3 b4 b5 : Bool) : pack6 b0 b1 b2 b3 b4 b5 < 64 := by
  unfold pack6; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem pack6_testBit (b0 b1 b2 b3 b4 b5 : Bool) (t : Fin 6) :
    (pack6 b0 b1 b2 b3 b4 b5).testBit t.val = match t.val with
      | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5 := by
  fin_cases t <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

theorem pow2_ge_64 {k : Nat} (hk : ¬k < 6) : 64 ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ k)

theorem pack6_and (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    pack6 (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) =
      pack6 a0 a1 a2 a3 a4 a5 &&& pack6 b0 b1 b2 b3 b4 b5 := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 6
  · rw [Nat.testBit_and]
    have h1 := pack6_testBit (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) ⟨k, hk⟩
    have h2 := pack6_testBit a0 a1 a2 a3 a4 a5 ⟨k, hk⟩
    have h3 := pack6_testBit b0 b1 b2 b3 b4 b5 ⟨k, hk⟩
    dsimp only at h1 h2 h3
    rw [h1, h2, h3]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [Nat.testBit_and]
    have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5)) (pow2_ge_64 hk))
    have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt a0 a1 a2 a3 a4 a5) (pow2_ge_64 hk))
    have h3 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt b0 b1 b2 b3 b4 b5) (pow2_ge_64 hk))
    rw [h1, h2, h3]; rfl

theorem pack6_or (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    pack6 (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) =
      pack6 a0 a1 a2 a3 a4 a5 ||| pack6 b0 b1 b2 b3 b4 b5 := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 6
  · rw [Nat.testBit_or]
    have h1 := pack6_testBit (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) ⟨k, hk⟩
    have h2 := pack6_testBit a0 a1 a2 a3 a4 a5 ⟨k, hk⟩
    have h3 := pack6_testBit b0 b1 b2 b3 b4 b5 ⟨k, hk⟩
    dsimp only at h1 h2 h3
    rw [h1, h2, h3]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [Nat.testBit_or]
    have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5)) (pow2_ge_64 hk))
    have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt a0 a1 a2 a3 a4 a5) (pow2_ge_64 hk))
    have h3 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt b0 b1 b2 b3 b4 b5) (pow2_ge_64 hk))
    rw [h1, h2, h3]; rfl

theorem pack6_not (a0 a1 a2 a3 a4 a5 : Bool) :
    pack6 (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) = 63 ^^^ pack6 a0 a1 a2 a3 a4 a5 := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 6
  · rw [Nat.testBit_xor]
    have h1 := pack6_testBit (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) ⟨k, hk⟩
    have h2 := pack6_testBit a0 a1 a2 a3 a4 a5 ⟨k, hk⟩
    dsimp only at h1 h2
    rw [h1, h2]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · cases a0 <;> rfl
    · cases a1 <;> rfl
    · cases a2 <;> rfl
    · cases a3 <;> rfl
    · cases a4 <;> rfl
    · cases a5 <;> rfl
  · rw [Nat.testBit_xor]
    have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt (!a0) (!a1) (!a2) (!a3) (!a4) (!a5)) (pow2_ge_64 hk))
    have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 63 < 64) (pow2_ge_64 hk))
    have h3 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt a0 a1 a2 a3 a4 a5) (pow2_ge_64 hk))
    rw [h1, h2, h3]; rfl

def vecAt (w : Nat → List Bool) (k : Nat) : Nat :=
  pack6 ((w 0).getD k false) ((w 1).getD k false) ((w 2).getD k false) ((w 3).getD k false) ((w 4).getD k false) ((w 5).getD k false)

def stepW (w : Nat → List Bool) (g : Gate) : Nat → List Bool :=
  fun t => w t ++ [g.op.eval (g.inputs.map fun i => (w t).getD i false)]

def foldW (gs : List Gate) (w : Nat → List Bool) : Nat → List Bool :=
  fun t => gs.foldl (fun cur g => cur ++ [g.op.eval (g.inputs.map fun i => cur.getD i false)]) (w t)

theorem getD_append_single (l : List Bool) (v : Bool) (k : Nat) :
    (l ++ [v]).getD k false = if k < l.length then l.getD k false else if k = l.length then v else false := by
  by_cases hlt : k < l.length
  · simp [hlt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · by_cases heq : k = l.length
    · subst heq; simp [List.getD_eq_getElem?_getD]
    · have hgt : l.length + 1 ≤ k := by omega
      simp [hlt, heq, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (l ++ [v]).length ≤ k)]

theorem gate_vec_cases (w : Nat → List Bool) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (S : Nat) (hcov : ∀ k, hasBit S (vecAt w k) = true) (h0 : hasBit S 0 = true) (h63 : hasBit S 63 = true) :
    let v := pack6
      (g.op.eval (g.inputs.map fun i => (w 0).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 1).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 2).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 3).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 4).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 5).getD i false))
    hasBit S v = true ∨
    (g.op ≠ GateOp.not ∧ ∃ a b, a < 64 ∧ b < 64 ∧ hasBit S a = true ∧ hasBit S b = true ∧ (v = a &&& b ∨ v = a ||| b)) ∨
    (g.op = GateOp.not ∧ ∃ a, a < 64 ∧ hasBit S a = true ∧ v = 63 ^^^ a) := by
  obtain ⟨hop, hlen⟩ := hfan
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · rw [hop]
    match hg : g.inputs with
    | [] => left; simpa [GateOp.eval, pack6] using h63
    | [i] => left; simpa [GateOp.eval, vecAt] using hcov i
    | [i, j] =>
      right; left
      refine ⟨fun h => GateOp.noConfusion h, vecAt w i, vecAt w j, pack6_lt _ _ _ _ _ _, pack6_lt _ _ _ _ _ _, hcov i, hcov j, Or.inl ?_⟩
      simpa [GateOp.eval, vecAt] using pack6_and _ _ _ _ _ _ _ _ _ _ _ _
    | _ :: _ :: _ :: _ => simp [hg] at hlen
  · rw [hop]
    match hg : g.inputs with
    | [] => left; simpa [GateOp.eval, pack6] using h0
    | [i] => left; simpa [GateOp.eval, vecAt] using hcov i
    | [i, j] =>
      right; left
      refine ⟨fun h => GateOp.noConfusion h, vecAt w i, vecAt w j, pack6_lt _ _ _ _ _ _, pack6_lt _ _ _ _ _ _, hcov i, hcov j, Or.inr ?_⟩
      simpa [GateOp.eval, vecAt] using pack6_or _ _ _ _ _ _ _ _ _ _ _ _
    | _ :: _ :: _ :: _ => simp [hg] at hlen
  · rw [hop]
    match hg : g.inputs with
    | [] => left; simpa [GateOp.eval, pack6] using h63
    | i :: _ =>
      right; right
      refine ⟨rfl, vecAt w i, pack6_lt _ _ _ _ _ _, hcov i, ?_⟩
      simpa [GateOp.eval, vecAt] using pack6_not _ _ _ _ _ _

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem notCount_cons (g : Gate) (rest : List Gate) :
    PEqualNP.NotBracket.notCount ⟨g :: rest, 0⟩ =
      (if isNotOp g.op then 1 else 0) + PEqualNP.NotBracket.notCount ⟨rest, 0⟩ := by
  rcases g with ⟨op, inputs⟩
  unfold PEqualNP.NotBracket.notCount
  cases op with
  | not =>
    have h : @decide (GateOp.not = GateOp.not) (lineDegreeGateOpDecEq GateOp.not GateOp.not) = true := rfl
    rw [List.filter_cons, h]
    simp only [ite_true, List.length_cons, isNotOp, Nat.add_comm]
  | and =>
    have h : @decide (GateOp.and = GateOp.not) (lineDegreeGateOpDecEq GateOp.and GateOp.not) = false := rfl
    simp only [List.filter_cons, h, isNotOp, Bool.false_eq_true, ite_false, Nat.zero_add]
  | or =>
    have h : @decide (GateOp.or = GateOp.not) (lineDegreeGateOpDecEq GateOp.or GateOp.not) = false := rfl
    simp only [List.filter_cons, h, isNotOp, Bool.false_eq_true, ite_false, Nat.zero_add]
  | mod m =>
    have h : @decide (GateOp.mod m = GateOp.not) (lineDegreeGateOpDecEq (GateOp.mod m) GateOp.not) = false := rfl
    simp only [List.filter_cons, h, isNotOp, Bool.false_eq_true, ite_false, Nat.zero_add]
  | maj =>
    have h : @decide (GateOp.maj = GateOp.not) (lineDegreeGateOpDecEq GateOp.maj GateOp.not) = false := rfl
    simp only [List.filter_cons, h, isNotOp, Bool.false_eq_true, ite_false, Nat.zero_add]

theorem foldW_to_canReach {A B C : Nat} (hA : A < 64) (hB : B < 64) (hC : C < 64) :
    ∀ (gs : List Gate) (w : Nat → List Bool) (len S : Nat),
      (∀ t, (w t).length = len) →
      (∀ k, hasBit S (vecAt w k) = true) →
      hasBit S 0 = true → hasBit S 63 = true →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∃ p q r : Nat,
        (∀ t : Fin 6, (foldW gs w t.val).getD p false = A.testBit t.val) ∧
        (∀ t : Fin 6, (foldW gs w t.val).getD q false = B.testBit t.val) ∧
        (∀ t : Fin 6, (foldW gs w t.val).getD r false = C.testBit t.val)) →
      CanReach A B C gs.length (PEqualNP.NotBracket.notCount ⟨gs, 0⟩) S := by
  intro gs
  induction gs with
  | nil =>
    intro w len S _ hcov _ _ _ ⟨p, q, r, hp, hq, hr⟩
    have eqV (k V : Nat) (hV : V < 64) (hk : ∀ t : Fin 6, (w t.val).getD k false = V.testBit t.val) :
        vecAt w k = V := by
      apply Nat.eq_of_testBit_eq; intro j
      by_cases hj : j < 6
      · have h012345 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases h012345 with rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨0, by decide⟩] using hk ⟨0, by decide⟩
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨1, by decide⟩] using hk ⟨1, by decide⟩
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨2, by decide⟩] using hk ⟨2, by decide⟩
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨3, by decide⟩] using hk ⟨3, by decide⟩
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨4, by decide⟩] using hk ⟨4, by decide⟩
        · simpa [vecAt, pack6_testBit _ _ _ _ _ _ ⟨5, by decide⟩] using hk ⟨5, by decide⟩
      · unfold vecAt
        have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (pack6_lt ((w 0).getD k false) ((w 1).getD k false) ((w 2).getD k false) ((w 3).getD k false) ((w 4).getD k false) ((w 5).getD k false)) (pow2_ge_64 hj))
        have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hV (pow2_ge_64 hj))
        rw [h1, h2]
    have hSA : hasBit S A = true := eqV p A hA hp ▸ hcov p
    have hSB : hasBit S B = true := eqV q B hB hq ▸ hcov q
    have hSC : hasBit S C = true := eqV r C hC hr ▸ hcov r
    exact CanReach.hit hSA hSB hSC
  | cons g rest ih =>
    intro w len S hlen hcov h0 h63 hfan hhit
    have hfg := hfan g List.mem_cons_self
    have hfr : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    have hlen' : ∀ t, (stepW w g t).length = len + 1 := fun t => by simp [stepW, hlen t]
    have hfold_eq : foldW (g :: rest) w = foldW rest (stepW w g) := rfl
    rw [hfold_eq] at hhit
    set v := pack6
      (g.op.eval (g.inputs.map fun i => (w 0).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 1).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 2).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 3).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 4).getD i false))
      (g.op.eval (g.inputs.map fun i => (w 5).getD i false))
    have hcov' : ∀ k, hasBit (setBit S v) (vecAt (stepW w g) k) = true := by
      intro k
      have hk : vecAt (stepW w g) k = if k < len then vecAt w k else if k = len then v else 0 := by
        unfold vecAt stepW
        simp only [getD_append_single, hlen]
        split_ifs <;> rfl
      rw [hk]
      split_ifs
      · rw [hasBit_setBit, hcov k]; rfl
      · rw [hasBit_setBit, Nat.beq_refl]; simp
      · rw [hasBit_setBit, h0]; rfl
    have h0' : hasBit (setBit S v) 0 = true := by rw [hasBit_setBit, h0]; rfl
    have h63' : hasBit (setBit S v) 63 = true := by rw [hasBit_setBit, h63]; rfl
    have hsub := ih (stepW w g) (len + 1) (setBit S v) hlen' hcov' h0' h63' hfr hhit
    rw [notCount_cons, List.length_cons]
    have hcases := gate_vec_cases w g hfg S hcov h0 h63
    change hasBit S v = true ∨
      (g.op ≠ GateOp.not ∧ ∃ a b, a < 64 ∧ b < 64 ∧ hasBit S a = true ∧ hasBit S b = true ∧ (v = a &&& b ∨ v = a ||| b)) ∨
      (g.op = GateOp.not ∧ ∃ a, a < 64 ∧ hasBit S a = true ∧ v = 63 ^^^ a) at hcases
    rcases hcases with hvS | ⟨hnot, a, b, ha, hb, hsa, hsb, hveq⟩ | ⟨hnot, a, ha, hsa, hveq⟩
    · rw [setBit_of_hasBit hvS] at hsub
      cases h : isNotOp g.op
      · simp only [Bool.false_eq_true, ite_false, Nat.zero_add]; exact CanReach.noop hsub
      · simp only [ite_true, Nat.add_comm 1]; exact CanReach.noopNot hsub
    · have hnf : isNotOp g.op = false := by cases h : g.op <;> simp_all [isNotOp]
      simp only [hnf, Bool.false_eq_true, ite_false, Nat.zero_add]
      rcases hveq with hve | hve
      · rw [hve] at hsub; exact CanReach.stepAnd ha hb hsa hsb hsub
      · rw [hve] at hsub; exact CanReach.stepOr ha hb hsa hsb hsub
    · simp only [hnot, isNotOp, ite_true, Nat.add_comm 1]
      rw [hveq] at hsub
      exact CanReach.stepNot ha hsa hsub

theorem threeout6_lb_main {A B C N : Nat} {layers : Nat → Nat → NTree}
    (hA : A < 64) (hB : B < 64) (hC : C < 64)
    (hinit : memTree initMask (layers N 2) = true)
    (hall : checkAllLayers A B C layers N = true) :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ N ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (A : Nat).testBit t.val ∧
        w.getD q.val false = (B : Nat).testBit t.val ∧
        w.getD r.val false = (C : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, _, hnc, hsz, heval⟩
  have hcov0 : ∀ k, hasBit initMask (vecAt inRow k) = true := by
    intro k
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
    | k' + 7 =>
      have hv0 : vecAt inRow (k' + 7) = 0 := by rfl
      rw [hv0]; decide
  have hhit : ∃ p' q' r' : Nat,
      (∀ t : Fin 6, (foldW D.gates inRow t.val).getD p' false = A.testBit t.val) ∧
      (∀ t : Fin 6, (foldW D.gates inRow t.val).getD q' false = B.testBit t.val) ∧
      (∀ t : Fin 6, (foldW D.gates inRow t.val).getD r' false = C.testBit t.val) := by
    refine ⟨p.val, q.val, r.val, ?_, ?_, ?_⟩
    · intro t; have ht := heval t; rw [inRow_eq t] at ht; exact ht.1
    · intro t; have ht := heval t; rw [inRow_eq t] at ht; exact ht.2.1
    · intro t; have ht := heval t; rw [inRow_eq t] at ht; exact ht.2.2
  have hreach := foldW_to_canReach hA hB hC D.gates inRow 7 initMask
    (fun t => by rfl) hcov0 (by decide) (by decide) hfan hhit
  have hnc' : PEqualNP.NotBracket.notCount ⟨D.gates, 0⟩ ≤ 2 := hnc
  have hsz' : D.gates.length ≤ N := hsz
  exact checkAllLayers_sound hall D.gates.length N 2 initMask
    (Nat.le_refl N) (Nat.le_refl 2) hinit hsz' (PEqualNP.NotBracket.notCount ⟨D.gates, 0⟩) hnc' hreach

def lay_0_0 : NTree := NTree.leaf
def lay_0_1 : NTree := NTree.leaf
def lay_0_2 : NTree := NTree.leaf
def lay_1_0 : NTree := NTree.leaf
def lay_1_1 : NTree := NTree.leaf
def lay_1_2 : NTree := NTree.leaf
def lay_2_0 : NTree := NTree.leaf
def lay_2_1 : NTree := NTree.leaf
def lay_2_2 : NTree := NTree.leaf
def lay_3_0 : NTree := NTree.node 0xd101000980000009 (NTree.node 0xd101000180010009 (NTree.node 0xd101000100009003 (NTree.node 0xd10100010000800d (NTree.node 0xd101000100000099 (NTree.node 0xd10100010000008d (NTree.node 0xd10100010000000f (NTree.leaf) (NTree.leaf)) (NTree.node 0xd101000100000093 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd1010001000000c9 (NTree.node 0xd1010001000000c3 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000100008103 (NTree.node 0xd1010001000080c1 (NTree.node 0xd101000100008091 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000100008181 (NTree.node 0xd101000100008109 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xd101000180000091 (NTree.node 0xd10100010000c009 (NTree.node 0xd101000100009081 (NTree.node 0xd101000100009009 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd10100010000c003 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd10100018000000d (NTree.node 0xd10100010000c081 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000180009001 (NTree.node 0xd101000180008101 (NTree.node 0xd1010001800000c1 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000180010003 (NTree.node 0xd10100018000c001 (NTree.leaf) (NTree.leaf)) (NTree.leaf))))) (NTree.node 0xd1010001c0000081 (NTree.node 0xd101000190000003 (NTree.node 0xd101000181000009 (NTree.node 0xd101000180018001 (NTree.node 0xd101000180010081 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd101000181000003 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd101000181008001 (NTree.node 0xd101000181000081 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000190008001 (NTree.node 0xd101000190000081 (NTree.node 0xd101000190000009 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd1010001c0000009 (NTree.node 0xd1010001c0000003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xd101000380000003 (NTree.node 0xd101000300000083 (NTree.node 0xd10100030000000b (NTree.node 0xd1010001c0008001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000340000003 (NTree.node 0xd101000300008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000900000089 (NTree.node 0xd10100090000000b (NTree.node 0xd1010003c0000001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000910000009 (NTree.node 0xd101000900008009 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))))) (NTree.node 0xd109000180000009 (NTree.node 0xd101800180010001 (NTree.node 0xd101008181000001 (NTree.node 0xd101008100008081 (NTree.node 0xd101008100000083 (NTree.node 0xd101000990000001 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd101008100000089 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd101008180000081 (NTree.node 0xd101008101000081 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101800100008081 (NTree.node 0xd101800100008009 (NTree.node 0xd101800100008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101800180008001 (NTree.node 0xd101800100018001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xd103000180000003 (NTree.node 0xd103000100004003 (NTree.node 0xd103000100000083 (NTree.node 0xd10300010000000b (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd10300010000c001 (NTree.node 0xd103000100008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd109000100001009 (NTree.node 0xd109000100000089 (NTree.node 0xd10900010000000b (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd109000100009001 (NTree.node 0xd109000100008009 (NTree.leaf) (NTree.leaf)) (NTree.leaf))))) (NTree.node 0xd90100010000000b (NTree.node 0xd30100010000000b (NTree.node 0xd181000100008081 (NTree.node 0xd181000100000089 (NTree.node 0xd181000100000083 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd181000100000181 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd181000180000081 (NTree.node 0xd181000100008101 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd3010001000000c1 (NTree.node 0xd301000100000083 (NTree.node 0xd301000100000043 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd301000180000003 (NTree.node 0xd301000100008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xf101000100000007 (NTree.node 0xd901000100000091 (NTree.node 0xd901000100000089 (NTree.node 0xd901000100000019 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd901000180000009 (NTree.node 0xd901000100008009 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xf101000100000083 (NTree.node 0xf10100010000000d (NTree.node 0xf10100010000000b (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xf101000180000003 (NTree.node 0xf101000100008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf))))))
def lay_3_1 : NTree := NTree.node 0xd101810100008001 (NTree.node 0xd101000d00000009 (NTree.node 0xd101000191000001 (NTree.node 0xd10100010000d001 (NTree.node 0xd101000100009101 (NTree.node 0xd1010001000000d1 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd10100010000c101 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd101000190010001 (NTree.node 0xd101000181010001 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd1010001d0000001 (NTree.node 0xd1010001c1000001 (NTree.node 0xd1010001c0010001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd10100090000000d (NTree.node 0xd10100050000000d (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xd101010100008101 (NTree.node 0xd1010081000000c1 (NTree.node 0xd1010041000000c1 (NTree.node 0xd101001100000091 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd101008100000091 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd10100c100000081 (NTree.node 0xd101009100000081 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101800100008101 (NTree.node 0xd10140010000c001 (NTree.node 0xd101100100009001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd10180010000c001 (NTree.node 0xd101800100009001 (NTree.leaf) (NTree.leaf)) (NTree.leaf))))) (NTree.node 0xd191000100000081 (NTree.node 0xd10d000100000009 (NTree.node 0xd10500010000000d (NTree.node 0xd101c00100008001 (NTree.node 0xd101900100008001 (NTree.leaf) (NTree.leaf)) (NTree.node 0xd103000300000003 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd109000900000009 (NTree.node 0xd10900010000000d (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd181000100000091 (NTree.node 0xd1410001000000c1 (NTree.node 0xd111000100000091 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd181008100000081 (NTree.node 0xd1810001000000c1 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))) (NTree.node 0xd901000900000009 (NTree.node 0xd303000100000003 (NTree.node 0xd301000300000003 (NTree.node 0xd1c1000100000081 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd90100010000000d (NTree.node 0xd50100010000000d (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xf101000300000003 (NTree.node 0xdd01000100000009 (NTree.node 0xd909000100000009 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xf301000100000003 (NTree.node 0xf103000100000003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)))))
def lay_3_2 : NTree := NTree.leaf
def lay_4_0 : NTree := NTree.node 0xd101000100008081 (NTree.node 0xd101000100000089 (NTree.node 0xd101000100000083 (NTree.node 0xd10100010000000b (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000100008009 (NTree.node 0xd101000100008003 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000180000081 (NTree.node 0xd101000180000009 (NTree.node 0xd101000180000003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000180008001 (NTree.leaf) (NTree.leaf)))
def lay_4_1 : NTree := NTree.node 0xd101000300000003 (NTree.node 0xd10100010000c001 (NTree.node 0xd1010001000000c1 (NTree.node 0xd101000100000091 (NTree.node 0xd10100010000000d (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000100009001 (NTree.node 0xd101000100008101 (NTree.leaf) (NTree.leaf)) (NTree.leaf))) (NTree.node 0xd101000190000001 (NTree.node 0xd101000181000001 (NTree.node 0xd101000180010001 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd1010001c0000001 (NTree.leaf) (NTree.leaf)))) (NTree.node 0xd109000100000009 (NTree.node 0xd101800100008001 (NTree.node 0xd101008100000081 (NTree.node 0xd101000900000009 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd103000100000003 (NTree.leaf) (NTree.leaf))) (NTree.node 0xd901000100000009 (NTree.node 0xd301000100000003 (NTree.node 0xd181000100000081 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xf101000100000003 (NTree.leaf) (NTree.leaf))))
def lay_4_2 : NTree := NTree.leaf
def lay_5_0 : NTree := NTree.leaf
def lay_5_1 : NTree := NTree.node 0xd101000100000081 (NTree.node 0xd101000100000009 (NTree.node 0xd101000100000003 (NTree.leaf) (NTree.leaf)) (NTree.leaf)) (NTree.node 0xd101000180000001 (NTree.node 0xd101000100008001 (NTree.leaf) (NTree.leaf)) (NTree.leaf))
def lay_5_2 : NTree := NTree.leaf
def lay_6_0 : NTree := NTree.leaf
def lay_6_1 : NTree := NTree.leaf
def lay_6_2 : NTree := NTree.node 0xd101000100000001 (NTree.leaf) (NTree.leaf)
def layersFn : Nat → Nat → NTree
  | 0, 0 => lay_0_0
  | 0, 1 => lay_0_1
  | 0, 2 => lay_0_2
  | 1, 0 => lay_1_0
  | 1, 1 => lay_1_1
  | 1, 2 => lay_1_2
  | 2, 0 => lay_2_0
  | 2, 1 => lay_2_1
  | 2, 2 => lay_2_2
  | 3, 0 => lay_3_0
  | 3, 1 => lay_3_1
  | 3, 2 => lay_3_2
  | 4, 0 => lay_4_0
  | 4, 1 => lay_4_1
  | 4, 2 => lay_4_2
  | 5, 0 => lay_5_0
  | 5, 1 => lay_5_1
  | 5, 2 => lay_5_2
  | 6, 0 => lay_6_0
  | 6, 1 => lay_6_1
  | 6, 2 => lay_6_2
  | _, _ => NTree.leaf

set_option maxHeartbeats 0 in
theorem all_ok : checkAllLayers 10 42 43 layersFn 6 = true := by decide +kernel

theorem init_ok : memTree initMask (layersFn 6 2) = true := by decide +kernel

end PEqualNP.Outside.L_meta_51308

theorem PEqualNP.Outside.L_meta_51308 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (42 : Nat).testBit t.val ∧
    w.getD r.val false = (43 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_51308.threeout6_lb_main (by decide) (by decide) (by decide) PEqualNP.Outside.L_meta_51308.init_ok PEqualNP.Outside.L_meta_51308.all_ok
