import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50928

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.NotBracket

def initBank : List ℕ := [0, 32, 48, 56, 60, 62, 63]

def insSorted (m : ℕ) : List ℕ → List ℕ
  | [] => [m]
  | x :: xs => if m < x then m :: x :: xs else if m = x then x :: xs else x :: insSorted m xs

def putMask (m : ℕ) (a : List ℕ) : List ℕ :=
  if m ∈ initBank ∨ m ∈ a then a else insSorted m a

def miss (a : List ℕ) : ℕ :=
  (if 10 ∈ a then 0 else 1) + (if 40 ∈ a then 0 else 1) + (if 46 ∈ a then 0 else 1)

def hasDom (bs : List (List ℕ × ℕ)) (a : List ℕ) (u : ℕ) : Bool :=
  bs.any fun p => decide (p.1 = a ∧ p.2 ≤ u)

def checkNext (bs : List (List ℕ × ℕ)) (rem : ℕ) (na : List ℕ) (nu : ℕ) : Bool :=
  if miss na ≤ rem then hasDom bs na nu else true

def pairsOK (bs : List (List ℕ × ℕ)) (rem : ℕ) (a : List ℕ) (u : ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs =>
    xs.all (fun y =>
      checkNext bs rem (putMask (x &&& y) a) u &&
      checkNext bs rem (putMask (x ||| y) a) u) &&
    pairsOK bs rem a u xs

def stateOK (bs : List (List ℕ × ℕ)) (rem : ℕ) (p : List ℕ × ℕ) : Bool :=
  let a := p.1
  let u := p.2
  let bank := initBank ++ a
  checkNext bs rem a u &&
  (if u < 2 then bank.all (fun x => checkNext bs rem (putMask (63 - x) a) (u + 1)) else true) &&
  pairsOK bs rem a u bank

def layerOK (cur nxt : List (List ℕ × ℕ)) (rem : ℕ) : Bool :=
  cur.all (stateOK nxt rem)

def B0 : List (List ℕ × ℕ) := [
  ([], 0)
]

def B1 : List (List ℕ × ℕ) := [
  ([], 0), ([1], 1), ([3], 1), ([7], 1), ([15], 1), ([31], 1)
]

def B2 : List (List ℕ × ℕ) := [
  ([], 0), ([1], 1), ([1,3], 2), ([1,7], 2), ([1,15], 2), ([1,31], 2),
  ([1,33], 1), ([1,49], 1), ([1,57], 1), ([1,61], 1), ([2,3], 1), ([3], 1),
  ([3,7], 2), ([3,15], 2), ([3,31], 2), ([3,35], 1), ([3,51], 1), ([3,59], 1),
  ([4,7], 1), ([6,7], 1), ([7], 1), ([7,15], 2), ([7,31], 2), ([7,39], 1),
  ([7,55], 1), ([8,15], 1), ([12,15], 1), ([14,15], 1), ([15], 1), ([15,31], 2),
  ([15,47], 1), ([16,31], 1), ([24,31], 1), ([28,31], 1), ([30,31], 1), ([31], 1)
]

def B3 : List (List ℕ × ℕ) := [
  ([], 0), ([1], 1), ([1,2,3], 2), ([1,2,61], 2), ([1,3], 2), ([1,3,33], 2),
  ([1,3,35], 2), ([1,3,49], 2), ([1,3,51], 2), ([1,3,57], 2), ([1,3,59], 2), ([1,3,61], 2),
  ([1,4,7], 2), ([1,6,7], 2), ([1,6,57], 2), ([1,7], 2), ([1,7,33], 2), ([1,7,39], 2),
  ([1,7,49], 2), ([1,7,55], 2), ([1,7,57], 2), ([1,7,61], 2), ([1,8,15], 2), ([1,12,15], 2),
  ([1,14,15], 2), ([1,14,49], 2), ([1,15], 2), ([1,15,33], 2), ([1,15,47], 2), ([1,15,49], 2),
  ([1,15,57], 2), ([1,15,61], 2), ([1,16,31], 2), ([1,24,31], 2), ([1,28,31], 2), ([1,30,31], 2),
  ([1,30,33], 2), ([1,31], 2), ([1,31,33], 2), ([1,31,49], 2), ([1,31,57], 2), ([1,31,61], 2),
  ([1,33], 1), ([1,33,49], 1), ([1,33,57], 1), ([1,33,61], 1), ([1,49], 1), ([1,49,57], 1),
  ([1,49,61], 1), ([1,57], 1), ([1,57,61], 1), ([1,61], 1), ([2,3], 1), ([2,3,7], 2),
  ([2,3,15], 2), ([2,3,31], 2), ([2,3,34], 1), ([2,3,35], 1), ([2,3,50], 1), ([2,3,51], 1),
  ([2,3,58], 1), ([2,3,59], 1), ([2,3,61], 2), ([3], 1), ([3,4,7], 2), ([3,4,59], 2),
  ([3,6,7], 2), ([3,7], 2), ([3,7,35], 2), ([3,7,39], 2), ([3,7,51], 2), ([3,7,55], 2),
  ([3,7,59], 2), ([3,8,15], 2), ([3,12,15], 2), ([3,12,51], 2), ([3,14,15], 2), ([3,15], 2),
  ([3,15,35], 2), ([3,15,47], 2), ([3,15,51], 2), ([3,15,59], 2), ([3,16,31], 2), ([3,24,31], 2),
  ([3,28,31], 2), ([3,28,35], 2), ([3,30,31], 2), ([3,31], 2), ([3,31,35], 2), ([3,31,51], 2),
  ([3,31,59], 2), ([3,34,35], 1), ([3,35], 1), ([3,35,51], 1), ([3,35,59], 1), ([3,50,51], 1),
  ([3,51], 1), ([3,51,59], 1), ([3,58,59], 1), ([3,59], 1), ([4,6,7], 1), ([4,7], 1),
  ([4,7,15], 2), ([4,7,31], 2), ([4,7,36], 1), ([4,7,39], 1), ([4,7,52], 1), ([4,7,55], 1),
  ([4,7,59], 2), ([6,7], 1), ([6,7,15], 2), ([6,7,31], 2), ([6,7,38], 1), ([6,7,39], 1),
  ([6,7,54], 1), ([6,7,55], 1), ([6,7,57], 2), ([7], 1), ([7,8,15], 2), ([7,8,55], 2),
  ([7,12,15], 2), ([7,14,15], 2), ([7,15], 2), ([7,15,39], 2), ([7,15,47], 2), ([7,15,55], 2),
  ([7,16,31], 2), ([7,24,31], 2), ([7,24,39], 2), ([7,28,31], 2), ([7,30,31], 2), ([7,31], 2),
  ([7,31,39], 2), ([7,31,55], 2), ([7,36,39], 1), ([7,38,39], 1), ([7,39], 1), ([7,39,55], 1),
  ([7,52,55], 1), ([7,54,55], 1), ([7,55], 1), ([8,12,15], 1), ([8,14,15], 1), ([8,15], 1),
  ([8,15,31], 2), ([8,15,40], 1), ([8,15,47], 1), ([8,15,55], 2), ([12,14,15], 1), ([12,15], 1),
  ([12,15,31], 2), ([12,15,44], 1), ([12,15,47], 1), ([12,15,51], 2), ([14,15], 1), ([14,15,31], 2),
  ([14,15,46], 1), ([14,15,47], 1), ([14,15,49], 2), ([15], 1), ([15,16,31], 2), ([15,16,47], 2),
  ([15,24,31], 2), ([15,28,31], 2), ([15,30,31], 2), ([15,31], 2), ([15,31,47], 2), ([15,40,47], 1),
  ([15,44,47], 1), ([15,46,47], 1), ([15,47], 1), ([16,24,31], 1), ([16,28,31], 1), ([16,30,31], 1),
  ([16,31], 1), ([16,31,47], 2), ([24,28,31], 1), ([24,30,31], 1), ([24,31], 1), ([24,31,39], 2),
  ([28,30,31], 1), ([28,31], 1), ([28,31,35], 2), ([30,31], 1), ([30,31,33], 2), ([31], 1)
]

def B4 : List (List ℕ × ℕ) := [
  ([1,8,15,40], 2), ([1,14,15,46], 2), ([1,14,46,49], 2), ([1,15,40,47], 2), ([1,15,46,47], 2), ([3,8,15,40], 2),
  ([3,14,15,46], 2), ([3,15,40,47], 2), ([3,15,46,47], 2), ([7,8,15,40], 2), ([7,8,40,55], 2), ([7,14,15,46], 2),
  ([7,15,40,47], 2), ([7,15,46,47], 2), ([8,12,15,40], 1), ([8,14,15,40], 1), ([8,14,15,46], 1), ([8,15,23,40], 2),
  ([8,15,31,40], 2), ([8,15,40], 1), ([8,15,40,47], 1), ([8,15,40,55], 2), ([8,15,46,47], 1), ([12,14,15,46], 1),
  ([12,15,40,44], 1), ([12,15,40,47], 1), ([12,15,46,47], 1), ([14,15,17,46], 2), ([14,15,31,46], 2), ([14,15,40,46], 1),
  ([14,15,40,47], 1), ([14,15,44,46], 1), ([14,15,46], 1), ([14,15,46,47], 1), ([14,15,46,49], 2), ([15,16,40,47], 2),
  ([15,16,46,47], 2), ([15,17,46,47], 2), ([15,23,40,47], 2), ([15,31,40,47], 2), ([15,31,46,47], 2), ([15,40,44,47], 1),
  ([15,40,46,47], 1), ([15,40,47], 1), ([15,44,46,47], 1), ([15,46,47], 1), ([16,31,40,47], 2), ([16,31,46,47], 2)
]

def B5 : List (List ℕ × ℕ) := [
  ([1,14,15,40,46], 2), ([1,14,40,46,49], 2), ([1,15,40,46,47], 2), ([3,14,15,40,46], 2), ([3,15,40,46,47], 2), ([7,14,15,40,46], 2),
  ([7,15,40,46,47], 2), ([8,14,15,40,46], 1), ([8,15,40,46,47], 1), ([12,14,15,40,46], 1), ([12,15,40,46,47], 1), ([14,15,17,40,46], 2),
  ([14,15,23,40,46], 2), ([14,15,31,40,46], 2), ([14,15,40,44,46], 1), ([14,15,40,46], 1), ([14,15,40,46,47], 1), ([14,15,40,46,49], 2),
  ([15,16,40,46,47], 2), ([15,17,40,46,47], 2), ([15,23,40,46,47], 2), ([15,31,40,46,47], 2), ([15,40,44,46,47], 1), ([15,40,46,47], 1),
  ([16,31,40,46,47], 2)
]

def B : ℕ → List (List ℕ × ℕ)
  | 0 => B0
  | 1 => B1
  | 2 => B2
  | 3 => B3
  | 4 => B4
  | 5 => B5
  | _ => []

lemma ok0 : layerOK B0 B1 5 = true := by decide +kernel
lemma ok1 : layerOK B1 B2 4 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
lemma ok2 : layerOK B2 B3 3 = true := by decide +kernel
set_option maxHeartbeats 2000000 in
lemma ok3 : layerOK B3 B4 2 = true := by decide +kernel
lemma ok4 : layerOK B4 B5 1 = true := by decide +kernel
lemma ok5 : layerOK B5 [] 0 = true := by decide +kernel

lemma noHit0 : B0.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel
lemma noHit1 : B1.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel
lemma noHit2 : B2.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel
lemma noHit3 : B3.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel
lemma noHit4 : B4.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel
lemma noHit5 : B5.all (fun p => decide (0 < miss p.1)) = true := by decide +kernel

lemma layerOK_all (k : ℕ) (hk : k < 6) : layerOK (B k) (B (k + 1)) (5 - k) = true := by
  interval_cases k
  · exact ok0
  · exact ok1
  · exact ok2
  · exact ok3
  · exact ok4
  · exact ok5

lemma noHit_all (k : ℕ) (p : List ℕ × ℕ) (hp : p ∈ B k) : 0 < miss p.1 := by
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k
    · exact of_decide_eq_true (List.all_eq_true.mp noHit0 p hp)
    · exact of_decide_eq_true (List.all_eq_true.mp noHit1 p hp)
    · exact of_decide_eq_true (List.all_eq_true.mp noHit2 p hp)
    · exact of_decide_eq_true (List.all_eq_true.mp noHit3 p hp)
    · exact of_decide_eq_true (List.all_eq_true.mp noHit4 p hp)
    · exact of_decide_eq_true (List.all_eq_true.mp noHit5 p hp)
  · have hB : B k = [] := by
      rcases k with _ | _ | _ | _ | _ | _ | k' <;> first | omega | rfl
    rw [hB] at hp
    cases hp

lemma mem_insSorted (m x : ℕ) (xs : List ℕ) : x ∈ insSorted m xs ↔ x = m ∨ x ∈ xs := by
  induction xs with
  | nil => simp [insSorted]
  | cons y ys ih =>
    unfold insSorted
    split_ifs with h1 h2
    · simp
    · subst h2
      simp only [List.mem_cons]
      tauto
    · simp only [List.mem_cons, ih]
      tauto

lemma putMask_of_mem (m : ℕ) (a : List ℕ) (h : m ∈ initBank ++ a) : putMask m a = a := by
  unfold putMask
  rw [List.mem_append] at h
  simp [h]

lemma mem_putMask (m x : ℕ) (a : List ℕ) :
    x ∈ initBank ++ putMask m a ↔ x = m ∨ x ∈ initBank ++ a := by
  unfold putMask
  split_ifs with hm
  · simp only [List.mem_append]
    constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h)
      · exact hm
      · exact h
  · simp only [List.mem_append, mem_insSorted]
    tauto

lemma mem_putMask_only (m x : ℕ) (a : List ℕ) (h : x ∈ putMask m a) : x = m ∨ x ∈ a := by
  unfold putMask at h
  split_ifs at h with hm
  · exact Or.inr h
  · exact (mem_insSorted m x a).mp h

lemma miss_le_putMask_succ (m : ℕ) (a : List ℕ) : miss a ≤ miss (putMask m a) + 1 := by
  unfold miss
  have h10 : 10 ∈ putMask m a → m = 10 ∨ 10 ∈ a := fun h =>
    (mem_putMask_only m 10 a h).imp Eq.symm id
  have h40 : 40 ∈ putMask m a → m = 40 ∨ 40 ∈ a := fun h =>
    (mem_putMask_only m 40 a h).imp Eq.symm id
  have h46 : 46 ∈ putMask m a → m = 46 ∨ 46 ∈ a := fun h =>
    (mem_putMask_only m 46 a h).imp Eq.symm id
  by_cases a10 : 10 ∈ a <;> by_cases a40 : 40 ∈ a <;> by_cases a46 : 46 ∈ a <;>
    by_cases b10 : 10 ∈ putMask m a <;> by_cases b40 : 40 ∈ putMask m a <;>
    by_cases b46 : 46 ∈ putMask m a <;>
    simp only [a10, a40, a46, b10, b40, b46, ↓reduceIte] <;>
    try omega
  all_goals
    first
    | (have e1 := (h10 b10).resolve_right a10; have e2 := (h40 b40).resolve_right a40; omega)
    | (have e1 := (h10 b10).resolve_right a10; have e2 := (h46 b46).resolve_right a46; omega)
    | (have e1 := (h40 b40).resolve_right a40; have e2 := (h46 b46).resolve_right a46; omega)

lemma hasDom_spec (bs : List (List ℕ × ℕ)) (a : List ℕ) (u : ℕ)
    (h : hasDom bs a u = true) : ∃ u' ≤ u, (a, u') ∈ bs := by
  unfold hasDom at h
  obtain ⟨⟨a', u'⟩, hmem, hdec⟩ := List.any_eq_true.mp h
  obtain ⟨rfl, hle⟩ := of_decide_eq_true hdec
  exact ⟨u', hle, hmem⟩

lemma checkNext_spec (bs : List (List ℕ × ℕ)) (rem : ℕ) (na : List ℕ) (nu : ℕ)
    (h : checkNext bs rem na nu = true) (hm : miss na ≤ rem) :
    ∃ u' ≤ nu, (na, u') ∈ bs := by
  unfold checkNext at h
  rw [ite_eq_left hm] at h
  exact hasDom_spec bs na nu h

lemma pairsOK_spec (bs : List (List ℕ × ℕ)) (rem : ℕ) (a : List ℕ) (u : ℕ)
    (hstay : checkNext bs rem a u = true) :
    ∀ (l : List ℕ), (∀ z ∈ l, z ∈ initBank ++ a) → pairsOK bs rem a u l = true →
      ∀ x ∈ l, ∀ y ∈ l,
        (miss (putMask (x &&& y) a) ≤ rem → ∃ u' ≤ u, (putMask (x &&& y) a, u') ∈ bs) ∧
        (miss (putMask (x ||| y) a) ≤ rem → ∃ u' ≤ u, (putMask (x ||| y) a, u') ∈ bs) := by
  intro l
  induction l with
  | nil => intro _ _ x hx; cases hx
  | cons z zs ih =>
    intro hsub h x hx y hy
    simp only [pairsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ w ∈ zs, checkNext bs rem (putMask (z &&& w) a) u = true ∧
        checkNext bs rem (putMask (z ||| w) a) u = true := by
      intro w hw
      have := List.all_eq_true.mp h1 w hw
      simpa [Bool.and_eq_true] using this
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · have hz : y ∈ initBank ++ a := hsub y List.mem_cons_self
      constructor
      · intro hm
        rw [Nat.and_self, putMask_of_mem y a hz] at hm ⊢
        exact checkNext_spec bs rem a u hstay hm
      · intro hm
        rw [Nat.or_self, putMask_of_mem y a hz] at hm ⊢
        exact checkNext_spec bs rem a u hstay hm
    · exact ⟨fun hm => checkNext_spec bs rem _ u (h1' y hy').1 hm,
             fun hm => checkNext_spec bs rem _ u (h1' y hy').2 hm⟩
    · exact ⟨fun hm => by rw [Nat.and_comm] at hm ⊢; exact checkNext_spec bs rem _ u (h1' x hx').1 hm,
             fun hm => by rw [Nat.or_comm] at hm ⊢; exact checkNext_spec bs rem _ u (h1' x hx').2 hm⟩
    · exact ih (fun w hw => hsub w (List.mem_cons_of_mem z hw)) h2 x hx' y hy'

def xsVec (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

def pack6 (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
  (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)

def packBits (f : Fin 6 → Bool) : ℕ :=
  pack6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)

lemma pack6_lt (b0 b1 b2 b3 b4 b5 : Bool) : pack6 b0 b1 b2 b3 b4 b5 < 64 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

lemma packBits_lt (f : Fin 6 → Bool) : packBits f < 64 :=
  pack6_lt (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)

lemma pack6_testBit (b0 b1 b2 b3 b4 b5 : Bool) (t : Fin 6) :
    (pack6 b0 b1 b2 b3 b4 b5).testBit t.val =
      match t.val with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | 3 => b3
      | 4 => b4
      | _ => b5 := by
  revert b0 b1 b2 b3 b4 b5 t
  decide

lemma testBit_packBits (f : Fin 6 → Bool) (k : ℕ) :
    (packBits f).testBit k = if h : k < 6 then f ⟨k, h⟩ else false := by
  by_cases hk : k < 6
  · rw [dite_eq_left hk]
    have h := pack6_testBit (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) ⟨k, hk⟩
    unfold packBits
    rw [h]
    interval_cases k <;> rfl
  · rw [dite_eq_right hk]
    apply Nat.testBit_lt_two_pow
    have hlt : packBits f < 2 ^ 6 := packBits_lt f
    have hpow : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega

lemma packBits_and (f g : Fin 6 → Bool) :
    packBits (fun t => f t && g t) = packBits f &&& packBits g := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, testBit_packBits, testBit_packBits, testBit_packBits]
  split_ifs <;> simp

lemma packBits_or (f g : Fin 6 → Bool) :
    packBits (fun t => f t || g t) = packBits f ||| packBits g := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, testBit_packBits, testBit_packBits, testBit_packBits]
  split_ifs <;> simp

lemma sub63_testBit (m : Fin 64) (t : Fin 6) :
    (63 - m.val).testBit t.val = !(m.val.testBit t.val) := by
  revert m t
  decide

lemma packBits_not (f : Fin 6 → Bool) :
    packBits (fun t => !(f t)) = 63 - packBits f := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_packBits]
  by_cases hk : k < 6
  · rw [dite_eq_left hk]
    have h := sub63_testBit ⟨packBits f, packBits_lt f⟩ ⟨k, hk⟩
    rw [h, testBit_packBits, dite_eq_left hk]
  · rw [dite_eq_right hk]
    symm
    apply Nat.testBit_lt_two_pow
    have hpow : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega

lemma packBits_const_true : packBits (fun _ => true) = 63 := by decide
lemma packBits_const_false : packBits (fun _ => false) = 0 := by decide

lemma packBits_init (i : ℕ) (hi : i < 7) :
    packBits (fun t => (xsVec t).getD i false) ∈ initBank := by
  interval_cases i <;> decide

lemma packBits_eq_of_testBit (f : Fin 6 → Bool) (c : ℕ) (hc : c < 64)
    (h : ∀ t : Fin 6, f t = c.testBit t.val) : packBits f = c := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_packBits]
  by_cases hk : k < 6
  · rw [dite_eq_left hk]
    exact h ⟨k, hk⟩
  · rw [dite_eq_right hk]
    symm
    apply Nat.testBit_lt_two_pow
    have hpow : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalW (gs : List Gate) (t : Fin 6) : List Bool :=
  gs.foldl stepW (xsVec t)

lemma wires_eq_evalW (D : Circuit) (t : Fin 6) : D.wires (xsVec t) = evalW D.gates t := rfl

lemma len_xsVec (t : Fin 6) : (xsVec t).length = 7 := by
  simp [xsVec]

lemma len_foldl_stepW (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma len_evalW (gs : List Gate) (t : Fin 6) : (evalW gs t).length = 7 + gs.length := by
  unfold evalW
  rw [len_foldl_stepW, len_xsVec]

lemma evalW_snoc_lt (gs : List Gate) (g : Gate) (t : Fin 6) (i : ℕ) (hi : i < 7 + gs.length) :
    (evalW (gs ++ [g]) t).getD i false = (evalW gs t).getD i false := by
  have heq : evalW (gs ++ [g]) t =
      evalW gs t ++ [g.op.eval (g.inputs.map fun j => (evalW gs t).getD j false)] := by
    unfold evalW
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  rw [heq]
  have hl : (evalW gs t).length = 7 + gs.length := len_evalW gs t
  exact List.getD_append _ _ _ _ (by omega)

lemma evalW_snoc_eq (gs : List Gate) (g : Gate) (t : Fin 6) :
    (evalW (gs ++ [g]) t).getD (7 + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalW gs t).getD i false) := by
  have heq : evalW (gs ++ [g]) t =
      evalW gs t ++ [g.op.eval (g.inputs.map fun j => (evalW gs t).getD j false)] := by
    unfold evalW
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  rw [heq, ← len_evalW gs t]
  simp

def maskOf (gs : List Gate) (i : ℕ) : ℕ :=
  packBits (fun t => (evalW gs t).getD i false)

lemma maskOf_snoc_lt (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < 7 + gs.length) :
    maskOf (gs ++ [g]) i = maskOf gs i := by
  unfold maskOf
  congr 1
  funext t
  exact evalW_snoc_lt gs g t i hi

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCountL (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

lemma notCount_eq (D : Circuit) : notCount D = notCountL D.gates := by
  unfold notCount notCountL
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> rfl

lemma notCountL_snoc (gs : List Gate) (g : Gate) :
    notCountL (gs ++ [g]) = notCountL gs + if isNotOp g.op then 1 else 0 := by
  unfold notCountL
  rw [List.filter_append, List.length_append]
  cases h : isNotOp g.op <;> simp [h]

lemma notCountL_take_le (gs : List Gate) (k : ℕ) : notCountL (gs.take k) ≤ notCountL gs := by
  unfold notCountL
  have h : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_rhs => rw [h]
  rw [List.filter_append, List.length_append]
  omega

def bankAt (gs : List Gate) : ℕ → List ℕ
  | 0 => []
  | k + 1 => putMask (maskOf (gs.take (k + 1)) (7 + k)) (bankAt gs k)

lemma cov_at (gs : List Gate) : ∀ k ≤ gs.length,
    ∀ i < 7 + k, maskOf (gs.take k) i ∈ initBank ++ bankAt gs k := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    simp only [List.take_zero, bankAt, List.append_nil]
    exact packBits_init i hi
  | succ k ih =>
    intro hk i hi
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    have hlen : (gs.take k).length = k := List.length_take_of_le (by omega)
    rw [bankAt, mem_putMask]
    by_cases hlt : i < 7 + k
    · right
      rw [htake, maskOf_snoc_lt (gs.take k) (gs[k]'(by omega)) i (by omega)]
      exact ih (by omega) i hlt
    · left
      have heq : i = 7 + k := by omega
      subst heq
      rfl

lemma miss_at_le (gs : List Gate) : ∀ k ≤ gs.length,
    miss (bankAt gs k) ≤ miss (bankAt gs gs.length) + (gs.length - k) := by
  intro k hk
  obtain ⟨d, hd⟩ : ∃ d, gs.length - k = d := ⟨gs.length - k, rfl⟩
  induction d generalizing k with
  | zero =>
    have heq : k = gs.length := by omega
    subst heq
    omega
  | succ d ih =>
    have h1 := miss_le_putMask_succ (maskOf (gs.take (k + 1)) (7 + k)) (bankAt gs k)
    have h2 := ih (k + 1) (by omega) (by omega)
    change miss (bankAt gs k) ≤ miss (bankAt gs (k + 1)) + 1 at h1
    omega

lemma gate_mask_cases (gs : List Gate) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < 7 + gs.length) :
    (g.op = GateOp.and ∧
      (maskOf (gs ++ [g]) (7 + gs.length) = 63 ∨
       (∃ i < 7 + gs.length, maskOf (gs ++ [g]) (7 + gs.length) = maskOf gs i) ∨
       (∃ i < 7 + gs.length, ∃ j < 7 + gs.length,
         maskOf (gs ++ [g]) (7 + gs.length) = maskOf gs i &&& maskOf gs j))) ∨
    (g.op = GateOp.or ∧
      (maskOf (gs ++ [g]) (7 + gs.length) = 0 ∨
       (∃ i < 7 + gs.length, maskOf (gs ++ [g]) (7 + gs.length) = maskOf gs i) ∨
       (∃ i < 7 + gs.length, ∃ j < 7 + gs.length,
         maskOf (gs ++ [g]) (7 + gs.length) = maskOf gs i ||| maskOf gs j))) ∨
    (g.op = GateOp.not ∧
      (maskOf (gs ++ [g]) (7 + gs.length) = 63 ∨
       (∃ i < 7 + gs.length, maskOf (gs ++ [g]) (7 + gs.length) = 63 - maskOf gs i))) := by
  obtain ⟨hop, hlen⟩ := hfan
  rcases hop with h | h | h
  · left
    refine ⟨h, ?_⟩
    rcases h_in : g.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
    · left
      unfold maskOf
      have hf : (fun t => (evalW (gs ++ [g]) t).getD (7 + gs.length) false) = fun _ => true := by
        funext t; rw [evalW_snoc_eq, h, h_in]; rfl
      rw [hf]; exact packBits_const_true
    · right; left
      refine ⟨i, hback i (by rw [h_in]; simp), ?_⟩
      unfold maskOf
      congr 1; funext t; rw [evalW_snoc_eq, h, h_in]; simp [GateOp.eval]
    · right; right
      refine ⟨i, hback i (by rw [h_in]; simp), j, hback j (by rw [h_in]; simp), ?_⟩
      unfold maskOf
      rw [← packBits_and]
      congr 1; funext t; rw [evalW_snoc_eq, h, h_in]; simp [GateOp.eval]
    · rw [h_in] at hlen; simp at hlen
  · right; left
    refine ⟨h, ?_⟩
    rcases h_in : g.inputs with _ | ⟨i, _ | ⟨j, _ | _⟩⟩
    · left
      unfold maskOf
      have hf : (fun t => (evalW (gs ++ [g]) t).getD (7 + gs.length) false) = fun _ => false := by
        funext t; rw [evalW_snoc_eq, h, h_in]; rfl
      rw [hf]; exact packBits_const_false
    · right; left
      refine ⟨i, hback i (by rw [h_in]; simp), ?_⟩
      unfold maskOf
      congr 1; funext t; rw [evalW_snoc_eq, h, h_in]; simp [GateOp.eval]
    · right; right
      refine ⟨i, hback i (by rw [h_in]; simp), j, hback j (by rw [h_in]; simp), ?_⟩
      unfold maskOf
      rw [← packBits_or]
      congr 1; funext t; rw [evalW_snoc_eq, h, h_in]; simp [GateOp.eval]
    · rw [h_in] at hlen; simp at hlen
  · right; right
    refine ⟨h, ?_⟩
    rcases h_in : g.inputs with _ | ⟨i, rest⟩
    · left
      unfold maskOf
      have hf : (fun t => (evalW (gs ++ [g]) t).getD (7 + gs.length) false) = fun _ => true := by
        funext t; rw [evalW_snoc_eq, h, h_in]; rfl
      rw [hf]; exact packBits_const_true
    · right
      refine ⟨i, hback i (by rw [h_in]; simp), ?_⟩
      unfold maskOf
      rw [← packBits_not]
      congr 1; funext t; rw [evalW_snoc_eq, h, h_in]; simp [GateOp.eval]

lemma cert_inv (D : Circuit) (hfan : FanInTwo D) (hback : ReadsBack 7 D)
    (hnot : notCount D ≤ 2) (hsize : D.size ≤ 6)
    (hmiss : miss (bankAt D.gates D.gates.length) = 0) :
    ∀ k ≤ D.gates.length, ∃ u ≤ notCountL (D.gates.take k), (bankAt D.gates k, u) ∈ B k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, Nat.zero_le _, ?_⟩
    change ([], 0) ∈ B0
    decide
  | succ k ih =>
    intro hk
    obtain ⟨u, hu, hmem⟩ := ih (by omega)
    have hlt6 : k < 6 := by
      have : D.gates.length ≤ 6 := hsize
      omega
    have hlayer := layerOK_all k hlt6
    have hst : stateOK (B (k + 1)) (5 - k) (bankAt D.gates k, u) = true :=
      List.all_eq_true.mp hlayer (bankAt D.gates k, u) hmem
    simp only [stateOK, Bool.and_eq_true] at hst
    obtain ⟨⟨hstay, hnotok⟩, hpairs⟩ := hst
    have htake : D.gates.take (k + 1) = D.gates.take k ++ [D.gates[k]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    have hlenk : (D.gates.take k).length = k := List.length_take_of_le (by omega)
    have hklt : k < D.gates.length := by omega
    set g : Gate := D.gates[k]'hklt with hg_def
    have hg_mem : g ∈ D.gates := List.getElem_mem hklt
    have hga : gateAt D k = g := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD, hklt, g]
    have hback_g : ∀ i ∈ g.inputs, i < 7 + (D.gates.take k).length := by
      intro i hi
      rw [hlenk]
      have := hback k hklt i (by rw [hga]; exact hi)
      exact this
    have hmiss_nxt : miss (bankAt D.gates (k + 1)) ≤ 5 - k := by
      have hm := miss_at_le D.gates (k + 1) hk
      rw [hmiss] at hm
      have : D.gates.length ≤ 6 := hsize
      omega
    have hcov := cov_at D.gates k (by omega)
    have hnc_succ : notCountL (D.gates.take (k + 1)) =
        notCountL (D.gates.take k) + if isNotOp g.op then 1 else 0 := by
      rw [htake, notCountL_snoc]
    have hcases := gate_mask_cases (D.gates.take k) g (hfan g hg_mem) hback_g
    rw [← htake, hlenk] at hcases
    have hstay_step : ∀ m, m ∈ initBank ++ bankAt D.gates k →
        putMask m (bankAt D.gates k) = bankAt D.gates k := fun m hm =>
      putMask_of_mem m (bankAt D.gates k) hm
    rcases hcases with ⟨hop, hm⟩ | ⟨hop, hm⟩ | ⟨hop, hm⟩
    · have hnc_ge : u ≤ notCountL (D.gates.take (k + 1)) := by
        rw [hnc_succ, hop]; simp [isNotOp]; omega
      rcases hm with hm63 | ⟨i, hi, hmi⟩ | ⟨i, hi, j, hj, hmij⟩
      · have heq : bankAt D.gates (k + 1) = bankAt D.gates k := by
          rw [bankAt, hm63]
          exact hstay_step 63 (by simp [initBank])
        rw [heq] at hmiss_nxt ⊢
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ u hstay hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
      · have heq : bankAt D.gates (k + 1) = bankAt D.gates k := by
          rw [bankAt, hmi]
          exact hstay_step _ (hcov i (by omega))
        rw [heq] at hmiss_nxt ⊢
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ u hstay hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
      · rw [bankAt, hmij] at hmiss_nxt ⊢
        have hspec := pairsOK_spec (B (k + 1)) (5 - k) (bankAt D.gates k) u hstay
          (initBank ++ bankAt D.gates k) (fun _ hz => hz) hpairs
          (maskOf (D.gates.take k) i) (hcov i (by omega))
          (maskOf (D.gates.take k) j) (hcov j (by omega))
        obtain ⟨u', hu', hmem'⟩ := hspec.1 hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
    · have hnc_ge : u ≤ notCountL (D.gates.take (k + 1)) := by
        rw [hnc_succ, hop]; simp [isNotOp]; omega
      rcases hm with hm0 | ⟨i, hi, hmi⟩ | ⟨i, hi, j, hj, hmij⟩
      · have heq : bankAt D.gates (k + 1) = bankAt D.gates k := by
          rw [bankAt, hm0]
          exact hstay_step 0 (by simp [initBank])
        rw [heq] at hmiss_nxt ⊢
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ u hstay hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
      · have heq : bankAt D.gates (k + 1) = bankAt D.gates k := by
          rw [bankAt, hmi]
          exact hstay_step _ (hcov i (by omega))
        rw [heq] at hmiss_nxt ⊢
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ u hstay hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
      · rw [bankAt, hmij] at hmiss_nxt ⊢
        have hspec := pairsOK_spec (B (k + 1)) (5 - k) (bankAt D.gates k) u hstay
          (initBank ++ bankAt D.gates k) (fun _ hz => hz) hpairs
          (maskOf (D.gates.take k) i) (hcov i (by omega))
          (maskOf (D.gates.take k) j) (hcov j (by omega))
        obtain ⟨u', hu', hmem'⟩ := hspec.2 hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
    · have hnc_eq : notCountL (D.gates.take (k + 1)) = notCountL (D.gates.take k) + 1 := by
        rw [hnc_succ, hop]; simp [isNotOp]
      have hnc_le2 : notCountL (D.gates.take (k + 1)) ≤ 2 :=
        (notCountL_take_le D.gates (k + 1)).trans (by rw [← notCount_eq]; exact hnot)
      have hu2 : u < 2 := by omega
      rw [ite_eq_left hu2] at hnotok
      rcases hm with hm63 | ⟨i, hi, hmi⟩
      · have heq : bankAt D.gates (k + 1) = bankAt D.gates k := by
          rw [bankAt, hm63]
          exact hstay_step 63 (by simp [initBank])
        rw [heq] at hmiss_nxt ⊢
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ u hstay hmiss_nxt
        exact ⟨u', by omega, hmem'⟩
      · rw [bankAt, hmi] at hmiss_nxt ⊢
        have hchk := List.all_eq_true.mp hnotok (maskOf (D.gates.take k) i) (hcov i (by omega))
        obtain ⟨u', hu', hmem'⟩ := checkNext_spec (B (k + 1)) (5 - k) _ (u + 1) hchk hmiss_nxt
        exact ⟨u', by omega, hmem'⟩

theorem main_proof : ¬ (∃ (D : Circuit) (p q r : Fin (7 + D.size)),
    FanInTwo D ∧ ReadsBack 7 D ∧ notCount D ≤ 2 ∧ D.size ≤ 6 ∧
    ∀ t : Fin 6,
      let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
      let w := D.wires xs
      w.getD p.val false = (10 : Nat).testBit t.val ∧
      w.getD q.val false = (40 : Nat).testBit t.val ∧
      w.getD r.val false = (46 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, hback, hnot, hsize, hcomp⟩
  have hp : maskOf D.gates p.val = 10 :=
    packBits_eq_of_testBit _ 10 (by omega) (fun t => (hcomp t).1)
  have hq : maskOf D.gates q.val = 40 :=
    packBits_eq_of_testBit _ 40 (by omega) (fun t => (hcomp t).2.1)
  have hr : maskOf D.gates r.val = 46 :=
    packBits_eq_of_testBit _ 46 (by omega) (fun t => (hcomp t).2.2)
  have hcov := cov_at D.gates D.gates.length le_rfl
  rw [List.take_length] at hcov
  have h10 : 10 ∈ bankAt D.gates D.gates.length := by
    have h := hcov p.val p.isLt
    rw [hp, List.mem_append] at h
    exact h.resolve_left (by decide)
  have h40 : 40 ∈ bankAt D.gates D.gates.length := by
    have h := hcov q.val q.isLt
    rw [hq, List.mem_append] at h
    exact h.resolve_left (by decide)
  have h46 : 46 ∈ bankAt D.gates D.gates.length := by
    have h := hcov r.val r.isLt
    rw [hr, List.mem_append] at h
    exact h.resolve_left (by decide)
  have hmiss : miss (bankAt D.gates D.gates.length) = 0 := by
    simp [miss, h10, h40, h46]
  obtain ⟨u, _, hmem⟩ := cert_inv D hfan hback hnot hsize hmiss D.gates.length le_rfl
  have hpos := noHit_all D.gates.length (bankAt D.gates D.gates.length, u) hmem
  dsimp only at hpos
  omega

end PEqualNP.Outside.L_meta_50928

theorem PEqualNP.Outside.L_meta_50928 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val)) := by
  exact PEqualNP.Outside.L_meta_50928.main_proof
