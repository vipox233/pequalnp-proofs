import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53159_aux

abbrev B := List Nat
def initial : B := [0,63491,1386508,235568,151748,287504,558408,1246721,1835170]
def contribution (p : Nat) : Nat :=
  if p &&& 2095104 == 0 then let v := p &&& 2047; v &&& (v - 1) else 0
def extra (b : B) (old x : Nat) : Nat :=
  b.foldl (fun s w => s ||| contribution (x &&& w)) (old ||| contribution x)
def outputs (b : B) : B :=
  ((b.flatMap fun x => b.flatMap fun y => [x &&& y, x ||| y]).eraseDups)


def readMask (bank : List (BitVec 21)) : BitVec 5 → BitVec 21 :=
  bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
    if index = 0 then wire else rest (index - 1)) (fun _ => 0)

theorem readMask_mem (bank : List (BitVec 21)) (i : BitVec 5) :
    readMask bank i ∈ bank ∨ readMask bank i = 0 := by
  induction bank generalizing i with
  | nil => exact Or.inr rfl
  | cons a tail ih =>
    change (if i = 0 then a else readMask tail (i - 1)) ∈ a :: tail ∨
      (if i = 0 then a else readMask tail (i - 1)) = 0
    by_cases h : i = 0
    · rw [if_pos h]
      exact Or.inl List.mem_cons_self
    · rw [if_neg h]
      rcases ih (i - 1) with hm | hz
      · exact Or.inl (List.mem_cons_of_mem a hm)
      · exact Or.inr hz

theorem oneGateBank (gates : Fin 1 → Bool × BitVec 5 × BitVec 5)
    (bank : List (BitVec 21)) :
    (List.ofFn gates).foldl (fun b g => b ++
      [if g.1 then readMask b g.2.1 &&& readMask b g.2.2
       else readMask b g.2.1 ||| readMask b g.2.2]) bank =
    bank ++ [if (gates 0).1 then readMask bank (gates 0).2.1 &&& readMask bank (gates 0).2.2
             else readMask bank (gates 0).2.1 ||| readMask bank (gates 0).2.2] := by
  rw [List.ofFn_succ]
  rfl


def bitWeight (mask word : BitVec 21) : Nat → Nat
  | 0 => 0
  | n+1 => bitWeight mask word n + (if mask.getLsbD n && word.getLsbD n then 1 else 0)

theorem bitWeight_or (mask x y : BitVec 21) (n : Nat) :
    bitWeight mask (x ||| y) n ≤ bitWeight mask x n + bitWeight mask y n := by
  induction n with
  | zero => simp [bitWeight]
  | succ n ih =>
    simp only [bitWeight, BitVec.getLsbD_or]
    cases mask.getLsbD n <;> cases x.getLsbD n <;> cases y.getLsbD n <;> simp <;> omega

theorem bitWeight_and (mask x y : BitVec 21) (n : Nat) :
    bitWeight mask (x &&& y) n ≤ bitWeight mask x n := by
  induction n with
  | zero => simp [bitWeight]
  | succ n ih =>
    simp only [bitWeight, BitVec.getLsbD_and]
    cases mask.getLsbD n <;> cases x.getLsbD n <;> cases y.getLsbD n <;> simp <;> omega

theorem bitWeight_zero (mask : BitVec 21) (n : Nat) :
    bitWeight mask 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bitWeight mask 0 n + (if mask.getLsbD n && (0#21).getLsbD n then 1 else 0) = 0
    rw [ih, BitVec.getLsbD_zero]
    simp

theorem terminal_weight {α : Type} (product : α → BitVec 21) (mask : BitVec 21)
    (hs : ∀ p, product p &&& 2095104 = 0 → bitWeight mask (product p) 11 ≤ 1)
    (xs : List α) (acc : BitVec 21)
    (hc : xs.all (fun p => (product p &&& 2095104) == 0) = true) :
    bitWeight mask (xs.foldl (fun a p => a ||| product p) acc) 11 ≤ bitWeight mask acc 11 + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hc
    have h1 := hs x hc.1
    have h2 := bitWeight_or mask acc (product x) 11
    have h3 := ih (acc ||| product x) hc.2
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem terminal_impossible {α : Type} (product : α → BitVec 21) (mask : BitVec 21)
    (hs : ∀ p, product p &&& 2095104 = 0 → bitWeight mask (product p) 11 ≤ 1)
    (xs : List α) (hg : xs.length < bitWeight mask 2047 11) (affordable : Bool) :
    (affordable && xs.all (fun p => (product p &&& 2095104) == 0) &&
      ((xs.foldl (fun a p => a ||| product p) 0 &&& 2047) == 2047)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hw := terminal_weight product mask hs xs 0 h.1.2
  rw [bitWeight_zero, Nat.zero_add] at hw
  have ha := bitWeight_and mask (xs.foldl (fun a p => a ||| product p) 0) 2047 11
  rw [h.2] at ha
  omega


abbrev Gate := Bool × BitVec 5 × BitVec 5
abbrev W := BitVec 21
def initBank : List W := ([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21)
def gateWire (b : List W) (g : Gate) : W :=
  if g.1 then readMask b g.2.1 &&& readMask b g.2.2 else readMask b g.2.1 ||| readMask b g.2.2
def updated (b : List W) (g : Gate) := b ++ [gateWire b g]
def Represents (b : List W) (s : B) := 0 ∈ s ∧ ∀ w ∈ b, w.toNat ∈ s

theorem represents_start : Represents initBank initial := by
  unfold Represents
  refine ⟨by decide, ?_⟩
  have h : initBank.all (fun w => initial.contains w.toNat) = true := by decide +kernel
  simpa only [List.all_eq_true, List.contains_iff_mem] using h

theorem read_in {b : List W} {s : B} (h : Represents b s) (i : BitVec 5) :
    (readMask b i).toNat ∈ s := by
  rcases readMask_mem b i with hm | hz
  · exact h.2 _ hm
  · rw [hz]
    exact h.1

theorem gate_in {b : List W} {s : B} (h : Represents b s) (g : Gate) :
    (gateWire b g).toNat ∈ outputs s := by
  unfold outputs
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨_, read_in h g.2.1, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨_, read_in h g.2.2, ?_⟩
  unfold gateWire
  split
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem represents_next {b : List W} {s : B} (h : Represents b s) (g : Gate) :
    Represents (updated b g) ((gateWire b g).toNat :: s) := by
  refine ⟨List.mem_cons_of_mem _ h.1, ?_⟩
  intro w hw
  rcases List.mem_append.mp hw with hm | he
  · exact List.mem_cons_of_mem _ (h.2 _ hm)
  · rw [List.mem_singleton.mp he]
    exact List.mem_cons_self

def Packed (s : B) := ∃ mask : W, 6 < bitWeight mask 2047 11 ∧
  ∀ a : W, a.toNat ∈ s → ∀ b : W, b.toNat ∈ s →
    (a &&& b) &&& 2095104 = 0 → bitWeight mask (a &&& b) 11 ≤ 1

theorem indexed_impossible
    (cover : ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial),
      ∀ z ∈ outputs (y :: x :: initial), Packed (z :: y :: x :: initial))
    (gates : Fin 3 → Gate) (pairs : Fin 6 → BitVec 5 × BitVec 5) (affordable : Bool) :
    let b := (List.ofFn gates).foldl updated initBank
    let prod := fun p : BitVec 5 × BitVec 5 => readMask b p.1 &&& readMask b p.2
    let xs := List.ofFn pairs
    (affordable && xs.all (fun p => (prod p &&& 2095104) == 0) &&
      ((xs.foldl (fun acc p => acc ||| prod p) 0 &&& 2047) == 2047)) = false := by
  have three : List.ofFn gates = [gates 0, gates 1, gates 2] := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    rfl
  dsimp only
  rw [three]
  let h0 := represents_start
  let h1 := represents_next h0 (gates 0)
  let h2 := represents_next h1 (gates 1)
  let h3 := represents_next h2 (gates 2)
  obtain ⟨mask, hg, hp⟩ := cover _ (gate_in h0 _) _ (gate_in h1 _) _ (gate_in h2 (gates 2))
  apply terminal_impossible _ mask
  · intro p
    exact hp _ (read_in h3 p.1) _ (read_in h3 p.2)
  · simpa using hg


def clear (v : Nat) := v &&& (v - 1)
def retained (e : Nat) : W := ~~~ BitVec.ofNat 21 e

theorem weight_retained_mono {e c : Nat} (h : c ||| e = e) (w : W) (n : Nat) :
    bitWeight (retained e) w n ≤ bitWeight (retained c) w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := congrArg (fun t : Nat => t.testBit n) h
    simp only [Nat.testBit_or] at hi
    simp only [bitWeight, retained, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
    unfold retained at ih
    by_cases hn : n < 21 <;> cases hc : c.testBit n <;> cases he : e.testBit n <;> cases hw : w.getLsbD n <;>
      simp [hn,hc,he,hw] at hi ⊢ <;> omega

def smallStrength (v : Nat) : Bool :=
  decide (clear (clear (clear v)) = 0 → 6 < bitWeight (retained v) 2047 11)
def smallUnit (v : Nat) : Bool :=
  decide (bitWeight (retained (clear v)) (BitVec.ofNat 21 v) 11 ≤ 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem strength_table : (List.range 2048).all smallStrength = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem unit_table : (List.range 2048).all smallUnit = true := by decide +kernel

theorem clean_small {p : W} (h : p &&& 2095104 = 0) :
    p.toNat &&& 2047 = p.toNat ∧ p.toNat < 2048 := by
  have allbits : (2095104 ||| 2047 : W) = BitVec.allOnes 21 := by decide
  have hh : p &&& 2047 = p := by
    have eq := BitVec.and_or_distrib_left (x := p) (y := 2095104) (z := 2047)
    rw [allbits, BitVec.and_allOnes, h] at eq
    change p = (BitVec.ofNat 21 0) ||| (p &&& 2047) at eq
    rw [BitVec.zero_or] at eq
    exact eq.symm
  have hn := congrArg BitVec.toNat hh
  change p.toNat &&& 2047 = p.toNat at hn
  have le : p.toNat &&& 2047 ≤ 2047 := Nat.and_le_right
  exact ⟨hn, by omega⟩

theorem packed_of_scalar (s : B) (e : Nat) (he : e < 2048) (hs : clear (clear (clear e)) = 0)
    (covered : ∀ a ∈ s, ∀ b ∈ s, contribution (a &&& b) ||| e = e) : Packed s := by
  refine ⟨retained e, ?_, ?_⟩
  · exact (of_decide_eq_true (List.all_eq_true.mp strength_table e (List.mem_range.mpr he))) hs
  · intro a ha b hb hc
    let p := a &&& b
    obtain ⟨hlo, hsmall⟩ := clean_small hc
    have c0 : p.toNat &&& 2095104 = 0 := congrArg BitVec.toNat hc
    have hc' : contribution p.toNat = clear p.toNat := by
      change p.toNat &&& 2047 = p.toNat at hlo
      simp only [contribution, c0, beq_self_eq_true, ite_true, hlo, clear]
    have hsub : contribution p.toNat ||| e = e := covered _ ha _ hb
    rw [hc'] at hsub
    have hu := List.all_eq_true.mp unit_table p.toNat (List.mem_range.mpr hsmall)
    have hunit : bitWeight (retained (clear p.toNat)) p 11 ≤ 1 := by
      simpa [smallUnit] using hu
    exact (weight_retained_mono hsub p 11).trans hunit

def Included (a b : Nat) := a ||| b = b

theorem included_trans {a b c : Nat} (h : Included a b) (k : Included b c) : Included a c := by
  unfold Included at *
  calc a ||| c = a ||| (b ||| c) := by rw [k]
       _ = (a ||| b) ||| c := (Nat.or_assoc ..).symm
       _ = c := by rw [h,k]

theorem included_left (a b : Nat) : Included a (a ||| b) := by
  unfold Included
  rw [← Nat.or_assoc, Nat.or_self]

theorem included_right (a b : Nat) : Included b (a ||| b) := by
  rw [Nat.or_comm a b]
  exact included_left _ _

theorem fold_extends (f : Nat → Nat) (xs : B) (acc : Nat) :
    Included acc (xs.foldl (fun s w => s ||| f w) acc) := by
  induction xs generalizing acc with
  | nil => exact Nat.or_self _
  | cons x xs ih => exact included_trans (included_left _ _) (ih _)

theorem fold_contains (f : Nat → Nat) (xs : B) (acc w : Nat) (hw : w ∈ xs) :
    Included (f w) (xs.foldl (fun s x => s ||| f x) acc) := by
  induction xs generalizing acc with
  | nil => simp at hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with rfl | ht
    · exact included_trans (included_right _ _) (fold_extends ..)
    · exact ih _ ht

def Covered (b : B) (e : Nat) := ∀ a ∈ b, ∀ v ∈ b, Included (contribution (a &&& v)) e

theorem start_covered : Covered initial 0 := by
  have h : initial.all (fun a => initial.all (fun b => contribution (a &&& b) == 0)) = true := by decide +kernel
  simpa only [Covered, Included, Nat.or_zero, List.all_eq_true, beq_iff_eq] using h

theorem covered_next (b : B) (x e : Nat) (h : Covered b e) : Covered (x :: b) (extra b e x) := by
  have hf : Included (e ||| contribution x) (extra b e x) := fold_extends .. 
  have hm (w : Nat) (hw : w ∈ b) : Included (contribution (x &&& w)) (extra b e x) :=
    fold_contains (fun t => contribution (x &&& t)) b (e ||| contribution x) w hw
  intro a ha v hv
  rcases List.mem_cons.mp ha with hax | hab
  · subst a
    rcases List.mem_cons.mp hv with hvx | hvb
    · subst v
      rw [Nat.and_self]
      exact included_trans (included_right ..) hf
    · exact hm _ hvb
  · rcases List.mem_cons.mp hv with hvx | hvb
    · subst v
      rw [Nat.and_comm]
      exact hm _ hab
    · exact included_trans (h _ hab _ hvb) (included_trans (included_left ..) hf)

theorem contribution_small (v : Nat) : contribution v < 2048 := by
  unfold contribution
  split
  · have h : (v &&& 2047) &&& ((v &&& 2047) - 1) ≤ v &&& 2047 := Nat.and_le_left
    have h' : v &&& 2047 ≤ 2047 := Nat.and_le_right
    dsimp only
    omega
  · decide

theorem extra_small (b : B) (e x : Nat) (he : e < 2048) : extra b e x < 2048 := by
  have fold (s : B) (a : Nat) (ha : a < 2048) :
      s.foldl (fun t w => t ||| contribution (x &&& w)) a < 2048 := by
    induction s generalizing a with
    | nil => exact ha
    | cons v vs ih => exact ih _ (Nat.or_lt_two_pow (n := 11) ha (contribution_small _))
  exact fold _ _ (Nat.or_lt_two_pow (n := 11) he (contribution_small _))

def accumulated (x y z : Nat) :=
  extra (y :: x :: initial) (extra (x :: initial) (extra initial 0 x) y) z

theorem scalar_cover (h : ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial),
    ∀ z ∈ outputs (y :: x :: initial), clear (clear (clear (accumulated x y z))) = 0) :
    ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial), ∀ z ∈ outputs (y :: x :: initial),
      Packed (z :: y :: x :: initial) := by
  intro x hx y hy z hz
  apply packed_of_scalar _ (accumulated x y z)
  · exact extra_small _ _ _ (extra_small _ _ _ (extra_small _ _ _ (by decide)))
  · exact h _ hx _ hy _ hz
  · exact covered_next _ _ _ (covered_next _ _ _ (covered_next _ _ _ start_covered))


theorem from_checks (checks : ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial),
    ∀ z ∈ outputs (y :: x :: initial), clear (clear (clear (accumulated x y z))) = 0) : ∀ (gates : Fin 3 → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin 6 → BitVec 5 × BitVec 5),
  let read := fun (bank : List (BitVec 21)) =>
    bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0)
  let product := fun (bank : List (BitVec 21)) (pair : BitVec 5 × BitVec 5) =>
    read bank pair.1 &&& read bank pair.2
  let program := List.ofFn gates
  let bank := program.foldl (fun bank gate => bank ++
    [if gate.1 then product bank gate.2 else read bank gate.2.1 ||| read bank gate.2.2])
    (([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21))
  let affordable := program.foldr (fun gate (rest : Bool → Bool) used =>
    (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false
  let terminals := List.ofFn pairs
  (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
    ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = false := by
  intro gates pairs
  exact indexed_impossible (scalar_cover checks) gates pairs _

def pairs : B → B
  | [] => []
  | x :: xs => (x :: xs).flatMap (fun y => [x &&& y, x ||| y]) ++ pairs xs
def pack (xs : B) := xs.foldr (fun x acc => x ||| (acc <<< 24)) 0
def pattern (k d : Nat) := ((1 <<< (k*d)) - 1) / ((1 <<< d) - 1)
def bits := 2^21-1
def strip (ones v : Nat) := v &&& ((v ||| (ones <<< 23)) - ones)
def repeated (ones p : Nat) :=
  let dirty := p &&& (ones * 2095104)
  let bad := ((dirty + ones * (2^23-1)) >>> 23) &&& ones
  strip ones (p &&& (ones * 2047)) &&& ((ones - bad) * bits)
def extras (ones : Nat) (x : Nat) (prev : B) :=
  prev.foldl (fun acc w => acc ||| repeated ones (w &&& x)) (repeated ones x)
def slice (x : Nat) : Bool :=
  let b := x :: initial
  let seconds := (pairs b).eraseDups
  let zs0 := pairs (0 :: b)
  let zs1 := pairs (bits :: b)
  let h := zs0.length
  let d := 24*h
  let line := pattern h 24
  let rows := pattern seconds.length d
  let ones := rows * line
  let y := seconds.foldr (fun v acc => (v * line) ||| (acc <<< d)) 0
  let z := (pack zs0 * rows) ||| (y &&& (pack zs1 * rows))
  let bs := b.map (fun v => v * ones)
  let base := extras 1 x initial
  let e := (base * ones) ||| extras ones y bs ||| extras ones z (y :: bs)
  strip ones (strip ones (strip ones e)) == 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0 : slice 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1 : slice 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2 : slice 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : slice 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4 : slice 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5 : slice 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c6 : slice 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c7 : slice 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c8 : slice 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c9 : slice 256 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c10 : slice 512 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c11 : slice 1024 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c12 : slice 10240 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c13 : slice 16384 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c14 : slice 20480 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c15 : slice 24576 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16 : slice 32768 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17 : slice 38912 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c18 : slice 63491 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c19 : slice 67584 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c20 : slice 131072 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c21 : slice 135168 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c22 : slice 151748 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c23 : slice 194759 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24 : slice 196608 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c25 : slice 235568 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c26 : slice 252148 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c27 : slice 260147 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c28 : slice 262144 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c29 : slice 270336 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c30 : slice 287504 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c31 : slice 326419 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c32 : slice 422868 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c33 : slice 523056 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c34 : slice 524288 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c35 : slice 558408 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c36 : slice 589131 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c37 : slice 710092 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c38 : slice 761208 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c39 : slice 845656 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c40 : slice 1048576 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c41 : slice 1114112 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c42 : slice 1246721 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c43 : slice 1267397 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c44 : slice 1285681 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c45 : slice 1310211 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c46 : slice 1310720 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c47 : slice 1386508 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c48 : slice 1403676 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c49 : slice 1439759 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c50 : slice 1519117 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c51 : slice 1533713 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c52 : slice 1538252 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c53 : slice 1554492 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c54 : slice 1804105 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c55 : slice 1835170 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c56 : slice 1860530 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c57 : slice 1869290 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c58 : slice 1898659 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c59 : slice 1910958 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c60 : slice 1944908 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c61 : slice 1986790 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c62 : slice 2033315 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c63 : slice 2070706 = true := by decide +kernel
def firsts : B := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10240, 16384, 20480, 24576, 32768, 38912, 63491, 67584, 131072, 135168, 151748, 194759, 196608, 235568, 252148, 260147, 262144, 270336, 287504, 326419, 422868, 523056, 524288, 558408, 589131, 710092, 761208, 845656, 1048576, 1114112, 1246721, 1267397, 1285681, 1310211, 1310720, 1386508, 1403676, 1439759, 1519117, 1533713, 1538252, 1554492, 1804105, 1835170, 1860530, 1869290, 1898659, 1910958, 1944908, 1986790, 2033315, 2070706]
theorem complete : ∀ x ∈ (pairs initial).eraseDups, slice x = true := by
  have sub : (pairs initial).eraseDups.all firsts.contains = true := by decide +kernel
  intro x hx
  have hh := List.contains_iff_mem.mp (List.all_eq_true.mp sub x hx)
  simp only [firsts, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c24
  · exact c25
  · exact c26
  · exact c27
  · exact c28
  · exact c29
  · exact c30
  · exact c31
  · exact c32
  · exact c33
  · exact c34
  · exact c35
  · exact c36
  · exact c37
  · exact c38
  · exact c39
  · exact c40
  · exact c41
  · exact c42
  · exact c43
  · exact c44
  · exact c45
  · exact c46
  · exact c47
  · exact c48
  · exact c49
  · exact c50
  · exact c51
  · exact c52
  · exact c53
  · exact c54
  · exact c55
  · exact c56
  · exact c57
  · exact c58
  · exact c59
  · exact c60
  · exact c61
  · exact c62
  · exact c63

def lane (v rest : Nat) := v + 16777216 * rest

theorem lane_mod {v : Nat} (hv : v < 16777216) (r : Nat) : lane v r % 2^24 = v := by
  unfold lane
  omega

theorem lane_hi {v : Nat} (hv : v < 16777216) (r : Nat) : lane v r >>> 24 = r := by
  rw [Nat.shiftRight_eq_div_pow]
  unfold lane
  omega

theorem lane_split (n : Nat) : n = lane (n % 2^24) (n >>> 24) := by
  rw [Nat.shiftRight_eq_div_pow]
  unfold lane
  omega

theorem lane_and {a b : Nat} (ha : a < 16777216) (hb : b < 16777216) (A B : Nat) :
    lane a A &&& lane b B = lane (a &&& b) (A &&& B) := by
  rw [lane_split (lane a A &&& lane b B), Nat.and_mod_two_pow, Nat.shiftRight_and_distrib,
    lane_mod ha, lane_mod hb, lane_hi ha, lane_hi hb]

theorem lane_or {a b : Nat} (ha : a < 16777216) (hb : b < 16777216) (A B : Nat) :
    lane a A ||| lane b B = lane (a ||| b) (A ||| B) := by
  rw [lane_split (lane a A ||| lane b B), Nat.or_mod_two_pow, Nat.shiftRight_or_distrib,
    lane_mod ha, lane_mod hb, lane_hi ha, lane_hi hb]

theorem lane_scale (a A k : Nat) : lane a A * k = lane (a*k) (A*k) := by
  simp [lane, Nat.add_mul, Nat.mul_assoc]

theorem lane_sub {a b A B : Nat} (hl : b ≤ a) (hh : B ≤ A) :
    lane a A - lane b B = lane (a-b) (A-B) := by
  unfold lane
  omega

theorem lane_flag {a : Nat} (ha : a < 16777216) (A B : Nat) :
    ((lane a A >>> 23) &&& lane 1 B) = lane ((a >>> 23) &&& 1) ((A >>> 23) &&& B) := by
  rw [lane_split ((lane a A >>> 23) &&& lane 1 B), Nat.and_mod_two_pow, Nat.shiftRight_and_distrib,
    lane_mod (by decide : 1 < 16777216), lane_hi (by decide : 1 < 16777216)]
  congr 1
  · simp only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, lane]
    omega
  · rw [← Nat.shiftRight_add, Nat.add_comm 23 24, Nat.shiftRight_add, lane_hi ha]

theorem strip_lane {v : Nat} (hv : v < 8388608) (V O : Nat)
    (hO : O ≤ V ||| (O <<< 23)) :
    strip (lane 1 O) (lane v V) = lane (strip 1 v) (strip O V) := by
  unfold strip
  have hs : lane 1 O <<< 23 = lane 8388608 (O <<< 23) := by
    simp only [Nat.shiftLeft_eq, lane_scale]
  rw [hs, lane_or (by omega) (by decide)]
  have h1 : 1 ≤ v ||| 8388608 := Nat.le_trans (by decide : 1 ≤ 8388608) Nat.right_le_or
  have hm : v ||| 8388608 < 2^24 := Nat.or_lt_two_pow (by omega) (by decide)
  rw [lane_sub h1 hO, lane_and (by omega) (by omega)]
  rfl

theorem strip_split {v : Nat} (hv : v < 8388608) (V O : Nat) :
    strip (lane 1 O) (lane v V) = lane (strip 1 v) (strip O V) := by
  apply strip_lane hv
  apply Nat.le_trans _ Nat.right_le_or
  rw [Nat.shiftLeft_eq]
  omega

theorem lane_add (a b A B : Nat) : lane a A + lane b B = lane (a+b) (A+B) := by
  unfold lane
  omega

theorem repeated_lane {p : Nat} (hp : p < 2097152) (P O : Nat) :
    repeated (lane 1 O) (lane p P) = lane (repeated 1 p) (repeated O P) := by
  let dl := p &&& 2095104
  let dh := P &&& (O * 2095104)
  let fl := ((dl + 8388607) >>> 23) &&& 1
  let fh := ((dh + O * 8388607) >>> 23) &&& O
  have hd : dl ≤ 2095104 := Nat.and_le_right
  have hfl : fl ≤ 1 := Nat.and_le_right
  have hfh : fh ≤ O := Nat.and_le_right
  have hlow : p &&& 2047 ≤ 2047 := Nat.and_le_right
  have hstrip : strip 1 (p &&& 2047) ≤ p &&& 2047 := Nat.and_le_left
  have hflags : ((((lane p P &&& (lane 1 O * 2095104)) + lane 1 O * 8388607) >>> 23) &&& lane 1 O)
      = lane fl fh := by
    rw [lane_scale, lane_and (by omega) (by decide), lane_scale, lane_add]
    exact lane_flag (by change dl + 8388607 < 16777216; omega) _ _
  unfold repeated
  dsimp only
  change strip (lane 1 O) (lane p P &&& (lane 1 O * 2047)) &&&
    ((lane 1 O - _) * bits) = _
  try simp only [show (2^23-1 : Nat) = 8388607 by decide]
  rw [hflags, lane_sub hfl hfh, lane_scale, lane_scale,
    lane_and (by omega) (by decide), strip_split (by change p &&& 2047 < 8388608; omega)]
  have hmul : (1-fl)*bits < 16777216 := by unfold bits; omega
  rw [lane_and (by change strip 1 (p &&& 2047) < 16777216; omega) hmul]

theorem strip_one {v : Nat} (hv : v < 8388608) : strip 1 v = v &&& (v-1) := by
  by_cases hz : v = 0
  · simp [hz, strip]
  have hh : v ||| 8388608 = v + 8388608 := by
    change v ||| (1 <<< 23) = v + 8388608
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv]
    omega
  unfold strip
  change v &&& ((v ||| 8388608) - 1) = _
  rw [hh]
  have hsmall : v &&& (v+8388608-1) < 2^23 := Nat.lt_of_le_of_lt Nat.and_le_left hv
  rw [← Nat.mod_eq_of_lt hsmall, Nat.and_mod_two_pow, Nat.mod_eq_of_lt hv]
  exact congrArg (fun z => v &&& z) (show (v + 8388608 - 1) % 8388608 = v - 1 by omega)

theorem repeated_one (p : Nat) :
    repeated 1 p = if p &&& 2095104 == 0 then (p &&& 2047) &&& ((p &&& 2047)-1) else 0 := by
  let d := p &&& 2095104
  have hd : d ≤ 2095104 := Nat.and_le_right
  have hv : p &&& 2047 ≤ 2047 := Nat.and_le_right
  have hm : (p &&& 2047) &&& ((p &&& 2047)-1) < 2^21 :=
    Nat.lt_of_le_of_lt Nat.and_le_left (by omega)
  unfold repeated
  simp only [Nat.one_mul, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, strip_one (by omega : p &&& 2047 < 8388608)]
  change _ &&& ((1 - ((d+8388607)/8388608)%2) * bits) = _
  by_cases h : d = 0
  · have hc : p &&& 2095104 = 0 := h
    simp only [h, hc, beq_self_eq_true, ite_true]
    change _ &&& (2^21-1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hm]
  · have hc : p &&& 2095104 ≠ 0 := h
    have hq : (d+8388607)/8388608 = 1 := by omega
    simp [hq, hc]

theorem pack_cons_lane {v : Nat} (hv : v < 16777216) (xs : B) :
    pack (v :: xs) = lane v (pack xs) := by
  change v ||| (pack xs <<< 24) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq]
  unfold lane
  omega

def lowOnes (xs : B) := pack (List.replicate xs.length 1)

theorem lowOnes_cons (v : Nat) (xs : B) : lowOnes (v :: xs) = lane 1 (lowOnes xs) := by
  unfold lowOnes
  rw [List.length_cons, List.replicate_succ, pack_cons_lane (by decide)]

theorem pack_map_strip (xs : B) (hs : ∀ v ∈ xs, v < 8388608) :
    strip (lowOnes xs) (pack xs) = pack (xs.map (strip 1)) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have hv := hs v List.mem_cons_self
    have hlow : strip 1 v ≤ v := Nat.and_le_left
    rw [lowOnes_cons, pack_cons_lane (by omega), strip_split hv, ih (fun w hw => hs w (List.mem_cons_of_mem _ hw)),
      List.map_cons, pack_cons_lane (by omega)]

theorem pack_map_repeated (xs : B) (hs : ∀ v ∈ xs, v < 2097152) :
    repeated (lowOnes xs) (pack xs) = pack (xs.map (repeated 1)) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have hv := hs v List.mem_cons_self
    have hlow : repeated 1 v ≤ v := by
      rw [repeated_one]
      split
      · exact Nat.le_trans Nat.and_le_left Nat.and_le_left
      · omega
    rw [lowOnes_cons, pack_cons_lane (by omega), repeated_lane hv, ih (fun w hw => hs w (List.mem_cons_of_mem _ hw)),
      List.map_cons, pack_cons_lane (by omega)]

theorem pack_zip_op (f : Nat → Nat → Nat) (hz : f 0 0 = 0)
    (small : ∀ a b, a < 16777216 → b < 16777216 → f a b < 16777216)
    (op : ∀ a b A B, a < 16777216 → b < 16777216 →
       f (lane a A) (lane b B) = lane (f a b) (f A B))
    (xs ys : B) (hx : ∀ v ∈ xs, v < 16777216) (hy : ∀ v ∈ ys, v < 16777216)
    (hlen : xs.length = ys.length) : f (pack xs) (pack ys) = pack (xs.zipWith f ys) := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    exact hz
  | cons v xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons w ys =>
      have hv := hx v List.mem_cons_self
      have hw := hy w List.mem_cons_self
      rw [pack_cons_lane hv, pack_cons_lane hw, op _ _ _ _ hv hw,
        ih ys (fun k hk => hx k (List.mem_cons_of_mem _ hk)) (fun k hk => hy k (List.mem_cons_of_mem _ hk)) (by simpa using hlen),
        List.zipWith_cons_cons, pack_cons_lane (small _ _ hv hw)]

def pack_zip_and := pack_zip_op (· &&& ·) rfl
  (fun _ _ h _ => Nat.lt_of_le_of_lt Nat.and_le_left h) (fun _ _ A B ha hb => lane_and ha hb A B)

def pack_zip_or := pack_zip_op (· ||| ·) rfl
  (fun _ _ ha hb => Nat.or_lt_two_pow (n := 24) ha hb) (fun _ _ A B ha hb => lane_or ha hb A B)

theorem zero_of_pack_zero (xs : B) (hz : pack xs = 0) : ∀ v ∈ xs, v = 0 := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    change v ||| (pack xs <<< 24) = 0 at hz
    have hv := @Nat.left_le_or v (pack xs <<< 24)
    have ht := @Nat.right_le_or v (pack xs <<< 24)
    rw [hz] at hv ht
    rw [Nat.shiftLeft_eq] at ht
    intro w hw
    rcases List.mem_cons.mp hw with rfl | h
    · omega
    · exact ih (by omega) w h

def corners (b : B) : List (Nat × Nat) :=
  [(0,bits),(0,bits)] ++ b.flatMap (fun v => [(0,v),(v,bits)]) ++ (pairs b).map (fun p => (p,p))
def affine (y : Nat) (c : Nat × Nat) := c.1 ||| (y &&& c.2)
theorem affine_same (y p : Nat) : affine y (p,p) = p := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [affine, Nat.testBit_or, Nat.testBit_and]
theorem pairs_affine (b : B) (y : Nat) (hy : y < 2^21) :
    pairs (y :: b) = (corners b).map (affine y) := by
  have mask : y &&& bits = y := Nat.and_two_pow_sub_one_of_lt_two_pow hy
  simp [pairs, corners, List.map_flatMap, affine, mask, Nat.or_comm]
  simp [Function.comp_def, affine_same]
theorem geom (n d : Nat) (hd : 0 < d) :
    pattern n d * (2^d-1) + 1 = 2^(n*d) := by
  have pos : 0 < 2^d - 1 := by have := Nat.one_lt_two_pow (n := d) (by omega); omega
  have hdvd : 2^d - 1 ∣ 2^(n*d) - 1 := by
    rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  unfold pattern
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.div_mul_cancel hdvd]
  have := Nat.two_pow_pos (n*d)
  omega
theorem pattern_succ (n d : Nat) (hd : 0 < d) :
    pattern (n+1) d = 1 + pattern n d * 2^d := by
  have h := geom n d hd
  have hs := geom (n+1) d hd
  rw [Nat.add_mul, Nat.one_mul, Nat.pow_add] at hs
  have hp : 1 < 2^d := Nat.one_lt_two_pow (n := d) (by omega)
  have ht : 2^d - 1 + 1 = 2^d := by omega
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^d - 1 by omega)
  nlinarith only [hs, congrArg (fun k : Nat => k * 2^d) h, ht]
theorem pack_replicate (n v : Nat) (hv : v < 2^24) :
    pack (List.replicate n v) = pattern n 24 * v := by
  induction n with
  | zero => simp [pack, pattern]
  | succ n ih =>
    rw [List.replicate_succ]
    change v ||| (pack (List.replicate n v) <<< 24) = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq, ih, pattern_succ n 24 (by decide)]
    ring
theorem interp (c : Nat × Nat) (y : Nat) (hy : y < 2^21) :
    affine y c = affine 0 c ||| (y &&& affine bits c) := by
  have mask : y &&& bits = y := Nat.and_two_pow_sub_one_of_lt_two_pow hy
  simp only [affine, Nat.zero_and, Nat.or_zero, Nat.and_or_distrib_left, ← Nat.and_assoc, mask, ← Nat.or_assoc]
  exact congrArg (fun t : Nat => t ||| (y &&& c.2)) (affine_same y c.1).symm
theorem third_slot (b : B) {y z : Nat} (hy : y < 2^21) (hz : z ∈ pairs (y :: b)) :
    ∃ i : Fin (corners b).length,
      z = (pairs (0 :: b))[(i:Nat)]! ||| (y &&& (pairs (bits :: b))[(i:Nat)]!) := by
  rw [pairs_affine b y hy] at hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hz
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hc
  refine ⟨⟨i,hi⟩, ?_⟩
  rw [pairs_affine b 0 (by decide), pairs_affine b bits (by decide)]
  simp [getElem!_pos, hi, he, ← interp c y hy]
theorem pattern_add (a b d : Nat) (hd : 0 < d) :
    pattern (a+b) d = pattern a d + 2^(a*d) * pattern b d := by
  induction b with
  | zero => simp [pattern]
  | succ b ih =>
    rw [← Nat.add_assoc, pattern_succ _ _ hd, ih, pattern_succ _ _ hd]
    have hg := geom a d hd
    have hp : 1 < 2^d := Nat.one_lt_two_pow (by omega)
    have hsub : 2^d - 1 + 1 = 2^d := by omega
    nlinarith only [hg, congrArg (fun t : Nat => pattern a d*t) hsub]
theorem pattern_tile (k h : Nat) :
    pattern k (24*h) * pattern h 24 = pattern (k*h) 24 := by
  by_cases hh : h = 0
  · simp [hh, pattern]
  induction k with
  | zero => simp [pattern]
  | succ k ih =>
    rw [Nat.succ_mul k h, Nat.add_comm (k*h) h, pattern_add h (k*h) 24 (by decide),
      pattern_succ k (24*h) (by omega)]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_right_comm, ih, Nat.mul_comm h 24, Nat.mul_comm (pattern (k*h) 24)]
theorem pack_cons_add {v : Nat} (hv : v < 2^24) (vs : B) :
    pack (v :: vs) = v + 2^24 * pack vs := by
  change v ||| (pack vs <<< 24) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq]
  omega
theorem pack_append (vs ws : B) (hv : ∀ v ∈ vs, v < 2^24) :
    pack (vs ++ ws) = pack vs + 2^(24*vs.length) * pack ws := by
  induction vs with
  | nil => simp [pack]
  | cons head tail ih =>
    have hh := hv head (by simp)
    simp only [List.cons_append, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [pack_cons_add hh, ih (fun x hx => hv x (by simp [hx])), pack_cons_add hh]
    ring
theorem pack_lt (vs : B) (hv : ∀ v ∈ vs, v < 2^24) : pack vs < 2^(24*vs.length) := by
  induction vs with
  | nil => decide
  | cons a t ih =>
    have ha := hv a (by simp)
    have ht := ih (fun x hx => hv x (by simp [hx]))
    rw [pack_cons_add ha]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    omega
theorem packed_seconds (ys : B) (h : Nat) (hy : ∀ y ∈ ys, y < 2^24) :
    ys.foldr (fun v acc => (v * pattern h 24) ||| (acc <<< (24*h))) 0 =
    pack (ys.flatMap (fun y => List.replicate h y)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have thisY := hy y (by simp)
    have hbound : ∀ t ∈ List.replicate h y, t < 2^24 := by
      intro t ht
      exact (List.eq_of_mem_replicate ht) ▸ thisY
    have small := pack_lt _ hbound
    rw [List.length_replicate, pack_replicate _ _ thisY, Nat.mul_comm _ y] at small
    rw [List.foldr_cons, ih (fun t ht => hy t (by simp [ht])),
      Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt small, Nat.shiftLeft_eq, List.flatMap_cons,
      pack_append _ _ hbound, List.length_replicate, pack_replicate _ _ thisY]
    ring
theorem packed_rows (r : B) (k : Nat) (hr : ∀ v ∈ r, v < 2^24) :
    pack r * pattern k (24*r.length) = pack ((List.replicate k r).flatten) := by
  by_cases empty : r = []
  · simp [empty, pack]
  have hpos : 0 < 24*r.length := by
    have hlen := List.length_pos_iff.mpr empty
    omega
  induction k with
  | zero => simp [pattern, pack]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, pack_append _ _ hr, ← ih, pattern_succ _ _ hpos]
    ring
theorem pack_map_and {α : Type} (l : List α) (f g : α → Nat)
    (hf : ∀ a ∈ l, f a < 2^24) (hg : ∀ a ∈ l, g a < 2^24) :
    pack (l.map f) &&& pack (l.map g) = pack (l.map (fun a => f a &&& g a)) := by
  induction l with
  | nil => simp [pack]
  | cons a t ih =>
    have ha := hf a (by simp)
    have hb := hg a (by simp)
    simp only [List.map_cons]
    rw [pack_cons_lane ha, pack_cons_lane hb, lane_and ha hb, ih (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx])),
      pack_cons_lane (Nat.lt_of_le_of_lt Nat.and_le_left ha)]
theorem pack_map_or {α : Type} (l : List α) (f g : α → Nat)
    (hf : ∀ a ∈ l, f a < 2^24) (hg : ∀ a ∈ l, g a < 2^24) :
    pack (l.map f) ||| pack (l.map g) = pack (l.map (fun a => f a ||| g a)) := by
  induction l with
  | nil => simp [pack]
  | cons a t ih =>
    have ha := hf a (by simp)
    have hb := hg a (by simp)
    simp only [List.map_cons]
    rw [pack_cons_lane ha, pack_cons_lane hb, lane_or ha hb, ih (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx])),
      pack_cons_lane (Nat.or_lt_two_pow ha hb)]
def positions (b : B) (ys : B) : List (Nat × (Nat × Nat)) :=
  ys.flatMap (fun y => (corners b).map (fun c => (y,c)))
theorem fixed_columns {α : Type} (b : B) (ys : B) (f : Nat × Nat → α) :
    (positions b ys).map (fun s => f s.2) = (List.replicate ys.length ((corners b).map f)).flatten := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simpa [positions, List.map_map, Function.comp_def, List.replicate_succ] using ih
theorem variable_columns (b : B) (ys : B) :
    (positions b ys).map Prod.fst = ys.flatMap (fun y => List.replicate (corners b).length y) := by
  simp [positions, List.map_flatMap, List.map_map, Function.comp_def, List.map_const']
theorem corners_size (b : B) : (corners b).length = (pairs (0 :: b)).length := by
  rw [pairs_affine b 0 (by decide), List.length_map]
theorem positions_size (b : B) (ys : B) :
    (positions b ys).length = ys.length * (pairs (0 :: b)).length := by
  induction ys with
  | nil => simp [positions]
  | cons y ys ih =>
    change ((corners b).map (fun c => (y,c)) ++ positions b ys).length = _
    rw [List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul, corners_size, Nat.add_comm]
theorem pairs_bound (b : B) (hb : ∀ v ∈ b, v < 2^21) : ∀ v ∈ pairs b, v < 2^21 := by
  induction b with
  | nil => simp [pairs]
  | cons a t ih =>
    intro v hv
    rw [pairs, List.mem_append] at hv
    rcases hv with hw | h
    · obtain ⟨w,hw,hv⟩ := List.mem_flatMap.mp hw
      have ha := hb a (by simp)
      have hw' := hb w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Nat.lt_of_le_of_lt Nat.and_le_left ha
      · exact Nat.or_lt_two_pow ha hw'
    · exact ih (fun x hx => hb x (by simp [hx])) v h
theorem fixed_pack (b ys : B) (v : Nat) (hv : v < 2^21) (hb : ∀ a ∈ b, a < 2^21) :
    pack (pairs (v :: b)) * pattern ys.length (24 * (pairs (0 :: b)).length) =
      pack ((positions b ys).map (fun s => affine v s.2)) := by
  rw [fixed_columns, ← pairs_affine b v hv]
  have hvb : ∀ a ∈ (v::b), a < 2^21 := by simpa using And.intro hv hb
  have bound := pairs_bound _ hvb
  have size : (pairs (v :: b)).length = (pairs (0 :: b)).length := by
    rw [pairs_affine b v hv, List.length_map, corners_size]
  rw [← size, packed_rows _ _ (fun a ha => by have := bound a ha; omega)]
theorem var_pack (b ys : B) (hy : ∀ y ∈ ys, y < 2^21) :
    let h := (pairs (0::b)).length
    ys.foldr (fun v acc => (v * pattern h 24) ||| (acc <<< (24*h))) 0 =
      pack ((positions b ys).map Prod.fst) := by
  dsimp only
  rw [packed_seconds _ _ (fun a ha => by have := hy a ha; omega), variable_columns, corners_size]
theorem pos_values (b ys : B) {s : Nat × Nat × Nat} (hs : s ∈ positions b ys) :
    s.1 ∈ ys ∧ s.2 ∈ corners b := by
  obtain ⟨v,hv,hrow⟩ := List.mem_flatMap.mp hs
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hrow
  exact ⟨hv,hc⟩
def layouts (b ys : B) := (positions b ys).map (fun s => (s.1,affine s.1 s.2))
theorem geometry (b ys : B) (hb : ∀ a ∈ b, a < 2^21) (hy : ∀ y ∈ ys, y < 2^21) :
    let h := (pairs (0 :: b)).length
    let d := 24*h
    let line := pattern h 24
    let rows := pattern ys.length d
    let Y := ys.foldr (fun v acc => (v * line) ||| (acc <<< d)) 0
    let Z := (pack (pairs (0::b)) * rows) ||| (Y &&& (pack (pairs (bits::b)) * rows))
    let ps := layouts b ys
    (∀ y ∈ ys, ∀ z ∈ pairs (y::b), (y,z) ∈ ps) ∧
      rows * line = pattern ps.length 24 ∧
      Y = pack (ps.map Prod.fst) ∧ Z = pack (ps.map Prod.snd) := by
  dsimp only
  have zero := fixed_pack b ys 0 (by decide) hb
  have one := fixed_pack b ys bits (by decide) hb
  have var := var_pack b ys hy
  have fit (v : Nat) (hv : v < 2^21) (s : Nat × Nat × Nat) (hs : s ∈ positions b ys) :
      affine v s.2 < 2^24 := by
    have mem : affine v s.2 ∈ pairs (v::b) := by
      rw [pairs_affine b v hv]
      exact List.mem_map.mpr ⟨_,(pos_values _ _ hs).2,rfl⟩
    have hvb : ∀ a ∈ (v::b), a < 2^21 := by simpa using And.intro hv hb
    have := pairs_bound _ hvb _ mem
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro y hys z hz
    rw [pairs_affine b y (hy y hys)] at hz
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hz
    apply List.mem_map.mpr
    exact ⟨(y,c),List.mem_flatMap.mpr ⟨y,hys,List.mem_map.mpr ⟨c,hc,rfl⟩⟩,rfl⟩
  · rw [layouts, List.length_map, positions_size, pattern_tile]
  · simpa only [layouts, List.map_map, Function.comp_def] using var
  · rw [zero, one, var, pack_map_and, pack_map_or]
    · rw [layouts, List.map_map]
      apply congrArg pack
      apply List.map_congr_left
      intro s hs
      exact (interp _ _ (hy _ (pos_values _ _ hs).1)).symm
    · exact fit 0 (by decide)
    · intro s hs
      exact Nat.lt_of_le_of_lt Nat.and_le_left (by have := hy _ (pos_values _ _ hs).1; omega)
    · intro s hs
      have := hy _ (pos_values _ _ hs).1
      omega
    · exact fit bits (by decide)
theorem layouts_bound (b ys : B) (hb : ∀ a ∈ b, a < 2^21) (hy : ∀ y ∈ ys, y < 2^21) :
    ∀ p ∈ layouts b ys, p.1 < 2^21 ∧ p.2 < 2^21 := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hsy,hsc⟩ := pos_values _ _ hs
  have h := hy _ hsy
  have hbc : ∀ a ∈ s.1 :: b, a < 2^21 := by simpa using And.intro h hb
  refine ⟨h,pairs_bound _ hbc _ ?_⟩
  rw [pairs_affine b _ h]
  exact List.mem_map.mpr ⟨_,hsc,rfl⟩

theorem mem_pairs_spec (b : B) (v : Nat) :
    v ∈ pairs b ↔ ∃ a ∈ b, ∃ c ∈ b, v = a &&& c ∨ v = a ||| c := by
  induction b with
  | nil => simp [pairs]
  | cons a b ih =>
    change v ∈ (a :: b).flatMap (fun c => [a &&& c, a ||| c]) ++ pairs b ↔ _
    rw [List.mem_append, List.mem_flatMap, ih]
    constructor
    · rintro (⟨c,hc,hv⟩ | ⟨u,hu,c,hc,hv⟩)
      · exact ⟨a,List.mem_cons_self,c,hc,by simpa using hv⟩
      · exact ⟨u,List.mem_cons_of_mem _ hu,c,List.mem_cons_of_mem _ hc,hv⟩
    · rintro ⟨u,hu,c,hc,hv⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl ⟨c,hc,by simpa using hv⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl ⟨u,hu,by simpa [Nat.and_comm, Nat.or_comm] using hv⟩
        · exact Or.inr ⟨u,hu,c,hc,hv⟩

theorem mem_pairs_outputs {b : B} {v : Nat} : v ∈ pairs b ↔ v ∈ outputs b := by
  simp [mem_pairs_spec, outputs, List.mem_flatMap]

theorem initial_small : ∀ v ∈ initial, v < 2^21 := by
  have h : initial.all (fun v => decide (v < 2^21)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

def lanes {α : Type} (ps : List α) (f : α → Nat) := pack (ps.map f)
def width {α : Type} (ps : List α) := pattern ps.length 24
def Bounded {α : Type} (ps : List α) (f : α → Nat) (n : Nat) := ∀ p ∈ ps, f p < n

theorem mapped_bound {α : Type} {ps : List α} {f : α → Nat} {n : Nat} (h : Bounded ps f n) :
    ∀ v ∈ ps.map f, v < n := by
  intro v hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  exact h p hp

theorem zip_same {α : Type} (h : Nat → Nat → Nat) (ps : List α) (f g : α → Nat) :
    (ps.map f).zipWith h (ps.map g) = ps.map (fun p => h (f p) (g p)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

theorem lanes_and {α : Type} {ps : List α} {f g : α → Nat}
    (hf : Bounded ps f 16777216) (hg : Bounded ps g 16777216) :
    lanes ps f &&& lanes ps g = lanes ps (fun p => f p &&& g p) := by
  unfold lanes
  rw [pack_zip_and _ _ (mapped_bound hf) (mapped_bound hg) (by simp), zip_same]

theorem lanes_or {α : Type} {ps : List α} {f g : α → Nat}
    (hf : Bounded ps f 16777216) (hg : Bounded ps g 16777216) :
    lanes ps f ||| lanes ps g = lanes ps (fun p => f p ||| g p) := by
  unfold lanes
  rw [pack_zip_or _ _ (mapped_bound hf) (mapped_bound hg) (by simp), zip_same]

theorem width_map {α : Type} (ps : List α) (f : α → Nat) :
    width ps = lowOnes (ps.map f) := by
  simp [width, lowOnes, pack_replicate _ _ (by decide : 1 < 2^24)]

theorem lanes_const {α : Type} (ps : List α) (v : Nat) (hv : v < 16777216) :
    v * width ps = lanes ps (fun _ => v) := by
  simp [width, lanes, List.map_const', pack_replicate _ _ hv, Nat.mul_comm]

theorem lanes_repeated {α : Type} {ps : List α} {f : α → Nat} (hf : Bounded ps f 2097152) :
    repeated (width ps) (lanes ps f) = lanes ps (fun p => contribution (f p)) := by
  rw [width_map ps f]
  unfold lanes
  rw [pack_map_repeated _ (mapped_bound hf)]
  simp only [List.map_map]
  exact congrArg pack (List.map_congr_left fun p _ => repeated_one _)

theorem lanes_strip {α : Type} {ps : List α} {f : α → Nat} (hf : Bounded ps f 8388608) :
    strip (width ps) (lanes ps f) = lanes ps (fun p => clear (f p)) := by
  rw [width_map ps f]
  unfold lanes
  rw [pack_map_strip _ (mapped_bound hf)]
  simp only [List.map_map]
  exact congrArg pack (List.map_congr_left fun p hp => strip_one (hf p hp))

theorem bound_up {α : Type} {ps : List α} {f : α → Nat} {n m : Nat}
    (h : Bounded ps f n) (le : n ≤ m) : Bounded ps f m := fun p hp => Nat.lt_of_lt_of_le (h p hp) le

def fold_extra (w : Nat) (s : B) (acc : Nat) :=
  s.foldl (fun a v => a ||| contribution (v &&& w)) acc

theorem lanes_fold {α : Type} (ps : List α) (f : α → Nat) (hf : Bounded ps f 2097152)
    (fs : List (α → Nat)) (hs : ∀ g ∈ fs, Bounded ps g 2097152)
    (acc : α → Nat) (ha : Bounded ps acc 2048) :
    (fs.map (lanes ps)).foldl (fun t v => t ||| repeated (width ps) (v &&& lanes ps f)) (lanes ps acc)
      = lanes ps (fun p => fold_extra (f p) (fs.map (fun g => g p)) (acc p)) := by
  induction fs generalizing acc with
  | nil => rfl
  | cons g fs ih =>
    have hg := hs g List.mem_cons_self
    have hm : Bounded ps (fun p => g p &&& f p) 2097152 :=
      fun p hp => Nat.lt_of_le_of_lt Nat.and_le_left (hg p hp)
    have hc : Bounded ps (fun p => contribution (g p &&& f p)) 2048 := fun _ _ => contribution_small _
    simp only [List.map_cons, List.foldl_cons]
    rw [lanes_and (bound_up hg (by decide)) (bound_up hf (by decide)), lanes_repeated hm,
      lanes_or (bound_up ha (by decide)) (bound_up hc (by decide))]
    exact ih (fun t ht => hs _ (List.mem_cons_of_mem g ht)) _
      (fun p hp => Nat.or_lt_two_pow (n := 11) (ha p hp) (hc p hp))

theorem lanes_extras {α : Type} (ps : List α) (f : α → Nat) (hf : Bounded ps f 2097152)
    (fs : List (α → Nat)) (hs : ∀ g ∈ fs, Bounded ps g 2097152) :
    extras (width ps) (lanes ps f) (fs.map (lanes ps)) =
      lanes ps (fun p => fold_extra (f p) (fs.map (fun g => g p)) (contribution (f p))) := by
  unfold extras
  rw [lanes_repeated hf]
  apply lanes_fold _ _ hf _ hs _ (fun _ _ => contribution_small _)

theorem fold_join (w : Nat) (s : B) (e acc : Nat) :
    fold_extra w s (e ||| acc) = e ||| fold_extra w s acc := by
  induction s generalizing acc with
  | nil => rfl
  | cons v s ih =>
    change fold_extra w s ((e ||| acc) ||| contribution (v &&& w)) = e ||| fold_extra w s _
    rw [Nat.or_assoc, ih]

theorem fold_extra_eq (w : Nat) (s : B) (e : Nat) :
    e ||| fold_extra w s (contribution w) = extra s e w := by
  rw [← fold_join]
  simp only [fold_extra, extra, Nat.and_comm w]

theorem fold_small (w : Nat) (s : B) (a : Nat) (ha : a < 2048) :
    fold_extra w s a < 2048 := by
  induction s generalizing a with
  | nil => exact ha
  | cons v s ih =>
    exact ih _ (Nat.or_lt_two_pow (n := 11) ha (contribution_small (v &&& w)))

theorem extra_base (x : Nat) : extras 1 x initial = extra initial 0 x := by
  have hr (v : Nat) : repeated 1 v = contribution v := repeated_one v
  simp only [extras, hr, extra, Nat.zero_or, Nat.and_comm x]

theorem project_extras (ps : List (Nat × Nat)) (b : B) (base : Nat)
    (hy : Bounded ps Prod.fst 2097152) (hz : Bounded ps Prod.snd 2097152)
    (hb : ∀ v ∈ b, v < 2097152) (hbase : base < 2048) :
    let o := width ps
    let y := lanes ps Prod.fst
    let z := lanes ps Prod.snd
    let bs := b.map (fun v => v * o)
    (base * o) ||| extras o y bs ||| extras o z (y :: bs) =
      lanes ps (fun p => extra (p.1 :: b) (extra b base p.1) p.2) := by
  dsimp only
  let fs : List (Nat × Nat → Nat) := b.map (fun t _ => t)
  have hfs : ∀ g ∈ fs, Bounded ps g 2097152 := by
    intro g hg
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    exact fun _ _ => hb _ hv
  have hbs : b.map (fun v => v * width ps) = fs.map (lanes ps) := by
    unfold fs
    rw [List.map_map]
    exact List.map_congr_left fun v hv => lanes_const _ _ (by have := hb v hv; omega)
  have hbs' : lanes ps Prod.fst :: fs.map (lanes ps) = (Prod.fst :: fs).map (lanes ps) := rfl
  have hmap (p : Nat × Nat) : fs.map (fun g => g p) = b := by simp [fs, Function.comp_def]
  have hfs' : ∀ g ∈ Prod.fst :: fs, Bounded ps g 2097152 := by
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · exact h ▸ hy
    · exact hfs _ h
  rw [hbs, hbs', lanes_extras _ _ hy _ hfs, lanes_extras _ _ hz _ hfs',
    lanes_const _ _ (by omega : base < 16777216)]
  simp only [List.map_cons, hmap]
  have hbase' : Bounded ps (fun _ => base) 16777216 := fun _ _ => by change base < 16777216; omega
  have small (v : Nat) (s : B) : fold_extra v s (contribution v) < 2048 :=
    fold_small _ _ _ (contribution_small _)
  rw [lanes_or hbase' (fun p _ => by have := small p.1 b; omega)]
  rw [lanes_or (fun p _ => Nat.or_lt_two_pow (n := 24) (by change base < 16777216; omega) (by have := small p.1 b; omega))
    (fun p _ => by have := small p.2 (p.1 :: b); omega)]
  apply congrArg pack
  exact List.map_congr_left fun p _ => by simp only [fold_extra_eq]

theorem three_strips (ps : List (Nat × Nat)) (f : Nat × Nat → Nat)
    (hf : Bounded ps f 2048)
    (hz : strip (width ps) (strip (width ps) (strip (width ps) (lanes ps f))) = 0) :
    ∀ p ∈ ps, clear (clear (clear (f p))) = 0 := by
  have hs {g : Nat × Nat → Nat} (hg : Bounded ps g 8388608) :
      Bounded ps (fun p => clear (g p)) 8388608 :=
    fun p hp => Nat.lt_of_le_of_lt Nat.and_le_left (hg p hp)
  have h := bound_up hf (by decide : 2048 ≤ 8388608)
  rw [lanes_strip h, lanes_strip (hs h), lanes_strip (hs (hs h))] at hz
  intro p hp
  exact zero_of_pack_zero _ hz _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

def checkFields (o Y Z : Nat) (b : B) (base : Nat) : Bool :=
  let bs := b.map (fun v => v * o)
  let e := base * o ||| extras o Y bs ||| extras o Z (Y :: bs)
  strip o (strip o (strip o e)) == 0

theorem fields_zero (ps : List (Nat × Nat)) (b : B) (base : Nat)
    (hy : Bounded ps Prod.fst 2097152) (hz : Bounded ps Prod.snd 2097152)
    (hb : ∀ v ∈ b, v < 2097152) (hbase : base < 2048)
    (o Y Z : Nat) (ho : o = width ps) (hY : Y = lanes ps Prod.fst) (hZ : Z = lanes ps Prod.snd)
    (h : checkFields o Y Z b base = true) :
    ∀ p ∈ ps, clear (clear (clear (extra (p.1 :: b) (extra b base p.1) p.2))) = 0 := by
  subst o Y Z
  unfold checkFields at h
  dsimp only at h
  rw [project_extras ps b base hy hz hb hbase] at h
  exact three_strips ps _ (fun _ _ => extra_small _ _ _ (extra_small _ _ _ hbase)) (beq_iff_eq.mp h)

set_option maxHeartbeats 1600000 in
theorem checks_of_verified (verified : ∀ x ∈ (pairs initial).eraseDups, slice x = true) :
    ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial), ∀ z ∈ outputs (y :: x :: initial),
      clear (clear (clear (accumulated x y z))) = 0 := by
  intro x hx y hy z hz
  let b := x :: initial
  let ys := (pairs b).eraseDups
  let ps := layouts b ys
  have hx' := mem_pairs_outputs.mpr hx
  have hxs := pairs_bound _ initial_small x hx'
  have hb : ∀ v ∈ b, v < 2^21 := by simpa [b] using And.intro hxs initial_small
  have hys : ∀ v ∈ ys, v < 2^21 := fun v hv => pairs_bound _ hb _ (List.mem_eraseDups.mp hv)
  obtain ⟨hm,ho,hY,hZ⟩ := geometry b ys hb hys
  have hpair : (y,z) ∈ ps :=
    hm _ (List.mem_eraseDups.mpr (mem_pairs_outputs.mpr hy)) _ (mem_pairs_outputs.mpr hz)
  have hbounds := layouts_bound b ys hb hys
  have ybound : Bounded ps Prod.fst 2097152 := fun p hp => (hbounds p hp).1
  have zbound : Bounded ps Prod.snd 2097152 := fun p hp => (hbounds p hp).2
  have hbase : extra initial 0 x < 2048 := extra_small _ _ _ (by decide)
  have hbase' : extras 1 x initial < 2048 := (extra_base x).symm ▸ hbase
  have result := fields_zero ps b (extras 1 x initial) ybound zbound hb hbase' _ _ _ ho hY hZ
    (verified x (List.mem_eraseDups.mpr hx')) (y,z) hpair
  rw [extra_base x] at result
  exact result

theorem checks : ∀ x ∈ outputs initial, ∀ y ∈ outputs (x :: initial),
    ∀ z ∈ outputs (y :: x :: initial), clear (clear (clear (accumulated x y z))) = 0 := checks_of_verified complete

end PEqualNP.Outside.L_meta_53159_aux

open PEqualNP.Outside.L_meta_53159_aux in
theorem PEqualNP.Outside.L_meta_53159 : ∀ (gates : Fin 3 → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin 6 → BitVec 5 × BitVec 5),
  let read := fun (bank : List (BitVec 21)) =>
    bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0)
  let product := fun (bank : List (BitVec 21)) (pair : BitVec 5 × BitVec 5) =>
    read bank pair.1 &&& read bank pair.2
  let program := List.ofFn gates
  let bank := program.foldl (fun bank gate => bank ++
    [if gate.1 then product bank gate.2 else read bank gate.2.1 ||| read bank gate.2.2])
    (([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21))
  let affordable := program.foldr (fun gate (rest : Bool → Bool) used =>
    (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false
  let terminals := List.ofFn pairs
  (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
    ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = false := by
  exact from_checks checks
