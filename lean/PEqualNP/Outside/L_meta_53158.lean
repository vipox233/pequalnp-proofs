import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53158_aux
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

def initBank : List (BitVec 21) := ([63491, 1386508, 235568, 0, 151748, 287504, 0, 0, 558408, 1246721, 1835170, 0, 1246721, 1835170, 0, 0] : List Nat).map (BitVec.ofNat 21)
def baseBank : List (BitVec 21) := [0, 63491, 151748, 235568, 287504, 558408, 1246721, 1386508, 1835170]
def outs : List (BitVec 21) := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10240, 16384, 20480, 24576, 32768, 38912, 63491, 67584, 131072, 135168, 151748, 194759, 196608, 235568, 252148, 260147, 262144, 270336, 287504, 326419, 422868, 523056, 524288, 558408, 589131, 710092, 761208, 845656, 1048576, 1114112, 1246721, 1267397, 1285681, 1310211, 1310720, 1386508, 1403676, 1439759, 1519117, 1533713, 1538252, 1554492, 1804105, 1835170, 1860530, 1869290, 1898659, 1910958, 1944908, 1986790, 2033315, 2070706]
def chosen (o : BitVec 21) : BitVec 21 :=
  if ([2033315] : List (BitVec 21)).contains o then 509 else if ([710092] : List (BitVec 21)).contains o then 503 else if ([260147, 1860530] : List (BitVec 21)).contains o then 479 else if ([1538252, 1944908] : List (BitVec 21)).contains o then 447 else if ([194759, 252148, 1869290, 1910958] : List (BitVec 21)).contains o then 383 else if ([0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10240, 16384, 20480, 24576, 32768, 38912, 63491, 67584, 131072, 135168, 151748, 196608, 235568, 262144, 270336, 287504, 326419, 422868, 523056, 524288, 558408, 589131, 761208, 845656, 1048576, 1114112, 1246721, 1267397, 1285681, 1310211, 1310720, 1386508, 1403676, 1439759, 1519117, 1533713, 1554492, 1804105, 1835170, 1898659, 1986790, 2070706] : List (BitVec 21)).contains o then 255 else 0

theorem initial_subset : ∀ x ∈ initBank, x ∈ baseBank := by
  have h : initBank.all (fun x => baseBank.contains x) = true := by decide +kernel
  simpa only [List.all_eq_true, List.contains_iff_mem] using h
theorem available : ∀ x ∈ baseBank, ∀ y ∈ baseBank, x &&& y ∈ outs ∧ x ||| y ∈ outs := by
  have h : baseBank.all (fun x => baseBank.all (fun y => outs.contains (x &&& y) && outs.contains (x ||| y))) = true := by decide +kernel
  simpa only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] using h
theorem strengths : ∀ o ∈ outs, 7 < bitWeight (chosen o) 2047 11 := by
  have h : outs.all (fun o => decide (7 < bitWeight (chosen o) 2047 11)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h
theorem packing : ∀ o ∈ outs, ∀ x ∈ o :: baseBank, ∀ y ∈ o :: baseBank,
    (x &&& y) &&& 2095104 = 0 → bitWeight (chosen o) (x &&& y) 11 ≤ 1 := by
  have h : outs.all (fun o => (o :: baseBank).all (fun x => (o :: baseBank).all (fun y =>
    decide ((x &&& y) &&& 2095104 = 0 → bitWeight (chosen o) (x &&& y) 11 ≤ 1)))) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

def extra (gate : Bool × BitVec 5 × BitVec 5) : BitVec 21 :=
  if gate.1 then readMask initBank gate.2.1 &&& readMask initBank gate.2.2
  else readMask initBank gate.2.1 ||| readMask initBank gate.2.2

theorem read_init (i : BitVec 5) : readMask initBank i ∈ baseBank := by
  rcases readMask_mem initBank i with h | h
  · exact initial_subset _ h
  · rw [h]
    decide

theorem extra_mem (g : Bool × BitVec 5 × BitVec 5) : extra g ∈ outs := by
  have h := available _ (read_init g.2.1) _ (read_init g.2.2)
  unfold extra
  split
  · exact h.1
  · exact h.2

theorem final_read (o : BitVec 21) (i : BitVec 5) : readMask (initBank ++ [o]) i ∈ o :: baseBank := by
  rcases readMask_mem (initBank ++ [o]) i with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_cons_of_mem _ (initial_subset _ h)
    · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
  · rw [h]
    exact List.mem_cons_of_mem _ (by decide : (0 : BitVec 21) ∈ baseBank)

end PEqualNP.Outside.L_meta_53158_aux

open PEqualNP.Outside.L_meta_53158_aux in
theorem PEqualNP.Outside.L_meta_53158 : ∀ (gates : Fin 1 → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin 7 → BitVec 5 × BitVec 5),
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
  dsimp only
  have one : List.ofFn gates = [gates 0] := by rw [List.ofFn_succ]; rfl
  rw [one]
  let o := extra (gates 0)
  let prod := fun (p : BitVec 5 × BitVec 5) => readMask (initBank ++ [o]) p.1 &&& readMask (initBank ++ [o]) p.2
  have ho := extra_mem (gates 0)
  apply terminal_impossible prod (chosen o)
  · intro p
    exact packing o ho _ (final_read o p.1) _ (final_read o p.2)
  · simpa using strengths o ho
