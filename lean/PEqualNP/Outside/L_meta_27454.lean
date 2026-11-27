import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_27454

open PEqualNP.CircuitLowerBounds

private abbrev Word := Fin 9 → Bool
private abbrev Fix := Option (Fin 9 × Bool)

private def keep (m : Fix) : Finset (Fin 9) :=
  match m with
  | none => Finset.univ.erase 0
  | some (p, _) => (Finset.univ.erase 0).erase p

private def freeze (m : Fix) (x : Word) : Word :=
  fun i => if i = 0 then true else
    match m with
    | none => x i
    | some (p, b) => if i = p then b else x i

private def matching (x : Word) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def restricted (m : Fix) (x : Word) : Bool := matching (freeze m x)

private lemma freeze_free {m : Fix} {i : Fin 9} (hi : i ∈ keep m) (x : Word) :
    freeze m x i = x i := by
  cases m with
  | none => simp [freeze, (Finset.mem_erase.mp hi).1]
  | some pair =>
    rcases pair with ⟨p, b⟩
    obtain ⟨hip, hi⟩ := Finset.mem_erase.mp hi
    simp [freeze, hip, (Finset.mem_erase.mp hi).1]

private lemma freeze_fixed {m : Fix} {i : Fin 9} (hi : i ∉ keep m) (x y : Word) :
    freeze m x i = freeze m y i := by
  cases m with
  | none =>
    have hi0 : i = 0 := by simpa [keep] using hi
    simp [freeze, hi0]
  | some pair =>
    rcases pair with ⟨p, b⟩
    have hp : i = p ∨ i = 0 := by
      by_cases eq : i = p
      · exact Or.inl eq
      · exact Or.inr (by simpa [keep, eq] using hi)
    rcases hp with rfl | rfl <;> simp [freeze]

private lemma freeze_twice (p : Fin 9) (b : Bool) (x : Word) :
    freeze (some (p, b)) x = freeze none (Function.update x p b) := by
  funext i
  by_cases hi : i = 0 <;> simp [freeze, hi, Function.update_apply]

private def pairWord (x : Word) (i j : Fin 9) (a b : Bool) : Word :=
  fun k => if k = i then a else if k = j then b else x k

private def rowWord (r : Nat) : Word := fun i => r.testBit i.val

private def table : Array (Array Nat) := #[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 49284, 49220, 32896, 16404, 135180, 4112, 0, 41056, 0, 41218, 33024, 41026, 8226, 4128, 69642, 0, 67680, 65616, 0, 67652, 132162, 67604, 2080, 1040, 0, 34912, 32904, 34948, 0, 34882, 2082, 34828, 10, 0, 33032, 33872, 33924, 33860, 0, 1044, 12, 33802, 0, 10504, 8328, 10372, 2304, 1152, 0, 10252, 17418, 0, 6240, 4176, 2306, 6212, 66, 6164, 0, 6154, 0, 4192, 5200, 1156, 68, 5186, 5140, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 49284, 49220, 32896, 16404, 135180, 4112, 0, 41056, 0, 41218, 33024, 41026, 8226, 4128, 69642, 0, 67680, 65616, 0, 67652, 132162, 67604, 2080, 1040, 0, 34912, 32904, 34948, 0, 34882, 2082, 34828, 10, 0, 33032, 33872, 33924, 33860, 0, 1044, 12, 33802, 0, 10504, 8328, 10372, 2304, 1152, 0, 10252, 17418, 0, 6240, 4176, 2306, 6212, 66, 6164, 0, 6154, 0, 4192, 5200, 1156, 68, 5186, 5140, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 49284, 49220, 32896, 16404, 135180, 4112, 0, 41056, 0, 41218, 33024, 41026, 8226, 4128, 69642, 0, 67680, 65616, 0, 67652, 132162, 67604, 2080, 1040, 0, 34912, 32904, 34948, 0, 34882, 2082, 34828, 10, 0, 33032, 33872, 33924, 33860, 0, 1044, 12, 33802, 0, 10504, 8328, 10372, 2304, 1152, 0, 10252, 17418, 0, 6240, 4176, 2306, 6212, 66, 6164, 0, 6154, 0, 4192, 5200, 1156, 68, 5186, 5140, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 327760, 33024, 41088, 270472, 4128, 69648, 0, 0, 65616, 0, 67652, 327812, 67604, 2080, 67600, 0, 0, 32904, 34948, 0, 34944, 264448, 34828, 262212, 0, 0, 65616, 65668, 65604, 0, 65556, 12, 65552, 0, 0, 8328, 10372, 2304, 10368, 0, 10252, 270356, 0, 0, 4176, 264224, 6212, 262156, 6164, 0, 6160, 0, 0, 8272, 8324, 68, 8320, 8212, 8204, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41216, 33024, 294992, 8224, 4128, 266320, 0, 0, 65616, 0, 67652, 131136, 67604, 2080, 16, 0, 0, 32904, 34948, 0, 131136, 2080, 34828, 8, 0, 0, 32848, 32900, 32836, 0, 20, 12, 32776, 0, 0, 8328, 10372, 2304, 128, 0, 10252, 16392, 0, 0, 4176, 2304, 6212, 64, 6164, 0, 16392, 0, 0, 4176, 132, 68, 4160, 4116, 4108, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 393312, 49408, 32896, 278792, 135200, 4112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131168, 0, 0, 393474, 132162, 132130, 132128, 1040, 0, 131168, 0, 131330, 0, 131138, 131106, 131104, 10, 0, 33032, 0, 34050, 34048, 0, 263296, 262210, 33802, 0, 16648, 0, 17666, 17664, 1152, 0, 278562, 17418, 0, 16480, 0, 16642, 16640, 66, 16418, 0, 16394, 0, 4192, 0, 263184, 262154, 5186, 5154, 5152, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49280, 295008, 32896, 16400, 266336, 4112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65632, 0, 0, 65600, 132162, 65552, 32, 1040, 0, 32864, 0, 32896, 0, 32834, 34, 32776, 10, 0, 33032, 0, 33920, 65600, 0, 1040, 8, 33802, 0, 8456, 0, 8320, 256, 1152, 0, 8200, 17418, 0, 4192, 0, 258, 4160, 66, 4112, 0, 4106, 0, 4192, 0, 1152, 64, 5186, 5136, 8200, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 0, 49220, 32896, 16404, 278624, 49168, 0, 41056, 0, 0, 33024, 41026, 8226, 40992, 270416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34912, 295168, 0, 0, 34882, 2082, 34848, 262212, 0, 295040, 33872, 0, 33860, 0, 1044, 262210, 33808, 0, 278548, 270370, 0, 2304, 1152, 0, 10272, 17424, 0, 16480, 16464, 0, 16452, 66, 16404, 0, 16400, 0, 8288, 8272, 0, 68, 8258, 8212, 8224, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 0, 49220, 32896, 16404, 131076, 16, 0, 41056, 0, 0, 33024, 41026, 8226, 32, 65538, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34912, 32896, 0, 0, 34882, 2082, 131076, 2, 0, 33024, 33872, 0, 33860, 0, 1044, 4, 65538, 0, 10496, 8320, 0, 2304, 1152, 0, 264212, 263188, 0, 2144, 80, 0, 2116, 66, 2068, 0, 2050, 0, 96, 1104, 0, 68, 1090, 1044, 1028, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49288, 49284, 0, 32896, 278792, 135180, 266336, 0, 69728, 0, 65794, 0, 296072, 69666, 4128, 69642, 0, 67680, 327938, 0, 0, 132162, 67618, 2080, 263300, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33032, 33928, 33924, 0, 0, 263296, 12, 33802, 0, 16648, 17544, 17540, 0, 1152, 0, 268322, 17418, 0, 6240, 266272, 2306, 0, 66, 6178, 0, 6154, 0, 4192, 5256, 1156, 0, 5186, 5154, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 295008, 49284, 0, 32896, 16388, 268384, 262240, 0, 32864, 0, 327744, 0, 32834, 34, 4128, 262208, 0, 67680, 65600, 0, 0, 296068, 264324, 2080, 262276, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 295040, 65600, 33924, 0, 0, 1028, 12, 262210, 0, 278532, 136, 2180, 0, 1152, 0, 2060, 262148, 0, 6240, 4160, 264224, 0, 66, 16388, 0, 262156, 0, 96, 64, 132, 0, 66, 4, 12, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135248, 131204, 297224, 0, 135188, 135180, 4112, 0, 41224, 0, 41218, 33024, 0, 270472, 266320, 69642, 0, 393348, 65616, 0, 67652, 0, 67604, 264450, 1040, 0, 35080, 32904, 34948, 0, 0, 264448, 34828, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10504, 8328, 10372, 2304, 0, 0, 10252, 267284, 0, 6408, 4176, 2306, 6212, 0, 6164, 0, 6154, 0, 266256, 5200, 1156, 68, 0, 5140, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32848, 393280, 32836, 0, 20, 262208, 4112, 0, 294992, 0, 41218, 33024, 0, 8194, 262224, 267344, 0, 131136, 132176, 0, 297218, 0, 263426, 262402, 1040, 0, 131136, 295168, 35074, 0, 0, 2050, 262212, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 264, 270338, 1282, 1280, 0, 0, 262146, 1034, 0, 64, 80, 258, 68, 0, 2, 0, 10, 0, 4160, 5200, 263184, 68, 0, 8194, 262154, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135304, 131204, 393480, 135296, 0, 135180, 4112, 0, 69896, 0, 65794, 69888, 327816, 0, 4128, 69642, 0, 393348, 327938, 0, 67840, 132224, 0, 2080, 1040, 0, 131336, 131208, 131204, 0, 131200, 0, 131084, 10, 0, 65800, 65672, 65668, 65792, 0, 0, 12, 65546, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6408, 266272, 2306, 6400, 262156, 0, 0, 6154, 0, 266256, 5256, 1156, 262154, 5248, 0, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16400, 16516, 16388, 128, 0, 135180, 4112, 0, 8224, 0, 8450, 256, 8194, 0, 4128, 69642, 0, 67616, 65552, 0, 264324, 263300, 0, 2080, 1040, 0, 2080, 136, 2180, 0, 2050, 0, 2060, 10, 0, 264, 1040, 1156, 1028, 0, 0, 12, 1034, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6176, 4112, 2306, 16388, 2, 0, 0, 6154, 0, 4128, 5136, 1156, 4, 8194, 0, 5132, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 393312, 49220, 295176, 16404, 0, 4112, 0, 41056, 0, 41218, 33024, 41026, 8226, 0, 267344, 0, 131168, 132176, 0, 297218, 132162, 132116, 0, 1040, 0, 34912, 295168, 35074, 0, 34882, 2082, 0, 10, 0, 33032, 33872, 34050, 33860, 0, 1044, 0, 33802, 0, 10504, 270370, 10498, 2304, 263188, 0, 0, 17418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4192, 5200, 263184, 68, 5186, 5140, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 266504, 131076, 297224, 262408, 135188, 0, 4112, 0, 4360, 0, 258, 4352, 262152, 270344, 0, 4106, 0, 393220, 80, 0, 2116, 262148, 2068, 0, 1040, 0, 35080, 32776, 131076, 0, 262212, 264448, 0, 10, 0, 264, 8, 4, 68, 0, 20, 0, 10, 0, 10504, 8200, 264212, 2304, 262164, 0, 0, 267284, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 266256, 8200, 1028, 68, 262154, 5140, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49232, 49284, 49220, 32896, 16404, 268384, 0, 0, 41056, 0, 327760, 295048, 41026, 8226, 4128, 0, 0, 67680, 65616, 0, 67652, 296068, 67604, 2080, 0, 0, 34912, 32904, 34948, 0, 34882, 2082, 34828, 0, 0, 295040, 33872, 33924, 33860, 0, 1044, 12, 0, 0, 278548, 8328, 10372, 264226, 1152, 0, 10252, 0, 0, 6240, 4176, 264224, 6212, 66, 6164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4232, 132, 262152, 4224, 278536, 4108, 0, 0, 266376, 0, 65538, 262280, 296072, 69666, 4128, 0, 0, 96, 327682, 0, 262146, 1090, 1058, 1056, 0, 0, 8, 136, 2, 0, 66, 34, 12, 0, 0, 32776, 33928, 65538, 262210, 0, 263296, 12, 0, 0, 16392, 17544, 263202, 262178, 1152, 0, 268322, 0, 0, 16392, 266272, 2050, 262156, 66, 6178, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

private def fixIndex : Fix → Nat
  | none => 0
  | some (p, b) => 1 + 2 * p.val + b.toNat

private def witness (m : Fix) (i j : Fin 9) : Nat :=
  (table[fixIndex m]?.getD #[])[i.val * 9 + j.val]?.getD 0

private def pattern (f : Word → Bool) (i j : Fin 9) (n : Nat) : Prop :=
  let t := n.testBit 18
  let x := rowWord (n % 512)
  let y := rowWord (n / 512 % 512)
  f (pairWord x i j false false) = false ∧
  f (pairWord x i j t (!t)) = true ∧
  f (pairWord x i j true true) = true ∧
  f (pairWord y i j t (!t)) = false ∧
  f (pairWord y i j true true) = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem patterns_checked :
    ∀ (m : Fix) (i j : Fin 9), i ∈ keep m → j ∈ keep m → i ≠ j →
      pattern (restricted m) i j (witness m i j) := by
  let (m : Fix) (i j : Fin 9) : Decidable (pattern (restricted m) i j (witness m i j)) := by
    unfold pattern
    infer_instance
  decide

private def noPair (m : Fix) : Prop :=
  ∀ i ∈ keep m, ∀ j ∈ keep m, i ≠ j → ∀ h : Bool → Bool → Bool,
    ¬ ∀ x y : Word, (∀ k, k ≠ i → k ≠ j → x k = y k) →
      h (x i) (x j) = h (y i) (y j) → restricted m x = restricted m y

private lemma avoid_pair (m : Fix) : noPair m := by
  intro i hi j hj ne h factored
  let n := witness m i j
  let t := n.testBit 18
  let x := rowWord (n % 512)
  let y := rowWord (n / 512 % 512)
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := patterns_checked m i j hi hj ne
  have same (z : Word) (a b c d : Bool) (hs : h a b = h c d) :
      restricted m (pairWord z i j a b) = restricted m (pairWord z i j c d) := by
    apply factored _ _
    · intro k hki hkj
      simp [pairWord, hki, hkj]
    · simpa [pairWord, ne.symm] using hs
  have collision : h false false = h t (!t) ∨ h false false = h true true ∨
      h t (!t) = h true true := by
    cases h false false <;> cases h t (!t) <;> cases h true true <;> decide
  rcases collision with hs | hs | hs
  · have contradiction := h₀.symm.trans ((same x _ _ _ _ hs).trans h₁)
    cases contradiction
  · have contradiction := h₀.symm.trans ((same x _ _ _ _ hs).trans h₂)
    cases contradiction
  · have contradiction := h₃.symm.trans ((same y _ _ _ _ hs).trans h₄)
    cases contradiction

private lemma keep_card (m : Fix) : 7 ≤ (keep m).card := by
  have h : (Finset.univ.erase (0 : Fin 9)).card = 8 := by decide
  cases m with
  | none => simp [keep, h]
  | some pair =>
    rcases pair with ⟨p, b⟩
    by_cases hp : p ∈ Finset.univ.erase (0 : Fin 9)
    · have := Finset.card_erase_add_one hp
      simp only [keep]
      omega
    · simp [keep, Finset.erase_eq_of_notMem hp, h]

private lemma essential (m : Fix) {i : Fin 9} (hi : i ∈ keep m) :
    ∃ x y : Word, (∀ k, k ≠ i → x k = y k) ∧ restricted m x ≠ restricted m y := by
  have positive : 0 < ((keep m).erase i).card := by
    have := Finset.card_erase_add_one hi
    have := keep_card m
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp positive
  obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
  let n := witness m i j
  let t := n.testBit 18
  let x := rowWord (n % 512)
  let y := rowWord (n / 512 % 512)
  have h : pattern (restricted m) i j n := patterns_checked m i j hi hj hne.symm
  change restricted m (pairWord x i j false false) = false ∧
    restricted m (pairWord x i j t (!t)) = true ∧
    restricted m (pairWord x i j true true) = true ∧
    restricted m (pairWord y i j t (!t)) = false ∧
    restricted m (pairWord y i j true true) = true at h
  obtain ⟨h₀, h₁, _, h₃, h₄⟩ := h
  cases ht : t
  · refine ⟨pairWord y i j t (!t), pairWord y i j true true, ?_, ?_⟩
    · intro k hk
      simp [pairWord, hk, ht]
    · simp [h₃, h₄]
  · refine ⟨pairWord x i j false false, pairWord x i j t (!t), ?_, ?_⟩
    · intro k hk
      simp [pairWord, hk, ht]
    · simp [h₀, h₁]

private abbrev Wires := Nat → Word → Bool

private def constant (f : Word → Bool) : Prop := ∀ x y, f x = f y

private def fresh (W : Wires) (v : Nat) : Prop :=
  ¬ constant (W v) ∧ ∀ i < v, W i ≠ W v

private noncomputable def rep (W : Wires) (v : Nat) : Nat := by
  classical
  exact Nat.find (show ∃ a, W a = W v from ⟨v, rfl⟩)

private lemma rep_value (W : Wires) (v : Nat) : W (rep W v) = W v := by
  classical
  exact Nat.find_spec (show ∃ a, W a = W v from ⟨v, rfl⟩)

private lemma rep_bound (W : Wires) {i v : Nat} (eq : W i = W v) : rep W v ≤ i := by
  classical
  exact Nat.find_min' (show ∃ a, W a = W v from ⟨v, rfl⟩) eq

private lemma rep_fresh (W : Wires) {v : Nat} (hv : ¬ constant (W v)) :
    fresh W (rep W v) := by
  refine ⟨by rwa [rep_value W v], ?_⟩
  intro i hi eq
  have := rep_bound W (eq.trans (rep_value W v))
  omega

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma stable (G : List Gate) (s : List Bool) (i : Nat) (hi : i < s.length) :
    (G.foldl gateStep s).getD i false = s.getD i false := by
  induction G generalizing s with
  | nil => rfl
  | cons g G ih =>
    simp only [List.foldl_cons]
    rw [ih (gateStep s g) (by simp [gateStep]; omega)]
    exact List.getD_append _ _ _ _ hi

private lemma gate_value (G : List Gate) (s : List Bool) (j : Fin G.length)
    (before : ∀ a ∈ (G.get j).inputs, a < s.length + j.val) :
    (G.foldl gateStep s).getD (s.length + j.val) false =
      (G.get j).op.eval ((G.get j).inputs.map fun a => (G.foldl gateStep s).getD a false) := by
  induction G generalizing s with
  | nil => exact Fin.elim0 j
  | cons g G ih =>
    cases j using Fin.cases with
    | zero =>
      simp only [List.get_cons_zero, Fin.val_zero, Nat.add_zero] at before ⊢
      rw [List.foldl_cons, stable G (gateStep s g) s.length (by simp [gateStep])]
      conv_lhs => unfold gateStep
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro a ha
      rw [stable G (gateStep s g) a (by simp [gateStep]; have := before a ha; omega)]
      exact (List.getD_append _ _ _ _ (before a ha)).symm
    | succ j =>
      change ∀ a ∈ (G.get j).inputs, a < s.length + (j.val + 1) at before
      change (G.foldl gateStep (gateStep s g)).getD (s.length + (j.val + 1)) false = _
      have size : (gateStep s g).length + j.val = s.length + (j.val + 1) := by
        simp [gateStep]
        omega
      rw [← size]
      exact ih (gateStep s g) j (by simpa only [size] using before)

private def wire (C : Circuit) (m : Fix) : Wires :=
  fun i x => (C.wires (List.ofFn (freeze m x))).getD i false

private lemma wire_input (C : Circuit) (m : Fix) (i : Fin 9) (x : Word) :
    wire C m i.val x = freeze m x i := by
  unfold wire Circuit.wires
  change (C.gates.foldl gateStep _).getD i.val false = _
  rw [stable C.gates _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some, Fin.eta]

private def normal (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧
      (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

private lemma gate_wire (C : Circuit) (m : Fix) (j : Fin C.gates.length)
    (before : ∀ a ∈ (C.gates.get j).inputs, a < 9 + j.val) :
    wire C m (9 + j.val) = fun x =>
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun a => wire C m a x) := by
  funext x
  change (C.gates.foldl gateStep (List.ofFn (freeze m x))).getD (9 + j.val) false =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun a =>
      (C.gates.foldl gateStep (List.ofFn (freeze m x))).getD a false)
  simpa only [List.length_ofFn] using
    gate_value C.gates (List.ofFn (freeze m x)) j (by simpa only [List.length_ofFn] using before)

private lemma gate_shape (C : Circuit) (m : Fix) (h : normal C) {v : Nat}
    (lo : 9 ≤ v) (hi : v < 9 + C.gates.length) :
    (∃ a < v, wire C m v = fun x => !(wire C m a x)) ∨
    ∃ a b, a < b ∧ b < v ∧
      (wire C m v = (fun x => wire C m a x && wire C m b x) ∨
       wire C m v = (fun x => wire C m a x || wire C m b x)) := by
  let j : Fin C.gates.length := ⟨v - 9, by omega⟩
  have pos : 9 + j.val = v := by dsimp [j]; omega
  rcases h j with ⟨op, a, ha, inputs⟩ | ⟨op, a, b, hab, hb, inputs⟩
  · have hw := gate_wire C m j (by rw [inputs]; simpa using ha)
    rw [pos, op, inputs] at hw
    exact Or.inl ⟨a, by omega, by simpa [GateOp.eval] using hw⟩
  · have hw := gate_wire C m j (by
      intro c hc
      simp only [inputs, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> omega)
    refine Or.inr ⟨a, b, hab, by omega, ?_⟩
    rcases op with op | op
    · rw [pos, op, inputs] at hw
      exact Or.inl (by simpa [GateOp.eval] using hw)
    · rw [pos, op, inputs] at hw
      exact Or.inr (by simpa [GateOp.eval] using hw)

private lemma wire_freeze (C : Circuit) (p : Fin 9) (b : Bool) (v : Nat) (x : Word) :
    wire C (some (p, b)) v x = wire C none v (Function.update x p b) := by
  simp only [wire, freeze_twice]

private lemma frozen_fresh (C : Circuit) (p : Fin 9) (b : Bool) {v : Nat}
    (h : fresh (wire C (some (p, b))) v) : fresh (wire C none) v := by
  refine ⟨?_, ?_⟩
  · intro hc
    apply h.1
    intro x y
    simpa only [wire_freeze] using hc (Function.update x p b) (Function.update y p b)
  · intro j hj eq
    apply h.2 j hj
    funext x
    simpa only [wire_freeze] using congrFun eq (Function.update x p b)

private def binary (op a b : Bool) : Bool := if op then a && b else a || b

private def gateLaw (W : Wires) (v : Nat) (P : Finset Nat) : Prop :=
  (∃ a, P = {a} ∧ W v = fun x => !(W a x)) ∨
  ∃ (a b : Nat) (op : Bool), a ≠ b ∧ P = {a, b} ∧
    W v = fun x => binary op (W a x) (W b x)

private lemma law_congr {W : Wires} {v : Nat} {P : Finset Nat} (law : gateLaw W v P)
    {x y : Word} (eq : ∀ a ∈ P, W a x = W a y) : W v x = W v y := by
  rcases law with ⟨a, rfl, formula⟩ | ⟨a, b, op, ne, rfl, formula⟩
  · simp only [formula, eq a (by simp)]
  · simp only [formula, eq a (by simp), eq b (by simp)]

private lemma constant_parent {W : Wires} {v p : Nat} {P : Finset Nat}
    (law : gateLaw W v P) (hp : p ∈ P) (hc : constant (W p)) :
    constant (W v) ∨ ∃ a ∈ P, W v = W a := by
  rcases law with ⟨a, rfl, formula⟩ | ⟨a, b, op, ne, rfl, formula⟩
  · have eq : p = a := by simpa using hp
    subst p
    exact Or.inl (fun x y => by simp only [formula, hc x y])
  · have h : p = a ∨ p = b := by simpa using hp
    rcases h with h | h
    · subst p
      have eval (x : Word) := hc x (fun _ => false)
      cases op <;> cases hval : W a (fun _ => false)
      · right
        exact ⟨b, by simp, funext fun x => by simp [formula, binary, eval x, hval]⟩
      · left
        intro x y
        simp [formula, binary, eval x, eval y, hval]
      · left
        intro x y
        simp [formula, binary, eval x, eval y, hval]
      · right
        exact ⟨b, by simp, funext fun x => by simp [formula, binary, eval x, hval]⟩
    · subst p
      have eval (x : Word) := hc x (fun _ => false)
      cases op <;> cases hval : W b (fun _ => false)
      · right
        exact ⟨a, by simp, funext fun x => by simp [formula, binary, eval x, hval]⟩
      · left
        intro x y
        simp [formula, binary, eval x, eval y, hval]
      · left
        intro x y
        simp [formula, binary, eval x, eval y, hval]
      · right
        exact ⟨a, by simp, funext fun x => by simp [formula, binary, eval x, hval]⟩

private def reach (P : Nat → Finset Nat) :=
  Relation.ReflTransGen (fun a b => a ∈ P b)

private structure Graph where
  W : Wires
  P : Nat → Finset Nat
  V : Finset Nat
  I : Finset (Fin 9)
  root : Nat
  root_mem : root ∈ V
  closes : ∀ v ∈ V, ∀ a ∈ P v, a ∈ V
  earlier : ∀ v ∈ V, ∀ a ∈ P v, a < v
  inputs : ∀ i : Fin 9, i.val ∈ V ↔ i ∈ I
  input_value : ∀ i ∈ I, W i.val = fun x => x i
  input_empty : ∀ i : Fin 9, P i.val = ∅
  unique : ∀ v ∈ V, fresh W v
  gates : ∀ v ∈ V, 9 ≤ v → gateLaw W v (P v)
  connected : ∀ v ∈ V, reach P v root

private noncomputable def children (G : Graph) (a : Nat) : Finset Nat :=
  G.V.filter (fun v => a ∈ G.P v)

private noncomputable def support (G : Graph) (v : Nat) : Finset (Fin 9) := by
  classical
  exact G.I.filter (fun i => reach G.P i.val v)

private lemma reach_mem (G : Graph) {a b : Nat} (r : reach G.P a b) (hb : b ∈ G.V) :
    a ∈ G.V := by
  revert hb
  induction r with
  | refl => exact id
  | tail prev edge ih =>
    intro hb
    exact ih (G.closes _ hb _ edge)

private lemma reach_le (G : Graph) {a b : Nat} (r : reach G.P a b) (hb : b ∈ G.V) :
    a ≤ b := by
  revert hb
  induction r with
  | refl => exact fun _ => le_rfl
  | tail prev edge ih =>
    intro hb
    exact (ih (G.closes _ hb _ edge)).trans (G.earlier _ hb _ edge).le

private lemma parent_of_path (G : Graph) {a b : Nat}
    (h : reach G.P a b) (ne : a ≠ b) :
    ∃ c ∈ G.P b, reach G.P a c := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, prev, edge⟩
  · exact False.elim (ne h.symm)
  · exact ⟨c, edge, prev⟩

private lemma children_mem (G : Graph) {u v : Nat} :
    v ∈ children G u ↔ v ∈ G.V ∧ u ∈ G.P v := by
  simp [children]

private lemma child_exists (G : Graph) {v : Nat} (hv : v ∈ G.V) (ne : v ≠ G.root) :
    (children G v).Nonempty := by
  rcases Relation.ReflTransGen.cases_head (G.connected v hv) with eq | ⟨u, edge, next⟩
  · exact False.elim (ne eq)
  · exact ⟨u, (children_mem G).mpr ⟨reach_mem G next G.root_mem, edge⟩⟩

private lemma support_value (G : Graph) {v : Nat} (hv : v ∈ G.V)
    (x y : Word) (eq : ∀ i ∈ support G v, x i = y i) : G.W v x = G.W v y := by
  classical
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases hi : v < 9
    · let i : Fin 9 := ⟨v, hi⟩
      have hm : i ∈ G.I := (G.inputs i).mp hv
      have hs : i ∈ support G v := Finset.mem_filter.mpr ⟨hm, .refl⟩
      change G.W i.val x = G.W i.val y
      rw [G.input_value i hm]
      exact eq i hs
    · apply law_congr (G.gates v hv (by omega))
      intro a ha
      apply ih a (G.earlier v hv a ha) (G.closes v hv a ha)
      intro i hi
      have ⟨hi, r⟩ := Finset.mem_filter.mp hi
      exact eq i (Finset.mem_filter.mpr ⟨hi, r.tail ha⟩)

private lemma cut_value (G : Graph) {q : Nat} (hq : q ∈ G.V)
    (small : ∀ a, reach G.P a q → a ≠ q → (children G a).card ≤ 1)
    (x y : Word) (outside : ∀ i ∈ G.I, i ∉ support G q → x i = y i)
    (same : G.W q x = G.W q y) : G.W G.root x = G.W G.root y := by
  classical
  have only_q : ∀ v ∈ G.V, ¬ (reach G.P v q ∧ v ≠ q) → G.W v x = G.W v y := by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv not_before
      by_cases qeq : v = q
      · rwa [qeq]
      · by_cases hi : v < 9
        · let i : Fin 9 := ⟨v, hi⟩
          have hm : i ∈ G.I := (G.inputs i).mp hv
          have hs : i ∉ support G q := fun hs =>
            not_before ⟨(Finset.mem_filter.mp hs).2, qeq⟩
          change G.W i.val x = G.W i.val y
          rw [G.input_value i hm]
          exact outside i hm hs
        · apply law_congr (G.gates v hv (by omega))
          intro a ha
          apply ih a (G.earlier v hv a ha) (G.closes v hv a ha)
          rintro ⟨r, ne⟩
          rcases Relation.ReflTransGen.cases_head r with eq | ⟨b, edge, rest⟩
          · exact ne eq
          · have bv := reach_mem G rest hq
            have beq := Finset.card_le_one.mp (small a r ne) b
              ((children_mem G).mpr ⟨bv, edge⟩) v ((children_mem G).mpr ⟨hv, ha⟩)
            exact not_before ⟨beq ▸ rest, qeq⟩
  apply only_q G.root G.root_mem
  rintro ⟨h, ne⟩
  exact ne (Nat.le_antisymm (reach_le G h hq) (reach_le G (G.connected q hq) G.root_mem))

private lemma support_input (G : Graph) {i : Fin 9} (hi : i ∈ G.I) :
    support G i.val = {i} := by
  classical
  ext j
  simp only [support, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    rcases Relation.ReflTransGen.cases_tail h with eq | ⟨k, _, hm⟩
    · exact Fin.ext eq.symm
    · have hm' : k ∈ G.P i.val := hm
      rw [G.input_empty] at hm'
      exact False.elim (Finset.notMem_empty _ hm')
  · rintro rfl
    exact ⟨hi, .refl⟩

private lemma support_union (G : Graph) {v : Nat} (hv : 9 ≤ v) :
    support G v = (G.P v).biUnion (support G) := by
  classical
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hi, r⟩
    obtain ⟨a, ha, rest⟩ := parent_of_path G r (by have := i.isLt; omega)
    exact ⟨a, ha, hi, rest⟩
  · rintro ⟨a, ha, hi, rest⟩
    exact ⟨hi, rest.tail ha⟩

private lemma unary_support (G : Graph) {v : Nat} (hv : v ∈ G.V)
    (none_binary : ∀ a ∈ G.V, reach G.P a v → (G.P a).card ≠ 2) :
    ∃ i ∈ G.I, support G v = {i} := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases h : v < 9
    · let i : Fin 9 := ⟨v, h⟩
      have hi := (G.inputs i).mp hv
      exact ⟨i, hi, support_input G hi⟩
    · rcases G.gates v hv (by omega) with ⟨a, pars, _⟩ | ⟨a, b, op, ne, pars, _⟩
      · have ha : a ∈ G.P v := by simp [pars]
        obtain ⟨i, hi, eq⟩ := ih a (G.earlier _ hv _ ha) (G.closes _ hv _ ha)
          (fun u hu r => none_binary u hu (r.tail ha))
        refine ⟨i, hi, ?_⟩
        rwa [support_union G (by omega), pars, Finset.singleton_biUnion]
      · exact False.elim (none_binary v hv .refl (by simp [pars, ne]))

private lemma unary_forms (f : Word → Bool) (i : Fin 9)
    (depend : ∀ x y : Word, x i = y i → f x = f y)
    (nonconst : ¬ constant f) :
    f = (fun x => x i) ∨ f = (fun x => !(x i)) := by
  have eval (x : Word) := depend x (fun _ => x i) rfl
  have distinct : f (fun _ => false) ≠ f (fun _ => true) := by
    intro eq
    apply nonconst
    intro x y
    rw [eval x, eval y]
    cases x i <;> cases y i <;> simp [eq]
  cases h₀ : f (fun _ => false) <;> cases h₁ : f (fun _ => true)
  · exact False.elim (distinct (h₀.trans h₁.symm))
  · left
    funext x
    rw [eval x]
    cases x i <;> assumption
  · right
    funext x
    rw [eval x]
    cases x i <;> assumption
  · exact False.elim (distinct (h₀.trans h₁.symm))

private lemma distinct_wires (G : Graph) {a b : Nat} (ha : a ∈ G.V) (hb : b ∈ G.V)
    (ne : a ≠ b) : G.W a ≠ G.W b := by
  rcases lt_or_gt_of_ne ne with h | h
  · exact (G.unique b hb).2 a h
  · exact fun eq => (G.unique a ha).2 b h eq.symm

private lemma pure_pair_impossible (G : Graph) (m : Fix)
    (out : G.W G.root = restricted m) (inputs : G.I = keep m) {v : Nat} (hv : v ∈ G.V)
    (binary_gate : (G.P v).card = 2)
    (none_binary : ∀ a ∈ G.V, reach G.P a v → a ≠ v → (G.P a).card ≠ 2)
    (small : ∀ a, reach G.P a v → a ≠ v → (children G a).card ≤ 1) : False := by
  classical
  have hg : 9 ≤ v := by
    by_contra! h
    have empty := G.input_empty (⟨v, h⟩ : Fin 9)
    change G.P v = ∅ at empty
    simp [empty] at binary_gate
  rcases G.gates v hv hg with ⟨a, pars, _⟩ | ⟨a, b, op, ab, pars, formula⟩
  · simp [pars] at binary_gate
  · have support_parent (p : Nat) (hp : p ∈ G.P v) : ∃ i ∈ G.I, support G p = {i} := by
      apply unary_support G (G.closes _ hv _ hp)
      intro a ha r
      have lt := (reach_le G r (G.closes _ hv _ hp)).trans_lt (G.earlier _ hv _ hp)
      exact none_binary a ha (r.tail hp) lt.ne
    have ap : a ∈ G.P v := by simp [pars]
    have bp : b ∈ G.P v := by simp [pars]
    obtain ⟨i, hi, sa⟩ := support_parent a ap
    obtain ⟨j, hj, sb⟩ := support_parent b bp
    have ne : i ≠ j := by
      rintro rfl
      have ha := G.closes _ hv _ ap
      have hb := G.closes _ hv _ bp
      have forms (p : Nat) (hp : p ∈ G.V) (hs : support G p = {i}) :=
        unary_forms (G.W p) i (fun x y e =>
          support_value G hp x y (by simpa [hs] using e)) (G.unique p hp).1
      have neq := distinct_wires G ha hb ab
      rcases forms a ha sa with a_form | a_form <;> rcases forms b hb sb with b_form | b_form
      · exact neq (a_form.trans b_form.symm)
      · apply (G.unique v hv).1
        intro x y
        cases op <;> cases h₁ : x i <;> cases h₂ : y i <;>
          simp [formula, binary, a_form, b_form, h₁, h₂]
      · apply (G.unique v hv).1
        intro x y
        cases op <;> cases h₁ : x i <;> cases h₂ : y i <;>
          simp [formula, binary, a_form, b_form, h₁, h₂]
      · exact neq (a_form.trans b_form.symm)
    have pair : support G v = {i, j} := by
      rw [support_union G hg, pars]
      simp [sa, sb]
    let h : Bool → Bool → Bool := fun a b => G.W v (pairWord (fun _ => false) i j a b)
    have eval (x : Word) : G.W v x = h (x i) (x j) := by
      apply support_value G hv
      intro k hk
      simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [pairWord, ne.symm]
    apply avoid_pair m i (inputs ▸ hi) j (inputs ▸ hj) ne h
    intro x y agree eq
    rw [← out]
    apply cut_value G hv small x y
    · intro k _ hk
      apply agree
      · intro hki
        exact hk (by simp [pair, hki])
      · intro hkj
        exact hk (by simp [pair, hkj])
    · rw [eval x, eval y, eq]

private lemma nonbranching_cone (G : Graph) (m : Fix) (out : G.W G.root = restricted m)
    (inputs : G.I = keep m) {v : Nat} (hv : v ∈ G.V)
    (small : ∀ a, reach G.P a v → a ≠ v → (children G a).card ≤ 1) :
    ∃ i ∈ G.I, support G v = {i} := by
  classical
  apply unary_support G hv
  intro a ha r binary_gate
  let S := G.V.filter (fun u => reach G.P u v ∧ (G.P u).card = 2)
  have hn : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, r, binary_gate⟩⟩
  let q := S.min' hn
  obtain ⟨hq, reach_q, gate_q⟩ := Finset.mem_filter.mp (Finset.min'_mem S hn)
  exact pure_pair_impossible G m out inputs hq gate_q (fun z hz rz ne gate_z => by
    have lower := lt_of_le_of_ne (reach_le G rz hq) ne
    have upper := Finset.min'_le S z (Finset.mem_filter.mpr ⟨hz, rz.trans reach_q, gate_z⟩)
    omega) (fun z rz ne => by
      have hz := (lt_of_le_of_ne (reach_le G rz hq) ne).trans_le (reach_le G reach_q hv)
      exact small z (rz.trans reach_q) hz.ne)

private lemma pure_branch (G : Graph) (m : Fix) (out : G.W G.root = restricted m)
    (inputs : G.I = keep m) :
    ∃ q ∈ G.V, 2 ≤ (children G q).card ∧ ∃ i ∈ G.I, support G q = {i} := by
  classical
  let B := G.V.filter (fun v => 2 ≤ (children G v).card)
  have n : B.Nonempty := by
    by_contra no
    obtain ⟨i, hi, s⟩ := nonbranching_cone G m out inputs G.root_mem (fun a r _ => by
      by_contra! large
      exact no ⟨a, Finset.mem_filter.mpr ⟨reach_mem G r G.root_mem, by omega⟩⟩)
    have all : support G G.root = G.I := by
      ext j
      simp only [support, Finset.mem_filter]
      exact ⟨And.left, fun hj => ⟨hj, G.connected j.val ((G.inputs j).mpr hj)⟩⟩
    have h := keep_card m
    rw [← inputs, ← all, s, Finset.card_singleton] at h
    omega
  let q := B.min' n
  have ⟨hq, large⟩ := Finset.mem_filter.mp (Finset.min'_mem B n)
  refine ⟨q, hq, large, nonbranching_cone G m out inputs hq ?_⟩
  intro a r ne
  by_contra! bad
  have le := Finset.min'_le B a (Finset.mem_filter.mpr ⟨reach_mem G r hq, by omega⟩)
  have lt := lt_of_le_of_ne (reach_le G r hq) ne
  omega

private lemma branch_not_root (G : Graph) {q : Nat} (h : (children G q).Nonempty) :
    q ≠ G.root := by
  intro eq
  subst q
  obtain ⟨v, hv⟩ := h
  obtain ⟨hv, edge⟩ := (children_mem G).mp hv
  exact (G.earlier v hv G.root edge).not_ge (reach_le G (G.connected v hv) G.root_mem)

private noncomputable def counted (C : Circuit) (m : Fix) : Finset Nat := by
  classical
  exact (Finset.range (9 + C.gates.length)).filter (fun v => 9 ≤ v ∧ fresh (wire C m) v)

open scoped BigOperators in
private lemma size_of_branch (G : Graph) {q : Nat} (hq : q ∈ G.V)
    (branch : 2 ≤ (children G q).card) :
    G.I.card ≤ (G.V.filter (fun v => 9 ≤ v)).card := by
  classical
  let gates := G.V.filter (fun v => 9 ≤ v)
  have inputs : G.V.filter (fun v => v < 9) = G.I.image Fin.val := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hv, h⟩
      exact ⟨⟨v, h⟩, (G.inputs ⟨v, h⟩).mp hv, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(G.inputs i).mpr hi, i.isLt⟩
  have partition : G.V.card = G.I.card + gates.card := by
    have h := Finset.card_filter_add_card_filter_not (s := G.V) (fun v => v < 9)
    rw [inputs, Finset.card_image_of_injective _ Fin.val_injective,
      show (G.V.filter (fun v => ¬ v < 9)) = gates by simp [gates]] at h
    exact h.symm
  have edge_count : (∑ a ∈ G.V, (children G a).card) = ∑ v ∈ G.V, (G.P v).card := by
    calc
      _ = ∑ a ∈ G.V, ∑ v ∈ G.V, if a ∈ G.P v then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [children, Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ v ∈ G.V, ∑ a ∈ G.V, if a ∈ G.P v then 1 else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have sub : G.P v ⊆ G.V := fun a ha => G.closes v hv a ha
        have eq : G.V.filter (fun a => a ∈ G.P v) = G.P v := by
          ext a
          simp only [Finset.mem_filter, and_iff_right_iff_imp]
          exact @sub a
        rw [← Finset.sum_filter, eq]
        simp
  have upper : (∑ v ∈ G.V, (G.P v).card) ≤ 2 * gates.card := by
    have bound : ∀ v ∈ G.V, (G.P v).card ≤ if 9 ≤ v then 2 else 0 := by
      intro v hv
      by_cases h : 9 ≤ v
      · rcases G.gates v hv h with ⟨a, eq, _⟩ | ⟨a, b, op, ne, eq, _⟩
        · simp [h, eq]
        · simp [h, eq, ne]
      · have eq := G.input_empty (⟨v, by omega⟩ : Fin 9)
        change G.P v = ∅ at eq
        simp [h, eq]
    calc
      _ ≤ ∑ v ∈ G.V, if 9 ≤ v then 2 else 0 := Finset.sum_le_sum bound
      _ = 2 * gates.card := by rw [← Finset.sum_filter]; simp [gates, Nat.mul_comm]
  have not_root := branch_not_root G (Finset.card_pos.mp (by omega : 0 < (children G q).card))
  let weight (v : Nat) : Nat := (if v = G.root then 0 else 1) + (if v = q then 1 else 0)
  have lower : G.V.card ≤ ∑ v ∈ G.V, (children G v).card := by
    have total : (∑ v ∈ G.V, weight v) = G.V.card := by
      simp only [weight, Finset.sum_add_distrib]
      have eraseCount : (∑ v ∈ G.V, if v = G.root then 0 else 1) = (G.V.erase G.root).card := by
        have eq := Finset.sum_erase_add G.V (fun v => if v = G.root then 0 else 1) G.root_mem
        rw [← eq]
        rw [show (if G.root = G.root then (0 : Nat) else 1) = 0 by simp, Nat.add_zero]
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro v hv
        simp [(Finset.mem_erase.mp hv).1]
      rw [eraseCount]
      simpa [hq] using Finset.card_erase_add_one G.root_mem
    rw [← total]
    apply Finset.sum_le_sum
    intro v hv
    by_cases he : v = G.root
    · subst v
      simp [weight, Ne.symm not_root]
    · by_cases hqv : v = q
      · simpa [weight, hqv, not_root] using branch
      · have more := Finset.card_pos.mpr (child_exists G hv he)
        simpa [weight, he, hqv] using more
  have result : G.I.card ≤ gates.card := by omega
  exact result

private lemma witness_parents (C : Circuit) (m : Fix) (h : normal C) {v : Nat}
    (lo : 9 ≤ v) (hi : v < 9 + C.gates.length) (new : fresh (wire C m) v) :
    ∃ P, (∀ a ∈ P, a < v ∧ fresh (wire C m) a) ∧ gateLaw (wire C m) v P := by
  let W := wire C m
  rcases gate_shape C m h lo hi with ⟨a, ha, form⟩ | ⟨a, b, ab, hb, form⟩
  · have nc : ¬ constant (W a) := by
      intro hc
      exact new.1 (fun x y => by simp only [W, form, hc x y])
    have earlier : rep W a < v := (rep_bound W (i := a) (v := a) rfl).trans_lt ha
    refine ⟨{rep W a}, ?_, Or.inl ⟨rep W a, rfl, ?_⟩⟩
    · intro u hu
      have eq : u = rep W a := Finset.mem_singleton.mp hu
      exact eq.symm ▸ ⟨earlier, rep_fresh W nc⟩
    · change W v = fun x => !(W (rep W a) x)
      rw [rep_value W a]
      exact form
  · have form : ∃ op : Bool, W v = fun x => binary op (W a x) (W b x) := by
      rcases form with form | form
      · exact ⟨true, form⟩
      · exact ⟨false, form⟩
    obtain ⟨op, form⟩ := form
    have law : gateLaw W v {a, b} := Or.inr ⟨a, b, op, ab.ne, rfl, form⟩
    have earlier (c : Nat) (hc : c ∈ ({a, b} : Finset Nat)) : c < v := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> omega
    have nc (c : Nat) (hc : c ∈ ({a,b} : Finset Nat)) : ¬ constant (W c) := by
      intro hconst
      rcases constant_parent law hc hconst with const | ⟨r, hr, eq⟩
      · exact new.1 const
      · exact new.2 r (earlier r hr) eq.symm
    have different : rep W a ≠ rep W b := by
      intro he
      have wa : W a = W b := (rep_value W a).symm.trans (he ▸ rep_value W b)
      apply new.2 a (ab.trans hb)
      symm
      change W v = W a
      rw [form]
      funext x
      rw [← wa]
      cases op <;> simp [binary]
    refine ⟨{rep W a, rep W b}, ?_, Or.inr ⟨rep W a, rep W b, op, different, rfl, ?_⟩⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact ⟨(rep_bound W (i := a) (v := a) rfl).trans_lt (ab.trans hb),
          rep_fresh W (nc a (by simp))⟩
      · exact ⟨(rep_bound W (i := b) (v := b) rfl).trans_lt hb,
          rep_fresh W (nc b (by simp))⟩
    · change W v = fun x => binary op (W (rep W a) x) (W (rep W b) x)
      rw [rep_value W a, rep_value W b]
      exact form

private noncomputable def parents (C : Circuit) (m : Fix) (h : normal C) (v : Nat) :
    Finset Nat := by
  classical
  exact if valid : 9 ≤ v ∧ v < 9 + C.gates.length ∧ fresh (wire C m) v
    then (witness_parents C m h valid.1 valid.2.1 valid.2.2).choose else ∅

private lemma parent_props (C : Circuit) (m : Fix) (h : normal C) {v : Nat}
    (lo : 9 ≤ v) (hi : v < 9 + C.gates.length) (new : fresh (wire C m) v) :
    (∀ a ∈ parents C m h v, a < v ∧ fresh (wire C m) a) ∧
      gateLaw (wire C m) v (parents C m h v) := by
  classical
  rw [parents, dite_eq_left (show 9 ≤ v ∧ v < 9 + C.gates.length ∧ fresh (wire C m) v
    from ⟨lo, hi, new⟩)]
  exact (witness_parents C m h lo hi new).choose_spec

private def computes (C : Circuit) : Prop :=
  ∀ x : Word, C.eval (List.ofFn x) = matching x

private lemma wire_output (C : Circuit) (m : Fix) (h : computes C) :
    wire C m C.output = restricted m := by
  funext x
  exact h (freeze m x)

private lemma output_nonconstant (m : Fix) : ¬ constant (restricted m) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by have := keep_card m; omega : 0 < (keep m).card)
  obtain ⟨x, y, _, ne⟩ := essential m hi
  exact fun h => ne (h x y)

private noncomputable def buildGraph (C : Circuit) (m : Fix) (h : normal C)
    (inb : C.output < 9 + C.gates.length) (correct : computes C) : Graph := by
  classical
  let W := wire C m
  let P := parents C m h
  let r := rep W C.output
  let V := (Finset.range (9 + C.gates.length)).filter (fun v => fresh W v ∧ reach P v r)
  let I := (keep m).filter (fun i => i.val ∈ V)
  have spec (v : Nat) (hv : v ∈ V) : v < 9 + C.gates.length ∧ fresh W v ∧ reach P v r := by
    simpa only [V, Finset.mem_filter, Finset.mem_range] using hv
  have free (i : Fin 9) (hi : i.val ∈ V) : i ∈ keep m := by
    by_contra hf
    exact (spec i.val hi).2.1.1 (fun x y => by
      simp only [W, wire_input, freeze_fixed hf x y])
  refine {
    W := W
    P := P
    V := V
    I := I
    root := r
    root_mem := ?_
    closes := ?_
    earlier := ?_
    inputs := ?_
    input_value := ?_
    input_empty := ?_
    unique := fun v hv => (spec v hv).2.1
    gates := fun v hv lo => (parent_props C m h lo (spec v hv).1 (spec v hv).2.1).2
    connected := fun v hv => (spec v hv).2.2
  }
  · have nc : ¬ constant (W C.output) := by
      simpa only [W, wire_output C m correct] using output_nonconstant m
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((rep_bound W (i := C.output) (v := C.output) rfl).trans_lt inb),
      rep_fresh W nc, .refl⟩
  · intro v hv a ha
    obtain ⟨hi, new, path⟩ := spec v hv
    by_cases lo : 9 ≤ v
    · obtain ⟨le, fresh_a⟩ := (parent_props C m h lo hi new).1 a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (le.trans hi), fresh_a, path.head ha⟩
    · simp [P, parents, lo] at ha
  · intro v hv a ha
    obtain ⟨hi, new, path⟩ := spec v hv
    by_cases lo : 9 ≤ v
    · exact ((parent_props C m h lo hi new).1 a ha).1
    · simp [P, parents, lo] at ha
  · intro i
    exact ⟨fun hi => Finset.mem_filter.mpr ⟨free i hi, hi⟩, fun hi => (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    funext x
    rw [show W i.val x = freeze m x i from wire_input C m i x]
    exact freeze_free (Finset.mem_filter.mp hi).1 x
  · intro i
    simp [P, parents, Nat.not_le.mpr i.isLt]

private lemma graph_output (C : Circuit) (m : Fix) (h : normal C)
    (inb : C.output < 9 + C.gates.length) (correct : computes C) :
    let G := buildGraph C m h inb correct
    G.W G.root = restricted m := by
  change wire C m (rep (wire C m) C.output) = restricted m
  rw [rep_value (wire C m) C.output, wire_output C m correct]

private lemma graph_inputs (C : Circuit) (m : Fix) (h : normal C)
    (inb : C.output < 9 + C.gates.length) (correct : computes C) :
    (buildGraph C m h inb correct).I = keep m := by
  classical
  let G := buildGraph C m h inb correct
  apply Finset.Subset.antisymm (Finset.filter_subset _ _)
  intro i hi
  by_contra missing
  obtain ⟨x, y, agree, ne⟩ := essential m hi
  have eval := support_value G G.root_mem x y (fun j hj =>
    agree j (fun eq => missing (eq ▸ (Finset.mem_filter.mp hj).1)))
  have out : G.W G.root = restricted m := graph_output C m h inb correct
  rw [out] at eval
  exact ne eval

private lemma graph_counted (C : Circuit) (m : Fix) (h : normal C)
    (inb : C.output < 9 + C.gates.length) (correct : computes C) :
    ((buildGraph C m h inb correct).V.filter (fun v => 9 ≤ v)) ⊆ counted C m := by
  classical
  intro v hv
  obtain ⟨hh, lo⟩ := Finset.mem_filter.mp hv
  obtain ⟨bound, new, _⟩ := Finset.mem_filter.mp hh
  exact Finset.mem_filter.mpr ⟨bound, lo, new⟩

private lemma losses {A B : Finset Nat} (sub : A ⊆ B) {a b c : Nat}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (na : a ∉ A) (nb : b ∉ A) (nc : c ∉ A) : A.card + 3 ≤ B.card := by
  let extra : Finset Nat := {a, b, c}
  have disj : Disjoint A extra := Finset.disjoint_left.mpr fun x hx he => by
    simp only [extra, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact na hx
    · exact nb hx
    · exact nc hx
  have aux : extra.card = 3 := by simp [extra, ab, ac, bc, Finset.card_insert_of_notMem]
  have h : A ∪ extra ⊆ B := Finset.union_subset sub (by
    intro x hx
    simp only [extra, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  simpa only [Finset.card_union_of_disjoint disj, aux] using Finset.card_le_card h

private lemma input_order (C : Circuit) (h : normal C) (j : Fin C.gates.length)
    {a : Nat} (ha : a ∈ (C.gates.get j).inputs) : a < 9 + j.val := by
  rcases h j with ⟨_, b, hb, eq⟩ | ⟨_, b, c, bc, hc, eq⟩ <;>
    simp only [eq, List.mem_cons, List.not_mem_nil, or_false] at ha
  · exact ha ▸ hb
  · rcases ha with rfl | rfl <;> omega

private lemma raw_law (C : Circuit) (m : Fix) (h : normal C) (j : Fin C.gates.length) :
    gateLaw (wire C m) (9 + j.val) (C.gates.get j).inputs.toFinset := by
  have w := gate_wire C m j (fun _ ha => input_order C h j ha)
  rcases h j with ⟨op, a, _, eq⟩ | ⟨op, a, b, ab, _, eq⟩
  · rw [op, eq] at w
    rw [eq]
    exact Or.inl ⟨a, by simp, by simpa [GateOp.eval] using w⟩
  · rw [eq] at w ⊢
    rcases op with op | op
    · rw [op] at w
      exact Or.inr ⟨a, b, true, ab.ne, by simp, by simpa [GateOp.eval, binary] using w⟩
    · rw [op] at w
      exact Or.inr ⟨a, b, false, ab.ne, by simp, by simpa [GateOp.eval, binary] using w⟩

private lemma initial_losses (C : Circuit) (h : normal C) (correct : computes C)
    (bound : C.gates.length ≤ 12) (out : C.output + 1 = 9 + C.gates.length)
    (used : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (first : C.gates.head? = some ⟨GateOp.not, [0]⟩)
    (second : C.gates.tail.head? = some ⟨GateOp.and, [4, 9]⟩) :
    (counted C none).card ≤ 9 := by
  classical
  rw [List.head?_eq_getElem?, List.getElem?_tail] at second
  have two : 1 < C.gates.length := by
    by_contra! short
    rw [List.getElem?_eq_none short] at second
    contradiction
  let a : Fin C.gates.length := ⟨0, by omega⟩
  let b : Fin C.gates.length := ⟨1, two⟩
  have gate0 : C.gates.get a = ⟨GateOp.not, [0]⟩ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at first
    exact Option.some.inj first
  have gate1 : C.gates.get b = ⟨GateOp.and, [4, 9]⟩ := by
    rw [List.getElem?_eq_getElem two] at second
    exact Option.some.inj second
  have wire0 : wire C none 0 = fun _ => true := by
    funext x
    simpa [freeze] using wire_input C none (0 : Fin 9) x
  have wire9 : wire C none 9 = fun _ => false := by
    have eq := gate_wire C none a (fun _ e => input_order C h a e)
    rw [gate0] at eq
    simpa [a, GateOp.eval, wire0] using eq
  have wire10 : wire C none 10 = fun _ => false := by
    have eq := gate_wire C none b (fun _ e => input_order C h b e)
    rw [gate1] at eq
    simpa [b, GateOp.eval, wire9] using eq
  have longer : 2 < C.gates.length := by
    by_contra! short
    have eq : C.output = 10 := by omega
    have p := wire_output C none correct
    rw [eq, wire10] at p
    exact output_nonconstant none (by rw [← p]; exact fun _ _ => rfl)
  obtain ⟨k, later, reads⟩ := used b longer
  have forbid_k : ¬ fresh (wire C none) (9 + k.val) := by
    intro fresh_k
    have edge : 10 ∈ (C.gates.get k).inputs.toFinset := List.mem_toFinset.mpr reads
    rcases constant_parent (raw_law C none h k) edge (by rw [wire10]; exact fun _ _ => rfl) with
      const | ⟨i, hi, same⟩
    · exact fresh_k.1 const
    · exact fresh_k.2 i (input_order C h k (List.mem_toFinset.mp hi)) same.symm
  have sub : counted C none ⊆ Finset.Ico 9 (9 + C.gates.length) := by
    intro v hv
    obtain ⟨lt, ge, _⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_Ico.mpr ⟨ge, Finset.mem_range.mp lt⟩
  have excluded (v : Nat) (no : ¬ fresh (wire C none) v) : v ∉ counted C none :=
    fun hv => no (Finset.mem_filter.mp hv).2.2
  have bound₀ := losses sub (a := 9) (b := 10) (c := 9 + k.val)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (Finset.mem_Ico.mpr ⟨by omega, Nat.add_lt_add_left k.isLt 9⟩)
    (by decide) (by change 1 < k.val at later; omega) (by change 1 < k.val at later; omega)
    (excluded _ (fun hi => hi.1 (by rw [wire9]; exact fun _ _ => rfl)))
    (excluded _ (fun hi => hi.1 (by rw [wire10]; exact fun _ _ => rfl)))
    (excluded _ forbid_k)
  rw [Nat.card_Ico] at bound₀
  omega

private def changeInput (W : Wires) (p : Fin 9) (b : Bool) : Wires :=
  fun v x => W v (Function.update x p b)

private lemma law_after {W : Wires} {v : Nat} {P : Finset Nat} (h : gateLaw W v P)
    (p : Fin 9) (d : Bool) : gateLaw (changeInput W p d) v P := by
  rcases h with ⟨a, ps, f⟩ | ⟨a, b, op, ne, ps, f⟩
  · exact Or.inl ⟨a, ps, funext fun x => congrFun f (Function.update x p d)⟩
  · exact Or.inr ⟨a, b, op, ne, ps, funext fun x => congrFun f (Function.update x p d)⟩

private lemma child_is_gate (G : Graph) {a v : Nat} (child : v ∈ children G a) : 9 ≤ v := by
  have h := (children_mem G).mp child
  by_contra! lo
  have eq := G.input_empty (⟨v, lo⟩ : Fin 9)
  change G.P v = ∅ at eq
  exact Finset.notMem_empty _ (eq ▸ h.2)

private lemma freeze_branch (G : Graph) {q : Nat} (hq : q ∈ G.V)
    (large : 2 ≤ (children G q).card) {p : Fin 9} (source : support G q = {p})
    (out : G.W G.root = restricted none) :
    ∃ (b : Bool) (a c d : Nat), a ≠ c ∧ a ≠ d ∧ c ≠ d ∧
      (∀ v ∈ ({a, c, d} : Finset Nat), v ∈ G.V ∧ 9 ≤ v ∧ ¬ fresh (changeInput G.W p b) v) := by
  have depends (x y : Word) (h : x p = y p) : G.W q x = G.W q y :=
    support_value G hq x y (by simpa [source] using h)
  have target (s : Bool) : ∃ b, ∀ x, changeInput G.W p b q x = s := by
    rcases unary_forms (G.W q) p depends (G.unique q hq).1 with h | h
    · exact ⟨s, fun x => by simp [changeInput, h]⟩
    · exact ⟨!s, fun x => by simp [changeInput, h]⟩
  obtain ⟨a, ha, c, hc, ac⟩ := Finset.one_lt_card_iff_nontrivial.mp (by omega : 1 < (children G q).card)
  have haV := ((children_mem G).mp ha).1
  have hcV := ((children_mem G).mp hc).1
  have hqa := ((children_mem G).mp ha).2
  have hqc := ((children_mem G).mp hc).2
  have qa : q < a := G.earlier a haV q hqa
  have hforce : ∃ b, constant (changeInput G.W p b q) ∧ constant (changeInput G.W p b a) := by
    rcases G.gates a haV (child_is_gate G ha) with ⟨u, parents, form⟩ |
        ⟨u, v, op, ne, parents, form⟩
    · obtain ⟨b, f⟩ := target false
      have uq : q = u := by simpa [parents] using hqa
      subst u
      have eq : changeInput G.W p b a = fun x => !(changeInput G.W p b q x) :=
        funext fun x => congrFun form (Function.update x p b)
      exact ⟨b, fun x y => (f x).trans (f y).symm, fun x y => by simp only [eq, f x, f y]⟩
    · obtain ⟨b, f⟩ := target (!op)
      have fn : changeInput G.W p b a = fun x =>
          binary op (changeInput G.W p b u x) (changeInput G.W p b v x) :=
        funext fun x => congrFun form (Function.update x p b)
      refine ⟨b, fun x y => (f x).trans (f y).symm, ?_⟩
      intro x y
      have eq : q = u ∨ q = v := by simpa [parents] using hqa
      rcases eq with eq | eq
      · subst u
        cases op <;> simp [fn, f x, f y, binary]
      · subst v
        cases op <;> simp [fn, f x, f y, binary]
  obtain ⟨b, q_const, a_const⟩ := hforce
  let W := changeInput G.W p b
  have root_live : ¬ constant (W G.root) := by
    intro h
    apply output_nonconstant (some (p, b))
    intro x y
    simpa only [W, changeInput, out, restricted, freeze_twice] using h x y
  have lost {u v : Nat} (e : v ∈ children G u) (cst : constant (W u)) :
      v ∈ G.V ∧ 9 ≤ v ∧ ¬ fresh W v := by
    obtain ⟨hv, hu⟩ := (children_mem G).mp e
    have hg := child_is_gate G e
    refine ⟨hv, hg, ?_⟩
    intro new
    rcases constant_parent (law_after (G.gates v hv hg) p b) hu cst with cst | ⟨s, hs, eq⟩
    · exact new.1 cst
    · exact new.2 s (G.earlier v hv s hs) eq.symm
  obtain ⟨d, hd⟩ := child_exists G haV (fun e => root_live (e ▸ a_const))
  have ad := G.earlier d ((children_mem G).mp hd).1 a ((children_mem G).mp hd).2
  by_cases dc : d = c
  · subst d
    have parents : G.P c = {q, a} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hqc
        · exact ((children_mem G).mp hd).2
      · rcases G.gates c hcV (child_is_gate G hc) with ⟨u, eq, _⟩ | ⟨u, v, op, ne, eq, _⟩
        · simp [eq, qa.ne]
        · simp [eq, ne, qa.ne]
    have c_const : constant (W c) := by
      intro x y
      apply law_congr (law_after (G.gates c hcV (child_is_gate G hc)) p b)
      intro u hu
      simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact q_const x y
      · exact a_const x y
    obtain ⟨e, he⟩ := child_exists G hcV (fun e => root_live (e ▸ c_const))
    have ce := G.earlier e ((children_mem G).mp he).1 c ((children_mem G).mp he).2
    refine ⟨b, a, c, e, ac, (ad.trans ce).ne, ce.ne, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact lost ha q_const
    · exact lost hc q_const
    · exact lost he c_const
  · refine ⟨b, a, c, d, ac, ad.ne, Ne.symm dc, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact lost ha q_const
    · exact lost hc q_const
    · exact lost hd a_const

private lemma no_circuit (C : Circuit) (h : normal C) (correct : computes C)
    (inb : C.output < 9 + C.gates.length) (bound : (counted C none).card ≤ 9) : False := by
  classical
  let G := buildGraph C none h inb correct
  have out : G.W G.root = restricted none := graph_output C none h inb correct
  have inputs : G.I = keep none := graph_inputs C none h inb correct
  obtain ⟨q, hq, shared, p, hp, cone⟩ := pure_branch G none out inputs
  obtain ⟨b, a, c, d, ac, ad, cd, drop⟩ := freeze_branch G hq shared cone out
  have sub : counted C (some (p, b)) ⊆ counted C none := by
    intro v hv
    obtain ⟨hv, lo, new⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv, lo, frozen_fresh C p b new⟩
  have gone (v : Nat) (hv : v ∈ ({a, c, d} : Finset Nat)) :
      v ∈ counted C none ∧ v ∉ counted C (some (p, b)) := by
    obtain ⟨vs, lo, missing⟩ := drop v hv
    refine ⟨graph_counted C none h inb correct (Finset.mem_filter.mpr ⟨vs, lo⟩), ?_⟩
    intro mem
    have new := (Finset.mem_filter.mp mem).2.2
    have eq : changeInput G.W p b = wire C (some (p, b)) := by
      funext v x
      exact (wire_freeze C p b v x).symm
    exact missing (eq.symm ▸ new)
  have s₁ := gone a (by simp)
  have s₂ := gone c (by simp)
  have s₃ := gone d (by simp)
  have after := losses sub s₁.1 s₂.1 s₃.1 ac ad cd s₁.2 s₂.2 s₃.2
  let H := buildGraph C (some (p, b)) h inb correct
  have ho : H.W H.root = restricted (some (p, b)) := graph_output C (some (p, b)) h inb correct
  have hi : H.I = keep (some (p, b)) := graph_inputs C (some (p, b)) h inb correct
  obtain ⟨u, hu, branch, _, _, _⟩ := pure_branch H (some (p, b)) ho hi
  have lower := (size_of_branch H hu branch).trans
    (Finset.card_le_card (graph_counted C (some (p, b)) h inb correct))
  have size := keep_card (some (p, b))
  rw [hi] at lower
  omega

end PEqualNP.Outside.L_meta_27454

open PEqualNP.Outside.L_meta_27454 in
theorem PEqualNP.Outside.L_meta_27454 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩)) := by
  rintro ⟨C, _, size, eval, out, shape, _, used, first, second⟩
  change C.gates.length ≤ 12 at size
  change C.output + 1 = 9 + C.gates.length at out
  exact no_circuit C shape eval (by omega) (initial_losses C shape eval size out used first second)
