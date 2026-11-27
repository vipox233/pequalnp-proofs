import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_104_aux

abbrev Row := (Fin 3 → Bool) → Bool
abbrev Mat4N := Fin 4 → Fin 4 → ℕ
abbrev Mat4B := Fin 4 → Fin 4 → Bool

def b0 (s : Fin 4) : Bool := decide (2 ≤ s.val)
def b1 (s : Fin 4) : Bool := decide (s.val % 2 = 1)

def mkSt (a b : Bool) : Fin 4 :=
  ⟨2 * a.toNat + b.toNat, by cases a <;> cases b <;> decide⟩

lemma b0_mkSt (a b : Bool) : b0 (mkSt a b) = a := by
  cases a <;> cases b <;> rfl

lemma b1_mkSt (a b : Bool) : b1 (mkSt a b) = b := by
  cases a <;> cases b <;> rfl

lemma mkSt_b0_b1 (s : Fin 4) : mkSt (b0 s) (b1 s) = s := by
  fin_cases s <;> rfl

def pat3 (a b c : Bool) : Fin 3 → Bool
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

lemma eq_pat3 (f : Fin 3 → Bool) : f = pat3 (f 0) (f 1) (f 2) := by
  funext o
  fin_cases o <;> rfl

def xor4 (f : Fin 4 → Bool) : Bool :=
  xor (xor (f 0) (f 1)) (xor (f 2) (f 3))

lemma xor4_xor (f g : Fin 4 → Bool) :
    xor4 (fun i => xor (f i) (g i)) = xor (xor4 f) (xor4 g) := by
  simp only [xor4]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;>
    cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;> rfl

lemma testBit_zero_eq (n : ℕ) : n.testBit 0 = decide (n % 2 = 1) :=
  Nat.testBit_zero n

lemma testBit_zero_add (a b : ℕ) : (a + b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  simp only [testBit_zero_eq]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

lemma testBit_zero_mul (a b : ℕ) : (a * b).testBit 0 = (a.testBit 0 && b.testBit 0) := by
  simp only [testBit_zero_eq]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.mul_mod, ha, hb]

lemma testBit_zero_sum4 (f : Fin 4 → ℕ) :
    (∑ i : Fin 4, f i).testBit 0 = xor4 (fun i => (f i).testBit 0) := by
  rw [Fin.sum_univ_four]
  simp only [testBit_zero_add, xor4]
  cases (f 0).testBit 0 <;> cases (f 1).testBit 0 <;>
    cases (f 2).testBit 0 <;> cases (f 3).testBit 0 <;> rfl

def idN : Mat4N := fun i j => if i = j then 1 else 0
def mulN (A B : Mat4N) : Mat4N := fun i j => ∑ k : Fin 4, A i k * B k j
def trN (A : Mat4N) : ℕ := ∑ i : Fin 4, A i i

def idB : Mat4B := fun i j => decide (i = j)
def mulB (A B : Mat4B) : Mat4B := fun i j => xor4 (fun k => A i k && B k j)
def trB (A : Mat4B) : Bool := xor4 (fun i => A i i)

def mod2 (A : Mat4N) : Mat4B := fun i j => (A i j).testBit 0
def liftB (A : Mat4B) : Mat4N := fun i j => (A i j).toNat

lemma mod2_liftB (A : Mat4B) : mod2 (liftB A) = A := by
  funext i j
  simp only [mod2, liftB]
  cases A i j <;> rfl

lemma mod2_id : mod2 idN = idB := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma mod2_mul (A B : Mat4N) : mod2 (mulN A B) = mulB (mod2 A) (mod2 B) := by
  funext i j
  simp only [mod2, mulN, mulB, testBit_zero_sum4, testBit_zero_mul]

lemma trN_testBit (A : Mat4N) : (trN A).testBit 0 = trB (mod2 A) := by
  simp only [trN, trB, mod2, testBit_zero_sum4]

lemma mulN_assoc (A B C : Mat4N) : mulN (mulN A B) C = mulN A (mulN B C) := by
  funext i j
  simp only [mulN, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma mulB_assoc (A B C : Mat4B) : mulB (mulB A B) C = mulB A (mulB B C) := by
  have h := congrArg mod2 (mulN_assoc (liftB A) (liftB B) (liftB C))
  simpa only [mod2_mul, mod2_liftB] using h

lemma idB_mulB (A : Mat4B) : mulB idB A = A := by
  funext i j
  fin_cases i <;> simp [mulB, idB, xor4]

lemma mulB_idB (A : Mat4B) : mulB A idB = A := by
  funext i j
  fin_cases j <;> simp [mulB, idB, xor4]

def rowMatN (r : Row) : Mat4N :=
  fun s t => if b1 s = b0 t ∧ r (pat3 (b0 s) (b1 s) (b1 t)) = true then 1 else 0

def rowMatB (r : Row) : Mat4B :=
  fun s t => decide (b1 s = b0 t) && r (pat3 (b0 s) (b1 s) (b1 t))

lemma mod2_rowMatN (r : Row) : mod2 (rowMatN r) = rowMatB r := by
  funext s t
  simp only [mod2, rowMatN, rowMatB]
  by_cases h1 : b1 s = b0 t <;> cases h2 : r (pat3 (b0 s) (b1 s) (b1 t)) <;> simp [h1]

def prodMatN (rs : List Row) : Mat4N :=
  rs.foldl (fun acc r => mulN acc (rowMatN r)) idN

def prodMatB (rs : List Row) : Mat4B :=
  rs.foldl (fun acc r => mulB acc (rowMatB r)) idB

lemma mod2_foldl (rs : List Row) (acc : Mat4N) :
    mod2 (rs.foldl (fun a r => mulN a (rowMatN r)) acc) =
      rs.foldl (fun a r => mulB a (rowMatB r)) (mod2 acc) := by
  induction rs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rw [ih, mod2_mul, mod2_rowMatN]

lemma mod2_prodMatN (rs : List Row) : mod2 (prodMatN rs) = prodMatB rs := by
  unfold prodMatN prodMatB
  rw [mod2_foldl, mod2_id]

lemma foldl_mulB_shift (rs : List Row) (A B : Mat4B) :
    rs.foldl (fun acc r => mulB acc (rowMatB r)) (mulB A B) =
      mulB A (rs.foldl (fun acc r => mulB acc (rowMatB r)) B) := by
  induction rs generalizing B with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldl_cons, mulB_assoc]
    exact ih (mulB B (rowMatB r))

lemma prodMatB_append (l1 l2 : List Row) :
    prodMatB (l1 ++ l2) = mulB (prodMatB l1) (prodMatB l2) := by
  unfold prodMatB
  rw [List.foldl_append]
  have h := foldl_mulB_shift l2 (l1.foldl (fun acc r => mulB acc (rowMatB r)) idB) idB
  simpa only [mulB_idB] using h

def rotRow : Row := fun pat => pat 0 == pat 2

lemma mulB_rotRow_rotRow : mulB (rowMatB rotRow) (rowMatB rotRow) = idB := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma prodMatB_rotRow_pair : prodMatB [rotRow, rotRow] = idB := by
  simp only [prodMatB, List.foldl_cons, List.foldl_nil, idB_mulB, mulB_rotRow_rotRow]

lemma prodMatB_replicate_rotRow (k : ℕ) : prodMatB (List.replicate (2 * k) rotRow) = idB := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hrep : List.replicate (2 * (k + 1)) rotRow = List.replicate (2 * k) rotRow ++ [rotRow, rotRow] := by
      have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h1, List.replicate_add]
      rfl
    rw [hrep, prodMatB_append, ih, prodMatB_rotRow_pair, idB_mulB]

def matPerm (σ : Equiv.Perm (Fin 5)) : Mat4B :=
  fun i j => xor (decide (σ i.castSucc = j.castSucc)) (decide (σ 4 = j.castSucc))

lemma matPerm_one : matPerm 1 = idB := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide

lemma xor4_single_matPerm (τ : Equiv.Perm (Fin 5)) (u : Fin 5) (j : Fin 4) :
    xor4 (fun k => decide (u = k.castSucc) && matPerm τ k j) =
      xor (decide (τ u = j.castSucc)) (decide (τ 4 = j.castSucc)) := by
  fin_cases u
  · simp only [xor4, matPerm]
    change xor (xor (true && xor (decide (τ 0 = j.castSucc)) (decide (τ 4 = j.castSucc)))
      (false && _)) (xor (false && _) (false && _)) = _
    simp
  · simp only [xor4, matPerm]
    change xor (xor (false && _) (true && xor (decide (τ 1 = j.castSucc)) (decide (τ 4 = j.castSucc))))
      (xor (false && _) (false && _)) = _
    simp
  · simp only [xor4, matPerm]
    change xor (xor (false && _) (false && _))
      (xor (true && xor (decide (τ 2 = j.castSucc)) (decide (τ 4 = j.castSucc))) (false && _)) = _
    simp
  · simp only [xor4, matPerm]
    change xor (xor (false && _) (false && _))
      (xor (false && _) (true && xor (decide (τ 3 = j.castSucc)) (decide (τ 4 = j.castSucc)))) = _
    simp
  · simp only [xor4, matPerm]
    change xor (xor (false && _) (false && _)) (xor (false && _) (false && _)) =
      xor (decide (τ 4 = j.castSucc)) (decide (τ 4 = j.castSucc))
    cases decide (τ 4 = j.castSucc) <;> rfl

lemma matPerm_mul (σ τ : Equiv.Perm (Fin 5)) :
    mulB (matPerm σ) (matPerm τ) = matPerm (τ * σ) := by
  funext i j
  have hstep : (fun k : Fin 4 => matPerm σ i k && matPerm τ k j) =
      (fun k : Fin 4 => xor (decide (σ i.castSucc = k.castSucc) && matPerm τ k j)
        (decide (σ 4 = k.castSucc) && matPerm τ k j)) := by
    funext k
    change (xor (decide (σ i.castSucc = k.castSucc)) (decide (σ 4 = k.castSucc)) && matPerm τ k j) = _
    cases decide (σ i.castSucc = k.castSucc) <;> cases decide (σ 4 = k.castSucc) <;>
      cases matPerm τ k j <;> rfl
  simp only [mulB, hstep, xor4_xor, xor4_single_matPerm]
  change xor (xor (decide (τ (σ i.castSucc) = j.castSucc)) (decide (τ 4 = j.castSucc)))
      (xor (decide (τ (σ 4) = j.castSucc)) (decide (τ 4 = j.castSucc))) =
    xor (decide (τ (σ i.castSucc) = j.castSucc)) (decide (τ (σ 4) = j.castSucc))
  cases decide (τ (σ i.castSucc) = j.castSucc) <;>
    cases decide (τ (σ 4) = j.castSucc) <;>
    cases decide (τ 4 = j.castSucc) <;> rfl

lemma trB_matPerm (σ : Equiv.Perm (Fin 5)) :
    trB (matPerm σ) = (Finset.univ.filter (fun p : Fin 5 => σ p ≠ p)).card.testBit 0 := by
  have hcard : (Finset.univ.filter (fun p : Fin 5 => σ p ≠ p)).card =
      ∑ p : Fin 5, if σ p ≠ p then 1 else 0 := by
    rw [Finset.card_filter]
  rw [hcard, Fin.sum_univ_castSucc]
  have hsum4 : (∑ i : Fin 4, if σ i.castSucc ≠ i.castSucc then 1 else 0) +
      (∑ i : Fin 4, if σ i.castSucc = i.castSucc then 1 else 0) = 4 := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ i : Fin 4, (if σ i.castSucc ≠ i.castSucc then 1 else 0) +
        (if σ i.castSucc = i.castSucc then 1 else 0) = 1 := by
      intro i
      by_cases h : σ i.castSucc = i.castSucc <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    decide
  have hmod4 : (∑ i : Fin 4, if σ i.castSucc ≠ i.castSucc then 1 else 0) % 2 =
      (∑ i : Fin 4, if σ i.castSucc = i.castSucc then 1 else 0) % 2 := by
    omega
  have hpar4 : (∑ i : Fin 4, if σ i.castSucc ≠ i.castSucc then 1 else 0).testBit 0 =
      (∑ i : Fin 4, if σ i.castSucc = i.castSucc then 1 else 0).testBit 0 := by
    rw [testBit_zero_eq, testBit_zero_eq, hmod4]
  rw [testBit_zero_add, hpar4, testBit_zero_sum4]
  have hlast : (if σ (Fin.last 4) ≠ Fin.last 4 then (1 : ℕ) else 0).testBit 0 =
      xor4 (fun i : Fin 4 => decide (σ 4 = i.castSucc)) := by
    have h4eq : Fin.last 4 = (4 : Fin 5) := rfl
    rw [h4eq]
    generalize hu : σ 4 = u
    fin_cases u <;> decide
  rw [hlast]
  have hfix : (fun i : Fin 4 => (if σ i.castSucc = i.castSucc then (1 : ℕ) else 0).testBit 0) =
      (fun i : Fin 4 => decide (σ i.castSucc = i.castSucc)) := by
    funext i
    by_cases h : σ i.castSucc = i.castSucc <;> simp [h]
  rw [hfix]
  simp only [trB, matPerm, xor4_xor]

def patOfMask (mask : ℕ) : Row :=
  fun pat => mask.testBit ((pat 0).toNat + 2 * (pat 1).toNat + 4 * (pat 2).toNat)

def swapMasksOrdered (a b : ℕ) : Fin 4 → ℕ
  | k =>
    if a = b then 165
    else if a = 0 ∧ b = 1 then
      match k with | ⟨0, _⟩ => 165 | ⟨1, _⟩ => 150 | ⟨2, _⟩ => 165 | ⟨3, _⟩ => 165
    else if a = 0 ∧ b = 2 then
      match k with | ⟨0, _⟩ => 150 | ⟨1, _⟩ => 165 | ⟨2, _⟩ => 165 | ⟨3, _⟩ => 165
    else if a = 0 ∧ b = 3 then
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 105 | ⟨2, _⟩ => 150 | ⟨3, _⟩ => 150
    else if a = 0 ∧ b = 4 then
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 121 | ⟨2, _⟩ => 94 | ⟨3, _⟩ => 215
    else if a = 1 ∧ b = 2 then
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 105 | ⟨2, _⟩ => 105 | ⟨3, _⟩ => 150
    else if a = 1 ∧ b = 3 then
      match k with | ⟨0, _⟩ => 105 | ⟨1, _⟩ => 165 | ⟨2, _⟩ => 165 | ⟨3, _⟩ => 165
    else if a = 1 ∧ b = 4 then
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 91 | ⟨2, _⟩ => 91 | ⟨3, _⟩ => 250
    else if a = 2 ∧ b = 3 then
      match k with | ⟨0, _⟩ => 165 | ⟨1, _⟩ => 105 | ⟨2, _⟩ => 165 | ⟨3, _⟩ => 165
    else if a = 2 ∧ b = 4 then
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 109 | ⟨2, _⟩ => 122 | ⟨3, _⟩ => 190
    else
      match k with | ⟨0, _⟩ => 90 | ⟨1, _⟩ => 94 | ⟨2, _⟩ => 122 | ⟨3, _⟩ => 250

def swapRow (i j : Fin 5) (k : Fin 4) : Row :=
  patOfMask (swapMasksOrdered (min i.val j.val) (max i.val j.val) k)

lemma prodMatB_swapRows (i j : Fin 5) :
    prodMatB [swapRow i j 0, swapRow i j 1, swapRow i j 2, swapRow i j 3] =
      matPerm (Equiv.swap i j) := by
  have hall : ∀ (i j : Fin 5) (r c : Fin 4),
      prodMatB [swapRow i j 0, swapRow i j 1, swapRow i j 2, swapRow i j 3] r c =
        matPerm (Equiv.swap i j) r c := by
    decide
  funext r c
  exact hall i j r c

lemma perm_decomp_swaps (σ : Equiv.Perm (Fin 5)) :
    let a0 := σ 0
    let σ1 := Equiv.swap 0 a0 * σ
    let a1 := σ1 1
    let σ2 := Equiv.swap 1 a1 * σ1
    let a2 := σ2 2
    let σ3 := Equiv.swap 2 a2 * σ2
    let a3 := σ3 3
    σ = Equiv.swap 0 a0 * (Equiv.swap 1 a1 * (Equiv.swap 2 a2 * Equiv.swap 3 a3)) := by
  dsimp only
  set a0 := σ 0
  set σ1 := Equiv.swap 0 a0 * σ
  set a1 := σ1 1
  set σ2 := Equiv.swap 1 a1 * σ1
  set a2 := σ2 2
  set σ3 := Equiv.swap 2 a2 * σ2
  set a3 := σ3 3
  set σ4 := Equiv.swap 3 a3 * σ3
  have h10 : σ1 0 = 0 := by
    simp [σ1, a0]
  have ha1 : a1 ≠ 0 := by
    intro h
    have := σ1.injective (h.trans h10.symm)
    exact absurd this (by decide)
  have h20 : σ2 0 = 0 := by
    simp [σ2, h10, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 1) ha1.symm]
  have h21 : σ2 1 = 1 := by
    simp [σ2, a1]
  have ha20 : a2 ≠ 0 := by
    intro h
    have := σ2.injective (h.trans h20.symm)
    exact absurd this (by decide)
  have ha21 : a2 ≠ 1 := by
    intro h
    have := σ2.injective (h.trans h21.symm)
    exact absurd this (by decide)
  have h30 : σ3 0 = 0 := by
    simp [σ3, h20, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 2) ha20.symm]
  have h31 : σ3 1 = 1 := by
    simp [σ3, h21, Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 5) ≠ 2) ha21.symm]
  have h32 : σ3 2 = 2 := by
    simp [σ3, a2]
  have ha30 : a3 ≠ 0 := by
    intro h
    have := σ3.injective (h.trans h30.symm)
    exact absurd this (by decide)
  have ha31 : a3 ≠ 1 := by
    intro h
    have := σ3.injective (h.trans h31.symm)
    exact absurd this (by decide)
  have ha32 : a3 ≠ 2 := by
    intro h
    have := σ3.injective (h.trans h32.symm)
    exact absurd this (by decide)
  have h40 : σ4 0 = 0 := by
    simp [σ4, h30, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 3) ha30.symm]
  have h41 : σ4 1 = 1 := by
    simp [σ4, h31, Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 5) ≠ 3) ha31.symm]
  have h42 : σ4 2 = 2 := by
    simp [σ4, h32, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 5) ≠ 3) ha32.symm]
  have h43 : σ4 3 = 3 := by
    simp [σ4, a3]
  have h44 : σ4 4 = 4 := by
    have h0 : σ4 4 ≠ 0 := fun h => absurd (σ4.injective (h.trans h40.symm)) (by decide)
    have h1 : σ4 4 ≠ 1 := fun h => absurd (σ4.injective (h.trans h41.symm)) (by decide)
    have h2 : σ4 4 ≠ 2 := fun h => absurd (σ4.injective (h.trans h42.symm)) (by decide)
    have h3 : σ4 4 ≠ 3 := fun h => absurd (σ4.injective (h.trans h43.symm)) (by decide)
    generalize hu : σ4 4 = u
    rw [hu] at h0 h1 h2 h3
    fin_cases u <;> simp_all
  have hσ4 : σ4 = 1 := by
    ext x
    fin_cases x <;> simp [h40, h41, h42, h43, h44]
  have h3eq : σ3 = Equiv.swap 3 a3 := by
    have h := congrArg (fun p => Equiv.swap 3 a3 * p) hσ4
    simpa [σ4, mul_assoc] using h
  have h2eq : σ2 = Equiv.swap 2 a2 * Equiv.swap 3 a3 := by
    have h := congrArg (fun p => Equiv.swap 2 a2 * p) h3eq
    simpa [σ3, mul_assoc] using h
  have h1eq : σ1 = Equiv.swap 1 a1 * (Equiv.swap 2 a2 * Equiv.swap 3 a3) := by
    have h := congrArg (fun p => Equiv.swap 1 a1 * p) h2eq
    simpa [σ2, mul_assoc] using h
  have h0eq := congrArg (fun p => Equiv.swap 0 a0 * p) h1eq
  simpa [σ1, mul_assoc] using h0eq

def permBlock (σ : Equiv.Perm (Fin 5)) (t : Fin 1154) : Row :=
  let a0 := σ 0
  let σ1 := Equiv.swap 0 a0 * σ
  let a1 := σ1 1
  let σ2 := Equiv.swap 1 a1 * σ1
  let a2 := σ2 2
  let σ3 := Equiv.swap 2 a2 * σ2
  let a3 := σ3 3
  if h0 : t.val < 4 then swapRow 3 a3 ⟨t.val, h0⟩
  else if h1 : t.val < 8 then swapRow 2 a2 ⟨t.val - 4, by omega⟩
  else if h2 : t.val < 12 then swapRow 1 a1 ⟨t.val - 8, by omega⟩
  else if h3 : t.val < 16 then swapRow 0 a0 ⟨t.val - 12, by omega⟩
  else rotRow

lemma prodMatB_permBlock (σ : Equiv.Perm (Fin 5)) :
    prodMatB ((List.finRange 1154).map (permBlock σ)) = matPerm σ := by
  let a0 := σ 0
  let σ1 := Equiv.swap 0 a0 * σ
  let a1 := σ1 1
  let σ2 := Equiv.swap 1 a1 * σ1
  let a2 := σ2 2
  let σ3 := Equiv.swap 2 a2 * σ2
  let a3 := σ3 3
  let s3 : List Row := [swapRow 3 a3 0, swapRow 3 a3 1, swapRow 3 a3 2, swapRow 3 a3 3]
  let s2 : List Row := [swapRow 2 a2 0, swapRow 2 a2 1, swapRow 2 a2 2, swapRow 2 a2 3]
  let s1 : List Row := [swapRow 1 a1 0, swapRow 1 a1 1, swapRow 1 a1 2, swapRow 1 a1 3]
  let s0 : List Row := [swapRow 0 a0 0, swapRow 0 a0 1, swapRow 0 a0 2, swapRow 0 a0 3]
  have hs3 : s3.length = 4 := rfl
  have hs2 : s2.length = 4 := rfl
  have hs1 : s1.length = 4 := rfl
  have hs0 : s0.length = 4 := rfl
  have hlist : (List.finRange 1154).map (permBlock σ) =
      s3 ++ s2 ++ s1 ++ s0 ++ List.replicate (2 * 569) rotRow := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, List.length_append, List.length_replicate,
        hs3, hs2, hs1, hs0]
    · intro i hi1 hi2
      have hi : i < 1154 := by simpa only [List.length_map, List.length_finRange] using hi1
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      by_cases h0 : i < 4
      · have h0' : i < s3.length := by omega
        have h1' : i < (s3 ++ s2).length := by simp only [List.length_append, hs3, hs2]; omega
        have h2' : i < (s3 ++ s2 ++ s1).length := by simp only [List.length_append, hs3, hs2, hs1]; omega
        have h3' : i < (s3 ++ s2 ++ s1 ++ s0).length := by simp only [List.length_append, hs3, hs2, hs1, hs0]; omega
        rw [List.getElem_append_left h3', List.getElem_append_left h2',
          List.getElem_append_left h1', List.getElem_append_left h0']
        simp only [permBlock, dite_eq_left h0]
        interval_cases i <;> rfl
      · by_cases h1 : i < 8
        · have h1' : i < (s3 ++ s2).length := by simp only [List.length_append, hs3, hs2]; omega
          have h2' : i < (s3 ++ s2 ++ s1).length := by simp only [List.length_append, hs3, hs2, hs1]; omega
          have h3' : i < (s3 ++ s2 ++ s1 ++ s0).length := by simp only [List.length_append, hs3, hs2, hs1, hs0]; omega
          have hge : s3.length ≤ i := by omega
          rw [List.getElem_append_left h3', List.getElem_append_left h2',
            List.getElem_append_left h1', List.getElem_append_right hge]
          simp only [permBlock, dite_eq_right h0, dite_eq_left h1]
          interval_cases i <;> rfl
        · by_cases h2 : i < 12
          · have h2' : i < (s3 ++ s2 ++ s1).length := by simp only [List.length_append, hs3, hs2, hs1]; omega
            have h3' : i < (s3 ++ s2 ++ s1 ++ s0).length := by simp only [List.length_append, hs3, hs2, hs1, hs0]; omega
            have hge : (s3 ++ s2).length ≤ i := by simp only [List.length_append, hs3, hs2]; omega
            rw [List.getElem_append_left h3', List.getElem_append_left h2',
              List.getElem_append_right hge]
            simp only [permBlock, dite_eq_right h0, dite_eq_right h1, dite_eq_left h2]
            interval_cases i <;> rfl
          · by_cases h3 : i < 16
            · have h3' : i < (s3 ++ s2 ++ s1 ++ s0).length := by simp only [List.length_append, hs3, hs2, hs1, hs0]; omega
              have hge : (s3 ++ s2 ++ s1).length ≤ i := by simp only [List.length_append, hs3, hs2, hs1]; omega
              rw [List.getElem_append_left h3', List.getElem_append_right hge]
              simp only [permBlock, dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
              interval_cases i <;> rfl
            · have hge : (s3 ++ s2 ++ s1 ++ s0).length ≤ i := by simp only [List.length_append, hs3, hs2, hs1, hs0]; omega
              rw [List.getElem_append_right hge, List.getElem_replicate]
              simp only [permBlock, dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
  rw [hlist, prodMatB_append, prodMatB_append, prodMatB_append, prodMatB_append,
    prodMatB_replicate_rotRow, mulB_idB]
  rw [prodMatB_swapRows 3 a3, prodMatB_swapRows 2 a2,
    prodMatB_swapRows 1 a1, prodMatB_swapRows 0 a0]
  rw [matPerm_mul, matPerm_mul, matPerm_mul]
  have hdec := perm_decomp_swaps σ
  dsimp only at hdec
  exact congrArg matPerm hdec.symm

def openPaths {n : ℕ} (row : Fin n → Row) (k : ℕ) (hk : k ≤ n) (s t : Fin 4) :
    Finset (Fin (k + 2) → Bool) :=
  Finset.univ.filter fun f =>
    mkSt (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) = s ∧
    mkSt (f ⟨k, by omega⟩) (f ⟨k + 1, by omega⟩) = t ∧
    ∀ i : Fin k, row ⟨i.val, by omega⟩ (fun o : Fin 3 => f ⟨i.val + o.val, by omega⟩) = true

lemma openPaths_card {n : ℕ} (row : Fin n → Row) :
    ∀ (k : ℕ) (hk : k ≤ n) (s t : Fin 4),
      (openPaths row k hk s t).card =
        prodMatN ((List.finRange k).map (fun i => row ⟨i.val, by omega⟩)) s t := by
  intro k
  induction k with
  | zero =>
    intro hk s t
    simp only [openPaths, List.finRange_zero, List.map_nil, prodMatN, List.foldl_nil, idN]
    by_cases hst : s = t
    · subst hst
      simp only [ite_true]
      refine Finset.card_eq_one.mpr ⟨fun j => if j.val = 0 then b0 s else b1 s, ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h0, _, _⟩
        funext j
        have hb0 : f ⟨0, by omega⟩ = b0 s := by rw [← h0, b0_mkSt]
        have hb1 : f ⟨1, by omega⟩ = b1 s := by rw [← h0, b1_mkSt]
        fin_cases j
        · exact hb0
        · exact hb1
      · intro hf
        subst hf
        refine ⟨by simp [mkSt_b0_b1], by simp [mkSt_b0_b1], fun i => Fin.elim0 i⟩
    · simp only [hst, ite_false]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _
      rintro ⟨h0, h1, _⟩
      exact hst (h0.symm.trans h1)
  | succ k ih =>
    intro hk s t
    have hk' : k ≤ n := by omega
    have hfr : (List.finRange (k + 1)).map (fun i => row ⟨i.val, by omega⟩) =
        ((List.finRange k).map (fun i => row ⟨i.val, by omega⟩)) ++ [row ⟨k, by omega⟩] := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        have hi : i < k + 1 := by simpa only [List.length_map, List.length_finRange] using hi1
        by_cases hik : i < k
        · have hlen : i < ((List.finRange k).map (fun i : Fin k => row ⟨i.val, by omega⟩)).length := by
            simp; omega
          simp only [List.getElem_append_left hlen, List.getElem_map, List.getElem_finRange]
          rfl
        · have hik' : i = k := by omega
          have hge : ((List.finRange k).map (fun j : Fin k => row ⟨j.val, by omega⟩)).length ≤ i := by
            simp; omega
          simp only [List.getElem_append_right hge, List.getElem_map, List.getElem_finRange,
            Fin.cast_mk, List.length_map, List.length_finRange]
          have hsub : i - k = 0 := by omega
          simp only [hsub, List.getElem_cons_zero]
          congr 1
          exact Fin.ext hik'
    rw [hfr]
    unfold prodMatN
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (openPaths row (k + 1) hk s t).card =
      ∑ m : Fin 4, prodMatN ((List.finRange k).map (fun i => row ⟨i.val, by omega⟩)) s m *
        rowMatN (row ⟨k, by omega⟩) m t
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun (f : Fin (k + 3) → Bool) => mkSt (f ⟨k, by omega⟩) (f ⟨k + 1, by omega⟩))
      (t := (Finset.univ : Finset (Fin 4))) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [← ih hk' s m]
    simp only [rowMatN]
    by_cases hcond : b1 m = b0 t ∧ row ⟨k, by omega⟩ (pat3 (b0 m) (b1 m) (b1 t)) = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd hcond h), mul_one]
      refine Finset.card_bij
        (fun f _ => fun i : Fin (k + 2) => f ⟨i.val, by omega⟩)
        ?_ ?_ ?_
      · intro f hf
        simp only [Finset.mem_filter, openPaths, Finset.mem_univ, true_and] at hf ⊢
        rcases hf with ⟨⟨h0, h1, hall⟩, hm⟩
        exact ⟨h0, hm, fun i => hall ⟨i.val, by omega⟩⟩
      · intro f1 hf1 f2 hf2 heq
        simp only [Finset.mem_filter, openPaths, Finset.mem_univ, true_and] at hf1 hf2
        funext j
        by_cases hj : j.val < k + 2
        · exact congrFun heq ⟨j.val, hj⟩
        · have hjlt := j.isLt
          have hjval : j.val = k + 2 := by omega
          have hj' : j = ⟨k + 2, by omega⟩ := Fin.ext hjval
          rw [hj']
          have h1 : f1 ⟨k + 2, by omega⟩ = b1 t := by rw [← hf1.1.2.1, b1_mkSt]
          have h2 : f2 ⟨k + 2, by omega⟩ = b1 t := by rw [← hf2.1.2.1, b1_mkSt]
          exact h1.trans h2.symm
      · intro g hg
        simp only [Finset.mem_filter, openPaths, Finset.mem_univ, true_and] at hg
        rcases hg with ⟨h0, hm, hall⟩
        refine ⟨fun j => if hj : j.val < k + 2 then g ⟨j.val, hj⟩ else b1 t, ?_, ?_⟩
        · simp only [Finset.mem_filter, openPaths, Finset.mem_univ, true_and]
          have hgk : g ⟨k, by omega⟩ = b0 m := by rw [← hm, b0_mkSt]
          have hgk1 : g ⟨k + 1, by omega⟩ = b1 m := by rw [← hm, b1_mkSt]
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · simpa [show (0 : ℕ) < k + 2 by omega, show (1 : ℕ) < k + 2 by omega] using h0
          · rw [dite_eq_left (by omega : k + 1 < k + 2),
              dite_eq_right (by omega : ¬(k + 1 + 1 < k + 2)),
              hgk1, hcond.1, mkSt_b0_b1]
          · intro i
            by_cases hik : i.val < k
            · have hi := hall ⟨i.val, hik⟩
              have hpat : (fun o : Fin 3 =>
                  if hj : i.val + o.val < k + 2 then g ⟨i.val + o.val, hj⟩ else b1 t) =
                  (fun o : Fin 3 => g ⟨i.val + o.val, by omega⟩) := by
                funext o
                rw [dite_eq_left (by omega)]
              rw [hpat]
              exact hi
            · have hik' : i.val = k := by omega
              have hpat : (fun o : Fin 3 =>
                  if hj : i.val + o.val < k + 2 then g ⟨i.val + o.val, hj⟩ else b1 t) =
                  pat3 (b0 m) (b1 m) (b1 t) := by
                funext o
                fin_cases o
                · simp [hik', pat3, hgk]
                · simp [hik', pat3, hgk1]
                · simp [hik', pat3]
              rw [hpat]
              have hrow : row ⟨i.val, by omega⟩ = row ⟨k, by omega⟩ := by
                congr 1; exact Fin.ext hik'
              rw [hrow]
              exact hcond.2
          · simpa [show k < k + 2 by omega, show k + 1 < k + 2 by omega] using hm
        · funext i
          simp [i.isLt]
    · simp only [hcond, ite_false, mul_zero]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f hf hm
      simp only [openPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rcases hf with ⟨_, ht, hall⟩
      have hfk : f ⟨k, by omega⟩ = b0 m := by rw [← hm, b0_mkSt]
      have hfk1 : f ⟨k + 1, by omega⟩ = b1 m := by rw [← hm, b1_mkSt]
      have hfk1' : f ⟨k + 1, by omega⟩ = b0 t := by rw [← ht, b0_mkSt]
      have hfk2 : f ⟨k + 2, by omega⟩ = b1 t := by rw [← ht, b1_mkSt]
      have hpat : (fun o : Fin 3 => f ⟨k + o.val, by omega⟩) = pat3 (b0 m) (b1 m) (b1 t) := by
        funext o
        fin_cases o
        · exact hfk
        · exact hfk1
        · exact hfk2
      have hk_ok := hall ⟨k, by omega⟩
      rw [hpat] at hk_ok
      exact hcond ⟨hfk1.symm.trans hfk1', hk_ok⟩

lemma card_cyclic_eq_trN {n : ℕ} (hn : 2 ≤ n) (row : Fin n → Row) :
    let loc := fun k : ℕ => (⟨k % n, Nat.mod_lt _ (by omega)⟩ : Fin n)
    (Finset.univ.filter (fun word : Fin n → Bool =>
      ∀ i : Fin n, row i (fun o : Fin 3 => word (loc (i.val + o.val))) = true)).card =
      trN (prodMatN ((List.finRange n).map row)) := by
  intro loc
  unfold trN
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun (word : Fin n → Bool) => mkSt (word ⟨0, by omega⟩) (word ⟨1, by omega⟩))
    (t := (Finset.univ : Finset (Fin 4))) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro s _
  have hopen := openPaths_card row n (le_refl n) s s
  have hmap : (List.finRange n).map (fun i : Fin n => row ⟨i.val, by omega⟩) =
      (List.finRange n).map row := by
    refine List.map_congr_left ?_
    intro i _
    rfl
  rw [hmap] at hopen
  rw [← hopen]
  refine Finset.card_bij
    (fun word _ => fun j : Fin (n + 2) => word (loc j.val))
    ?_ ?_ ?_
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, openPaths] at hword ⊢
    rcases hword with ⟨hacc, hs⟩
    have h0 : loc 0 = ⟨0, by omega⟩ := Fin.ext (Nat.zero_mod n)
    have h1 : loc 1 = ⟨1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hn0 : loc n = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self n)
    have hn1 : loc (n + 1) = ⟨1, by omega⟩ := Fin.ext (by
      change (n + 1) % n = 1
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)])
    refine ⟨?_, ?_, ?_⟩
    · simpa [h0, h1] using hs
    · simpa [hn0, hn1] using hs
    · intro i
      exact hacc i
  · intro w1 _ w2 _ heq
    funext i
    have hmod : loc i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have h := congrFun heq ⟨i.val, by omega⟩
    simpa [hmod] using h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, openPaths] at hf
    rcases hf with ⟨hs0, hsn, hall⟩
    have hf0 : f ⟨0, by omega⟩ = f ⟨n, by omega⟩ := by
      have a : f ⟨0, by omega⟩ = b0 s := by rw [← hs0, b0_mkSt]
      have b : f ⟨n, by omega⟩ = b0 s := by rw [← hsn, b0_mkSt]
      exact a.trans b.symm
    have hf1 : f ⟨1, by omega⟩ = f ⟨n + 1, by omega⟩ := by
      have a : f ⟨1, by omega⟩ = b1 s := by rw [← hs0, b1_mkSt]
      have b : f ⟨n + 1, by omega⟩ = b1 s := by rw [← hsn, b1_mkSt]
      exact a.trans b.symm
    have hloc_eq : ∀ k : ℕ, (hk : k < n + 2) → f ⟨(loc k).val, by omega⟩ = f ⟨k, hk⟩ := by
      intro k hk
      by_cases hkn : k < n
      · have hmod : (loc k).val = k := Nat.mod_eq_of_lt hkn
        congr 1; exact Fin.ext hmod
      · by_cases hk0 : k = n
        · have hmod : (loc k).val = 0 := by rw [hk0]; exact Nat.mod_self n
          have hfin1 : (⟨(loc k).val, by omega⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := Fin.ext hmod
          have hfin2 : (⟨k, hk⟩ : Fin (n + 2)) = ⟨n, by omega⟩ := Fin.ext hk0
          rw [hfin1, hfin2]
          exact hf0
        · have hk1 : k = n + 1 := by omega
          have hmod : (loc k).val = 1 := by
            rw [hk1]
            change (n + 1) % n = 1
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          have hfin1 : (⟨(loc k).val, by omega⟩ : Fin (n + 2)) = ⟨1, by omega⟩ := Fin.ext hmod
          have hfin2 : (⟨k, hk⟩ : Fin (n + 2)) = ⟨n + 1, by omega⟩ := Fin.ext hk1
          rw [hfin1, hfin2]
          exact hf1
    refine ⟨fun i => f ⟨i.val, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hs0⟩
      intro i
      have hpat : (fun o : Fin 3 => f ⟨(loc (i.val + o.val)).val, by omega⟩) =
          (fun o : Fin 3 => f ⟨i.val + o.val, by omega⟩) := by
        funext o
        exact hloc_eq (i.val + o.val) (by omega)
      rw [hpat]
      exact hall i
    · funext j
      dsimp only
      exact hloc_eq j.val j.isLt

lemma foldl_perm_eval {α : Type*} (l : List α) (f : α → Equiv.Perm (Fin 5))
    (init : Equiv.Perm (Fin 5)) (s : Fin 5) :
    (l.foldl (fun p j => f j * p) init) s = l.foldl (fun a j => f j a) (init s) := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (f x * init)

lemma flatMap_finRange_getElem {α : Type*} (B : ℕ) (hB : 0 < B) :
    ∀ (k : ℕ) (g : Fin k → List α),
      (∀ j, (g j).length = B) →
      ∀ (idx : ℕ) (hidx : idx < ((List.finRange k).flatMap g).length)
        (hdiv' : idx / B < k) (hmod' : idx % B < (g ⟨idx / B, hdiv'⟩).length),
        ((List.finRange k).flatMap g)[idx]'hidx = (g ⟨idx / B, hdiv'⟩)[idx % B]'hmod' := by
  intro k
  induction k with
  | zero =>
    intro g _ idx hidx
    simp at hidx
  | succ k ihk =>
    intro g hgl idx hidx hdiv' hmod'
    have hfr : (List.finRange (k + 1)).flatMap g =
        g 0 ++ (List.finRange k).flatMap (fun j => g j.succ) := by
      rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    have h0len : (g 0).length = B := hgl 0
    have hEq2 : ∀ (u v : Fin (k + 1)) (p q : ℕ) (hp : p < (g u).length) (hq : q < (g v).length),
        u = v → p = q → (g u)[p]'hp = (g v)[q]'hq := by
      rintro u _ p _ hp hq rfl rfl
      rfl
    by_cases hltB : idx < B
    · have hidx0 : idx < (g 0).length := by omega
      have hd0 : idx / B = 0 := Nat.div_eq_of_lt hltB
      have hm0 : idx % B = idx := Nat.mod_eq_of_lt hltB
      have hEq : ((List.finRange (k + 1)).flatMap g)[idx]'hidx = (g 0)[idx]'hidx0 := by
        simp only [hfr]
        rw [List.getElem_append_left hidx0]
      rw [hEq]
      have hfin : (0 : Fin (k + 1)) = ⟨idx / B, hdiv'⟩ := Fin.ext hd0.symm
      exact hEq2 0 ⟨idx / B, hdiv'⟩ idx (idx % B) hidx0 hmod' hfin hm0.symm
    · have hge0 : (g 0).length ≤ idx := by omega
      have hidx_sub : idx - B < ((List.finRange k).flatMap (fun j => g j.succ)).length := by
        have h1 : ((List.finRange (k + 1)).flatMap g).length =
            B + ((List.finRange k).flatMap (fun j => g j.succ)).length := by
          rw [hfr, List.length_append, h0len]
        omega
      have hEq : ((List.finRange (k + 1)).flatMap g)[idx]'hidx =
          ((List.finRange k).flatMap (fun j => g j.succ))[idx - B]'hidx_sub := by
        have hidx' : idx < (g 0 ++ (List.finRange k).flatMap (fun j => g j.succ)).length := by
          rw [← hfr]; exact hidx
        have hstep1 : ((List.finRange (k + 1)).flatMap g)[idx]'hidx =
            (g 0 ++ (List.finRange k).flatMap (fun j => g j.succ))[idx]'hidx' := by
          simp only [hfr]
        rw [hstep1, List.getElem_append_right hge0]
        congr 1
        rw [h0len]
      rw [hEq]
      have hdiv_sub : (idx - B) / B < k := by
        have := Nat.div_eq_sub_div hB (by omega : B ≤ idx)
        omega
      have hmod_sub : (idx - B) % B = idx % B := by
        have := Nat.mod_eq_sub_mod (by omega : B ≤ idx)
        omega
      have hgl' : ∀ j : Fin k, (g j.succ).length = B := fun j => hgl j.succ
      have hsub := ihk (fun j => g j.succ) hgl' (idx - B) hidx_sub hdiv_sub
        (by rw [hgl']; exact Nat.mod_lt _ hB)
      rw [hsub]
      have hfin : (⟨(idx - B) / B, hdiv_sub⟩ : Fin k).succ = ⟨idx / B, hdiv'⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        have := Nat.div_eq_sub_div hB (by omega : B ≤ idx)
        omega
      exact hEq2 _ _ _ _ _ _ hfin hmod_sub

lemma prodMatB_blocks {h : ℕ} (f : Fin h → Equiv.Perm (Fin 5)) :
    let B := 1154
    let n := h * B + 2
    let row : Fin n → Row := fun i pat =>
      if hi : i.val / B < h then
        permBlock (f ⟨i.val / B, hi⟩) ⟨i.val % B, Nat.mod_lt _ (by omega)⟩ pat
      else pat 0 == pat 2
    prodMatB ((List.finRange n).map row) =
      matPerm ((List.finRange h).foldl (fun p j => f j * p) 1) := by
  intro B n row
  have hsplit : (List.finRange n).map row =
      ((List.finRange h).flatMap (fun j => (List.finRange B).map (permBlock (f j)))) ++
        [rotRow, rotRow] := by
    have hlen_flat : ((List.finRange h).flatMap (fun j => (List.finRange B).map (permBlock (f j)))).length =
        h * B := by
      rw [List.length_flatMap]
      have hmap : ((List.finRange h).map (fun j => ((List.finRange B).map (permBlock (f j))).length)) =
          List.replicate h B := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          simp
      rw [hmap, List.sum_replicate, smul_eq_mul]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, List.length_append, hlen_flat,
        List.length_cons, List.length_nil, n, B]
    · intro i hi1 hi2
      have hi : i < h * B + 2 := by simpa only [List.length_map, List.length_finRange, n, B] using hi1
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      by_cases hlt : i < h * B
      · have hlt' : i < ((List.finRange h).flatMap (fun j => (List.finRange B).map (permBlock (f j)))).length := by
          omega
        rw [List.getElem_append_left hlt']
        have hdiv : i / B < h := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)
        have hmod : i % B < B := Nat.mod_lt i (by omega)
        have hrow : row ⟨i, hi⟩ = permBlock (f ⟨i / B, hdiv⟩) ⟨i % B, hmod⟩ := by
          funext pat
          simp only [row, dite_eq_left hdiv]
        rw [hrow]
        have hfg := flatMap_finRange_getElem B (by omega) h
          (fun j => (List.finRange B).map (permBlock (f j)))
          (fun j => by simp) i hlt' hdiv (by simp; exact hmod)
        rw [hfg, List.getElem_map, List.getElem_finRange]
        rfl
      · have hge : ((List.finRange h).flatMap (fun j => (List.finRange B).map (permBlock (f j)))).length ≤ i := by
          omega
        rw [List.getElem_append_right hge]
        have hndiv : ¬(i / B < h) := by
          intro hlt'
          have := Nat.lt_mul_of_div_lt hlt' (by omega : 0 < B)
          omega
        have hrow : row ⟨i, hi⟩ = rotRow := by
          funext pat
          simp only [row, dite_eq_right hndiv, rotRow]
        rw [hrow]
        simp only [hlen_flat]
        have hidx2 : i - h * B = 0 ∨ i - h * B = 1 := by omega
        rcases hidx2 with h0 | h1
        · simp [h0]
        · simp [h1]
  rw [hsplit, prodMatB_append, prodMatB_rotRow_pair, mulB_idB]
  have hfold : ∀ (l : List (Fin h)) (init : Equiv.Perm (Fin 5)),
      mulB (matPerm init) (prodMatB (l.flatMap (fun j => (List.finRange B).map (permBlock (f j))))) =
        matPerm (l.foldl (fun p j => f j * p) init) := by
    intro l
    induction l with
    | nil =>
      intro init
      simp only [List.flatMap_nil, List.foldl_nil, prodMatB, List.foldl_nil, mulB_idB]
    | cons j js ih =>
      intro init
      rw [List.flatMap_cons, prodMatB_append, ← mulB_assoc, prodMatB_permBlock (f j),
        matPerm_mul, List.foldl_cons]
      exact ih (f j * init)
  have hres := hfold (List.finRange h) 1
  rw [matPerm_one, idB_mulB] at hres
  exact hres

theorem main_proof :
    ∀ (m h : ℕ) (query : Fin h → Fin m) (step : Fin h → Bool → Equiv.Perm (Fin 5)),
      let B := 1154
      let n := h * B + 2
      let loc := fun k : ℕ => (⟨k % n, Nat.mod_lt _ (Nat.zero_lt_succ _)⟩ : Fin n)
      ∃ block : Fin h → Bool → Fin B → (Fin 3 → Bool) → Bool,
        ∀ input : Fin m → Bool,
          let row := fun (i : Fin n) (pat : Fin 3 → Bool) =>
            if hi : i.val / B < h then
              let j : Fin h := ⟨i.val / B, hi⟩
              block j (input (query j)) ⟨i.val % B, Nat.mod_lt _ (Nat.zero_lt_succ 1153)⟩ pat
            else pat 0 == pat 2
          let accepts := fun word : Fin n → Bool =>
            ∀ i : Fin n, row i (fun offset => word (loc (i.val + offset.val))) = true
          let finish := fun s : Fin 5 =>
            (List.finRange h).foldl (fun a j => step j (input (query j)) a) s
          (Finset.univ.filter accepts).card.testBit 0 =
            (Finset.univ.filter (fun point : Fin 5 => finish point ≠ point)).card.testBit 0 := by
  intro m h query step B n loc
  refine ⟨fun j b t => permBlock (step j b) t, ?_⟩
  intro input row accepts finish
  have hn : 2 ≤ n := by omega
  have hcard := card_cyclic_eq_trN hn row
  dsimp only at hcard
  rw [hcard, trN_testBit, mod2_prodMatN]
  have hprod := prodMatB_blocks (fun j => step j (input (query j)))
  dsimp only at hprod
  have hrow_eq : row = (fun (i : Fin n) (pat : Fin 3 → Bool) =>
      if hi : i.val / B < h then
        permBlock (step ⟨i.val / B, hi⟩ (input (query ⟨i.val / B, hi⟩)))
          ⟨i.val % B, Nat.mod_lt _ (by omega)⟩ pat
      else pat 0 == pat 2) := rfl
  rw [hrow_eq, hprod, trB_matPerm]
  have hfin : ∀ s : Fin 5, ((List.finRange h).foldl (fun p j => step j (input (query j)) * p) 1) s =
      finish s := by
    intro s
    simpa [finish] using foldl_perm_eval (List.finRange h) (fun j => step j (input (query j))) 1 s
  congr 2
  ext p
  simp [hfin p]

end PEqualNP.Outside.L_clb_104_aux

theorem PEqualNP.Outside.L_clb_104 : ∀ (m h : ℕ) (query : Fin h → Fin m) (step : Fin h → Bool → Equiv.Perm (Fin 5)),
  let B := 1154
  let n := h * B + 2
  let loc := fun k : ℕ => (⟨k % n, Nat.mod_lt _ (Nat.zero_lt_succ _)⟩ : Fin n)
  ∃ block : Fin h → Bool → Fin B → (Fin 3 → Bool) → Bool,
    ∀ input : Fin m → Bool,
      let row := fun (i : Fin n) (pat : Fin 3 → Bool) =>
        if hi : i.val / B < h then
          let j : Fin h := ⟨i.val / B, hi⟩
          block j (input (query j)) ⟨i.val % B, Nat.mod_lt _ (Nat.zero_lt_succ 1153)⟩ pat
        else pat 0 == pat 2
      let accepts := fun word : Fin n → Bool =>
        ∀ i : Fin n, row i (fun offset => word (loc (i.val + offset.val))) = true
      let finish := fun s : Fin 5 =>
        (List.finRange h).foldl (fun a j => step j (input (query j)) a) s
      (Finset.univ.filter accepts).card.testBit 0 =
        (Finset.univ.filter (fun point : Fin 5 => finish point ≠ point)).card.testBit 0 :=
  PEqualNP.Outside.L_clb_104_aux.main_proof
