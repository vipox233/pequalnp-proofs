import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_790

open Finset

def ALL : ℕ := 2 ^ 128 - 1

def Zm (i : ℕ) : ℕ :=
  (List.range 128).foldr (fun Y acc => if Y.testBit i then acc ||| 2 ^ Y else acc) 0

def ex (c : Bool) : ℕ := if c then ALL else 0

def T (bb X : ℕ) : ℕ :=
  let z := fun i => Zm i ^^^ ex (X.testBit i)
  let b := fun j => ex (bb.testBit j)
  let p := z 1 &&& z 2
  let q := (z 3 ^^^ (b 0 &&& p)) &&& (z 4 ^^^ (b 1 &&& p))
  let l := z 5 ^^^ (b 2 &&& p) ^^^ (b 3 &&& q)
  let r := z 6 ^^^ (b 4 &&& p) ^^^ (b 5 &&& q)
  z 0 ^^^ (b 6 &&& p) ^^^ (b 7 &&& q) ^^^ (l &&& r)

def fb (b z : ℕ → Bool) : Bool :=
  let p := z 1 && z 2
  let q := (z 3 ^^ (b 0 && p)) && (z 4 ^^ (b 1 && p))
  let l := z 5 ^^ (b 2 && p) ^^ (b 3 && q)
  let r := z 6 ^^ (b 4 && p) ^^ (b 5 && q)
  z 0 ^^ (b 6 && p) ^^ (b 7 && q) ^^ (l && r)

def piv (v : ℕ) : ℕ := ((List.range 128).find? (fun i => v.testBit i)).getD 0

def red (B : List (ℕ × ℕ)) (v : ℕ) : ℕ × List ℕ :=
  B.foldl (fun acc pb => if acc.1.testBit pb.1 then (acc.1 ^^^ pb.2, pb.2 :: acc.2) else acc)
    (v, [])

def ins (B : List (ℕ × ℕ)) (v : ℕ) : List (ℕ × ℕ) :=
  if (red B v).1 = 0 then B else
    (piv (red B v).1, (red B v).1) :: B.map (fun pb =>
      if pb.2.testBit (piv (red B v).1) then (pb.1, pb.2 ^^^ (red B v).1) else pb)

def basisOf (bb : ℕ) : List (ℕ × ℕ) :=
  (List.range 128).foldl (fun B X => ins B (T bb X)) []

def okAll : Bool := (List.range 256).all fun bb =>
  decide (((basisOf bb).map Prod.snd).length ≤ 16) &&
  (List.range 128).all fun X =>
    ((red (basisOf bb) (T bb X)).2.all fun b => decide (b ∈ (basisOf bb).map Prod.snd)) &&
    (T bb X == (red (basisOf bb) (T bb X)).2.foldr (· ^^^ ·) 0)

theorem okAll_true : okAll = true := by decide +kernel

theorem zmChk : ((List.range 7).all fun i => (List.range 128).all fun Y =>
    (Zm i).testBit Y == Y.testBit i) = true := by decide +kernel

theorem zm_bit {i Y : ℕ} (hi : i < 7) (hY : Y < 128) : (Zm i).testBit Y = Y.testBit i := by
  have h := zmChk
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi Y hY

theorem ex_bit (c : Bool) {Y : ℕ} (hY : Y < 128) : (ex c).testBit Y = c := by
  cases c
  · simp [ex]
  · show (2 ^ 128 - 1).testBit Y = true
    rw [Nat.testBit_two_pow_sub_one]
    simpa using hY

theorem T_bit (bb X : ℕ) {Y : ℕ} (hY : Y < 128) :
    (T bb X).testBit Y = fb bb.testBit (fun i => Y.testBit i ^^ X.testBit i) := by
  simp only [T, fb, Nat.testBit_xor, Nat.testBit_land, ex_bit _ hY,
    zm_bit (by norm_num : 0 < 7) hY, zm_bit (by norm_num : 1 < 7) hY,
    zm_bit (by norm_num : 2 < 7) hY, zm_bit (by norm_num : 3 < 7) hY,
    zm_bit (by norm_num : 4 < 7) hY, zm_bit (by norm_num : 5 < 7) hY,
    zm_bit (by norm_num : 6 < 7) hY]

def toB (a : ZMod 2) : Bool := decide (a = 1)

def toZ (c : Bool) : ZMod 2 := if c then 1 else 0

theorem toB_add (a b : ZMod 2) : toB (a + b) = (toB a ^^ toB b) := by
  revert a b; decide

theorem toB_mul (a b : ZMod 2) : toB (a * b) = (toB a && toB b) := by
  revert a b; decide

theorem toZ_toB (a : ZMod 2) : toZ (toB a) = a := by
  revert a; decide

theorem toZ_xor (c d : Bool) : toZ (c ^^ d) = toZ c + toZ d := by
  revert c d; decide

def outp (bits : Fin 8 → ZMod 2) (z : Fin 7 → ZMod 2) : ZMod 2 :=
  let p := z 1 * z 2
  let q := (z 3 + bits 0 * p) * (z 4 + bits 1 * p)
  let left := z 5 + bits 2 * p + bits 3 * q
  let right := z 6 + bits 4 * p + bits 5 * q
  z 0 + bits 6 * p + bits 7 * q + left * right

theorem outp_eq (bits : Fin 8 → ZMod 2) (z : Fin 7 → ZMod 2) (bB zB : ℕ → Bool)
    (hb : ∀ j : Fin 8, bB j = toB (bits j)) (hz : ∀ i : Fin 7, zB i = toB (z i)) :
    outp bits z = toZ (fb bB zB) := by
  rw [← toZ_toB (outp bits z)]
  congr 1
  have b0 : bB 0 = toB (bits 0) := hb 0
  have b1 : bB 1 = toB (bits 1) := hb 1
  have b2 : bB 2 = toB (bits 2) := hb 2
  have b3 : bB 3 = toB (bits 3) := hb 3
  have b4 : bB 4 = toB (bits 4) := hb 4
  have b5 : bB 5 = toB (bits 5) := hb 5
  have b6 : bB 6 = toB (bits 6) := hb 6
  have b7 : bB 7 = toB (bits 7) := hb 7
  have z0 : zB 0 = toB (z 0) := hz 0
  have z1 : zB 1 = toB (z 1) := hz 1
  have z2 : zB 2 = toB (z 2) := hz 2
  have z3 : zB 3 = toB (z 3) := hz 3
  have z4 : zB 4 = toB (z 4) := hz 4
  have z5 : zB 5 = toB (z 5) := hz 5
  have z6 : zB 6 = toB (z 6) := hz 6
  simp only [outp, fb, toB_add, toB_mul, b0, b1, b2, b3, b4, b5, b6, b7,
    z0, z1, z2, z3, z4, z5, z6]

def code (z : Fin 7 → ZMod 2) : ℕ :=
  (z 0).val + 2 * (z 1).val + 4 * (z 2).val + 8 * (z 3).val + 16 * (z 4).val +
    32 * (z 5).val + 64 * (z 6).val

theorem code_aux : ∀ a0 a1 a2 a3 a4 a5 a6 : ZMod 2, ∀ i : Fin 7,
    (a0.val + 2 * a1.val + 4 * a2.val + 8 * a3.val + 16 * a4.val +
      32 * a5.val + 64 * a6.val).testBit i = toB (![a0, a1, a2, a3, a4, a5, a6] i) := by
  decide +kernel

theorem code_bit (z : Fin 7 → ZMod 2) (i : Fin 7) : (code z).testBit i = toB (z i) := by
  unfold code
  rw [code_aux]
  fin_cases i <;> rfl

theorem code_lt (z : Fin 7 → ZMod 2) : code z < 128 := by
  have h0 := ZMod.val_lt (z 0)
  have h1 := ZMod.val_lt (z 1)
  have h2 := ZMod.val_lt (z 2)
  have h3 := ZMod.val_lt (z 3)
  have h4 := ZMod.val_lt (z 4)
  have h5 := ZMod.val_lt (z 5)
  have h6 := ZMod.val_lt (z 6)
  unfold code
  omega

def code8 (z : Fin 8 → ZMod 2) : ℕ :=
  (z 0).val + 2 * (z 1).val + 4 * (z 2).val + 8 * (z 3).val + 16 * (z 4).val +
    32 * (z 5).val + 64 * (z 6).val + 128 * (z 7).val

theorem code8_aux : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : ZMod 2, ∀ i : Fin 8,
    (a0.val + 2 * a1.val + 4 * a2.val + 8 * a3.val + 16 * a4.val +
      32 * a5.val + 64 * a6.val + 128 * a7.val).testBit i =
      toB (![a0, a1, a2, a3, a4, a5, a6, a7] i) := by
  decide +kernel

theorem code8_bit (z : Fin 8 → ZMod 2) (i : Fin 8) : (code8 z).testBit i = toB (z i) := by
  unfold code8
  rw [code8_aux]
  fin_cases i <;> rfl

theorem code8_lt (z : Fin 8 → ZMod 2) : code8 z < 256 := by
  have h0 := ZMod.val_lt (z 0)
  have h1 := ZMod.val_lt (z 1)
  have h2 := ZMod.val_lt (z 2)
  have h3 := ZMod.val_lt (z 3)
  have h4 := ZMod.val_lt (z 4)
  have h5 := ZMod.val_lt (z 5)
  have h6 := ZMod.val_lt (z 6)
  have h7 := ZMod.val_lt (z 7)
  unfold code8
  omega

theorem foldr_bit (u : List ℕ) (Y : ℕ) :
    toZ ((u.foldr (· ^^^ ·) 0).testBit Y) = (u.map (fun n => toZ (n.testBit Y))).sum := by
  induction u with
  | nil => simp [toZ]
  | cons a u ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, Nat.testBit_xor,
      toZ_xor, ih]

theorem lsum_apply {α : Type} (l : List (α → ZMod 2)) (y : α) :
    l.sum y = (l.map (fun v => v y)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Pi.add_apply, ih]

theorem chk (bb : ℕ) (hbb : bb < 256) :
    ((basisOf bb).map Prod.snd).length ≤ 16 ∧ ∀ X < 128,
      (∀ b ∈ (red (basisOf bb) (T bb X)).2, b ∈ (basisOf bb).map Prod.snd) ∧
      T bb X = (red (basisOf bb) (T bb X)).2.foldr (· ^^^ ·) 0 := by
  have h := okAll_true
  simp only [okAll, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨(h bb hbb).1, fun X hX => (h bb hbb).2 X hX⟩

theorem main (bits : Fin 8 → ZMod 2) :
    (Matrix.of (fun x y : Fin 7 → ZMod 2 => outp bits (x + y))).rank ≤ 16 := by
  obtain ⟨hlen, hX⟩ := chk (code8 bits) (code8_lt bits)
  let w : ℕ → (Fin 7 → ZMod 2) → ZMod 2 := fun n y => toZ (n.testBit (code y))
  have e1 : ∀ x y, outp bits (x + y) = toZ ((T (code8 bits) (code x)).testBit (code y)) := by
    intro x y
    rw [T_bit _ _ (code_lt y)]
    apply outp_eq
    · intro j
      exact code8_bit bits j
    · intro i
      simp only [Pi.add_apply, toB_add, code_bit]
      exact Bool.xor_comm _ _
  have hrow : ∀ x, (fun y => outp bits (x + y)) =
      ((red (basisOf (code8 bits)) (T (code8 bits) (code x))).2.map w).sum := by
    intro x
    funext y
    rw [lsum_apply, List.map_map, e1 x y]
    have e2 := (hX _ (code_lt x)).2
    rw [show toZ ((T (code8 bits) (code x)).testBit (code y)) =
        toZ (((red (basisOf (code8 bits)) (T (code8 bits) (code x))).2.foldr
          (· ^^^ ·) 0).testBit (code y)) by rw [← e2]]
    rw [foldr_bit]
    rfl
  set B := (basisOf (code8 bits)).map Prod.snd with hB
  have hspan : Submodule.span (ZMod 2) (Set.range (Matrix.of fun x y : Fin 7 → ZMod 2 =>
      outp bits (x + y))) ≤
      Submodule.span (ZMod 2) (Set.range (fun i : Fin B.length => w (B.get i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    show (fun y => outp bits (x + y)) ∈ _
    rw [hrow x]
    refine list_sum_mem (fun v hv => ?_)
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hv
    have hnB : n ∈ B := (hX _ (code_lt x)).1 n hn
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hnB
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row]
  calc _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun i : Fin B.length => w (B.get i)))) := Submodule.finrank_mono hspan
    _ ≤ Fintype.card (Fin B.length) := finrank_range_le_card _
    _ ≤ 16 := by simpa using hlen

end PEqualNP.Outside.L_lib_790

open PEqualNP.Outside.L_lib_790 in
theorem PEqualNP.Outside.L_lib_790 :
∀ bits : Fin 8 → ZMod 2,
  let output := fun (z : Fin 7 → ZMod 2) =>
    let p := z 1 * z 2
    let q := (z 3 + bits 0 * p) * (z 4 + bits 1 * p)
    let left := z 5 + bits 2 * p + bits 3 * q
    let right := z 6 + bits 4 * p + bits 5 * q
    z 0 + bits 6 * p + bits 7 * q + left * right
  (Matrix.of (fun x y : Fin 7 → ZMod 2 => output (x + y))).rank ≤ 16
 := by
  intro bits output
  exact main bits
