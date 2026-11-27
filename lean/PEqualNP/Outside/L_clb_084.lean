import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_084_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def matOf (f : Bool → Bool → Bool) : Fin 16 :=
  ⟨(if f false false then 1 else 0) +
   (if f true false then 2 else 0) +
   (if f false true then 4 else 0) +
   (if f true true then 8 else 0), by
    cases f false false <;> cases f true false <;> cases f false true <;> cases f true true <;> decide⟩

def entry (m : Fin 16) (r c : Bool) : Bool :=
  m.val.testBit ((if r then 1 else 0) + (if c then 2 else 0))

lemma entry_matOf (f : Bool → Bool → Bool) (r c : Bool) :
    entry (matOf f) r c = f r c := by
  cases h00 : f false false <;> cases h10 : f true false <;>
  cases h01 : f false true <;> cases h11 : f true true <;>
  cases r <;> cases c <;>
  simp [entry, matOf, h00, h10, h01, h11] <;> decide

lemma matOf_entry (m : Fin 16) : matOf (entry m) = m := by
  fin_cases m <;> decide

def mMul (A B : Fin 16) : Fin 16 :=
  matOf (fun r c => xor (entry A r false && entry B false c) (entry A r true && entry B true c))

def mId : Fin 16 := matOf (fun r c => decide (r = c))
def mZero : Fin 16 := ⟨0, by decide⟩
def mTrans (A : Fin 16) : Fin 16 := matOf (fun r c => entry A c r)
def mTrace (A : Fin 16) : Bool := xor (entry A false false) (entry A true true)
def mDet (A : Fin 16) : Bool := xor (entry A false false && entry A true true) (entry A false true && entry A true false)
def mIsZero (A : Fin 16) : Bool := decide (A.val = 0)
def mIsInv (A : Fin 16) : Bool := mDet A
def mIsRank1 (A : Fin 16) : Bool := !mIsZero A && !mIsInv A
def mInvPart (A : Fin 16) : Fin 16 := if mIsInv A then A else mId

def vecBit (v : Fin 3) (b : Bool) : Bool :=
  match v.val with
  | 0 => !b
  | 1 => b
  | _ => true

def vOfBits (b0 b1 : Bool) : Fin 3 :=
  if b0 then (if b1 then ⟨2, by decide⟩ else ⟨0, by decide⟩) else ⟨1, by decide⟩

def vDot (u v : Fin 3) : Bool :=
  xor (vecBit u false && vecBit v false) (vecBit u true && vecBit v true)

def outer (c r : Fin 3) : Fin 16 :=
  matOf (fun a b => vecBit c a && vecBit r b)

def gOf (s : Bool) (t : Fin 3) : Fin 16 :=
  let img (z : Fin 3) : Fin 3 :=
    if s then ⟨(3 - z.val + t.val) % 3, Nat.mod_lt _ (by decide)⟩
    else ⟨(z.val + t.val) % 3, Nat.mod_lt _ (by decide)⟩
  matOf (fun a b => vecBit (img (if b then ⟨1, by decide⟩ else ⟨0, by decide⟩)) a)

def gInv (s : Bool) (t : Fin 3) : Bool × Fin 3 :=
  if s then (true, t) else (false, ⟨(3 - t.val) % 3, Nat.mod_lt _ (by decide)⟩)

def gSign (m : Fin 16) : Bool :=
  decide (m = gOf true ⟨0, by decide⟩ ∨ m = gOf true ⟨1, by decide⟩ ∨ m = gOf true ⟨2, by decide⟩)

def gTrans (m : Fin 16) : Fin 3 :=
  if m = gOf false ⟨1, by decide⟩ ∨ m = gOf true ⟨1, by decide⟩ then ⟨1, by decide⟩
  else if m = gOf false ⟨2, by decide⟩ ∨ m = gOf true ⟨2, by decide⟩ then ⟨2, by decide⟩
  else ⟨0, by decide⟩

def matActVec (A : Fin 16) (v : Fin 3) : Fin 3 :=
  vOfBits
    (xor (entry A false false && vecBit v false) (entry A false true && vecBit v true))
    (xor (entry A true false && vecBit v false) (entry A true true && vecBit v true))

def gActC (s : Bool) (t : Fin 3) (c : Fin 3) : Fin 3 :=
  matActVec (gOf s t) c

def gActR (s : Bool) (t : Fin 3) (r : Fin 3) : Fin 3 :=
  let gi := gInv s t
  matActVec (mTrans (gOf gi.1 gi.2)) r

def mCol (m : Fin 16) : Fin 3 :=
  vOfBits (entry m false false || entry m false true) (entry m true false || entry m true true)

def mRow (m : Fin 16) : Fin 3 :=
  vOfBits (entry m false false || entry m true false) (entry m false true || entry m true true)

def bDot (s : Bool) (t : Fin 3) (c r : Fin 3) : Bool :=
  mTrace (mMul (outer c r) (gOf s t))

lemma mMul_assoc (A B C : Fin 16) : mMul (mMul A B) C = mMul A (mMul B C) := by
  revert A B C; decide

lemma mMul_id_left (A : Fin 16) : mMul mId A = A := by
  revert A; decide

lemma mMul_id_right (A : Fin 16) : mMul A mId = A := by
  revert A; decide

lemma mMul_zero_left (A : Fin 16) : mMul mZero A = mZero := by
  revert A; decide

lemma mMul_zero_right (A : Fin 16) : mMul A mZero = mZero := by
  revert A; decide

lemma mTrace_zero : mTrace mZero = false := by decide

lemma mInvPart_eq_gOf (m : Fin 16) : mInvPart m = gOf (gSign m) (gTrans m) := by
  revert m; decide

lemma gOf_mul (s1 : Bool) (t1 : Fin 3) (s2 : Bool) (t2 : Fin 3) :
    mMul (gOf s1 t1) (gOf s2 t2) =
      gOf (xor s1 s2) ⟨(t1.val + (if s1 then 2 * t2.val else t2.val)) % 3, Nat.mod_lt _ (by decide)⟩ := by
  revert s1 t1 s2 t2; decide

lemma gOf_inv_right (s : Bool) (t : Fin 3) :
    mMul (gOf s t) (gOf (gInv s t).1 (gInv s t).2) = mId := by
  revert s t; decide

lemma gOf_inv_left (s : Bool) (t : Fin 3) :
    mMul (gOf (gInv s t).1 (gInv s t).2) (gOf s t) = mId := by
  revert s t; decide

lemma gOf_id : gOf false ⟨0, by decide⟩ = mId := by decide

lemma rank1_outer (m : Fin 16) (h : mIsRank1 m = true) :
    m = outer (mCol m) (mRow m) := by
  revert m h; decide

lemma conj_outer (s : Bool) (t c r : Fin 3) :
    mMul (mMul (gOf s t) (outer c r)) (gOf (gInv s t).1 (gInv s t).2) =
      outer (gActC s t c) (gActR s t r) := by
  revert s t c r; decide

lemma outer_mul_outer (c1 r1 c2 r2 : Fin 3) :
    mMul (outer c1 r1) (outer c2 r2) = if vDot r1 c2 then outer c1 r2 else mZero := by
  revert c1 r1 c2 r2; decide

lemma trace_gOf (s : Bool) (t : Fin 3) :
    mTrace (gOf s t) = (!s && decide (t.val ≠ 0)) := by
  revert s t; decide

lemma vDot_eq_false (u v : Fin 3) :
    vDot u v = false ↔
      (u = ⟨0, by decide⟩ ∧ v = ⟨1, by decide⟩) ∨
      (u = ⟨1, by decide⟩ ∧ v = ⟨0, by decide⟩) ∨
      (u = ⟨2, by decide⟩ ∧ v = ⟨2, by decide⟩) := by
  revert u v; decide

lemma mIsZero_iff (m : Fin 16) : mIsZero m = true ↔ m = mZero := by
  revert m; decide

lemma trichotomy_mat (m : Fin 16) :
    mIsZero m = true ∨ mIsInv m = true ∨ mIsRank1 m = true := by
  revert m; decide

def mProd : List (Fin 16) → Fin 16
  | [] => mId
  | A :: rest => mMul A (mProd rest)

lemma mProd_append (l1 l2 : List (Fin 16)) :
    mProd (l1 ++ l2) = mMul (mProd l1) (mProd l2) := by
  induction l1 with
  | nil => simp [mProd, mMul_id_left]
  | cons a t ih => simp [mProd, ih, mMul_assoc]

lemma mProd_eq_zero_of_mem {l : List (Fin 16)} (h : mZero ∈ l) : mProd l = mZero := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | ht
    · simp [mProd, mMul_zero_left]
    · simp [mProd, ih ht, mMul_zero_right]

def walkCount (k : ℕ) (T : Fin k → Bool → Bool → Bool) (a b : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin (k + 1) → Bool)).filter (fun w =>
    w 0 = a ∧ w ⟨k, Nat.lt_succ_self k⟩ = b ∧
    ∀ i : Fin k, T i (w i.castSucc) (w i.succ) = true)).card

lemma walkCount_mod2 (k : ℕ) (T : Fin k → Bool → Bool → Bool) (a b : Bool) :
    decide (walkCount k T a b % 2 = 1) =
      entry (mProd (List.ofFn (fun i : Fin k => matOf (T i)))) a b := by
  induction k generalizing a b with
  | zero =>
    have hcard : walkCount 0 T a b = if a = b then 1 else 0 := by
      unfold walkCount
      by_cases hab : a = b
      · subst hab
        have hEq : (Finset.univ.filter (fun w : Fin 1 → Bool =>
            w 0 = a ∧ w ⟨0, Nat.lt_succ_self 0⟩ = a ∧
            ∀ i : Fin 0, T i (w i.castSucc) (w i.succ) = true)) = {fun _ => a} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h; funext i; fin_cases i; exact h.1
          · intro h; subst h; exact ⟨rfl, rfl, fun i => Fin.elim0 i⟩
        rw [hEq, Finset.card_singleton, if_pos rfl]
      · have hEq : (Finset.univ.filter (fun w : Fin 1 → Bool =>
            w 0 = a ∧ w ⟨0, Nat.lt_succ_self 0⟩ = b ∧
            ∀ i : Fin 0, T i (w i.castSucc) (w i.succ) = true)) = ∅ := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h; exact hab (h.1.symm.trans h.2.1)
        rw [hEq, Finset.card_empty, if_neg hab]
    rw [hcard]
    simp only [List.ofFn_zero, mProd, mId, entry_matOf]
    by_cases hab : a = b <;> simp [hab]
  | succ k ih =>
    let T' : Fin k → Bool → Bool → Bool := fun i => T i.succ
    have hsplit : walkCount (k + 1) T a b =
        (if T 0 a false = true then walkCount k T' false b else 0) +
        (if T 0 a true = true then walkCount k T' true b else 0) := by
      let S := (Finset.univ : Finset (Fin (k + 2) → Bool)).filter (fun w =>
        w 0 = a ∧ w ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = b ∧
        ∀ i : Fin (k + 1), T i (w i.castSucc) (w i.succ) = true)
      have hpart : S.card =
          (S.filter (fun w => w ⟨1, by omega⟩ = false)).card +
          (S.filter (fun w => w ⟨1, by omega⟩ = true)).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext w
          simp only [Finset.mem_union, Finset.mem_filter]
          cases h1 : w ⟨1, by omega⟩ <;> simp
        · rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_filter] at hw1 hw2
          rw [hw1.2] at hw2; exact Bool.false_ne_true hw2.2
      have hbranch (mid : Bool) :
          (S.filter (fun w => w ⟨1, by omega⟩ = mid)).card =
          if T 0 a mid = true then walkCount k T' mid b else 0 := by
        by_cases hT0 : T 0 a mid = true
        · rw [if_pos hT0]
          unfold walkCount
          refine Finset.card_nbij' (fun w => fun j : Fin (k + 1) => w j.succ)
            (fun u => Fin.cons a u) ?_ ?_ ?_ ?_
          · intro w hw
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hw ⊢
            refine ⟨hw.2, hw.1.2.1, fun i => hw.1.2.2 i.succ⟩
          · intro u hu
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hu ⊢
            refine ⟨⟨rfl, hu.2.1, ?_⟩, hu.1⟩
            intro i
            cases i using Fin.cases with
            | zero =>
              change T 0 a (u 0) = true
              rw [hu.1]; exact hT0
            | succ j =>
              exact hu.2.2 j
          · intro w hw
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hw
            funext j
            cases j using Fin.cases with
            | zero => exact hw.1.1.symm
            | succ r => rfl
          · intro u _
            funext j; rfl
        · rw [if_neg hT0]
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hw
          have h0 := hw.1.2.2 0
          change T 0 (w 0) (w ⟨1, by omega⟩) = true at h0
          rw [hw.1.1, hw.2] at h0
          exact hT0 h0
      exact hpart.trans (by rw [hbranch false, hbranch true])
    rw [List.ofFn_succ, mProd, mMul, entry_matOf]
    rw [← ih T' false b, ← ih T' true b, entry_matOf, entry_matOf, hsplit]
    have hpar (p q : ℕ) : decide ((p + q) % 2 = 1) = xor (decide (p % 2 = 1)) (decide (q % 2 = 1)) := by
      have hp : p % 2 = 0 ∨ p % 2 = 1 := Nat.mod_two_eq_zero_or_one p
      have hq : q % 2 = 0 ∨ q % 2 = 1 := Nat.mod_two_eq_zero_or_one q
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp [Nat.add_mod, hp, hq]
    rw [hpar]
    have h0m : decide (0 % 2 = 1) = false := rfl
    cases h0 : T 0 a false <;> cases h1 : T 0 a true <;> simp [h0, h1, h0m, T']

lemma words_card_mod2_iff (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
      ∀ i : Fin n, T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true)).card % 2 = 1 ↔
    mTrace (mProd (List.ofFn (fun i : Fin n => matOf (T i)))) = true := by
  let words := (Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
    ∀ i : Fin n, T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true)
  have hpart : words.card =
      (words.filter (fun w => w ⟨0, hn⟩ = false)).card +
      (words.filter (fun w => w ⟨0, hn⟩ = true)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter]
      cases h0 : w ⟨0, hn⟩ <;> simp
    · rw [Finset.disjoint_left]; intro w h1 h2
      simp only [Finset.mem_filter] at h1 h2; rw [h1.2] at h2; exact Bool.false_ne_true h2.2
  have hbr (a : Bool) : (words.filter (fun w => w ⟨0, hn⟩ = a)).card = walkCount n T a a := by
    unfold walkCount
    refine Finset.card_nbij'
      (fun w => fun j : Fin (n + 1) => if h : j.val < n then w ⟨j.val, h⟩ else w ⟨0, hn⟩)
      (fun u => fun i : Fin n => u i.castSucc) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, words] at hw ⊢
      refine ⟨?_, ?_, ?_⟩
      · simp [hn, hw.2]
      · simp [hw.2]
      · intro i
        have hi := hw.1 i
        simp only [Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta]
        by_cases h1 : i.val + 1 < n
        · simp only [Fin.val_succ, h1, ↓reduceDIte]
          have hmod : (i.val + 1) % n = i.val + 1 := Nat.mod_eq_of_lt h1
          simpa [hmod] using hi
        · simp only [Fin.val_succ, h1, ↓reduceDIte]
          have heq : i.val + 1 = n := by omega
          have hmod : (i.val + 1) % n = 0 := by rw [heq, Nat.mod_self]
          simpa [hmod] using hi
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, words] at hu ⊢
      refine ⟨?_, hu.1⟩
      intro i
      have hi := hu.2.2 i
      by_cases h1 : i.val + 1 < n
      · have hmod : (i.val + 1) % n = i.val + 1 := Nat.mod_eq_of_lt h1
        have hfin : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n).castSucc = i.succ := by
          apply Fin.ext; simp [hmod]
        rwa [hfin]
      · have heq : i.val + 1 = n := by omega
        have hmod : (i.val + 1) % n = 0 := by rw [heq, Nat.mod_self]
        have h0 : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n).castSucc = 0 := by
          apply Fin.ext; simp [hmod]
        have hsucc : i.succ = ⟨n, Nat.lt_succ_self n⟩ := by apply Fin.ext; simp [heq]
        rw [h0, hu.1]
        rw [hsucc, hu.2.1] at hi
        exact hi
    · intro w _
      funext i; simp [i.isLt]
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter] at hu
      funext j
      by_cases hj : j.val < n
      · simp [hj]
      · have hjEq : j = ⟨n, Nat.lt_succ_self n⟩ := by apply Fin.ext; dsimp; omega
        subst hjEq; simp only [lt_irrefl, ↓reduceDIte]
        exact hu.2.1.trans hu.2.2.1.symm
  rw [hpart, hbr false, hbr true]
  have hf := walkCount_mod2 n T false false
  have ht := walkCount_mod2 n T true true
  unfold mTrace
  rw [← hf, ← ht]
  have hp : walkCount n T false false % 2 = 0 ∨ walkCount n T false false % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  have hq : walkCount n T true true % 2 = 0 ∨ walkCount n T true true % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp [Nat.add_mod, hp, hq]

lemma pow2_log2_le (n : ℕ) (hn : 0 < n) : 2 ^ Nat.log2 n ≤ n :=
  Nat.log2_self_le (by omega)

lemma lt_pow2_log2_succ (n : ℕ) : n < 2 ^ (Nat.log2 n + 1) :=
  Nat.lt_log2_self

lemma log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  induction a using Nat.strong_induction_on generalizing b with
  | ind a ih =>
    rw [Nat.log2_def a, Nat.log2_def b]
    split_ifs with ha hb hb
    · exact Nat.add_le_add_right (ih (a / 2) (by omega) (Nat.div_le_div_right h)) 1
    · omega
    · omega
    · exact le_rfl

lemma log2_le_self (n : ℕ) : Nat.log2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [Nat.log2_def n]
    split_ifs with h2
    · have h1 := ih (n / 2) (by omega)
      omega
    · omega

def v2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0
termination_by n => n

lemma v2_spec (m : ℕ) (hm : 0 < m) :
    2 ^ v2 m ∣ m ∧ (m / 2 ^ v2 m) % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero => omega
    | succ k =>
      rw [v2]
      split_ifs with heven
      · have hpos : 0 < (k + 1) / 2 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rcases ih ((k + 1) / 2) hlt hpos with ⟨hdvd, hodd⟩
        rcases hdvd with ⟨q, hq⟩
        have hmEq : k + 1 = 2 ^ (1 + v2 ((k + 1) / 2)) * q := by
          rw [Nat.pow_add, Nat.pow_one, Nat.mul_assoc, ← hq]; omega
        refine ⟨⟨q, hmEq⟩, ?_⟩
        conv_lhs => arg 1; arg 1; rw [hmEq]
        rw [Nat.mul_div_cancel_left q (Nat.two_pow_pos _)]
        have hqEq : q = (k + 1) / 2 / 2 ^ v2 ((k + 1) / 2) := by
          conv_rhs => arg 1; rw [hq]
          rw [Nat.mul_div_cancel_left q (Nat.two_pow_pos _)]
        rw [hqEq]; exact hodd
      · simp only [Nat.pow_zero, one_dvd, Nat.div_one, true_and]
        omega

lemma v2_odd_mul_pow2 (b l : ℕ) : v2 ((2 * b + 1) * 2 ^ l) = l := by
  induction l with
  | zero =>
    have hpos : 0 < 2 * b + 1 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 * b + 1 ≠ 0)
    simp only [Nat.pow_zero, Nat.mul_one, hk, v2]
    have hodd : (k + 1) % 2 ≠ 0 := by omega
    simp [hodd]
  | succ l ih =>
    have hne : (2 * b + 1) * 2 ^ (l + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [Nat.succ_eq_add_one] at hk
    rw [hk, v2]
    have heven : (k + 1) % 2 = 0 := by rw [← hk, Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [if_pos heven]
    have hdiv : (k + 1) / 2 = (2 * b + 1) * 2 ^ l := by
      rw [← hk, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
    rw [hdiv, ih]; omega

lemma v2_lt_log2_succ (n m : ℕ) (hm0 : 0 < m) (hmn : m < n) : v2 m < Nat.log2 n + 1 := by
  have hdvd := (v2_spec m hm0).1
  have hle : 2 ^ v2 m ≤ m := Nat.le_of_dvd hm0 hdvd
  have hlt : 2 ^ v2 m < 2 ^ (Nat.log2 n + 1) := lt_of_le_of_lt hle (lt_trans hmn (lt_pow2_log2_succ n))
  by_contra hge
  push_neg at hge
  have h2 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hge
  omega

def prefSign {n : ℕ} (Ms : Fin n → Fin 16) (i : ℕ) : Bool :=
  decide (((List.finRange (min i n)).map (fun j => gSign (Ms ⟨j.val, by omega⟩))).count true % 2 = 1)

def signedU {n : ℕ} (Ms : Fin n → Fin 16) (j : Fin n) : ℕ :=
  if prefSign Ms j.val then (2 * (gTrans (Ms j)).val) % 3 else (gTrans (Ms j)).val

def prefTrans {n : ℕ} (Ms : Fin n → Fin 16) (i : ℕ) : Fin 3 :=
  ⟨(((List.finRange (min i n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum) % 3,
   Nat.mod_lt _ (by decide)⟩

def prefMat {n : ℕ} (Ms : Fin n → Fin 16) (i : ℕ) : Fin 16 :=
  gOf (prefSign Ms i) (prefTrans Ms i)

lemma map_finRange_eq {n a b : ℕ} (hab : a = b) (ha : a ≤ n) (hb : b ≤ n) {α : Type*} (f : Fin n → α) :
    (List.finRange a).map (fun j => f ⟨j.val, by omega⟩) =
    (List.finRange b).map (fun j => f ⟨j.val, by omega⟩) := by
  subst hab; rfl

lemma prefSign_zero {n : ℕ} (Ms : Fin n → Fin 16) : prefSign Ms 0 = false := by
  unfold prefSign
  rw [map_finRange_eq (Nat.zero_min n) (Nat.min_le_right _ _) (Nat.zero_le n) (fun j => gSign (Ms j))]
  rfl

lemma prefTrans_zero {n : ℕ} (Ms : Fin n → Fin 16) : prefTrans Ms 0 = ⟨0, by decide⟩ := by
  apply Fin.ext
  unfold prefTrans
  change (((List.finRange (min 0 n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum) % 3 = 0
  rw [map_finRange_eq (Nat.zero_min n) (Nat.min_le_right _ _) (Nat.zero_le n)]
  rfl

lemma prefMat_zero {n : ℕ} (Ms : Fin n → Fin 16) : prefMat Ms 0 = mId := by
  unfold prefMat; rw [prefSign_zero, prefTrans_zero]; exact gOf_id

lemma prefSign_succ {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) :
    prefSign Ms (i.val + 1) = xor (prefSign Ms i.val) (gSign (Ms i)) := by
  unfold prefSign
  rw [map_finRange_eq (Nat.min_eq_left i.isLt) (Nat.min_le_right _ _) i.isLt (fun j => gSign (Ms j)),
      map_finRange_eq (Nat.min_eq_left (le_of_lt i.isLt)) (Nat.min_le_right _ _) (le_of_lt i.isLt) (fun j => gSign (Ms j)),
      List.finRange_succ_last, List.map_append, List.map_singleton, List.count_append]
  have hmap : List.map (fun j : Fin i.val => gSign (Ms ⟨j.val, by omega⟩)) (List.finRange i.val) =
      List.map (fun j : Fin (i.val + 1) => gSign (Ms ⟨j.val, by omega⟩))
        (List.map Fin.castSucc (List.finRange i.val)) := by
    rw [List.map_map]; rfl
  rw [← hmap]
  set c := (List.map (fun j : Fin i.val => gSign (Ms ⟨j.val, by omega⟩)) (List.finRange i.val)).count true
  have hc : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
  have hlast : (⟨(Fin.last i.val).val, by omega⟩ : Fin n) = i := by apply Fin.ext; simp
  rw [hlast]
  cases hg : gSign (Ms i) <;> rcases hc with hc | hc <;> simp [Nat.add_mod, hc, hg]

lemma prefTrans_succ {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) :
    prefTrans Ms (i.val + 1) =
      ⟨((prefTrans Ms i.val).val + (if prefSign Ms i.val then 2 * (gTrans (Ms i)).val else (gTrans (Ms i)).val)) % 3,
       Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  unfold prefTrans
  change (((List.finRange (min (i.val + 1) n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum) % 3 =
    ((((List.finRange (min i.val n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum) % 3 +
      (if prefSign Ms i.val then 2 * (gTrans (Ms i)).val else (gTrans (Ms i)).val)) % 3
  rw [map_finRange_eq (Nat.min_eq_left i.isLt) (Nat.min_le_right _ _) i.isLt (signedU Ms),
      map_finRange_eq (Nat.min_eq_left (le_of_lt i.isLt)) (Nat.min_le_right _ _) (le_of_lt i.isLt) (signedU Ms),
      List.finRange_succ_last, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
  have hmap : List.map (fun j : Fin i.val => signedU Ms ⟨j.val, by omega⟩) (List.finRange i.val) =
      List.map (fun j : Fin (i.val + 1) => signedU Ms ⟨j.val, by omega⟩)
        (List.map Fin.castSucc (List.finRange i.val)) := by
    rw [List.map_map]; rfl
  rw [← hmap]
  have hlast : (⟨(Fin.last i.val).val, by omega⟩ : Fin n) = i := by apply Fin.ext; simp
  rw [hlast]
  unfold signedU
  cases hs : prefSign Ms i.val
  · simp [Nat.add_mod]
  · simp [Nat.add_mod]

lemma prefMat_succ {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) :
    prefMat Ms (i.val + 1) = mMul (prefMat Ms i.val) (mInvPart (Ms i)) := by
  unfold prefMat
  rw [mInvPart_eq_gOf, gOf_mul, prefSign_succ, prefTrans_succ]

def tildeC {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) : Fin 3 :=
  gActC (prefSign Ms i.val) (prefTrans Ms i.val) (mCol (Ms i))

def tildeR {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) : Fin 3 :=
  gActR (prefSign Ms i.val) (prefTrans Ms i.val) (mRow (Ms i))

def conjMat {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) : Fin 16 :=
  let gi := gInv (prefSign Ms (i.val + 1)) (prefTrans Ms (i.val + 1))
  mMul (mMul (prefMat Ms i.val) (Ms i)) (gOf gi.1 gi.2)

lemma conjMat_of_inv {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) (hinv : mIsInv (Ms i) = true) :
    conjMat Ms i = mId := by
  unfold conjMat
  have hps : prefMat Ms (i.val + 1) = mMul (prefMat Ms i.val) (Ms i) := by
    rw [prefMat_succ]; unfold mInvPart; rw [if_pos hinv]
  rw [← hps]
  exact gOf_inv_right (prefSign Ms (i.val + 1)) (prefTrans Ms (i.val + 1))

lemma conjMat_of_rank1 {n : ℕ} (Ms : Fin n → Fin 16) (i : Fin n) (hr1 : mIsRank1 (Ms i) = true) :
    conjMat Ms i = outer (tildeC Ms i) (tildeR Ms i) := by
  have hnotInv : mIsInv (Ms i) = false := by
    unfold mIsRank1 at hr1; cases h : mIsInv (Ms i) <;> simp [h] at hr1 ⊢
  have hps : prefMat Ms (i.val + 1) = prefMat Ms i.val := by
    rw [prefMat_succ]; unfold mInvPart; rw [if_neg (by simp [hnotInv]), mMul_id_right]
  have hsign : prefSign Ms (i.val + 1) = prefSign Ms i.val := by
    have hgs : ∀ m : Fin 16, mIsInv m = false → gSign m = false := by decide
    rw [prefSign_succ, hgs (Ms i) hnotInv]; simp
  have htr : prefTrans Ms (i.val + 1) = prefTrans Ms i.val := by
    have hgt : ∀ m : Fin 16, mIsInv m = false → gTrans m = ⟨0, by decide⟩ := by decide
    apply Fin.ext
    rw [prefTrans_succ, hgt (Ms i) hnotInv]
    cases prefSign Ms i.val <;> simp [Nat.mod_eq_of_lt (prefTrans Ms i.val).isLt]
  unfold conjMat tildeC tildeR prefMat
  rw [hsign, htr]
  have houter := rank1_outer (Ms i) hr1
  conv_lhs => rw [houter]
  exact conj_outer (prefSign Ms i.val) (prefTrans Ms i.val) (mCol (Ms i)) (mRow (Ms i))

lemma mProd_take_eq {n : ℕ} (Ms : Fin n → Fin 16) (k : ℕ) (hk : k ≤ n) :
    mProd ((List.finRange k).map (fun j => Ms ⟨j.val, by omega⟩)) =
      mMul (mProd ((List.finRange k).map (fun j => conjMat Ms ⟨j.val, by omega⟩))) (prefMat Ms k) := by
  induction k with
  | zero => simp [mProd, prefMat_zero, mMul_id_left]
  | succ k ih =>
    rw [List.finRange_succ_last, List.map_append, List.map_singleton, mProd_append,
      List.map_append, List.map_singleton, mProd_append]
    have hm1 : List.map (fun j : Fin k => Ms ⟨j.val, by omega⟩) (List.finRange k) =
        List.map (fun j : Fin (k + 1) => Ms ⟨j.val, by omega⟩) (List.map Fin.castSucc (List.finRange k)) := by
      rw [List.map_map]; rfl
    have hm2 : List.map (fun j : Fin k => conjMat Ms ⟨j.val, by omega⟩) (List.finRange k) =
        List.map (fun j : Fin (k + 1) => conjMat Ms ⟨j.val, by omega⟩) (List.map Fin.castSucc (List.finRange k)) := by
      rw [List.map_map]; rfl
    rw [← hm1, ← hm2, ih (by omega)]
    simp only [mProd, mMul_id_right, Fin.val_last]
    let ik : Fin n := ⟨k, by omega⟩
    have hstep : mMul (conjMat Ms ik) (prefMat Ms (k + 1)) = mMul (prefMat Ms k) (Ms ik) := by
      unfold conjMat prefMat
      rw [mMul_assoc, gOf_inv_left, mMul_id_right]
    rw [mMul_assoc, ← hstep, ← mMul_assoc]

lemma list_ofFn_eq_map_finRange {n : ℕ} {α : Type*} (f : Fin n → α) :
    List.ofFn f = (List.finRange n).map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

def ConsecRank1 {n : ℕ} (Ms : Fin n → Fin 16) (a b : Fin n) : Prop :=
  a.val < b.val ∧ mIsRank1 (Ms a) = true ∧ mIsRank1 (Ms b) = true ∧
  ∀ k : Fin n, a.val < k.val → k.val < b.val → mIsRank1 (Ms k) = false

open Classical in
lemma mProd_conj_spec {n : ℕ} (Ms : Fin n → Fin 16)
    (hnoZero : ∀ i : Fin n, mIsZero (Ms i) = false) (k : ℕ) (hk : k ≤ n) :
    let P := mProd ((List.finRange k).map (fun j => conjMat Ms ⟨j.val, by omega⟩))
    (∀ i : Fin n, i.val < k → mIsRank1 (Ms i) = false) ∧ P = mId ∨
    ∃ (i1 im : Fin n),
      i1.val < k ∧ im.val < k ∧
      mIsRank1 (Ms i1) = true ∧ mIsRank1 (Ms im) = true ∧
      (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
      (∀ j : Fin n, im.val < j.val → j.val < k → mIsRank1 (Ms j) = false) ∧
      P = if (∀ a b : Fin n, a.val < k → b.val < k → ConsecRank1 Ms a b → vDot (tildeR Ms a) (tildeC Ms b) = true)
          then outer (tildeC Ms i1) (tildeR Ms im) else mZero := by
  induction k with
  | zero =>
    left
    exact ⟨fun i hi => by omega, rfl⟩
  | succ k ih =>
    dsimp only
    rw [List.finRange_succ_last, List.map_append, List.map_singleton, mProd_append]
    have hm : List.map (fun j : Fin k => conjMat Ms ⟨j.val, by omega⟩) (List.finRange k) =
        List.map (fun j : Fin (k + 1) => conjMat Ms ⟨j.val, by omega⟩) (List.map Fin.castSucc (List.finRange k)) := by
      rw [List.map_map]; rfl
    rw [← hm]
    simp only [mProd, mMul_id_right, Fin.val_last]
    let ik : Fin n := ⟨k, by omega⟩
    rcases ih (by omega) with ⟨hnone, hP⟩ | ⟨i1, im, hi1, him, hr1, hrm, hfirst, hlast, hP⟩
    · by_cases hrk : mIsRank1 (Ms ik) = true
      · right
        refine ⟨ik, ik, by dsimp [ik]; omega, by dsimp [ik]; omega, hrk, hrk,
          fun j hj => hnone j (by dsimp [ik] at hj; omega), fun j hj1 hj2 => by dsimp [ik] at hj1; omega, ?_⟩
        rw [hP, mMul_id_left, conjMat_of_rank1 Ms ik hrk]
        have hvac : ∀ a b : Fin n, a.val < k + 1 → b.val < k + 1 → ConsecRank1 Ms a b →
            vDot (tildeR Ms a) (tildeC Ms b) = true := by
          intro a b ha hb hcon
          have ha_lt : a.val < k := by have := hcon.1; omega
          have hfa := hnone a ha_lt
          rw [hcon.2.1] at hfa; exact absurd hfa Bool.false_ne_true.symm
        rw [if_pos hvac]
      · have hnotr : mIsRank1 (Ms ik) = false := by
          cases h : mIsRank1 (Ms ik) <;> simp [h] at hrk ⊢
        have hinv : mIsInv (Ms ik) = true := by
          rcases trichotomy_mat (Ms ik) with hz | hinv | hr
          · rw [hnoZero ik] at hz; exact absurd hz Bool.false_ne_true
          · exact hinv
          · exact absurd hr hrk
        left
        refine ⟨fun i hi => ?_, ?_⟩
        · by_cases hik : i.val < k
          · exact hnone i hik
          · have heq : i = ik := by apply Fin.ext; dsimp [ik]; omega
            rw [heq]; exact hnotr
        · rw [hP, conjMat_of_inv Ms ik hinv, mMul_id_left]
    · by_cases hrk : mIsRank1 (Ms ik) = true
      · right
        refine ⟨i1, ik, by omega, by dsimp [ik]; omega, hr1, hrk, hfirst, fun j hj1 hj2 => by dsimp [ik] at hj1; omega, ?_⟩
        rw [hP, conjMat_of_rank1 Ms ik hrk]
        have hcon_mk : ConsecRank1 Ms im ik :=
          ⟨him, hrm, hrk, fun j hj1 hj2 => hlast j hj1 hj2⟩
        by_cases hprev : ∀ a b : Fin n, a.val < k → b.val < k → ConsecRank1 Ms a b →
            vDot (tildeR Ms a) (tildeC Ms b) = true
        · rw [if_pos hprev, outer_mul_outer]
          by_cases hdot : vDot (tildeR Ms im) (tildeC Ms ik) = true
          · rw [if_pos hdot]
            have hall : ∀ a b : Fin n, a.val < k + 1 → b.val < k + 1 → ConsecRank1 Ms a b →
                vDot (tildeR Ms a) (tildeC Ms b) = true := by
              intro a b ha hb hcon
              by_cases hbk : b.val < k
              · exact hprev a b (by have := hcon.1; omega) hbk hcon
              · have hbeq : b = ik := by apply Fin.ext; dsimp [ik]; omega
                have haeq : a = im := by
                  by_contra hne
                  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
                  · have hfa := hcon.2.2.2 im hlt (by rw [hbeq]; exact him)
                    rw [hrm] at hfa; exact Bool.false_ne_true.symm hfa
                  · have hfa := hlast a hgt (by have := hcon.1; rw [hbeq] at this; dsimp [ik] at this; omega)
                    rw [hcon.2.1] at hfa; exact Bool.false_ne_true.symm hfa
                rw [haeq, hbeq]; exact hdot
            rw [if_pos hall]
          · rw [if_neg hdot]
            have hnotall : ¬ (∀ a b : Fin n, a.val < k + 1 → b.val < k + 1 → ConsecRank1 Ms a b →
                vDot (tildeR Ms a) (tildeC Ms b) = true) := by
              intro hall
              exact hdot (hall im ik (by omega) (by dsimp [ik]; omega) hcon_mk)
            rw [if_neg hnotall]
        · rw [if_neg hprev, mMul_zero_left]
          have hnotall : ¬ (∀ a b : Fin n, a.val < k + 1 → b.val < k + 1 → ConsecRank1 Ms a b →
              vDot (tildeR Ms a) (tildeC Ms b) = true) := by
            intro hall; apply hprev
            intro a b ha hb hcon; exact hall a b (by omega) (by omega) hcon
          rw [if_neg hnotall]
      · have hnotr : mIsRank1 (Ms ik) = false := by
          cases h : mIsRank1 (Ms ik) <;> simp [h] at hrk ⊢
        have hinv : mIsInv (Ms ik) = true := by
          rcases trichotomy_mat (Ms ik) with hz | hinv | hr
          · rw [hnoZero ik] at hz; exact absurd hz Bool.false_ne_true
          · exact hinv
          · exact absurd hr hrk
        right
        refine ⟨i1, im, by omega, by omega, hr1, hrm, hfirst, ?_, ?_⟩
        · intro j hj1 hj2
          by_cases hjk : j.val < k
          · exact hlast j hj1 hjk
          · have heq : j = ik := by apply Fin.ext; dsimp [ik]; omega
            rw [heq]; exact hnotr
        · rw [hP, conjMat_of_inv Ms ik hinv, mMul_id_right]
          have hiff : (∀ a b : Fin n, a.val < k → b.val < k → ConsecRank1 Ms a b →
                vDot (tildeR Ms a) (tildeC Ms b) = true) ↔
              (∀ a b : Fin n, a.val < k + 1 → b.val < k + 1 → ConsecRank1 Ms a b →
                vDot (tildeR Ms a) (tildeC Ms b) = true) := by
            constructor
            · intro h a b ha hb hcon
              by_cases hbk : b.val < k
              · exact h a b (by have := hcon.1; omega) hbk hcon
              · have hbeq : b = ik := by apply Fin.ext; dsimp [ik]; omega
                rw [hbeq] at hcon; exact absurd hcon.2.2.1 hrk
            · intro h a b ha hb hcon; exact h a b (by omega) (by omega) hcon
          by_cases hp : ∀ a b : Fin n, a.val < k → b.val < k → ConsecRank1 Ms a b →
              vDot (tildeR Ms a) (tildeC Ms b) = true
          · rw [if_pos hp, if_pos (hiff.mp hp)]
          · rw [if_neg hp, if_neg (fun h => hp (hiff.mpr h))]

def dyadBad {n : ℕ} (Ms : Fin n → Fin 16) : Prop :=
  ∃ m : Fin n, 0 < m.val ∧
    let l := v2 m.val
    let lo := m.val - 2 ^ l
    let hi := min n (m.val + 2 ^ l)
    ∃ (i j : Fin n),
      lo ≤ i.val ∧ i.val < m.val ∧ mIsRank1 (Ms i) = true ∧
      (∀ k : Fin n, i.val < k.val → k.val < m.val → mIsRank1 (Ms k) = false) ∧
      m.val ≤ j.val ∧ j.val < hi ∧ mIsRank1 (Ms j) = true ∧
      (∀ k : Fin n, m.val ≤ k.val → k.val < j.val → mIsRank1 (Ms k) = false) ∧
      vDot (tildeR Ms i) (tildeC Ms j) = false

lemma exists_bad_consec_iff_dyadBad {n : ℕ} (Ms : Fin n → Fin 16) :
    (∃ a b : Fin n, ConsecRank1 Ms a b ∧ vDot (tildeR Ms a) (tildeC Ms b) = false) ↔
      dyadBad Ms := by
  constructor
  · rintro ⟨a, b, hcon, hdot⟩
    have hlt_pow : b.val < 2 ^ (Nat.log2 n + 1) := lt_trans b.isLt (lt_pow2_log2_succ n)
    have hzero : a.val / 2 ^ 0 ≠ b.val / 2 ^ 0 := by
      have := hcon.1; simp only [Nat.pow_zero, Nat.div_one]; omega
    have hex : ∃ l : ℕ, l < Nat.log2 n + 1 ∧ a.val / 2 ^ l ≠ b.val / 2 ^ l ∧
        a.val / 2 ^ (l + 1) = b.val / 2 ^ (l + 1) := by
      have htop : a.val / 2 ^ (Nat.log2 n + 1) = b.val / 2 ^ (Nat.log2 n + 1) := by
        rw [Nat.div_eq_of_lt (lt_trans hcon.1 hlt_pow), Nat.div_eq_of_lt hlt_pow]
      suffices hgen : ∀ L : ℕ, a.val / 2 ^ L = b.val / 2 ^ L →
          ∃ l < L, a.val / 2 ^ l ≠ b.val / 2 ^ l ∧ a.val / 2 ^ (l + 1) = b.val / 2 ^ (l + 1) by
        exact hgen (Nat.log2 n + 1) htop
      intro L
      induction L with
      | zero => intro h; exact absurd h hzero
      | succ L ih =>
        intro hEq
        by_cases hL : a.val / 2 ^ L = b.val / 2 ^ L
        · rcases ih hL with ⟨l, hl, h1, h2⟩
          exact ⟨l, by omega, h1, h2⟩
        · exact ⟨L, Nat.lt_succ_self L, hL, hEq⟩
    rcases hex with ⟨l, _, hne, heq⟩
    set q := a.val / 2 ^ (l + 1)
    have ha_div : a.val / 2 ^ l / 2 = q := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hb_div : b.val / 2 ^ l / 2 = q := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; exact heq.symm
    have hle_div : a.val / 2 ^ l ≤ b.val / 2 ^ l := Nat.div_le_div_right (le_of_lt hcon.1)
    have ha_q : a.val / 2 ^ l = 2 * q := by omega
    have hb_q : b.val / 2 ^ l = 2 * q + 1 := by omega
    have h2p : 0 < 2 ^ l := Nat.two_pow_pos l
    have ha_lo : 2 * q * 2 ^ l ≤ a.val := by
      have := Nat.div_mul_le_self a.val (2 ^ l); rw [ha_q] at this; exact this
    have ha_hi : a.val < (2 * q + 1) * 2 ^ l := by
      have := Nat.lt_mul_div_succ a.val h2p; rw [ha_q, Nat.mul_comm] at this; exact this
    have hb_lo : (2 * q + 1) * 2 ^ l ≤ b.val := by
      have := Nat.div_mul_le_self b.val (2 ^ l); rw [hb_q] at this; exact this
    have hb_hi : b.val < (2 * q + 2) * 2 ^ l := by
      have := Nat.lt_mul_div_succ b.val h2p; rw [hb_q, Nat.mul_comm] at this; exact this
    let mval := (2 * q + 1) * 2 ^ l
    have hm_lt : mval < n := lt_of_le_of_lt hb_lo b.isLt
    have hm_pos : 0 < mval := Nat.mul_pos (by omega) h2p
    refine ⟨⟨mval, hm_lt⟩, hm_pos, ?_⟩
    have hv2 : v2 mval = l := v2_odd_mul_pow2 q l
    dsimp only
    rw [hv2]
    have hlo_eq : mval - 2 ^ l = 2 * q * 2 ^ l := by
      dsimp only [mval]; rw [Nat.add_mul, Nat.one_mul]; omega
    have hhi_eq : mval + 2 ^ l = (2 * q + 2) * 2 ^ l := by
      dsimp only [mval]; rw [Nat.add_mul, Nat.add_mul]; ring
    refine ⟨a, b, ?_, ha_hi, hcon.2.1, ?_, hb_lo, ?_, hcon.2.2.1, ?_, hdot⟩
    · rw [hlo_eq]; exact ha_lo
    · intro k hk1 hk2; exact hcon.2.2.2 k hk1 (lt_of_lt_of_le hk2 hb_lo)
    · rw [hhi_eq]; exact lt_min b.isLt hb_hi
    · intro k hk1 hk2; exact hcon.2.2.2 k (lt_of_lt_of_le ha_hi hk1) hk2
  · rintro ⟨m, _, i, j, _, him, hri, hleft, hmj, _, hrj, hright, hdot⟩
    refine ⟨i, j, ⟨lt_of_lt_of_le him hmj, hri, hrj, ?_⟩, hdot⟩
    intro k hk1 hk2
    by_cases hkm : k.val < m.val
    · exact hleft k hk1 hkm
    · exact hright k (by omega) hk2

open Classical in
lemma main_alg_iff (n : ℕ) (hn : 0 < n) (Ms : Fin n → Fin 16) :
    mTrace (mProd (List.ofFn Ms)) = true ↔
      (∀ i : Fin n, mIsZero (Ms i) = false) ∧
      (((∀ i : Fin n, mIsRank1 (Ms i) = false) ∧
          (!prefSign Ms n && decide ((prefTrans Ms n).val ≠ 0)) = true) ∨
       ((∃ i : Fin n, mIsRank1 (Ms i) = true) ∧
        ¬ dyadBad Ms ∧
        ∃ i1 im : Fin n,
          mIsRank1 (Ms i1) = true ∧ (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
          mIsRank1 (Ms im) = true ∧ (∀ j : Fin n, im.val < j.val → mIsRank1 (Ms j) = false) ∧
          bDot (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im) = true)) := by
  by_cases hzero : ∃ i : Fin n, mIsZero (Ms i) = true
  · rcases hzero with ⟨i0, hi0⟩
    have hm0 : Ms i0 = mZero := (mIsZero_iff _).mp hi0
    have hmem : mZero ∈ List.ofFn Ms := by
      rw [← hm0]; exact List.mem_ofFn.mpr ⟨i0, rfl⟩
    rw [mProd_eq_zero_of_mem hmem, mTrace_zero]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · rintro ⟨hno, _⟩; rw [hno i0] at hi0; exact absurd hi0 Bool.false_ne_true
  · have hnoZero : ∀ i : Fin n, mIsZero (Ms i) = false := by
      intro i; cases h : mIsZero (Ms i)
      · rfl
      · exact absurd ⟨i, h⟩ hzero
    have hprod_eq : mProd (List.ofFn Ms) =
        mMul (mProd ((List.finRange n).map (fun j => conjMat Ms ⟨j.val, j.isLt⟩))) (prefMat Ms n) := by
      rw [list_ofFn_eq_map_finRange]
      exact mProd_take_eq Ms n le_rfl
    rw [hprod_eq]
    rcases mProd_conj_spec Ms hnoZero n le_rfl with ⟨hnone, hP⟩ | ⟨i1, im, _, _, hr1, hrm, hfirst, hlast, hP⟩
    · rw [hP, mMul_id_left]
      have hnone' : ∀ i : Fin n, mIsRank1 (Ms i) = false := fun i => hnone i i.isLt
      unfold prefMat
      rw [trace_gOf]
      constructor
      · intro ht
        exact ⟨hnoZero, Or.inl ⟨hnone', ht⟩⟩
      · rintro ⟨_, ⟨_, ht⟩ | ⟨⟨i0, hi0⟩, _⟩⟩
        · exact ht
        · rw [hnone' i0] at hi0; exact absurd hi0 Bool.false_ne_true
    · rw [hP]
      have hexR1 : ∃ i : Fin n, mIsRank1 (Ms i) = true := ⟨i1, hr1⟩
      have hnotNone : ¬ (∀ i : Fin n, mIsRank1 (Ms i) = false) := by
        intro h; have := h i1; rw [hr1] at this; exact Bool.false_ne_true.symm this
      have huniq1 : ∀ j : Fin n, mIsRank1 (Ms j) = true →
          (∀ r : Fin n, r.val < j.val → mIsRank1 (Ms r) = false) → j = i1 := by
        intro j hrj hfj
        by_contra hne
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
        · have := hfirst j hlt; rw [hrj] at this; exact Bool.false_ne_true.symm this
        · have := hfj i1 hgt; rw [hr1] at this; exact Bool.false_ne_true.symm this
      have huniqm : ∀ j : Fin n, mIsRank1 (Ms j) = true →
          (∀ r : Fin n, j.val < r.val → mIsRank1 (Ms r) = false) → j = im := by
        intro j hrj hlj
        by_contra hne
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
        · have := hlj im hlt; rw [hrm] at this; exact Bool.false_ne_true.symm this
        · have := hlast j hgt j.isLt; rw [hrj] at this; exact Bool.false_ne_true.symm this
      have hall_iff : (∀ a b : Fin n, a.val < n → b.val < n → ConsecRank1 Ms a b →
            vDot (tildeR Ms a) (tildeC Ms b) = true) ↔ ¬ dyadBad Ms := by
        rw [← exists_bad_consec_iff_dyadBad]
        constructor
        · rintro hall ⟨a, b, hcon, hfalse⟩
          have ht := hall a b a.isLt b.isLt hcon
          rw [ht] at hfalse; exact Bool.false_ne_true.symm hfalse
        · intro hno a b _ _ hcon
          cases hv : vDot (tildeR Ms a) (tildeC Ms b)
          · exact absurd ⟨a, b, hcon, hv⟩ hno
          · rfl
      by_cases hnd : ¬ dyadBad Ms
      · rw [if_pos (hall_iff.mpr hnd)]
        constructor
        · intro ht
          refine ⟨hnoZero, Or.inr ⟨hexR1, hnd, i1, im, hr1, hfirst, hrm, fun j hj => hlast j hj j.isLt, ht⟩⟩
        · rintro ⟨_, ⟨hno, _⟩ | ⟨_, _, j1, jm, hrj1, hfj1, hrjm, hljm, hb⟩⟩
          · exact absurd hno hnotNone
          · rw [huniq1 j1 hrj1 hfj1, huniqm jm hrjm hljm] at hb
            exact hb
      · rw [if_neg (fun h => hnd (hall_iff.mp h)), mMul_zero_left, mTrace_zero]
        constructor
        · intro h; exact absurd h Bool.false_ne_true
        · rintro ⟨_, ⟨hno, _⟩ | ⟨_, hnd2, _⟩⟩
          · exact absurd hno hnotNone
          · exact absurd hnd2 hnd

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def evalDepths (n : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
    (List.replicate n 0)

lemma evalWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalWires (gs1 ++ gs2) x = evalWires gs2 (evalWires gs1 x) := by
  unfold evalWires; rw [List.foldl_append]

lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  unfold evalWires
  induction gs generalizing x with
  | nil => simp
  | cons g t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma evalWires_getD_lt (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (evalWires gs x).getD j false = x.getD j false := by
  unfold evalWires
  induction gs generalizing x with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    have hlt : j < (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length := by
      rw [List.length_append]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma evalWires_prefix_agree (pref suff : List Gate) (x : List Bool) (j : ℕ)
    (hj : j < x.length + pref.length) :
    (evalWires (pref ++ suff) x).getD j false = (evalWires pref x).getD j false := by
  rw [evalWires_append]
  apply evalWires_getD_lt
  rw [evalWires_length]; exact hj

lemma evalWires_batch_getD (batch : List Gate) (w : List Bool)
    (hclosed : ∀ g ∈ batch, ∀ j ∈ g.inputs, j < w.length)
    (k : ℕ) (hk : k < batch.length) :
    (evalWires batch w).getD (w.length + k) false =
      (batch[k]).op.eval ((batch[k]).inputs.map (fun j => w.getD j false)) := by
  induction batch generalizing w k with
  | nil => simp at hk
  | cons g t ih =>
    unfold evalWires
    rw [List.foldl_cons]
    set w1 := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hw1_len : w1.length = w.length + 1 := by simp [w1]
    cases k with
    | zero =>
      have hlt : w.length < w1.length := by omega
      have h1 := evalWires_getD_lt t w1 w.length hlt
      simpa [evalWires, w1, List.getD_eq_getElem?_getD] using h1
    | succ k' =>
      have hk' : k' < t.length := by simp at hk; omega
      have hclosed_t : ∀ g' ∈ t, ∀ j ∈ g'.inputs, j < w1.length := fun g' hg' j hj => by
        have := hclosed g' (List.mem_cons_of_mem g hg') j hj; omega
      have hrec := ih w1 hclosed_t k' hk'
      rw [hw1_len, Nat.add_assoc, Nat.add_comm 1 k'] at hrec
      change (evalWires t w1).getD (w.length + (k' + 1)) false = _
      rw [hrec]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjlt : j < w.length := hclosed t[k'] (List.mem_cons_of_mem g (List.getElem_mem hk')) j hj
      simp only [w1, List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]

lemma evalWires_append_batch_getD (prev batch : List Gate) (x : List Bool)
    (hclosed : ∀ g ∈ batch, ∀ j ∈ g.inputs, j < x.length + prev.length)
    (k : ℕ) (hk : k < batch.length) :
    (evalWires (prev ++ batch) x).getD (x.length + prev.length + k) false =
      (batch[k]).op.eval ((batch[k]).inputs.map (fun j => (evalWires prev x).getD j false)) := by
  rw [evalWires_append]
  have hlen : (evalWires prev x).length = x.length + prev.length := evalWires_length prev x
  rw [← hlen]
  exact evalWires_batch_getD batch (evalWires prev x) (by rwa [hlen]) k hk

lemma evalWires_agree_in_full (full pref suff : List Gate) (x : List Bool) (off w : ℕ)
    (hgs : full = pref ++ suff) (hoff : x.length + pref.length = off) (hw : w < off) :
    (evalWires full x).getD w false = (evalWires pref x).getD w false := by
  rw [hgs]
  exact evalWires_prefix_agree pref suff x w (by omega)

lemma evalWires_batch_in_full (full prev batch : List Gate) (x : List Bool) (off k : ℕ)
    (hk : k < batch.length) (hsp : ∃ suff, full = (prev ++ batch) ++ suff)
    (hoff : x.length + prev.length = off)
    (hcl : ∀ g ∈ batch, ∀ j ∈ g.inputs, j < off) :
    (evalWires full x).getD (off + k) false =
      (batch[k]).op.eval ((batch[k]).inputs.map (fun j => (evalWires full x).getD j false)) := by
  rcases hsp with ⟨suff, hgs⟩
  have hlt1 : off + k < x.length + (prev ++ batch).length := by rw [List.length_append]; omega
  rw [evalWires_agree_in_full full (prev ++ batch) suff x (x.length + (prev ++ batch).length) (off + k) hgs rfl hlt1]
  rw [← hoff]
  rw [evalWires_append_batch_getD prev batch x (by rwa [hoff]) k hk]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjlt : j < off := hcl batch[k] (List.getElem_mem hk) j hj
  have hgs2 : full = prev ++ (batch ++ suff) := by rw [hgs, List.append_assoc]
  exact (evalWires_agree_in_full full prev (batch ++ suff) x off j hgs2 hoff hjlt).symm

lemma evalDepths_length_aux (gs : List Gate) (d : List ℕ) :
    (gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]) d).length =
      d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp
  | cons g t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]; omega

lemma evalDepths_length (n : ℕ) (gs : List Gate) :
    (evalDepths n gs).length = n + gs.length := by
  unfold evalDepths
  rw [evalDepths_length_aux, List.length_replicate]

lemma evalDepths_append (n : ℕ) (gs1 gs2 : List Gate) :
    evalDepths n (gs1 ++ gs2) =
      gs2.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
        (evalDepths n gs1) := by
  unfold evalDepths; rw [List.foldl_append]

lemma foldr_max_le (l : List ℕ) (D : ℕ) (h : ∀ x ∈ l, x ≤ D) : l.foldr max 0 ≤ D := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

lemma evalDepths_batch_le (n D : ℕ) (prev batch : List Gate)
    (hD : ∀ j < n + prev.length, (evalDepths n prev).getD j 0 ≤ D)
    (hclosed : ∀ g ∈ batch, ∀ j ∈ g.inputs, j < n + prev.length) :
    ∀ j < n + (prev ++ batch).length, (evalDepths n (prev ++ batch)).getD j 0 ≤ D + 1 := by
  rw [evalDepths_append, List.length_append]
  set d0 := evalDepths n prev
  have hd0_len : d0.length = n + prev.length := evalDepths_length n prev
  suffices hgen : ∀ (bs : List Gate) (d : List ℕ),
      d0.length ≤ d.length →
      (∀ j < d0.length, d.getD j 0 ≤ D) →
      (∀ j < d.length, d.getD j 0 ≤ D + 1) →
      (∀ g ∈ bs, ∀ j ∈ g.inputs, j < d0.length) →
      ∀ j < d.length + bs.length,
        (bs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]) d).getD j 0 ≤ D + 1 by
    have := hgen batch d0 le_rfl (by rwa [hd0_len])
      (fun j hj => Nat.le_succ_of_le (hD j (by rwa [← hd0_len])))
      (by rwa [hd0_len])
    simpa [hd0_len, Nat.add_assoc] using this
  intro bs
  induction bs with
  | nil =>
    intro d _ _ hall _ j hj
    exact hall j (by simpa using hj)
  | cons g t ih =>
    intro d hle hbase hall hcl j hj
    simp only [List.foldl_cons]
    set v := (g.inputs.map fun i => d.getD i 0).foldr max 0 + 1
    have hv : v ≤ D + 1 := by
      apply Nat.add_le_add_right
      apply foldr_max_le
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact hbase i (hcl g (List.mem_cons_self ..) i hi)
    have hlen1 : (d ++ [v]).length = d.length + 1 := by simp
    apply ih (d ++ [v]) (by omega)
    · intro i hi
      have hilt : i < d.length := lt_of_lt_of_le hi hle
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt] using hbase i hi
    · intro i hi
      by_cases hilt : i < d.length
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt] using hall i hilt
      · have heq : i = d.length := by rw [hlen1] at hi; omega
        subst heq
        simpa [List.getD_eq_getElem?_getD] using hv
    · exact fun g' hg' => hcl g' (List.mem_cons_of_mem g hg')
    · rw [hlen1]; simp only [List.length_cons] at hj; omega

lemma readsBack_append_batch (n : ℕ) (prev batch : List Gate)
    (hrb : ReadsBack n ⟨prev, 0⟩)
    (hclosed : ∀ g ∈ batch, ∀ j ∈ g.inputs, j < n + prev.length) :
    ReadsBack n ⟨prev ++ batch, 0⟩ := by
  intro j hj i hi
  simp only [gateAt, List.getD_eq_getElem?_getD] at hi
  by_cases hjp : j < prev.length
  · rw [List.getElem?_append_left hjp] at hi
    exact hrb j hjp i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (by omega)] at hi
    have hjb : j - prev.length < batch.length := by simp at hj; omega
    rw [List.getElem?_eq_getElem hjb] at hi
    simp only [Option.getD_some] at hi
    have hlt := hclosed batch[j - prev.length] (List.getElem_mem hjb) i hi
    omega

lemma map_len_append (l1 l2 : List Gate) :
    ((l1 ++ l2).map (fun g => g.inputs.length)).sum =
      (l1.map (fun g => g.inputs.length)).sum + (l2.map (fun g => g.inputs.length)).sum := by
  rw [List.map_append, List.sum_append]

lemma sum_le_mul_of_le (l : List ℕ) (M : ℕ) (h : ∀ x ∈ l, x ≤ M) : l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

lemma gateOp_and_iff (l : List Bool) : GateOp.and.eval l = true ↔ ∀ b ∈ l, b = true := by
  simp [GateOp.eval]

lemma gateOp_or_iff (l : List Bool) : GateOp.or.eval l = true ↔ ∃ b ∈ l, b = true := by
  simp [GateOp.eval]

lemma gateOp_not_singleton (b : Bool) : GateOp.not.eval [b] = !b := rfl

lemma gateOp_mod6_iff (l : List Bool) : (GateOp.mod 6).eval l = true ↔ l.count true % 6 = 0 := by
  simp [GateOp.eval]

lemma count_flatMap_triple (l : List Bool) :
    (l.flatMap (fun b => [b, b, b])).count true = 3 * l.count true := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.count_append, ih]
    cases a <;> simp <;> omega

lemma count_flatMap_quad (l : List (Bool × Bool)) :
    (l.flatMap (fun p => [p.1, p.1, p.2, p.2])).count true =
      2 * (l.map (fun p => (if p.1 then 1 else 0) + (if p.2 then 1 else 0))).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.flatMap_cons, List.count_append, List.map_cons, List.sum_cons, ih]
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> simp <;> omega

lemma signedU_split {n : ℕ} (Ms : Fin n → Fin 16) (j : Fin n) :
    signedU Ms j =
      (if decide ((gTrans (Ms j)).val ≠ 0) then 1 else 0) +
      (if ((!prefSign Ms j.val && decide ((gTrans (Ms j)).val = 2)) ||
           (prefSign Ms j.val && decide ((gTrans (Ms j)).val = 1))) then 1 else 0) := by
  unfold signedU
  have ht := (gTrans (Ms j)).isLt
  cases hs : prefSign Ms j.val <;>
  (rcases (show (gTrans (Ms j)).val = 0 ∨ (gTrans (Ms j)).val = 1 ∨ (gTrans (Ms j)).val = 2 by omega) with h | h | h <;>
   simp [h])

def ordinaryGate (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

def allMatTuples : List (Bool × Fin 3 × Fin 3) :=
  [false, true].flatMap (fun s =>
    (List.finRange 3).flatMap (fun t =>
      (List.finRange 3).map (fun v => (s, t, v))))

def allBdotTuples : List (Bool × Fin 3 × Fin 3 × Fin 3) :=
  ([false, true].flatMap (fun s =>
    (List.finRange 3).flatMap (fun t =>
      (List.finRange 3).flatMap (fun c =>
        (List.finRange 3).map (fun r => (s, t, c, r)))))).filter
    (fun q => bDot q.1 q.2.1 q.2.2.1 q.2.2.2)

lemma allMatTuples_length : allMatTuples.length = 18 := by decide
lemma mem_allMatTuples (s : Bool) (t v : Fin 3) : (s, t, v) ∈ allMatTuples := by
  revert s t v; decide

lemma allBdotTuples_length_le : allBdotTuples.length ≤ 54 := by decide
lemma mem_allBdotTuples_iff (s : Bool) (t c r : Fin 3) :
    (s, t, c, r) ∈ allBdotTuples ↔ bDot s t c r = true := by
  revert s t c r; decide

def tupIdx (s : Bool) (t v : Fin 3) : ℕ :=
  (if s then 9 else 0) + t.val * 3 + v.val

lemma div_lt_of_lt_mul_r {a b c : ℕ} (h : a < b * c) : a / c < b :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)

lemma tupIdx_lt (s : Bool) (t v : Fin 3) : tupIdx s t v < 18 := by
  cases s <;> (have := t.isLt; have := v.isLt; unfold tupIdx; simp; omega)

def stIdx (s : Bool) (t : Fin 3) : ℕ :=
  (if s then 3 else 0) + t.val

lemma stIdx_lt (s : Bool) (t : Fin 3) : stIdx s t < 6 := by
  cases s <;> (have := t.isLt; unfold stIdx; simp; omega)

lemma stIdx_s (s : Bool) (t : Fin 3) : decide (3 ≤ stIdx s t) = s := by
  revert s t; decide
lemma stIdx_t (s : Bool) (t : Fin 3) : (⟨stIdx s t % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = t := by
  revert s t; decide
lemma tupIdx_s (s : Bool) (t v : Fin 3) : decide (9 ≤ tupIdx s t v) = s := by
  revert s t v; decide
lemma tupIdx_t (s : Bool) (t v : Fin 3) : (⟨(tupIdx s t v % 9) / 3, by have := Nat.mod_lt (tupIdx s t v) (by decide : 0 < 9); omega⟩ : Fin 3) = t := by
  apply Fin.ext; revert s t v; decide
lemma tupIdx_v (s : Bool) (t v : Fin 3) : (⟨tupIdx s t v % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = v := by
  revert s t v; decide

section CircuitConst

variable (n : ℕ) (hn : 0 < n)

def I_w : ℕ := 4 * n
def Lmax : ℕ := Nat.log2 n + 1

def batchA0 : List Gate :=
  List.ofFn (fun k : Fin (I_w n) => ⟨.not, [k.val]⟩) ++ [⟨.and, []⟩, ⟨.or, []⟩]

def offA0 : ℕ := I_w n
def wNotIn (k : ℕ) : ℕ := offA0 n + k
def wTrue : ℕ := offA0 n + I_w n
def wFalse : ℕ := offA0 n + (I_w n + 1)

def offA1 : ℕ := offA0 n + (batchA0 n).length

def matMintermGate (i : Fin n) (m : Fin 16) : Gate :=
  ⟨.and, (List.finRange 4).map (fun r =>
    if m.val.testBit r.val then 4 * i.val + r.val else wNotIn n (4 * i.val + r.val))⟩

def batchA1 : List Gate :=
  List.ofFn (fun p : Fin (n * 16) =>
    matMintermGate n ⟨p.val / 16, div_lt_of_lt_mul_r p.isLt⟩
      ⟨p.val % 16, Nat.mod_lt _ (by decide)⟩)

def wEqMat (i : Fin n) (m : Fin 16) : ℕ := offA1 n + (i.val * 16 + m.val)

def offA2 : ℕ := offA1 n + (batchA1 n).length

def matPropGate (i : Fin n) (pred : Fin 16 → Bool) : Gate :=
  ⟨.or, ((List.finRange 16).filter pred).map (fun m => wEqMat n i m)⟩

def a2Pred (slot : Fin 12) (m : Fin 16) : Bool :=
  match slot.val with
  | 0 => mIsZero m
  | 1 => mIsRank1 m
  | 2 => gSign m
  | 3 => decide ((gTrans m).val = 1)
  | 4 => decide ((gTrans m).val = 2)
  | 5 => decide ((gTrans m).val ≠ 0)
  | 6 => decide ((mCol m).val = 0)
  | 7 => decide ((mCol m).val = 1)
  | 8 => decide ((mCol m).val = 2)
  | 9 => decide ((mRow m).val = 0)
  | 10 => decide ((mRow m).val = 1)
  | _ => decide ((mRow m).val = 2)

def batchA2 : List Gate :=
  List.ofFn (fun p : Fin (n * 12) =>
    matPropGate n ⟨p.val / 12, div_lt_of_lt_mul_r p.isLt⟩
      (a2Pred ⟨p.val % 12, Nat.mod_lt _ (by decide)⟩))

def wA2 (i : Fin n) (slot : ℕ) : ℕ := offA2 n + (i.val * 12 + slot)
def wIsZero (i : Fin n) : ℕ := wA2 n i 0
def wIsRank1 (i : Fin n) : ℕ := wA2 n i 1
def wOddSign (i : Fin n) : ℕ := wA2 n i 2
def wTrans1 (i : Fin n) : ℕ := wA2 n i 3
def wTrans2 (i : Fin n) : ℕ := wA2 n i 4
def wTransNZ (i : Fin n) : ℕ := wA2 n i 5
def wColVec (i : Fin n) (v : Fin 3) : ℕ := wA2 n i (6 + v.val)
def wRowVec (i : Fin n) (v : Fin 3) : ℕ := wA2 n i (9 + v.val)

def offA3 : ℕ := offA2 n + (batchA2 n).length

def batchA3 : List Gate :=
  List.ofFn (fun i : Fin n => ⟨.not, [wIsRank1 n i]⟩) ++
  [⟨.or, List.ofFn (fun i : Fin n => wIsZero n i)⟩,
   ⟨.or, List.ofFn (fun i : Fin n => wIsRank1 n i)⟩]

def wNotRank1 (i : Fin n) : ℕ := offA3 n + i.val
def wHasZero : ℕ := offA3 n + n
def wHasRank1 : ℕ := offA3 n + (n + 1)

def secA : List Gate := batchA0 n ++ batchA1 n ++ batchA2 n ++ batchA3 n

def offS : ℕ := offA3 n + (batchA3 n).length

def secS : List Gate :=
  List.ofFn (fun i : Fin n =>
    ⟨.mod 6, (List.finRange (i.val + 1)).flatMap (fun j =>
      let w := wOddSign n ⟨j.val, by omega⟩
      [w, w, w])⟩)

def wSignEven (p : ℕ) : ℕ :=
  if p = 0 then wTrue n else offS n + (p - 1)

def offB0 : ℕ := offS n + (secS n).length

def batchB0 : List Gate :=
  List.ofFn (fun i : Fin n => ⟨.not, [wSignEven n (i.val + 1)]⟩)

def wSignOdd (p : ℕ) : ℕ :=
  if p = 0 then wFalse n else offB0 n + (p - 1)

def offB1 : ℕ := offB0 n + (batchB0 n).length

def batchB1 : List Gate :=
  List.ofFn (fun p : Fin (n * 2) =>
    let j : Fin n := ⟨p.val / 2, div_lt_of_lt_mul_r p.isLt⟩
    if p.val % 2 = 0 then ⟨.and, [wSignEven n j.val, wTrans2 n j]⟩
    else ⟨.and, [wSignOdd n j.val, wTrans1 n j]⟩)

def wBPos (j : Fin n) : ℕ := offB1 n + (j.val * 2)
def wBNeg (j : Fin n) : ℕ := offB1 n + (j.val * 2 + 1)

def offB2 : ℕ := offB1 n + (batchB1 n).length

def batchB2 : List Gate :=
  List.ofFn (fun j : Fin n => ⟨.or, [wBPos n j, wBNeg n j]⟩)

def wB (j : Fin n) : ℕ := offB2 n + j.val

def secB : List Gate := batchB0 n ++ batchB1 n ++ batchB2 n

def offR : ℕ := offB2 n + (batchB2 n).length

def rBaseInputs (i : Fin n) : List ℕ :=
  (List.finRange (i.val + 1)).flatMap (fun j =>
    let jf : Fin n := ⟨j.val, by omega⟩
    [wTransNZ n jf, wTransNZ n jf, wB n jf, wB n jf])

def secR : List Gate :=
  List.ofFn (fun p : Fin (n * 2) =>
    let i : Fin n := ⟨p.val / 2, div_lt_of_lt_mul_r p.isLt⟩
    if p.val % 2 = 0 then ⟨.mod 6, rBaseInputs n i⟩
    else ⟨.mod 6, rBaseInputs n i ++ [wTrue n, wTrue n, wTrue n, wTrue n]⟩)

def wTr0 (p : ℕ) : ℕ :=
  if p = 0 then wTrue n else offR n + ((p - 1) * 2)

def wTr1 (p : ℕ) : ℕ :=
  if p = 0 then wFalse n else offR n + ((p - 1) * 2 + 1)

def offD0 : ℕ := offR n + (secR n).length

def dyadMaskGate (l : Fin (Lmax n)) (i : Fin n) : Gate :=
  let lo := (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1)
  let mid := lo + 2 ^ l.val
  if i.val < mid then
    ⟨.and, wIsRank1 n i ::
      (List.finRange (min n mid - (i.val + 1))).map (fun t =>
        wNotRank1 n ⟨i.val + 1 + t.val, by omega⟩)⟩
  else
    ⟨.and, wIsRank1 n i ::
      (List.finRange (i.val - mid)).map (fun t =>
        wNotRank1 n ⟨mid + t.val, by omega⟩)⟩

def batchD0 : List Gate :=
  List.ofFn (fun p : Fin (n * 2) =>
    let i := p.val / 2
    if p.val % 2 = 0 then ⟨.not, [wTr0 n (i + 1)]⟩
    else ⟨.not, [wTr1 n (i + 1)]⟩) ++
  [⟨.not, [wHasZero n]⟩, ⟨.not, [wHasRank1 n]⟩] ++
  List.ofFn (fun i : Fin n =>
    ⟨.and, wIsRank1 n i :: (List.finRange i.val).map (fun k => wNotRank1 n ⟨k.val, by omega⟩)⟩) ++
  List.ofFn (fun i : Fin n =>
    ⟨.and, wIsRank1 n i ::
      (List.finRange (n - (i.val + 1))).map (fun t => wNotRank1 n ⟨i.val + 1 + t.val, by omega⟩)⟩) ++
  List.ofFn (fun p : Fin (Lmax n * n) =>
    let l : Fin (Lmax n) := ⟨p.val / n, div_lt_of_lt_mul_r p.isLt⟩
    let i : Fin n := ⟨p.val % n, Nat.mod_lt _ hn⟩
    dyadMaskGate n l i)

def wNotTr0 (p : ℕ) : ℕ := offD0 n + ((p - 1) * 2)
def wNotTr1 (p : ℕ) : ℕ := offD0 n + ((p - 1) * 2 + 1)
def wNotHasZero : ℕ := offD0 n + n * 2
def wNotHasRank1 : ℕ := offD0 n + (n * 2 + 1)
def wIsFirstGlobal (i : Fin n) : ℕ := offD0 n + (n * 2 + 2 + i.val)
def wIsLastGlobal (i : Fin n) : ℕ := offD0 n + (n * 2 + 2 + n + i.val)
def wDyadMask (l : Fin (Lmax n)) (i : Fin n) : ℕ :=
  offD0 n + (n * 2 + 2 + n + n + (l.val * n + i.val))

def offD1 : ℕ := offD0 n + (batchD0 n hn).length

def batchD1 : List Gate :=
  List.ofFn (fun i : Fin n => ⟨.and, [wNotTr0 n (i.val + 1), wNotTr1 n (i.val + 1)]⟩)

def wTr2 (p : ℕ) : ℕ :=
  if p = 0 then wFalse n else offD1 n hn + (p - 1)

def wSignEq (p : ℕ) (s : Bool) : ℕ :=
  if s then wSignOdd n p else wSignEven n p

def wTrEq (p : ℕ) (t : Fin 3) : ℕ :=
  match t.val with
  | 0 => wTr0 n p
  | 1 => wTr1 n p
  | _ => wTr2 n hn p

def offD2 : ℕ := offD1 n hn + (batchD1 n).length

def batchD2 : List Gate :=
  List.ofFn (fun q : Fin ((n + 1) * 6) =>
    let p := q.val / 6
    let r := q.val % 6
    let s := decide (3 ≤ r)
    let t : Fin 3 := ⟨r % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.and, [wSignEq n p s, wTrEq n hn p t]⟩)

def wPEq (p : ℕ) (s : Bool) (t : Fin 3) : ℕ :=
  offD2 n hn + (p * 6 + stIdx s t)

def offD3 : ℕ := offD2 n hn + (batchD2 n hn).length

def batchD3 : List Gate :=
  List.ofFn (fun q : Fin (n * 18) =>
    let i : Fin n := ⟨q.val / 18, div_lt_of_lt_mul_r q.isLt⟩
    let r := q.val % 18
    let s := decide (9 ≤ r)
    let t : Fin 3 := ⟨(r % 9) / 3, by omega⟩
    let c : Fin 3 := ⟨r % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.and, [wPEq n hn i.val s t, wColVec n i c]⟩) ++
  List.ofFn (fun q : Fin (n * 18) =>
    let i : Fin n := ⟨q.val / 18, div_lt_of_lt_mul_r q.isLt⟩
    let r := q.val % 18
    let s := decide (9 ≤ r)
    let t : Fin 3 := ⟨(r % 9) / 3, by omega⟩
    let v : Fin 3 := ⟨r % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.and, [wPEq n hn i.val s t, wRowVec n i v]⟩)

def wPC (i : Fin n) (s : Bool) (t c : Fin 3) : ℕ :=
  offD3 n hn + (i.val * 18 + tupIdx s t c)

def wPR (i : Fin n) (s : Bool) (t r : Fin 3) : ℕ :=
  offD3 n hn + (n * 18 + (i.val * 18 + tupIdx s t r))

def offD4 : ℕ := offD3 n hn + (batchD3 n hn).length

def batchD4 : List Gate :=
  List.ofFn (fun q : Fin (n * 3) =>
    let i : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
    let v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.or, (allMatTuples.filter (fun x => decide (gActC x.1 x.2.1 x.2.2 = v))).map
      (fun x => wPC n hn i x.1 x.2.1 x.2.2)⟩) ++
  List.ofFn (fun q : Fin (n * 3) =>
    let i : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
    let v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.or, (allMatTuples.filter (fun x => decide (gActR x.1 x.2.1 x.2.2 = v))).map
      (fun x => wPR n hn i x.1 x.2.1 x.2.2)⟩)

def wTildeC (i : Fin n) (v : Fin 3) : ℕ := offD4 n hn + (i.val * 3 + v.val)
def wTildeR (i : Fin n) (v : Fin 3) : ℕ := offD4 n hn + (n * 3 + (i.val * 3 + v.val))

def offD5 : ℕ := offD4 n hn + (batchD4 n hn).length

def batchD5 : List Gate :=
  List.ofFn (fun q : Fin (n * 3) =>
    let i : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
    let v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.and, [wIsFirstGlobal n i, wTildeC n hn i v]⟩) ++
  List.ofFn (fun q : Fin (n * 3) =>
    let i : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
    let v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
    ⟨.and, [wIsLastGlobal n i, wTildeR n hn i v]⟩) ++
  List.ofFn (fun q : Fin (Lmax n * n * 3) =>
    let li := q.val / 3
    let v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
    let l : Fin (Lmax n) := ⟨li / n, div_lt_of_lt_mul_r (div_lt_of_lt_mul_r q.isLt)⟩
    let i : Fin n := ⟨li % n, Nat.mod_lt _ hn⟩
    let lo := (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1)
    let mid := lo + 2 ^ l.val
    if i.val < mid then ⟨.and, [wDyadMask n l i, wTildeR n hn i v]⟩
    else ⟨.and, [wDyadMask n l i, wTildeC n hn i v]⟩)

def wFirstCTag (i : Fin n) (v : Fin 3) : ℕ := offD5 n hn + (i.val * 3 + v.val)
def wLastRTag (i : Fin n) (v : Fin 3) : ℕ := offD5 n hn + (n * 3 + (i.val * 3 + v.val))
def wDyadTag (l : Fin (Lmax n)) (i : Fin n) (v : Fin 3) : ℕ :=
  offD5 n hn + (n * 3 + n * 3 + ((l.val * n + i.val) * 3 + v.val))

def offD6 : ℕ := offD5 n hn + (batchD5 n hn).length

def leftVecGate (m : Fin n) (v : Fin 3) : Gate :=
  if hm : 0 < m.val then
    let l : Fin (Lmax n) := ⟨v2 m.val, v2_lt_log2_succ n m.val hm m.isLt⟩
    let lo := m.val - 2 ^ l.val
    ⟨.or, (List.finRange (m.val - lo)).map (fun t =>
      wDyadTag n hn l ⟨lo + t.val, by omega⟩ v)⟩
  else ⟨.or, []⟩

def rightVecGate (m : Fin n) (v : Fin 3) : Gate :=
  if hm : 0 < m.val then
    let l : Fin (Lmax n) := ⟨v2 m.val, v2_lt_log2_succ n m.val hm m.isLt⟩
    let hi := min n (m.val + 2 ^ l.val)
    ⟨.or, (List.finRange (hi - m.val)).map (fun t =>
      wDyadTag n hn l ⟨m.val + t.val, by omega⟩ v)⟩
  else ⟨.or, []⟩

def batchD6 : List Gate :=
  List.ofFn (fun v : Fin 3 => ⟨.or, List.ofFn (fun i : Fin n => wFirstCTag n hn i v)⟩) ++
  List.ofFn (fun v : Fin 3 => ⟨.or, List.ofFn (fun i : Fin n => wLastRTag n hn i v)⟩) ++
  List.ofFn (fun q : Fin (n * 3) =>
    leftVecGate n hn ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
      ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩) ++
  List.ofFn (fun q : Fin (n * 3) =>
    rightVecGate n hn ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
      ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩)

def wFirstC (v : Fin 3) : ℕ := offD6 n hn + v.val
def wLastR (v : Fin 3) : ℕ := offD6 n hn + (3 + v.val)
def wLeftVec (m : Fin n) (v : Fin 3) : ℕ := offD6 n hn + (6 + (m.val * 3 + v.val))
def wRightVec (m : Fin n) (v : Fin 3) : ℕ := offD6 n hn + (6 + n * 3 + (m.val * 3 + v.val))

def offD7 : ℕ := offD6 n hn + (batchD6 n hn).length

def batchD7 : List Gate :=
  List.ofFn (fun q : Fin (n * 3) =>
    let m : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
    match q.val % 3 with
    | 0 => ⟨.and, [wLeftVec n hn m ⟨0, by decide⟩, wRightVec n hn m ⟨1, by decide⟩]⟩
    | 1 => ⟨.and, [wLeftVec n hn m ⟨1, by decide⟩, wRightVec n hn m ⟨0, by decide⟩]⟩
    | _ => ⟨.and, [wLeftVec n hn m ⟨2, by decide⟩, wRightVec n hn m ⟨2, by decide⟩]⟩) ++
  allBdotTuples.map (fun q =>
    ⟨.and, [wPEq n hn n q.1 q.2.1, wFirstC n hn q.2.2.1, wLastR n hn q.2.2.2]⟩) ++
  [⟨.or, [wPEq n hn n false ⟨1, by decide⟩, wPEq n hn n false ⟨2, by decide⟩]⟩]

def wBadTriple (m : Fin n) (k : Fin 3) : ℕ := offD7 n hn + (m.val * 3 + k.val)
def wBdotTerm (idx : ℕ) : ℕ := offD7 n hn + (n * 3 + idx)
def wTracePn : ℕ := offD7 n hn + (n * 3 + allBdotTuples.length)

def offD8 : ℕ := offD7 n hn + (batchD7 n hn).length

def batchD8 : List Gate :=
  [⟨.or, List.ofFn (fun q : Fin (n * 3) => offD7 n hn + q.val)⟩,
   ⟨.or, List.ofFn (fun q : Fin allBdotTuples.length => wBdotTerm n hn q.val)⟩,
   ⟨.and, [wNotHasRank1 n, wTracePn n hn]⟩]

def wAnyBadPair : ℕ := offD8 n hn
def wBoundaryDot1 : ℕ := offD8 n hn + 1
def wCase1 : ℕ := offD8 n hn + 2

def offD9 : ℕ := offD8 n hn + (batchD8 n hn).length

def batchD9 : List Gate := [⟨.not, [wAnyBadPair n hn]⟩]
def wNoBadPair : ℕ := offD9 n hn

def offD10 : ℕ := offD9 n hn + (batchD9 n hn).length

def batchD10 : List Gate := [⟨.and, [wHasRank1 n, wNoBadPair n hn, wBoundaryDot1 n hn]⟩]
def wCase2 : ℕ := offD10 n hn

def offD11 : ℕ := offD10 n hn + (batchD10 n hn).length

def batchD11 : List Gate := [⟨.or, [wCase1 n hn, wCase2 n hn]⟩]
def wEither : ℕ := offD11 n hn

def offD12 : ℕ := offD11 n hn + (batchD11 n hn).length

def batchD12 : List Gate := [⟨.and, [wNotHasZero n, wEither n hn]⟩]
def wOut : ℕ := offD12 n hn

def secD : List Gate :=
  batchD0 n hn ++ batchD1 n ++ batchD2 n hn ++ batchD3 n hn ++ batchD4 n hn ++
  batchD5 n hn ++ batchD6 n hn ++ batchD7 n hn ++ batchD8 n hn ++
  batchD9 n hn ++ batchD10 n hn ++ batchD11 n hn ++ batchD12 n hn

def fullGates : List Gate :=
  secA n ++ secS n ++ secB n ++ secR n ++ secD n hn

def buildCircuit : Circuit :=
  ⟨fullGates n hn, wOut n hn⟩

lemma len_batchA0 : (batchA0 n).length = 4 * n + 2 := by simp [batchA0, I_w]
lemma len_batchA1 : (batchA1 n).length = n * 16 := by simp [batchA1]
lemma len_batchA2 : (batchA2 n).length = n * 12 := by simp [batchA2]
lemma len_batchA3 : (batchA3 n).length = n + 2 := by simp [batchA3]
lemma len_secS : (secS n).length = n := by simp [secS]
lemma len_batchB0 : (batchB0 n).length = n := by simp [batchB0]
lemma len_batchB1 : (batchB1 n).length = n * 2 := by simp [batchB1]
lemma len_batchB2 : (batchB2 n).length = n := by simp [batchB2]
lemma len_secR : (secR n).length = n * 2 := by simp [secR]
lemma len_batchD0 : (batchD0 n hn).length = n * 2 + 2 + n + n + Lmax n * n := by
  simp [batchD0]; omega
lemma len_batchD1 : (batchD1 n).length = n := by simp [batchD1]
lemma len_batchD2 : (batchD2 n hn).length = (n + 1) * 6 := by simp [batchD2]; ring
lemma len_batchD3 : (batchD3 n hn).length = n * 18 + n * 18 := by simp [batchD3]
lemma len_batchD4 : (batchD4 n hn).length = n * 3 + n * 3 := by simp [batchD4]
lemma len_batchD5 : (batchD5 n hn).length = n * 3 + n * 3 + Lmax n * n * 3 := by
  simp [batchD5]; omega
lemma len_batchD6 : (batchD6 n hn).length = 3 + 3 + n * 3 + n * 3 := by
  simp [batchD6]; omega
lemma len_batchD7 : (batchD7 n hn).length = n * 3 + allBdotTuples.length + 1 := by
  simp [batchD7]; omega
lemma len_batchD8 : (batchD8 n hn).length = 3 := by simp [batchD8]
lemma len_batchD9 : (batchD9 n hn).length = 1 := by simp [batchD9]
lemma len_batchD10 : (batchD10 n hn).length = 1 := by simp [batchD10]
lemma len_batchD11 : (batchD11 n hn).length = 1 := by simp [batchD11]
lemma len_batchD12 : (batchD12 n hn).length = 1 := by simp [batchD12]

lemma off_order :
    I_w n = offA0 n ∧
    offA0 n + (batchA0 n).length = offA1 n ∧
    offA1 n + (batchA1 n).length = offA2 n ∧
    offA2 n + (batchA2 n).length = offA3 n ∧
    offA3 n + (batchA3 n).length = offS n ∧
    offS n + (secS n).length = offB0 n ∧
    offB0 n + (batchB0 n).length = offB1 n ∧
    offB1 n + (batchB1 n).length = offB2 n ∧
    offB2 n + (batchB2 n).length = offR n ∧
    offR n + (secR n).length = offD0 n ∧
    offD0 n + (batchD0 n hn).length = offD1 n hn ∧
    offD1 n hn + (batchD1 n).length = offD2 n hn ∧
    offD2 n hn + (batchD2 n hn).length = offD3 n hn ∧
    offD3 n hn + (batchD3 n hn).length = offD4 n hn ∧
    offD4 n hn + (batchD4 n hn).length = offD5 n hn ∧
    offD5 n hn + (batchD5 n hn).length = offD6 n hn ∧
    offD6 n hn + (batchD6 n hn).length = offD7 n hn ∧
    offD7 n hn + (batchD7 n hn).length = offD8 n hn ∧
    offD8 n hn + (batchD8 n hn).length = offD9 n hn ∧
    offD9 n hn + (batchD9 n hn).length = offD10 n hn ∧
    offD10 n hn + (batchD10 n hn).length = offD11 n hn ∧
    offD11 n hn + (batchD11 n hn).length = offD12 n hn := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma wTrue_lt_offA1 : wTrue n < offA1 n := by
  unfold wTrue offA1; rw [len_batchA0]; unfold I_w; omega
lemma wFalse_lt_offA1 : wFalse n < offA1 n := by
  unfold wFalse offA1; rw [len_batchA0]; unfold I_w; omega
lemma wNotIn_lt_offA1 (k : ℕ) (hk : k < I_w n) : wNotIn n k < offA1 n := by
  unfold wNotIn offA1; rw [len_batchA0]; unfold I_w at *; omega
lemma wEqMat_lt_offA2 (i : Fin n) (m : Fin 16) : wEqMat n i m < offA2 n := by
  unfold wEqMat offA2; rw [len_batchA1]; have := i.isLt; have := m.isLt; omega
lemma wA2_lt_offA3 (i : Fin n) (s : ℕ) (hs : s < 12) : wA2 n i s < offA3 n := by
  unfold wA2 offA3; rw [len_batchA2]; have := i.isLt; omega
lemma wNotRank1_lt_offS (i : Fin n) : wNotRank1 n i < offS n := by
  unfold wNotRank1 offS; rw [len_batchA3]; have := i.isLt; omega
lemma wHasZero_lt_offS : wHasZero n < offS n := by
  unfold wHasZero offS; rw [len_batchA3]; omega
lemma wHasRank1_lt_offS : wHasRank1 n < offS n := by
  unfold wHasRank1 offS; rw [len_batchA3]; omega
lemma wSignEven_lt_offB0 (p : ℕ) (hp : p ≤ n) : wSignEven n p < offB0 n := by
  unfold wSignEven; split_ifs with h0
  · have := wTrue_lt_offA1 n
    unfold offB0 offS offA3 offA2 at *; omega
  · unfold offB0; rw [len_secS]; omega
lemma wSignOdd_lt_offB1 (p : ℕ) (hp : p ≤ n) : wSignOdd n p < offB1 n := by
  unfold wSignOdd; split_ifs with h0
  · have := wFalse_lt_offA1 n
    unfold offB1 offB0 offS offA3 offA2 at *; omega
  · unfold offB1; rw [len_batchB0]; omega
lemma wBPos_lt_offB2 (j : Fin n) : wBPos n j < offB2 n := by
  unfold wBPos offB2; rw [len_batchB1]; have := j.isLt; omega
lemma wBNeg_lt_offB2 (j : Fin n) : wBNeg n j < offB2 n := by
  unfold wBNeg offB2; rw [len_batchB1]; have := j.isLt; omega
lemma wB_lt_offR (j : Fin n) : wB n j < offR n := by
  unfold wB offR; rw [len_batchB2]; have := j.isLt; omega
lemma wTr0_lt_offD0 (p : ℕ) (hp : p ≤ n) : wTr0 n p < offD0 n := by
  unfold wTr0; split_ifs with h0
  · have := wTrue_lt_offA1 n
    unfold offD0 offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
  · unfold offD0; rw [len_secR]; omega
lemma wTr1_lt_offD0 (p : ℕ) (hp : p ≤ n) : wTr1 n p < offD0 n := by
  unfold wTr1; split_ifs with h0
  · have := wFalse_lt_offA1 n
    unfold offD0 offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
  · unfold offD0; rw [len_secR]; omega
lemma wNotTr0_lt_offD1 (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) : wNotTr0 n p < offD1 n hn := by
  unfold wNotTr0 offD1; rw [len_batchD0]; omega
lemma wNotTr1_lt_offD1 (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) : wNotTr1 n p < offD1 n hn := by
  unfold wNotTr1 offD1; rw [len_batchD0]; omega
lemma wNotHasZero_lt_offD1 : wNotHasZero n < offD1 n hn := by
  unfold wNotHasZero offD1; rw [len_batchD0]; omega
lemma wNotHasRank1_lt_offD1 : wNotHasRank1 n < offD1 n hn := by
  unfold wNotHasRank1 offD1; rw [len_batchD0]; omega
lemma wIsFirstGlobal_lt_offD1 (i : Fin n) : wIsFirstGlobal n i < offD1 n hn := by
  unfold wIsFirstGlobal offD1; rw [len_batchD0]; have := i.isLt; omega
lemma wIsLastGlobal_lt_offD1 (i : Fin n) : wIsLastGlobal n i < offD1 n hn := by
  unfold wIsLastGlobal offD1; rw [len_batchD0]; have := i.isLt; omega
lemma wDyadMask_lt_offD1 (l : Fin (Lmax n)) (i : Fin n) : wDyadMask n l i < offD1 n hn := by
  unfold wDyadMask offD1; rw [len_batchD0]
  have hlt : l.val * n + i.val < Lmax n * n := by
    calc l.val * n + i.val < l.val * n + n := Nat.add_lt_add_left i.isLt _
      _ = (l.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Lmax n * n := Nat.mul_le_mul_right n l.isLt
  omega
lemma wTr2_lt_offD2 (p : ℕ) (hp : p ≤ n) : wTr2 n hn p < offD2 n hn := by
  unfold wTr2; split_ifs with h0
  · have := wFalse_lt_offA1 n
    unfold offD2 offD1 offD0 offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
  · unfold offD2; rw [len_batchD1]; omega
lemma wPEq_lt_offD3 (p : ℕ) (hp : p ≤ n) (s : Bool) (t : Fin 3) :
    wPEq n hn p s t < offD3 n hn := by
  unfold wPEq offD3; rw [len_batchD2]
  have hs := stIdx_lt s t
  have : p * 6 + stIdx s t < (n + 1) * 6 := by omega
  omega
lemma wPC_lt_offD4 (i : Fin n) (s : Bool) (t c : Fin 3) : wPC n hn i s t c < offD4 n hn := by
  unfold wPC offD4; rw [len_batchD3]
  have := i.isLt; have := tupIdx_lt s t c; omega
lemma wPR_lt_offD4 (i : Fin n) (s : Bool) (t r : Fin 3) : wPR n hn i s t r < offD4 n hn := by
  unfold wPR offD4; rw [len_batchD3]
  have := i.isLt; have := tupIdx_lt s t r; omega
lemma wTildeC_lt_offD5 (i : Fin n) (v : Fin 3) : wTildeC n hn i v < offD5 n hn := by
  unfold wTildeC offD5; rw [len_batchD4]
  have := i.isLt; have := v.isLt; omega
lemma wTildeR_lt_offD5 (i : Fin n) (v : Fin 3) : wTildeR n hn i v < offD5 n hn := by
  unfold wTildeR offD5; rw [len_batchD4]
  have := i.isLt; have := v.isLt; omega
lemma wFirstCTag_lt_offD6 (i : Fin n) (v : Fin 3) : wFirstCTag n hn i v < offD6 n hn := by
  unfold wFirstCTag offD6; rw [len_batchD5]
  have := i.isLt; have := v.isLt; omega
lemma wLastRTag_lt_offD6 (i : Fin n) (v : Fin 3) : wLastRTag n hn i v < offD6 n hn := by
  unfold wLastRTag offD6; rw [len_batchD5]
  have := i.isLt; have := v.isLt; omega
lemma wDyadTag_lt_offD6 (l : Fin (Lmax n)) (i : Fin n) (v : Fin 3) :
    wDyadTag n hn l i v < offD6 n hn := by
  unfold wDyadTag offD6; rw [len_batchD5]
  have h1 : l.val * n + i.val < Lmax n * n := by
    calc l.val * n + i.val < l.val * n + n := Nat.add_lt_add_left i.isLt _
      _ = (l.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Lmax n * n := Nat.mul_le_mul_right n l.isLt
  have := v.isLt
  omega
lemma wFirstC_lt_offD7 (v : Fin 3) : wFirstC n hn v < offD7 n hn := by
  unfold wFirstC offD7; rw [len_batchD6]; have := v.isLt; omega
lemma wLastR_lt_offD7 (v : Fin 3) : wLastR n hn v < offD7 n hn := by
  unfold wLastR offD7; rw [len_batchD6]; have := v.isLt; omega
lemma wLeftVec_lt_offD7 (m : Fin n) (v : Fin 3) : wLeftVec n hn m v < offD7 n hn := by
  unfold wLeftVec offD7; rw [len_batchD6]; have := m.isLt; have := v.isLt; omega
lemma wRightVec_lt_offD7 (m : Fin n) (v : Fin 3) : wRightVec n hn m v < offD7 n hn := by
  unfold wRightVec offD7; rw [len_batchD6]; have := m.isLt; have := v.isLt; omega

lemma closed_A0 : ∀ g ∈ batchA0 n, ∀ j ∈ g.inputs, j < offA0 n := by
  intro g hg j hj
  simp only [batchA0, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨k, rfl⟩ | rfl | rfl
  · simp only [List.mem_singleton] at hj; rw [hj]; exact k.isLt
  · simp at hj
  · simp at hj

lemma closed_A1 : ∀ g ∈ batchA1 n, ∀ j ∈ g.inputs, j < offA1 n := by
  intro g hg j hj
  simp only [batchA1, List.mem_ofFn] at hg
  rcases hg with ⟨p, rfl⟩
  simp only [matMintermGate, List.mem_map] at hj
  rcases hj with ⟨r, _, rfl⟩
  split_ifs
  · have hlt : 4 * (p.val / 16) + r.val < I_w n := by
      unfold I_w; have := r.isLt; have := p.isLt; omega
    unfold offA1 offA0 at *; omega
  · apply wNotIn_lt_offA1
    unfold I_w; have := r.isLt; have := p.isLt; omega

lemma closed_A2 : ∀ g ∈ batchA2 n, ∀ j ∈ g.inputs, j < offA2 n := by
  intro g hg j hj
  simp only [batchA2, List.mem_ofFn] at hg
  rcases hg with ⟨p, rfl⟩
  simp only [matPropGate, List.mem_map] at hj
  rcases hj with ⟨m, _, rfl⟩
  exact wEqMat_lt_offA2 n _ m

lemma closed_A3 : ∀ g ∈ batchA3 n, ∀ j ∈ g.inputs, j < offA3 n := by
  intro g hg j hj
  simp only [batchA3, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, rfl⟩ | rfl | rfl
  · simp only [List.mem_singleton] at hj; rw [hj]; exact wA2_lt_offA3 n i 1 (by decide)
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨i, rfl⟩; exact wA2_lt_offA3 n i 0 (by decide)
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨i, rfl⟩; exact wA2_lt_offA3 n i 1 (by decide)

lemma closed_S : ∀ g ∈ secS n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < offS n := by
  intro g hg
  simp only [secS, List.mem_ofFn] at hg
  rcases hg with ⟨i, rfl⟩
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with ⟨k, _, rfl | rfl | rfl⟩ <;>
  · have := wA2_lt_offA3 n ⟨k.val, by omega⟩ 2 (by decide)
    unfold wOddSign offS at *; omega

lemma closed_B0 : ∀ g ∈ batchB0 n, ∀ j ∈ g.inputs, j < offB0 n := by
  intro g hg j hj
  simp only [batchB0, List.mem_ofFn] at hg
  rcases hg with ⟨i, rfl⟩
  simp only [List.mem_singleton] at hj; rw [hj]
  exact wSignEven_lt_offB0 n (i.val + 1) i.isLt

lemma closed_B1 : ∀ g ∈ batchB1 n, ∀ j ∈ g.inputs, j < offB1 n := by
  intro g hg j hj
  simp only [batchB1, List.mem_ofFn] at hg
  rcases hg with ⟨p, rfl⟩
  split_ifs at hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have := wSignEven_lt_offB0 n (p.val / 2) (by have := p.isLt; omega)
      unfold offB1 at *; omega
    · have := wA2_lt_offA3 n ⟨p.val / 2, div_lt_of_lt_mul_r p.isLt⟩ 4 (by decide)
      unfold wTrans2 offB1 offB0 offS at *; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact wSignOdd_lt_offB1 n (p.val / 2) (by have := p.isLt; omega)
    · have := wA2_lt_offA3 n ⟨p.val / 2, div_lt_of_lt_mul_r p.isLt⟩ 3 (by decide)
      unfold wTrans1 offB1 offB0 offS at *; omega

lemma closed_B2 : ∀ g ∈ batchB2 n, ∀ j ∈ g.inputs, j < offB2 n := by
  intro g hg j hj
  simp only [batchB2, List.mem_ofFn] at hg
  rcases hg with ⟨k, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact wBPos_lt_offB2 n k
  · exact wBNeg_lt_offB2 n k

lemma closed_R : ∀ g ∈ secR n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < offR n := by
  intro g hg
  simp only [secR, List.mem_ofFn] at hg
  rcases hg with ⟨p, rfl⟩
  have hbase : ∀ i : Fin n, ∀ j ∈ rBaseInputs n i, j < offR n := by
    intro i j hj
    simp only [rBaseInputs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with ⟨k, _, rfl | rfl | rfl | rfl⟩
    · have := wA2_lt_offA3 n ⟨k.val, by omega⟩ 5 (by decide)
      unfold wTransNZ offR offB2 offB1 offB0 offS at *; omega
    · have := wA2_lt_offA3 n ⟨k.val, by omega⟩ 5 (by decide)
      unfold wTransNZ offR offB2 offB1 offB0 offS at *; omega
    · exact wB_lt_offR n ⟨k.val, by omega⟩
    · exact wB_lt_offR n ⟨k.val, by omega⟩
  split_ifs
  · exact ⟨rfl, hbase _⟩
  · refine ⟨rfl, ?_⟩
    intro j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with hb | rfl | rfl | rfl | rfl
    · exact hbase _ j hb
    · have := wTrue_lt_offA1 n; unfold offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
    · have := wTrue_lt_offA1 n; unfold offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
    · have := wTrue_lt_offA1 n; unfold offR offB2 offB1 offB0 offS offA3 offA2 at *; omega
    · have := wTrue_lt_offA1 n; unfold offR offB2 offB1 offB0 offS offA3 offA2 at *; omega

lemma closed_D0 : ∀ g ∈ batchD0 n hn, ∀ j ∈ g.inputs, j < offD0 n := by
  intro g hg j hj
  simp only [batchD0, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((((⟨p, rfl⟩ | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨p, rfl⟩)
  · split_ifs at hj
    · simp only [List.mem_singleton] at hj; rw [hj]
      exact wTr0_lt_offD0 n (p.val / 2 + 1) (by have := p.isLt; omega)
    · simp only [List.mem_singleton] at hj; rw [hj]
      exact wTr1_lt_offD0 n (p.val / 2 + 1) (by have := p.isLt; omega)
  · simp only [List.mem_singleton] at hj; rw [hj]
    have := wHasZero_lt_offS n; unfold offD0 offR offB2 offB1 offB0 at *; omega
  · simp only [List.mem_singleton] at hj; rw [hj]
    have := wHasRank1_lt_offS n; unfold offD0 offR offB2 offB1 offB0 at *; omega
  · simp only [List.mem_cons, List.mem_map] at hj
    rcases hj with rfl | ⟨k, _, rfl⟩
    · have := wA2_lt_offA3 n i 1 (by decide)
      unfold wIsRank1 offD0 offR offB2 offB1 offB0 offS at *; omega
    · have := wNotRank1_lt_offS n ⟨k.val, by omega⟩
      unfold offD0 offR offB2 offB1 offB0 at *; omega
  · simp only [List.mem_cons, List.mem_map] at hj
    rcases hj with rfl | ⟨t, _, rfl⟩
    · have := wA2_lt_offA3 n i 1 (by decide)
      unfold wIsRank1 offD0 offR offB2 offB1 offB0 offS at *; omega
    · have := wNotRank1_lt_offS n ⟨i.val + 1 + t.val, by omega⟩
      unfold offD0 offR offB2 offB1 offB0 at *; omega
  · unfold dyadMaskGate at hj
    dsimp only at hj
    split_ifs at hj
    · simp only [List.mem_cons, List.mem_map] at hj
      rcases hj with rfl | ⟨t, _, rfl⟩
      · have := wA2_lt_offA3 n ⟨p.val % n, Nat.mod_lt _ hn⟩ 1 (by decide)
        unfold wIsRank1 offD0 offR offB2 offB1 offB0 offS at *; omega
      · have := wNotRank1_lt_offS n ⟨p.val % n + 1 + t.val, by omega⟩
        unfold offD0 offR offB2 offB1 offB0 at *; omega
    · simp only [List.mem_cons, List.mem_map] at hj
      rcases hj with rfl | ⟨t, _, rfl⟩
      · have := wA2_lt_offA3 n ⟨p.val % n, Nat.mod_lt _ hn⟩ 1 (by decide)
        unfold wIsRank1 offD0 offR offB2 offB1 offB0 offS at *; omega
      · have := wNotRank1_lt_offS n ⟨((p.val % n) / 2 ^ (p.val / n + 1)) * 2 ^ (p.val / n + 1) + 2 ^ (p.val / n) + t.val, by have := t.isLt; have := Nat.mod_lt p.val hn; omega⟩
        unfold offD0 offR offB2 offB1 offB0 at *; omega

lemma closed_D1 : ∀ g ∈ batchD1 n, ∀ j ∈ g.inputs, j < offD1 n hn := by
  intro g hg j hj
  simp only [batchD1, List.mem_ofFn] at hg
  rcases hg with ⟨i, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact wNotTr0_lt_offD1 n hn (i.val + 1) (by omega) i.isLt
  · exact wNotTr1_lt_offD1 n hn (i.val + 1) (by omega) i.isLt

lemma closed_D2 : ∀ g ∈ batchD2 n hn, ∀ j ∈ g.inputs, j < offD2 n hn := by
  intro g hg j hj
  simp only [batchD2, List.mem_ofFn] at hg
  rcases hg with ⟨q, rfl⟩
  have hp : q.val / 6 ≤ n := by have := q.isLt; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · unfold wSignEq
    split_ifs
    · have := wSignOdd_lt_offB1 n (q.val / 6) hp
      unfold offD2 offD1 offD0 offR offB2 at *; omega
    · have := wSignEven_lt_offB0 n (q.val / 6) hp
      unfold offD2 offD1 offD0 offR offB2 offB1 at *; omega
  · unfold wTrEq
    rcases (show q.val % 6 % 3 = 0 ∨ q.val % 6 % 3 = 1 ∨ q.val % 6 % 3 = 2 by omega) with h | h | h
    · simp only [h]
      have := wTr0_lt_offD0 n (q.val / 6) hp
      unfold offD2 offD1 at *; omega
    · simp only [h]
      have := wTr1_lt_offD0 n (q.val / 6) hp
      unfold offD2 offD1 at *; omega
    · simp only [h]
      exact wTr2_lt_offD2 n hn (q.val / 6) hp

lemma closed_D3 : ∀ g ∈ batchD3 n hn, ∀ j ∈ g.inputs, j < offD3 n hn := by
  intro g hg j hj
  simp only [batchD3, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact wPEq_lt_offD3 n hn (q.val / 18) (by have := q.isLt; omega) _ _
    · have hmod : q.val % 18 % 3 = q.val % 3 := by omega
      have := wA2_lt_offA3 n ⟨q.val / 18, div_lt_of_lt_mul_r q.isLt⟩ (6 + q.val % 3) (by omega)
      unfold wColVec offD3 offD2 offD1 offD0 offR offB2 offB1 offB0 offS at *; dsimp only at *; rw [hmod]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact wPEq_lt_offD3 n hn (q.val / 18) (by have := q.isLt; omega) _ _
    · have hmod : q.val % 18 % 3 = q.val % 3 := by omega
      have := wA2_lt_offA3 n ⟨q.val / 18, div_lt_of_lt_mul_r q.isLt⟩ (9 + q.val % 3) (by omega)
      unfold wRowVec offD3 offD2 offD1 offD0 offR offB2 offB1 offB0 offS at *; dsimp only at *; rw [hmod]; omega

lemma closed_D4 : ∀ g ∈ batchD4 n hn, ∀ j ∈ g.inputs, j < offD4 n hn := by
  intro g hg j hj
  simp only [batchD4, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · simp only [List.mem_map] at hj; rcases hj with ⟨x, _, rfl⟩
    exact wPC_lt_offD4 n hn _ x.1 x.2.1 x.2.2
  · simp only [List.mem_map] at hj; rcases hj with ⟨x, _, rfl⟩
    exact wPR_lt_offD4 n hn _ x.1 x.2.1 x.2.2

lemma closed_D5 : ∀ g ∈ batchD5 n hn, ∀ j ∈ g.inputs, j < offD5 n hn := by
  intro g hg j hj
  simp only [batchD5, List.mem_append, List.mem_ofFn] at hg
  rcases hg with (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have := wIsFirstGlobal_lt_offD1 n hn ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
      unfold offD5 offD4 offD3 offD2 at *; omega
    · exact wTildeC_lt_offD5 n hn _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have := wIsLastGlobal_lt_offD1 n hn ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
      unfold offD5 offD4 offD3 offD2 at *; omega
    · exact wTildeR_lt_offD5 n hn _ _
  · split_ifs at hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · have := wDyadMask_lt_offD1 n hn ⟨q.val / 3 / n, div_lt_of_lt_mul_r (div_lt_of_lt_mul_r q.isLt)⟩ ⟨q.val / 3 % n, Nat.mod_lt _ hn⟩
        unfold offD5 offD4 offD3 offD2 at *; omega
      · exact wTildeR_lt_offD5 n hn _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · have := wDyadMask_lt_offD1 n hn ⟨q.val / 3 / n, div_lt_of_lt_mul_r (div_lt_of_lt_mul_r q.isLt)⟩ ⟨q.val / 3 % n, Nat.mod_lt _ hn⟩
        unfold offD5 offD4 offD3 offD2 at *; omega
      · exact wTildeC_lt_offD5 n hn _ _

lemma closed_D6 : ∀ g ∈ batchD6 n hn, ∀ j ∈ g.inputs, j < offD6 n hn := by
  intro g hg j hj
  simp only [batchD6, List.mem_append, List.mem_ofFn] at hg
  rcases hg with ((⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨q, rfl⟩) | ⟨q, rfl⟩
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨i, rfl⟩; exact wFirstCTag_lt_offD6 n hn i v
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨i, rfl⟩; exact wLastRTag_lt_offD6 n hn i v
  · unfold leftVecGate at hj
    split_ifs at hj
    · simp only [List.mem_map] at hj; rcases hj with ⟨t, _, rfl⟩; exact wDyadTag_lt_offD6 n hn _ _ _
    · simp at hj
  · unfold rightVecGate at hj
    split_ifs at hj
    · simp only [List.mem_map] at hj; rcases hj with ⟨t, _, rfl⟩; exact wDyadTag_lt_offD6 n hn _ _ _
    · simp at hj

lemma closed_D7 : ∀ g ∈ batchD7 n hn, ∀ j ∈ g.inputs, j < offD7 n hn := by
  intro g hg j hj
  simp only [batchD7, List.mem_append, List.mem_ofFn, List.mem_map, List.mem_singleton] at hg
  rcases hg with (⟨q, rfl⟩ | ⟨x, _, rfl⟩) | rfl
  · rcases (show q.val % 3 = 0 ∨ q.val % 3 = 1 ∨ q.val % 3 = 2 by omega) with h | h | h
    · simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact wLeftVec_lt_offD7 n hn _ _
      · exact wRightVec_lt_offD7 n hn _ _
    · simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact wLeftVec_lt_offD7 n hn _ _
      · exact wRightVec_lt_offD7 n hn _ _
    · simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact wLeftVec_lt_offD7 n hn _ _
      · exact wRightVec_lt_offD7 n hn _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · have := wPEq_lt_offD3 n hn n le_rfl x.1 x.2.1
      unfold offD7 offD6 offD5 offD4 at *; omega
    · exact wFirstC_lt_offD7 n hn x.2.2.1
    · exact wLastR_lt_offD7 n hn x.2.2.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have := wPEq_lt_offD3 n hn n le_rfl false ⟨1, by decide⟩
      unfold offD7 offD6 offD5 offD4 at *; omega
    · have := wPEq_lt_offD3 n hn n le_rfl false ⟨2, by decide⟩
      unfold offD7 offD6 offD5 offD4 at *; omega

lemma closed_D8 : ∀ g ∈ batchD8 n hn, ∀ j ∈ g.inputs, j < offD8 n hn := by
  intro g hg j hj
  simp only [batchD8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨q, rfl⟩
    unfold offD8; rw [len_batchD7]; have := q.isLt; omega
  · simp only [List.mem_ofFn] at hj; rcases hj with ⟨q, rfl⟩
    unfold wBdotTerm offD8; rw [len_batchD7]; have := q.isLt; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have := wNotHasRank1_lt_offD1 n hn
      unfold offD8 offD7 offD6 offD5 offD4 offD3 offD2 at *; omega
    · unfold wTracePn offD8; rw [len_batchD7]; omega

lemma closed_D9 : ∀ g ∈ batchD9 n hn, ∀ j ∈ g.inputs, j < offD9 n hn := by
  intro g hg j hj
  simp only [batchD9, List.mem_singleton] at hg; subst hg
  simp only [List.mem_singleton] at hj; rw [hj]
  unfold wAnyBadPair offD9; rw [len_batchD8]; omega

lemma closed_D10 : ∀ g ∈ batchD10 n hn, ∀ j ∈ g.inputs, j < offD10 n hn := by
  intro g hg j hj
  simp only [batchD10, List.mem_singleton] at hg; subst hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have := wHasRank1_lt_offS n
    unfold offD10 offD9 offD8 offD7 offD6 offD5 offD4 offD3 offD2 offD1 offD0 offR offB2 offB1 offB0 at *; omega
  · unfold wNoBadPair offD10; rw [len_batchD9]; omega
  · unfold wBoundaryDot1 offD10 offD9; rw [len_batchD9, len_batchD8]; omega

lemma closed_D11 : ∀ g ∈ batchD11 n hn, ∀ j ∈ g.inputs, j < offD11 n hn := by
  intro g hg j hj
  simp only [batchD11, List.mem_singleton] at hg; subst hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · unfold wCase1 offD11 offD10 offD9; rw [len_batchD10, len_batchD9, len_batchD8]; omega
  · unfold wCase2 offD11; rw [len_batchD10]; omega

lemma closed_D12 : ∀ g ∈ batchD12 n hn, ∀ j ∈ g.inputs, j < offD12 n hn := by
  intro g hg j hj
  simp only [batchD12, List.mem_singleton] at hg; subst hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · have := wNotHasZero_lt_offD1 n hn
    unfold offD12 offD11 offD10 offD9 offD8 offD7 offD6 offD5 offD4 offD3 offD2 at *; omega
  · unfold wEither offD12; rw [len_batchD11]; omega

lemma ordinary_secA : ∀ g ∈ secA n, ordinaryGate g := by
  intro g hg
  simp only [secA, batchA0, batchA1, batchA2, batchA3, List.mem_append, List.mem_ofFn,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (((⟨_, rfl⟩ | rfl | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | (⟨_, rfl⟩ | rfl | rfl) <;>
  simp [ordinaryGate, matMintermGate, matPropGate]

lemma ordinary_secB : ∀ g ∈ secB n, ordinaryGate g := by
  intro g hg
  simp only [secB, batchB0, batchB1, batchB2, List.mem_append, List.mem_ofFn] at hg
  rcases hg with (⟨_, rfl⟩ | ⟨p, rfl⟩) | ⟨_, rfl⟩
  · simp [ordinaryGate]
  · split_ifs <;> simp [ordinaryGate]
  · simp [ordinaryGate]

lemma ordinary_secD : ∀ g ∈ secD n hn, ordinaryGate g := by
  intro g hg
  simp only [secD, List.mem_append] at hg
  rcases hg with (((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12
  · simp only [batchD0, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at h0
    rcases h0 with ((((⟨p, rfl⟩ | rfl | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩)
    · split_ifs <;> simp [ordinaryGate]
    · simp [ordinaryGate]
    · simp [ordinaryGate]
    · simp [ordinaryGate]
    · simp [ordinaryGate]
    · unfold dyadMaskGate; dsimp only; split_ifs <;> simp [ordinaryGate]
  · simp only [batchD1, List.mem_ofFn] at h1; rcases h1 with ⟨_, rfl⟩; simp [ordinaryGate]
  · simp only [batchD2, List.mem_ofFn] at h2; rcases h2 with ⟨_, rfl⟩; simp [ordinaryGate]
  · simp only [batchD3, List.mem_append, List.mem_ofFn] at h3
    rcases h3 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [ordinaryGate]
  · simp only [batchD4, List.mem_append, List.mem_ofFn] at h4
    rcases h4 with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [ordinaryGate]
  · simp only [batchD5, List.mem_append, List.mem_ofFn] at h5
    rcases h5 with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · simp [ordinaryGate]
    · simp [ordinaryGate]
    · split_ifs <;> simp [ordinaryGate]
  · simp only [batchD6, List.mem_append, List.mem_ofFn] at h6
    rcases h6 with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · simp [ordinaryGate]
    · simp [ordinaryGate]
    · unfold leftVecGate; split_ifs <;> simp [ordinaryGate]
    · unfold rightVecGate; split_ifs <;> simp [ordinaryGate]
  · simp only [batchD7, List.mem_append, List.mem_ofFn, List.mem_map, List.mem_singleton] at h7
    rcases h7 with (⟨q, rfl⟩ | ⟨_, _, rfl⟩) | rfl
    · rcases (show q.val % 3 = 0 ∨ q.val % 3 = 1 ∨ q.val % 3 = 2 by omega) with h | h | h <;>
      simp [h, ordinaryGate]
    · simp [ordinaryGate]
    · simp [ordinaryGate]
  · simp only [batchD8, List.mem_cons, List.not_mem_nil, or_false] at h8
    rcases h8 with rfl | rfl | rfl <;> simp [ordinaryGate]
  · simp only [batchD9, List.mem_singleton] at h9; subst h9; simp [ordinaryGate]
  · simp only [batchD10, List.mem_singleton] at h10; subst h10; simp [ordinaryGate]
  · simp only [batchD11, List.mem_singleton] at h11; subst h11; simp [ordinaryGate]
  · simp only [batchD12, List.mem_singleton] at h12; subst h12; simp [ordinaryGate]

lemma fullGates_eq_chain :
    fullGates n hn =
      ((((((((((((((((((((([] ++ batchA0 n) ++ batchA1 n) ++ batchA2 n) ++ batchA3 n) ++
      secS n) ++ batchB0 n) ++ batchB1 n) ++ batchB2 n) ++ secR n) ++
      batchD0 n hn) ++ batchD1 n) ++ batchD2 n hn) ++ batchD3 n hn) ++
      batchD4 n hn) ++ batchD5 n hn) ++ batchD6 n hn) ++ batchD7 n hn) ++
      batchD8 n hn) ++ batchD9 n hn) ++ batchD10 n hn) ++ batchD11 n hn) ++ batchD12 n hn := by
  simp [fullGates, secA, secB, secD, List.append_assoc]

lemma structural_bounds :
    ReadsBack (4 * n) (buildCircuit n hn) ∧
    (buildCircuit n hn).output < 4 * n + (buildCircuit n hn).size ∧
    (buildCircuit n hn).depth (4 * n) ≤ 40 ∧
    (buildCircuit n hn).size ≤ 1000 * (n + 2) * (Nat.log2 (n + 2) + 1) ∧
    ((buildCircuit n hn).gates.map (fun g => g.inputs.length)).sum ≤ 1000 * (n + 2) ^ 2 ∧
    (∀ g ∈ secS n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < 4 * n + (secA n).length) ∧
    (∀ g ∈ secR n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < 4 * n + (secA n).length + (secS n).length + (secB n).length) := by
  have hlenA : 4 * n + (secA n).length = offS n := by
    simp [secA, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have hlenASB : 4 * n + (secA n).length + (secS n).length + (secB n).length = offR n := by
    simp [secA, secB, offR, offB2, offB1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have hS : ∀ g ∈ secS n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < 4 * n + (secA n).length := by
    rw [hlenA]; exact closed_S n
  have hR : ∀ g ∈ secR n, g.op = .mod 6 ∧ ∀ j ∈ g.inputs,
      j < 4 * n + (secA n).length + (secS n).length + (secB n).length := by
    rw [hlenASB]; exact closed_R n
  have hstep_rb : ∀ (p b : List Gate) (off : ℕ),
      4 * n + p.length = off →
      ReadsBack (4 * n) ⟨p, 0⟩ →
      (∀ g ∈ b, ∀ j ∈ g.inputs, j < off) →
      ReadsBack (4 * n) ⟨p ++ b, 0⟩ := by
    intro p b off hoff hrb hcl
    exact readsBack_append_batch (4 * n) p b hrb (by rwa [hoff])
  have hstep_d : ∀ (p b : List Gate) (off D : ℕ),
      4 * n + p.length = off →
      (∀ j < 4 * n + p.length, (evalDepths (4 * n) p).getD j 0 ≤ D) →
      (∀ g ∈ b, ∀ j ∈ g.inputs, j < off) →
      (∀ j < 4 * n + (p ++ b).length, (evalDepths (4 * n) (p ++ b)).getD j 0 ≤ D + 1) := by
    intro p b off D hoff hD hcl
    exact evalDepths_batch_le (4 * n) D p b hD (by rwa [hoff])
  have hrb0 : ReadsBack (4 * n) ⟨[], 0⟩ := fun j hj => by simp at hj
  have hd0 : ∀ j < 4 * n + ([] : List Gate).length, (evalDepths (4 * n) []).getD j 0 ≤ 0 := by
    intro j hj
    simp only [evalDepths, List.foldl_nil, List.getD_eq_getElem?_getD]
    have hj' : j < 4 * n := by simpa using hj
    rw [List.getElem?_eq_getElem (by simp [hj']), Option.getD_some, List.getElem_replicate]
  set g1 := [] ++ batchA0 n
  set g2 := g1 ++ batchA1 n
  set g3 := g2 ++ batchA2 n
  set g4 := g3 ++ batchA3 n
  set g5 := g4 ++ secS n
  set g6 := g5 ++ batchB0 n
  set g7 := g6 ++ batchB1 n
  set g8 := g7 ++ batchB2 n
  set g9 := g8 ++ secR n
  set g10 := g9 ++ batchD0 n hn
  set g11 := g10 ++ batchD1 n
  set g12 := g11 ++ batchD2 n hn
  set g13 := g12 ++ batchD3 n hn
  set g14 := g13 ++ batchD4 n hn
  set g15 := g14 ++ batchD5 n hn
  set g16 := g15 ++ batchD6 n hn
  set g17 := g16 ++ batchD7 n hn
  set g18 := g17 ++ batchD8 n hn
  set g19 := g18 ++ batchD9 n hn
  set g20 := g19 ++ batchD10 n hn
  set g21 := g20 ++ batchD11 n hn
  set g22 := g21 ++ batchD12 n hn
  have heq_full : fullGates n hn = g22 := fullGates_eq_chain n hn
  have h1 : 4 * n + ([] : List Gate).length = offA0 n := by simp [offA0, I_w]
  have h2 : 4 * n + g1.length = offA1 n := by simp [g1, offA1, offA0, I_w]
  have h3 : 4 * n + g2.length = offA2 n := by simp [g2, g1, offA2, offA1, offA0, I_w]; omega
  have h4 : 4 * n + g3.length = offA3 n := by simp [g3, g2, g1, offA3, offA2, offA1, offA0, I_w]; omega
  have h5 : 4 * n + g4.length = offS n := by simp [g4, g3, g2, g1, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h6 : 4 * n + g5.length = offB0 n := by simp [g5, g4, g3, g2, g1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h7 : 4 * n + g6.length = offB1 n := by simp [g6, g5, g4, g3, g2, g1, offB1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h8 : 4 * n + g7.length = offB2 n := by simp [g7, g6, g5, g4, g3, g2, g1, offB2, offB1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h9 : 4 * n + g8.length = offR n := by simp [g8, g7, g6, g5, g4, g3, g2, g1, offR, offB2, offB1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h10 : 4 * n + g9.length = offD0 n := by simp [g9, g8, g7, g6, g5, g4, g3, g2, g1, offD0, offR, offB2, offB1, offB0, offS, offA3, offA2, offA1, offA0, I_w]; omega
  have h11 : 4 * n + g10.length = offD1 n hn := by simp [g10, offD1]; rw [← h10]; omega
  have h12 : 4 * n + g11.length = offD2 n hn := by simp [g11, offD2]; rw [← h11]; omega
  have h13 : 4 * n + g12.length = offD3 n hn := by simp [g12, offD3]; rw [← h12]; omega
  have h14 : 4 * n + g13.length = offD4 n hn := by simp [g13, offD4]; rw [← h13]; omega
  have h15 : 4 * n + g14.length = offD5 n hn := by simp [g14, offD5]; rw [← h14]; omega
  have h16 : 4 * n + g15.length = offD6 n hn := by simp [g15, offD6]; rw [← h15]; omega
  have h17 : 4 * n + g16.length = offD7 n hn := by simp [g16, offD7]; rw [← h16]; omega
  have h18 : 4 * n + g17.length = offD8 n hn := by simp [g17, offD8]; rw [← h17]; omega
  have h19 : 4 * n + g18.length = offD9 n hn := by simp [g18, offD9]; rw [← h18]; omega
  have h20 : 4 * n + g19.length = offD10 n hn := by simp [g19, offD10]; rw [← h19]; omega
  have h21 : 4 * n + g20.length = offD11 n hn := by simp [g20, offD11]; rw [← h20]; omega
  have h22 : 4 * n + g21.length = offD12 n hn := by simp [g21, offD12]; rw [← h21]; omega
  have hrb22 : ReadsBack (4 * n) ⟨g22, 0⟩ := by
    have r1 := hstep_rb _ _ _ h1 hrb0 (closed_A0 n)
    have r2 := hstep_rb _ _ _ h2 r1 (closed_A1 n)
    have r3 := hstep_rb _ _ _ h3 r2 (closed_A2 n)
    have r4 := hstep_rb _ _ _ h4 r3 (closed_A3 n)
    have r5 := hstep_rb _ _ _ h5 r4 (fun g hg => (closed_S n g hg).2)
    have r6 := hstep_rb _ _ _ h6 r5 (closed_B0 n)
    have r7 := hstep_rb _ _ _ h7 r6 (closed_B1 n)
    have r8 := hstep_rb _ _ _ h8 r7 (closed_B2 n)
    have r9 := hstep_rb _ _ _ h9 r8 (fun g hg => (closed_R n g hg).2)
    have r10 := hstep_rb _ _ _ h10 r9 (closed_D0 n hn)
    have r11 := hstep_rb _ _ _ h11 r10 (closed_D1 n hn)
    have r12 := hstep_rb _ _ _ h12 r11 (closed_D2 n hn)
    have r13 := hstep_rb _ _ _ h13 r12 (closed_D3 n hn)
    have r14 := hstep_rb _ _ _ h14 r13 (closed_D4 n hn)
    have r15 := hstep_rb _ _ _ h15 r14 (closed_D5 n hn)
    have r16 := hstep_rb _ _ _ h16 r15 (closed_D6 n hn)
    have r17 := hstep_rb _ _ _ h17 r16 (closed_D7 n hn)
    have r18 := hstep_rb _ _ _ h18 r17 (closed_D8 n hn)
    have r19 := hstep_rb _ _ _ h19 r18 (closed_D9 n hn)
    have r20 := hstep_rb _ _ _ h20 r19 (closed_D10 n hn)
    have r21 := hstep_rb _ _ _ h21 r20 (closed_D11 n hn)
    exact hstep_rb _ _ _ h22 r21 (closed_D12 n hn)
  have hd22 : ∀ j < 4 * n + g22.length, (evalDepths (4 * n) g22).getD j 0 ≤ 22 := by
    have d1 := hstep_d _ _ _ 0 h1 hd0 (closed_A0 n)
    have d2 := hstep_d _ _ _ 1 h2 d1 (closed_A1 n)
    have d3 := hstep_d _ _ _ 2 h3 d2 (closed_A2 n)
    have d4 := hstep_d _ _ _ 3 h4 d3 (closed_A3 n)
    have d5 := hstep_d _ _ _ 4 h5 d4 (fun g hg => (closed_S n g hg).2)
    have d6 := hstep_d _ _ _ 5 h6 d5 (closed_B0 n)
    have d7 := hstep_d _ _ _ 6 h7 d6 (closed_B1 n)
    have d8 := hstep_d _ _ _ 7 h8 d7 (closed_B2 n)
    have d9 := hstep_d _ _ _ 8 h9 d8 (fun g hg => (closed_R n g hg).2)
    have d10 := hstep_d _ _ _ 9 h10 d9 (closed_D0 n hn)
    have d11 := hstep_d _ _ _ 10 h11 d10 (closed_D1 n hn)
    have d12 := hstep_d _ _ _ 11 h12 d11 (closed_D2 n hn)
    have d13 := hstep_d _ _ _ 12 h13 d12 (closed_D3 n hn)
    have d14 := hstep_d _ _ _ 13 h14 d13 (closed_D4 n hn)
    have d15 := hstep_d _ _ _ 14 h15 d14 (closed_D5 n hn)
    have d16 := hstep_d _ _ _ 15 h16 d15 (closed_D6 n hn)
    have d17 := hstep_d _ _ _ 16 h17 d16 (closed_D7 n hn)
    have d18 := hstep_d _ _ _ 17 h18 d17 (closed_D8 n hn)
    have d19 := hstep_d _ _ _ 18 h19 d18 (closed_D9 n hn)
    have d20 := hstep_d _ _ _ 19 h20 d19 (closed_D10 n hn)
    have d21 := hstep_d _ _ _ 20 h21 d20 (closed_D11 n hn)
    exact hstep_d _ _ _ 21 h22 d21 (closed_D12 n hn)
  have hout_lt : (buildCircuit n hn).output < 4 * n + (buildCircuit n hn).size := by
    change wOut n hn < 4 * n + (fullGates n hn).length
    rw [heq_full]
    change offD12 n hn < 4 * n + (g21 ++ batchD12 n hn).length
    rw [List.length_append, len_batchD12, ← Nat.add_assoc, h22]; omega
  have hdepth_le : (buildCircuit n hn).depth (4 * n) ≤ 40 := by
    change (evalDepths (4 * n) (fullGates n hn)).getD (wOut n hn) 0 ≤ 40
    rw [heq_full]
    have hlt : wOut n hn < 4 * n + g22.length := by
      rw [← heq_full]; exact hout_lt
    exact le_trans (hd22 _ hlt) (by decide)
  have hLmax_le : Lmax n ≤ Nat.log2 (n + 2) + 1 := by
    unfold Lmax; exact Nat.add_le_add_right (log2_mono (by omega)) 1
  have hLmax_le_n : Lmax n ≤ n + 1 := by
    unfold Lmax; have := log2_le_self n; omega
  have hsize_le : (buildCircuit n hn).size ≤ 1000 * (n + 2) * (Nat.log2 (n + 2) + 1) := by
    change (fullGates n hn).length ≤ _
    rw [heq_full]
    have hlen_g22 : g22.length =
        (4 * n + 2) + n * 16 + n * 12 + (n + 2) + n + n + n * 2 + n + n * 2 +
        (n * 2 + 2 + n + n + Lmax n * n) + n + (n + 1) * 6 + (n * 18 + n * 18) +
        (n * 3 + n * 3) + (n * 3 + n * 3 + Lmax n * n * 3) + (3 + 3 + n * 3 + n * 3) +
        (n * 3 + allBdotTuples.length + 1) + 3 + 1 + 1 + 1 + 1 := by
      simp only [g22, g21, g20, g19, g18, g17, g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1,
        List.length_append, List.length_nil, Nat.zero_add,
        len_batchA0, len_batchA1, len_batchA2, len_batchA3, len_secS,
        len_batchB0, len_batchB1, len_batchB2, len_secR,
        len_batchD0, len_batchD1, len_batchD2, len_batchD3, len_batchD4,
        len_batchD5, len_batchD6, len_batchD7, len_batchD8, len_batchD9,
        len_batchD10, len_batchD11, len_batchD12]
    rw [hlen_g22]
    have hb54 := allBdotTuples_length_le
    set M := Nat.log2 (n + 2) + 1
    set P := (n + 2) * M
    have hM1 : 1 ≤ M := by omega
    have h1 : Lmax n * n ≤ P := by
      calc Lmax n * n ≤ M * n := Nat.mul_le_mul_right n hLmax_le
        _ = n * M := Nat.mul_comm _ _
        _ ≤ (n + 2) * M := Nat.mul_le_mul_right M (by omega)
    have h2 : n + 2 ≤ P := Nat.le_mul_of_pos_right (n + 2) hM1
    have hmul : 1000 * (n + 2) * M = 1000 * P := Nat.mul_assoc 1000 (n + 2) M
    rw [hmul]
    omega
  have hfanin : ((buildCircuit n hn).gates.map (fun g => g.inputs.length)).sum ≤ 1000 * (n + 2) ^ 2 := by
    change ((fullGates n hn).map (fun g => g.inputs.length)).sum ≤ _
    rw [heq_full]
    have hsum_le (l : List Gate) (M : ℕ) (h : ∀ g ∈ l, g.inputs.length ≤ M) :
        (l.map (fun g => g.inputs.length)).sum ≤ l.length * M := by
      have := sum_le_mul_of_le (l.map (fun g => g.inputs.length)) M (by
        intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨g, hg, rfl⟩; exact h g hg)
      simpa using this
    have fA0 : ((batchA0 n).map (fun g => g.inputs.length)).sum ≤ (4 * n + 2) * 1 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchA0 n]); intro g hg
      simp only [batchA0, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | rfl | rfl <;> simp
    have fA1 : ((batchA1 n).map (fun g => g.inputs.length)).sum ≤ (n * 16) * 4 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchA1 n]); intro g hg
      simp only [batchA1, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; simp [matMintermGate]
    have fA2 : ((batchA2 n).map (fun g => g.inputs.length)).sum ≤ (n * 12) * 16 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchA2 n]); intro g hg
      simp only [batchA2, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩
      simp only [matPropGate, List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    have fA3 : ((batchA3 n).map (fun g => g.inputs.length)).sum ≤ (n + 2) * n := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchA3 n]); intro g hg
      simp only [batchA3, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ⟨_, rfl⟩ | rfl | rfl <;> simp <;> omega
    have fS : ((secS n).map (fun g => g.inputs.length)).sum ≤ n * (3 * n) := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_secS n]); intro g hg
      simp only [secS, List.mem_ofFn] at hg; rcases hg with ⟨i, rfl⟩
      have hlen : ((List.finRange (i.val + 1)).flatMap (fun j =>
          let w := wOddSign n ⟨j.val, by omega⟩; [w, w, w])).length = 3 * (i.val + 1) := by
        rw [List.length_flatMap]
        have : ∀ l : List (Fin (i.val + 1)), (l.map (fun j => ([wOddSign n ⟨j.val, by omega⟩,
            wOddSign n ⟨j.val, by omega⟩, wOddSign n ⟨j.val, by omega⟩]).length)).sum = 3 * l.length := by
          intro l; induction l with | nil => simp | cons _ _ ih => simp [ih]; omega
        simpa using this (List.finRange (i.val + 1))
      dsimp only; rw [hlen]; have := i.isLt; omega
    have fB0 : ((batchB0 n).map (fun g => g.inputs.length)).sum ≤ n * 1 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchB0 n]); intro g hg
      simp only [batchB0, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; simp
    have fB1 : ((batchB1 n).map (fun g => g.inputs.length)).sum ≤ (n * 2) * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchB1 n]); intro g hg
      simp only [batchB1, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; split_ifs <;> simp
    have fB2 : ((batchB2 n).map (fun g => g.inputs.length)).sum ≤ n * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchB2 n]); intro g hg
      simp only [batchB2, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; simp
    have fR : ((secR n).map (fun g => g.inputs.length)).sum ≤ (n * 2) * (4 * n + 4) := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_secR n]); intro g hg
      simp only [secR, List.mem_ofFn] at hg; rcases hg with ⟨p, rfl⟩
      have hrb_len : ∀ i : Fin n, (rBaseInputs n i).length = 4 * (i.val + 1) := by
        intro i; unfold rBaseInputs; rw [List.length_flatMap]
        have : ∀ l : List (Fin (i.val + 1)), (l.map (fun j =>
            ([wTransNZ n ⟨j.val, by omega⟩, wTransNZ n ⟨j.val, by omega⟩,
              wB n ⟨j.val, by omega⟩, wB n ⟨j.val, by omega⟩]).length)).sum = 4 * l.length := by
          intro l; induction l with | nil => simp | cons _ _ ih => simp [ih]; omega
        simpa using this (List.finRange (i.val + 1))
      split_ifs
      · dsimp only; rw [hrb_len]; have := p.isLt; omega
      · simp only [List.length_append, List.length_cons, List.length_nil, hrb_len]; have := p.isLt; omega
    have fD0 : ((batchD0 n hn).map (fun g => g.inputs.length)).sum ≤
        (n * 2) * 1 + 2 * 1 + n * (n + 1) + n * (n + 1) + 4 * n * (n + 1) := by
      unfold batchD0
      simp only [map_len_append]
      have s1 : ((List.ofFn (fun p : Fin (n * 2) =>
          let i := p.val / 2
          if p.val % 2 = 0 then (⟨.not, [wTr0 n (i + 1)]⟩ : Gate)
          else ⟨.not, [wTr1 n (i + 1)]⟩)).map (fun g => g.inputs.length)).sum ≤ (n * 2) * 1 := by
        have := hsum_le (List.ofFn (fun p : Fin (n * 2) =>
          let i := p.val / 2
          if p.val % 2 = 0 then (⟨.not, [wTr0 n (i + 1)]⟩ : Gate)
          else ⟨.not, [wTr1 n (i + 1)]⟩)) 1 (by
          intro g hg; simp only [List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; split_ifs <;> simp)
        simpa using this
      have s2 : (([⟨.not, [wHasZero n]⟩, ⟨.not, [wHasRank1 n]⟩] : List Gate).map
          (fun g => g.inputs.length)).sum ≤ 2 * 1 := by simp
      have s3 : ((List.ofFn (fun i : Fin n =>
          (⟨.and, wIsRank1 n i :: (List.finRange i.val).map (fun k => wNotRank1 n ⟨k.val, by omega⟩)⟩ : Gate))).map
          (fun g => g.inputs.length)).sum ≤ n * (n + 1) := by
        have h := hsum_le (List.ofFn (fun i : Fin n =>
          (⟨.and, wIsRank1 n i :: (List.finRange i.val).map (fun k => wNotRank1 n ⟨k.val, by omega⟩)⟩ : Gate))) (n + 1) (by
          intro g hg; simp only [List.mem_ofFn] at hg; rcases hg with ⟨i, rfl⟩
          simp only [List.length_cons, List.length_map, List.length_finRange]; have := i.isLt; omega)
        simpa using h
      have s4 : ((List.ofFn (fun i : Fin n =>
          (⟨.and, wIsRank1 n i :: (List.finRange (n - (i.val + 1))).map (fun t => wNotRank1 n ⟨i.val + 1 + t.val, by omega⟩)⟩ : Gate))).map
          (fun g => g.inputs.length)).sum ≤ n * (n + 1) := by
        have h := hsum_le (List.ofFn (fun i : Fin n =>
          (⟨.and, wIsRank1 n i :: (List.finRange (n - (i.val + 1))).map (fun t => wNotRank1 n ⟨i.val + 1 + t.val, by omega⟩)⟩ : Gate))) (n + 1) (by
          intro g hg; simp only [List.mem_ofFn] at hg; rcases hg with ⟨i, rfl⟩
          simp only [List.length_cons, List.length_map, List.length_finRange]; omega)
        simpa using h
      have s5 : ((List.ofFn (fun p : Fin (Lmax n * n) =>
          let l : Fin (Lmax n) := ⟨p.val / n, div_lt_of_lt_mul_r p.isLt⟩
          let i : Fin n := ⟨p.val % n, Nat.mod_lt _ hn⟩
          dyadMaskGate n l i)).map (fun g => g.inputs.length)).sum ≤ 4 * n * (n + 1) := by
        have hlen_dm (l : Fin (Lmax n)) (i : Fin n) : (dyadMaskGate n l i).inputs.length ≤ 2 ^ l.val + 1 := by
          unfold dyadMaskGate
          dsimp only
          split_ifs with hlt
          · simp only [List.length_cons, List.length_map, List.length_finRange]
            have hlo : (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) ≤ i.val := by
              rw [Nat.mul_comm]; exact Nat.mul_div_le i.val (2 ^ (l.val + 1))
            omega
          · simp only [List.length_cons, List.length_map, List.length_finRange]
            have hhi : i.val < (i.val / 2 ^ (l.val + 1) + 1) * 2 ^ (l.val + 1) := by
              rw [Nat.mul_comm]; exact Nat.lt_mul_div_succ i.val (Nat.two_pow_pos _)
            have hpow : 2 ^ (l.val + 1) = 2 ^ l.val + 2 ^ l.val := by rw [Nat.pow_succ]; omega
            have hhi2 : i.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ (l.val + 1) := by
              rw [Nat.add_mul, Nat.one_mul] at hhi; exact hhi
            omega
        have hsum_fin : ((List.ofFn (fun p : Fin (Lmax n * n) =>
            let l : Fin (Lmax n) := ⟨p.val / n, div_lt_of_lt_mul_r p.isLt⟩
            let i : Fin n := ⟨p.val % n, Nat.mod_lt _ hn⟩
            dyadMaskGate n l i)).map (fun g => g.inputs.length)).sum =
            ∑ p : Fin (Lmax n * n),
              (dyadMaskGate n ⟨p.val / n, div_lt_of_lt_mul_r p.isLt⟩
                ⟨p.val % n, Nat.mod_lt _ hn⟩).inputs.length := by
          rw [List.map_ofFn, List.sum_ofFn]; rfl
        rw [hsum_fin]
        have hle1 : (∑ p : Fin (Lmax n * n),
            (dyadMaskGate n ⟨p.val / n, div_lt_of_lt_mul_r p.isLt⟩
              ⟨p.val % n, Nat.mod_lt _ hn⟩).inputs.length) ≤
            ∑ p : Fin (Lmax n * n), (2 ^ (p.val / n) + 1) := by
          apply Finset.sum_le_sum; intro p _; exact hlen_dm _ _
        have hsum_eq : (∑ p : Fin (Lmax n * n), (2 ^ (p.val / n) + 1)) =
            n * (∑ l : Fin (Lmax n), (2 ^ l.val + 1)) := by
          have hbij : (∑ p : Fin (Lmax n * n), (2 ^ (p.val / n) + 1)) =
              ∑ l : Fin (Lmax n), ∑ _i : Fin n, (2 ^ l.val + 1) := by
            rw [← Fintype.sum_prod_type']
            refine Fintype.sum_equiv (finProdFinEquiv.symm) _ _ ?_
            intro p
            have h1 : (finProdFinEquiv.symm p).1.val = p.val / n := rfl
            simp [h1]
          rw [hbij]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
        have hpow_sum : ∀ k : ℕ, (∑ l : Fin k, 2 ^ l.val) + 1 = 2 ^ k := by
          intro k; induction k with
          | zero => simp
          | succ k ih =>
            rw [Fin.sum_univ_castSucc, Nat.pow_succ]; simp only [Fin.val_castSucc, Fin.val_last]; omega
        have hinner : (∑ l : Fin (Lmax n), (2 ^ l.val + 1)) ≤ 4 * (n + 1) := by
          rw [Finset.sum_add_distrib]
          have hs1 := hpow_sum (Lmax n)
          have h2L : 2 ^ Lmax n ≤ 2 * n := by
            unfold Lmax; rw [Nat.pow_succ]; have := pow2_log2_le n hn; omega
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          omega
        calc (∑ p : Fin (Lmax n * n), _) ≤ n * (∑ l : Fin (Lmax n), (2 ^ l.val + 1)) := by
              rw [← hsum_eq]; exact hle1
          _ ≤ n * (4 * (n + 1)) := Nat.mul_le_mul_left n hinner
          _ = 4 * n * (n + 1) := by ring
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add s1 s2) s3) s4) s5
    have fD1 : ((batchD1 n).map (fun g => g.inputs.length)).sum ≤ n * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD1 n]); intro g hg
      simp only [batchD1, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; simp
    have fD2 : ((batchD2 n hn).map (fun g => g.inputs.length)).sum ≤ ((n + 1) * 6) * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD2 n hn]); intro g hg
      simp only [batchD2, List.mem_ofFn] at hg; rcases hg with ⟨_, rfl⟩; simp
    have fD3 : ((batchD3 n hn).map (fun g => g.inputs.length)).sum ≤ (n * 18 + n * 18) * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD3 n hn]); intro g hg
      simp only [batchD3, List.mem_append, List.mem_ofFn] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have fD4 : ((batchD4 n hn).map (fun g => g.inputs.length)).sum ≤ (n * 3 + n * 3) * 18 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD4 n hn]); intro g hg
      simp only [batchD4, List.mem_append, List.mem_ofFn] at hg
      rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      · simp only [List.length_map]
        exact le_trans (List.length_filter_le _ _) (by rw [allMatTuples_length])
    have fD5 : ((batchD5 n hn).map (fun g => g.inputs.length)).sum ≤
        (n * 3 + n * 3 + Lmax n * n * 3) * 2 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD5 n hn]); intro g hg
      simp only [batchD5, List.mem_append, List.mem_ofFn] at hg
      rcases hg with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
      · simp
      · simp
      · split_ifs <;> simp
    have fD6 : ((batchD6 n hn).map (fun g => g.inputs.length)).sum ≤
        (3 + 3 + n * 3 + n * 3) * n := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD6 n hn]); intro g hg
      simp only [batchD6, List.mem_append, List.mem_ofFn] at hg
      rcases hg with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨q, rfl⟩) | ⟨q, rfl⟩
      · simp
      · simp
      · unfold leftVecGate; split_ifs
        · simp only [List.length_map, List.length_finRange]; have := div_lt_of_lt_mul_r q.isLt; omega
        · simp
      · unfold rightVecGate; split_ifs
        · simp only [List.length_map, List.length_finRange]; omega
        · simp
    have fD7 : ((batchD7 n hn).map (fun g => g.inputs.length)).sum ≤
        (n * 3 + allBdotTuples.length + 1) * 3 := by
      refine le_trans (hsum_le _ _ ?_) (by rw [len_batchD7 n hn]); intro g hg
      simp only [batchD7, List.mem_append, List.mem_ofFn, List.mem_map, List.mem_singleton] at hg
      rcases hg with (⟨q, rfl⟩ | ⟨_, _, rfl⟩) | rfl
      · rcases (show q.val % 3 = 0 ∨ q.val % 3 = 1 ∨ q.val % 3 = 2 by omega) with h | h | h <;> simp [h]
      · simp
      · simp
    have fD8 : ((batchD8 n hn).map (fun g => g.inputs.length)).sum ≤ n * 3 + allBdotTuples.length + 2 := by
      simp [batchD8]; omega
    have fD9 : ((batchD9 n hn).map (fun g => g.inputs.length)).sum = 1 := by simp [batchD9]
    have fD10 : ((batchD10 n hn).map (fun g => g.inputs.length)).sum = 3 := by simp [batchD10]
    have fD11 : ((batchD11 n hn).map (fun g => g.inputs.length)).sum = 2 := by simp [batchD11]
    have fD12 : ((batchD12 n hn).map (fun g => g.inputs.length)).sum = 2 := by simp [batchD12]
    have hD5_sq : Lmax n * n ≤ n * n + n := by
      have := Nat.mul_le_mul_right n hLmax_le_n; rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hb54 := allBdotTuples_length_le
    have hsq_exp : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
    have hmul1 : (n + 2) * n = n * n + 2 * n := by ring
    have hmul2 : n * (3 * n) = 3 * (n * n) := by ring
    have hmul3 : n * 2 * (4 * n + 4) = 8 * (n * n) + 8 * n := by ring
    have hmul4 : n * (n + 1) = n * n + n := by ring
    have hmul5 : 4 * n * (n + 1) = 4 * (n * n) + 4 * n := by ring
    have hmul6 : (3 + 3 + n * 3 + n * 3) * n = 6 * (n * n) + 6 * n := by ring
    simp only [g22, g21, g20, g19, g18, g17, g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1,
      map_len_append, List.map_nil, List.sum_nil, Nat.zero_add]
    rw [hmul1] at fA3
    rw [hmul2] at fS
    rw [hmul3] at fR
    rw [hmul4, hmul5] at fD0
    rw [hmul6] at fD6
    rw [hsq_exp]
    omega
  refine ⟨?_, hout_lt, hdepth_le, hsize_le, hfanin, hS, hR⟩
  change ReadsBack (4 * n) ⟨fullGates n hn, wOut n hn⟩
  rw [heq_full]
  exact hrb22

lemma input_x_spec (T : Fin n → Bool → Bool → Bool) :
    let x := (List.ofFn (fun i : Fin n =>
      [T i false false, T i true false, T i false true, T i true true])).flatten
    x.length = 4 * n ∧
    ∀ (i : Fin n) (r : Fin 4),
      x.getD (4 * i.val + r.val) false = (matOf (T i)).val.testBit r.val := by
  intro x
  have hlen : x.length = 4 * n := by
    have hflat : ∀ (k : ℕ) (f : Fin k → List Bool), (∀ i, (f i).length = 4) →
        (List.ofFn f).flatten.length = 4 * k := by
      intro k
      induction k with
      | zero => intro _ _; simp
      | succ k ih =>
        intro f hf
        rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0, ih (fun i => f i.succ) (fun i => hf i.succ)]
        omega
    exact hflat n _ (fun _ => rfl)
  refine ⟨hlen, ?_⟩
  intro i r
  have hget : ∀ (k : ℕ) (f : Fin k → Bool → Bool → Bool) (i : Fin k) (r : Fin 4),
      ((List.ofFn (fun j : Fin k => [f j false false, f j true false, f j false true, f j true true])).flatten).getD
        (4 * i.val + r.val) false =
      match r.val with
      | 0 => f i false false
      | 1 => f i true false
      | 2 => f i false true
      | _ => f i true true := by
    intro k
    induction k with
    | zero => intro _ i; exact Fin.elim0 i
    | succ k ih =>
      intro f i r
      rw [List.ofFn_succ, List.flatten_cons]
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD]
        have hr4 : r.val < ([f 0 false false, f 0 true false, f 0 false true, f 0 true true]).length := by
          simp
        rw [List.getElem?_append_left hr4]
        fin_cases r <;> rfl
      | succ j =>
        simp only [Fin.val_succ, List.getD_eq_getElem?_getD]
        have hge : 4 ≤ 4 * (j.val + 1) + r.val := by omega
        have hlen4 : ([f 0 false false, f 0 true false, f 0 false true, f 0 true true]).length = 4 := rfl
        rw [List.getElem?_append_right (by omega), hlen4]
        have hsub : 4 * (j.val + 1) + r.val - 4 = 4 * j.val + r.val := by omega
        rw [hsub]
        simpa [List.getD_eq_getElem?_getD] using ih (fun m => f m.succ) j r
  rw [hget n T i r]
  have h00 := entry_matOf (T i) false false
  have h10 := entry_matOf (T i) true false
  have h01 := entry_matOf (T i) false true
  have h11 := entry_matOf (T i) true true
  unfold entry at h00 h10 h01 h11
  fin_cases r
  · exact h00.symm
  · exact h10.symm
  · exact h01.symm
  · exact h11.symm

lemma eval_circuit_part1 (T : Fin n → Bool → Bool → Bool) (Ms : Fin n → Fin 16)
    (hMs : Ms = fun i => matOf (T i)) (W : List Bool)
    (hW_eq : W = evalWires (fullGates n hn)
      ((List.ofFn (fun i : Fin n =>
        [T i false false, T i true false, T i false true, T i true true])).flatten)) :
    (W.getD (wHasRank1 n) false = true ↔ ∃ i : Fin n, mIsRank1 (Ms i) = true) ∧
    (W.getD (wNotHasZero n) false = true ↔ ∀ i : Fin n, mIsZero (Ms i) = false) ∧
    (W.getD (wNotHasRank1 n) false = true ↔ ∀ i : Fin n, mIsRank1 (Ms i) = false) ∧
    (∀ i : Fin n, W.getD (wIsFirstGlobal n i) false = true ↔
      mIsRank1 (Ms i) = true ∧ ∀ j : Fin n, j.val < i.val → mIsRank1 (Ms j) = false) ∧
    (∀ i : Fin n, W.getD (wIsLastGlobal n i) false = true ↔
      mIsRank1 (Ms i) = true ∧ ∀ j : Fin n, i.val < j.val → mIsRank1 (Ms j) = false) ∧
    (∀ (l : Fin (Lmax n)) (i : Fin n),
      W.getD (wDyadMask n l i) false = true ↔
        mIsRank1 (Ms i) = true ∧
        if i.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val then
          ∀ k : Fin n, i.val < k.val → k.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val → mIsRank1 (Ms k) = false
        else
          ∀ k : Fin n, (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val ≤ k.val → k.val < i.val → mIsRank1 (Ms k) = false) ∧
    (∀ (p : ℕ) (hp : p ≤ n) (s : Bool) (t : Fin 3),
      W.getD (wPEq n hn p s t) false = (decide (prefSign Ms p = s) && decide (prefTrans Ms p = t))) ∧
    (∀ (i : Fin n) (v : Fin 3), W.getD (wTildeC n hn i v) false = decide (tildeC Ms i = v)) ∧
    (∀ (i : Fin n) (v : Fin 3), W.getD (wTildeR n hn i v) false = decide (tildeR Ms i = v)) := by
  subst hMs
  set x := (List.ofFn (fun i : Fin n =>
    [T i false false, T i true false, T i false true, T i true true])).flatten
  let Ms : Fin n → Fin 16 := fun i => matOf (T i)
  rcases input_x_spec n T with ⟨hxlen, hxbit⟩
  change x.length = 4 * n at hxlen
  let g0 : List Gate := []
  let g1 := g0 ++ batchA0 n
  let g2 := g1 ++ batchA1 n
  let g3 := g2 ++ batchA2 n
  let g4 := g3 ++ batchA3 n
  let g5 := g4 ++ secS n
  let g6 := g5 ++ batchB0 n
  let g7 := g6 ++ batchB1 n
  let g8 := g7 ++ batchB2 n
  let g9 := g8 ++ secR n
  let g10 := g9 ++ batchD0 n hn
  let g11 := g10 ++ batchD1 n
  let g12 := g11 ++ batchD2 n hn
  let g13 := g12 ++ batchD3 n hn
  let g14 := g13 ++ batchD4 n hn
  let g15 := g14 ++ batchD5 n hn
  let g16 := g15 ++ batchD6 n hn
  let g17 := g16 ++ batchD7 n hn
  let g18 := g17 ++ batchD8 n hn
  let g19 := g18 ++ batchD9 n hn
  let g20 := g19 ++ batchD10 n hn
  let g21 := g20 ++ batchD11 n hn
  let g22 := g21 ++ batchD12 n hn
  have hfull : fullGates n hn = g22 := fullGates_eq_chain n hn
  have o0 : x.length + g0.length = offA0 n := by simp [g0, hxlen, offA0, I_w]
  have o1 : x.length + g1.length = offA1 n := by simp only [g1, List.length_append, offA1]; rw [← o0]; omega
  have o2 : x.length + g2.length = offA2 n := by simp only [g2, List.length_append, offA2]; rw [← o1]; omega
  have o3 : x.length + g3.length = offA3 n := by simp only [g3, List.length_append, offA3]; rw [← o2]; omega
  have o4 : x.length + g4.length = offS n := by simp only [g4, List.length_append, offS]; rw [← o3]; omega
  have o5 : x.length + g5.length = offB0 n := by simp only [g5, List.length_append, offB0]; rw [← o4]; omega
  have o6 : x.length + g6.length = offB1 n := by simp only [g6, List.length_append, offB1]; rw [← o5]; omega
  have o7 : x.length + g7.length = offB2 n := by simp only [g7, List.length_append, offB2]; rw [← o6]; omega
  have o8 : x.length + g8.length = offR n := by simp only [g8, List.length_append, offR]; rw [← o7]; omega
  have o9 : x.length + g9.length = offD0 n := by simp only [g9, List.length_append, offD0]; rw [← o8]; omega
  have o10 : x.length + g10.length = offD1 n hn := by simp only [g10, List.length_append, offD1]; rw [← o9]; omega
  have o11 : x.length + g11.length = offD2 n hn := by simp only [g11, List.length_append, offD2]; rw [← o10]; omega
  have o12 : x.length + g12.length = offD3 n hn := by simp only [g12, List.length_append, offD3]; rw [← o11]; omega
  have o13 : x.length + g13.length = offD4 n hn := by simp only [g13, List.length_append, offD4]; rw [← o12]; omega
  have o14 : x.length + g14.length = offD5 n hn := by simp only [g14, List.length_append, offD5]; rw [← o13]; omega
  have o15 : x.length + g15.length = offD6 n hn := by simp only [g15, List.length_append, offD6]; rw [← o14]; omega
  have o16 : x.length + g16.length = offD7 n hn := by simp only [g16, List.length_append, offD7]; rw [← o15]; omega
  have o17 : x.length + g17.length = offD8 n hn := by simp only [g17, List.length_append, offD8]; rw [← o16]; omega
  have o18 : x.length + g18.length = offD9 n hn := by simp only [g18, List.length_append, offD9]; rw [← o17]; omega
  have o19 : x.length + g19.length = offD10 n hn := by simp only [g19, List.length_append, offD10]; rw [← o18]; omega
  have o20 : x.length + g20.length = offD11 n hn := by simp only [g20, List.length_append, offD11]; rw [← o19]; omega
  have o21 : x.length + g21.length = offD12 n hn := by simp only [g21, List.length_append, offD12]; rw [← o20]; omega
  have hspl : ∀ (A B : List Gate), (∃ suff, g22 = (A ++ B) ++ suff) → ∃ suff, g22 = A ++ suff := by
    rintro A B ⟨suff, h⟩; exact ⟨B ++ suff, by rw [h, List.append_assoc]⟩
  have hsp21 : ∃ suff, g22 = (g21 ++ batchD12 n hn) ++ suff := ⟨[], by simp [g22]⟩
  have hsp20 : ∃ suff, g22 = (g20 ++ batchD11 n hn) ++ suff := hspl _ _ hsp21
  have hsp19 : ∃ suff, g22 = (g19 ++ batchD10 n hn) ++ suff := hspl _ _ hsp20
  have hsp18 : ∃ suff, g22 = (g18 ++ batchD9 n hn) ++ suff := hspl _ _ hsp19
  have hsp17 : ∃ suff, g22 = (g17 ++ batchD8 n hn) ++ suff := hspl _ _ hsp18
  have hsp16 : ∃ suff, g22 = (g16 ++ batchD7 n hn) ++ suff := hspl _ _ hsp17
  have hsp15 : ∃ suff, g22 = (g15 ++ batchD6 n hn) ++ suff := hspl _ _ hsp16
  have hsp14 : ∃ suff, g22 = (g14 ++ batchD5 n hn) ++ suff := hspl _ _ hsp15
  have hsp13 : ∃ suff, g22 = (g13 ++ batchD4 n hn) ++ suff := hspl _ _ hsp14
  have hsp12 : ∃ suff, g22 = (g12 ++ batchD3 n hn) ++ suff := hspl _ _ hsp13
  have hsp11 : ∃ suff, g22 = (g11 ++ batchD2 n hn) ++ suff := hspl _ _ hsp12
  have hsp10 : ∃ suff, g22 = (g10 ++ batchD1 n) ++ suff := hspl _ _ hsp11
  have hsp9 : ∃ suff, g22 = (g9 ++ batchD0 n hn) ++ suff := hspl _ _ hsp10
  have hsp8 : ∃ suff, g22 = (g8 ++ secR n) ++ suff := hspl _ _ hsp9
  have hsp7 : ∃ suff, g22 = (g7 ++ batchB2 n) ++ suff := hspl _ _ hsp8
  have hsp6 : ∃ suff, g22 = (g6 ++ batchB1 n) ++ suff := hspl _ _ hsp7
  have hsp5 : ∃ suff, g22 = (g5 ++ batchB0 n) ++ suff := hspl _ _ hsp6
  have hsp4 : ∃ suff, g22 = (g4 ++ secS n) ++ suff := hspl _ _ hsp5
  have hsp3 : ∃ suff, g22 = (g3 ++ batchA3 n) ++ suff := hspl _ _ hsp4
  have hsp2 : ∃ suff, g22 = (g2 ++ batchA2 n) ++ suff := hspl _ _ hsp3
  have hsp1 : ∃ suff, g22 = (g1 ++ batchA1 n) ++ suff := hspl _ _ hsp2
  have hsp0 : ∃ suff, g22 = (g0 ++ batchA0 n) ++ suff := hspl _ _ hsp1
  rw [hfull] at hW_eq
  have hagree : ∀ (pref suff : List Gate) (off : ℕ) (w : ℕ),
      g22 = pref ++ suff → x.length + pref.length = off → w < off →
      W.getD w false = (evalWires pref x).getD w false :=
    fun pref suff off w hgs hoff hw => by rw [hW_eq]; exact evalWires_agree_in_full g22 pref suff x off w hgs hoff hw
  have hbatch : ∀ (prev batch : List Gate) (off : ℕ) (k : ℕ) (hk : k < batch.length),
      (∃ suff, g22 = (prev ++ batch) ++ suff) →
      x.length + prev.length = off →
      (∀ g ∈ batch, ∀ j ∈ g.inputs, j < off) →
      W.getD (off + k) false =
        (batch[k]).op.eval ((batch[k]).inputs.map (fun j => W.getD j false)) :=
    fun prev batch off k hk hsp hoff hcl => by rw [hW_eq]; exact evalWires_batch_in_full g22 prev batch x off k hk hsp hoff hcl
  have hIn (k : ℕ) (hk : k < 4 * n) : W.getD k false = x.getD k false := by
    exact hagree g0 g22 (offA0 n) k (by simp [g0]) o0 (by unfold offA0 I_w; omega)
  have hNotIn (k : ℕ) (hk : k < 4 * n) : W.getD (wNotIn n k) false = !(x.getD k false) := by
    have hk' : k < (batchA0 n).length := by rw [len_batchA0]; omega
    have hb := hbatch g0 (batchA0 n) (offA0 n) k hk' hsp0 o0 (closed_A0 n)
    unfold wNotIn
    rw [hb]
    have hget : (batchA0 n)[k]'hk' = ⟨.not, [k]⟩ := by
      unfold batchA0 at hk' ⊢
      rw [List.getElem_append_left (by simp [I_w]; omega)]
      simp
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hIn k hk]
  have hTrue : W.getD (wTrue n) false = true := by
    have hk' : I_w n < (batchA0 n).length := by rw [len_batchA0]; unfold I_w; omega
    have hb := hbatch g0 (batchA0 n) (offA0 n) (I_w n) hk' hsp0 o0 (closed_A0 n)
    unfold wTrue; rw [hb]
    have hget : (batchA0 n)[I_w n]'hk' = ⟨.and, []⟩ := by
      unfold batchA0 at hk' ⊢
      rw [List.getElem_append_right (by simp)]
      simp
    rw [hget]; rfl
  have hFalse : W.getD (wFalse n) false = false := by
    have hk' : I_w n + 1 < (batchA0 n).length := by rw [len_batchA0]; unfold I_w; omega
    have hb := hbatch g0 (batchA0 n) (offA0 n) (I_w n + 1) hk' hsp0 o0 (closed_A0 n)
    change W.getD (offA0 n + (I_w n + 1)) false = false
    rw [hb]
    have hget : (batchA0 n)[I_w n + 1]'hk' = ⟨.or, []⟩ := by
      unfold batchA0 at hk' ⊢
      rw [List.getElem_append_right (by simp)]
      simp
    rw [hget]; rfl
  have hEqMat (i : Fin n) (m : Fin 16) : W.getD (wEqMat n i m) false = decide (Ms i = m) := by
    have hk' : i.val * 16 + m.val < (batchA1 n).length := by
      rw [len_batchA1]; have := i.isLt; have := m.isLt; omega
    have hb := hbatch g1 (batchA1 n) (offA1 n) (i.val * 16 + m.val) hk' hsp1 o1 (closed_A1 n)
    unfold wEqMat; rw [hb]
    have hget : (batchA1 n)[i.val * 16 + m.val]'hk' = matMintermGate n i m := by
      unfold batchA1 at hk' ⊢
      rw [List.getElem_ofFn]
      have hd : (⟨(i.val * 16 + m.val) / 16, div_lt_of_lt_mul_r (by have := i.isLt; have := m.isLt; omega)⟩ : Fin n) = i := Fin.ext (by have := m.isLt; dsimp; omega)
      have hm : (⟨(i.val * 16 + m.val) % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = m := Fin.ext (by have := m.isLt; dsimp; omega)
      rw [hd, hm]
    rw [hget]
    apply Bool.eq_iff_iff.mpr
    simp only [matMintermGate, gateOp_and_iff, List.mem_map, decide_eq_true_eq]
    constructor
    · intro hall
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro r
      by_cases hr : r < 4
      · have hmem := hall _ ⟨_, ⟨⟨r, hr⟩, List.mem_finRange _, rfl⟩, rfl⟩
        have hlt4 : 4 * i.val + r < 4 * n := by have := i.isLt; omega
        split_ifs at hmem with hbit
        · rw [hIn _ hlt4, hxbit i ⟨r, hr⟩] at hmem
          exact hmem.trans hbit.symm
        · rw [hNotIn _ hlt4, hxbit i ⟨r, hr⟩] at hmem
          have hbf : m.val.testBit r = false := by cases hb' : m.val.testBit r <;> simp [hb'] at hbit ⊢
          cases hms : (Ms i).val.testBit r
          · exact hbf.symm
          · rw [hms] at hmem; exact absurd hmem (by decide)
      · have h16 : 16 ≤ 2 ^ r := le_trans (by decide : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
        have h1 : (Ms i).val < 2 ^ r := lt_of_lt_of_le (Ms i).isLt h16
        have h2 : m.val < 2 ^ r := lt_of_lt_of_le m.isLt h16
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    · rintro rfl b ⟨w', ⟨r, _, rfl⟩, rfl⟩
      have hlt4 : 4 * i.val + r.val < 4 * n := by have := i.isLt; have := r.isLt; omega
      split_ifs with hbit
      · rw [hIn _ hlt4, hxbit i r]; exact hbit
      · rw [hNotIn _ hlt4, hxbit i r]
        cases hms : (Ms i).val.testBit r.val <;> simp [hms] at hbit ⊢
  have hA2 (i : Fin n) (slot : Fin 12) : W.getD (wA2 n i slot.val) false = a2Pred slot (Ms i) := by
    have hk' : i.val * 12 + slot.val < (batchA2 n).length := by
      rw [len_batchA2]; have := i.isLt; have := slot.isLt; omega
    have hb := hbatch g2 (batchA2 n) (offA2 n) (i.val * 12 + slot.val) hk' hsp2 o2 (closed_A2 n)
    unfold wA2; rw [hb]
    have hget : (batchA2 n)[i.val * 12 + slot.val]'hk' = matPropGate n i (a2Pred slot) := by
      unfold batchA2 at hk' ⊢
      rw [List.getElem_ofFn]
      have hd : (⟨(i.val * 12 + slot.val) / 12, div_lt_of_lt_mul_r (by have := i.isLt; have := slot.isLt; omega)⟩ : Fin n) = i := Fin.ext (by have := slot.isLt; dsimp; omega)
      have hm : (⟨(i.val * 12 + slot.val) % 12, Nat.mod_lt _ (by decide)⟩ : Fin 12) = slot := Fin.ext (by have := slot.isLt; dsimp; omega)
      rw [hd, hm]
    rw [hget]
    apply Bool.eq_iff_iff.mpr
    simp only [matPropGate, gateOp_or_iff, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
    constructor
    · rintro ⟨b, ⟨w', ⟨m, hm, rfl⟩, rfl⟩, hb1⟩
      rw [hEqMat i m, decide_eq_true_eq] at hb1
      rw [hb1]; exact hm
    · intro hp
      exact ⟨true, ⟨wEqMat n i (Ms i), ⟨Ms i, hp, rfl⟩, by rw [hEqMat]; simp⟩, rfl⟩
  have hIsZero (i : Fin n) : W.getD (wIsZero n i) false = mIsZero (Ms i) := by simpa [wIsZero, a2Pred] using hA2 i ⟨0, by decide⟩
  have hIsRank1 (i : Fin n) : W.getD (wIsRank1 n i) false = mIsRank1 (Ms i) := by simpa [wIsRank1, a2Pred] using hA2 i ⟨1, by decide⟩
  have hOddSign (i : Fin n) : W.getD (wOddSign n i) false = gSign (Ms i) := by simpa [wOddSign, a2Pred] using hA2 i ⟨2, by decide⟩
  have hTrans1 (i : Fin n) : W.getD (wTrans1 n i) false = decide ((gTrans (Ms i)).val = 1) := by simpa [wTrans1, a2Pred] using hA2 i ⟨3, by decide⟩
  have hTrans2 (i : Fin n) : W.getD (wTrans2 n i) false = decide ((gTrans (Ms i)).val = 2) := by simpa [wTrans2, a2Pred] using hA2 i ⟨4, by decide⟩
  have hTransNZ (i : Fin n) : W.getD (wTransNZ n i) false = decide ((gTrans (Ms i)).val ≠ 0) := by simpa [wTransNZ, a2Pred] using hA2 i ⟨5, by decide⟩
  have hColVec (i : Fin n) (v : Fin 3) : W.getD (wColVec n i v) false = decide (mCol (Ms i) = v) := by
    have h := hA2 i ⟨6 + v.val, by have := v.isLt; omega⟩
    fin_cases v <;> (change W.getD (wA2 n i _) false = _; rw [h]; apply Bool.eq_iff_iff.mpr; simp only [a2Pred, decide_eq_true_eq, Fin.ext_iff])
  have hRowVec (i : Fin n) (v : Fin 3) : W.getD (wRowVec n i v) false = decide (mRow (Ms i) = v) := by
    have h := hA2 i ⟨9 + v.val, by have := v.isLt; omega⟩
    fin_cases v <;> (change W.getD (wA2 n i _) false = _; rw [h]; apply Bool.eq_iff_iff.mpr; simp only [a2Pred, decide_eq_true_eq, Fin.ext_iff])
  have hNotRank1 (i : Fin n) : W.getD (wNotRank1 n i) false = !(mIsRank1 (Ms i)) := by
    have hk' : i.val < (batchA3 n).length := by rw [len_batchA3]; have := i.isLt; omega
    have hb := hbatch g3 (batchA3 n) (offA3 n) i.val hk' hsp3 o3 (closed_A3 n)
    unfold wNotRank1; rw [hb]
    have hget : (batchA3 n)[i.val]'hk' = ⟨.not, [wIsRank1 n i]⟩ := by
      unfold batchA3 at hk' ⊢; rw [List.getElem_append_left (by simp [i.isLt])]; simp
    rw [hget]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hIsRank1]
  have hHasZero : W.getD (wHasZero n) false = true ↔ ∃ i : Fin n, mIsZero (Ms i) = true := by
    have hk' : n < (batchA3 n).length := by rw [len_batchA3]; omega
    have hb := hbatch g3 (batchA3 n) (offA3 n) n hk' hsp3 o3 (closed_A3 n)
    unfold wHasZero; rw [hb]
    have hget : (batchA3 n)[n]'hk' = ⟨.or, List.ofFn (fun i : Fin n => wIsZero n i)⟩ := by
      unfold batchA3 at hk' ⊢; rw [List.getElem_append_right (by simp)]; simp
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, h1⟩; exact ⟨i, by rwa [← hIsZero i]⟩
    · rintro ⟨i, hi⟩; exact ⟨true, ⟨wIsZero n i, ⟨i, rfl⟩, by rw [hIsZero, hi]⟩, rfl⟩
  have hHasRank1 : W.getD (wHasRank1 n) false = true ↔ ∃ i : Fin n, mIsRank1 (Ms i) = true := by
    have hk' : n + 1 < (batchA3 n).length := by rw [len_batchA3]; omega
    have hb := hbatch g3 (batchA3 n) (offA3 n) (n + 1) hk' hsp3 o3 (closed_A3 n)
    change W.getD (offA3 n + (n + 1)) false = true ↔ _
    rw [hb]
    have hget : (batchA3 n)[n + 1]'hk' = ⟨.or, List.ofFn (fun i : Fin n => wIsRank1 n i)⟩ := by
      unfold batchA3 at hk' ⊢; rw [List.getElem_append_right (by simp)]; simp
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, h1⟩; exact ⟨i, by rwa [← hIsRank1 i]⟩
    · rintro ⟨i, hi⟩; exact ⟨true, ⟨wIsRank1 n i, ⟨i, rfl⟩, by rw [hIsRank1, hi]⟩, rfl⟩
  have hSignEven (p : ℕ) (hp : p ≤ n) : W.getD (wSignEven n p) false = !(prefSign Ms p) := by
    cases p with
    | zero => unfold wSignEven; rw [if_pos rfl, hTrue, prefSign_zero]; rfl
    | succ q =>
      have hk' : q < (secS n).length := by rw [len_secS]; omega
      have hb := hbatch g4 (secS n) (offS n) q hk' hsp4 o4 (fun g hg => (closed_S n g hg).2)
      simp only [wSignEven, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [hb]
      have hget : (secS n)[q]'hk' = ⟨.mod 6, (List.finRange (q + 1)).flatMap (fun j =>
          let w := wOddSign n ⟨j.val, by omega⟩; [w, w, w])⟩ := by
        unfold secS at hk' ⊢; rw [List.getElem_ofFn]
      rw [hget]
      have hmap : (((List.finRange (q + 1)).flatMap (fun j =>
            let w := wOddSign n ⟨j.val, by omega⟩; [w, w, w])).map (fun j => W.getD j false)) =
          (((List.finRange (q + 1)).map (fun j => gSign (Ms ⟨j.val, by omega⟩))).flatMap (fun b => [b, b, b])) := by
        rw [List.map_flatMap, List.flatMap_map]
        exact congrArg (List.flatMap · (List.finRange (q + 1))) (funext fun j => by simp only [Function.comp_apply, List.map_cons, List.map_nil, hOddSign])
      apply Bool.eq_iff_iff.mpr
      rw [gateOp_mod6_iff, hmap, count_flatMap_triple]
      unfold prefSign
      rw [map_finRange_eq (Nat.min_eq_left hp) (Nat.min_le_right _ _) hp (fun j => gSign (Ms j))]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      omega
  have hSignOdd (p : ℕ) (hp : p ≤ n) : W.getD (wSignOdd n p) false = prefSign Ms p := by
    cases p with
    | zero => unfold wSignOdd; rw [if_pos rfl, hFalse, prefSign_zero]
    | succ q =>
      have hk' : q < (batchB0 n).length := by rw [len_batchB0]; omega
      have hb := hbatch g5 (batchB0 n) (offB0 n) q hk' hsp5 o5 (closed_B0 n)
      simp only [wSignOdd, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [hb]
      have hget : (batchB0 n)[q]'hk' = ⟨.not, [wSignEven n (q + 1)]⟩ := by
        unfold batchB0 at hk' ⊢; rw [List.getElem_ofFn]
      rw [hget]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hSignEven (q + 1) hp, Bool.not_not]
  have hBPos (j : Fin n) : W.getD (wBPos n j) false = (!prefSign Ms j.val && decide ((gTrans (Ms j)).val = 2)) := by
    have hk' : j.val * 2 < (batchB1 n).length := by rw [len_batchB1]; have := j.isLt; omega
    have hb := hbatch g6 (batchB1 n) (offB1 n) (j.val * 2) hk' hsp6 o6 (closed_B1 n)
    unfold wBPos; rw [hb]
    have hget : (batchB1 n)[j.val * 2]'hk' = ⟨.and, [wSignEven n j.val, wTrans2 n j]⟩ := by
      unfold batchB1 at hk' ⊢; rw [List.getElem_ofFn]
      have hd : j.val * 2 / 2 = j.val := by omega
      have hm : j.val * 2 % 2 = 0 := by omega
      simp [hd, hm]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hSignEven j.val (le_of_lt j.isLt), hTrans2]
  have hBNeg (j : Fin n) : W.getD (wBNeg n j) false = (prefSign Ms j.val && decide ((gTrans (Ms j)).val = 1)) := by
    have hk' : j.val * 2 + 1 < (batchB1 n).length := by rw [len_batchB1]; have := j.isLt; omega
    have hb := hbatch g6 (batchB1 n) (offB1 n) (j.val * 2 + 1) hk' hsp6 o6 (closed_B1 n)
    unfold wBNeg; rw [hb]
    have hget : (batchB1 n)[j.val * 2 + 1]'hk' = ⟨.and, [wSignOdd n j.val, wTrans1 n j]⟩ := by
      unfold batchB1 at hk' ⊢; rw [List.getElem_ofFn]
      have hd : (j.val * 2 + 1) / 2 = j.val := by omega
      have hm : (j.val * 2 + 1) % 2 = 1 := by omega
      simp [hd, hm]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hSignOdd j.val (le_of_lt j.isLt), hTrans1]
  have hB (j : Fin n) : W.getD (wB n j) false =
      ((!prefSign Ms j.val && decide ((gTrans (Ms j)).val = 2)) ||
       (prefSign Ms j.val && decide ((gTrans (Ms j)).val = 1))) := by
    have hk' : j.val < (batchB2 n).length := by rw [len_batchB2]; exact j.isLt
    have hb := hbatch g7 (batchB2 n) (offB2 n) j.val hk' hsp7 o7 (closed_B2 n)
    unfold wB; rw [hb]
    have hget : (batchB2 n)[j.val]'hk' = ⟨.or, [wBPos n j, wBNeg n j]⟩ := by
      unfold batchB2 at hk' ⊢; rw [List.getElem_ofFn]
    rw [hget]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hBPos, hBNeg]
  have hRBaseCount (q : ℕ) (hq : q < n) :
      ((rBaseInputs n ⟨q, hq⟩).map (fun j => W.getD j false)).count true =
        2 * ((List.finRange (q + 1)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum := by
    unfold rBaseInputs
    have hmap : (((List.finRange (q + 1)).flatMap (fun j =>
          let jf : Fin n := ⟨j.val, by omega⟩
          [wTransNZ n jf, wTransNZ n jf, wB n jf, wB n jf])).map (fun w => W.getD w false)) =
        (((List.finRange (q + 1)).map (fun j =>
          let jf : Fin n := ⟨j.val, by omega⟩
          (W.getD (wTransNZ n jf) false, W.getD (wB n jf) false))).flatMap (fun p => [p.1, p.1, p.2, p.2])) := by
      rw [List.map_flatMap, List.flatMap_map]; rfl
    rw [hmap, count_flatMap_quad, List.map_map]
    refine congrArg (2 * ·) (congrArg List.sum (List.map_congr_left fun j _ => ?_))
    simp only [Function.comp_apply, hTransNZ, hB]
    exact (signedU_split Ms ⟨j.val, by omega⟩).symm
  have hTr0 (p : ℕ) (hp : p ≤ n) : W.getD (wTr0 n p) false = decide ((prefTrans Ms p).val = 0) := by
    cases p with
    | zero => unfold wTr0; rw [if_pos rfl, hTrue, prefTrans_zero]; rfl
    | succ q =>
      have hk' : q * 2 < (secR n).length := by rw [len_secR]; omega
      have hb := hbatch g8 (secR n) (offR n) (q * 2) hk' hsp8 o8 (fun g hg => (closed_R n g hg).2)
      simp only [wTr0, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [hb]
      have hget : (secR n)[q * 2]'hk' = ⟨.mod 6, rBaseInputs n ⟨q, by omega⟩⟩ := by
        unfold secR at hk' ⊢; rw [List.getElem_ofFn]
        have hd : q * 2 / 2 = q := by omega
        have hm : q * 2 % 2 = 0 := by omega
        simp [hd, hm]
      rw [hget]
      apply Bool.eq_iff_iff.mpr
      rw [gateOp_mod6_iff, hRBaseCount q (by omega)]
      have htr_v : (prefTrans Ms (q + 1)).val = ((List.finRange (q + 1)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum % 3 := by
        change ((List.finRange (min (q + 1) n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum % 3 = _
        rw [map_finRange_eq (Nat.min_eq_left hp) (Nat.min_le_right _ _) hp (signedU Ms)]
      rw [htr_v]
      simp only [decide_eq_true_eq]
      omega
  have hTr1 (p : ℕ) (hp : p ≤ n) : W.getD (wTr1 n p) false = decide ((prefTrans Ms p).val = 1) := by
    cases p with
    | zero => unfold wTr1; rw [if_pos rfl, hFalse, prefTrans_zero]; rfl
    | succ q =>
      have hk' : q * 2 + 1 < (secR n).length := by rw [len_secR]; omega
      have hb := hbatch g8 (secR n) (offR n) (q * 2 + 1) hk' hsp8 o8 (fun g hg => (closed_R n g hg).2)
      simp only [wTr1, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [hb]
      have hget : (secR n)[q * 2 + 1]'hk' = ⟨.mod 6, rBaseInputs n ⟨q, by omega⟩ ++ [wTrue n, wTrue n, wTrue n, wTrue n]⟩ := by
        unfold secR at hk' ⊢; rw [List.getElem_ofFn]
        have hd : (q * 2 + 1) / 2 = q := by omega
        have hm : (q * 2 + 1) % 2 = 1 := by omega
        simp [hd, hm]
      rw [hget]
      apply Bool.eq_iff_iff.mpr
      rw [gateOp_mod6_iff, List.map_append, List.count_append, hRBaseCount q (by omega)]
      have hc4 : (([wTrue n, wTrue n, wTrue n, wTrue n]).map (fun j => W.getD j false)).count true = 4 := by
        simp only [List.map_cons, List.map_nil, hTrue]; decide
      rw [hc4]
      have htr_v : (prefTrans Ms (q + 1)).val = ((List.finRange (q + 1)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum % 3 := by
        change ((List.finRange (min (q + 1) n)).map (fun j => signedU Ms ⟨j.val, by omega⟩)).sum % 3 = _
        rw [map_finRange_eq (Nat.min_eq_left hp) (Nat.min_le_right _ _) hp (signedU Ms)]
      rw [htr_v]
      simp only [decide_eq_true_eq]
      omega
  have hD0_call (k : ℕ) (hk : k < (batchD0 n hn).length) :
      W.getD (offD0 n + k) false =
        ((batchD0 n hn)[k]'hk).op.eval (((batchD0 n hn)[k]'hk).inputs.map (fun j => W.getD j false)) :=
    hbatch g9 (batchD0 n hn) (offD0 n) k hk hsp9 o9 (closed_D0 n hn)
  have hNotTr0 (q : ℕ) (hq : q < n) : W.getD (wNotTr0 n (q + 1)) false = !decide ((prefTrans Ms (q + 1)).val = 0) := by
    have hk' : q * 2 < (batchD0 n hn).length := by rw [len_batchD0]; omega
    unfold wNotTr0; simp only [Nat.add_sub_cancel]
    rw [hD0_call (q * 2) hk']
    have hget : (batchD0 n hn)[q * 2]'hk' = ⟨.not, [wTr0 n (q + 1)]⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega),
        List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega), List.getElem_ofFn]
      have hd : q * 2 / 2 = q := by omega
      have hm : q * 2 % 2 = 0 := by omega
      simp [hd, hm]
    rw [hget]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hTr0 (q + 1) (by omega)]
  have hNotTr1 (q : ℕ) (hq : q < n) : W.getD (wNotTr1 n (q + 1)) false = !decide ((prefTrans Ms (q + 1)).val = 1) := by
    have hk' : q * 2 + 1 < (batchD0 n hn).length := by rw [len_batchD0]; omega
    unfold wNotTr1; simp only [Nat.add_sub_cancel]
    rw [hD0_call (q * 2 + 1) hk']
    have hget : (batchD0 n hn)[q * 2 + 1]'hk' = ⟨.not, [wTr1 n (q + 1)]⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega),
        List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega), List.getElem_ofFn]
      have hd : (q * 2 + 1) / 2 = q := by omega
      have hm : (q * 2 + 1) % 2 = 1 := by omega
      simp [hd, hm]
    rw [hget]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hTr1 (q + 1) (by omega)]
  have hNotHasZero : W.getD (wNotHasZero n) false = true ↔ ∀ i : Fin n, mIsZero (Ms i) = false := by
    have hk' : n * 2 < (batchD0 n hn).length := by rw [len_batchD0]; omega
    unfold wNotHasZero; rw [hD0_call (n * 2) hk']
    have hget : (batchD0 n hn)[n * 2]'hk' = ⟨.not, [wHasZero n]⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega),
        List.getElem_append_left (by simp; try omega), List.getElem_append_right (by simp)]
      simp
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_true']
    constructor
    · intro hf i
      cases hz : mIsZero (Ms i)
      · rfl
      · have h1 := hHasZero.mpr ⟨i, hz⟩; rw [hf] at h1; exact absurd h1 Bool.false_ne_true
    · intro hall
      cases hw : W.getD (wHasZero n) false
      · rfl
      · rcases hHasZero.mp hw with ⟨i, hi⟩; rw [hall i] at hi; exact absurd hi Bool.false_ne_true
  have hNotHasRank1 : W.getD (wNotHasRank1 n) false = true ↔ ∀ i : Fin n, mIsRank1 (Ms i) = false := by
    have hk' : n * 2 + 1 < (batchD0 n hn).length := by rw [len_batchD0]; omega
    change W.getD (offD0 n + (n * 2 + 1)) false = true ↔ _
    rw [hD0_call (n * 2 + 1) hk']
    have hget : (batchD0 n hn)[n * 2 + 1]'hk' = ⟨.not, [wHasRank1 n]⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega),
        List.getElem_append_left (by simp; try omega), List.getElem_append_right (by simp)]
      simp
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_true']
    constructor
    · intro hf i
      cases hz : mIsRank1 (Ms i)
      · rfl
      · have h1 := hHasRank1.mpr ⟨i, hz⟩; rw [hf] at h1; exact absurd h1 Bool.false_ne_true
    · intro hall
      cases hw : W.getD (wHasRank1 n) false
      · rfl
      · rcases hHasRank1.mp hw with ⟨i, hi⟩; rw [hall i] at hi; exact absurd hi Bool.false_ne_true
  have hIsFirstGlobal (i : Fin n) : W.getD (wIsFirstGlobal n i) false = true ↔
      mIsRank1 (Ms i) = true ∧ ∀ j : Fin n, j.val < i.val → mIsRank1 (Ms j) = false := by
    have hk' : n * 2 + 2 + i.val < (batchD0 n hn).length := by rw [len_batchD0]; have := i.isLt; omega
    change W.getD (offD0 n + (n * 2 + 2 + i.val)) false = true ↔ _
    rw [hD0_call (n * 2 + 2 + i.val) hk']
    have hget : (batchD0 n hn)[n * 2 + 2 + i.val]'hk' =
        ⟨.and, wIsRank1 n i :: (List.finRange i.val).map (fun k => wNotRank1 n ⟨k.val, by omega⟩)⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp; try omega),
        List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hsub : n * 2 + 2 + i.val - (n * 2 + 2) = i.val := by omega
      simp [hsub]
    rw [hget, gateOp_and_iff]
    simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_finRange, true_and, forall_eq_or_imp,
      hIsRank1]
    constructor
    · rintro ⟨hr, hall⟩
      refine ⟨hr, fun j hj => ?_⟩
      have h1 := hall _ ⟨wNotRank1 n j, ⟨⟨j.val, hj⟩, rfl⟩, rfl⟩
      rw [hNotRank1, Bool.not_eq_true'] at h1; exact h1
    · rintro ⟨hr, hall⟩
      refine ⟨hr, ?_⟩
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [hNotRank1, hall ⟨k.val, by omega⟩ k.isLt]; rfl
  have hIsLastGlobal (i : Fin n) : W.getD (wIsLastGlobal n i) false = true ↔
      mIsRank1 (Ms i) = true ∧ ∀ j : Fin n, i.val < j.val → mIsRank1 (Ms j) = false := by
    have hk' : n * 2 + 2 + n + i.val < (batchD0 n hn).length := by rw [len_batchD0]; have := i.isLt; omega
    change W.getD (offD0 n + (n * 2 + 2 + n + i.val)) false = true ↔ _
    rw [hD0_call (n * 2 + 2 + n + i.val) hk']
    have hget : (batchD0 n hn)[n * 2 + 2 + n + i.val]'hk' =
        ⟨.and, wIsRank1 n i :: (List.finRange (n - (i.val + 1))).map (fun t => wNotRank1 n ⟨i.val + 1 + t.val, by omega⟩)⟩ := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hsub : n * 2 + 2 + n + i.val - (n * 2 + 2 + n) = i.val := by omega
      simp [hsub]
    rw [hget, gateOp_and_iff]
    simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_finRange, true_and, forall_eq_or_imp,
      hIsRank1]
    constructor
    · rintro ⟨hr, hall⟩
      refine ⟨hr, fun j hj => ?_⟩
      have ht : j.val - (i.val + 1) < n - (i.val + 1) := by have := j.isLt; omega
      have h1 := hall _ ⟨wNotRank1 n j, ⟨⟨j.val - (i.val + 1), ht⟩, congrArg (wNotRank1 n) (Fin.ext (by dsimp; omega))⟩, rfl⟩
      rw [hNotRank1, Bool.not_eq_true'] at h1; exact h1
    · rintro ⟨hr, hall⟩
      refine ⟨hr, ?_⟩
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      rw [hNotRank1, hall ⟨i.val + 1 + t.val, by omega⟩ (by dsimp; omega)]; rfl
  have hDyadMask (l : Fin (Lmax n)) (i : Fin n) :
      W.getD (wDyadMask n l i) false = true ↔
        mIsRank1 (Ms i) = true ∧
        if i.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val then
          ∀ k : Fin n, i.val < k.val → k.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val → mIsRank1 (Ms k) = false
        else
          ∀ k : Fin n, (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val ≤ k.val → k.val < i.val → mIsRank1 (Ms k) = false := by
    have hli : l.val * n + i.val < Lmax n * n := by
      calc l.val * n + i.val < l.val * n + n := Nat.add_lt_add_left i.isLt _
        _ = (l.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ Lmax n * n := Nat.mul_le_mul_right n l.isLt
    have hk' : n * 2 + 2 + n + n + (l.val * n + i.val) < (batchD0 n hn).length := by
      rw [len_batchD0]; omega
    change W.getD (offD0 n + (n * 2 + 2 + n + n + (l.val * n + i.val))) false = true ↔ _
    rw [hD0_call (n * 2 + 2 + n + n + (l.val * n + i.val)) hk']
    have hget : (batchD0 n hn)[n * 2 + 2 + n + n + (l.val * n + i.val)]'hk' = dyadMaskGate n l i := by
      unfold batchD0 at hk' ⊢
      rw [List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hsub : n * 2 + 2 + n + n + (l.val * n + i.val) - (n * 2 + 2 + n + n) = l.val * n + i.val := by omega
      simp only [hsub, List.getElem_ofFn]
      have hd : (⟨(l.val * n + i.val) / n, div_lt_of_lt_mul_r hli⟩ : Fin (Lmax n)) = l := Fin.ext (by dsimp; rw [Nat.mul_comm l.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, Nat.add_zero])
      have hm : (⟨(l.val * n + i.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext (by dsimp; rw [Nat.mul_comm l.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt])
      rw [hd, hm]
    rw [hget]
    unfold dyadMaskGate
    dsimp only
    split_ifs with hlt
    · rw [gateOp_and_iff]
      simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_finRange, true_and, forall_eq_or_imp,
        hIsRank1]
      constructor
      · rintro ⟨hr, hall⟩
        refine ⟨hr, fun k hk1 hk2 => ?_⟩
        have ht : k.val - (i.val + 1) < min n ((i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val) - (i.val + 1) := by
          have := k.isLt; omega
        have h1 := hall _ ⟨wNotRank1 n k, ⟨⟨k.val - (i.val + 1), ht⟩, congrArg (wNotRank1 n) (Fin.ext (by dsimp; omega))⟩, rfl⟩
        rw [hNotRank1, Bool.not_eq_true'] at h1; exact h1
      · rintro ⟨hr, hall⟩
        refine ⟨hr, ?_⟩
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hNotRank1, hall ⟨i.val + 1 + t.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)]; rfl
    · rw [gateOp_and_iff]
      simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_finRange, true_and, forall_eq_or_imp,
        hIsRank1]
      constructor
      · rintro ⟨hr, hall⟩
        refine ⟨hr, fun k hk1 hk2 => ?_⟩
        have ht : k.val - ((i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val) <
            i.val - ((i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val) := by omega
        have h1 := hall _ ⟨wNotRank1 n k, ⟨⟨_, ht⟩, congrArg (wNotRank1 n) (Fin.ext (by dsimp; omega))⟩, rfl⟩
        rw [hNotRank1, Bool.not_eq_true'] at h1; exact h1
      · rintro ⟨hr, hall⟩
        refine ⟨hr, ?_⟩
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hNotRank1, hall ⟨_, by omega⟩ (by dsimp; omega) (by dsimp; omega)]; rfl
  have hTr2 (p : ℕ) (hp : p ≤ n) : W.getD (wTr2 n hn p) false = decide ((prefTrans Ms p).val = 2) := by
    cases p with
    | zero => unfold wTr2; rw [if_pos rfl, hFalse, prefTrans_zero]; rfl
    | succ q =>
      have hk' : q < (batchD1 n).length := by rw [len_batchD1]; omega
      have hb := hbatch g10 (batchD1 n) (offD1 n hn) q hk' hsp10 o10 (closed_D1 n hn)
      simp only [wTr2, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      rw [hb]
      have hget : (batchD1 n)[q]'hk' = ⟨.and, [wNotTr0 n (q + 1), wNotTr1 n (q + 1)]⟩ := by
        unfold batchD1 at hk' ⊢; rw [List.getElem_ofFn]
      rw [hget]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, hNotTr0 q (by omega), hNotTr1 q (by omega)]
      have hlt3 := (prefTrans Ms (q + 1)).isLt
      rcases (show (prefTrans Ms (q + 1)).val = 0 ∨ (prefTrans Ms (q + 1)).val = 1 ∨
          (prefTrans Ms (q + 1)).val = 2 by omega) with h | h | h <;> simp [h]
  have hSignEq (p : ℕ) (hp : p ≤ n) (s : Bool) : W.getD (wSignEq n p s) false = decide (prefSign Ms p = s) := by
    unfold wSignEq
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, hSignEven p hp]; cases prefSign Ms p <;> rfl
    · simp only [↓reduceIte, hSignOdd p hp]; cases prefSign Ms p <;> rfl
  have hTrEq (p : ℕ) (hp : p ≤ n) (t : Fin 3) : W.getD (wTrEq n hn p t) false = decide (prefTrans Ms p = t) := by
    unfold wTrEq; fin_cases t <;> (apply Bool.eq_iff_iff.mpr; simp only [hTr0 p hp, hTr1 p hp, hTr2 p hp, decide_eq_true_eq, Fin.ext_iff])
  have hPEq (p : ℕ) (hp : p ≤ n) (s : Bool) (t : Fin 3) :
      W.getD (wPEq n hn p s t) false = (decide (prefSign Ms p = s) && decide (prefTrans Ms p = t)) := by
    have hk' : p * 6 + stIdx s t < (batchD2 n hn).length := by
      rw [len_batchD2]; have := stIdx_lt s t; omega
    have hb := hbatch g11 (batchD2 n hn) (offD2 n hn) (p * 6 + stIdx s t) hk' hsp11 o11 (closed_D2 n hn)
    unfold wPEq; rw [hb]
    have hget : (batchD2 n hn)[p * 6 + stIdx s t]'hk' = ⟨.and, [wSignEq n p s, wTrEq n hn p t]⟩ := by
      unfold batchD2 at hk' ⊢; rw [List.getElem_ofFn]
      have hs := stIdx_lt s t
      have hd : (p * 6 + stIdx s t) / 6 = p := by omega
      have hm : (p * 6 + stIdx s t) % 6 = stIdx s t := by omega
      have hs_eq : decide (3 ≤ stIdx s t) = s := stIdx_s s t
      have ht_eq : (⟨stIdx s t % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = t := stIdx_t s t
      simp only [hd, hm, hs_eq, ht_eq]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hSignEq p hp s, hTrEq p hp t]
  have hPC (i : Fin n) (s : Bool) (t c : Fin 3) :
      W.getD (wPC n hn i s t c) false =
        (decide (prefSign Ms i.val = s) && decide (prefTrans Ms i.val = t) && decide (mCol (Ms i) = c)) := by
    have hk' : i.val * 18 + tupIdx s t c < (batchD3 n hn).length := by
      rw [len_batchD3]; have := i.isLt; have := tupIdx_lt s t c; omega
    have hb := hbatch g12 (batchD3 n hn) (offD3 n hn) (i.val * 18 + tupIdx s t c) hk' hsp12 o12 (closed_D3 n hn)
    unfold wPC; rw [hb]
    have hget : (batchD3 n hn)[i.val * 18 + tupIdx s t c]'hk' = ⟨.and, [wPEq n hn i.val s t, wColVec n i c]⟩ := by
      unfold batchD3 at hk' ⊢
      have hlt1 : i.val * 18 + tupIdx s t c < n * 18 := by have := i.isLt; have := tupIdx_lt s t c; omega
      rw [List.getElem_append_left (by simp [hlt1]), List.getElem_ofFn]
      have htl := tupIdx_lt s t c
      have hd : (i.val * 18 + tupIdx s t c) / 18 = i.val := by omega
      have hm : (i.val * 18 + tupIdx s t c) % 18 = tupIdx s t c := by omega
      have hs_eq : decide (9 ≤ tupIdx s t c) = s := tupIdx_s s t c
      have ht_eq : (⟨(tupIdx s t c % 9) / 3, by omega⟩ : Fin 3) = t := tupIdx_t s t c
      have hc_eq : (⟨tupIdx s t c % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = c := tupIdx_v s t c
      simp only [hd, hm, hs_eq, ht_eq, hc_eq, Fin.eta]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hPEq i.val (le_of_lt i.isLt) s t, hColVec]
  have hPR (i : Fin n) (s : Bool) (t r : Fin 3) :
      W.getD (wPR n hn i s t r) false =
        (decide (prefSign Ms i.val = s) && decide (prefTrans Ms i.val = t) && decide (mRow (Ms i) = r)) := by
    have hk' : n * 18 + (i.val * 18 + tupIdx s t r) < (batchD3 n hn).length := by
      rw [len_batchD3]; have := i.isLt; have := tupIdx_lt s t r; omega
    have hb := hbatch g12 (batchD3 n hn) (offD3 n hn) (n * 18 + (i.val * 18 + tupIdx s t r)) hk' hsp12 o12 (closed_D3 n hn)
    change W.getD (offD3 n hn + (n * 18 + (i.val * 18 + tupIdx s t r))) false = _
    rw [hb]
    have hget : (batchD3 n hn)[n * 18 + (i.val * 18 + tupIdx s t r)]'hk' =
        ⟨.and, [wPEq n hn i.val s t, wRowVec n i r]⟩ := by
      unfold batchD3 at hk' ⊢
      rw [List.getElem_append_right (by simp; try omega)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
      have htl := tupIdx_lt s t r
      have hd : (i.val * 18 + tupIdx s t r) / 18 = i.val := by omega
      have hm : (i.val * 18 + tupIdx s t r) % 18 = tupIdx s t r := by omega
      have hs_eq : decide (9 ≤ tupIdx s t r) = s := tupIdx_s s t r
      have ht_eq : (⟨(tupIdx s t r % 9) / 3, by omega⟩ : Fin 3) = t := tupIdx_t s t r
      have hr_eq : (⟨tupIdx s t r % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = r := tupIdx_v s t r
      simp only [hd, hm, hs_eq, ht_eq, hr_eq, Fin.eta]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hPEq i.val (le_of_lt i.isLt) s t, hRowVec]
  have hTildeC (i : Fin n) (v : Fin 3) : W.getD (wTildeC n hn i v) false = decide (tildeC Ms i = v) := by
    have hk' : i.val * 3 + v.val < (batchD4 n hn).length := by
      rw [len_batchD4]; have := i.isLt; have := v.isLt; omega
    have hb := hbatch g13 (batchD4 n hn) (offD4 n hn) (i.val * 3 + v.val) hk' hsp13 o13 (closed_D4 n hn)
    unfold wTildeC; rw [hb]
    have hget : (batchD4 n hn)[i.val * 3 + v.val]'hk' =
        ⟨.or, (allMatTuples.filter (fun q => decide (gActC q.1 q.2.1 q.2.2 = v))).map
          (fun q => wPC n hn i q.1 q.2.1 q.2.2)⟩ := by
      unfold batchD4 at hk' ⊢
      have hlt1 : i.val * 3 + v.val < n * 3 := by have := i.isLt; have := v.isLt; omega
      rw [List.getElem_append_left (by simp [hlt1]), List.getElem_ofFn]
      have hd : (i.val * 3 + v.val) / 3 = i.val := by have := v.isLt; omega
      have hm : (i.val * 3 + v.val) % 3 = v.val := by have := v.isLt; omega
      simp only [hd, hm, Fin.eta]
    rw [hget]
    apply Bool.eq_iff_iff.mpr
    simp only [gateOp_or_iff, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨_, ⟨q, ⟨_, hact⟩, rfl⟩, rfl⟩, h1⟩
      rw [hPC] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      unfold tildeC; rw [h1.1.1, h1.1.2, h1.2]; exact hact
    · intro hv
      refine ⟨true, ⟨wPC n hn i (prefSign Ms i.val) (prefTrans Ms i.val) (mCol (Ms i)),
        ⟨(prefSign Ms i.val, prefTrans Ms i.val, mCol (Ms i)),
          ⟨mem_allMatTuples _ _ _, hv⟩, rfl⟩, ?_⟩, rfl⟩
      rw [hPC]; simp
  have hTildeR (i : Fin n) (v : Fin 3) : W.getD (wTildeR n hn i v) false = decide (tildeR Ms i = v) := by
    have hk' : n * 3 + (i.val * 3 + v.val) < (batchD4 n hn).length := by
      rw [len_batchD4]; have := i.isLt; have := v.isLt; omega
    have hb := hbatch g13 (batchD4 n hn) (offD4 n hn) (n * 3 + (i.val * 3 + v.val)) hk' hsp13 o13 (closed_D4 n hn)
    change W.getD (offD4 n hn + (n * 3 + (i.val * 3 + v.val))) false = _
    rw [hb]
    have hget : (batchD4 n hn)[n * 3 + (i.val * 3 + v.val)]'hk' =
        ⟨.or, (allMatTuples.filter (fun q => decide (gActR q.1 q.2.1 q.2.2 = v))).map
          (fun q => wPR n hn i q.1 q.2.1 q.2.2)⟩ := by
      unfold batchD4 at hk' ⊢
      rw [List.getElem_append_right (by simp; try omega)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
      have hd : (i.val * 3 + v.val) / 3 = i.val := by have := v.isLt; omega
      have hm : (i.val * 3 + v.val) % 3 = v.val := by have := v.isLt; omega
      simp only [hd, hm, Fin.eta]
    rw [hget]
    apply Bool.eq_iff_iff.mpr
    simp only [gateOp_or_iff, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨_, ⟨q, ⟨_, hact⟩, rfl⟩, rfl⟩, h1⟩
      rw [hPR] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      unfold tildeR; rw [h1.1.1, h1.1.2, h1.2]; exact hact
    · intro hv
      refine ⟨true, ⟨wPR n hn i (prefSign Ms i.val) (prefTrans Ms i.val) (mRow (Ms i)),
        ⟨(prefSign Ms i.val, prefTrans Ms i.val, mRow (Ms i)),
          ⟨mem_allMatTuples _ _ _, hv⟩, rfl⟩, ?_⟩, rfl⟩
      rw [hPR]; simp
  exact ⟨hHasRank1, hNotHasZero, hNotHasRank1, hIsFirstGlobal, hIsLastGlobal, hDyadMask, hPEq, hTildeC, hTildeR⟩

lemma eval_circuit_correct (T : Fin n → Bool → Bool → Bool) :
    let x := (List.ofFn (fun i : Fin n =>
      [T i false false, T i true false, T i false true, T i true true])).flatten
    (buildCircuit n hn).eval x = true ↔
      mTrace (mProd (List.ofFn (fun i : Fin n => matOf (T i)))) = true := by
  intro x
  let Ms : Fin n → Fin 16 := fun i => matOf (T i)
  rcases input_x_spec n T with ⟨hxlen, hxbit⟩
  change x.length = 4 * n at hxlen
  let g0 : List Gate := []
  let g1 := g0 ++ batchA0 n
  let g2 := g1 ++ batchA1 n
  let g3 := g2 ++ batchA2 n
  let g4 := g3 ++ batchA3 n
  let g5 := g4 ++ secS n
  let g6 := g5 ++ batchB0 n
  let g7 := g6 ++ batchB1 n
  let g8 := g7 ++ batchB2 n
  let g9 := g8 ++ secR n
  let g10 := g9 ++ batchD0 n hn
  let g11 := g10 ++ batchD1 n
  let g12 := g11 ++ batchD2 n hn
  let g13 := g12 ++ batchD3 n hn
  let g14 := g13 ++ batchD4 n hn
  let g15 := g14 ++ batchD5 n hn
  let g16 := g15 ++ batchD6 n hn
  let g17 := g16 ++ batchD7 n hn
  let g18 := g17 ++ batchD8 n hn
  let g19 := g18 ++ batchD9 n hn
  let g20 := g19 ++ batchD10 n hn
  let g21 := g20 ++ batchD11 n hn
  let g22 := g21 ++ batchD12 n hn
  have hfull : fullGates n hn = g22 := fullGates_eq_chain n hn
  have o0 : x.length + g0.length = offA0 n := by simp [g0, hxlen, offA0, I_w]
  have o1 : x.length + g1.length = offA1 n := by simp only [g1, List.length_append, offA1]; rw [← o0]; omega
  have o2 : x.length + g2.length = offA2 n := by simp only [g2, List.length_append, offA2]; rw [← o1]; omega
  have o3 : x.length + g3.length = offA3 n := by simp only [g3, List.length_append, offA3]; rw [← o2]; omega
  have o4 : x.length + g4.length = offS n := by simp only [g4, List.length_append, offS]; rw [← o3]; omega
  have o5 : x.length + g5.length = offB0 n := by simp only [g5, List.length_append, offB0]; rw [← o4]; omega
  have o6 : x.length + g6.length = offB1 n := by simp only [g6, List.length_append, offB1]; rw [← o5]; omega
  have o7 : x.length + g7.length = offB2 n := by simp only [g7, List.length_append, offB2]; rw [← o6]; omega
  have o8 : x.length + g8.length = offR n := by simp only [g8, List.length_append, offR]; rw [← o7]; omega
  have o9 : x.length + g9.length = offD0 n := by simp only [g9, List.length_append, offD0]; rw [← o8]; omega
  have o10 : x.length + g10.length = offD1 n hn := by simp only [g10, List.length_append, offD1]; rw [← o9]; omega
  have o11 : x.length + g11.length = offD2 n hn := by simp only [g11, List.length_append, offD2]; rw [← o10]; omega
  have o12 : x.length + g12.length = offD3 n hn := by simp only [g12, List.length_append, offD3]; rw [← o11]; omega
  have o13 : x.length + g13.length = offD4 n hn := by simp only [g13, List.length_append, offD4]; rw [← o12]; omega
  have o14 : x.length + g14.length = offD5 n hn := by simp only [g14, List.length_append, offD5]; rw [← o13]; omega
  have o15 : x.length + g15.length = offD6 n hn := by simp only [g15, List.length_append, offD6]; rw [← o14]; omega
  have o16 : x.length + g16.length = offD7 n hn := by simp only [g16, List.length_append, offD7]; rw [← o15]; omega
  have o17 : x.length + g17.length = offD8 n hn := by simp only [g17, List.length_append, offD8]; rw [← o16]; omega
  have o18 : x.length + g18.length = offD9 n hn := by simp only [g18, List.length_append, offD9]; rw [← o17]; omega
  have o19 : x.length + g19.length = offD10 n hn := by simp only [g19, List.length_append, offD10]; rw [← o18]; omega
  have o20 : x.length + g20.length = offD11 n hn := by simp only [g20, List.length_append, offD11]; rw [← o19]; omega
  have o21 : x.length + g21.length = offD12 n hn := by simp only [g21, List.length_append, offD12]; rw [← o20]; omega
  have hspl : ∀ (A B : List Gate), (∃ suff, g22 = (A ++ B) ++ suff) → ∃ suff, g22 = A ++ suff := by
    rintro A B ⟨suff, h⟩; exact ⟨B ++ suff, by rw [h, List.append_assoc]⟩
  have hsp21 : ∃ suff, g22 = (g21 ++ batchD12 n hn) ++ suff := ⟨[], by simp [g22]⟩
  have hsp20 : ∃ suff, g22 = (g20 ++ batchD11 n hn) ++ suff := hspl _ _ hsp21
  have hsp19 : ∃ suff, g22 = (g19 ++ batchD10 n hn) ++ suff := hspl _ _ hsp20
  have hsp18 : ∃ suff, g22 = (g18 ++ batchD9 n hn) ++ suff := hspl _ _ hsp19
  have hsp17 : ∃ suff, g22 = (g17 ++ batchD8 n hn) ++ suff := hspl _ _ hsp18
  have hsp16 : ∃ suff, g22 = (g16 ++ batchD7 n hn) ++ suff := hspl _ _ hsp17
  have hsp15 : ∃ suff, g22 = (g15 ++ batchD6 n hn) ++ suff := hspl _ _ hsp16
  have hsp14 : ∃ suff, g22 = (g14 ++ batchD5 n hn) ++ suff := hspl _ _ hsp15
  have hsp13 : ∃ suff, g22 = (g13 ++ batchD4 n hn) ++ suff := hspl _ _ hsp14
  have hsp12 : ∃ suff, g22 = (g12 ++ batchD3 n hn) ++ suff := hspl _ _ hsp13
  have hsp11 : ∃ suff, g22 = (g11 ++ batchD2 n hn) ++ suff := hspl _ _ hsp12
  have hsp10 : ∃ suff, g22 = (g10 ++ batchD1 n) ++ suff := hspl _ _ hsp11
  have hsp9 : ∃ suff, g22 = (g9 ++ batchD0 n hn) ++ suff := hspl _ _ hsp10
  have hsp8 : ∃ suff, g22 = (g8 ++ secR n) ++ suff := hspl _ _ hsp9
  have hsp7 : ∃ suff, g22 = (g7 ++ batchB2 n) ++ suff := hspl _ _ hsp8
  have hsp6 : ∃ suff, g22 = (g6 ++ batchB1 n) ++ suff := hspl _ _ hsp7
  have hsp5 : ∃ suff, g22 = (g5 ++ batchB0 n) ++ suff := hspl _ _ hsp6
  have hsp4 : ∃ suff, g22 = (g4 ++ secS n) ++ suff := hspl _ _ hsp5
  have hsp3 : ∃ suff, g22 = (g3 ++ batchA3 n) ++ suff := hspl _ _ hsp4
  have hsp2 : ∃ suff, g22 = (g2 ++ batchA2 n) ++ suff := hspl _ _ hsp3
  have hsp1 : ∃ suff, g22 = (g1 ++ batchA1 n) ++ suff := hspl _ _ hsp2
  have hsp0 : ∃ suff, g22 = (g0 ++ batchA0 n) ++ suff := hspl _ _ hsp1
  change (evalWires (fullGates n hn) x).getD (wOut n hn) false = true ↔ _
  rw [hfull]
  suffices hW_main : ∀ W : List Bool, W = evalWires g22 x →
      (W.getD (wOut n hn) false = true ↔ mTrace (mProd (List.ofFn (fun i : Fin n => matOf (T i)))) = true) by
    exact hW_main (evalWires g22 x) rfl
  intro W hW_eq
  have hagree : ∀ (pref suff : List Gate) (off : ℕ) (w : ℕ),
      g22 = pref ++ suff → x.length + pref.length = off → w < off →
      W.getD w false = (evalWires pref x).getD w false :=
    fun pref suff off w hgs hoff hw => by rw [hW_eq]; exact evalWires_agree_in_full g22 pref suff x off w hgs hoff hw
  have hbatch : ∀ (prev batch : List Gate) (off : ℕ) (k : ℕ) (hk : k < batch.length),
      (∃ suff, g22 = (prev ++ batch) ++ suff) →
      x.length + prev.length = off →
      (∀ g ∈ batch, ∀ j ∈ g.inputs, j < off) →
      W.getD (off + k) false =
        (batch[k]).op.eval ((batch[k]).inputs.map (fun j => W.getD j false)) :=
    fun prev batch off k hk hsp hoff hcl => by rw [hW_eq]; exact evalWires_batch_in_full g22 prev batch x off k hk hsp hoff hcl
  rcases eval_circuit_part1 n hn T Ms rfl W (by rw [hfull]; exact hW_eq) with
    ⟨hHasRank1, hNotHasZero, hNotHasRank1, hIsFirstGlobal, hIsLastGlobal, hDyadMask, hPEq, hTildeC, hTildeR⟩
  have hD5_call (k : ℕ) (hk : k < (batchD5 n hn).length) :
      W.getD (offD5 n hn + k) false =
        ((batchD5 n hn)[k]'hk).op.eval (((batchD5 n hn)[k]'hk).inputs.map (fun j => W.getD j false)) :=
    hbatch g14 (batchD5 n hn) (offD5 n hn) k hk hsp14 o14 (closed_D5 n hn)
  have hFirstCTag (i : Fin n) (v : Fin 3) :
      W.getD (wFirstCTag n hn i v) false = true ↔
        mIsRank1 (Ms i) = true ∧ (∀ j : Fin n, j.val < i.val → mIsRank1 (Ms j) = false) ∧ tildeC Ms i = v := by
    have hk' : i.val * 3 + v.val < (batchD5 n hn).length := by
      rw [len_batchD5]; have := i.isLt; have := v.isLt; omega
    unfold wFirstCTag; rw [hD5_call (i.val * 3 + v.val) hk']
    have hget : (batchD5 n hn)[i.val * 3 + v.val]'hk' = ⟨.and, [wIsFirstGlobal n i, wTildeC n hn i v]⟩ := by
      unfold batchD5 at hk' ⊢
      have hlt1 : i.val * 3 + v.val < n * 3 := by have := i.isLt; have := v.isLt; omega
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp [hlt1]), List.getElem_ofFn]
      have hd : (i.val * 3 + v.val) / 3 = i.val := by have := v.isLt; omega
      have hm : (i.val * 3 + v.val) % 3 = v.val := by have := v.isLt; omega
      simp only [hd, hm, Fin.eta]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true, hIsFirstGlobal, hTildeC, decide_eq_true_eq, and_assoc]
  have hLastRTag (i : Fin n) (v : Fin 3) :
      W.getD (wLastRTag n hn i v) false = true ↔
        mIsRank1 (Ms i) = true ∧ (∀ j : Fin n, i.val < j.val → mIsRank1 (Ms j) = false) ∧ tildeR Ms i = v := by
    have hk' : n * 3 + (i.val * 3 + v.val) < (batchD5 n hn).length := by
      rw [len_batchD5]; have := i.isLt; have := v.isLt; omega
    change W.getD (offD5 n hn + (n * 3 + (i.val * 3 + v.val))) false = true ↔ _
    rw [hD5_call (n * 3 + (i.val * 3 + v.val)) hk']
    have hget : (batchD5 n hn)[n * 3 + (i.val * 3 + v.val)]'hk' = ⟨.and, [wIsLastGlobal n i, wTildeR n hn i v]⟩ := by
      unfold batchD5 at hk' ⊢
      rw [List.getElem_append_left (by simp; have := i.isLt; have := v.isLt; omega),
        List.getElem_append_right (by simp; try omega)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
      have hd : (i.val * 3 + v.val) / 3 = i.val := by have := v.isLt; omega
      have hm : (i.val * 3 + v.val) % 3 = v.val := by have := v.isLt; omega
      simp only [hd, hm, Fin.eta]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true, hIsLastGlobal, hTildeR, decide_eq_true_eq, and_assoc]
  have hDyadTag (l : Fin (Lmax n)) (i : Fin n) (v : Fin 3) :
      W.getD (wDyadTag n hn l i v) false = true ↔
        W.getD (wDyadMask n l i) false = true ∧
        if i.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val then tildeR Ms i = v else tildeC Ms i = v := by
    have hli : l.val * n + i.val < Lmax n * n := by
      calc l.val * n + i.val < l.val * n + n := Nat.add_lt_add_left i.isLt _
        _ = (l.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ Lmax n * n := Nat.mul_le_mul_right n l.isLt
    have hk' : n * 3 + n * 3 + ((l.val * n + i.val) * 3 + v.val) < (batchD5 n hn).length := by
      rw [len_batchD5]; have := v.isLt; omega
    change W.getD (offD5 n hn + (n * 3 + n * 3 + ((l.val * n + i.val) * 3 + v.val))) false = true ↔ _
    rw [hD5_call (n * 3 + n * 3 + ((l.val * n + i.val) * 3 + v.val)) hk']
    have hget : (batchD5 n hn)[n * 3 + n * 3 + ((l.val * n + i.val) * 3 + v.val)]'hk' =
        (if i.val < (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val then
          ⟨.and, [wDyadMask n l i, wTildeR n hn i v]⟩
        else ⟨.and, [wDyadMask n l i, wTildeC n hn i v]⟩) := by
      unfold batchD5 at hk' ⊢
      rw [List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
      have hd1 : ((l.val * n + i.val) * 3 + v.val) / 3 = l.val * n + i.val := by have := v.isLt; omega
      have hm1 : ((l.val * n + i.val) * 3 + v.val) % 3 = v.val := by have := v.isLt; omega
      have hd2 : (l.val * n + i.val) / n = l.val := by
        rw [Nat.mul_comm l.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
      have hm2 : (l.val * n + i.val) % n = i.val := by
        rw [Nat.mul_comm l.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
      simp only [hd1, hm1, hd2, hm2, Fin.eta]
    rw [hget]
    split_ifs <;>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true, hTildeR, hTildeC, decide_eq_true_eq]
  have hD6_call (k : ℕ) (hk : k < (batchD6 n hn).length) :
      W.getD (offD6 n hn + k) false =
        ((batchD6 n hn)[k]'hk).op.eval (((batchD6 n hn)[k]'hk).inputs.map (fun j => W.getD j false)) :=
    hbatch g15 (batchD6 n hn) (offD6 n hn) k hk hsp15 o15 (closed_D6 n hn)
  have hFirstC (v : Fin 3) : W.getD (wFirstC n hn v) false = true ↔
      ∃ i : Fin n, mIsRank1 (Ms i) = true ∧ (∀ j : Fin n, j.val < i.val → mIsRank1 (Ms j) = false) ∧ tildeC Ms i = v := by
    have hk' : v.val < (batchD6 n hn).length := by rw [len_batchD6]; have := v.isLt; omega
    unfold wFirstC; rw [hD6_call v.val hk']
    have hget : (batchD6 n hn)[v.val]'hk' = ⟨.or, List.ofFn (fun i : Fin n => wFirstCTag n hn i v)⟩ := by
      unfold batchD6 at hk' ⊢
      rw [List.getElem_append_left (by simp; have := v.isLt; omega),
        List.getElem_append_left (by simp; have := v.isLt; omega),
        List.getElem_append_left (by simp), List.getElem_ofFn]
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, h1⟩; exact ⟨i, (hFirstCTag i v).mp h1⟩
    · rintro ⟨i, hi⟩; exact ⟨true, ⟨wFirstCTag n hn i v, ⟨i, rfl⟩, (hFirstCTag i v).mpr hi⟩, rfl⟩
  have hLastR (v : Fin 3) : W.getD (wLastR n hn v) false = true ↔
      ∃ i : Fin n, mIsRank1 (Ms i) = true ∧ (∀ j : Fin n, i.val < j.val → mIsRank1 (Ms j) = false) ∧ tildeR Ms i = v := by
    have hk' : 3 + v.val < (batchD6 n hn).length := by rw [len_batchD6]; have := v.isLt; omega
    change W.getD (offD6 n hn + (3 + v.val)) false = true ↔ _
    rw [hD6_call (3 + v.val) hk']
    have hget : (batchD6 n hn)[3 + v.val]'hk' = ⟨.or, List.ofFn (fun i : Fin n => wLastRTag n hn i v)⟩ := by
      unfold batchD6 at hk' ⊢
      rw [List.getElem_append_left (by simp; have := v.isLt; omega),
        List.getElem_append_left (by simp; have := v.isLt; omega),
        List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn]
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, h1⟩; exact ⟨i, (hLastRTag i v).mp h1⟩
    · rintro ⟨i, hi⟩; exact ⟨true, ⟨wLastRTag n hn i v, ⟨i, rfl⟩, (hLastRTag i v).mpr hi⟩, rfl⟩
  have hLeftVec (m : Fin n) (v : Fin 3) : W.getD (wLeftVec n hn m v) false = true ↔
      0 < m.val ∧
      let l := v2 m.val
      let lo := m.val - 2 ^ l
      ∃ i : Fin n, lo ≤ i.val ∧ i.val < m.val ∧ mIsRank1 (Ms i) = true ∧
        (∀ k : Fin n, i.val < k.val → k.val < m.val → mIsRank1 (Ms k) = false) ∧ tildeR Ms i = v := by
    have hk' : 6 + (m.val * 3 + v.val) < (batchD6 n hn).length := by
      rw [len_batchD6]; have := m.isLt; have := v.isLt; omega
    change W.getD (offD6 n hn + (6 + (m.val * 3 + v.val))) false = true ↔ _
    rw [hD6_call (6 + (m.val * 3 + v.val)) hk']
    have hget : (batchD6 n hn)[6 + (m.val * 3 + v.val)]'hk' = leftVecGate n hn m v := by
      unfold batchD6 at hk' ⊢
      rw [List.getElem_append_left (by simp; have := m.isLt; have := v.isLt; omega),
        List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn]
      have hsub : 6 + (m.val * 3 + v.val) - (3 + 3) = m.val * 3 + v.val := by omega
      simp only [hsub, List.getElem_ofFn]
      have hd : (⟨(m.val * 3 + v.val) / 3, div_lt_of_lt_mul_r (by have := m.isLt; have := v.isLt; omega)⟩ : Fin n) = m := Fin.ext (by have := v.isLt; dsimp; omega)
      have hm : (⟨(m.val * 3 + v.val) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = v := Fin.ext (by have := v.isLt; dsimp; omega)
      rw [hd, hm]
    rw [hget]
    unfold leftVecGate
    by_cases hm : 0 < m.val
    · rw [dif_pos hm, gateOp_or_iff]
      set l : Fin (Lmax n) := ⟨v2 m.val, v2_lt_log2_succ n m.val hm m.isLt⟩
      set lo := m.val - 2 ^ l.val
      rcases v2_spec m.val hm with ⟨⟨q, hq⟩, hodd⟩
      have hq_eq : q = m.val / 2 ^ l.val := by
        rw [hq, Nat.mul_div_cancel_left q (Nat.two_pow_pos _)]
      have hq_odd : q % 2 = 1 := by rw [hq_eq]; exact hodd
      set b := q / 2
      have hq_2b : q = 2 * b + 1 := by omega
      have hm_eq : m.val = (2 * b + 1) * 2 ^ l.val := by rw [hq, hq_2b, Nat.mul_comm]
      have hle_m : 2 ^ l.val ≤ m.val := Nat.le_of_dvd hm ⟨q, hq⟩
      have hlo_le : lo ≤ m.val := Nat.sub_le _ _
      have hlo_eq : lo = b * 2 ^ (l.val + 1) := by
        dsimp only [lo]; rw [hm_eq, Nat.pow_succ]; ring_nf; omega
      have hmid_of (i : Fin n) (h1 : lo ≤ i.val) (h2 : i.val < m.val) :
          (i.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val = m.val := by
        have hdiv : i.val / 2 ^ (l.val + 1) = b := by
          have hge : b * 2 ^ (l.val + 1) ≤ i.val := by rwa [← hlo_eq]
          have hlt : i.val < (b + 1) * 2 ^ (l.val + 1) := by
            have : m.val ≤ (b + 1) * 2 ^ (l.val + 1) := by
              rw [hm_eq, Nat.pow_succ]; ring_nf; omega
            omega
          have hpos : 0 < 2 ^ (l.val + 1) := Nat.two_pow_pos _
          have hle1 : b ≤ i.val / 2 ^ (l.val + 1) := (Nat.le_div_iff_mul_le hpos).mpr hge
          have hlt2 : i.val / 2 ^ (l.val + 1) < b + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hlt
          omega
        rw [hdiv, ← hlo_eq]; dsimp only [lo]; omega
      simp only [List.mem_map, List.mem_finRange, true_and, hm]
      constructor
      · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, h1⟩
        have htlt : t.val < m.val - lo := t.isLt
        have hmlt : m.val < n := m.isLt
        let i : Fin n := ⟨lo + t.val, by omega⟩
        have hi1 : lo ≤ i.val := by dsimp [i]; omega
        have hi2 : i.val < m.val := by dsimp [i]; omega
        have hmid := hmid_of i hi1 hi2
        rw [hDyadTag l i v, hmid, if_pos hi2, hDyadMask l i, hmid, if_pos hi2] at h1
        exact ⟨i, hi1, hi2, h1.1.1, h1.1.2, h1.2⟩
      · rintro ⟨i, hi1, hi2, hri, hleft, hr⟩
        have hi1' : lo ≤ i.val := hi1
        have hmid := hmid_of i hi1' hi2
        let t : Fin (m.val - lo) := ⟨i.val - lo, by omega⟩
        have htlt : t.val < m.val - lo := t.isLt
        have hmlt : m.val < n := m.isLt
        have hi_eq : (⟨lo + t.val, by omega⟩ : Fin n) = i := by
          apply Fin.ext; dsimp [t]; omega
        refine ⟨true, ⟨wDyadTag n hn l i v, ⟨t, by rw [hi_eq]⟩, ?_⟩, rfl⟩
        rw [hDyadTag l i v, hmid, if_pos hi2, hDyadMask l i, hmid, if_pos hi2]
        exact ⟨⟨hri, hleft⟩, hr⟩
    · rw [dif_neg hm]; simp [hm, GateOp.eval]
  have hRightVec (m : Fin n) (v : Fin 3) : W.getD (wRightVec n hn m v) false = true ↔
      0 < m.val ∧
      let l := v2 m.val
      let hi := min n (m.val + 2 ^ l)
      ∃ j : Fin n, m.val ≤ j.val ∧ j.val < hi ∧ mIsRank1 (Ms j) = true ∧
        (∀ k : Fin n, m.val ≤ k.val → k.val < j.val → mIsRank1 (Ms k) = false) ∧ tildeC Ms j = v := by
    have hk' : 6 + n * 3 + (m.val * 3 + v.val) < (batchD6 n hn).length := by
      rw [len_batchD6]; have := m.isLt; have := v.isLt; omega
    change W.getD (offD6 n hn + (6 + n * 3 + (m.val * 3 + v.val))) false = true ↔ _
    rw [hD6_call (6 + n * 3 + (m.val * 3 + v.val)) hk']
    have hget : (batchD6 n hn)[6 + n * 3 + (m.val * 3 + v.val)]'hk' = rightVecGate n hn m v := by
      unfold batchD6 at hk' ⊢
      rw [List.getElem_append_right (by simp; try omega)]
      simp only [List.length_append, List.length_ofFn]
      have hsub : 6 + n * 3 + (m.val * 3 + v.val) - (3 + 3 + n * 3) = m.val * 3 + v.val := by omega
      simp only [hsub, List.getElem_ofFn]
      have hd : (⟨(m.val * 3 + v.val) / 3, div_lt_of_lt_mul_r (by have := m.isLt; have := v.isLt; omega)⟩ : Fin n) = m := Fin.ext (by have := v.isLt; dsimp; omega)
      have hm : (⟨(m.val * 3 + v.val) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = v := Fin.ext (by have := v.isLt; dsimp; omega)
      rw [hd, hm]
    rw [hget]
    unfold rightVecGate
    by_cases hm : 0 < m.val
    · rw [dif_pos hm, gateOp_or_iff]
      set l : Fin (Lmax n) := ⟨v2 m.val, v2_lt_log2_succ n m.val hm m.isLt⟩
      set hi := min n (m.val + 2 ^ l.val)
      rcases v2_spec m.val hm with ⟨⟨q, hq⟩, hodd⟩
      have hq_eq : q = m.val / 2 ^ l.val := by
        rw [hq, Nat.mul_div_cancel_left q (Nat.two_pow_pos _)]
      have hq_odd : q % 2 = 1 := by rw [hq_eq]; exact hodd
      set b := q / 2
      have hq_2b : q = 2 * b + 1 := by omega
      have hm_eq : m.val = (2 * b + 1) * 2 ^ l.val := by rw [hq, hq_2b, Nat.mul_comm]
      have hmid_of (j : Fin n) (h1 : m.val ≤ j.val) (h2 : j.val < hi) :
          (j.val / 2 ^ (l.val + 1)) * 2 ^ (l.val + 1) + 2 ^ l.val = m.val := by
        have hdiv : j.val / 2 ^ (l.val + 1) = b := by
          have hge : b * 2 ^ (l.val + 1) ≤ j.val := by
            have : b * 2 ^ (l.val + 1) ≤ m.val := by rw [hm_eq, Nat.pow_succ]; ring_nf; omega
            omega
          have hlt : j.val < (b + 1) * 2 ^ (l.val + 1) := by
            have : hi ≤ (b + 1) * 2 ^ (l.val + 1) := by
              have : m.val + 2 ^ l.val = (b + 1) * 2 ^ (l.val + 1) := by
                rw [hm_eq, Nat.pow_succ]; ring
              omega
            omega
          have hpos : 0 < 2 ^ (l.val + 1) := Nat.two_pow_pos _
          have hle1 : b ≤ j.val / 2 ^ (l.val + 1) := (Nat.le_div_iff_mul_le hpos).mpr hge
          have hlt2 : j.val / 2 ^ (l.val + 1) < b + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hlt
          omega
        rw [hdiv, hm_eq, Nat.pow_succ]; ring
      have hm_le_hi : m.val ≤ hi := le_min (le_of_lt m.isLt) (Nat.le_add_right _ _)
      have hhi_le_n : hi ≤ n := Nat.min_le_left _ _
      simp only [List.mem_map, List.mem_finRange, true_and, hm]
      constructor
      · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, h1⟩
        have htlt : t.val < hi - m.val := t.isLt
        let j : Fin n := ⟨m.val + t.val, by omega⟩
        have hj1 : m.val ≤ j.val := by dsimp [j]; omega
        have hj2 : j.val < hi := by dsimp [j]; omega
        have hmid := hmid_of j hj1 hj2
        have hnot : ¬ j.val < m.val := by omega
        rw [hDyadTag l j v, hmid, if_neg hnot, hDyadMask l j, hmid, if_neg hnot] at h1
        exact ⟨j, hj1, hj2, h1.1.1, h1.1.2, h1.2⟩
      · rintro ⟨j, hj1, hj2, hrj, hright, hc⟩
        have hj2' : j.val < hi := hj2
        have hmid := hmid_of j hj1 hj2'
        have hnot : ¬ j.val < m.val := by omega
        let t : Fin (hi - m.val) := ⟨j.val - m.val, by omega⟩
        have htlt : t.val < hi - m.val := t.isLt
        have hj_eq : (⟨m.val + t.val, by omega⟩ : Fin n) = j := by
          apply Fin.ext; dsimp [t]; omega
        refine ⟨true, ⟨wDyadTag n hn l j v, ⟨t, by rw [hj_eq]⟩, ?_⟩, rfl⟩
        rw [hDyadTag l j v, hmid, if_neg hnot, hDyadMask l j, hmid, if_neg hnot]
        exact ⟨⟨hrj, hright⟩, hc⟩
    · rw [dif_neg hm]; simp [hm, GateOp.eval]
  have hD7_call (k : ℕ) (hk : k < (batchD7 n hn).length) :
      W.getD (offD7 n hn + k) false =
        ((batchD7 n hn)[k]'hk).op.eval (((batchD7 n hn)[k]'hk).inputs.map (fun j => W.getD j false)) :=
    hbatch g16 (batchD7 n hn) (offD7 n hn) k hk hsp16 o16 (closed_D7 n hn)
  have hBadTriple (m : Fin n) (k : Fin 3) :
      W.getD (offD7 n hn + (m.val * 3 + k.val)) false = true ↔
        match k.val with
        | 0 => W.getD (wLeftVec n hn m ⟨0, by decide⟩) false = true ∧ W.getD (wRightVec n hn m ⟨1, by decide⟩) false = true
        | 1 => W.getD (wLeftVec n hn m ⟨1, by decide⟩) false = true ∧ W.getD (wRightVec n hn m ⟨0, by decide⟩) false = true
        | _ => W.getD (wLeftVec n hn m ⟨2, by decide⟩) false = true ∧ W.getD (wRightVec n hn m ⟨2, by decide⟩) false = true := by
    have hk' : m.val * 3 + k.val < (batchD7 n hn).length := by
      rw [len_batchD7]; have := m.isLt; have := k.isLt; omega
    rw [hD7_call (m.val * 3 + k.val) hk']
    have hlt1 : m.val * 3 + k.val < n * 3 := by have := m.isLt; have := k.isLt; omega
    have hhd : (m.val * 3 + k.val) / 3 = m.val := by have := k.isLt; omega
    have hhm : (m.val * 3 + k.val) % 3 = k.val := by have := k.isLt; omega
    have hget : (batchD7 n hn)[m.val * 3 + k.val]'hk' =
        (match k.val with
        | 0 => ⟨.and, [wLeftVec n hn m ⟨0, by decide⟩, wRightVec n hn m ⟨1, by decide⟩]⟩
        | 1 => ⟨.and, [wLeftVec n hn m ⟨1, by decide⟩, wRightVec n hn m ⟨0, by decide⟩]⟩
        | _ => ⟨.and, [wLeftVec n hn m ⟨2, by decide⟩, wRightVec n hn m ⟨2, by decide⟩]⟩) := by
      unfold batchD7 at hk' ⊢
      rw [List.getElem_append_left (by simp; try omega), List.getElem_append_left (by simp [hlt1]), List.getElem_ofFn]
      simp only [hhd, hhm, Fin.eta]
    rw [hget]
    fin_cases k <;> simp [GateOp.eval]
  have hBdotTerm (idx : Fin allBdotTuples.length) :
      W.getD (wBdotTerm n hn idx.val) false = true ↔
        prefSign Ms n = (allBdotTuples[idx.val]'idx.isLt).1 ∧
        prefTrans Ms n = (allBdotTuples[idx.val]'idx.isLt).2.1 ∧
        W.getD (wFirstC n hn (allBdotTuples[idx.val]'idx.isLt).2.2.1) false = true ∧
        W.getD (wLastR n hn (allBdotTuples[idx.val]'idx.isLt).2.2.2) false = true := by
    have hk' : n * 3 + idx.val < (batchD7 n hn).length := by rw [len_batchD7]; have := idx.isLt; omega
    change W.getD (offD7 n hn + (n * 3 + idx.val)) false = true ↔ _
    rw [hD7_call (n * 3 + idx.val) hk']
    have hget : (batchD7 n hn)[n * 3 + idx.val]'hk' =
        let q := allBdotTuples[idx.val]'idx.isLt
        ⟨.and, [wPEq n hn n q.1 q.2.1, wFirstC n hn q.2.2.1, wLastR n hn q.2.2.2]⟩ := by
      unfold batchD7 at hk' ⊢
      rw [List.getElem_append_left (by simp),
        List.getElem_append_right (by simp; try omega)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_map]
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true, hPEq n le_rfl, decide_eq_true_eq, and_assoc]
  have hTracePn : W.getD (wTracePn n hn) false = true ↔
      (!prefSign Ms n && decide ((prefTrans Ms n).val ≠ 0)) = true := by
    have hk' : n * 3 + allBdotTuples.length < (batchD7 n hn).length := by rw [len_batchD7]; omega
    change W.getD (offD7 n hn + (n * 3 + allBdotTuples.length)) false = true ↔ _
    rw [hD7_call (n * 3 + allBdotTuples.length) hk']
    have hget : (batchD7 n hn)[n * 3 + allBdotTuples.length]'hk' =
        ⟨.or, [wPEq n hn n false ⟨1, by decide⟩, wPEq n hn n false ⟨2, by decide⟩]⟩ := by
      unfold batchD7 at hk' ⊢
      rw [List.getElem_append_right (by simp)]
      simp
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, hPEq n le_rfl, decide_eq_true_eq,
      Bool.not_eq_true']
    have hlt3 := (prefTrans Ms n).isLt
    cases hs : prefSign Ms n <;>
    (rcases (show (prefTrans Ms n).val = 0 ∨ (prefTrans Ms n).val = 1 ∨ (prefTrans Ms n).val = 2 by omega) with h | h | h <;>
     simp [Fin.ext_iff, h])
  have hD8_call (k : ℕ) (hk : k < (batchD8 n hn).length) :
      W.getD (offD8 n hn + k) false =
        ((batchD8 n hn)[k]'hk).op.eval (((batchD8 n hn)[k]'hk).inputs.map (fun j => W.getD j false)) :=
    hbatch g17 (batchD8 n hn) (offD8 n hn) k hk hsp17 o17 (closed_D8 n hn)
  have hAnyBadPair : W.getD (wAnyBadPair n hn) false = true ↔ dyadBad Ms := by
    have hk' : 0 < (batchD8 n hn).length := by rw [len_batchD8]; omega
    have h0 := hD8_call 0 hk'
    simp only [Nat.add_zero] at h0
    unfold wAnyBadPair; rw [h0]
    have hget : (batchD8 n hn)[0]'hk' = ⟨.or, List.ofFn (fun q : Fin (n * 3) => offD7 n hn + q.val)⟩ := rfl
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨q, rfl⟩, rfl⟩, h1⟩
      let m : Fin n := ⟨q.val / 3, div_lt_of_lt_mul_r q.isLt⟩
      let k : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩
      have hqeq : m.val * 3 + k.val = q.val := by dsimp [m, k]; omega
      rw [← hqeq, hBadTriple m k] at h1
      generalize hk_eq : k = k' at h1
      fin_cases k'
      · rcases h1 with ⟨hl, hr⟩
        rw [hLeftVec] at hl; rw [hRightVec] at hr
        rcases hl with ⟨hm, i, hi1, hi2, hri, hleft, hr0⟩
        rcases hr with ⟨_, j, hj1, hj2, hrj, hright, hc1⟩
        refine ⟨m, hm, i, j, hi1, hi2, hri, hleft, hj1, hj2, hrj, hright, ?_⟩
        rw [hr0, hc1]; decide
      · rcases h1 with ⟨hl, hr⟩
        rw [hLeftVec] at hl; rw [hRightVec] at hr
        rcases hl with ⟨hm, i, hi1, hi2, hri, hleft, hr1⟩
        rcases hr with ⟨_, j, hj1, hj2, hrj, hright, hc0⟩
        refine ⟨m, hm, i, j, hi1, hi2, hri, hleft, hj1, hj2, hrj, hright, ?_⟩
        rw [hr1, hc0]; decide
      · rcases h1 with ⟨hl, hr⟩
        rw [hLeftVec] at hl; rw [hRightVec] at hr
        rcases hl with ⟨hm, i, hi1, hi2, hri, hleft, hr2⟩
        rcases hr with ⟨_, j, hj1, hj2, hrj, hright, hc2⟩
        refine ⟨m, hm, i, j, hi1, hi2, hri, hleft, hj1, hj2, hrj, hright, ?_⟩
        rw [hr2, hc2]; decide
    · rintro ⟨m, hm, i, j, hi1, hi2, hri, hleft, hj1, hj2, hrj, hright, hdot⟩
      rcases (vDot_eq_false (tildeR Ms i) (tildeC Ms j)).mp hdot with ⟨hr0, hc1⟩ | ⟨hr1, hc0⟩ | ⟨hr2, hc2⟩
      · let q : Fin (n * 3) := ⟨m.val * 3 + 0, by have := m.isLt; omega⟩
        refine ⟨true, ⟨offD7 n hn + q.val, ⟨q, rfl⟩, ?_⟩, rfl⟩
        change W.getD (offD7 n hn + (m.val * 3 + (⟨0, by decide⟩ : Fin 3).val)) false = true
        rw [hBadTriple m ⟨0, by decide⟩]
        exact ⟨(hLeftVec m _).mpr ⟨hm, i, hi1, hi2, hri, hleft, hr0⟩,
               (hRightVec m _).mpr ⟨hm, j, hj1, hj2, hrj, hright, hc1⟩⟩
      · let q : Fin (n * 3) := ⟨m.val * 3 + 1, by have := m.isLt; omega⟩
        refine ⟨true, ⟨offD7 n hn + q.val, ⟨q, rfl⟩, ?_⟩, rfl⟩
        change W.getD (offD7 n hn + (m.val * 3 + (⟨1, by decide⟩ : Fin 3).val)) false = true
        rw [hBadTriple m ⟨1, by decide⟩]
        exact ⟨(hLeftVec m _).mpr ⟨hm, i, hi1, hi2, hri, hleft, hr1⟩,
               (hRightVec m _).mpr ⟨hm, j, hj1, hj2, hrj, hright, hc0⟩⟩
      · let q : Fin (n * 3) := ⟨m.val * 3 + 2, by have := m.isLt; omega⟩
        refine ⟨true, ⟨offD7 n hn + q.val, ⟨q, rfl⟩, ?_⟩, rfl⟩
        change W.getD (offD7 n hn + (m.val * 3 + (⟨2, by decide⟩ : Fin 3).val)) false = true
        rw [hBadTriple m ⟨2, by decide⟩]
        exact ⟨(hLeftVec m _).mpr ⟨hm, i, hi1, hi2, hri, hleft, hr2⟩,
               (hRightVec m _).mpr ⟨hm, j, hj1, hj2, hrj, hright, hc2⟩⟩
  have hBoundaryDot1 : W.getD (wBoundaryDot1 n hn) false = true ↔
      ∃ i1 im : Fin n,
        mIsRank1 (Ms i1) = true ∧ (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
        mIsRank1 (Ms im) = true ∧ (∀ j : Fin n, im.val < j.val → mIsRank1 (Ms j) = false) ∧
        bDot (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im) = true := by
    have hk' : 1 < (batchD8 n hn).length := by rw [len_batchD8]; omega
    unfold wBoundaryDot1; rw [hD8_call 1 hk']
    have hget : (batchD8 n hn)[1]'hk' = ⟨.or, List.ofFn (fun q : Fin allBdotTuples.length => wBdotTerm n hn q.val)⟩ := rfl
    rw [hget, gateOp_or_iff]
    simp only [List.mem_map, List.mem_ofFn]
    constructor
    · rintro ⟨_, ⟨_, ⟨idx, rfl⟩, rfl⟩, h1⟩
      rw [hBdotTerm idx] at h1
      rcases h1 with ⟨hs, ht, hfc, hlr⟩
      rw [hFirstC] at hfc; rw [hLastR] at hlr
      rcases hfc with ⟨i1, hr1, hf1, hc1⟩
      rcases hlr with ⟨im, hrm, hlm, hrm_eq⟩
      have hmem : allBdotTuples[idx.val]'idx.isLt ∈ allBdotTuples := List.getElem_mem idx.isLt
      have hbd := (mem_allBdotTuples_iff _ _ _ _).mp hmem
      refine ⟨i1, im, hr1, hf1, hrm, hlm, ?_⟩
      rw [hs, ht, hc1, hrm_eq]; exact hbd
    · rintro ⟨i1, im, hr1, hf1, hrm, hlm, hbd⟩
      have hmem := (mem_allBdotTuples_iff (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im)).mpr hbd
      rw [List.mem_iff_getElem] at hmem
      rcases hmem with ⟨idx, hidx, hq⟩
      refine ⟨true, ⟨wBdotTerm n hn idx, ⟨⟨idx, hidx⟩, rfl⟩, ?_⟩, rfl⟩
      rw [hBdotTerm ⟨idx, hidx⟩]
      dsimp only
      rw [hq]
      exact ⟨rfl, rfl, (hFirstC _).mpr ⟨i1, hr1, hf1, rfl⟩, (hLastR _).mpr ⟨im, hrm, hlm, rfl⟩⟩
  have hCase1 : W.getD (wCase1 n hn) false = true ↔
      (∀ i : Fin n, mIsRank1 (Ms i) = false) ∧ (!prefSign Ms n && decide ((prefTrans Ms n).val ≠ 0)) = true := by
    have hk' : 2 < (batchD8 n hn).length := by rw [len_batchD8]; omega
    unfold wCase1; rw [hD8_call 2 hk']
    have hget : (batchD8 n hn)[2]'hk' = ⟨.and, [wNotHasRank1 n, wTracePn n hn]⟩ := rfl
    rw [hget]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [hNotHasRank1, hTracePn, Bool.and_eq_true]
  have hNoBadPair : W.getD (wNoBadPair n hn) false = true ↔ ¬ dyadBad Ms := by
    have hk' : 0 < (batchD9 n hn).length := by rw [len_batchD9]; omega
    have hb := hbatch g18 (batchD9 n hn) (offD9 n hn) 0 hk' hsp18 o18 (closed_D9 n hn)
    simp only [Nat.add_zero] at hb
    unfold wNoBadPair; rw [hb]
    change !(W.getD (wAnyBadPair n hn) false) = true ↔ ¬ dyadBad Ms
    rw [Bool.not_eq_true', ← hAnyBadPair]
    cases W.getD (wAnyBadPair n hn) false <;> simp
  have hCase2 : W.getD (wCase2 n hn) false = true ↔
      (∃ i : Fin n, mIsRank1 (Ms i) = true) ∧ ¬ dyadBad Ms ∧
      ∃ i1 im : Fin n,
        mIsRank1 (Ms i1) = true ∧ (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
        mIsRank1 (Ms im) = true ∧ (∀ j : Fin n, im.val < j.val → mIsRank1 (Ms j) = false) ∧
        bDot (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im) = true := by
    have hk' : 0 < (batchD10 n hn).length := by rw [len_batchD10]; omega
    have hb := hbatch g19 (batchD10 n hn) (offD10 n hn) 0 hk' hsp19 o19 (closed_D10 n hn)
    simp only [Nat.add_zero] at hb
    unfold wCase2; rw [hb]
    simp only [batchD10, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true,
      hHasRank1, hNoBadPair, hBoundaryDot1, and_assoc]
  have hEither : W.getD (wEither n hn) false = true ↔
      ((∀ i : Fin n, mIsRank1 (Ms i) = false) ∧ (!prefSign Ms n && decide ((prefTrans Ms n).val ≠ 0)) = true) ∨
      ((∃ i : Fin n, mIsRank1 (Ms i) = true) ∧ ¬ dyadBad Ms ∧
      ∃ i1 im : Fin n,
        mIsRank1 (Ms i1) = true ∧ (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
        mIsRank1 (Ms im) = true ∧ (∀ j : Fin n, im.val < j.val → mIsRank1 (Ms j) = false) ∧
        bDot (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im) = true) := by
    have hk' : 0 < (batchD11 n hn).length := by rw [len_batchD11]; omega
    have hb := hbatch g20 (batchD11 n hn) (offD11 n hn) 0 hk' hsp20 o20 (closed_D11 n hn)
    simp only [Nat.add_zero] at hb
    unfold wEither; rw [hb]
    simp only [batchD11, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true, hCase1, hCase2]
  have hOut : W.getD (wOut n hn) false = true ↔
      (∀ i : Fin n, mIsZero (Ms i) = false) ∧
      (((∀ i : Fin n, mIsRank1 (Ms i) = false) ∧ (!prefSign Ms n && decide ((prefTrans Ms n).val ≠ 0)) = true) ∨
       ((∃ i : Fin n, mIsRank1 (Ms i) = true) ∧ ¬ dyadBad Ms ∧
       ∃ i1 im : Fin n,
         mIsRank1 (Ms i1) = true ∧ (∀ j : Fin n, j.val < i1.val → mIsRank1 (Ms j) = false) ∧
         mIsRank1 (Ms im) = true ∧ (∀ j : Fin n, im.val < j.val → mIsRank1 (Ms j) = false) ∧
         bDot (prefSign Ms n) (prefTrans Ms n) (tildeC Ms i1) (tildeR Ms im) = true)) := by
    have hk' : 0 < (batchD12 n hn).length := by rw [len_batchD12]; omega
    have hb := hbatch g21 (batchD12 n hn) (offD12 n hn) 0 hk' hsp21 o21 (closed_D12 n hn)
    simp only [Nat.add_zero] at hb
    unfold wOut; rw [hb]
    simp only [batchD12, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true, hNotHasZero, hEither]
  exact hOut.trans (main_alg_iff n hn Ms).symm

end CircuitConst

theorem main_proof :
    ∃ K : ℕ, ∀ (n : ℕ) (hn : 0 < n),
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        let ordinary := fun g : PEqualNP.CircuitLowerBounds.Gate =>
          g.op = .and ∨ g.op = .or ∨ g.op = .not
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) C ∧
        C.output < 4 * n + C.size ∧ C.depth (4 * n) ≤ 40 ∧
        C.size ≤ K * (n + 2) * (Nat.log2 (n + 2) + 1) ∧
        (C.gates.map (fun g => g.inputs.length)).sum ≤ K * (n + 2) ^ 2 ∧
        (∃ A S B R D : List PEqualNP.CircuitLowerBounds.Gate,
          C.gates = A ++ S ++ B ++ R ++ D ∧ (∀ g ∈ A ++ B ++ D, ordinary g) ∧
          S.length ≤ n ∧ R.length ≤ 2 * n ∧
          (∀ g ∈ S, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < 4 * n + A.length) ∧
          (∀ g ∈ R, g.op = .mod 6 ∧
            ∀ j ∈ g.inputs, j < 4 * n + A.length + S.length + B.length)) ∧
        ∀ T : Fin n → Bool → Bool → Bool,
          let x := (List.ofFn (fun i : Fin n =>
            [T i false false, T i true false, T i false true, T i true true])).flatten
          let words := (Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
            ∀ i : Fin n, T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true)
          C.eval x = true ↔ words.card % 2 = 1 := by
  refine ⟨1000, fun n hn => ?_⟩
  refine ⟨buildCircuit n hn, ?_⟩
  rcases structural_bounds n hn with ⟨hrb, hout, hdepth, hsize, hfanin, hS, hR⟩
  refine ⟨hrb, hout, hdepth, hsize, hfanin, ?_, ?_⟩
  · refine ⟨secA n, secS n, secB n, secR n, secD n hn, rfl, ?_, ?_, ?_, hS, hR⟩
    · intro g hg
      simp only [List.mem_append] at hg
      rcases hg with (hA | hB) | hD
      · exact ordinary_secA n g hA
      · exact ordinary_secB n g hB
      · exact ordinary_secD n hn g hD
    · rw [len_secS]
    · rw [len_secR]; omega
  · intro T
    dsimp only
    exact (eval_circuit_correct n hn T).trans (words_card_mod2_iff n hn T).symm

end PEqualNP.Outside.L_clb_084_aux

theorem PEqualNP.Outside.L_clb_084 :
∃ K : ℕ, ∀ (n : ℕ) (hn : 0 < n),
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    let ordinary := fun g : PEqualNP.CircuitLowerBounds.Gate =>
      g.op = .and ∨ g.op = .or ∨ g.op = .not
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) C ∧
    C.output < 4 * n + C.size ∧ C.depth (4 * n) ≤ 40 ∧
    C.size ≤ K * (n + 2) * (Nat.log2 (n + 2) + 1) ∧
    (C.gates.map (fun g => g.inputs.length)).sum ≤ K * (n + 2) ^ 2 ∧
    (∃ A S B R D : List PEqualNP.CircuitLowerBounds.Gate,
      C.gates = A ++ S ++ B ++ R ++ D ∧ (∀ g ∈ A ++ B ++ D, ordinary g) ∧
      S.length ≤ n ∧ R.length ≤ 2 * n ∧
      (∀ g ∈ S, g.op = .mod 6 ∧ ∀ j ∈ g.inputs, j < 4 * n + A.length) ∧
      (∀ g ∈ R, g.op = .mod 6 ∧
        ∀ j ∈ g.inputs, j < 4 * n + A.length + S.length + B.length)) ∧
    ∀ T : Fin n → Bool → Bool → Bool,
      let x := (List.ofFn (fun i : Fin n =>
        [T i false false, T i true false, T i false true, T i true true])).flatten
      let words := (Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
        ∀ i : Fin n, T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true)
      C.eval x = true ↔ words.card % 2 = 1 :=
  PEqualNP.Outside.L_clb_084_aux.main_proof
