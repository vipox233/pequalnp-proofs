import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_30706

open Finset

def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k))
    ((constant round).val.testBit (pos % k))

def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

lemma rotFn_lt {k : ℕ} (s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotFn_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsm : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hhi : word.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and, hmod]
  · have hlt : i < s % k := by omega
    have hdec : decide (s % k ≤ i) = false := decide_eq_false (by omega)
    have hmod : (i + k - s % k) % k = i + (k - s % k) := by
      have h1 : i + k - s % k = i + (k - s % k) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hdec, Bool.false_and, Bool.false_or, hmod, Nat.add_comm (k - s % k) i]

lemma mod_sub_one {k n : ℕ} (hk : 1 ≤ k) :
    (n % k + k - 1 % k) % k = (n + k - 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : n % k < k := Nat.mod_lt n (by omega)
    have hrew : n % k + k - 1 = n % k + (k - 1) := by omega
    have hrew2 : n + k - 1 = n + (k - 1) := by omega
    rw [hrew, hrew2, Nat.mod_add_mod]

lemma bitFn_zero {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    bitFn k constant row 0 key pos =
      xor (key.testBit ((pos + k - 1) % k)) (row.testBit (pos % k)) := by
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]

abbrev Block := Bool × Bool × Bool

def bxor (x y : Block) : Block :=
  (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2 y.2.2)

def affine (flag : Bool) (x : Block) : Bool :=
  if flag then x.1 else x.2.1

def point (flag : Bool) : Block := (true, true, flag)

def localValue (α β δ f₅ : Bool) (x : Block) : Bool :=
  let u := xor α x.1
  let v := xor β ((!x.1) && x.2.1)
  let w := xor δ ((x.1 == x.2.1) && x.2.2)
  let s₅ := xor (xor β f₅) u
  let s₆ := xor (xor f₅ u) v
  let s₇ := xor (xor u v) w
  xor s₅ ((!s₆) && s₇)

lemma localValue_eq (α β δ f₅ : Bool) (x : Block)
    (h : xor β f₅ = !α) :
    localValue α β δ f₅ x =
      xor (!affine (xor (xor α β) δ) x) (decide (x = point (xor (xor α β) δ))) := by
  rcases x with ⟨a, b, c⟩
  cases α <;> cases β <;> cases δ <;> cases f₅ <;> cases a <;> cases b <;> cases c <;>
    first | decide | contradiction

def shareBit (k : ℕ) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) : Bool :=
  xor (bitFn k constant row.val 0 key.val pos) (bitFn k constant row.val 0 ref.val pos)

lemma shareBit_eq {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key pos =
      xor (key.val.testBit ((pos + k - 1) % k)) (ref.val.testBit ((pos + k - 1) % k)) := by
  unfold shareBit
  rw [bitFn_zero hk constant key.isLt, bitFn_zero hk constant ref.isLt]
  cases key.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;>
    cases row.val.testBit (pos % k) <;> rfl

def combine {k : ℕ} (ref left right : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(left.val ^^^ right.val ^^^ ref.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

lemma shareBit_combine {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref (combine ref left right) pos =
      xor (shareBit k constant row ref left pos) (shareBit k constant row ref right pos) := by
  simp only [shareBit_eq hk, combine, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    decide_eq_true (Nat.mod_lt _ (by omega : 0 < k)), Bool.true_and]
  cases left.val.testBit ((pos + k - 1) % k) <;>
    cases right.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;> rfl

lemma shareBit_mod {k : ℕ} (_hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key (pos % k) = shareBit k constant row ref key pos := by
  unfold shareBit bitFn
  rw [Nat.mod_mod]

noncomputable def shareBitsEquiv {k : ℕ} (hk : 12 ≤ k)
    (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) : Fin (2 ^ k) ≃ (Fin k → Bool) := by
  classical
  apply Equiv.ofBijective (fun key j => shareBit k constant row ref key j.val)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · let j : Fin k := ⟨(i+1)%k, Nat.mod_lt _ (by omega)⟩
    have hh := congrFun hab j
    change shareBit k constant row ref a ((i + 1) % k) =
      shareBit k constant row ref b ((i + 1) % k) at hh
    rw [shareBit_mod hk, shareBit_mod hk, shareBit_eq hk, shareBit_eq hk,
      show i + 1 + k - 1 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi] at hh
    cases ref.val.testBit i <;> simpa using hh
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]

def toBlock (f : Fin 3 → Bool) : Block := (f 0, f 1, f 2)

def fromBlock (x : Block) (j : Fin 3) : Bool :=
  if j = 0 then x.1 else if j = 1 then x.2.1 else x.2.2

lemma toBlock_fromBlock (x : Block) : toBlock (fromBlock x) = x := by
  rcases x with ⟨a, b, c⟩
  rfl

lemma fromBlock_toBlock (f : Fin 3 → Bool) (j : Fin 3) : fromBlock (toBlock f) j = f j := by
  fin_cases j <;> rfl

abbrev Remainder {m k : ℕ} (pin : Finset (Fin k)) (coord : Fin m × Fin 3 → Fin k) :=
  {j : Fin k // j ∉ pin ∧ j ∉ Set.range coord}

noncomputable def splitBits {m k : ℕ} (pin : Finset (Fin k))
    (coord : Fin m × Fin 3 → Fin k) (hc : Function.Injective coord)
    (hf : ∀ ij, coord ij ∉ pin) :
    {f : Fin k → Bool // ∀ j ∈ pin, f j = false} ≃
      (Fin m → Block) × (Remainder pin coord → Bool) := by
  classical
  let tail := fun (g : Remainder pin coord → Bool) (j : Fin k) =>
    if h : j ∉ pin ∧ j ∉ Set.range coord then g ⟨j, h⟩ else false
  let pack := fun (p : (Fin m → Block) × (Remainder pin coord → Bool)) =>
    Function.extend coord (fun ij => fromBlock (p.1 ij.1) ij.2) (tail p.2)
  have hpack (p : (Fin m → Block) × (Remainder pin coord → Bool)) (j : Fin k) (hj : j ∉ Set.range coord) :
      pack p j = tail p.2 j := Function.extend_apply' _ _ _ hj
  refine
    { toFun := fun f => (fun i => toBlock (fun j => f.val (coord (i,j))), fun j => f.val j.val)
      invFun := fun p => ⟨pack p, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro j hj
    have hn : j ∉ Set.range coord := by
      rintro ⟨ij, rfl⟩
      exact hf ij hj
    rw [hpack _ _ hn]
    simp [tail, hj]
  · intro f
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range coord
    · obtain ⟨⟨i, t⟩, rfl⟩ := hj
      change pack _ (coord (i,t)) = f.val (coord (i,t))
      dsimp only [pack]
      rw [hc.extend_apply]
      exact fromBlock_toBlock _ _
    · change pack _ j = f.val j
      rw [hpack _ _ hj]
      by_cases hp : j ∈ pin
      · simp [tail, hp, f.property j hp]
      · have h : j ∉ pin ∧ j ∉ Set.range coord := ⟨hp, hj⟩
        simp only [tail, dite_eq_left h]
  · intro p
    apply Prod.ext
    · funext i
      change toBlock (fun j => pack p (coord (i,j))) = p.1 i
      simp_rw [pack, hc.extend_apply]
      exact toBlock_fromBlock _
    · funext j
      change pack p j.val = p.2 j
      rw [hpack _ _ j.property.2]
      simp only [tail, dite_eq_left j.property]

lemma extract_local {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (p : ℕ) :
    let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
    let first := fun j => bitFn k constant row.val 1 ref.val (p+j)
    let pair := xor (old 7) (old 8)
    let τ := xor (old 6) pair
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
    let β := xor τ (injectedFn k constant 1 ref.val (p+7))
    let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
    let x : Block :=
      (xor (bitFn k constant row.val 0 key.val (p+9)) pair,
       xor (bitFn k constant row.val 0 key.val (p+10)) (old 7),
       xor (bitFn k constant row.val 0 key.val (p+11)) (old 8))
    (∀ j < 9, bitFn k constant row.val 0 key.val (p+j) = old j) →
    τ = false → xor (first 4) (first 5) = !α → first 4 = β →
    bitFn k constant row.val 2 key.val (p+5) =
      xor (xor (!affine (xor (xor α β) δ) x) (decide (x = point (xor (xor α β) δ))))
        (injectedFn k constant 2 ref.val (p+5)) := by
  intro old first pair τ α β δ x hkey hτ h45 h4
  have hh45 : xor β (first 5) = !α := by simpa only [h4] using h45
  have hmerged := PEqualNP.Outside.L_meta_25620 k (by omega) constant hk row ref p
  have hmem : key ∈ (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun q => (List.range 9).all (fun j => bitFn k constant row.val 0 q.val (p+j) == old j)) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
      beq_iff_eq] using hkey
  have hb := (hmerged.1 key hmem).2 (3 : Fin 4)
  let n : ℕ := x.1.toNat + 2 * x.2.1.toNat + 4 * x.2.2.toNat
  let model : ℕ → Bool := fun j =>
    if j = 6 then xor α ((!τ) && n.testBit 0)
    else if j = 7 then xor β ((!n.testBit 0) && n.testBit 1)
    else if j = 8 then xor δ ((n.testBit 0 == n.testBit 1) && n.testBit 2)
    else first j
  change bitFn k constant row.val 2 key.val (p+5) =
    xor (xor (xor (xor (model 4) (model 5)) (model 6))
      (!(xor (xor (model 5) (model 6)) (model 7)) && xor (xor (model 6) (model 7)) (model 8)))
      (injectedFn k constant 2 ref.val (p+5)) at hb
  have bits (y : Block) :
      let v := y.1.toNat + 2 * y.2.1.toNat + 4 * y.2.2.toNat
      v.testBit 0 = y.1 ∧ v.testBit 1 = y.2.1 ∧ v.testBit 2 = y.2.2 := by
    rcases y with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> decide
  have hn := bits x
  change n.testBit 0 = x.1 ∧ n.testBit 1 = x.2.1 ∧ n.testBit 2 = x.2.2 at hn
  have hm : bitFn k constant row.val 2 key.val (p+5) =
      xor (localValue α β δ (first 5) x) (injectedFn k constant 2 ref.val (p+5)) := by
    rw [hb]
    simp only [model, h4, hτ, Bool.not_false, Bool.true_and, hn.1, hn.2.1, hn.2.2,
      show (4 : ℕ) ≠ 6 by decide, show (4 : ℕ) ≠ 7 by decide, show (4 : ℕ) ≠ 8 by decide,
      show (5 : ℕ) ≠ 6 by decide, show (5 : ℕ) ≠ 7 by decide, show (5 : ℕ) ≠ 8 by decide,
      show (7 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 7 by decide,
      ↓reduceIte, localValue]
  rw [hm, localValue_eq α β δ (first 5) x hh45]

def windowFlag {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Bool :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  let pair := xor (old 7) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
  let β := xor (xor (old 6) pair) (injectedFn k constant 1 ref.val (p+7))
  let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
  xor (xor α β) δ

def windowOffset {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  (xor (old 9) (xor (old 7) (old 8)), xor (old 10) (old 7), xor (old 11) (old 8))

def windowShare {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref key : Fin (2 ^ k)) (p : ℕ) : Block :=
  (shareBit k constant row ref key (p+9), shareBit k constant row ref key (p+10),
    shareBit k constant row ref key (p+11))

def windowShift {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  bxor (windowOffset constant row ref p) (point (windowFlag constant row ref p))

lemma xor_left_eq (a b c : Bool) : xor a b = c ↔ a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

lemma bxor_eq (a b c : Block) : bxor a b = c ↔ a = bxor b c := by
  rcases a with ⟨aa, ab, ac⟩
  rcases b with ⟨ba, bb, bc⟩
  rcases c with ⟨ca, cb, cc⟩
  simp only [bxor, Prod.mk.injEq, xor_left_eq]

lemma bxor_assoc (a b c : Block) : bxor (bxor a b) c = bxor a (bxor b c) := by
  simp [bxor]

lemma bxor_comm (a b : Block) : bxor a b = bxor b a := by
  simp [bxor, Bool.xor_comm]

lemma bxor_cancel (a b : Block) : bxor a (bxor a b) = b := by
  rcases b with ⟨b₁, b₂, b₃⟩
  simp [bxor]

lemma bxor_cancel_right (a b : Block) : bxor (bxor a b) b = a := by
  rw [bxor_comm (bxor a b) b, bxor_comm a b, bxor_cancel]

lemma xor_recover (a b c : Bool) : xor (xor a b) (xor b c) = xor a c := by
  cases a <;> cases b <;> cases c <;> rfl

lemma affine_bxor (f : Bool) (a b : Block) : affine f (bxor a b) = xor (affine f a) (affine f b) := by
  cases f <;> rfl

lemma guarded_window {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (p : ℕ) :
    let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
    let first := fun j => bitFn k constant row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
    let β := xor τ (injectedFn k constant 1 ref.val (p+7))
    let l := windowShare constant row ref left p
    let r := bxor (windowShare constant row ref right p) (windowShift constant row ref p)
    let f := windowFlag constant row ref p
    let base := xor (!affine f (point f)) (injectedFn k constant 2 ref.val (p+5))
    (∀ j < 9, shareBit k constant row ref left (p+j) = false) →
    (∀ j < 9, shareBit k constant row ref right (p+j) = false) →
    τ = false → xor (first 4) (first 5) = !α → first 4 = β →
    bitFn k constant row.val 2 (combine ref left right).val (p+5) =
      xor (xor (xor base (affine f l)) (affine f r)) (decide (l = r)) := by
  intro old first τ α β l r f base hl hr ht h45 h4
  let key := combine ref left right
  let o := windowOffset constant row ref p
  have hh j (hj : j < 9) : bitFn k constant row.val 0 key.val (p+j) = old j := by
    have h := shareBit_combine hk constant row ref left right (p+j)
    rw [hl j hj, hr j hj] at h
    change xor (bitFn k constant row.val 0 key.val (p+j)) (old j) = false at h
    exact (xor_left_eq _ _ _).mp h |>.trans (Bool.xor_false _)
  have ht' : xor (old 6) (xor (old 7) (old 8)) = false := by
    rw [← Bool.xor_assoc]
    exact ht
  have h4' : first 4 = xor (xor (old 6) (xor (old 7) (old 8)))
      (injectedFn k constant 1 ref.val (p+7)) := by
    rw [← Bool.xor_assoc]
    exact h4
  have hvalue := extract_local hk constant row ref key p hh ht' h45 h4'
  let x : Block := (xor (bitFn k constant row.val 0 key.val (p+9)) (xor (old 7) (old 8)),
    xor (bitFn k constant row.val 0 key.val (p+10)) (old 7),
    xor (bitFn k constant row.val 0 key.val (p+11)) (old 8))
  change bitFn k constant row.val 2 key.val (p+5) =
    xor (xor (!affine f x) (decide (x = point f))) (injectedFn k constant 2 ref.val (p+5)) at hvalue
  have hshift j : xor (bitFn k constant row.val 0 key.val (p+j)) (old j) =
      xor (shareBit k constant row ref left (p+j)) (shareBit k constant row ref right (p+j)) :=
    shareBit_combine hk constant row ref left right (p+j)
  have hx : x = bxor l (bxor r (point f)) := by
    have hxo : x = bxor (bxor l (windowShare constant row ref right p)) o := by
      dsimp only [x, bxor, l, windowShare, o, windowOffset]
      rw [← hshift 9, ← hshift 10, ← hshift 11]
      exact Prod.ext (xor_recover _ _ _).symm (Prod.ext (xor_recover _ _ _).symm (xor_recover _ _ _).symm)
    rw [hxo, bxor_assoc]
    change bxor l (bxor (windowShare constant row ref right p) o) =
      bxor l (bxor (bxor (windowShare constant row ref right p) (bxor o (point f))) (point f))
    rw [bxor_assoc (windowShare constant row ref right p), bxor_cancel_right]
  have heq : (x = point f) ↔ l = r := by
    rw [hx, bxor_eq, bxor_cancel_right]
  rw [hvalue, decide_eq_decide.mpr heq, hx, affine_bxor, affine_bxor]
  change xor (xor (!(xor (affine f l) (xor (affine f r) (affine f (point f))))) (decide (l = r)))
      (injectedFn k constant 2 ref.val (p+5)) = _
  dsimp only [base]
  generalize affine f l = a, affine f r = b, affine f (point f) = c,
    decide (l = r) = e, injectedFn k constant 2 ref.val (p+5) = j
  cases a <;> cases b <;> cases c <;> cases e <;> cases j <;> rfl

def parityOn {I : Type} (s : Finset I) (f : I → Bool) : Bool :=
  (∑ i ∈ s, (f i).toNat) % 2 == 1

lemma parity_add (a b : ℕ) : ((a+b)%2 == 1) = xor (a%2 == 1) (b%2 == 1) := by
  have ha : a%2 = 0 ∨ a%2 = 1 := by omega
  have hb : b%2 = 0 ∨ b%2 = 1 := by omega
  rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> rfl

lemma parity_insert {I : Type} [DecidableEq I] {s : Finset I} {i : I} (hi : i ∉ s) (f : I → Bool) :
    parityOn (insert i s) f = xor (f i) (parityOn s f) := by
  unfold parityOn
  rw [sum_insert hi, parity_add]
  cases f i <;> rfl

lemma parity_xor {I : Type} (s : Finset I) (f g : I → Bool) :
    parityOn s (fun i => xor (f i) (g i)) = xor (parityOn s f) (parityOn s g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    simp only [parity_insert hi, ih, Bool.xor_assoc, Bool.xor_left_comm]

noncomputable def bitSign (b : Bool) : ℝ := if b then -1 else 1

lemma sign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> norm_num [bitSign]

lemma sign_sq (a : Bool) : bitSign a ^ 2 = 1 := by cases a <;> norm_num [bitSign]

lemma sign_parity {I : Type} (s : Finset I) (f : I → Bool) :
    bitSign (parityOn s f) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [parityOn, bitSign]
  | @insert i s hi ih => rw [parity_insert hi, sign_xor, ih, prod_insert hi]

def modelTruth {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x y : Fin m → Block) : Bool :=
  xor (xor (φ x) (ψ y)) (parityOn univ fun i => decide (x i = y i))

def support {m : ℕ} {B : Type} (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (x : Fin m → B) : Finset (Fin m) := univ.filter (fun i => p i (x i))

lemma card_support {m : ℕ} {B : Type} [Fintype B] (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (a b : ℕ) (ha : ∀ i, (univ.filter (p i)).card = a)
    (hb : ∀ i, (univ.filter (fun x => ¬p i x)).card = b) (J : Finset ℕ) :
    (univ.filter (fun x => (support p x).card ∈ J)).card =
      ∑ j ∈ J, m.choose j * a ^ j * b ^ (m-j) := by
  classical
  have hfiber (s : Finset (Fin m)) :
      (univ.filter (fun x => support p x = s)).card = a ^ s.card * b ^ (m-s.card) := by
    let allow := fun i => if i ∈ s then univ.filter (p i) else univ.filter (fun x => ¬p i x)
    have hrect : univ.filter (fun x => support p x = s) = Fintype.piFinset allow := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl i
        by_cases hi : p i (x i) <;> simp [allow, support, hi]
      · intro h
        ext i
        have hh := h i
        by_cases hi : i ∈ s <;> simp_all [allow, support]
    rw [hrect, Fintype.card_piFinset]
    have hallow i : (allow i).card = if i ∈ s then a else b := by
      by_cases hi : i ∈ s <;> simp [allow, hi, ha, hb]
    simp_rw [hallow]
    rw [Finset.prod_ite]
    have hs : univ.filter (fun i => i ∈ s) = s := by ext i; simp
    have hc : (univ.filter (fun i => i ∉ s)).card = m - s.card := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (p := fun i => i ∈ s)
      rw [hs, card_univ, Fintype.card_fin] at h
      omega
    rw [hs, prod_const, prod_const, hc]
  rw [← sum_card_fiberwise_eq_card_filter univ J (fun x => (support p x).card)]
  apply sum_congr rfl
  intro j hj
  let S := (univ : Finset (Fin m)).powersetCard j
  have hm : ((univ : Finset (Fin m → B)).filter (fun x => (support p x).card = j) : Set (Fin m → B)).MapsTo
      (support p) S := by
    intro x hx
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hx).2⟩
  rw [card_eq_sum_card_fiberwise hm]
  have hterm (s : Finset (Fin m)) (hs : s ∈ S) :
      ((univ.filter (fun x => (support p x).card = j)).filter (fun x => support p x = s)).card =
      a ^ j * b ^ (m-j) := by
    have hs' := (mem_powersetCard.mp hs).2
    rw [← hs', ← hfiber s]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact And.right
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [sum_congr rfl hterm, sum_const, Nat.nsmul_eq_mul, mul_assoc]
  simp [S, card_powersetCard]

def distance {m : ℕ} (x y : Fin m → Block) : ℕ :=
  (univ.filter (fun i => x i ≠ y i)).card

lemma card_block_ne : ∀ x : Block, (univ.filter (fun y : Block => x ≠ y)).card = 7 := by
  decide +kernel

lemma card_near {m : ℕ} (h : ℕ) (x : Fin m → Block) :
    (univ.filter (fun y => distance x y ≤ h)).card = ∑ j ∈ range (h+1), m.choose j * 7^j := by
  classical
  let p := fun i (b : Block) => x i ≠ b
  let _ : ∀ i, DecidablePred (p i) := fun i b => inferInstanceAs (Decidable (x i ≠ b))
  have hp : ∀ i, (univ.filter (p i)).card = 7 := fun i => card_block_ne (x i)
  have hn : ∀ i, (univ.filter (fun b => ¬p i b)).card = 1 := by
    intro i
    have hs : (univ.filter (fun b => ¬p i b)) = {x i} := by
      ext b
      simp [p, eq_comm]
    simp [hs]
  have heq : univ.filter (fun y => distance x y ≤ h) =
      univ.filter (fun y => (support p y).card ∈ range (h+1)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_range, Nat.lt_succ_iff]
    rfl
  rw [heq, card_support p 7 1 hp hn]
  simp

lemma card_code (m : ℕ) : Fintype.card (Fin m → Block) = 8 ^ m := by
  simp [Fintype.card_prod]

def rationalSign (b : Bool) : ℚ := if b then -1 else 1

lemma rationalSign_cast (b : Bool) : ((rationalSign b : ℚ) : ℝ) = bitSign b := by
  cases b <;> norm_num [rationalSign, bitSign]

lemma local_correlation (x y : Block) :
    (∑ z : Block, bitSign (decide (x = z)) * bitSign (decide (y = z))) =
      if x ≠ y then (4 : ℝ) else 8 := by
  have hq : ∀ a b : Block,
      (∑ z : Block, rationalSign (decide (a = z)) * rationalSign (decide (b = z))) =
        if a ≠ b then (4 : ℚ) else 8 := by decide +kernel
  have hc := congrArg (fun q : ℚ => (q : ℝ)) (hq x y)
  split_ifs at hc ⊢ <;> simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, rationalSign_cast] using hc

lemma correlation {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x x' : Fin m → Block) :
    (∑ y : Fin m → Block, bitSign (modelTruth φ ψ x y) * bitSign (modelTruth φ ψ x' y)) =
      (bitSign (φ x) * bitSign (φ x')) * (8 : ℝ)^m * (1 / 2)^distance x x' := by
  classical
  have hfactor (y : Fin m → Block) :
      bitSign (modelTruth φ ψ x y) * bitSign (modelTruth φ ψ x' y) =
        (bitSign (φ x) * bitSign (φ x')) *
          (∏ i : Fin m, (bitSign (decide (x i = y i)) * bitSign (decide (x' i = y i)))) := by
    simp only [modelTruth, sign_xor, sign_parity, prod_mul_distrib]
    calc
      _ = (bitSign (φ x) * bitSign (φ x')) * bitSign (ψ y) ^ 2 *
          ((∏ i : Fin m, bitSign (decide (x i = y i))) * ∏ i : Fin m, bitSign (decide (x' i = y i))) := by ring
      _ = _ := by rw [sign_sq, mul_one]
  simp_rw [hfactor, ← mul_sum]
  rw [← Fintype.prod_sum (fun (i : Fin m) (z : Block) =>
    bitSign (decide (x i = z)) * bitSign (decide (x' i = z)))]
  simp_rw [local_correlation]
  rw [Finset.prod_ite, prod_const, prod_const]
  have hcompl : (univ.filter (fun i => ¬x i ≠ x' i)).card = m - distance x x' := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (p := fun i => x i ≠ x' i)
    rw [card_univ, Fintype.card_fin] at h
    change distance x x' + (univ.filter (fun i => ¬x i ≠ x' i)).card = m at h
    omega
  rw [hcompl]
  change bitSign (φ x) * bitSign (φ x') * (4 ^ distance x x' * 8 ^ (m-distance x x')) = _
  have hd : distance x x' ≤ m := by simpa [distance] using card_filter_le (univ : Finset (Fin m)) (fun i => x i ≠ x' i)
  have hp : (8 : ℝ)^m = 8^distance x x' * 8^(m-distance x x') := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  rw [hp, show (4 : ℝ) = 8 * (1/2) by norm_num, mul_pow]
  ring

lemma card_filter_fst {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) [DecidablePred p] :
    ((univ : Finset (A × B)).filter (fun z => p z.1)).card =
      (univ.filter p).card * Fintype.card B := by
  have heq : (univ : Finset (A × B)).filter (fun z => p z.1) = (univ.filter p).product univ := by
    ext z
    simp
  rw [heq]
  change ((univ.filter p) ×ˢ (univ : Finset B)).card = _
  rw [card_product, card_univ]

abbrev Input (m : ℕ) (R : Type) := (Fin m → Block) × R

lemma xor_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  rw [xor_left_eq, Bool.xor_false]

def shiftBlock {m : ℕ} (s : Fin m → Block) : (Fin m → Block) ≃ (Fin m → Block) where
  toFun x i := bxor (x i) (s i)
  invFun x i := bxor (x i) (s i)
  left_inv x := funext fun i => bxor_cancel_right (x i) (s i)
  right_inv x := funext fun i => bxor_cancel_right (x i) (s i)


lemma model_stats {m : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (φ ψ : (Fin m → Block) → Bool) (h : ℕ) :
    let ball := ∑ j ∈ range (h+1), m.choose j * 7^j
    let S := Input m R
    (Fintype.card S : ℝ) = 8^m * Fintype.card R ∧
    (∀ x : S, ((univ.filter (fun y : S => distance x.1 y.1 ≤ h)).card : ℝ) ≤
      (ball : ℝ) * Fintype.card R) ∧
    (∀ x x' : S, (∑ y : S, bitSign (modelTruth φ ψ x.1 y.1) * bitSign (modelTruth φ ψ x'.1 y.1)) ≤
      (Fintype.card S : ℝ) * ((1/2 : ℝ)^(h+1) + (1-(1/2 : ℝ)^(h+1)) *
        (if distance x.1 x'.1 ≤ h then 1 else 0))) := by
  intro ball S
  let close := fun (x y : Input m R) => distance x.1 y.1 ≤ h
  let N : ℝ := Fintype.card R
  let r : ℝ := (1/2)^(h+1)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcount : (Fintype.card (Input m R) : ℝ) = 8^m * N := by
    simp only [Input, Fintype.card_prod, card_code, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, N]
  have hnear (x : Input m R) : ((univ.filter (close x)).card : ℝ) ≤ (ball : ℝ) * N := by
    rw [card_filter_fst (fun y => distance x.1 y ≤ h), card_near, Nat.cast_mul]
  have hc (x x' : Input m R) :
      (∑ y : Input m R, bitSign (modelTruth φ ψ x.1 y.1) * bitSign (modelTruth φ ψ x'.1 y.1)) ≤
        (Fintype.card (Input m R) : ℝ) * (r + (1-r) * (if close x x' then 1 else 0)) := by
    rw [Fintype.sum_prod_type, hcount]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    rw [correlation]
    let d := distance x.1 x'.1
    have hf : bitSign (φ x.1) * bitSign (φ x'.1) ≤ 1 := by
      cases φ x.1 <;> cases φ x'.1 <;> norm_num [bitSign]
    have hd : (1/2 : ℝ)^d ≤ r + (1-r) * (if close x x' then 1 else 0) := by
      by_cases he : close x x'
      · rw [ite_eq_left he, mul_one, add_sub_cancel]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      · rw [ite_eq_right he, mul_zero, add_zero]
        have hh : h + 1 ≤ d := by simpa [close, d] using Nat.succ_le_iff.mpr (Nat.lt_of_not_ge he)
        calc
          _ = (1/2 : ℝ)^(h+1) * (1/2 : ℝ)^(d-(h+1)) := by rw [← pow_add, Nat.add_sub_of_le hh]
          _ ≤ (1/2 : ℝ)^(h+1) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr0
          _ = _ := by simp [r]
    change N * (bitSign (φ x.1) * bitSign (φ x'.1) * 8^m * (1/2)^d) ≤ _
    calc
      _ = (8^m * N) * ((bitSign (φ x.1) * bitSign (φ x'.1)) * (1/2)^d) := by ring
      _ ≤ (8^m * N) * ((1/2)^d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using mul_le_mul_of_nonneg_right hf (show (0 : ℝ) ≤ (1/2)^d by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  exact ⟨hcount, hnear, hc⟩

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706
open Finset

theorem rectangle_bound {A B M : Type} [Fintype A] [Fintype B] [Fintype M]
    [Nonempty A] [Nonempty B]
    (f : A → B → ℝ) (read : M → B → ℝ) (left : M → Finset A) (right : M → Finset B)
    (close : A → A → Prop) [∀ a, DecidablePred (close a)]
    (r D mass : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hD : 0 ≤ D)
    (hclose : ∀ a, ((univ.filter (close a)).card : ℝ) ≤ D)
    (hcorr : ∀ a a', (∑ y : B, f a y * f a' y) ≤
      (Fintype.card B : ℝ) * (r + (1-r) * (if close a a' then 1 else 0)))
    (hsign : ∀ j y, (read j y)^2 = 1)
    (harea : (∑ j : M, ((left j).card : ℝ) * (right j).card) ≤
      (Fintype.card A : ℝ) * Fintype.card B)
    (hleft : (∑ j : M, ((left j).card : ℝ)) ≤ (Fintype.card A : ℝ) * mass) :
    ((∑ j : M, ∑ y ∈ right j, read j y * ∑ x ∈ left j, f x y) /
      ((Fintype.card A : ℝ) * Fintype.card B))^2 ≤
      r*mass + (1-r) * ((Fintype.card M : ℝ) * D / Fintype.card A) := by
  classical
  let na : ℝ := Fintype.card A
  let nb : ℝ := Fintype.card B
  have ha : 0 < na := by dsimp [na]; exact_mod_cast Fintype.card_pos
  have hb : 0 < nb := by dsimp [nb]; exact_mod_cast Fintype.card_pos
  let n := fun j : M => ((left j).card : ℝ)
  let t := fun j : M => ((right j).card : ℝ)
  let v := fun j y => ∑ x ∈ left j, f x y
  let score := fun j => ∑ y ∈ right j, read j y * v j y
  let w := fun j => nb * (r*n j + (1-r)*D)
  have hwn (j : M) : 0 ≤ w j := by dsimp [w,n]; positivity
  have hnear (j : M) (a : A) : (((left j).filter (close a)).card : ℝ) ≤ D := by
    refine le_trans ?_ (hclose a)
    exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ (left j)))
  have hinner (j : M) (a : A) : (∑ a' ∈ left j, ∑ y : B, f a y * f a' y) ≤ w j := by
    calc
      _ ≤ ∑ a' ∈ left j, nb * (r + (1-r) * (if close a a' then 1 else 0)) :=
        sum_le_sum fun a' _ => hcorr a a'
      _ = nb * (r*n j + (1-r) * (((left j).filter (close a)).card : ℝ)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← sum_filter, sum_const, sum_const]
        simp only [nsmul_eq_mul, mul_one, n]
        ring
      _ ≤ w j := mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hnear j a) (sub_nonneg.mpr hr1))) hb.le
  have henergy (j : M) : (∑ y : B, v j y ^ 2) ≤ n j * w j := by
    calc
      _ = ∑ y : B, ∑ a ∈ left j, ∑ a' ∈ left j, f a y * f a' y := by
        simp only [v, pow_two, sum_mul, mul_sum]
        apply sum_congr rfl
        intro y hy
        apply sum_congr rfl
        intro a ha'
        apply sum_congr rfl
        intro a' h'
        exact mul_comm _ _
      _ = ∑ a ∈ left j, ∑ a' ∈ left j, ∑ y : B, f a y * f a' y := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha'
        rw [sum_comm]
      _ ≤ ∑ _a ∈ left j, w j := sum_le_sum fun a _ => hinner j a
      _ = _ := by simp [n, nsmul_eq_mul]
  have hscore (j : M) : score j ^ 2 ≤ (n j * t j) * w j := by
    have hc := sum_mul_sq_le_sq_mul_sq (right j) (read j) (v j)
    simp only [hsign, sum_const, nsmul_eq_mul, mul_one] at hc
    have hrestricted : (∑ y ∈ right j, v j y ^ 2) ≤ ∑ y : B, v j y ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => sq_nonneg _)
    calc
      _ ≤ t j * ∑ y ∈ right j, v j y ^ 2 := hc
      _ ≤ t j * (n j * w j) := mul_le_mul_of_nonneg_left (hrestricted.trans (henergy j)) (by dsimp [t]; positivity)
      _ = _ := by ring
  have hw : (∑ j : M, w j) ≤ nb * (r*(na*mass) + (Fintype.card M : ℝ)*((1-r)*D)) := by
    dsimp only [w]
    rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hleft hr0) le_rfl) hb.le
  have htotal : (∑ j : M, score j)^2 ≤ (na*nb) * (nb * (r*(na*mass) + (Fintype.card M : ℝ)*((1-r)*D))) := by
    calc
      _ ≤ (∑ j : M, n j*t j) * ∑ j : M, w j :=
        sum_sq_le_sum_mul_sum_of_sq_le_mul univ (f := fun j => n j*t j) (g := w)
          (by intro j _; dsimp [n,t]; positivity) (fun j _ => hwn j) (fun j _ => hscore j)
      _ ≤ _ := mul_le_mul harea hw (sum_nonneg fun j _ => hwn j) (by positivity)
  change ((∑ j : M, score j) / (na*nb))^2 ≤ r*mass + (1-r)*((Fintype.card M : ℝ)*D/na)
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc
    _ ≤ _ := htotal
    _ = _ := by field_simp

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706

def guardedLog {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    let q := guardedLog alice speak x y t
    q + (speak t q (if alice t q then x else y)).toNat * 2^t

theorem guardedLog_foldl {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c : Nat) :
    guardedLog alice speak x y c =
      (List.range c).foldl (fun log t =>
        let v := speak t log (if alice t log then x else y)
        log + (v.toNat <<< t)) 0 := by
  induction c with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.shiftLeft_eq, guardedLog, ih]

theorem guardedLog_lt {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c : Nat) :
    guardedLog alice speak x y c < 2^c := by
  induction c with
  | zero => simp [guardedLog]
  | succ t ih =>
    rw [guardedLog, Nat.pow_succ]
    have hb := Bool.toNat_le (speak t (guardedLog alice speak x y t)
      (if alice t (guardedLog alice speak x y t) then x else y))
    have hm := Nat.mul_le_mul_right (2^t) hb
    omega

def guardedAccept {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (side : Bool) (x : X) : Nat → Nat → Prop
  | 0, q => q = 0
  | t+1, q =>
    let prev := q % 2^t
    guardedAccept alice speak side x t prev ∧
      (alice t prev = side → prev + (speak t prev x).toNat * 2^t = q)

theorem guardedLog_rect {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c q : Nat) :
    guardedLog alice speak x y c = q ↔
      guardedAccept alice speak true x c q ∧
      guardedAccept alice speak false y c q := by
  induction c generalizing q with
  | zero =>
    simp [guardedLog, guardedAccept, eq_comm]
  | succ t ih =>
    let prev := q % 2^t
    have hmod : guardedLog alice speak x y (t+1) % 2^t = guardedLog alice speak x y t := by
      rw [guardedLog, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (guardedLog_lt ..)]
    rw [guardedAccept, guardedAccept]
    change guardedLog alice speak x y (t+1) = q ↔
      (guardedAccept alice speak true x t prev ∧ _) ∧
      (guardedAccept alice speak false y t prev ∧ _)
    constructor
    · intro h
      have hp : guardedLog alice speak x y t = prev := by rw [← hmod, h]
      have ha := (ih prev).mp hp
      rw [guardedLog] at h
      rw [hp] at h
      exact ⟨⟨ha.1, fun ea => by
          change alice t prev = true at ea
          simpa [ea] using h⟩,
        ⟨ha.2, fun eb => by
          change alice t prev = false at eb
          simpa [eb] using h⟩⟩
    · rintro ⟨⟨ha, ea⟩, ⟨hb, eb⟩⟩
      have hp := (ih prev).mpr ⟨ha, hb⟩
      rw [guardedLog, hp]
      cases e : alice t prev with
      | false => simpa [e] using eb e
      | true => simpa [e] using ea e

def bobCount (alice : Nat → Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | t+1, q =>
    let prev := q % 2^t
    bobCount alice t prev + (!(alice t prev)).toNat

theorem guardedRun_eq {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x y : X) (c : Nat) :
    (List.range c).foldl (fun (acc : Nat × Nat) tick =>
      let left := alice tick acc.1
      let v := speak tick acc.1 (if left then x else y)
      (acc.1 + (v.toNat <<< tick), acc.2 + (!left).toNat)) (0,0) =
      (guardedLog alice speak x y c, bobCount alice c (guardedLog alice speak x y c)) := by
  induction c with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.shiftLeft_eq, guardedLog, bobCount,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (guardedLog_lt alice speak x y t)]

private theorem bobCount_le (alice : Nat → Nat → Bool) (c q : Nat) :
    bobCount alice c q ≤ c := by
  induction c generalizing q with
  | zero => rfl
  | succ t ih =>
    simp only [bobCount]
    exact Nat.add_le_add (ih _) (Bool.toNat_le _)

open Classical in
private noncomputable def leafWeight {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x : X) (c q : Nat) : Nat :=
  if guardedAccept alice speak true x c q then 2^(c - bobCount alice c q) else 0

private theorem leafWeight_split {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x : X) (t q : Nat) (hq : q < 2^t) :
    leafWeight alice speak x (t+1) q + leafWeight alice speak x (t+1) (q+2^t)
      = 2 * leafWeight alice speak x t q := by
  classical
  have hqmod := Nat.mod_eq_of_lt hq
  have hplus : (q+2^t) % 2^t = q := by simpa using hqmod
  have hp : 0 < 2^t := by positivity
  have hn := bobCount_le alice t q
  have hs : t + 1 - bobCount alice t q = (t - bobCount alice t q) + 1 := by omega
  by_cases ha : guardedAccept alice speak true x t q <;>
    cases turn : alice t q <;> cases bit : speak t q x <;>
    simp [leafWeight, guardedAccept, bobCount, hqmod, hplus, ha, turn, bit, hs, pow_succ,
      Nat.ne_of_gt hp, Nat.ne_of_lt hp] <;> omega

private theorem leafWeight_sum {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x : X) (c : Nat) :
    ∑ q ∈ Finset.range (2^c), leafWeight alice speak x c q = 2^c := by
  induction c with
  | zero => simp [leafWeight, guardedAccept, bobCount]
  | succ t ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    simp_rw [show ∀ q, 2^t + q = q + 2^t from Nat.add_comm _]
    calc
      _ = ∑ q ∈ Finset.range (2^t), 2 * leafWeight alice speak x t q :=
        Finset.sum_congr rfl fun q hq => leafWeight_split alice speak x t q (Finset.mem_range.mp hq)
      _ = _ := by rw [← Finset.mul_sum, ih]; omega

open Classical in
theorem retainedMultiplicity {X : Type*} (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (x : X) (c b : Nat) :
    ((Finset.range (2^c)).filter (fun q =>
      guardedAccept alice speak true x c q ∧ bobCount alice c q ≤ b)).card ≤ 2^b := by
  classical
  let leaves := (Finset.range (2^c)).filter (fun q =>
    guardedAccept alice speak true x c q ∧ bobCount alice c q ≤ b)
  have hmul : leaves.card * 2^c ≤ 2^b * 2^c := by
    calc
      leaves.card * 2^c = ∑ _q ∈ leaves, 2^c := by simp
      _ ≤ ∑ q ∈ leaves, 2^b * leafWeight alice speak x c q := by
        refine Finset.sum_le_sum fun q hq => ?_
        have both := (Finset.mem_filter.mp hq).2
        rw [leafWeight, if_pos both.1, ← pow_add]
        have hc := bobCount_le alice c q
        exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ ∑ q ∈ Finset.range (2^c), 2^b * leafWeight alice speak x c q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = 2^b * 2^c := by rw [← Finset.mul_sum, leafWeight_sum]
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706
open Finset
open Classical in
noncomputable def keptLeft {A X : Type*} [Fintype A] (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (key : A → X) (c b q : Nat) : Finset A :=
  univ.filter fun x => guardedAccept alice speak true (key x) c q ∧ bobCount alice c q ≤ b

open Classical in
noncomputable def keptRight {B X : Type*} [Fintype B] (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (key : B → X) (c q : Nat) : Finset B :=
  univ.filter fun y => guardedAccept alice speak false (key y) c q

theorem keptLeft_sum {A X : Type*} [Fintype A] (alice : Nat → Nat → Bool)
    (speak : Nat → Nat → X → Bool) (key : A → X) (c b : Nat) :
    (∑ q : Fin (2^c), ((keptLeft alice speak key c b q).card : ℝ)) ≤
      (Fintype.card A : ℝ) * 2^b := by
  classical
  simp only [keptLeft, natCast_card_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ _x : A, (2 : ℝ)^b := by
      refine sum_le_sum fun x _ => ?_
      let ind (q : Nat) : ℝ := if guardedAccept alice speak true (key x) c q ∧
          bobCount alice c q ≤ b then 1 else 0
      change (∑ q : Fin (2^c), ind q.val) ≤ _
      rw [Fin.sum_univ_eq_sum_range]
      simp only [ind, sum_boole]
      exact_mod_cast retainedMultiplicity alice speak (key x) c b
    _ = _ := by simp

theorem keptRect_score {A B X : Type*} [Fintype A] [Fintype B]
    (alice : Nat → Nat → Bool) (speak : Nat → Nat → X → Bool)
    (ka : A → X) (kb : B → X) (c b : Nat)
    (read : Nat → B → ℝ) (f : A → B → ℝ) :
    (∑ q : Fin (2^c), ∑ y ∈ keptRight alice speak kb c q,
      read q y * ∑ x ∈ keptLeft alice speak ka c b q, f x y) =
    ∑ x : A, ∑ y : B,
      let q := guardedLog alice speak (ka x) (kb y) c
      if bobCount alice c q ≤ b then read q y * f x y else 0 := by
  classical
  let score (q : Fin (2^c)) (x : A) (y : B) : ℝ :=
    if x ∈ keptLeft alice speak ka c b q ∧ y ∈ keptRight alice speak kb c q
    then read q y * f x y else 0
  calc
    _ = ∑ q : Fin (2^c), ∑ x : A, ∑ y : B, score q x y := by
      refine sum_congr rfl fun q _ => ?_
      rw [sum_comm]
      simp only [keptLeft, keptRight, sum_filter, mul_ite, mul_zero, mul_sum, score,
        mem_filter, mem_univ, true_and]
      refine sum_congr rfl fun y _ => ?_
      split_ifs with h <;> simp [h]
    _ = ∑ x : A, ∑ y : B, ∑ q : Fin (2^c), score q x y := by
      rw [sum_comm]
      exact sum_congr rfl fun x _ => sum_comm
    _ = _ := by
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      let q₀ : Fin (2^c) := ⟨guardedLog alice speak (ka x) (kb y) c, guardedLog_lt ..⟩
      have hrect (q : Fin (2^c)) :
          (x ∈ keptLeft alice speak ka c b q ∧ y ∈ keptRight alice speak kb c q) ↔
            q₀ = q ∧ bobCount alice c q ≤ b := by
        simp only [keptLeft, keptRight, mem_filter, mem_univ, true_and, Fin.ext_iff, q₀,
          guardedLog_rect]
        tauto
      rw [sum_eq_single q₀]
      · simp only [score, hrect q₀, true_and, eq_self]
        by_cases hb : bobCount alice c (guardedLog alice speak (ka x) (kb y) c) ≤ b <;>
          simp [q₀, hb]
      · intro q _ hq
        simp [score, hrect, Ne.symm hq]
      · simp

theorem keptRect_area {A B X : Type*} [Fintype A] [Fintype B]
    (alice : Nat → Nat → Bool) (speak : Nat → Nat → X → Bool)
    (ka : A → X) (kb : B → X) (c b : Nat) :
    (∑ q : Fin (2^c), ((keptLeft alice speak ka c b q).card : ℝ) *
      (keptRight alice speak kb c q).card) ≤ (Fintype.card A : ℝ) * Fintype.card B := by
  classical
  have h := keptRect_score alice speak ka kb c b (fun _ _ => 1) (fun _ _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  rw [show (∑ q : Fin (2^c), ((keptLeft alice speak ka c b q).card : ℝ) *
      (keptRight alice speak kb c q).card) = _ from
      sum_congr rfl (fun q _ => mul_comm _ _), h]
  calc
    _ ≤ ∑ _x : A, ∑ _y : B, (1 : ℝ) := by
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => by split <;> norm_num
    _ = _ := by simp

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706
open Finset

theorem tail_error {A B : Type} [Fintype A] [Fintype B]
    (v : A → B → ℝ) (habs : ∀ x y, |v x y| ≤ 1)
    (omitted : A → B → Prop) [∀ x, DecidablePred (omitted x)] (den : ℝ) (hden : 0 < den) :
    |(∑ x : A, ∑ y : B, v x y) / den -
      (∑ x : A, ∑ y : B, if omitted x y then 0 else v x y) / den| ≤
      (∑ x : A, ∑ y : B, if omitted x y then (1 : ℝ) else 0) / den := by
  classical
  rw [← sub_div, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ x : A, |∑ y : B, (v x y - if omitted x y then 0 else v x y)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ x : A, ∑ y : B, |v x y - if omitted x y then 0 else v x y| :=
      sum_le_sum fun x _ => abs_sum_le_sum_abs ..
    _ ≤ _ := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      split_ifs <;> simp_all

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706

theorem mixture_truncation {ι : Type*} [Fintype ι] (w F G T : ι → ℝ) (U : ℝ)
    (hw : ∀ z, 0 ≤ w z) (hsum : ∑ z, w z = 1) (_hT : ∀ z, 0 ≤ T z)
    (hgap : ∀ z, |F z - G z| ≤ T z) (hG : ∀ z, (G z)^2 ≤ U) :
    (max 0 (|∑ z, w z * F z| - ∑ z, w z * T z))^2 ≤ U := by
  obtain ⟨z₀, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by simp [hsum] : ∑ z, w z ≠ 0)
  have hU := (sq_nonneg (G z₀)).trans (hG z₀)
  have bound (z : ι) : |F z| ≤ Real.sqrt U + T z := by
    have hk : |G z| ≤ Real.sqrt U := by simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt (hG z)
    have hadd := abs_add_le (F z - G z) (G z)
    rw [sub_add_cancel] at hadd
    linarith [hgap z]
  have avg : |∑ z, w z * F z| ≤ Real.sqrt U + ∑ z, w z * T z := by
    calc
      _ ≤ ∑ z, |w z * F z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, w z * (Real.sqrt U + T z) := by
        apply Finset.sum_le_sum
        intro z _
        rw [abs_mul, abs_of_nonneg (hw z)]
        exact mul_le_mul_of_nonneg_left (bound z) (hw z)
      _ = _ := by simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
  have hh : max 0 (|∑ z, w z * F z| - ∑ z, w z * T z) ≤ Real.sqrt U :=
    max_le (Real.sqrt_nonneg _) (by linarith)
  exact ((sq_le_sq₀ (le_max_left _ _) (Real.sqrt_nonneg U)).mpr hh).trans_eq (Real.sq_sqrt hU)

theorem fiber_pairs_sum {α β : Type*} (S : Finset α) (B : Finset β) (f : α × β → ℝ) :
    ∑ p ∈ S ×ˢ B, f p = ∑ a : S, ∑ b : B, f (a.val, b.val) := by
  classical
  rw [Finset.sum_product]
  calc
    _ = ∑ a : S, ∑ b ∈ B, f (a.val, b) :=
      (Finset.sum_coe_sort (s := S) (f := fun a => ∑ b ∈ B, f (a, b))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Finset.sum_coe_sort (s := B) (f := fun b => f (a.val, b))).symm

theorem fiber_pairs_card_pos {α β : Type*} (S : Finset α) (B : Finset β)
    (hS : S.Nonempty) (hB : B.Nonempty) : 0 < ((S ×ˢ B).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr (hS.product hB)

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706
open Finset

noncomputable def averaged {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z]
    (w : Z → ℝ) (u : Z → A → B → ℝ) : ℝ :=
  ∑ z, w z * ((∑ x : A, ∑ y : B, u z x y) / ((Fintype.card A : ℝ) * Fintype.card B))

theorem public_boxes {A B Z X : Type} [Fintype A] [Fintype B] [Fintype Z]
    [Nonempty A] [Nonempty B] (ka : A → X) (kb : B → X)
    (f : A → B → ℝ) (hf : ∀ x y, |f x y| = 1)
    (close : A → A → Prop) [∀ a, DecidablePred (close a)]
    (r D : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hD : 0 ≤ D)
    (hclose : ∀ a, ((univ.filter (close a)).card : ℝ) ≤ D)
    (hcorr : ∀ a a', (∑ y : B, f a y * f a' y) ≤
      (Fintype.card B : ℝ) * (r + (1-r) * (if close a a' then 1 else 0)))
    (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hsum : ∑ z, w z = 1)
    (alice : Z → ℕ → ℕ → Bool) (speak : Z → ℕ → ℕ → X → Bool)
    (read : Z → ℕ → B → ℝ) (hsign : ∀ z j y, (read z j y)^2 = 1)
    (c b : ℕ) :
    let log := fun z x y => guardedLog (alice z) (speak z) (ka x) (kb y) c
    let feedback := fun z x y => bobCount (alice z) c (log z x y)
    (max 0 (|averaged w (fun z x y => read z (log z x y) y * f x y)| -
      averaged w (fun z x y => if b < feedback z x y then 1 else 0)))^2 ≤
      r * 2^b + (1-r) * (2^c * D / Fintype.card A) := by
  classical
  intro log feedback
  let den := (Fintype.card A : ℝ) * Fintype.card B
  have hden : 0 < den := by
    dsimp [den]
    exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  let value := fun z x y => read z (log z x y) y * f x y
  let full := fun z => (∑ x : A, ∑ y : B, value z x y) / den
  let kept := fun z => (∑ x : A, ∑ y : B, if b < feedback z x y then 0 else value z x y) / den
  let tail := fun z => (∑ x : A, ∑ y : B, if b < feedback z x y then (1 : ℝ) else 0) / den
  have hval z x y : |value z x y| ≤ 1 := by
    dsimp only [value]
    rw [abs_mul, hf, mul_one]
    have hh := hsign z (log z x y) y
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have htrunc z : |full z - kept z| ≤ tail z :=
    tail_error (value z) (hval z) (fun x y => b < feedback z x y) den hden
  have hkeep z : (kept z)^2 ≤ r * 2^b + (1-r) * (2^c * D / Fintype.card A) := by
    have v := rectangle_bound (M := Fin (2^c)) f (fun j y => read z j y)
      (fun j => keptLeft (alice z) (speak z) ka c b j)
      (fun j => keptRight (alice z) (speak z) kb c j)
      close r D (2^b) hr0 hr1 hD hclose hcorr (fun j => hsign z j)
      (keptRect_area (alice z) (speak z) ka kb c b) (keptLeft_sum (alice z) (speak z) ka c b)
    rw [keptRect_score (alice z) (speak z) ka kb c b (read z) f] at v
    have flip (n : ℕ) (x : ℝ) : (if n ≤ b then x else 0) = (if b < n then 0 else x) := by
      by_cases hn : n ≤ b
      · simp [hn, not_lt.mpr hn]
      · simp [hn, lt_of_not_ge hn]
    simpa only [kept, den, feedback, log, value, flip,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using v
  apply mixture_truncation w full kept tail _ hw hsum _ htrunc hkeep
  intro z
  apply div_nonneg _ hden.le
  apply sum_nonneg
  intro x _
  apply sum_nonneg
  intro y _
  split <;> norm_num

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706
open Finset

theorem model_protocol_bound {m : ℕ} {R X Z : Type} [Fintype R] [Nonempty R] [Fintype Z]
    (φ ψ : (Fin m → Block) → Bool) (ka kb : Input m R → X)
    (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hsum : ∑ z, w z = 1)
    (alice : Z → ℕ → ℕ → Bool) (speak : Z → ℕ → ℕ → X → Bool)
    (read : Z → ℕ → X → Bool) (c b h : ℕ) :
    let log := fun z x y => guardedLog (alice z) (speak z) (ka x) (kb y) c
    let val := fun z x y => bitSign (read z (log z x y) (kb y)) * bitSign (modelTruth φ ψ x.1 y.1)
    let tail := fun z x y => if b < bobCount (alice z) c (log z x y) then (1 : ℝ) else 0
    let ball := ∑ j ∈ range (h+1), m.choose j * 7^j
    (2 : ℝ)^(h+1) * 8^m * (max 0 (|averaged w val| - averaged w tail))^2 ≤
      2^b * 8^m + ((2 : ℝ)^(h+1)-1) * 2^c * (ball : ℝ) := by
  classical
  intro log val tail ball
  let r : ℝ := (1/2)^(h+1)
  let N : ℝ := Fintype.card R
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨hc, hclose, hcorr⟩ := model_stats (R := R) φ ψ h
  have hsignabs (u : Bool) : |bitSign u| = 1 := by cases u <;> norm_num [bitSign]
  have hg := public_boxes ka kb (fun x y => bitSign (modelTruth φ ψ x.1 y.1))
    (fun x y => hsignabs _) (fun x y => distance x.1 y.1 ≤ h) r ((ball : ℝ)*N)
    (by dsimp [r]; positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    hclose hcorr w hw hsum alice speak (fun z q y => bitSign (read z q (kb y)))
    (fun z q y => sign_sq _) c b
  change (max 0 (|averaged w val| - averaged w tail))^2 ≤
    r*2^b + (1-r) * (2^c*((ball : ℝ)*N)/(Fintype.card (Input m R) : ℝ)) at hg
  rw [hc] at hg
  have hcancel : (2:ℝ)^c*((ball:ℝ)*N) / (8^m*N) = 2^c*(ball:ℝ)/8^m := by field_simp
  change (max 0 (|averaged w val| - averaged w tail))^2 ≤
    r*2^b + (1-r) * (2^c*((ball : ℝ)*N)/(8^m*N)) at hg
  rw [hcancel] at hg
  calc
    _ ≤ (2:ℝ)^(h+1)*8^m*(r*2^b+(1-r)*(2^c*(ball:ℝ)/8^m)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by dsimp [r]; rw [one_div_pow]; field_simp

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706

private theorem num_pow_slope (x : ℝ) (hx : 0 ≤ x) (n : Nat) :
    (1+x)^n * (1-(n:ℝ)*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh : (1+x) * (1-((n:ℝ)+1)*x) ≤ 1-(n:ℝ)*x := by
      have hnon : 0 ≤ ((n:ℝ)+1)*x^2 := by positivity
      nlinarith
    rw [pow_succ, Nat.cast_succ, mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_left hh (by positivity)) ih

private theorem num_exp_bound (m : Nat) :
    (1+(7:ℝ)/65536)^m ≤ (2:ℝ)^(m/4096+1) := by
  have h := num_pow_slope ((7:ℝ)/65536) (by norm_num) 4096
  have hc : 1-(4096:ℝ)*(7/65536) = 9/16 := by norm_num
  have hcast : ((4096:Nat):ℝ) = 4096 := by norm_num
  rw [hcast,hc] at h
  have slack (z : ℝ) (hz : z*(9/16) ≤ 1) : z ≤ 2 := by linarith only [hz]
  have hblock : (1+(7:ℝ)/65536)^4096 ≤ 2 := slack _ h
  calc
    (1+(7:ℝ)/65536)^m ≤ (1+(7:ℝ)/65536)^(4096*(m/4096+1)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    _ = ((1+(7:ℝ)/65536)^4096)^(m/4096+1) := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg (by norm_num) _) hblock _

private theorem num_ball_bound (m h : Nat) (hh : h ≤ m) :
    ((∑ j ∈ Finset.range (h+1), Nat.choose m j * 7^j : Nat) : ℝ) ≤
      (2:ℝ)^(16*h+m/4096+1) := by
  let x : ℝ := 7/65536
  have hx : 0 ≤ x := by dsimp [x]; norm_num
  have h7 : (7:ℝ) = 65536*x := by dsimp [x]; norm_num
  have point (j : Nat) (hj : j ∈ Finset.range (h+1)) :
      (m.choose j : ℝ)*7^j ≤ (65536:ℝ)^h*(x^j * (m.choose j : ℝ)) := by
    have hle : (65536:ℝ)^j ≤ (65536:ℝ)^h :=
      pow_le_pow_right₀ (by norm_num) (by simpa using Finset.mem_range.mp hj)
    calc
      (m.choose j : ℝ)*7^j = (65536:ℝ)^j*(x^j*(m.choose j : ℝ)) := by
        rw [h7,mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  have sub : Finset.range (h+1) ⊆ Finset.range (m+1) := Finset.range_mono (by omega)
  have expand : (∑ j ∈ Finset.range (m+1), x^j*(m.choose j : ℝ)) = (1+x)^m := by
    rw [add_comm (1:ℝ) x, add_pow]
    simp
  have hteen : (65536:ℝ) = 2^16 := by norm_num
  push_cast
  calc
    (∑ j ∈ Finset.range (h+1), (m.choose j : ℝ)*7^j)
        ≤ ∑ j ∈ Finset.range (h+1), (65536:ℝ)^h*(x^j*(m.choose j : ℝ)) :=
      Finset.sum_le_sum point
    _ = (65536:ℝ)^h * ∑ j ∈ Finset.range (h+1), x^j*(m.choose j : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (65536:ℝ)^h * ∑ j ∈ Finset.range (m+1), x^j*(m.choose j : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ (65536:ℝ)^h * (2:ℝ)^(m/4096+1) := by
      rw [expand]; exact mul_le_mul_of_nonneg_left (num_exp_bound m) (by positivity)
    _ = _ := by rw [hteen, ← pow_mul, ← pow_add]; congr 1

theorem numeric_finish (m c : Nat) (gap : Nat → ℝ)
    (first : ∀ b h : Nat, h ≤ m →
      (2:ℝ)^(h+1)*8^m*(gap b)^2 ≤ 2^b*8^m+
        ((2:ℝ)^(h+1)-1)*2^c*((∑ j ∈ Finset.range (h+1), Nat.choose m j*7^j : Nat):ℝ))
    (hc : c ≤ 3*m-m/1280+2) :
    (2:ℝ)^(m/65536)*(gap (m/65536))^2 ≤ 17 := by
  let b := m/65536
  let h := 2*b
  let ball : ℝ := ((∑ j ∈ Finset.range (h+1), Nat.choose m j*7^j : Nat):ℝ)
  have hh : h ≤ m := by dsimp [h,b]; omega
  have hbnd : b+c+(16*h+m/4096+1) ≤ 3*m+4 := by dsimp [h,b]; omega
  have h8 : (8:ℝ) = 2^3 := by norm_num
  have h16 : (16:ℝ) = 2^4 := by norm_num
  have term1 : (2:ℝ)^b*2^b ≤ (2:ℝ)^(h+1) := by
    rw [← pow_add]; apply pow_le_pow_right₀ (by norm_num); dsimp [h]; omega
  have term2 : (2:ℝ)^b * 2^c * ball ≤ 16*8^m := by
    calc
      (2:ℝ)^b*2^c*ball ≤ 2^b*2^c*2^(16*h+m/4096+1) :=
        mul_le_mul_of_nonneg_left (num_ball_bound m h hh) (by positivity)
      _ = (2:ℝ)^(b+c+(16*h+m/4096+1)) := by simp only [pow_add,mul_assoc]
      _ ≤ (2:ℝ)^(3*m+4) := pow_le_pow_right₀ (by norm_num) hbnd
      _ = _ := by rw [pow_add,h16,h8,← pow_mul,mul_comm]
  have H : 0 < (2:ℝ)^(h+1)*8^m := by positivity
  have B : 0 ≤ ball := by dsimp [ball]; positivity
  have G := mul_le_mul_of_nonneg_left (first b h hh) (show (0:ℝ) ≤ 2^b by positivity)
  have T1 := mul_le_mul_of_nonneg_right term1 (show (0:ℝ) ≤ 8^m by positivity)
  have T2 := mul_le_mul_of_nonneg_left term2 (show (0:ℝ) ≤ 2^(h+1) by positivity)
  have T3 : (2:ℝ)^b*2^c*ball*1 ≥ 0 := by positivity
  change (2:ℝ)^b*(gap b)^2 ≤ 17
  apply (le_of_mul_le_mul_left _ H)
  change (2:ℝ)^b*((2:ℝ)^(h+1)*8^m*(gap b)^2) ≤
    (2:ℝ)^b*(2^b*8^m + ((2:ℝ)^(h+1)-1)*2^c*ball) at G
  nlinarith only [G,T1,T2,T3]

end PEqualNP.Outside.L_meta_30706

namespace PEqualNP.Outside.L_meta_30706

theorem fiber_average_eq {K A B Z : Type} [Fintype A] [Fintype B] [Fintype Z]
    (fiber : Finset K) (ea : (fiber : Type) ≃ A) (eb : (fiber : Type) ≃ B)
    (w : Z → ℝ) (f : Z → K × K → ℝ) :
    (∑ z, w z * ∑ p ∈ fiber.product fiber, f z p) / ((fiber.product fiber).card : ℝ) =
      ∑ z, w z * ((∑ x : A, ∑ y : B, f z ((ea.symm x).val, (eb.symm y).val)) /
        ((Fintype.card A : ℝ) * Fintype.card B)) := by
  classical
  have hsum (z : Z) : (∑ p ∈ fiber.product fiber, f z p) =
      ∑ x : A, ∑ y : B, f z ((ea.symm x).val, (eb.symm y).val) := by
    calc
      _ = ∑ x ∈ fiber, ∑ y ∈ fiber, f z (x, y) := Finset.sum_product _ _ _
      _ = ∑ x : fiber, ∑ y : fiber, f z (x.val, y.val) := by
        rw [← Finset.sum_coe_sort fiber (fun x => ∑ y ∈ fiber, f z (x,y))]
        exact Finset.sum_congr rfl (fun x _ =>
          (Finset.sum_coe_sort fiber (fun y => f z (x.val,y))).symm)
      _ = _ := Fintype.sum_equiv ea _ _ (fun x =>
        Fintype.sum_equiv eb _ _ (fun y => by simp))
  have ha : fiber.card = Fintype.card A := by simpa using Fintype.card_congr ea
  have hb : fiber.card = Fintype.card B := by simpa using Fintype.card_congr eb
  have hcard : (fiber.product fiber).card = Fintype.card A * Fintype.card B :=
    (Finset.card_product fiber fiber).trans (congrArg₂ (· * ·) ha hb)
  simp only [hcard, Nat.cast_mul, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [hsum, mul_assoc]

end PEqualNP.Outside.L_meta_30706

open Finset PEqualNP.Outside.L_meta_30706

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_30706 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  ∀ (c s : Nat) (weight : Fin s → ℝ),
    (∀ z, 0 ≤ weight z) → (∑ z : Fin s, weight z) = 1 →
    ∀ (aliceTurn : Fin s → Nat → Nat → Bool)
      (emit : Fin s → Nat → Nat → K → Bool)
      (decode : Fin s → Nat → K → Bool),
      let run := fun (z : Fin s) (x y : K) =>
        (List.range c).foldl (fun (acc : Nat × Nat) tick =>
          let left := aliceTurn z tick acc.1
          let v := emit z tick acc.1 (if left then x else y)
          (acc.1 + (v.toNat <<< tick), acc.2 + (!left).toNat)) (0,0)
      let mean := fun (f : Fin s → K × K → ℝ) =>
        (∑ z : Fin s, weight z * ∑ p ∈ pairs, f z p) / (pairs.card : ℝ)
      let bias := mean (fun z p => if decode z (run z p.1 p.2).1 p.2 = truth p.1 p.2
        then (1 : ℝ) else -1)
      let gap := fun (b : Nat) =>
        let tail := mean (fun z p => if b < (run z p.1 p.2).2 then (1 : ℝ) else 0)
        max 0 (|bias| - tail)
      (∀ (b h : Nat), h ≤ m →
        let ball := ∑ j ∈ Finset.range (h+1), Nat.choose m j * 7^j
        (2 : ℝ)^(h+1) * 8^m * (gap b)^2 ≤
          (2 : ℝ)^b * 8^m + ((2 : ℝ)^(h+1)-1) * 2^c * (ball : ℝ)) ∧
      (c ≤ 3*m - m/1280 + 2 →
        (2 : ℝ)^(m/65536) * (gap (m/65536))^2 ≤ 17)) := by
  classical
  intro k hk0 constant rot step state injected bit m starts hm hinj good row ref hgood pin hpin hfree K fiber
    pairs truth c s weight hw hsum aliceTurn emit decode run mean bias gap
  let windows : Fin m × Fin 12 → Fin k := fun ij =>
    ⟨(starts ij.1 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  have hwin : Function.Injective windows := by
    intro a b h
    exact hinj (congrArg Fin.val h)
  have hk : 12 ≤ k := by
    have hc := Fintype.card_le_of_injective windows hwin
    simp [Fintype.card_prod] at hc
    omega
  let coord : Fin m × Fin 3 → Fin k := fun ij =>
    ⟨(starts ij.1 + 9 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  let lift : Fin m × Fin 3 → Fin m × Fin 12 := fun ij =>
    (ij.1, ⟨9 + ij.2.val, by omega⟩)
  have hcoord : Function.Injective coord := by
    intro a b h
    have hh : windows (lift a) = windows (lift b) := by
      apply Fin.ext
      simpa only [windows, lift, coord, Nat.add_assoc] using congrArg Fin.val h
    have he := hwin hh
    apply Prod.ext
    · have hfst := congrArg Prod.fst he
      exact hfst
    · apply Fin.ext
      have hn := congrArg (fun x : Fin m × Fin 12 => x.2.val) he
      change 9 + a.2.val = 9 + b.2.val at hn
      omega
  have hcFree (ij : Fin m × Fin 3) : coord ij ∉ pin := by
    intro h
    exact hfree ij.1 ij.2 (coord ij) h rfl
  let eBits := shareBitsEquiv hk constant row ref
  have hFiber (q : Fin (2^k)) : q ∈ fiber ↔ ∀ z ∈ pin, eBits q z = false := by
    change (q ∈ univ.filter (fun key : Fin (2^k) =>
      ∀ z ∈ pin, bitFn k constant row.val 0 key.val z.val = bitFn k constant row.val 0 ref.val z.val)) ↔ _
    simp only [mem_filter, mem_univ, true_and]
    change (∀ z ∈ pin, bitFn k constant row.val 0 q.val z.val = bitFn k constant row.val 0 ref.val z.val) ↔
      ∀ z ∈ pin, xor (bitFn k constant row.val 0 q.val z.val) (bitFn k constant row.val 0 ref.val z.val) = false
    simp only [xor_false_iff]
  let Extra := Remainder pin coord → Bool
  let Side := Input m Extra
  let left : fiber ≃ Side := (eBits.subtypeEquiv hFiber).trans (splitBits pin coord hcoord hcFree)
  let shifts := fun i => windowShift constant row ref (starts i)
  let right : fiber ≃ Side := left.trans (Equiv.prodCongr (shiftBlock shifts) (Equiv.refl Extra))
  let flag := fun i => windowFlag constant row ref (starts i)
  let base := fun i => xor (!affine (flag i) (point (flag i)))
    (injectedFn k constant 2 ref.val (starts i+5))
  let φ := fun x : Fin m → Block => xor (parityOn univ base)
    (parityOn univ (fun i => affine (flag i) (x i)))
  let ψ := fun y : Fin m → Block => parityOn univ (fun i => affine (flag i) (y i))
  let model : Side → Side → Bool := fun x y => modelTruth φ ψ x.1 y.1
  have hLeft (q : fiber) (i : Fin m) : (left q).1 i = windowShare constant row ref q.val (starts i) := by
    change toBlock (fun j => shareBit k constant row ref q.val (coord (i,j)).val) = _
    dsimp only [toBlock, coord, windowShare]
    rw [shareBit_mod hk, shareBit_mod hk, shareBit_mod hk]
    rfl
  have hRight (q : fiber) (i : Fin m) : (right q).1 i =
      bxor (windowShare constant row ref q.val (starts i)) (shifts i) := by
    change bxor ((left q).1 i) (shifts i) = _
    rw [hLeft]
  have hpinShare (q : fiber) (i : Fin m) (j : ℕ) (hj : j < 9) :
      shareBit k constant row ref q.val (starts i+j) = false := by
    obtain ⟨z, hz, hzval⟩ := hpin i ⟨j, hj⟩
    have hs := (hFiber q.val).mp q.property z hz
    change shareBit k constant row ref q.val z.val = false at hs
    rw [hzval, shareBit_mod hk] at hs
    exact hs
  have hTruth (x y : fiber) : truth x.val y.val = model (left x) (right y) := by
    have hrow (i : Fin m) :
        bitFn k constant row.val 2 (combine ref x.val y.val).val (starts i+5) =
          xor (xor (xor (base i) (affine (flag i) ((left x).1 i)))
            (affine (flag i) ((right y).1 i))) (decide ((left x).1 i = (right y).1 i)) := by
      rw [hLeft, hRight]
      exact guarded_window hk constant row ref x.val y.val (starts i) (hpinShare x i) (hpinShare y i)
        (hgood i).1 (hgood i).2.2.1 (hgood i).2.2.2
    change parityOn univ (fun i => bitFn k constant row.val 2 (combine ref x.val y.val).val (starts i+5)) = _
    rw [funext hrow]
    simp only [model, modelTruth, parity_xor, φ, ψ]
  let ka : Side → K := fun x => (left.symm x).val
  let kb : Side → K := fun y => (right.symm y).val
  let log := fun (z : Fin s) (x y : Side) => guardedLog (aliceTurn z) (emit z) (ka x) (kb y) c
  let val := fun (z : Fin s) (x y : Side) => bitSign (decode z (log z x y) (kb y)) * bitSign (model x y)
  let tail := fun (b : ℕ) (z : Fin s) (x y : Side) =>
    if b < bobCount (aliceTurn z) c (log z x y) then (1 : ℝ) else 0
  have ht (x y : Side) : truth (ka x) (kb y) = model x y := by
    simpa only [ka, kb, Equiv.apply_symm_apply] using hTruth (left.symm x) (right.symm y)
  have hrun (z : Fin s) (x y : K) : run z x y =
      (guardedLog (aliceTurn z) (emit z) x y c,
       bobCount (aliceTurn z) c (guardedLog (aliceTurn z) (emit z) x y c)) :=
    guardedRun_eq (aliceTurn z) (emit z) x y c
  have hmean (f : Fin s → K × K → ℝ) (g : Fin s → Side → Side → ℝ)
      (hfg : ∀ z x y, f z (ka x, kb y) = g z x y) : mean f = averaged weight g := by
    calc
      mean f = averaged weight (fun z x y => f z (ka x, kb y)) :=
        fiber_average_eq fiber left right weight f
      _ = _ := congrArg (averaged weight) (funext fun z => funext fun x => funext fun y => hfg z x y)
  have signs (a b : Bool) : (if a = b then (1 : ℝ) else -1) = bitSign a * bitSign b := by
    cases a <;> cases b <;> norm_num [bitSign]
  have hbias : bias = averaged weight val := by
    apply hmean (fun z p => if decode z (run z p.1 p.2).1 p.2 = truth p.1 p.2 then (1 : ℝ) else -1) val
    intro z x y
    change (if decode z (run z (ka x) (kb y)).1 (kb y) = truth (ka x) (kb y) then (1 : ℝ) else -1) = _
    rw [hrun, ht]
    exact signs _ _
  have htail (b : ℕ) : mean (fun z p => if b < (run z p.1 p.2).2 then (1 : ℝ) else 0) =
      averaged weight (tail b) := by
    apply hmean
    intro z x y
    change (if b < (run z (ka x) (kb y)).2 then (1 : ℝ) else 0) = _
    rw [hrun]
  have hgap (b : ℕ) : gap b = max 0 (|averaged weight val| - averaged weight (tail b)) := by
    change max 0 (|bias| - mean (fun z p => if b < (run z p.1 p.2).2 then (1 : ℝ) else 0)) = _
    rw [hbias, htail]
  have first (b h : ℕ) (_hh : h ≤ m) :
      (2 : ℝ)^(h+1) * 8^m * (gap b)^2 ≤ 2^b * 8^m + ((2 : ℝ)^(h+1)-1) * 2^c *
        ((∑ j ∈ Finset.range (h+1), Nat.choose m j * 7^j : ℕ) : ℝ) := by
    rw [hgap]
    exact model_protocol_bound (R := Extra) φ ψ ka kb weight hw hsum aliceTurn emit decode c b h
  exact ⟨first, numeric_finish m c gap first⟩
