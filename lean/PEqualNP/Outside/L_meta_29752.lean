import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620
import Mathlib.Data.Nat.Choose.Sum

namespace PEqualNP.Outside.L_meta_29752

open Finset

private def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

private def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

private def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k))
    ((constant round).val.testBit (pos % k))

private def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

private lemma rotFn_lt {k : ℕ} (s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma rotFn_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
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

private lemma mod_sub_one {k n : ℕ} (hk : 1 ≤ k) :
    (n % k + k - 1 % k) % k = (n + k - 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : n % k < k := Nat.mod_lt n (by omega)
    have hrew : n % k + k - 1 = n % k + (k - 1) := by omega
    have hrew2 : n + k - 1 = n + (k - 1) := by omega
    rw [hrew, hrew2, Nat.mod_add_mod]

private lemma bitFn_zero {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    bitFn k constant row 0 key pos =
      xor (key.testBit ((pos + k - 1) % k)) (row.testBit (pos % k)) := by
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]

private abbrev Block := Bool × Bool × Bool

private def bxor (x y : Block) : Block :=
  (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2 y.2.2)

private def affine (flag : Bool) (x : Block) : Bool :=
  if flag then x.1 else x.2.1

private def point (flag : Bool) : Block := (true, true, flag)

private def localValue (α β δ f₅ : Bool) (x : Block) : Bool :=
  let u := xor α x.1
  let v := xor β ((!x.1) && x.2.1)
  let w := xor δ ((x.1 == x.2.1) && x.2.2)
  let s₅ := xor (xor β f₅) u
  let s₆ := xor (xor f₅ u) v
  let s₇ := xor (xor u v) w
  xor s₅ ((!s₆) && s₇)

private lemma localValue_eq (α β δ f₅ : Bool) (x : Block)
    (h : xor β f₅ = !α) :
    localValue α β δ f₅ x =
      xor (!affine (xor (xor α β) δ) x) (decide (x = point (xor (xor α β) δ))) := by
  rcases x with ⟨a, b, c⟩
  cases α <;> cases β <;> cases δ <;> cases f₅ <;> cases a <;> cases b <;> cases c <;>
    first | decide | contradiction

private def shareBit (k : ℕ) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) : Bool :=
  xor (bitFn k constant row.val 0 key.val pos) (bitFn k constant row.val 0 ref.val pos)

private lemma shareBit_eq {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key pos =
      xor (key.val.testBit ((pos + k - 1) % k)) (ref.val.testBit ((pos + k - 1) % k)) := by
  unfold shareBit
  rw [bitFn_zero hk constant key.isLt, bitFn_zero hk constant ref.isLt]
  cases key.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;>
    cases row.val.testBit (pos % k) <;> rfl

private def combine {k : ℕ} (ref left right : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(left.val ^^^ right.val ^^^ ref.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

private lemma shareBit_combine {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref (combine ref left right) pos =
      xor (shareBit k constant row ref left pos) (shareBit k constant row ref right pos) := by
  simp only [shareBit_eq hk, combine, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    decide_eq_true (Nat.mod_lt _ (by omega : 0 < k)), Bool.true_and]
  cases left.val.testBit ((pos + k - 1) % k) <;>
    cases right.val.testBit ((pos + k - 1) % k) <;>
    cases ref.val.testBit ((pos + k - 1) % k) <;> rfl

private lemma shareBit_mod {k : ℕ} (_hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pos : ℕ) :
    shareBit k constant row ref key (pos % k) = shareBit k constant row ref key pos := by
  unfold shareBit bitFn
  rw [Nat.mod_mod]

private noncomputable def shareBitsEquiv {k : ℕ} (hk : 12 ≤ k)
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

private def toBlock (f : Fin 3 → Bool) : Block := (f 0, f 1, f 2)

private def fromBlock (x : Block) (j : Fin 3) : Bool :=
  if j = 0 then x.1 else if j = 1 then x.2.1 else x.2.2

private lemma toBlock_fromBlock (x : Block) : toBlock (fromBlock x) = x := by
  rcases x with ⟨a, b, c⟩
  rfl

private lemma fromBlock_toBlock (f : Fin 3 → Bool) (j : Fin 3) : fromBlock (toBlock f) j = f j := by
  fin_cases j <;> rfl

private abbrev Remainder {m k : ℕ} (pin : Finset (Fin k)) (coord : Fin m × Fin 3 → Fin k) :=
  {j : Fin k // j ∉ pin ∧ j ∉ Set.range coord}

private noncomputable def splitBits {m k : ℕ} (pin : Finset (Fin k))
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

private lemma extract_local {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
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

private def windowFlag {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Bool :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  let pair := xor (old 7) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injectedFn k constant 1 ref.val (p+6))
  let β := xor (xor (old 6) pair) (injectedFn k constant 1 ref.val (p+7))
  let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
  xor (xor α β) δ

private def windowOffset {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  let old := fun j => bitFn k constant row.val 0 ref.val (p+j)
  (xor (old 9) (xor (old 7) (old 8)), xor (old 10) (old 7), xor (old 11) (old 8))

private def windowShare {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref key : Fin (2 ^ k)) (p : ℕ) : Block :=
  (shareBit k constant row ref key (p+9), shareBit k constant row ref key (p+10),
    shareBit k constant row ref key (p+11))

private def windowShift {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Block :=
  bxor (windowOffset constant row ref p) (point (windowFlag constant row ref p))

private lemma xor_left_eq (a b c : Bool) : xor a b = c ↔ a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

private lemma bxor_eq (a b c : Block) : bxor a b = c ↔ a = bxor b c := by
  rcases a with ⟨aa, ab, ac⟩
  rcases b with ⟨ba, bb, bc⟩
  rcases c with ⟨ca, cb, cc⟩
  simp only [bxor, Prod.mk.injEq, xor_left_eq]

private lemma bxor_assoc (a b c : Block) : bxor (bxor a b) c = bxor a (bxor b c) := by
  simp [bxor]

private lemma bxor_comm (a b : Block) : bxor a b = bxor b a := by
  simp [bxor, Bool.xor_comm]

private lemma bxor_cancel (a b : Block) : bxor a (bxor a b) = b := by
  rcases b with ⟨b₁, b₂, b₃⟩
  simp [bxor]

private lemma bxor_cancel_right (a b : Block) : bxor (bxor a b) b = a := by
  rw [bxor_comm (bxor a b) b, bxor_comm a b, bxor_cancel]

private lemma xor_recover (a b c : Bool) : xor (xor a b) (xor b c) = xor a c := by
  cases a <;> cases b <;> cases c <;> rfl

private lemma affine_bxor (f : Bool) (a b : Block) : affine f (bxor a b) = xor (affine f a) (affine f b) := by
  cases f <;> rfl

private lemma guarded_window {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
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

private def parityOn {I : Type} (s : Finset I) (f : I → Bool) : Bool :=
  (∑ i ∈ s, (f i).toNat) % 2 == 1

private lemma parity_add (a b : ℕ) : ((a+b)%2 == 1) = xor (a%2 == 1) (b%2 == 1) := by
  have ha : a%2 = 0 ∨ a%2 = 1 := by omega
  have hb : b%2 = 0 ∨ b%2 = 1 := by omega
  rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> rfl

private lemma parity_insert {I : Type} [DecidableEq I] {s : Finset I} {i : I} (hi : i ∉ s) (f : I → Bool) :
    parityOn (insert i s) f = xor (f i) (parityOn s f) := by
  unfold parityOn
  rw [sum_insert hi, parity_add]
  cases f i <;> rfl

private lemma parity_xor {I : Type} (s : Finset I) (f g : I → Bool) :
    parityOn s (fun i => xor (f i) (g i)) = xor (parityOn s f) (parityOn s g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    simp only [parity_insert hi, ih, Bool.xor_assoc, Bool.xor_left_comm]

private def bitSign (b : Bool) : ℚ := if b then -1 else 1

private lemma sign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> norm_num [bitSign]

private lemma sign_sq (a : Bool) : bitSign a ^ 2 = 1 := by cases a <;> norm_num [bitSign]

private lemma sign_parity {I : Type} (s : Finset I) (f : I → Bool) :
    bitSign (parityOn s f) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [parityOn, bitSign]
  | @insert i s hi ih => rw [parity_insert hi, sign_xor, ih, prod_insert hi]

private def modelTruth {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x y : Fin m → Block) : Bool :=
  xor (xor (φ x) (ψ y)) (parityOn univ fun i => decide (x i = y i))

private def support {m : ℕ} {B : Type} (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (x : Fin m → B) : Finset (Fin m) := univ.filter (fun i => p i (x i))

private lemma card_support {m : ℕ} {B : Type} [Fintype B] (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
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

private def distance {m : ℕ} (x y : Fin m → Block) : ℕ :=
  (univ.filter (fun i => x i ≠ y i)).card

private lemma card_block_ne : ∀ x : Block, (univ.filter (fun y : Block => x ≠ y)).card = 7 := by
  decide +kernel

private lemma card_near {m : ℕ} (h : ℕ) (x : Fin m → Block) :
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

private lemma card_code (m : ℕ) : Fintype.card (Fin m → Block) = 8 ^ m := by
  simp [Fintype.card_prod]

private lemma local_correlation : ∀ x y : Block,
    (∑ z : Block, bitSign (decide (x = z)) * bitSign (decide (y = z))) =
      if x ≠ y then (4 : ℚ) else 8 := by
  decide +kernel

private lemma correlation {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x x' : Fin m → Block) :
    (∑ y : Fin m → Block, bitSign (modelTruth φ ψ x y) * bitSign (modelTruth φ ψ x' y)) =
      (bitSign (φ x) * bitSign (φ x')) * (8 : ℚ)^m * (1 / 2)^distance x x' := by
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
  have hp : (8 : ℚ)^m = 8^distance x x' * 8^(m-distance x x') := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  rw [hp, show (4 : ℚ) = 8 * (1/2) by norm_num, mul_pow]
  ring

private def agreement {A B : Type} [Fintype A] [Fintype B] (truth guess : A → B → Bool) : ℚ :=
  ((univ.filter (fun z : A × B => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) /
    ((Fintype.card A : ℚ) * (Fintype.card B : ℚ))

private lemma score_bias {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (truth guess : A → B → Bool) :
    (∑ a : A, ∑ b : B, bitSign (guess a b) * bitSign (truth a b)) =
      ((Fintype.card A : ℚ) * (Fintype.card B : ℚ)) * (2 * agreement truth guess - 1) := by
  let P := fun z : A × B => guess z.1 z.2 = truth z.1 z.2
  have hind (z : A × B) : bitSign (guess z.1 z.2) * bitSign (truth z.1 z.2) =
      2 * (if P z then (1 : ℚ) else 0) - 1 := by
    dsimp only [P]
    cases guess z.1 z.2 <;> cases truth z.1 z.2 <;> norm_num [bitSign]
  rw [← Fintype.sum_prod_type (fun z : A × B => bitSign (guess z.1 z.2) * bitSign (truth z.1 z.2))]
  simp_rw [hind, sum_sub_distrib, ← mul_sum, ← sum_filter, sum_const]
  simp only [nsmul_eq_mul, mul_one, card_univ, Fintype.card_prod, Nat.cast_mul]
  unfold agreement
  change 2 * ((univ.filter P).card : ℚ) - _ = _
  have hA : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  field_simp
  ring

private lemma error_count {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (truth guess : A → B → Bool) :
    1 - agreement truth guess =
      ((univ.filter (fun z : A × B => guess z.1 z.2 ≠ truth z.1 z.2)).card : ℚ) /
        ((Fintype.card A : ℚ) * (Fintype.card B : ℚ)) := by
  let P := fun z : A × B => guess z.1 z.2 = truth z.1 z.2
  have h := card_filter_add_card_filter_not (s := (univ : Finset (A × B))) (p := P)
  rw [card_univ, Fintype.card_prod] at h
  have hcast : ((univ.filter P).card : ℚ) + ((univ.filter (fun z => ¬ P z)).card : ℚ) =
      (Fintype.card A : ℚ) * (Fintype.card B : ℚ) := by exact_mod_cast h
  have hA : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  unfold agreement
  change 1 - ((univ.filter P).card : ℚ) / _ = ((univ.filter (fun z => ¬ P z)).card : ℚ) / _
  field_simp
  linarith

set_option maxHeartbeats 2000000 in
private lemma bound_bias {A B M : Type} [Fintype A] [Fintype B] [Fintype M] [Nonempty A] [Nonempty B]
    (truth : A → B → Bool) (send : A → M) (read : M → B → Bool)
    (close : A → A → Prop) [∀ a, DecidablePred (close a)]
    (r D : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hD : 0 ≤ D)
    (hclose : ∀ a, ((univ.filter (close a)).card : ℚ) ≤ D)
    (hcorr : ∀ a a', (∑ b : B, bitSign (truth a b) * bitSign (truth a' b)) ≤
      (Fintype.card B : ℚ) * (r + (1-r) * (if close a a' then 1 else 0))) :
    (2 * agreement truth (fun a b => read (send a) b) - 1)^2 ≤
      r + (1-r) * ((Fintype.card M : ℚ) * D / Fintype.card A) := by
  classical
  let Acount : ℚ := Fintype.card A
  let Bcount : ℚ := Fintype.card B
  have hA : 0 < Acount := by dsimp [Acount]; exact_mod_cast Fintype.card_pos
  have hB : 0 < Bcount := by dsimp [Bcount]; exact_mod_cast Fintype.card_pos
  let bucket := fun j : M => univ.filter (fun a => send a = j)
  let n := fun j => ((bucket j).card : ℚ)
  let V := fun (j : M) (b : B) => ∑ a ∈ bucket j, bitSign (truth a b)
  let S := fun j : M => ∑ b : B, bitSign (read j b) * V j b
  let W := fun j : M => Bcount^2 * (r * n j + (1-r)*D)
  have hnear (j : M) (a : A) : (( (bucket j).filter (close a)).card : ℚ) ≤ D := by
    refine le_trans ?_ (hclose a)
    exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ (bucket j)))
  have hinner (j : M) (a : A) :
      (∑ a' ∈ bucket j, ∑ b : B, bitSign (truth a b) * bitSign (truth a' b)) ≤
        Bcount * (r * n j + (1-r)*D) := by
    calc
      _ ≤ ∑ a' ∈ bucket j, Bcount * (r + (1-r) * (if close a a' then 1 else 0)) :=
        sum_le_sum fun a' _ => hcorr a a'
      _ = Bcount * (r * n j + (1-r) * (((bucket j).filter (close a)).card : ℚ)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← sum_filter, sum_const, sum_const]
        simp only [nsmul_eq_mul, mul_one, n]
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (add_le_add (show r * n j ≤ r * n j from le_rfl)
          (mul_le_mul_of_nonneg_left (hnear j a) (sub_nonneg.mpr hr1))) hB.le
  have henergy (j : M) : (∑ b : B, V j b ^ 2) ≤
      n j * (Bcount * (r * n j + (1-r)*D)) := by
    calc
      _ = ∑ b : B, ∑ a ∈ bucket j, ∑ a' ∈ bucket j, bitSign (truth a b) * bitSign (truth a' b) := by
        simp only [V, pow_two, sum_mul, mul_sum]
        apply sum_congr rfl
        intro b hb
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro a' ha'
        exact mul_comm _ _
      _ = ∑ a ∈ bucket j, ∑ a' ∈ bucket j, ∑ b : B, bitSign (truth a b) * bitSign (truth a' b) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [sum_comm]
      _ ≤ ∑ _a ∈ bucket j, Bcount * (r * n j + (1-r)*D) := sum_le_sum fun a _ => hinner j a
      _ = _ := by simp [n, nsmul_eq_mul]
  have hS (j : M) : S j ^ 2 ≤ n j * W j := by
    have h := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (fun b => bitSign (read j b)) (V j)
    simp only [sign_sq, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    calc
      _ ≤ Bcount * (∑ b : B, V j b ^ 2) := h
      _ ≤ Bcount * (n j * (Bcount * (r * n j + (1-r)*D))) :=
        mul_le_mul_of_nonneg_left (henergy j) hB.le
      _ = _ := by dsimp only [W]; ring
  have hn : (∑ j : M, n j) = Acount := by
    have h := card_eq_sum_card_fiberwise (f := send) (s := (univ : Finset A)) (t := (univ : Finset M))
      (by intro a ha; exact mem_univ _)
    simp only [card_univ] at h
    dsimp only [n, Acount, bucket]
    exact_mod_cast h.symm
  have hW : (∑ j : M, W j) = Bcount^2 * (r * Acount + (Fintype.card M : ℚ) * ((1-r)*D)) := by
    dsimp only [W]
    rw [← mul_sum, sum_add_distrib, ← mul_sum, hn, sum_const, card_univ, nsmul_eq_mul]
  have hCS : (∑ j : M, S j)^2 ≤
      Acount * (Bcount^2 * (r * Acount + (Fintype.card M : ℚ) * ((1-r)*D))) := by
    calc
      _ ≤ (∑ j : M, n j) * (∑ j : M, W j) :=
        sum_sq_le_sum_mul_sum_of_sq_le_mul univ (f := n) (g := W)
          (by intro j hj; dsimp [n]; positivity)
          (by intro j hj; dsimp only [W, n]; positivity)
          (fun j _ => hS j)
      _ = _ := by rw [hn, hW]
  have hSsum : (∑ j : M, S j) =
      Acount * Bcount * (2 * agreement truth (fun a b => read (send a) b) - 1) := by
    rw [← score_bias truth (fun a b => read (send a) b)]
    dsimp only [S, V]
    rw [sum_comm, sum_comm (s := (univ : Finset A))]
    apply sum_congr rfl
    intro b hb
    simp_rw [mul_sum]
    rw [← sum_fiberwise_of_maps_to (g := send) (s := (univ : Finset A)) (t := (univ : Finset M))
      (by intro a ha; exact mem_univ _) (fun a => bitSign (read (send a) b) * bitSign (truth a b))]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro a ha
    rw [(mem_filter.mp ha).2]
  rw [hSsum, mul_pow] at hCS
  apply (mul_le_mul_iff_of_pos_left (show 0 < (Acount*Bcount)^2 by positivity)).mp
  calc
    _ ≤ _ := hCS
    _ = _ := by field_simp; ring

private lemma card_filter_fst {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) [DecidablePred p] :
    ((univ : Finset (A × B)).filter (fun z => p z.1)).card =
      (univ.filter p).card * Fintype.card B := by
  have heq : (univ : Finset (A × B)).filter (fun z => p z.1) = (univ.filter p).product univ := by
    ext z
    simp
  rw [heq]
  change ((univ.filter p) ×ˢ (univ : Finset B)).card = _
  rw [card_product, card_univ]

private lemma card_pairs {A B : Type} [Fintype A] [Fintype B]
    (p : A → B → Prop) [∀ a, DecidablePred (p a)] :
    ((univ : Finset (A × B)).filter (fun z => p z.1 z.2)).card =
      ∑ a : A, (univ.filter (p a)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact Fintype.sum_prod_type (fun z : A × B => if p z.1 z.2 then (1 : ℕ) else 0)

private abbrev Input (m : ℕ) (R : Type) := (Fin m → Block) × R

private lemma model_lower {m : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (φ ψ : (Fin m → Block) → Bool) (c h : ℕ)
    (send : Input m R → Fin (2^c)) (read : Fin (2^c) → Input m R → Bool) :
    let ball := ∑ j ∈ range (h+1), m.choose j * 7^j
    let rate := agreement (fun x y => modelTruth φ ψ x.1 y.1) (fun x y => read (send x) y)
    (2 : ℚ)^(h+1) * 8^m * (2*rate-1)^2 ≤ 8^m + ((2 : ℚ)^(h+1)-1) * 2^c * (ball : ℚ) := by
  intro ball rate
  let close := fun (x y : Input m R) => distance x.1 y.1 ≤ h
  let N : ℚ := Fintype.card R
  let r : ℚ := (1/2)^(h+1)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcount : (Fintype.card (Input m R) : ℚ) = 8^m * N := by
    simp only [Input, Fintype.card_prod, card_code, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, N]
  have hnear (x : Input m R) : ((univ.filter (close x)).card : ℚ) ≤ (ball : ℚ) * N := by
    rw [card_filter_fst (fun y => distance x.1 y ≤ h), card_near, Nat.cast_mul]
  have hc (x x' : Input m R) :
      (∑ y : Input m R, bitSign (modelTruth φ ψ x.1 y.1) * bitSign (modelTruth φ ψ x'.1 y.1)) ≤
        (Fintype.card (Input m R) : ℚ) * (r + (1-r) * (if close x x' then 1 else 0)) := by
    rw [Fintype.sum_prod_type, hcount]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    rw [correlation]
    let d := distance x.1 x'.1
    have hf : bitSign (φ x.1) * bitSign (φ x'.1) ≤ 1 := by
      cases φ x.1 <;> cases φ x'.1 <;> norm_num [bitSign]
    have hd : (1/2 : ℚ)^d ≤ r + (1-r) * (if close x x' then 1 else 0) := by
      by_cases he : close x x'
      · rw [ite_eq_left he, mul_one, add_sub_cancel]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      · rw [ite_eq_right he, mul_zero, add_zero]
        have hh : h + 1 ≤ d := by simpa [close, d] using Nat.succ_le_iff.mpr (Nat.lt_of_not_ge he)
        calc
          _ = (1/2 : ℚ)^(h+1) * (1/2 : ℚ)^(d-(h+1)) := by rw [← pow_add, Nat.add_sub_of_le hh]
          _ ≤ (1/2 : ℚ)^(h+1) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr0
          _ = _ := by simp [r]
    change N * (bitSign (φ x.1) * bitSign (φ x'.1) * 8^m * (1/2)^d) ≤ _
    calc
      _ = (8^m * N) * ((bitSign (φ x.1) * bitSign (φ x'.1)) * (1/2)^d) := by ring
      _ ≤ (8^m * N) * ((1/2)^d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using mul_le_mul_of_nonneg_right hf (show (0 : ℚ) ≤ (1/2)^d by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  have hb := bound_bias (fun x y => modelTruth φ ψ x.1 y.1) send read close r
    ((ball : ℚ)*N) hr0 hr1 (by positivity) hnear hc
  rw [hcount, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hb
  have hcancel : (2^c * ((ball : ℚ)*N) / (8^m * N)) = 2^c * (ball : ℚ) / 8^m := by
    field_simp
  rw [hcancel] at hb
  let H : ℚ := 2^(h+1)
  have hH : H*r = 1 := by dsimp [H, r]; rw [← mul_pow]; norm_num
  have hH' : H*(1-r) = H-1 := by linarith [hH]
  change H * 8^m * (2*rate-1)^2 ≤ 8^m + (H-1) * 2^c * (ball : ℚ)
  calc
    _ ≤ H * 8^m * (r + (1-r) * (2^c * (ball : ℚ) / 8^m)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 8^m * (H*r) + (H*(1-r)) * (2^c * (ball : ℚ)) := by field_simp
    _ = _ := by rw [hH, hH', mul_one, mul_assoc]

private lemma agreement_perfect {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (truth : A → B → Bool) : agreement truth truth = 1 := by
  have hA : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  simp [agreement, hA.ne', hB.ne', Nat.cast_mul]

private lemma model_high {m : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (φ ψ : (Fin m → Block) → Bool) (c : ℕ) :
    (∃ (send : Input m R → Fin (2^c)) (read : Fin (2^c) → Input m R → Bool),
      (15 : ℚ)/16 ≤ agreement (fun x y => modelTruth φ ψ x.1 y.1) (fun x y => read (send x) y)) ↔ 3*m ≤ c := by
  constructor
  · rintro ⟨send, read, hrate⟩
    by_contra hc
    have hexp : c + 1 ≤ 3*m := by omega
    have hp : (2 : ℚ)^(c+1) ≤ 8^m := by
      rw [show (8 : ℚ) = 2^3 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) hexp
    let rate := agreement (fun x y => modelTruth φ ψ x.1 y.1) (fun x y => read (send x) y)
    have hr : (7/8 : ℚ) ≤ 2*rate-1 := by change (15:ℚ)/16 ≤ rate at hrate; linarith
    have hsq : (49/64 : ℚ) ≤ (2*rate-1)^2 := by nlinarith
    have hl := model_lower φ ψ c 0 send read
    norm_num [Finset.sum_range_succ] at hl
    change 2 * 8^m * (2*rate-1)^2 ≤ 8^m + 2^c at hl
    rw [pow_succ] at hp
    have hpos : (0 : ℚ) < 8^m := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsq (show (0 : ℚ) ≤ 2*8^m by positivity)
    linarith
  · intro hc
    have hsz : Fintype.card (Fin m → Block) = 2^(3*m) := by rw [card_code, show (8 : ℕ) = 2^3 by decide, pow_mul]
    let emb := (Fintype.equivFinOfCardEq hsz).toEmbedding.trans
      (Fin.castLEEmb (Nat.pow_le_pow_right (by decide) hc))
    let decode := Function.invFun emb
    have hdec := Function.leftInverse_invFun emb.injective
    refine ⟨(fun x => emb x.1), (fun msg y => modelTruth φ ψ (decode msg) y.1), ?_⟩
    have hs : (fun (x y : Input m R) => modelTruth φ ψ (decode (emb x.1)) y.1) =
        fun x y => modelTruth φ ψ x.1 y.1 := by
      funext x y
      exact congrArg (fun a => modelTruth φ ψ a y.1) (hdec x.1)
    rw [hs, agreement_perfect]
    norm_num

private abbrev Front := Bool × Bool

private def frontBits (x : Block) : Front := (x.1, x.2.1)

private def candidates {m : ℕ} (x : Fin m → Block) (first : Fin m → Front) : Finset (Fin m) :=
  univ.filter (fun i => frontBits (x i) = first i)

private lemma front_card : ∀ x : Block,
    (univ.filter (fun y => frontBits x = frontBits y)).card = 2 ∧
    (univ.filter (fun y => frontBits x ≠ frontBits y)).card = 6 := by
  decide +kernel

private lemma front_eq_decide (x y : Block) : decide (x = y) =
    if frontBits x = frontBits y then xor (!x.2.2) y.2.2 else false := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private lemma parity_filter {I : Type} (s : Finset I) (p : I → Prop) [DecidablePred p] (f : I → Bool) :
    parityOn (s.filter p) f = parityOn s (fun i => if p i then f i else false) := by
  unfold parityOn
  rw [sum_filter]
  congr 2
  apply sum_congr rfl
  intro i hi
  by_cases hv : p i <;> simp [hv]

private lemma parity_candidates {m : ℕ} (x y : Fin m → Block) :
    parityOn univ (fun i => decide (x i = y i)) =
      xor (parityOn (candidates x (fun i => frontBits (y i))) (fun i => !(x i).2.2))
        (parityOn (candidates x (fun i => frontBits (y i))) (fun i => (y i).2.2)) := by
  rw [← parity_xor, candidates, parity_filter]
  congr 1
  funext i
  exact front_eq_decide (x i) (y i)

private lemma card_small (m t : ℕ) :
    ((univ : Finset (Finset (Fin m))).filter (fun s => s.card ≤ t)).card =
      ∑ j ∈ range (t+1), m.choose j := by
  have heq : (univ : Finset (Finset (Fin m))).filter (fun s => s.card ≤ t) =
      univ.filter (fun s => s.card ∈ range (t+1)) := by ext s; simp
  rw [heq, ← sum_card_fiberwise_eq_card_filter _ _ Finset.card]
  apply sum_congr rfl
  intro j hj
  have hs : ((univ : Finset (Finset (Fin m))).filter (fun s => s.card = j)) =
      (univ : Finset (Fin m)).powersetCard j := by ext s; simp [mem_powersetCard]
  rw [hs, card_powersetCard, card_univ, Fintype.card_fin]

private lemma card_overflow {m : ℕ} (t : ℕ) (x : Fin m → Block) :
    (univ.filter (fun (y : Fin m → Block) => t < (candidates x (fun i => frontBits (y i))).card)).card =
      2^m * (∑ j ∈ (range (m+1)).filter (fun j => t < j), m.choose j * 3^(m-j)) := by
  classical
  let p := fun i (b : Block) => frontBits (x i) = frontBits b
  let _ : ∀ i, DecidablePred (p i) := fun i b => inferInstanceAs (Decidable (frontBits (x i) = frontBits b))
  let J := (range (m+1)).filter (fun j => t < j)
  have heq : univ.filter (fun y => t < (candidates x (fun i => frontBits (y i))).card) =
      univ.filter (fun y => (support p y).card ∈ J) := by
    ext y
    have hsize : (support p y).card ≤ m := by
      unfold support
      exact (card_filter_le _ _).trans_eq (by simp)
    have he : candidates x (fun i => frontBits (y i)) = support p y := by ext i; simp [candidates, support, p]
    simp only [mem_filter, mem_univ, true_and, J, mem_range, Nat.lt_succ_iff, hsize, he]
  rw [heq, card_support p 2 6 (fun i => (front_card (x i)).1) (fun i => (front_card (x i)).2), mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hj).1)
  have hp : 2^m = 2^j * 2^(m-j) := by rw [← pow_add, Nat.add_sub_of_le hjm]
  rw [show (6 : ℕ) = 2*3 by decide, mul_pow, hp]
  ring

set_option maxHeartbeats 2000000 in
private lemma model_upper {m : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (φ ψ : (Fin m → Block) → Bool) (t alphabet : ℕ)
    (hsize : 2 * (∑ j ∈ range (t+1), m.choose j) ≤ alphabet) :
    let tail := ∑ j ∈ (range (m+1)).filter (fun j => t < j), m.choose j * 3^(m-j)
    ∃ (first : Input m R → Fin (2^(2*m)))
      (reply : Fin (2^(2*m)) → Input m R → Fin alphabet) (read : Fin alphabet → Input m R → Bool),
      1 - agreement (fun x y => modelTruth φ ψ x.1 y.1)
        (fun x y => read (reply (first y) x) y) ≤ (tail : ℚ) / (2 * 4^m) := by
  classical
  intro tail
  let Side := Input m R
  let Short := {s : Finset (Fin m) // s.card ≤ t}
  let Reply := Short × Bool
  let empty : Short := ⟨∅, by simp⟩
  let truth : Side → Side → Bool := fun x y => modelTruth φ ψ x.1 y.1
  let first := fun (y : Side) (i : Fin m) => frontBits (y.1 i)
  let reply : Bool → (Fin m → Front) → Side → Reply := fun fallback msg x =>
    let s := candidates x.1 msg
    if h : s.card ≤ t then
      (⟨s, h⟩, xor (φ x.1) (parityOn s (fun i => !(x.1 i).2.2)))
    else (empty, fallback)
  let read := fun (msg : Reply) (y : Side) =>
    xor (xor msg.2 (ψ y.1)) (parityOn msg.1.val (fun i => (y.1 i).2.2))
  let guess := fun b (x y : Side) => read (reply b (first y) x) y
  let errors := fun b => (univ : Finset (Side × Side)).filter (fun z => guess b z.1 z.2 ≠ truth z.1 z.2)
  let overflow := (univ : Finset (Side × Side)).filter (fun z => t < (candidates z.1.1 (first z.2)).card)
  have hgood (b : Bool) (x y : Side) (h : (candidates x.1 (first y)).card ≤ t) : guess b x y = truth x y := by
    dsimp only [guess, read, reply]
    rw [dite_eq_left h]
    dsimp only [truth, modelTruth, first]
    rw [parity_candidates]
    simp only [Bool.xor_assoc, Bool.xor_left_comm]
  have hbad (x y : Side) (h : ¬ (candidates x.1 (first y)).card ≤ t) :
      guess false x y ≠ guess true x y := by
    dsimp only [guess, read, reply]
    rw [dite_eq_right h, dite_eq_right h]
    simp [empty, parityOn]
  have hsub (b : Bool) : errors b ⊆ overflow := by
    intro z hz
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    apply Nat.lt_of_not_ge
    intro hg
    exact (mem_filter.mp hz).2 (hgood b z.1 z.2 hg)
  have hdis : Disjoint (errors false) (errors true) := by
    apply disjoint_left.mpr
    intro z h0 h1
    have h := (mem_filter.mp (hsub false h0)).2
    have hflip := hbad z.1 z.2 (Nat.not_le_of_gt h)
    have hf := (mem_filter.mp h0).2
    have ht := (mem_filter.mp h1).2
    generalize guess false z.1 z.2 = a at hf hflip
    generalize guess true z.1 z.2 = b at ht hflip
    generalize truth z.1 z.2 = c at hf ht
    cases a <;> cases b <;> cases c <;> simp_all
  have hboth : (errors false).card + (errors true).card ≤ overflow.card := by
    rw [← card_union_of_disjoint hdis]
    exact card_le_card (union_subset (hsub false) (hsub true))
  have hboth' : ((errors false).card : ℚ) + (errors true).card ≤ overflow.card := by exact_mod_cast hboth
  obtain ⟨chosen, hchosen⟩ : ∃ b : Bool, ((errors b).card : ℚ) ≤ (overflow.card : ℚ)/2 := by
    by_cases h : ((errors false).card : ℚ) ≤ (overflow.card : ℚ)/2
    · exact ⟨false, h⟩
    · exact ⟨true, by linarith⟩
  have hover : overflow.card = Fintype.card Side * (2^m * tail * Fintype.card R) := by
    have hsplit := card_pairs (fun x y : Side => t < (candidates x.1 (first y)).card)
    have hfilter : overflow = univ.filter
        (fun z : Side × Side => t < (candidates z.1.1 (first z.2)).card) := by
      ext z
      simp [overflow]
    rw [hfilter]
    refine hsplit.trans ?_
    have hf (x : Side) :
        (univ.filter (fun y : Side => t < (candidates x.1 (first y)).card)).card =
          2^m * tail * Fintype.card R := by
      rw [card_filter_fst (B := R)
        (fun y : Fin m → Block => t < (candidates x.1 (fun i => frontBits (y i))).card),
        card_overflow]
    simp_rw [hf, sum_const, card_univ, Nat.nsmul_eq_mul]
  have hcard : Fintype.card Side = 8^m * Fintype.card R := by rw [Fintype.card_prod, card_code]
  have hRate : 1 - agreement truth (guess chosen) ≤ (tail : ℚ) / (2 * 4^m) := by
    rw [error_count]
    change ((errors chosen).card : ℚ) / ((Fintype.card Side : ℚ) * Fintype.card Side) ≤ _
    have hN : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
    have hS : (0 : ℚ) < Fintype.card Side := by exact_mod_cast Fintype.card_pos
    calc
      _ ≤ ((overflow.card : ℚ)/2) / ((Fintype.card Side : ℚ) * Fintype.card Side) := by gcongr
      _ = _ := by
        rw [hover]
        push_cast
        rw [hcard]
        push_cast
        rw [show (8 : ℚ) = 2*4 by norm_num, mul_pow]
        field_simp
  have hFirst : Fintype.card (Fin m → Front) = 2^(2*m) := by
    simp [Fintype.card_prod, pow_mul]
  have hReply : Fintype.card Reply = 2 * (∑ j ∈ range (t+1), m.choose j) := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype, card_small, mul_comm]
  let encodeFirst := Fintype.equivFinOfCardEq hFirst
  let encodeReply := (Fintype.equivFinOfCardEq hReply).toEmbedding.trans (Fin.castLEEmb hsize)
  let _ : Nonempty Reply := ⟨(empty, false)⟩
  let decodeReply := Function.invFun encodeReply
  have hdec := Function.leftInverse_invFun encodeReply.injective
  refine ⟨(fun y => encodeFirst (first y)),
    (fun msg x => encodeReply (reply chosen (encodeFirst.symm msg) x)),
    (fun msg y => read (decodeReply msg) y), ?_⟩
  have hf : (fun (x y : Side) =>
      read (decodeReply (encodeReply (reply chosen (encodeFirst.symm (encodeFirst (first y))) x))) y) =
      guess chosen := by
    funext x y
    rw [Equiv.symm_apply_apply]
    exact congrArg (fun v => read v y) (hdec _)
  rw [hf]
  exact hRate

private lemma small_bound (m : ℕ) :
    (∑ j ∈ range (m / 3 + 1), m.choose j) ≤ 2 ^ ((14 * m + 14) / 15) := by
  let t := m / 3
  let e := (14 * m + 14) / 15
  let S := ∑ j ∈ range (t + 1), m.choose j
  change S ≤ 2 ^ e
  have htm : t ≤ m := by dsimp [t]; omega
  have hsum : (S : ℚ) ≤ 2 ^ t * (3 / 2) ^ m := by
    have hexpand : (3 / 2 : ℚ) ^ m =
        ∑ j ∈ range (m + 1), (1 / 2 : ℚ) ^ j * (m.choose j : ℚ) := by
      have h := add_pow (1 / 2 : ℚ) 1 m
      norm_num at h ⊢
      exact h
    calc
      (S : ℚ) = ∑ j ∈ range (t + 1), (m.choose j : ℚ) := by simp [S]
      _ ≤ ∑ j ∈ range (t + 1), 2 ^ t * ((1 / 2 : ℚ) ^ j * (m.choose j : ℚ)) := by
        apply sum_le_sum
        intro j hj
        have hjt : j ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have hp : (2 : ℚ) ^ j ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) hjt
        have hi : 1 ≤ (2 : ℚ) ^ t * (1 / 2) ^ j := by
          rw [show (1 / 2 : ℚ) = 2⁻¹ by norm_num, inv_pow, ← div_eq_mul_inv]
          exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
        rw [← mul_assoc]
        simpa using mul_le_mul_of_nonneg_right hi (show (0 : ℚ) ≤ m.choose j by positivity)
      _ ≤ ∑ j ∈ range (m + 1), 2 ^ t * ((1 / 2 : ℚ) ^ j * (m.choose j : ℚ)) :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; positivity)
      _ = _ := by rw [← mul_sum, ← hexpand]
  have hpower : (2 ^ t * (3 / 2 : ℚ) ^ m) ^ 15 ≤ (2 ^ e : ℚ) ^ 15 := by
    have hbase : (3 / 2 : ℚ) ^ 15 ≤ 2 ^ 9 := by norm_num
    have hle : 15 * t + 9 * m ≤ 15 * e := by dsimp [t, e]; omega
    calc
      (2 ^ t * (3 / 2 : ℚ) ^ m) ^ 15 = (2 : ℚ) ^ (15 * t) * ((3 / 2 : ℚ) ^ 15) ^ m := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm t, Nat.mul_comm m]
      _ ≤ (2 : ℚ) ^ (15 * t) * ((2 : ℚ) ^ 9) ^ m := by gcongr
      _ ≤ (2 ^ e : ℚ) ^ 15 := by
        rw [← pow_mul, ← pow_add, ← pow_mul, Nat.mul_comm e]
        exact pow_le_pow_right₀ (by norm_num) hle
  have hfinal := hsum.trans ((pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by decide : 15 ≠ 0)).mp hpower)
  exact_mod_cast hfinal

private lemma tail_bound (m : ℕ) (hm : 216 ≤ m) :
    (∑ j ∈ (range (m + 1)).filter (fun j => m / 3 < j),
      m.choose j * 3 ^ (m - j) : ℕ) ≤ (4 : ℚ) ^ m / 8 := by
  let u := m / 3 + 1
  let T := (range (m + 1)).filter (fun j => m / 3 < j)
  let weight := fun j => (m.choose j : ℚ) * 3 ^ (m - j)
  have hu : 72 ≤ u := by dsimp [u]; omega
  have hmu : m ≤ 3 * u := by dsimp [u]; omega
  push_cast
  change ∑ j ∈ T, weight j ≤ 4 ^ m / 8
  have hscaled : (3 / 2 : ℚ) ^ u * (∑ j ∈ T, weight j) ≤ (9 / 2 : ℚ) ^ m := by
    rw [mul_sum]
    calc
      _ ≤ ∑ j ∈ T, (3 / 2 : ℚ) ^ j * weight j := by
        apply sum_le_sum
        intro j hj
        have hj' : u ≤ j := (mem_filter.mp hj).2
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj') (by dsimp [weight]; positivity)
      _ ≤ ∑ j ∈ range (m + 1), (3 / 2 : ℚ) ^ j * weight j :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; dsimp [weight]; positivity)
      _ = _ := by
        rw [show (9 / 2 : ℚ) = 3 / 2 + 3 by norm_num, add_pow]
        apply sum_congr rfl
        intro j hj
        dsimp [weight]
        ring
  have hratio : (9 / 8 : ℚ) ^ m ≤ (3 / 2 : ℚ) ^ u / 8 := by
    have hgeom : (243 / 256 : ℚ) ^ u ≤ 1 / 8 :=
      calc
        _ = (243 / 256 : ℚ) ^ 72 * (243 / 256 : ℚ) ^ (u - 72) := by
          rw [← pow_add, Nat.add_sub_of_le hu]
        _ ≤ (243 / 256 : ℚ) ^ 72 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
        _ ≤ 1 / 8 := by norm_num
    calc
      _ ≤ (9 / 8 : ℚ) ^ (3 * u) := pow_le_pow_right₀ (by norm_num) hmu
      _ = (3 / 2 : ℚ) ^ u * (243 / 256 : ℚ) ^ u := by
        rw [pow_mul, ← mul_pow]
        norm_num
      _ ≤ (3 / 2 : ℚ) ^ u * (1 / 8) := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by ring
  have h9 : (9 / 2 : ℚ) ^ m ≤ (3 / 2 : ℚ) ^ u * (4 ^ m / 8) := by
    calc
      _ = (4 : ℚ) ^ m * (9 / 8 : ℚ) ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (4 : ℚ) ^ m * ((3 / 2 : ℚ) ^ u / 8) := by gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_left (hscaled.trans h9) (by positivity)

private lemma agreement_transfer {K X Y : Type} [DecidableEq K] [Fintype X] [Fintype Y]
    (fiber : Finset K) (left : fiber ≃ X) (right : fiber ≃ Y)
    (truth : K → K → Bool) (model : X → Y → Bool)
    (htruth : ∀ x y : fiber, truth x.val y.val = model (left x) (right y))
    (guess : K → K → Bool) :
    (((fiber.product fiber).filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) /
      ((fiber.product fiber).card : ℚ) =
      agreement model (fun x y => guess (left.symm x).val (right.symm y).val) := by
  let pairs := fiber.product fiber
  let e₀ : pairs ≃ fiber × fiber :=
    (Equiv.subtypeEquivRight (fun z : K × K =>
      show z ∈ pairs ↔ z.1 ∈ fiber ∧ z.2 ∈ fiber from Finset.mem_product)).trans
      Equiv.subtypeProdEquivProd
  let e := e₀.trans (Equiv.prodCongr left right)
  let p := fun z : K × K => guess z.1 z.2 = truth z.1 z.2
  let q := fun z : X × Y => guess (left.symm z.1).val (right.symm z.2).val = model z.1 z.2
  have hp (z : pairs) : p z.val ↔ q (e z) := by
    let a : fiber := (e₀ z).1
    let b : fiber := (e₀ z).2
    change guess a.val b.val = truth a.val b.val ↔
      guess (left.symm (left a)).val (right.symm (right b)).val = model (left a) (right b)
    rw [left.symm_apply_apply, right.symm_apply_apply, htruth a b]
  have hcard := Fintype.card_congr (e.subtypeEquiv hp)
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  change (pairs.attach.filter (fun z => p z.val)).card = (univ.filter q).card at hcard
  have hattach : pairs.attach.filter (fun z => p z.val) = _ := filter_attach p pairs
  rw [hattach, card_map, card_attach] at hcard
  have hall := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_prod] at hall
  change (((pairs.filter p).card : ℚ) / (pairs.card : ℚ)) =
    ((univ.filter q).card : ℚ) / ((Fintype.card X : ℚ) * (Fintype.card Y : ℚ))
  rw [hcard, hall, Nat.cast_mul]

private lemma xor_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  rw [xor_left_eq, Bool.xor_false]

private def shiftBlock {m : ℕ} (s : Fin m → Block) : (Fin m → Block) ≃ (Fin m → Block) where
  toFun x i := bxor (x i) (s i)
  invFun x i := bxor (x i) (s i)
  left_inv x := funext fun i => bxor_cancel_right (x i) (s i)
  right_inv x := funext fun i => bxor_cancel_right (x i) (s i)

end PEqualNP.Outside.L_meta_29752

open Finset PEqualNP.Outside.L_meta_29752

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_29752 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let lower := ∀ c : Nat,
    let M := Fin (2^c)
    let rate := fun (send : K → M) (read : M → K → Bool) =>
      agree (fun left right => read (send left) right)
    (∀ h : Nat, h ≤ m → ∀ (send : K → M) (read : M → K → Bool),
      let ball := ∑ j ∈ Finset.range (h+1), Nat.choose m j * 7^j
      (2 : ℚ)^(h+1) * 8^m * (2 * rate send read - 1)^2 ≤
        8^m + ((2 : ℚ)^(h+1)-1) * 2^c * (ball : ℚ)) ∧
    (Iff (∃ send read, (15 : ℚ)/16 ≤ rate send read) (3*m ≤ c))
  let twoMessages := fun (alphabet : Nat) (maxError : ℚ) =>
    let First := Fin (2^(2*m))
    let Reply := Fin alphabet
    ∃ (first : K → First) (reply : First → K → Reply) (read : Reply → K → Bool),
      1 - agree (fun left right => read (reply (first right) left) right) ≤ maxError
  let upper := ∀ t : Nat, t ≤ m →
    let small := ∑ j ∈ Finset.range (t+1), Nat.choose m j
    let tail := ∑ j ∈ (Finset.range (m+1)).filter (fun j => t < j), Nat.choose m j * 3^(m-j)
    twoMessages (2*small) ((tail : ℚ) / (2*4^m))
  And lower (And upper (216 ≤ m → twoMessages (2^(1+(14*m+14)/15)) ((1 : ℚ)/16)))) := by
  classical
  intro k hk0 constant rot step state injected bit m starts hm hinj good row ref hgood pin hpin hfree K fiber
    pairs truth agree lower twoMessages upper
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
  have hAgree (guess : K → K → Bool) :
      agree guess = agreement model (fun x y => guess (left.symm x).val (right.symm y).val) :=
    agreement_transfer fiber left right truth model hTruth guess
  let leftInput := fun q : K => if h : q ∈ fiber then left ⟨q, h⟩ else
    ((fun _ => (false, false, false)), fun _ => false)
  let rightInput := fun q : K => if h : q ∈ fiber then right ⟨q, h⟩ else
    ((fun _ => (false, false, false)), fun _ => false)
  have hLI (x : Side) : leftInput (left.symm x).val = x := by
    dsimp only [leftInput]
    rw [dite_eq_left (left.symm x).property]
    exact left.apply_symm_apply x
  have hRI (y : Side) : rightInput (right.symm y).val = y := by
    dsimp only [rightInput]
    rw [dite_eq_left (right.symm y).property]
    exact right.apply_symm_apply y
  have hTwo (t alphabet : ℕ) (hcap : 2 * (∑ j ∈ range (t+1), m.choose j) ≤ alphabet) :
      twoMessages alphabet
        (((∑ j ∈ (range (m+1)).filter (fun j => t < j), m.choose j * 3^(m-j)) : ℕ) / (2 * 4^m)) := by
    obtain ⟨f, reply, read, hr⟩ := model_upper (R := Extra) φ ψ t alphabet hcap
    refine ⟨(fun y => f (rightInput y)), (fun msg x => reply msg (leftInput x)),
      (fun msg y => read msg (rightInput y)), ?_⟩
    rw [hAgree (fun x y => read (reply (f (rightInput y)) (leftInput x)) (rightInput y))]
    simp_rw [hLI, hRI]
    exact hr
  refine ⟨?_, ?_, ?_⟩
  · intro c M rate
    constructor
    · intro h hh send read ball
      change (2 : ℚ)^(h+1) * 8^m * (2 * agree (fun x y => read (send x) y) - 1)^2 ≤ _
      rw [hAgree (fun x y => read (send x) y)]
      exact model_lower (R := Extra) φ ψ c h (fun x => send (left.symm x).val)
        (fun msg y => read msg (right.symm y).val)
    · constructor
      · rintro ⟨send, read, hrate⟩
        change (15 : ℚ)/16 ≤ agree (fun x y => read (send x) y) at hrate
        rw [hAgree (fun x y => read (send x) y)] at hrate
        apply (model_high (R := Extra) φ ψ c).mp
        exact ⟨(fun x => send (left.symm x).val), (fun msg y => read msg (right.symm y).val), hrate⟩
      · intro hc
        obtain ⟨send, read, hs⟩ := (model_high (R := Extra) φ ψ c).mpr hc
        refine ⟨(fun x => send (leftInput x)), (fun msg y => read msg (rightInput y)), ?_⟩
        change (15 : ℚ)/16 ≤ agree (fun x y => read (send (leftInput x)) (rightInput y))
        rw [hAgree (fun x y => read (send (leftInput x)) (rightInput y))]
        simp_rw [hLI, hRI]
        exact hs
  · intro t ht small tail
    exact hTwo t (2*small) le_rfl
  · intro hm216
    let t := m / 3
    let e := (14*m+14)/15
    have hcap : 2 * (∑ j ∈ range (t+1), m.choose j) ≤ 2^(1+e) := by
      rw [pow_add, pow_one]
      exact Nat.mul_le_mul_left _ (small_bound m)
    obtain ⟨f, reply, read, hs⟩ := hTwo t (2^(1+e)) hcap
    refine ⟨f, reply, read, hs.trans ?_⟩
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := tail_bound m hm216
    convert hh using 1
    ring
