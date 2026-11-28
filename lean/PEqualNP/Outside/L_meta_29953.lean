import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620

namespace PEqualNP.Outside.L_meta_29953_aux

namespace Guard29953

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

def Abstract : Prop := ∀ (m : ℕ) (φ ψ : (Fin m → Fin 8) → Bool),
  let X := Fin m → Fin 8
  let groups := m/32
  ∃ (seeds replyBits : Nat)
    (first : Fin seeds → X → Fin (2^(2*groups)))
    (reply : Fin seeds → Fin (2^(2*groups)) → X → Fin (2^replyBits))
    (decode : Fin seeds → X → Fin (2^replyBits) → Bool),
    0 < seeds ∧ 2*groups + replyBits ≤ 3*m - m/1280 + 2 ∧
    ∀ x y : X,
      let truth := xor (xor (φ x) (ψ y)) (((∑ i : Fin m, (decide (x i = y i)).toNat) % 2) == 1)
      let wrong := (Finset.univ : Finset (Fin seeds)).filter (fun z =>
        decode z y (reply z (first z y) x) ≠ truth)
      (wrong.card : ℚ) ≤ (seeds : ℚ)*((2047 : ℚ)/2048)^groups

def EqualityOnly : Prop := ∀ (m : ℕ),
  let X := Fin m → Fin 8
  let groups := m/32
  ∃ (seeds replyBits : Nat)
    (first : Fin seeds → X → Fin (2^(2*groups)))
    (reply : Fin seeds → Fin (2^(2*groups)) → X → Fin (2^replyBits))
    (decode : Fin seeds → X → Fin (2^replyBits) → Bool),
    0 < seeds ∧ 2*groups + replyBits ≤ 3*m - m/1280 + 1 ∧
    ∀ x y : X,
      let truth := (((∑ i : Fin m, (decide (x i = y i)).toNat) % 2) == 1)
      let wrong := (Finset.univ : Finset (Fin seeds)).filter (fun z =>
        decode z y (reply z (first z y) x) ≠ truth)
      (wrong.card : ℚ) ≤ (seeds : ℚ)*((2047 : ℚ)/2048)^groups

theorem withPhases (protocol : EqualityOnly) : Abstract := by
  classical
  intro m φ ψ X groups
  obtain ⟨seeds, n, f, r, dec, hpos, hsize, hp⟩ := protocol m
  let e : (Fin (2^n) × Bool) ≃ Fin (2^(n+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ])
  let reply (z : Fin seeds) (msg : Fin (2^(2*groups))) (x : X) := e (r z msg x, φ x)
  let decode (z : Fin seeds) (y : X) (msg : Fin (2^(n+1))) :=
    xor (xor (e.symm msg).2 (ψ y)) (dec z y (e.symm msg).1)
  refine ⟨seeds, n+1, f, reply, decode, hpos, ?_, ?_⟩
  · dsimp only [groups]; omega
  · intro x y
    dsimp only [reply, decode]
    simpa only [Equiv.symm_apply_apply, ne_eq, Bool.xor_right_inj] using (hp x y)

set_option maxHeartbeats 2000000 in
theorem bridge (protocol : Abstract) : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  let groups := m/32
  ∃ (seeds replyBits : Nat)
    (first : Fin seeds → K → Fin (2^(2*groups)))
    (reply : Fin seeds → Fin (2^(2*groups)) → K → Fin (2^replyBits))
    (decode : Fin seeds → K → Fin (2^replyBits) → Bool),
    0 < seeds ∧ 2*groups + replyBits ≤ 3*m - m/1280 + 2 ∧
    ∀ pair ∈ pairs,
      let wrong := (Finset.univ : Finset (Fin seeds)).filter (fun z =>
        decode z pair.2 (reply z (first z pair.2) pair.1) ≠ truth pair.1 pair.2)
      (wrong.card : ℚ) ≤ (seeds : ℚ)*((2047 : ℚ)/2048)^groups := by
  classical
  intro k hk0 constant rot step state injected bit m starts hm hinj good row ref hgood pin hpin _ K fiber pairs truth groups
  let windows : Fin m × Fin 12 → Fin k := fun ij =>
    ⟨(starts ij.1 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  have hwin : Function.Injective windows := by
    intro a b h
    exact hinj (congrArg Fin.val h)
  have hk : 12 ≤ k := by
    have hc := Fintype.card_le_of_injective windows hwin
    simp [Fintype.card_prod] at hc
    omega
  let e : Block ≃ Fin 8 := Fintype.equivFinOfCardEq (by decide)
  let shifts := fun i => windowShift constant row ref (starts i)
  let leftB (q : K) (i : Fin m) := windowShare constant row ref q (starts i)
  let rightB (q : K) (i : Fin m) := bxor (windowShare constant row ref q (starts i)) (shifts i)
  let left (q : K) (i : Fin m) := e (leftB q i)
  let right (q : K) (i : Fin m) := e (rightB q i)
  let flag := fun i => windowFlag constant row ref (starts i)
  let base := fun i => xor (!affine (flag i) (point (flag i)))
    (injectedFn k constant 2 ref.val (starts i+5))
  let φ := fun x : Fin m → Fin 8 => xor (parityOn univ base)
    (parityOn univ (fun i => affine (flag i) (e.symm (x i))))
  let ψ := fun y : Fin m → Fin 8 => parityOn univ (fun i => affine (flag i) (e.symm (y i)))
  have hpinShare (q : K) (hq : q ∈ fiber) (i : Fin m) (j : ℕ) (hj : j < 9) :
      shareBit k constant row ref q (starts i+j) = false := by
    obtain ⟨z, hz, hzval⟩ := hpin i ⟨j, hj⟩
    have hs := (mem_filter.mp hq).2 z hz
    change bitFn k constant row.val 0 q.val z.val = bitFn k constant row.val 0 ref.val z.val at hs
    have hz' : shareBit k constant row ref q z.val = false := by simp [shareBit, hs]
    rw [hzval, shareBit_mod hk] at hz'
    exact hz'
  have hTruth (x y : K) (hx : x ∈ fiber) (hy : y ∈ fiber) :
      truth x y = xor (xor (φ (left x)) (ψ (right y)))
       (parityOn univ fun i => decide (left x i = right y i)) := by
    have hrow (i : Fin m) :
        bitFn k constant row.val 2 (combine ref x y).val (starts i+5) =
          xor (xor (xor (base i) (affine (flag i) (leftB x i)))
            (affine (flag i) (rightB y i))) (decide (leftB x i = rightB y i)) :=
      guarded_window hk constant row ref x y (starts i) (hpinShare x hx i) (hpinShare y hy i)
        (hgood i).1 (hgood i).2.2.1 (hgood i).2.2.2
    change parityOn univ (fun i => bitFn k constant row.val 2 (combine ref x y).val (starts i+5)) = _
    rw [funext hrow]
    simp only [parity_xor, φ, ψ, left, right, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨seeds, n, f, r, dec, hpos, hsize, hp⟩ := protocol m φ ψ
  refine ⟨seeds, n, (fun z y => f z (right y)), (fun z msg x => r z msg (left x)),
    (fun z y msg => dec z (right y) msg), hpos, hsize, ?_⟩
  intro pair hpair
  have h := Finset.mem_product.mp hpair
  dsimp only
  rw [hTruth pair.1 pair.2 h.1 h.2]
  exact hp (left pair.1) (right pair.2)

end Guard29953

namespace Comm29953

open scoped BigOperators

abbrev Block (t : ℕ) := Fin t × Fin 32 → Fin 8
abbrev Rand (t : ℕ) := Fin t → Fin 32 × Fin 7
abbrev Side (r : ℕ) := Fin r → Fin 8

def eq1 (x y : Fin 8) : ZMod 2 := if x = y then 1 else 0

def bucket (v : Fin 7) (x : Fin 8) : Fin 4 :=
  let d := v.val + 1
  let p := d.log2
  let a := min x.val (x.val ^^^ d)
  ⟨((a % 2^p) + (a / 2^(p+1)) * 2^p) % 4, Nat.mod_lt _ (by decide)⟩

def sign1 (v : Fin 7) (x : Fin 8) : ZMod 2 :=
  if x.val.testBit ((v.val+1).log2) then 1 else 0

theorem bucket_eq1 : ∀ v x y,
    (if bucket v x = bucket v y then (1 + sign1 v x : ZMod 2) else 0) +
    (if bucket v x = bucket v y then sign1 v y else 0) = eq1 x y := by decide

theorem bucket_card : ∀ x y : Fin 8,
    ((Finset.univ : Finset (Fin 7)).filter (fun v => bucket v x = bucket v y)).card =
      if x = y then 7 else 1 := by decide

variable {t r : ℕ}

def firstQ (z : Rand t) (y : Block t) (i : Fin t) : Fin 4 :=
  bucket (z i).2 (y (i,(z i).1))

def maskQ (z : Rand t) (q : Fin t → Fin 4) (x : Block t) : Finset (Fin t) :=
  Finset.univ.filter fun i => bucket (z i).2 (x (i,(z i).1)) = q i

def omitQ (z : Rand t) (x : Block t) (p : Fin t × Fin 31) : Fin 8 :=
  x (p.1, (z p.1).1.succAbove p.2)

def patchQ (z : Rand t) (M : Finset (Fin t)) (x : Block t) : ZMod 2 :=
  ∑ i : Fin t, if i ∈ M then 1 + sign1 (z i).2 (x (i,(z i).1)) else 0

def readQ (z : Rand t) (M : Finset (Fin t)) (o : Fin t × Fin 31 → Fin 8) (y : Block t) : ZMod 2 :=
  (∑ i : Fin t, if i ∈ M then sign1 (z i).2 (y (i,(z i).1)) else 0) +
    ∑ i : Fin t, ∑ j : Fin 31, eq1 (o (i,j)) (omitQ z y (i,j))

def blockVal (x y : Block t) : ZMod 2 := ∑ p : Fin t × Fin 32, eq1 (x p) (y p)

def sideVal (x y : Side r) : ZMod 2 := ∑ i, eq1 (x i) (y i)

theorem far_read (x y : Block t) (z : Rand t) :
    let M := maskQ z (firstQ z y) x
    patchQ z M x + readQ z M (omitQ z x) y = blockVal x y := by
  classical
  dsimp only
  unfold patchQ readQ blockVal
  rw [←add_assoc, ←Finset.sum_add_distrib, ←Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succAbove _ (z i).1]
  have hM : i ∈ maskQ z (firstQ z y) x ↔ bucket (z i).2 (x (i,(z i).1)) = bucket (z i).2 (y (i,(z i).1)) := by
    unfold maskQ
    rw [Finset.mem_filter]
    simp [firstQ]
  simp only [hM, bucket_eq1, omitQ]

abbrev Input (t r : ℕ) := Block t × Side r

def BlockAPI (t r : ℕ) : Prop := ∀ (a b : Input t r → ZMod 2),
  ∃ (S bits : ℕ)
    (first : Fin S → Input t r → Fin (2^(2*t)))
    (reply : Fin S → Fin (2^(2*t)) → Input t r → Fin (2^bits))
    (decode : Fin S → Input t r → Fin (2^bits) → ZMod 2),
    0 < S ∧ 2*t + bits ≤ 3*(32*t+r) - t/40 + 2 ∧ ∀ x y,
    ((Finset.univ.filter fun z => decode z y (reply z (first z y) x) ≠
      blockVal x.1 y.1 + sideVal x.2 y.2 + a x + b y).card : ℚ) ≤
        S * ((2047:ℚ)/2048)^t

abbrev Thin (t : ℕ) := {M : Finset (Fin t) // 5*M.card ≤ 2*t}
abbrev FarData (t : ℕ) := Thin t × (Fin t × Fin 31 → Fin 8)
abbrev hBits (t : ℕ) := 94*t - t/40
abbrev HashMsg (t : ℕ) := Fin (2 ^ hBits t)

def smallD (x y : Block t) : Prop :=
  (Finset.univ.filter (fun p => x p ≠ y p)).card ≤ 23*t

abbrev Answer (t r : ℕ) := (FarData t ⊕ HashMsg t) × Side r × ZMod 2

private theorem answer_bound (lim : Fintype.card (Thin t) ≤ 2^(t - t/40)) :
    Fintype.card (Answer t r) ≤ 2^(hBits t + 3*r + 2) := by
  have h0 : Fintype.card (FarData t) ≤ 2^(hBits t) := by
    simp only [FarData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    calc
      _ ≤ 2^(t - t/40) * 8^(t*31) := Nat.mul_le_mul_right _ lim
      _ = _ := by
        rw [show (8:ℕ) = 2^3 by decide, ←pow_mul, ←pow_add]
        congr 1
        dsimp [hBits]; omega
  change Fintype.card ((FarData t ⊕ HashMsg t) × Side r × ZMod 2) ≤ _
  simp only [Fintype.card_prod, Fintype.card_sum, HashMsg, Side, Fintype.card_fin, ZMod.card,
    Fintype.card_fun]
  calc
    _ ≤ (2^hBits t + 2^hBits t) * (8^r * 2) := by
      gcongr
      simpa only [FarData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using h0
    _ = _ := by rw [show (8:ℕ) = 2^3 by decide, ←pow_mul, pow_add, pow_add]; ring

private theorem mk_codec {A : Type*} [Fintype A] [Nonempty A] {n : ℕ}
    (h : Fintype.card A ≤ n) :
    ∃ (enc : A → Fin n) (dec : Fin n → A), Function.LeftInverse dec enc := by
  let enc := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb h)
  exact ⟨enc, Function.invFun enc, Function.leftInverse_invFun enc.injective⟩

variable {H : Type} [Fintype H] [Nonempty H]

private def ansQ (hash : H → Block t → HashMsg t) (a : Input t r → ZMod 2)
    (s : Rand t × H) (q : Fin t → Fin 4) (x : Input t r) : Answer t r :=
  let M := maskQ s.1 q x.1
  if h : 5*M.card ≤ 2*t then (Sum.inl (⟨M,h⟩, omitQ s.1 x.1), x.2, a x + patchQ s.1 M x.1)
  else (Sum.inr (hash s.2 x.1), x.2, a x)

private def decodeQ (read : H → Block t → HashMsg t → Block t) (b : Input t r → ZMod 2)
    (s : Rand t × H) (y : Input t r) (ans : Answer t r) : ZMod 2 :=
  (match ans.1 with
    | Sum.inl (⟨M,_⟩,o) => readQ s.1 M o y.1
    | Sum.inr h => blockVal (read s.2 y.1 h) y.1) + sideVal ans.2.1 y.2 + ans.2.2 + b y

private theorem decode_ok (hash : H → Block t → HashMsg t)
    (read : H → Block t → HashMsg t → Block t) (a b : Input t r → ZMod 2)
    (s : Rand t × H) (x y : Input t r)
    (h : 5*(maskQ s.1 (firstQ s.1 y.1) x.1).card ≤ 2*t ∨ read s.2 y.1 (hash s.2 x.1) = x.1) :
    decodeQ read b s y (ansQ hash a s (firstQ s.1 y.1) x) =
      blockVal x.1 y.1 + sideVal x.2 y.2 + a x + b y := by
  by_cases hM : 5*(maskQ s.1 (firstQ s.1 y.1) x.1).card ≤ 2*t
  · simp only [decodeQ, ansQ, dif_pos hM]
    rw [←far_read x.1 y.1 s.1]; abel
  · simp only [decodeQ, ansQ, dif_neg hM, h.resolve_left hM]

private theorem count_left {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B → Prop) [DecidablePred p] (u : A → Prop) [DecidablePred u]
    (inc : ∀ z, p z → u z.1) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter u).card * Fintype.card B := by
  classical
  rw [←Finset.card_univ (α := B), ←Finset.card_product]
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc z (Finset.mem_filter.mp hz).2⟩, Finset.mem_univ _⟩

private theorem count_right {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B → Prop) [DecidablePred p] (u : B → Prop) [DecidablePred u]
    (inc : ∀ z, p z → u z.2) :
    (Finset.univ.filter p).card ≤ Fintype.card A * (Finset.univ.filter u).card := by
  classical
  rw [←Finset.card_univ (α := A), ←Finset.card_product]
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc z (Finset.mem_filter.mp hz).2⟩⟩

theorem blockProtocol (lim : Fintype.card (Thin t) ≤ 2^(t - t/40))
    (hash : H → Block t → HashMsg t) (read : H → Block t → HashMsg t → Block t)
    (near : ∀ x y : Block t, smallD x y →
      ((Finset.univ.filter fun h => read h y (hash h x) ≠ x).card : ℚ) ≤
        Fintype.card H * ((2047:ℚ)/2048)^t)
    (far : ∀ x y : Block t, ¬smallD x y →
      ((Finset.univ.filter fun z : Rand t => 2*t < 5*(maskQ z (firstQ z y) x).card).card : ℚ) ≤
        Fintype.card (Rand t) * ((2047:ℚ)/2048)^t) : BlockAPI t r := by
  classical
  intro a b
  let e := Fintype.equivFin (Rand t × H)
  letI : Nonempty (Answer t r) := ⟨Sum.inr ⟨0, Nat.two_pow_pos _⟩, fun _ => 0, 0⟩
  obtain ⟨pack,unpack,hpack⟩ := mk_codec (answer_bound (r := r) lim)
  have cQ : Fintype.card (Fin t → Fin 4) = 2^(2*t) := by
    simp [show (4:ℕ) = 2^2 by decide, pow_mul]
  let f := Fintype.equivFinOfCardEq cQ
  refine ⟨_, hBits t + 3*r + 2, fun s y => f (firstQ (e.symm s).1 y.1),
    fun s q x => pack (ansQ hash a (e.symm s) (f.symm q) x),
    fun s y ans => decodeQ read b (e.symm s) y (unpack ans), Fintype.card_pos, ?_, ?_⟩
  · dsimp [hBits]; omega
  · intro x y
    let wrong := fun s : Rand t × H =>
      decodeQ read b s y (ansQ hash a s (firstQ s.1 y.1) x) ≠
        blockVal x.1 y.1 + sideVal x.2 y.2 + a x + b y
    have hcard : (Finset.univ.filter (fun s : Fin (Fintype.card (Rand t × H)) =>
      decodeQ read b (e.symm s) y (unpack (pack (ansQ hash a (e.symm s)
        (f.symm (f (firstQ (e.symm s).1 y.1))) x))) ≠
        blockVal x.1 y.1 + sideVal x.2 y.2 + a x + b y)).card = (Finset.univ.filter wrong).card := by
      apply Finset.card_equiv e.symm
      intro s
      simp [wrong, hpack _]
    rw [hcard, Fintype.card_prod, Nat.cast_mul]
    by_cases hD : smallD x.1 y.1
    · have inc (s : Rand t × H) (hw : wrong s) : read s.2 y.1 (hash s.2 x.1) ≠ x.1 :=
        fun he => hw (decode_ok hash read a b s x y (.inr he))
      have h := count_right wrong (fun h => read h y.1 (hash h x.1) ≠ x.1) inc
      calc
        _ ≤ (Fintype.card (Rand t) : ℚ) * _ := by exact_mod_cast h
        _ ≤ (Fintype.card (Rand t) : ℚ) * (Fintype.card H * ((2047:ℚ)/2048)^t) :=
          mul_le_mul_of_nonneg_left (near x.1 y.1 hD) (Nat.cast_nonneg _)
        _ = _ := by ring
    · have inc (s : Rand t × H) (hw : wrong s) : 2*t < 5*(maskQ s.1 (firstQ s.1 y.1) x.1).card := by
        apply lt_of_not_ge
        intro h
        exact hw (decode_ok hash read a b s x y (.inl h))
      have h := count_left wrong (fun z => 2*t < 5*(maskQ z (firstQ z y.1) x.1).card) inc
      calc
        _ ≤ _ * (Fintype.card H : ℚ) := by exact_mod_cast h
        _ ≤ (Fintype.card (Rand t) * ((2047:ℚ)/2048)^t) * Fintype.card H :=
          mul_le_mul_of_nonneg_right (far x.1 y.1 hD) (Nat.cast_nonneg _)
        _ = _ := by ring

end Comm29953

namespace Concentration29953
open Finset

theorem product_le_budget {I : Type*} [DecidableEq I] (s : Finset I) (x : I → ℚ)
    (a : ℚ) (ha : 0 ≤ a) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hs : ∑ i ∈ s, x i ≤ s.card * a) : ∏ i ∈ s, x i ≤ a ^ s.card := by
  classical
  induction s using Finset.strongInductionOn generalizing x with
  | _ s ih =>
    by_cases hall : ∀ i ∈ s, x i ≤ a
    · simpa using Finset.prod_le_prod₀ hx hall
    push Not at hall
    obtain ⟨j, hj, hlarge⟩ := hall
    obtain ⟨i, hi, hsmall⟩ := Finset.exists_le_of_sum_le (f := x) (g := fun _ => a)
      ⟨j, hj⟩ (by simpa [nsmul_eq_mul] using hs)
    have hji : j ≠ i := by rintro rfl; exact hlarge.not_ge hsmall
    let t := s.erase i
    let u := t.erase j
    have hjt : j ∈ t := Finset.mem_erase.mpr ⟨hji, hj⟩
    have ht : insert i t = s := Finset.insert_erase hi
    have hu : insert j u = t := Finset.insert_erase hjt
    have hit : i ∉ t := Finset.notMem_erase _ _
    have hju : j ∉ u := Finset.notMem_erase _ _
    let b := x i + x j - a
    let y := fun k => if k = j then b else x k
    have hb : 0 ≤ b := by dsimp [b]; linarith [hx i hi]
    have hy : ∀ k ∈ t, 0 ≤ y k := by
      intro k hk
      by_cases h : k = j
      · simpa [y, h] using hb
      · simpa [y, h] using hx k (Finset.mem_of_mem_erase hk)
    have hyu : ∀ k ∈ u, y k = x k := fun k hk => by simp [y, Finset.ne_of_mem_erase hk]
    have hys : ∑ k ∈ t, y k = b + ∑ k ∈ u, x k := by
      rw [← hu, Finset.sum_insert hju, Finset.sum_congr rfl hyu]; simp [y]
    have hyp : ∏ k ∈ t, y k = b * ∏ k ∈ u, x k := by
      rw [← hu, Finset.prod_insert hju, Finset.prod_congr rfl hyu]; simp [y]
    have hc : s.card = t.card + 1 := by rw [← ht, Finset.card_insert_of_notMem hit]
    have hxs : ∑ k ∈ s, x k = x i + (x j + ∑ k ∈ u, x k) := by
      rw [← ht, Finset.sum_insert hit, ← hu, Finset.sum_insert hju]
    have hxp : ∏ k ∈ s, x k = x i * (x j * ∏ k ∈ u, x k) := by
      rw [← ht, Finset.prod_insert hit, ← hu, Finset.prod_insert hju]
    have hbudget : ∑ k ∈ t, y k ≤ t.card * a := by
      rw [hxs, hc, Nat.cast_add_one] at hs
      rw [hys]; dsimp [b]; linarith
    have hind := ih t (Finset.erase_ssubset hi) y hy hbudget
    have hp : 0 ≤ ∏ k ∈ u, x k := Finset.prod_nonneg fun k hk =>
      hx k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
    have hpair : x i * x j ≤ a * b := by
      dsimp [b]; nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (sub_nonneg.mpr hlarge.le)]
    rw [hxp, ← mul_assoc, hc, pow_succ']
    calc
      _ ≤ (a * b) * ∏ k ∈ u, x k := mul_le_mul_of_nonneg_right hpair hp
      _ = a * ∏ k ∈ t, y k := by rw [hyp, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hind ha

private theorem threshold {t c : ℕ} (h : 2*t ≤ 5*c) :
    (2049/2000 : ℚ)^t ≤ (17/16 : ℚ)^c := by
  apply le_of_pow_le_pow_left₀ (n := 5) (by decide) (by positivity)
  calc
    ((2049/2000 : ℚ)^t)^5 = ((2049/2000 : ℚ)^5)^t := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ((17/16 : ℚ)^2)^t := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ = (17/16 : ℚ)^(2*t) := (pow_mul _ _ _).symm
    _ ≤ (17/16 : ℚ)^(5*c) := pow_le_pow_right₀ (by norm_num) h
    _ = ((17/16 : ℚ)^c)^5 := by rw [Nat.mul_comm, pow_mul]

theorem blockTail {t : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (hit : Fin t → S → Bool)
    (mean : 112 * (∑ i, (univ.filter fun s => hit i s).card) ≤ 43*t*Fintype.card S) :
    ((univ.filter fun z : Fin t → S => 2*t < 5*(univ.filter fun i => hit i (z i)).card).card : ℚ)
       ≤ Fintype.card (Fin t → S) * ((2047:ℚ)/2048)^t := by
  classical
  let c := fun z : Fin t → S => (univ.filter fun i => hit i (z i)).card
  let bad := univ.filter fun z : Fin t → S => 2*t < 5*c z
  let n : ℚ := Fintype.card S
  let h := fun i : Fin t => ((univ.filter fun s => hit i s).card : ℚ)
  let w := fun i s => if hit i s then (17/16 : ℚ) else 1
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hw (z : Fin t → S) : ∏ i, w i (z i) = (17/16 : ℚ)^c z := by
    simp [w, c, Finset.prod_ite, div_pow]
  have wsum (i : Fin t) : ∑ s, w i s = n + h i / 16 := by
    have hh (s : S) : w i s = 1 + (if hit i s then (1:ℚ) else 0)/16 := by
      unfold w; split <;> simp_all <;> norm_num
    simp_rw [hh]
    simp only [sum_add_distrib, div_eq_mul_inv, ← sum_mul, sum_boole, h, n,
      sum_const, card_univ, nsmul_eq_mul, mul_one]
  have mh : 112 * (∑ i, h i) ≤ 43*(t:ℚ)*n := by
    dsimp [h, n]; exact_mod_cast mean
  have av : ∑ i, (n + h i / 16) ≤ t * (n * (1+43/1792)) := by
    simp_rw [div_eq_mul_inv]; rw [sum_add_distrib, ← sum_mul]; simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; linarith
  have mom : (∑ z : Fin t → S, (17/16 : ℚ)^c z) ≤ (n * (1+43/1792))^t := by
    simp_rw [← hw]; rw [← Fintype.prod_sum]; simp_rw [wsum]
    simpa only [card_univ, Fintype.card_fin] using
      product_le_budget univ (fun i => n + h i / 16) (n * (1 + 43/1792))
        (by positivity) (fun i _ => by dsimp [h]; positivity)
        (by simpa only [card_univ, Fintype.card_fin] using av)
  have total : (bad.card : ℚ) * (2049/2000 : ℚ)^t ≤ (n * (1+43/1792))^t := calc
    _ = ∑ _z ∈ bad, (2049/2000 : ℚ)^t := by simp
    _ ≤ ∑ z ∈ bad, (17/16 : ℚ)^c z := by
      apply sum_le_sum; intro z hz
      exact threshold (mem_filter.mp hz).2.le
    _ ≤ ∑ z, (17/16 : ℚ)^c z := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ ≤ _ := mom
  have tail : (bad.card : ℚ) ≤ n^t * ((2047:ℚ)/2048)^t := by
    apply le_of_mul_le_mul_right (a := (2049/2000 : ℚ)^t) _ (by positivity)
    refine total.trans ?_
    rw [← mul_pow, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by norm_num) hn
  simpa [Fintype.card_fun, n, bad, c] using tail

end Concentration29953
namespace Concentration29953
open Finset

theorem blockMean {t : ℕ} (hit : Fin t → Fin 32 × Fin 7 → Bool)
    (different : Fin t → Fin 32 → Bool)
    (counts : ∀ i j, (univ.filter fun r : Fin 7 => hit i (j,r)).card =
      if different i j then 1 else 7)
    (far : 23*t ≤ ∑ i, (univ.filter fun j => different i j).card) :
    112 * (∑ i, (univ.filter fun s => hit i s).card) ≤ 43*t*Fintype.card (Fin 32 × Fin 7) := by
  classical
  have mass (i : Fin t) : (univ.filter fun s => hit i s).card +
      6*(univ.filter fun j => different i j).card = 224 := by
    rw [card_filter, Fintype.sum_prod_type]
    simp_rw [← card_filter, counts]
    rw [card_filter, mul_sum, ← sum_add_distrib]
    have coord (j : Fin 32) : (if different i j then 1 else 7) +
        6*(if different i j then 1 else 0) = 7 := by split <;> simp_all
    simp_rw [coord]; simp
  have allmass := sum_congr (s₁ := univ) rfl (fun i _ => mass i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at allmass
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp only [Nat.cast_id] at allmass
  omega

end Concentration29953

namespace Comm29953
open Finset

theorem far_hit_mean {t : ℕ} (x y : Block t)
    (far : 23*t ≤ (univ.filter fun p : Fin t × Fin 32 => x p ≠ y p).card) :
    112 * (∑ i : Fin t, (univ.filter fun s : Fin 32 × Fin 7 =>
      bucket s.2 (x (i,s.1)) = bucket s.2 (y (i,s.1))).card) ≤ 43*t*Fintype.card (Fin 32 × Fin 7) := by
  classical
  let hit : Fin t → Fin 32 × Fin 7 → Bool := fun i s =>
    decide (bucket s.2 (x (i,s.1)) = bucket s.2 (y (i,s.1)))
  let different : Fin t → Fin 32 → Bool := fun i j => decide (x (i,j) ≠ y (i,j))
  have hh (i j) : (univ.filter fun r : Fin 7 => hit i (j,r)).card =
      if different i j then 1 else 7 := by
    simp only [hit, different, decide_eq_true_eq, bucket_card]; split <;> simp_all
  have hd : 23*t ≤ ∑ i, (univ.filter fun j => different i j).card := by
    rw [card_filter, Fintype.sum_prod_type] at far
    simpa [different, card_filter] using far
  simpa only [hit, decide_eq_true_eq] using Concentration29953.blockMean hit different hh hd

theorem far_mask_tail {t : ℕ} (x y : Block t)
    (far : 23*t ≤ (univ.filter fun p : Fin t × Fin 32 => x p ≠ y p).card) :
    ((univ.filter fun z : Rand t => 2*t < 5*(maskQ z (firstQ z y) x).card).card : ℚ) ≤
    Fintype.card (Rand t) * ((2047:ℚ)/2048)^t := by
  classical
  let hit : Fin t → Fin 32 × Fin 7 → Bool := fun i s =>
    decide (bucket s.2 (x (i,s.1)) = bucket s.2 (y (i,s.1)))
  have hm := far_hit_mean x y far
  have h := Concentration29953.blockTail hit (by simpa only [hit, decide_eq_true_eq] using hm)
  have he (z : Rand t) : (univ.filter fun i => hit i (z i)).card =
      (maskQ z (firstQ z y) x).card := by
    apply congrArg Finset.card
    ext i
    unfold maskQ firstQ
    rw [mem_filter, mem_filter]
    simp [hit]
  simpa only [he] using h

end Comm29953

namespace Volume29953

theorem maskArith (t C : ℕ)
    (h : (C:ℚ) * (2/3:ℚ)^(2*t/5) ≤ (1+2/3:ℚ)^t) : C ≤ 2^(t-t/40) := by
  have hc := (le_div_iff₀ (show 0 < (2/3:ℚ)^(2*t/5) by positivity)).2 h
  rw [div_eq_mul_inv, ← inv_pow, show (2/3:ℚ)⁻¹ = 3/2 by norm_num] at hc
  have hu : (C:ℚ)^40 ≤ ((1+2/3:ℚ)^t * (3/2:ℚ)^(2*t/5))^40 :=
    pow_le_pow_left₀ (by positivity) hc _
  have hb : (1+2/3:ℚ)^40 * (3/2:ℚ)^16 ≤ 2^39 := by norm_num
  have hr : (C:ℚ)^40 ≤ ((2:ℚ)^(t-t/40))^40 := calc
    _ ≤ _ := hu
    _ = (1+2/3:ℚ)^(40*t) * (3/2:ℚ)^((2*t/5)*40) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 40]
    _ ≤ (1+2/3:ℚ)^(40*t) * (3/2:ℚ)^(16*t) := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    _ = ((1+2/3:ℚ)^40 * (3/2:ℚ)^16)^t := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ ((2:ℚ)^39)^t := pow_le_pow_left₀ (by positivity) hb _
    _ ≤ _ := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact_mod_cast le_of_pow_le_pow_left₀ (by norm_num : 40 ≠ 0) (by positivity) hr

theorem nearArith (t C : ℕ)
    (h : (C:ℚ)*(3/8:ℚ)^(23*t) ≤ (1+7*(3/8):ℚ)^(32*t)) :
    (C:ℚ) ≤ (2:ℚ)^(94*t - t/40) * (2047/2048:ℚ)^t := by
  have hc := (le_div_iff₀ (show 0 < (3/8:ℚ)^(23*t) by positivity)).2 h
  rw [div_eq_mul_inv, ← inv_pow, show (3/8:ℚ)⁻¹ = 8/3 by norm_num,
    pow_mul, pow_mul, ← mul_pow] at hc
  let a : ℚ := (1+7*(3/8):ℚ)^32 * (8/3:ℚ)^23
  let b : ℚ := 2047/2048
  change (C:ℚ) ≤ a^t at hc
  change (C:ℚ) ≤ (2:ℚ)^(94*t - t/40) * b^t
  have hsmall : a ≤ (2:ℚ)^93*b := by norm_num [a,b]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hbn : 0 ≤ b := by dsimp [b]; positivity
  calc
    _ ≤ a^t := hc
    _ ≤ ((2:ℚ)^93*b)^t := pow_le_pow_left₀ ha hsmall _
    _ ≤ _ := by
      rw [mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

end Volume29953

namespace Volume29953
open Finset

private theorem lowerMoment {X : Type*} [Fintype X] (s : Finset X) (D : X → ℕ)
    (k : ℕ) (a : ℚ) (ha : 0 ≤ a) (ha' : a ≤ 1) (hs : ∀ x ∈ s, D x ≤ k) :
    (s.card : ℚ) * a^k ≤ ∑ x, a^(D x) := by
  classical
  calc
    _ = ∑ _x ∈ s, a^k := by simp
    _ ≤ ∑ x ∈ s, a^(D x) := sum_le_sum fun x hx => pow_le_pow_of_le_one ha ha' (hs x hx)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)

theorem maskMoment (t : ℕ) :
    (Fintype.card {M : Finset (Fin t) // 5*M.card ≤ 2*t} : ℚ) * (2/3:ℚ)^(2*t/5) ≤
    (1 + 2/3:ℚ)^t := by
  classical
  rw [Fintype.card_subtype]
  refine (lowerMoment _ Finset.card _ _ (by norm_num) (by norm_num) ?_).trans ?_
  · intro M hM
    have h := (mem_filter.mp hM).2
    exact (show M.card ≤ 2*t/5 by omega)
  · exact le_of_eq (by simpa [add_comm] using Fintype.sum_pow_mul_eq_add_pow (Fin t) (2/3:ℚ) 1)

theorem ballMoment (t : ℕ) (y : Fin t × Fin 32 → Fin 8) :
    ((univ.filter fun x : Fin t × Fin 32 → Fin 8 => (univ.filter (fun p => x p ≠ y p)).card ≤ 23*t).card : ℚ) *
      (3/8:ℚ)^(23*t) ≤ (1+7*(3/8):ℚ)^(32*t) := by
  classical
  let c := fun x : Fin t × Fin 32 → Fin 8 => (univ.filter (fun p => x p ≠ y p)).card
  let w := fun (p : Fin t × Fin 32) (b : Fin 8) => if b ≠ y p then (3/8:ℚ) else 1
  have prodW (x) : ∏ p, w p (x p) = (3/8:ℚ)^(c x) := by
    simp [w, c, prod_ite, div_pow]
  have sumW : ∀ b : Fin 8, (∑ v : Fin 8, (if v ≠ b then (3/8:ℚ) else 1)) = 1+7*(3/8:ℚ) := by
    intro b
    rw [Finset.sum_ite, Finset.filter_ne']
    norm_num [Finset.card_erase_of_mem, Finset.filter_eq']
  refine (lowerMoment _ c _ _ (by norm_num) (by norm_num) (fun x hx => (mem_filter.mp hx).2)).trans ?_
  simp_rw [← prodW]
  rw [← Fintype.prod_sum]
  simp only [w, sumW, Finset.prod_const, card_univ, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, le_refl]

end Volume29953

namespace Volume29953

theorem thinCard (t : ℕ) : Fintype.card {M : Finset (Fin t) // 5*M.card ≤ 2*t} ≤ 2^(t-t/40) :=
  maskArith t _ (maskMoment t)

theorem ballCard (t : ℕ) (y : Fin t × Fin 32 → Fin 8) :
    ((Finset.univ.filter fun x : Fin t × Fin 32 → Fin 8 =>
      (Finset.univ.filter (fun p => x p ≠ y p)).card ≤ 23*t).card : ℚ) ≤
    (2:ℚ)^(94*t-t/40) * (2047/2048:ℚ)^t :=
  nearArith t _ (ballMoment t y)

end Volume29953

namespace Hash29953
open Finset
open scoped BigOperators

theorem collision_count {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (x z : A) (hz : z ≠ x) :
    ((univ : Finset (A → B)).filter (fun h => h z = h x)).card * Fintype.card B =
      Fintype.card (A → B) := by
  classical
  let C := (univ : Finset (A → B)).filter (fun h => h z = h x)
  have eqv : (C × B) ≃ (A → B) := {
    toFun := fun p => Function.update p.1.val z p.2
    invFun := fun h => (⟨Function.update h z (h x), by simp [C, Ne.symm hz]⟩, h z)
    left_inv := by
      rintro ⟨⟨h, hm⟩, b⟩
      have hz' : h z = h x := (mem_filter.mp hm).2
      apply Prod.ext
      · apply Subtype.ext
        funext a
        by_cases ha : a = z
        · subst a; simp [Ne.symm hz, hz']
        · simp [ha, Ne.symm hz]
      · simp
    right_inv := by
      intro h
      funext a
      by_cases ha : a = z
      · subst a; simp
      · simp [ha] }
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_congr eqv

variable {A B : Type*} [DecidableEq B]

noncomputable def decode (h : A → B) (ball : Finset A) (fallback : A) (s : B) : A :=
  if e : ∃ z ∈ ball, h z = s then Classical.choose e else fallback

theorem decode_spec (h : A → B) (ball : Finset A) (fallback x : A) (hx : x ∈ ball) :
    decode h ball fallback (h x) ∈ ball ∧ h (decode h ball fallback (h x)) = h x := by
  have e : ∃ z ∈ ball, h z = h x := ⟨x, hx, rfl⟩
  simpa only [decode, dite_eq_left e] using Classical.choose_spec e

theorem decode_success (h : A → B) (ball : Finset A) (fallback x : A) (hx : x ∈ ball)
    (uniq : ∀ z ∈ ball, h z = h x → z = x) : decode h ball fallback (h x) = x :=
  let hs := decode_spec h ball fallback x hx
  uniq _ hs.1 hs.2

theorem bad_count [Fintype A] [DecidableEq A] [Fintype B] (ball : Finset A) (fallback x : A) (hx : x ∈ ball) :
    ((univ : Finset (A → B)).filter (fun h => decode h ball fallback (h x) ≠ x)).card *
      Fintype.card B ≤ ball.card * Fintype.card (A → B) := by
  classical
  let C (z : A) := (univ : Finset (A → B)).filter (fun h => h z = h x)
  let bad := (univ : Finset (A → B)).filter (fun h => decode h ball fallback (h x) ≠ x)
  have sub : bad ⊆ (ball.erase x).biUnion C := by
    intro h hh
    have hs := decode_spec h ball fallback x hx
    exact mem_biUnion.mpr ⟨_, mem_erase.mpr ⟨(mem_filter.mp hh).2, hs.1⟩,
      mem_filter.mpr ⟨mem_univ _, hs.2⟩⟩
  calc
    bad.card * Fintype.card B ≤ (∑ z ∈ ball.erase x, (C z).card) * Fintype.card B :=
      Nat.mul_le_mul_right _ ((card_le_card sub).trans card_biUnion_le)
    _ = ∑ z ∈ ball.erase x, Fintype.card (A → B) := by
      rw [sum_mul]
      exact sum_congr rfl fun z hz => collision_count x z (mem_erase.mp hz).1
    _ = (ball.erase x).card * Fintype.card (A → B) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card (erase_subset _ _))

end Hash29953
namespace Comm29953
open Finset Classical

abbrev HashSeed (t : ℕ) := Block t → HashMsg t

noncomputable def nearDecode {t : ℕ} (h : HashSeed t) (y : Block t) (s : HashMsg t) : Block t :=
  Hash29953.decode h (univ.filter fun z => smallD z y) y s

theorem nearError {t : ℕ} (x y : Block t) (hxy : smallD x y)
    (hvol : (((univ : Finset (Block t)).filter fun z => smallD z y).card : ℚ) ≤
      (2 : ℚ)^hBits t * ((2047:ℚ)/2048)^t) :
    (((univ : Finset (HashSeed t)).filter fun h => nearDecode h y (h x) ≠ x).card : ℚ) ≤
      Fintype.card (HashSeed t) * ((2047:ℚ)/2048)^t := by
  let ball := (univ : Finset (Block t)).filter fun z => smallD z y
  have hcount := Hash29953.bad_count (B := HashMsg t) ball y x (mem_filter.mpr ⟨mem_univ _, hxy⟩)
  let bad := (univ : Finset (HashSeed t)).filter fun h => nearDecode h y (h x) ≠ x
  change bad.card * Fintype.card (HashMsg t) ≤ ball.card * Fintype.card (HashSeed t) at hcount
  rw [Fintype.card_fin] at hcount
  have hq : (bad.card : ℚ) * (2:ℚ)^hBits t ≤ ball.card * (Fintype.card (HashSeed t) : ℚ) := by
    exact_mod_cast hcount
  apply le_of_mul_le_mul_right (a := (2:ℚ)^hBits t) _ (by positivity)
  calc
    (bad.card : ℚ) * _ ≤ _ := hq
    _ ≤ ((2:ℚ)^hBits t * ((2047:ℚ)/2048)^t) * (Fintype.card (HashSeed t) : ℚ) :=
      mul_le_mul_of_nonneg_right hvol (by positivity)
    _ = _ := by ring

theorem nearAPI (t : ℕ)
    (hvol : ∀ y : Block t, (((univ : Finset (Block t)).filter fun z => smallD z y).card : ℚ) ≤
      (2 : ℚ)^hBits t * ((2047:ℚ)/2048)^t) :
    ∃ (H : ℕ) (_ : 0 < H) (hash : Fin H → Block t → HashMsg t)
        (read : Fin H → Block t → HashMsg t → Block t), ∀ x y, smallD x y →
      (((univ : Finset (Fin H)).filter fun h => read h y (hash h x) ≠ x).card : ℚ) ≤
        H * ((2047:ℚ)/2048)^t := by
  let e := Fintype.equivFin (HashSeed t)
  refine ⟨_, Fintype.card_pos, e.symm, fun h => nearDecode (e.symm h), ?_⟩
  intro x y hxy
  have heq : ((univ : Finset (Fin (Fintype.card (HashSeed t)))).filter
      fun h => nearDecode (e.symm h) y ((e.symm h) x) ≠ x).card =
      ((univ : Finset (HashSeed t)).filter fun h => nearDecode h y (h x) ≠ x).card := by
    apply Finset.card_equiv e.symm
    intro _
    simp
  rw [heq]
  exact nearError x y hxy (hvol y)

end Comm29953
namespace Comm29953

theorem allBlocks (t r : ℕ) : BlockAPI t r := by
  classical
  apply blockProtocol (H := HashSeed t) (Volume29953.thinCard t) (fun h x => h x) nearDecode
  · intro x y hD
    apply nearError x y hD
    have hball : (Finset.univ.filter fun z : Block t => smallD z y) =
        (Finset.univ.filter fun z : Fin t × Fin 32 → Fin 8 =>
          (Finset.univ.filter fun p => z p ≠ y p).card ≤ 23*t) := by
      ext z
      rw [Finset.mem_filter, Finset.mem_filter]
      rfl
    rw [hball]
    exact Volume29953.ballCard t y
  · intro x y hD
    exact far_mask_tail x y (le_of_lt (lt_of_not_ge hD))

end Comm29953

namespace Reindex29953
open Comm29953

abbrev Positions (m : ℕ) := (Fin (m/32) × Fin 32) ⊕ Fin (m%32)
noncomputable def idx (m : ℕ) : Positions m ≃ Fin m :=
  Fintype.equivFinOfCardEq (by simp [Positions]; omega)
noncomputable def split {m : ℕ} (x : Fin m → Fin 8) : Input (m/32) (m%32) :=
  (fun p => x (idx m (.inl p)), fun p => x (idx m (.inr p)))
noncomputable def unsplit {m : ℕ} (x : Input (m/32) (m%32)) : Fin m → Fin 8 :=
  fun p => Sum.elim x.1 x.2 ((idx m).symm p)
private theorem unsplit_split {m : ℕ} (x : Fin m → Fin 8) : unsplit (split x) = x := by
  funext i
  obtain ⟨p,rfl⟩ := (idx m).surjective i
  cases p <;> simp [unsplit,split]

private theorem repart {m : ℕ} (x y : Fin m → Fin 8) :
    blockVal (split x).1 (split y).1 + sideVal (split x).2 (split y).2 =
    ((∑ i, (decide (x i = y i)).toNat : ℕ) : ZMod 2) := by
  calc
    _ = ∑ p : Positions m, eq1 (x (idx m p)) (y (idx m p)) := by
      rw [Fintype.sum_sum_type]; rfl
    _ = ∑ i : Fin m, eq1 (x i) (y i) := (idx m).sum_comp (fun i : Fin m => eq1 (x i) (y i))
    _ = _ := by
      rw [Nat.cast_sum]; apply Finset.sum_congr rfl; intro i _
      by_cases h : x i = y i <;> simp [eq1,h]

def tag (c : ZMod 2) : Bool := c.val == 1
private theorem tag_inj : Function.Injective tag := by decide
private theorem tag_add : ∀ p q : ZMod 2, tag (p+q) = xor (tag p) (tag q) := by decide
private theorem tag_bool : ∀ c : Bool, tag (c.toNat : ZMod 2) = c := by decide
private theorem tag_nat (n : ℕ) : tag (n : ZMod 2) = (n%2 == 1) := by simp only [tag, ZMod.val_natCast]

theorem transport (h : ∀ t r : ℕ, r < 32 → BlockAPI t r) : Guard29953.Abstract := by
  classical
  intro m φ ψ X t
  let a (x : Input (m/32) (m%32)) : ZMod 2 := (φ (unsplit (m:=m) x)).toNat
  let b (x : Input (m/32) (m%32)) : ZMod 2 := (ψ (unsplit (m:=m) x)).toNat
  obtain ⟨S,n,f,r,dc,hS,hsize,hp⟩ := h (m/32) (m%32) (Nat.mod_lt _ (by decide)) a b
  refine ⟨S,n,fun z y => f z (split y),fun z q x => r z q (split x),
    fun z y msg => tag (dc z (split y) msg),hS,?_,?_⟩
  · change 2*(m/32)+n ≤ 3*m-m/1280+2
    have hdiv : m/32/40 = m/1280 := by rw [Nat.div_div_eq_div_mul]
    have hrem : 32*(m/32)+m%32=m := by omega
    simpa only [hdiv,hrem] using hsize
  · intro x y
    have hv : tag (blockVal (split x).1 (split y).1 + sideVal (split x).2 (split y).2 + a (split x) + b (split y)) =
      xor (xor (φ x) (ψ y)) (((∑ i : Fin m, (decide (x i = y i)).toNat) % 2) == 1) := by
      rw [repart,tag_add,tag_add,tag_nat]; simp only [a,b,unsplit_split,tag_bool]
      exact (by decide : ∀ a b c : Bool, xor (xor a b) c = xor (xor b c) a) _ _ _
    dsimp only
    rw [← hv]
    simpa only [tag_inj.ne_iff] using hp (split x) (split y)

end Reindex29953

end PEqualNP.Outside.L_meta_29953_aux

theorem PEqualNP.Outside.L_meta_29953 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  let groups := m/32
  ∃ (seeds replyBits : Nat)
    (first : Fin seeds → K → Fin (2^(2*groups)))
    (reply : Fin seeds → Fin (2^(2*groups)) → K → Fin (2^replyBits))
    (decode : Fin seeds → K → Fin (2^replyBits) → Bool),
    0 < seeds ∧ 2*groups + replyBits ≤ 3*m - m/1280 + 2 ∧
    ∀ pair ∈ pairs,
      let wrong := (Finset.univ : Finset (Fin seeds)).filter (fun z =>
        decode z pair.2 (reply z (first z pair.2) pair.1) ≠ truth pair.1 pair.2)
      (wrong.card : ℚ) ≤ (seeds : ℚ)*((2047 : ℚ)/2048)^groups) := by
  exact PEqualNP.Outside.L_meta_29953_aux.Guard29953.bridge (PEqualNP.Outside.L_meta_29953_aux.Reindex29953.transport (fun t r _ => PEqualNP.Outside.L_meta_29953_aux.Comm29953.allBlocks t r))
