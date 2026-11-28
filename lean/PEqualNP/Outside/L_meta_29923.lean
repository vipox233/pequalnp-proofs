import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn
import Mathlib.Tactic
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620

namespace PEqualNP.Outside.L_meta_29923_aux

open Finset

private def publicThree {K : Type} (pairs : Finset (K × K)) (truth : K → K → Bool)
    (budget : Nat) (err : ℝ) : Prop :=
  ∃ (seeds firstBits : Nat) (middleBits lastBits : Bool → Nat)
    (first : Fin seeds → K → Fin (2^firstBits))
    (middle : Fin seeds → Fin (2^firstBits) → K → (Σ b : Bool, Fin (2^(middleBits b))))
    (last : (b : Bool) → Fin seeds → K → Fin (2^(middleBits b)) → Fin (2^(lastBits b)))
    (read : (b : Bool) → Fin seeds → K → Fin (2^firstBits) → Fin (2^(lastBits b)) → Bool),
    0 < seeds ∧ (∀ b, firstBits+1+middleBits b+lastBits b ≤ budget) ∧
    ∀ p ∈ pairs,
      let predicts := fun z : Fin seeds =>
        let a := first z p.1
        let msg := middle z a p.2
        read msg.1 z p.2 a (last msg.1 z p.1 msg.2)
      (((Finset.univ : Finset (Fin seeds)).filter
        (fun z => predicts z ≠ truth p.1 p.2)).card : ℝ) ≤ (seeds : ℝ)*err

private lemma threePullback {K W : Type} [Fintype W]
    {pairs : Finset (K × K)} {truth : K → K → Bool} {model : W → W → Bool}
    (L R : K → W) (h : ∀ p ∈ pairs, truth p.1 p.2 = model (L p.1) (R p.2))
    {c : Nat} {e : ℝ} (hp : publicThree (univ : Finset (W × W)) model c e) :
    publicThree pairs truth c e := by
  obtain ⟨s, f, mb, lb, send, reply, last, read, hs, hc, he⟩ := hp
  refine ⟨s, f, mb, lb, (fun z x => send z (L x)), (fun z a y => reply z a (R y)),
    (fun b z x t => last b z (L x) t), (fun b z y a t => read b z (R y) a t), hs, hc, ?_⟩
  intro p hp
  rw [h p hp]
  exact he (L p.1, R p.2) (mem_univ _)

private noncomputable def encode {A : Type*} [Fintype A] {n : Nat}
    (h : Fintype.card A ≤ 2^n) : A ↪ Fin (2^n) :=
  (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb h)

private noncomputable def recover {A : Type*} [Fintype A] [Nonempty A] {n : Nat}
    (h : Fintype.card A ≤ 2^n) : Fin (2^n) → A :=
  Function.invFun (encode h)

private lemma recover_encode {A : Type*} [Fintype A] [Nonempty A] {n : Nat}
    (h : Fintype.card A ≤ 2^n) (a : A) : recover h (encode h a) = a :=
  Function.leftInverse_invFun (encode h).injective a

private noncomputable def eventCard {A : Type*} (p : A → Prop) : ℝ :=
  (Nat.card {a : A // p a} : ℝ)

private lemma eventCard_filter {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    eventCard p = ((univ.filter p).card : ℝ) := by
  unfold eventCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma eventCard_mono {A : Type*} [Fintype A] {p q : A → Prop}
    (h : ∀ a, p a → q a) : eventCard p ≤ eventCard q := by
  classical
  rw [eventCard_filter, eventCard_filter]
  exact_mod_cast card_le_card (monotone_filter_right univ (fun a _ => h a))

private lemma eventCard_union {A : Type*} [Fintype A] (p q : A → Prop) :
    eventCard (fun a => p a ∨ q a) ≤ eventCard p + eventCard q := by
  classical
  rw [eventCard_filter, eventCard_filter, eventCard_filter, filter_or]
  exact_mod_cast card_union_le (univ.filter p) (univ.filter q)

private lemma eventCard_congr {A B : Type*}
    (e : A ≃ B) (p : B → Prop) : eventCard (fun a => p (e a)) = eventCard p := by
  unfold eventCard
  exact congrArg (fun n : Nat => (n : ℝ)) (Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)))

private lemma eventCard_fst {A B : Type*} [Fintype B] (p : A → Prop) :
    eventCard (fun z : A × B => p z.1) = eventCard p * Fintype.card B := by
  unfold eventCard
  have e : {z : A × B // p z.1} ≃ {a : A // p a} × B :=
    { toFun := fun z => (⟨z.val.1, z.property⟩, z.val.2),
      invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := B), Nat.cast_mul]

private lemma eventCard_snd {A B : Type*} [Fintype A] (p : B → Prop) :
    eventCard (fun z : A × B => p z.2) = Fintype.card A * eventCard p := by
  rw [← eventCard_congr (Equiv.prodComm B A) (fun z : A × B => p z.2)]
  change eventCard (fun z : B × A => p z.1) = _
  rw [eventCard_fst, mul_comm]

open Finset

-- Local guarded-window identity adapted from lean/PEqualNP/Outside/L_meta_29752.lean
-- at c98185bc025b6ab4b6dde2d166fa3b27df97a51b. Only its pointwise direction is used.

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

private def modelTruth {m : ℕ} (φ ψ : (Fin m → Block) → Bool) (x y : Fin m → Block) : Bool :=
  xor (xor (φ x) (ψ y)) (parityOn univ fun i => decide (x i = y i))

private lemma xor_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

section Concentration

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal

private lemma tailUniformReal {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (s : Finset B) :
    (uniformOn (Set.univ : Set B)).real (s : Set B) = (s.card : ℝ) / Fintype.card B := by
  rw [measureReal_def, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div]
  simp

private lemma upperTail {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (hit : I → A → Bool) (t d : ℝ) (hd : 0 ≤ d)
    (ht : (∑ i, ((Finset.univ.filter (fun a : A => hit i a = true)).card : ℝ) /
      Fintype.card A) + d * Fintype.card I ≤ t) :
    ((Finset.univ.filter (fun z : I → A => t ≤ ∑ i, ((hit i (z i)).toNat : ℝ))).card : ℝ) ≤
      (Fintype.card (I → A) : ℝ) * Real.exp (-2 * d^2 * Fintype.card I) := by
  let : MeasurableSpace A := ⊤
  let : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  let m : I → Measure A := fun _ => uniformOn Set.univ
  have : ∀ i, IsProbabilityMeasure (m i) := fun _ => inferInstanceAs
    (IsProbabilityMeasure (uniformOn (Set.univ : Set A)))
  let μ : Measure (I → A) := Measure.pi m
  have hμ : μ = uniformOn Set.univ := by
    apply Measure.ext_of_singleton
    intro z
    simp only [μ, Measure.pi_singleton, m, uniformOn_univ, Measure.count_singleton, one_div]
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]
  let X (i : I) (a : A) : ℝ := (hit i a).toNat
  let p (i : I) : ℝ := ((Finset.univ.filter (fun a : A => hit i a = true)).card : ℝ) /
    Fintype.card A
  let Y (i : I) (z : I → A) : ℝ := X i (z i) - p i
  have hmean (i : I) : (∫ z, X i (z i) ∂μ) = p i := by
    rw [integral_comp_eval (μ := m) (measurable_of_finite (X i)).aestronglyMeasurable]
    let s := Finset.univ.filter (fun a : A => hit i a = true)
    have hindicator : X i = (s : Set A).indicator (1 : A → ℝ) := by
      funext a
      cases h : hit i a <;> simp [X, s, Set.indicator, h]
    rw [hindicator, integral_indicator_one s.measurableSet]
    exact tailUniformReal s
  have hIndep : iIndepFun Y μ :=
    iIndepFun_pi (μ := m) (X := fun i a => X i a - p i)
      (fun i => (measurable_of_finite (fun a => X i a - p i)).aemeasurable)
  have hSub (i : I) : HasSubgaussianMGF (Y i) (1 / 4) μ := by
    have hb : ∀ᵐ z ∂μ, X i (z i) ∈ Set.Icc (0 : ℝ) 1 := by
      exact ae_of_all _ (fun z => by cases h : hit i (z i) <;> simp [X, h])
    have h := hasSubgaussianMGF_of_mem_Icc
      (measurable_of_finite (fun z : I → A => X i (z i))).aemeasurable hb
    rw [hmean i] at h
    have hquarter : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) = (1 / 4 : ℝ≥0) := by norm_num
    rw [hquarter] at h
    exact h
  let s := Finset.univ.filter (fun z : I → A => t ≤ ∑ i, X i (z i))
  have hsub : (s : Set (I → A)) ⊆ {z | d * Fintype.card I ≤ ∑ i, Y i z} := by
    intro z hz
    have hz' : t ≤ ∑ i, X i (z i) := (Finset.mem_filter.mp hz).2
    change d * Fintype.card I ≤ ∑ i, (X i (z i) - p i)
    rw [Finset.sum_sub_distrib]
    exact le_sub_iff_add_le.mpr ((add_comm _ _).trans_le (ht.trans hz'))
  have hbound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep
    (s := Finset.univ) (c := fun _ => 1 / 4) (fun i _ => hSub i)
    (show 0 ≤ d * (Fintype.card I : ℝ) by positivity)
  have hexp : -(d * (Fintype.card I : ℝ))^2 / (2 * ∑ _ : I, (1 / 4 : ℝ≥0)) =
      -2 * d^2 * Fintype.card I := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    by_cases hzero : Fintype.card I = 0
    · simp [hzero]
    · have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hzero
      field_simp
      ring
  rw [hexp] at hbound
  have hprob := (measureReal_mono (μ := μ) hsub).trans hbound
  rw [hμ, tailUniformReal s] at hprob
  have hcard : (0 : ℝ) < Fintype.card (I → A) := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hcard).mp hprob |>.trans_eq (mul_comm _ _)

end Concentration

-- The front projections have respective nonzero kernel vectors
-- 100, 010, 001, 110, 101, 011, and 111. The back bit separates each kernel pair.
private def labelFront (d : Fin 7) (x : Bool × Bool × Bool) : Bool × Bool :=
  let (a, b, c) := x
  match d.val with
  | 0 => (b, c)
  | 1 => (a, c)
  | 2 => (a, b)
  | 3 => (xor a b, c)
  | 4 => (xor a c, b)
  | 5 => (a, xor b c)
  | _ => (xor a b, xor a c)

private def labelBack (d : Fin 7) (x : Bool × Bool × Bool) : Bool :=
  let (a, b, c) := x
  match d.val with
  | 1 | 5 => b
  | 2 => c
  | _ => a

private theorem labelEq (d : Fin 7) (x y : Bool × Bool × Bool) :
    decide (x = y) =
      if labelFront d x = labelFront d y then xor (!(labelBack d x)) (labelBack d y)
      else false := by
  revert d x y
  decide +kernel

private theorem labelCount (x y : Bool × Bool × Bool) :
    (Finset.univ.filter (fun d : Fin 7 => labelFront d x = labelFront d y)).card =
      if x = y then 7 else 1 := by
  revert x y
  decide +kernel

private noncomputable def decodeWord {W Z : Type*} (D : W → Finset W)
    (hash : W → Z) (x : W) (msg : Z) : W := by
  classical
  exact if h : ∃ w ∈ D x, hash w = msg then h.choose else x

private theorem decodeWord_eq {W Z : Type*} (D : W → Finset W) (hash : W → Z)
    (x y : W) (hy : y ∈ D x)
    (hunique : ∀ w ∈ D x, hash w = hash y → w = y) :
    decodeWord D hash x (hash y) = y := by
  classical
  have h : ∃ w ∈ D x, hash w = hash y := ⟨y, hy, rfl⟩
  unfold decodeWord
  rw [dite_eq_left h]
  exact hunique h.choose h.choose_spec.1 h.choose_spec.2

-- The saved value is precisely the overwritten coordinate of the original table.
private def hashCollisionTableEquiv {W Z : Type*} [DecidableEq W]
    {w y : W} (hne : w ≠ y) : ({h : W → Z // h w = h y} × Z) ≃ (W → Z) where
  toFun p := Function.update p.1.val w p.2
  invFun h := (⟨Function.update h w (h y), by simp [Function.update_of_ne hne.symm]⟩, h w)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext z
      by_cases hz : z = w
      · subst z
        simpa [Function.update_of_ne hne.symm] using p.1.property.symm
      · simp [Function.update_of_ne hz]
    · simp
  right_inv h := by
    funext z
    by_cases hz : z = w
    · subst z
      simp
    · simp [Function.update_of_ne hz]

private theorem hashCollisionCount {W Z : Type*} [Fintype W] [DecidableEq W]
    [Fintype Z] [DecidableEq Z] {w y : W} (hne : w ≠ y) :
    ((Finset.univ : Finset (W → Z)).filter (fun h => h w = h y)).card * Fintype.card Z =
      Fintype.card (W → Z) := by
  rw [← Fintype.card_subtype (fun h : W → Z => h w = h y), ← Fintype.card_prod]
  exact Fintype.card_congr (hashCollisionTableEquiv hne)

private theorem hashFailure {W : Type*} [Fintype W] [DecidableEq W]
    (D : W → Finset W) (x y : W) (n slack : ℕ) (hy : y ∈ D x)
    (hsize : (D x).card ≤ 2 ^ n) :
    (((Finset.univ : Finset (W → Fin (2 ^ (n + slack)))).filter
      (fun h => decodeWord D h x (h y) ≠ y)).card : ℝ) ≤
      (Fintype.card (W → Fin (2 ^ (n + slack))) : ℝ) / (2 : ℝ) ^ slack := by
  classical
  let Z := Fin (2 ^ (n + slack))
  let coll (w : W) : Finset (W → Z) := Finset.univ.filter (fun h => h w = h y)
  let fail : Finset (W → Z) := Finset.univ.filter (fun h => decodeWord D h x (h y) ≠ y)
  have hsub : fail ⊆ ((D x).erase y).biUnion coll := by
    intro h hh
    have hf := (Finset.mem_filter.mp hh).2
    by_contra hout
    apply hf
    apply decodeWord_eq D h x y hy
    intro w hw heq
    by_contra hne
    exact hout (Finset.mem_biUnion.mpr
      ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩)
  have hcard : fail.card * 2 ^ (n + slack) ≤ 2 ^ n * Fintype.card (W → Z) := calc
    fail.card * 2 ^ (n + slack) ≤
        (∑ w ∈ (D x).erase y, (coll w).card) * 2 ^ (n + slack) :=
      Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = ∑ w ∈ (D x).erase y, Fintype.card (W → Z) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      simpa only [coll, Z, Fintype.card_fin] using
        (hashCollisionCount (Z := Z) (Finset.mem_erase.mp hw).1)
    _ ≤ 2 ^ n * Fintype.card (W → Z) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_erase_le.trans hsize)
  have hcardR : (fail.card : ℝ) * (2 : ℝ) ^ (n + slack) ≤
      (2 : ℝ) ^ n * (Fintype.card (W → Z) : ℝ) := by
    exact_mod_cast hcard
  change (fail.card : ℝ) ≤ (Fintype.card (W → Z) : ℝ) / (2 : ℝ) ^ slack
  apply (le_div_iff₀ (by positivity)).2
  apply (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ) ^ n by positivity)).1
  simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hcardR

open Finset
open scoped BigOperators

private def capSupport {m : ℕ} {B : Type} (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (x : Fin m → B) : Finset (Fin m) := univ.filter (fun i => p i (x i))

private lemma capCardSupport {m : ℕ} {B : Type} [Fintype B] (p : Fin m → B → Prop) [∀ i, DecidablePred (p i)]
    (a b : ℕ) (ha : ∀ i, (univ.filter (p i)).card = a)
    (hb : ∀ i, (univ.filter (fun x => ¬p i x)).card = b) (J : Finset ℕ) :
    (univ.filter (fun x => (capSupport p x).card ∈ J)).card =
      ∑ j ∈ J, m.choose j * a ^ j * b ^ (m-j) := by
  classical
  have hfiber (s : Finset (Fin m)) :
      (univ.filter (fun x => capSupport p x = s)).card = a ^ s.card * b ^ (m-s.card) := by
    let allow := fun i => if i ∈ s then univ.filter (p i) else univ.filter (fun x => ¬p i x)
    have hrect : univ.filter (fun x => capSupport p x = s) = Fintype.piFinset allow := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl i
        by_cases hi : p i (x i) <;> simp [allow, capSupport, hi]
      · intro h
        ext i
        have hh := h i
        by_cases hi : i ∈ s <;> simp_all [allow, capSupport]
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
  rw [← sum_card_fiberwise_eq_card_filter univ J (fun x => (capSupport p x).card)]
  apply sum_congr rfl
  intro j hj
  let S := (univ : Finset (Fin m)).powersetCard j
  have hm : ((univ : Finset (Fin m → B)).filter (fun x => (capSupport p x).card = j) : Set (Fin m → B)).MapsTo
      (capSupport p) S := by
    intro x hx
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hx).2⟩
  rw [card_eq_sum_card_fiberwise hm]
  have hterm (s : Finset (Fin m)) (hs : s ∈ S) :
      ((univ.filter (fun x => (capSupport p x).card = j)).filter (fun x => capSupport p x = s)).card =
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

private def feedbackDist {m : ℕ} (x y : Fin m → (Bool × Bool × Bool)) : ℕ :=
  (univ.filter (fun i => x i ≠ y i)).card

private lemma capBlockNe : ∀ x : (Bool × Bool × Bool), (univ.filter (fun y : (Bool × Bool × Bool) => x ≠ y)).card = 7 := by
  decide +kernel

private lemma capCardNear {m : ℕ} (h : ℕ) (x : Fin m → (Bool × Bool × Bool)) :
    (univ.filter (fun y => feedbackDist x y ≤ h)).card = ∑ j ∈ range (h+1), m.choose j * 7^j := by
  classical
  let p := fun i (b : (Bool × Bool × Bool)) => x i ≠ b
  let _ : ∀ i, DecidablePred (p i) := fun i b => inferInstanceAs (Decidable (x i ≠ b))
  have hp : ∀ i, (univ.filter (p i)).card = 7 := fun i => capBlockNe (x i)
  have hn : ∀ i, (univ.filter (fun b => ¬p i b)).card = 1 := by
    intro i
    have hs : (univ.filter (fun b => ¬p i b)) = {x i} := by
      ext b
      simp [p, eq_comm]
    simp [hs]
  have heq : univ.filter (fun y => feedbackDist x y ≤ h) =
      univ.filter (fun y => (capSupport p y).card ∈ range (h+1)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_range, Nat.lt_succ_iff]
    rfl
  rw [heq, capCardSupport p 7 1 hp hn]
  simp

private lemma capCardSmall (m t : ℕ) :
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

private lemma capWeighted (m t a : ℕ) (ht : t ≤ m) (r : ℚ) (hr : 1 ≤ r) :
    ((∑ j ∈ range (t+1), m.choose j * a^j : ℕ) : ℚ) ≤
      r^t * (1 + (a : ℚ) / r)^m := by
  have hr0 : 0 < r := by linarith
  rw [add_comm 1, add_pow]
  push_cast
  simp only [one_pow, mul_one, mul_sum]
  calc
    (∑ j ∈ range (t+1), (m.choose j : ℚ) * (a : ℚ)^j) ≤
        ∑ j ∈ range (t+1), r^t * (((a : ℚ) / r)^j * (m.choose j : ℚ)) := by
      apply sum_le_sum
      intro j hj
      have hjt : j ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hi : 1 ≤ r^t / r^j := (le_div_iff₀ (by positivity)).mpr
        (by simpa using pow_le_pow_right₀ hr hjt)
      rw [div_pow]
      calc
        (m.choose j : ℚ) * (a : ℚ)^j ≤
            (r^t / r^j) * ((m.choose j : ℚ) * (a : ℚ)^j) :=
          le_mul_of_one_le_left (by positivity) hi
        _ = _ := by
          field_simp [ne_of_gt hr0]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; positivity)

private lemma capRound (m t a k b c e : ℕ) (ht : t ≤ m) (hk : k ≠ 0)
    (r : ℚ) (hr : 1 ≤ r) (htk : t*k ≤ b*m) (he : c*m ≤ e*k)
    (hb : r^b * (1 + (a : ℚ)/r)^k ≤ 2^c) :
    (∑ j ∈ range (t+1), m.choose j * a^j : ℕ) ≤ 2^e := by
  have hr0 : 0 < r := by linarith
  have hp : (r^t * (1 + (a : ℚ)/r)^m)^k ≤ ((2 : ℚ)^e)^k := by
    calc
      (r^t * (1 + (a : ℚ)/r)^m)^k = r^(t*k) * ((1+(a : ℚ)/r)^k)^m := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm m]
      _ ≤ r^(b*m) * ((1+(a : ℚ)/r)^k)^m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr htk) (by positivity)
      _ = (r^b * (1+(a : ℚ)/r)^k)^m := by simp only [mul_pow, pow_mul]
      _ ≤ ((2 : ℚ)^c)^m := pow_le_pow_left₀ (by positivity) hb m
      _ ≤ ((2 : ℚ)^e)^k := by
        rw [← pow_mul, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) he
  exact_mod_cast (capWeighted m t a ht r hr).trans
    ((pow_le_pow_iff_left₀ (by positivity) (by positivity) hk).mp hp)

private lemma cardSmallBound (m : ℕ) :
    Fintype.card {s : Finset (Fin m) // s.card ≤ 2*m/5} ≤ 2^((39*m+39)/40) := by
  rw [Fintype.card_subtype, capCardSmall]
  have h := capRound m (2*m/5) 1 40 16 39 ((39*m+39)/40) (by omega) (by decide)
    (3/2) (by norm_num) (by omega) (by omega) (by norm_num)
  simpa using h

private lemma cardBallBound (m : ℕ) (x : Fin m → (Bool × Bool × Bool)) :
    Fintype.card {y : Fin m → (Bool × Bool × Bool) // feedbackDist x y ≤ 25*m/32} ≤
      2^((119*m+39)/40) := by
  rw [Fintype.card_subtype, capCardNear]
  exact capRound m (25*m/32) 7 160 125 476 ((119*m+39)/40) (by omega) (by decide)
    2 (by norm_num) (by omega) (by omega) (by
      rw [show (476 : ℕ) = 238 + 238 by decide, pow_add]
      norm_num)

open Finset

private lemma countTrueReal {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] :
    (∑ i, ((decide (p i)).toNat : ℝ)) = ((univ.filter p).card : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases h : p i <;> simp [h]

private lemma countPartition {I : Type*} [Fintype I] [DecidableEq I] (p : I → Prop) [DecidablePred p] :
    (univ.filter p).card + (univ.filter fun i => ¬ p i).card = Fintype.card I := by
  rw [← card_union_of_disjoint (by simp [disjoint_left]), ← filter_or]
  have hu : (univ.filter fun i => p i ∨ ¬ p i) = (univ : Finset I) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, iff_true]
    exact Classical.em (p i)
  rw [hu, card_univ]

private abbrev FeedbackWord (m : Nat) := Fin m → Block
private abbrev Draws (m s : Nat) := Fin s → Fin m

private def sampleNear {m s : Nat} (z : Draws m s) (x y : FeedbackWord m) : Prop :=
  4 * feedbackDist (x ∘ z) (y ∘ z) ≤ 3 * s

private def candidatesAt {m : Nat} (z : Fin m → Fin 7) (x : FeedbackWord m)
    (heads : Fin m → Bool × Bool) : Finset (Fin m) :=
  univ.filter (fun i => labelFront (z i) (x i) = heads i)

private lemma sampleBadNear {m s : Nat} (hm : 0 < m) (x y : FeedbackWord m) :
    eventCard (fun z : Draws m s => sampleNear z x y ∧ 25*m/32 < feedbackDist x y) ≤
      (Fintype.card (Draws m s) : ℝ) * Real.exp (-(s : ℝ)/512) := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  by_cases h : 25*m/32 < feedbackDist x y
  · have hdist : (25 : ℝ) * m < 32 * feedbackDist x y := by
      exact_mod_cast (show 25*m < 32*feedbackDist x y by omega)
    let hit : Fin s → Fin m → Bool := fun _ i => decide (x i = y i)
    have mean : (∑ i : Fin s, (((univ.filter (fun a : Fin m => hit i a = true)).card : ℝ) /
        Fintype.card (Fin m))) + (1/32 : ℝ) * Fintype.card (Fin s) ≤ (s : ℝ)/4 := by
      simp only [hit, decide_eq_true_eq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hp : (univ.filter (fun i : Fin m => x i = y i)).card + feedbackDist x y = m := by
        simpa only [feedbackDist, Fintype.card_fin] using countPartition (fun i : Fin m => x i = y i)
      have hpr : ((univ.filter (fun i : Fin m => x i = y i)).card : ℝ) + feedbackDist x y = m := by
        exact_mod_cast hp
      have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
      have hb : ((univ.filter (fun i : Fin m => x i = y i)).card : ℝ) / m ≤ 7/32 := by
        rw [div_le_iff₀ hm']; linarith
      nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg s)]
    have bound := upperTail hit ((s : ℝ)/4) (1/32 : ℝ) (by norm_num) mean
    rw [← eventCard_filter] at bound
    calc
      _ ≤ eventCard (fun z : Draws m s => (s : ℝ)/4 ≤ ∑ i, ((hit i (z i)).toNat : ℝ)) := by
        apply eventCard_mono
        intro z hz
        simp only [hit, countTrueReal]
        have hz' : 4 * feedbackDist (x ∘ z) (y ∘ z) ≤ 3*s := hz.1
        have hp : (univ.filter (fun i : Fin s => x (z i) = y (z i))).card +
            feedbackDist (x ∘ z) (y ∘ z) = s := by
          simpa only [feedbackDist, Function.comp_apply, Fintype.card_fin] using
            countPartition (fun i : Fin s => x (z i) = y (z i))
        have hh : s ≤ 4 * (univ.filter (fun i : Fin s => x (z i) = y (z i))).card := by omega
        have hh' : (s : ℝ) ≤ 4 * ((univ.filter (fun i : Fin s => x (z i) = y (z i))).card : ℝ) := by exact_mod_cast hh
        linarith
      _ ≤ _ := by
        have he : -2 * (1/32 : ℝ)^2 * (s : ℝ) = -(s : ℝ)/512 := by ring
        simpa only [Fintype.card_fin, he] using bound
  · classical
    rw [eventCard_filter]
    simp only [h, and_false, filter_false, card_empty, Nat.cast_zero]
    positivity

private lemma sampleBadFar {m s : Nat} (hm : 0 < m) (x y : FeedbackWord m) :
    eventCard (fun z : Draws m s => ¬ sampleNear z x y ∧ 32 * feedbackDist x y < 23*m) ≤
      (Fintype.card (Draws m s) : ℝ) * Real.exp (-(s : ℝ)/512) := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  by_cases h : 32*feedbackDist x y < 23*m
  · have hdist : (32 : ℝ) * feedbackDist x y < 23 * m := by exact_mod_cast h
    let hit : Fin s → Fin m → Bool := fun _ i => decide (x i ≠ y i)
    have mean : (∑ i : Fin s, (((univ.filter (fun a : Fin m => hit i a = true)).card : ℝ) /
        Fintype.card (Fin m))) + (1/32 : ℝ) * Fintype.card (Fin s) ≤ 3 * (s : ℝ)/4 := by
      simp only [hit, decide_eq_true_eq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (s : ℝ) * ((feedbackDist x y : ℝ) / m) + 1/32 * s ≤ _
      have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
      have hb : (feedbackDist x y : ℝ) / m ≤ 23/32 := by rw [div_le_iff₀ hm']; linarith
      nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg s)]
    have bound := upperTail hit (3*(s : ℝ)/4) (1/32 : ℝ) (by norm_num) mean
    rw [← eventCard_filter] at bound
    calc
      _ ≤ eventCard (fun z : Draws m s => 3*(s : ℝ)/4 ≤ ∑ i, ((hit i (z i)).toNat : ℝ)) := by
        apply eventCard_mono
        intro z hz
        simp only [hit, countTrueReal]
        have hz' : 3 * s < 4 * feedbackDist (x ∘ z) (y ∘ z) :=
          Nat.lt_of_not_ge hz.1
        have hh' : 3 * (s : ℝ) < 4 * (feedbackDist (x ∘ z) (y ∘ z) : ℝ) := by exact_mod_cast hz'
        change 3 * (s : ℝ)/4 ≤ (feedbackDist (x ∘ z) (y ∘ z) : ℝ)
        linarith
      _ ≤ _ := by
        have he : -2 * (1/32 : ℝ)^2 * (s : ℝ) = -(s : ℝ)/512 := by ring
        simpa only [Fintype.card_fin, he] using bound
  · rw [eventCard_filter]
    simp only [h, and_false, filter_false, card_empty, Nat.cast_zero]
    positivity

private lemma labelOverflow {m : Nat} (x y : FeedbackWord m) :
    eventCard (fun z : Fin m → Fin 7 => 23*m ≤ 32*feedbackDist x y ∧
        2*m/5 < (candidatesAt z x (fun i => labelFront (z i) (y i))).card) ≤
      (Fintype.card (Fin m → Fin 7) : ℝ) * Real.exp (-(m : ℝ)/2000) := by
  classical
  by_cases h : 23*m ≤ 32*feedbackDist x y
  · have hdist : (23 : ℝ) * m ≤ 32 * feedbackDist x y := by exact_mod_cast h
    let hit : Fin m → Fin 7 → Bool := fun i d => decide (labelFront d (x i) = labelFront d (y i))
    have mean : (∑ i : Fin m, (((univ.filter (fun d : Fin 7 => hit i d = true)).card : ℝ) /
        Fintype.card (Fin 7))) + (9/560 : ℝ) * Fintype.card (Fin m) ≤ 2 * (m : ℝ)/5 := by
      have hsum : (∑ i : Fin m, (((univ.filter (fun d : Fin 7 => hit i d = true)).card : ℝ) /
          Fintype.card (Fin 7))) = m - (6/7 : ℝ) * feedbackDist x y := by
        simp only [hit, decide_eq_true_eq, labelCount, Fintype.card_fin]
        calc
          _ = ∑ i : Fin m, (1 - (6/7 : ℝ) * (if x i ≠ y i then 1 else 0)) := by
            apply sum_congr rfl
            intro i _
            by_cases hi : x i = y i <;> norm_num [hi]
          _ = _ := by
            have hcount : (∑ i : Fin m, (if x i ≠ y i then (1 : ℝ) else 0)) = feedbackDist x y := by
              unfold feedbackDist
              rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
              apply sum_congr rfl
              intro i _
              split <;> simp_all
            rw [sum_sub_distrib, ← mul_sum, hcount, sum_const, card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
      rw [hsum, Fintype.card_fin]
      linarith
    have bound := upperTail hit (2*(m : ℝ)/5) (9/560 : ℝ) (by norm_num) mean
    rw [← eventCard_filter] at bound
    calc
      _ ≤ eventCard (fun z : Fin m → Fin 7 => 2*(m : ℝ)/5 ≤ ∑ i, ((hit i (z i)).toNat : ℝ)) := by
        apply eventCard_mono
        intro z hz
        simp only [hit, countTrueReal]
        change 2*(m : ℝ)/5 ≤ ((candidatesAt z x (fun i => labelFront (z i) (y i))).card : ℝ)
        have hn : 2*m < 5*(candidatesAt z x (fun i => labelFront (z i) (y i))).card := by omega
        have hr : 2*(m : ℝ) < 5*((candidatesAt z x (fun i => labelFront (z i) (y i))).card : ℝ) := by exact_mod_cast hn
        linarith
      _ ≤ _ := by
        have he : -2 * (9/560 : ℝ)^2 * (m : ℝ) ≤ -(m : ℝ)/2000 := by
          nlinarith [show 0 ≤ (m : ℝ) from Nat.cast_nonneg m]
        refine (by simpa only [Fintype.card_fin] using bound :
          _ ≤ (Fintype.card (Fin m → Fin 7) : ℝ) * Real.exp (-2 * (9/560 : ℝ)^2 * (m : ℝ))).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Nat.cast_nonneg _)
  · rw [eventCard_filter]
    simp only [h, false_and, filter_false, card_empty, Nat.cast_zero]
    positivity

open Finset

private lemma eventCard_fst_le {A B : Type*} [Fintype A] [Fintype B] (p : A → Prop)
    (r : ℝ) (h : eventCard p ≤ Fintype.card A * r) :
    eventCard (fun z : A × B => p z.1) ≤ Fintype.card (A × B) * r := by
  rw [eventCard_fst, Fintype.card_prod, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans_eq (by ring)

private lemma eventCard_snd_le {A B : Type*} [Fintype A] [Fintype B] (p : B → Prop)
    (r : ℝ) (h : eventCard p ≤ Fintype.card B * r) :
    eventCard (fun z : A × B => p z.2) ≤ Fintype.card (A × B) * r := by
  rw [eventCard_snd, Fintype.card_prod, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (by ring)

private lemma labelParity {m : Nat} (z : Fin m → Fin 7) (x y : FeedbackWord m) :
    parityOn univ (fun i => decide (x i = y i)) =
      xor (parityOn (candidatesAt z x (fun i => labelFront (z i) (y i)))
        (fun i => !(labelBack (z i) (x i))))
        (parityOn (candidatesAt z x (fun i => labelFront (z i) (y i)))
        (fun i => labelBack (z i) (y i))) := by
  rw [← parity_xor]
  unfold candidatesAt parityOn
  rw [sum_filter]
  congr 2
  apply sum_congr rfl
  intro i _
  dsimp only
  rw [labelEq (z i) (x i) (y i)]
  split <;> simp_all

private def feedbackBall {m : Nat} (x : FeedbackWord m) : Finset (FeedbackWord m) :=
  univ.filter (fun y => feedbackDist x y ≤ 25 * m / 32)

private lemma feedbackBall_size {m : Nat} (x : FeedbackWord m) :
    (feedbackBall x).card ≤ 2^((119*m+39)/40) := by
  unfold feedbackBall
  rw [← Fintype.card_subtype]
  exact cardBallBound m x

private abbrev FeedbackSmall (m : Nat) := {t : Finset (Fin m) // t.card ≤ 2*m/5}
private abbrev FeedbackFront (m : Nat) := Fin m → Bool × Bool

private lemma frontCapacity (m : Nat) : Fintype.card (FeedbackFront m) ≤ 2^(2*m) := by
  rw [pow_mul]
  simp [FeedbackFront]

private lemma wordCapacity (s : Nat) : Fintype.card (FeedbackWord s) ≤ 2^(3*s) := by
  rw [pow_mul]
  norm_num [FeedbackWord, Block]

private lemma smallCapacity (m : Nat) : Fintype.card (FeedbackSmall m × Bool) ≤ 2^((39*m+39)/40+1) := by
  rw [Fintype.card_prod, Fintype.card_bool, pow_succ]
  exact Nat.mul_le_mul_right 2 (cardSmallBound m)

private lemma boolCapacity : Fintype.card Bool ≤ 2^1 := by decide

set_option maxHeartbeats 1500000 in
private lemma feedbackProtocol (m s slack : Nat) (hm : 0 < m) (_hs : 0 < s)
    (φ ψ : FeedbackWord m → Bool) :
    publicThree univ (modelTruth φ ψ) (3*s+2+slack+(119*m+39)/40)
      (2*Real.exp (-(s : ℝ)/512) + 1/(2 : ℝ)^slack + Real.exp (-(m : ℝ)/2000)) := by
  classical
  let n := (119*m+39)/40
  let c := (39*m+39)/40
  let W := FeedbackWord m
  let H := W → Fin (2^(n+slack))
  let P := Fin m → Fin 7
  let S := Draws m s × (H × P)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (FeedbackSmall m) := ⟨⟨∅, by simp⟩⟩
  let mb : Bool → Nat := fun b => if b then 2*m else n+slack
  let lb : Bool → Nat := fun b => if b then c+1 else 1
  let send (z : S) (x : W) : Fin (2^(3*s)) := encode (wordCapacity s) (x ∘ z.1)
  let reply (z : S) (a : Fin (2^(3*s))) (y : W) : Σ b : Bool, Fin (2^(mb b)) :=
    if 4 * feedbackDist (recover (wordCapacity s) a) (y ∘ z.1) ≤ 3*s then
      ⟨false, z.2.1 y⟩
    else ⟨true, encode (frontCapacity m) (fun i => labelFront (z.2.2 i) (y i))⟩
  let last : (b : Bool) → S → W → Fin (2^(mb b)) → Fin (2^(lb b)) := fun b =>
    match b with
    | false => fun z x msg => encode boolCapacity (xor (φ x)
        (parityOn univ (fun i => decide (x i = decodeWord feedbackBall z.2.1 x msg i))))
    | true => fun z x msg =>
        let t := candidatesAt z.2.2 x (recover (frontCapacity m) msg)
        if ht : t.card ≤ 2*m/5 then
          encode (smallCapacity m) (⟨t, ht⟩, xor (φ x)
            (parityOn t (fun i => !(labelBack (z.2.2 i) (x i)))))
        else encode (smallCapacity m) (⟨∅, by simp⟩, false)
  let read : (b : Bool) → S → W → Fin (2^(3*s)) → Fin (2^(lb b)) → Bool := fun b =>
    match b with
    | false => fun _ y _ msg => xor (recover boolCapacity msg) (ψ y)
    | true => fun z y _ msg =>
        let pack := recover (smallCapacity m) msg
        xor (xor pack.2 (ψ y)) (parityOn pack.1.val (fun i => labelBack (z.2.2 i) (y i)))
  let evaluate (z : S) (x y : W) (a : Fin (2^(3*s))) (msg : Σ b : Bool, Fin (2^(mb b))) :=
    read msg.1 z y a (last msg.1 z x msg.2)
  let predict (z : S) (x y : W) : Bool :=
    evaluate z x y (send z x) (reply z (send z x) y)
  have near_ok (z : S) (x y : W) (hn : sampleNear z.1 x y)
      (hd : decodeWord feedbackBall z.2.1 x (z.2.1 y) = y) :
      predict z x y = modelTruth φ ψ x y := by
    have hn' : 4 * feedbackDist (x ∘ z.1) (y ∘ z.1) ≤ 3*s := hn
    have hr : reply z (send z x) y = ⟨false, z.2.1 y⟩ := by
      dsimp only [reply, send]
      rw [recover_encode, ite_eq_left hn']
    calc
      _ = evaluate z x y (send z x) ⟨false, z.2.1 y⟩ :=
        congrArg (evaluate z x y (send z x)) hr
      _ = _ := by
        simp only [evaluate, last, read, recover_encode, hd, modelTruth,
          Bool.xor_assoc, Bool.xor_left_comm]
        exact congrArg (xor (φ x)) (Bool.xor_comm _ _)
  have far_ok (z : S) (x y : W) (hn : ¬ sampleNear z.1 x y)
      (hd : (candidatesAt z.2.2 x (fun i => labelFront (z.2.2 i) (y i))).card ≤ 2*m/5) :
      predict z x y = modelTruth φ ψ x y := by
    have hn' : ¬ 4 * feedbackDist (x ∘ z.1) (y ∘ z.1) ≤ 3*s := hn
    have hr : reply z (send z x) y = ⟨true, encode (frontCapacity m)
        (fun i => labelFront (z.2.2 i) (y i))⟩ := by
      dsimp only [reply, send]
      rw [recover_encode, ite_eq_right hn']
    calc
      _ = evaluate z x y (send z x) ⟨true, encode (frontCapacity m)
          (fun i => labelFront (z.2.2 i) (y i))⟩ :=
        congrArg (evaluate z x y (send z x)) hr
      _ = _ := by
        simp only [evaluate, last, read, recover_encode, dite_eq_left hd,
          modelTruth, labelParity z.2.2 x y, Bool.xor_assoc, Bool.xor_left_comm]
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, 3*s, mb, lb, (fun z => send (e z)), (fun z => reply (e z)),
    (fun b z => last b (e z)), (fun b z => read b (e z)), Fintype.card_pos, ?_, ?_⟩
  · intro b
    cases b <;> dsimp [mb, lb, n, c] <;> omega
  · rintro ⟨x,y⟩ _
    let bad₁ (z : Draws m s) := sampleNear z x y ∧ 25*m/32 < feedbackDist x y
    let bad₂ (z : Draws m s) := ¬ sampleNear z x y ∧ 32*feedbackDist x y < 23*m
    let bad₃ (h : H) := y ∈ feedbackBall x ∧ decodeWord feedbackBall h x (h y) ≠ y
    let bad₄ (z : P) := 23*m ≤ 32*feedbackDist x y ∧
        2*m/5 < (candidatesAt z x (fun i => labelFront (z i) (y i))).card
    let r := Real.exp (-(s : ℝ)/512)
    let t := 1 / (2 : ℝ)^slack
    let u := Real.exp (-(m : ℝ)/2000)
    have b₁ : eventCard (fun z : S => bad₁ z.1) ≤ Fintype.card S * r :=
      eventCard_fst_le bad₁ r (sampleBadNear hm x y)
    have b₂ : eventCard (fun z : S => bad₂ z.1) ≤ Fintype.card S * r :=
      eventCard_fst_le bad₂ r (sampleBadFar hm x y)
    have b₃ : eventCard (fun z : S => bad₃ z.2.1) ≤ Fintype.card S * t := by
      apply eventCard_snd_le (fun z : H × P => bad₃ z.1) t
      apply eventCard_fst_le bad₃ t
      by_cases hy : y ∈ feedbackBall x
      · have h := hashFailure feedbackBall x y n slack hy (feedbackBall_size x)
        rw [← eventCard_filter] at h
        simpa only [bad₃, hy, true_and, t, mul_one_div] using h
      · classical
        rw [eventCard_filter]
        simp only [bad₃, hy, false_and, filter_false, card_empty, Nat.cast_zero]
        dsimp only [t]
        positivity
    have b₄ : eventCard (fun z : S => bad₄ z.2.2) ≤ Fintype.card S * u :=
      eventCard_snd_le (fun z : H × P => bad₄ z.2) u (eventCard_snd_le bad₄ u (labelOverflow x y))
    have cover (z : S) (hf : predict z x y ≠ modelTruth φ ψ x y) :
        (bad₁ z.1 ∨ bad₂ z.1) ∨ (bad₃ z.2.1 ∨ bad₄ z.2.2) := by
      by_cases hn : sampleNear z.1 x y
      · by_cases hd : y ∈ feedbackBall x
        · exact Or.inr (Or.inl ⟨hd, fun h => hf (near_ok z x y hn h)⟩)
        · exact Or.inl (Or.inl ⟨hn, Nat.lt_of_not_ge ((fun he => hd (mem_filter.mpr ⟨mem_univ _, he⟩)))⟩)
      · by_cases hd : 23*m ≤ 32*feedbackDist x y
        · apply Or.inr ∘ Or.inr
          exact ⟨hd, Nat.lt_of_not_ge (fun h => hf (far_ok z x y hn h))⟩
        · exact Or.inl (Or.inr ⟨hn, Nat.lt_of_not_ge hd⟩)
    change ((univ.filter (fun z : Fin (Fintype.card S) => predict (e z) x y ≠ modelTruth φ ψ x y)).card : ℝ) ≤
      (Fintype.card S : ℝ) * (2*r+t+u)
    rw [← eventCard_filter, eventCard_congr e (fun z : S => predict z x y ≠ modelTruth φ ψ x y)]
    apply (eventCard_mono cover).trans
    apply (eventCard_union (fun z : S => bad₁ z.1 ∨ bad₂ z.1)
      (fun z : S => bad₃ z.2.1 ∨ bad₄ z.2.2)).trans
    calc
      _ ≤ (eventCard (fun z : S => bad₁ z.1) + eventCard (fun z : S => bad₂ z.1)) +
          (eventCard (fun z : S => bad₃ z.2.1) + eventCard (fun z : S => bad₄ z.2.2)) := by
        exact add_le_add (eventCard_union _ _) (eventCard_union _ _)
      _ ≤ _ := by nlinarith only [b₁, b₂, b₃, b₄]

end PEqualNP.Outside.L_meta_29923_aux

open PEqualNP.Outside.L_meta_29923_aux

theorem PEqualNP.Outside.L_meta_29923 :
∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  let three := fun (budget : Nat) (err : ℝ) =>
    ∃ (seeds firstBits : Nat) (middleBits lastBits : Bool → Nat)
      (first : Fin seeds → K → Fin (2^firstBits))
      (middle : Fin seeds → Fin (2^firstBits) → K →
        (Σ b : Bool, Fin (2^(middleBits b))))
      (last : (b : Bool) → Fin seeds → K → Fin (2^(middleBits b)) → Fin (2^(lastBits b)))
      (read : (b : Bool) → Fin seeds → K → Fin (2^firstBits) → Fin (2^(lastBits b)) → Bool),
      0 < seeds ∧ (∀ b, firstBits+1+middleBits b+lastBits b ≤ budget) ∧
      ∀ p ∈ pairs,
        let predicts := fun z : Fin seeds =>
          let a := first z p.1
          let msg := middle z a p.2
          read msg.1 z p.2 a (last msg.1 z p.1 msg.2)
        (((Finset.univ : Finset (Fin seeds)).filter
          (fun z => predicts z ≠ truth p.1 p.2)).card : ℝ) ≤ (seeds : ℝ)*err
  ∀ (samples slack : Nat), 0 < samples →
    three (3*samples+2+slack+(119*m+39)/40)
      (2*Real.exp (-(samples : ℝ)/512) + 1/(2 : ℝ)^slack + Real.exp (-(m : ℝ)/2000)) := by
  classical
  intro k hk0 constant rot step state injected bit m starts hm hinj good row ref hgood pin hpin _ K fiber
    pairs truth three samples slack hs
  let windows : Fin m × Fin 12 → Fin k := fun ij =>
    ⟨(starts ij.1 + ij.2.val) % k, Nat.mod_lt _ hk0⟩
  have hwin : Function.Injective windows := by
    intro a b h
    exact hinj (congrArg Fin.val h)
  have hk : 12 ≤ k := by
    have hc := Fintype.card_le_of_injective windows hwin
    simp [Fintype.card_prod] at hc
    omega
  let left := fun (q : K) (i : Fin m) => windowShare constant row ref q (starts i)
  let right := fun (q : K) (i : Fin m) => bxor (windowShare constant row ref q (starts i))
    (windowShift constant row ref (starts i))
  let flag := fun i => windowFlag constant row ref (starts i)
  let base := fun i => xor (!affine (flag i) (point (flag i)))
    (injectedFn k constant 2 ref.val (starts i+5))
  let φ := fun x : Fin m → Block => xor (parityOn Finset.univ base)
    (parityOn Finset.univ (fun i => affine (flag i) (x i)))
  let ψ := fun y : Fin m → Block => parityOn Finset.univ (fun i => affine (flag i) (y i))
  have hpinShare (q : K) (hq : q ∈ fiber) (i : Fin m) (j : ℕ) (hj : j < 9) :
      shareBit k constant row ref q (starts i+j) = false := by
    obtain ⟨z, hz, hzval⟩ := hpin i ⟨j, hj⟩
    have hmem : ∀ z ∈ pin, bitFn k constant row.val 0 q.val z.val =
        bitFn k constant row.val 0 ref.val z.val := (Finset.mem_filter.mp hq).2
    have hv := (xor_false_iff _ _).2 (hmem z hz)
    change shareBit k constant row ref q z.val = false at hv
    rwa [hzval, shareBit_mod hk] at hv
  have hTruth (p : K × K) (hp : p ∈ pairs) : truth p.1 p.2 = modelTruth φ ψ (left p.1) (right p.2) := by
    have hp' : p.1 ∈ fiber ∧ p.2 ∈ fiber := Finset.mem_product.mp hp
    have hrow (i : Fin m) :
        bitFn k constant row.val 2 (combine ref p.1 p.2).val (starts i+5) =
          xor (xor (xor (base i) (affine (flag i) (left p.1 i)))
            (affine (flag i) (right p.2 i))) (decide (left p.1 i = right p.2 i)) :=
      guarded_window hk constant row ref p.1 p.2 (starts i) (hpinShare p.1 hp'.1 i)
        (hpinShare p.2 hp'.2 i) (hgood i).1 (hgood i).2.2.1 (hgood i).2.2.2
    change parityOn Finset.univ (fun i => bitFn k constant row.val 2 (combine ref p.1 p.2).val (starts i+5)) = _
    rw [funext hrow]
    simp only [modelTruth, parity_xor, φ, ψ]
  exact threePullback left right hTruth (feedbackProtocol m samples slack hm hs φ ψ)
