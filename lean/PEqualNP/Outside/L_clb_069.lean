import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_069_aux

abbrev Word (n : ℕ) := Fin n → Bool
abbrev State (d : ℕ) := Word (d + 1)
abbrev Payload (d : ℕ) := Word d
abbrev Test (w : ℕ) := Fin w → Word (w + 1) → Bool

def splice {w : ℕ} (a b : Word w) (i : Fin w) : Word (w + 1) := fun j =>
  if h : i.val + j.val < w then a ⟨i.val + j.val, h⟩ else
    b ⟨i.val + j.val - w, by have := i.isLt; have := j.isLt; omega⟩

def SweepOk {w : ℕ} (test : Test w) (a b : Word w) : Prop :=
  ∀ i : Fin w, test i (splice a b i) = true

lemma splice_head {w : ℕ} (a b : Word w) (i : Fin w) : splice a b i 0 = a i := by
  simp [splice, i.isLt]

lemma splice_last {w : ℕ} (a b : Word w) (i : Fin w) :
    splice a b i (Fin.last w) = b i := by
  simp [splice, show ¬ (i.val + w < w) by omega]

def tagOffset {d : ℕ} (i : Fin (d + 1)) : Fin ((d + 1) + 1) :=
  ⟨d + 1 - i.val, by omega⟩

lemma splice_tag {d : ℕ} (a b : State d) (i : Fin (d + 1)) :
    splice a b i (tagOffset i) = b 0 := by
  have e : i.val + (d + 1 - i.val) = d + 1 := by have := i.isLt; omega
  simp [splice, tagOffset, e]

def payload {d : ℕ} (a : State d) : Payload d := fun j => a j.succ
def diff {d : ℕ} (a h : Payload d) : Payload d := fun j => xor (a j) (h j)
def mask {d : ℕ} (h : Payload d) (a : State d) : State d :=
  Fin.cases (a 0) (fun j => xor (a j.succ) (a 0 && h j))
def rise {d : ℕ} (a : State d) : State d := Fin.cases true (payload a)
def switched {d : ℕ} (h : Payload d) (a : State d) : State d :=
  Fin.cases true (diff (payload a) h)
def mkFalse {d : ℕ} (u : Payload d) : State d := Fin.cases false u
def mkTrue {d : ℕ} (v : Payload d) : State d := Fin.cases true v

lemma payload_switched {d : ℕ} (h : Payload d) (a : State d) :
    payload (switched h a) = diff (payload a) h := by
  funext j; rfl

lemma payload_mkFalse {d : ℕ} (u : Payload d) : payload (mkFalse u) = u := by
  funext j; rfl

lemma payload_mkTrue {d : ℕ} (v : Payload d) : payload (mkTrue v) = v := by
  funext j; rfl

lemma diff_self_right {d : ℕ} (a h : Payload d) : diff (diff a h) h = a := by
  funext j
  simp [diff]

def maskTest {d : ℕ} (h : Payload d) : Test (d + 1) :=
  Fin.cases (fun p => p (Fin.last (d + 1)) == p 0) (fun j p =>
    p (Fin.last (d + 1)) == xor (p 0) (p (tagOffset j.succ) && h j))

lemma mask_ok {d : ℕ} (h : Payload d) (a b : State d) :
    SweepOk (maskTest h) a b ↔ b = mask h a := by
  constructor
  · intro ok
    have tag : b 0 = a 0 := by
      simpa [maskTest, splice_last, splice_head] using ok 0
    funext i
    refine Fin.cases (by simpa [mask] using tag) ?_ i
    intro j
    simpa [maskTest, splice_last, splice_head, splice_tag, mask, tag] using ok j.succ
  · rintro rfl i
    refine Fin.cases ?_ ?_ i
    · simp [maskTest, splice_last, splice_head, mask]
    · intro j
      simp [maskTest, splice_last, splice_head, splice_tag, mask]

def toggleTest {d : ℕ} (h : Payload d) (A : Payload d → Payload d → Bool) : Test (d + 1) :=
  Fin.cases (fun p =>
    if p (Fin.last (d + 1)) == p 0 then true else
    if p 0 then false else A (fun j => p j.succ.castSucc) (diff (fun j => p j.succ.castSucc) h))
    (fun _ p => p (Fin.last (d + 1)) == p 0)

lemma splice_payload {d : ℕ} (a b : State d) (j : Fin d) :
    splice a b 0 j.succ.castSucc = a j.succ := by
  simp [splice]
  rfl

lemma toggle_ok {d : ℕ} (h : Payload d) (A : Payload d → Payload d → Bool) (a b : State d) :
    SweepOk (toggleTest h A) a b ↔
      b = a ∨ (a 0 = false ∧ A (payload a) (diff (payload a) h) = true ∧ b = rise a) := by
  have at0 : toggleTest h A 0 (splice a b 0) =
      (if b 0 == a 0 then true else if a 0 then false else A (payload a) (diff (payload a) h)) := by
    simp only [toggleTest, Fin.cases_zero, splice_last, splice_head, splice_payload]
    rfl
  have at1 (j : Fin d) : toggleTest h A j.succ (splice a b j.succ) = (b j.succ == a j.succ) := by
    simp [toggleTest, splice_last, splice_head]
  constructor
  · intro ok
    have pl (j : Fin d) : b j.succ = a j.succ := by simpa [at1] using ok j.succ
    have hd := ok 0
    rw [at0] at hd
    by_cases he : b 0 = a 0
    · exact Or.inl (funext (fun i => Fin.cases he pl i))
    · have e : a 0 = false ∧ b 0 = true ∧ A (payload a) (diff (payload a) h) = true := by
        cases ha : a 0 <;> cases hb : b 0 <;> simp_all
      exact Or.inr ⟨e.1, e.2.2, funext (fun i => Fin.cases (by simpa [rise] using e.2.1)
        (fun j => by simpa [rise, payload] using pl j) i)⟩
  · rintro (rfl | ⟨ha, ht, rfl⟩) i
    · exact Fin.cases (by simp [at0]) (fun j => by simp [at1]) i
    · exact Fin.cases (by simp [at0, rise, ha, ht]) (fun j => by simp [at1, rise, payload]) i

lemma mask_twice {d : ℕ} (h : Payload d) (a : State d) : mask h (mask h a) = a := by
  funext i
  refine Fin.cases (by simp [mask]) ?_ i
  intro j
  simp [mask]

lemma mask_off {d : ℕ} (h : Payload d) {a : State d} (ha : a 0 = false) : mask h a = a := by
  funext i
  refine Fin.cases (by simp [mask]) (fun j => by simp [mask, ha]) i

lemma mask_rise {d : ℕ} (a : State d) (h : Payload d) : mask h (rise a) = switched h a := by
  funext i
  refine Fin.cases (by simp [mask, rise, switched])
    (fun j => by simp [mask, rise, switched, diff, payload]) i

lemma mask_mkTrue {d : ℕ} (h v : Payload d) : mask h (mkTrue v) = mkTrue (diff v h) := by
  funext i
  refine Fin.cases (by simp [mask, mkTrue]) (fun j => by simp [mask, mkTrue, diff]) i

def tests {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) : List (Test (d + 1)) :=
  hs.flatMap (fun h => [maskTest h, toggleTest h A, maskTest h])

lemma len_tests {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) :
    (tests A hs).length = 3 * hs.length := by
  induction hs with
  | nil => simp [tests]
  | cons h hs ih =>
    change (tests A hs).length + 3 = 3 * (hs.length + 1)
    rw [ih]
    omega

noncomputable def keyList (d : ℕ) : List (Payload d) :=
  (List.finRange (Fintype.card (Payload d))).map (Fintype.equivFin (Payload d)).symm

lemma keylen (d : ℕ) : (keyList d).length = 2 ^ d := by
  simp [keyList]

lemma keyAll {d : ℕ} (h : Payload d) : h ∈ keyList d := by
  apply List.mem_map.mpr
  exact ⟨Fintype.equivFin _ h, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

def Reach {w : ℕ} : List (Test w) → Word w → Word w → Prop
  | [], a, b => a = b
  | t :: ts, a, b => ∃ y, SweepOk t a y ∧ Reach ts y b

lemma reach_append {w : ℕ} (ts1 ts2 : List (Test w)) (a c : Word w) :
    Reach (ts1 ++ ts2) a c ↔ ∃ b, Reach ts1 a b ∧ Reach ts2 b c := by
  induction ts1 generalizing a with
  | nil => simp [Reach]
  | cons t ts1 ih =>
    simp only [List.cons_append, Reach]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨b, h1, h2⟩ := (ih y).mp h
      exact ⟨b, ⟨y, hy, h1⟩, h2⟩
    · rintro ⟨b, ⟨y, hy, h1⟩, h2⟩
      exact ⟨y, hy, (ih y).mpr ⟨b, h1, h2⟩⟩

lemma reach_block {d : ℕ} (A : Payload d → Payload d → Bool) (h : Payload d) (a b : State d) :
    Reach [maskTest h, toggleTest h A, maskTest h] a b ↔
      b = a ∨ (a 0 = false ∧ A (payload a) (diff (payload a) h) = true ∧ b = switched h a) := by
  simp only [Reach, mask_ok, toggle_ok, exists_eq_left]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with rfl | ⟨ha, hA, rfl⟩
    · exact Or.inl (mask_twice h a)
    · have ha0 : a 0 = false := by simpa [mask] using ha
      rw [mask_off h ha0] at hA ⊢
      exact Or.inr ⟨ha0, hA, mask_rise a h⟩
  · rintro (hba | ⟨ha, hA, rfl⟩)
    · rw [hba]
      exact ⟨mask h a, Or.inl rfl, mask_twice h a⟩
    · refine ⟨rise a, Or.inr ⟨?_, ?_, ?_⟩, mask_rise a h⟩
      · simpa [mask] using ha
      · rwa [mask_off h ha]
      · rw [mask_off h ha]

lemma reach_tests {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (a b : State d) :
    Reach (tests A hs) a b ↔
      b = a ∨ (a 0 = false ∧ b 0 = true ∧ A (payload a) (payload b) = true ∧
        diff (payload a) (payload b) ∈ hs) := by
  induction hs generalizing a with
  | nil =>
    simp only [tests, List.flatMap_nil, Reach, List.not_mem_nil, and_false, or_false]
    exact eq_comm
  | cons h hs ih =>
    have hcons : tests A (h :: hs) = [maskTest h, toggleTest h A, maskTest h] ++ tests A hs := rfl
    rw [hcons, reach_append]
    constructor
    · rintro ⟨y, hy, hys⟩
      rw [reach_block] at hy
      rw [ih] at hys
      rcases hy with rfl | ⟨ha, hA, rfl⟩
      · rcases hys with rfl | ⟨ha, hb, hA, hmem⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨ha, hb, hA, List.mem_cons_of_mem h hmem⟩
      · rcases hys with rfl | ⟨hs0, _, _, _⟩
        · refine Or.inr ⟨ha, rfl, ?_, ?_⟩
          · rw [payload_switched]; exact hA
          · have : diff (payload a) (payload (switched h a)) = h := by
              rw [payload_switched]
              funext j
              simp [diff]
            rw [this]
            exact List.mem_cons_self
        · simp [switched] at hs0
    · rintro (hba | ⟨ha, hb, hA, hmem⟩)
      · subst hba
        exact ⟨b, (reach_block A h b b).mpr (Or.inl rfl), (ih b).mpr (Or.inl rfl)⟩
      · rcases List.mem_cons.mp hmem with rfl | hmem'
        · have heq : switched (diff (payload a) (payload b)) a = b := by
            funext i
            refine Fin.cases (by simpa [switched] using hb.symm) ?_ i
            intro j
            simp [switched, payload, diff]
          have hd : diff (payload a) (diff (payload a) (payload b)) = payload b := by
            funext j; simp [diff]
          refine ⟨b, (reach_block A _ a b).mpr (Or.inr ⟨ha, ?_, heq.symm⟩), (ih b).mpr (Or.inl rfl)⟩
          rwa [hd]
        · exact ⟨a, (reach_block A h a a).mpr (Or.inl rfl),
            (ih a).mpr (Or.inr ⟨ha, hb, hA, hmem'⟩)⟩

lemma reach_keyList {d : ℕ} (A : Payload d → Payload d → Bool) (a b : State d) :
    Reach (tests A (keyList d)) a b ↔
      b = a ∨ (a 0 = false ∧ b 0 = true ∧ A (payload a) (payload b) = true) := by
  rw [reach_tests]
  simp [keyAll]

lemma tests_getElem_0 {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (m : ℕ) (hm : m < hs.length) :
    (tests A hs)[3 * m]'(by rw [len_tests]; omega) = maskTest (hs[m]'hm) := by
  induction hs generalizing m with
  | nil => simp at hm
  | cons h hs ih =>
    cases m with
    | zero => rfl
    | succ m =>
      have hm' : m < hs.length := by simpa using hm
      have h1 : 3 * (m + 1) = 3 * m + 3 := by omega
      simpa [tests, h1] using ih m hm'

lemma tests_getElem_1 {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (m : ℕ) (hm : m < hs.length) :
    (tests A hs)[3 * m + 1]'(by rw [len_tests]; omega) = toggleTest (hs[m]'hm) A := by
  induction hs generalizing m with
  | nil => simp at hm
  | cons h hs ih =>
    cases m with
    | zero => rfl
    | succ m =>
      have hm' : m < hs.length := by simpa using hm
      have h1 : 3 * (m + 1) + 1 = (3 * m + 1) + 3 := by omega
      simpa [tests, h1] using ih m hm'

lemma tests_getElem_2 {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (m : ℕ) (hm : m < hs.length) :
    (tests A hs)[3 * m + 2]'(by rw [len_tests]; omega) = maskTest (hs[m]'hm) := by
  induction hs generalizing m with
  | nil => simp at hm
  | cons h hs ih =>
    cases m with
    | zero => rfl
    | succ m =>
      have hm' : m < hs.length := by simpa using hm
      have h1 : 3 * (m + 1) + 2 = (3 * m + 2) + 3 := by omega
      simpa [tests, h1] using ih m hm'

lemma tests_take_3m {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (m : ℕ) :
    (tests A hs).take (3 * m) = tests A (hs.take m) := by
  induction hs generalizing m with
  | nil => simp [tests]
  | cons h hs ih =>
    cases m with
    | zero => simp [tests]
    | succ m =>
      have h1 : 3 * (m + 1) = 3 * m + 3 := by omega
      change (maskTest h :: toggleTest h A :: maskTest h :: tests A hs).take (3 * (m + 1)) =
        maskTest h :: toggleTest h A :: maskTest h :: tests A (hs.take m)
      rw [h1]
      simp only [List.take_succ_cons]
      rw [ih m]

lemma reach_take_3m {d : ℕ} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (m : ℕ) (u : Payload d) (s : State d)
    (hreach : Reach ((tests A hs).take (3 * m)) (mkFalse u) s) :
    s = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ s = mkTrue v := by
  rw [tests_take_3m, reach_tests] at hreach
  rcases hreach with rfl | ⟨_, hb, hA, _⟩
  · exact Or.inl rfl
  · rw [payload_mkFalse] at hA
    refine Or.inr ⟨payload s, hA, ?_⟩
    funext i
    refine Fin.cases (by simpa [mkTrue] using hb) (fun j => rfl) i

def copyPat {w : ℕ} (pat : Word (w + 1)) : Bool :=
  pat (Fin.last w) == pat 0

def rotState {d : ℕ} (shift : ℕ) (s : State d) : State d :=
  fun l => s ⟨(shift + l.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

def unrotState {d : ℕ} (shift : ℕ) (s : State d) : State d :=
  fun l => s ⟨(d + 1 - shift % (d + 1) + l.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

lemma rot_unrot {d : ℕ} (shift : ℕ) (s : State d) :
    rotState shift (unrotState shift s) = s := by
  funext l
  simp only [rotState, unrotState]
  congr 1
  apply Fin.ext
  have hlt : shift % (d + 1) < d + 1 := Nat.mod_lt shift (Nat.succ_pos d)
  have h1 : d + 1 - shift % (d + 1) + (shift + l.val) % (d + 1) ≡
      d + 1 - shift % (d + 1) + (shift + l.val) [MOD (d + 1)] :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
  have h2 : d + 1 - shift % (d + 1) + (shift + l.val) = (1 + shift / (d + 1)) * (d + 1) + l.val := by
    have hdiv := Nat.div_add_mod shift (d + 1)
    have hmul : (1 + shift / (d + 1)) * (d + 1) = (d + 1) + (d + 1) * (shift / (d + 1)) := by ring
    omega
  change (d + 1 - shift % (d + 1) + (shift + l.val) % (d + 1)) % (d + 1) = l.val
  rw [h1, h2, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt l.isLt]

lemma unrot_rot {d : ℕ} (shift : ℕ) (s : State d) :
    unrotState shift (rotState shift s) = s := by
  funext l
  simp only [rotState, unrotState]
  congr 1
  apply Fin.ext
  have hlt : shift % (d + 1) < d + 1 := Nat.mod_lt shift (Nat.succ_pos d)
  have h1 : shift + (d + 1 - shift % (d + 1) + l.val) % (d + 1) ≡
      shift + (d + 1 - shift % (d + 1) + l.val) [MOD (d + 1)] :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
  have h2 : shift + (d + 1 - shift % (d + 1) + l.val) = (1 + shift / (d + 1)) * (d + 1) + l.val := by
    have hdiv := Nat.div_add_mod shift (d + 1)
    have hmul : (1 + shift / (d + 1)) * (d + 1) = (d + 1) + (d + 1) * (shift / (d + 1)) := by ring
    omega
  change (shift + (d + 1 - shift % (d + 1) + l.val) % (d + 1)) % (d + 1) = l.val
  rw [h1, h2, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt l.isLt]

def partialMask {d : ℕ} (k : Payload d) (r : ℕ) (hr : r < d + 1) (s : State d) : State d :=
  fun j => if h : r + j.val < d + 1 then s ⟨r + j.val, h⟩
    else mask k s ⟨r + j.val - (d + 1), by have := j.isLt; omega⟩

def partialStay {d : ℕ} (r : ℕ) (hr : r < d + 1) (s : State d) : State d :=
  fun j => if h : r + j.val < d + 1 then s ⟨r + j.val, h⟩
    else s ⟨r + j.val - (d + 1), by have := j.isLt; omega⟩

noncomputable def buildP (d padding : ℕ) (A : Payload d → Payload d → Bool) :
    Fin (padding + 3 * (d + 1) * 2 ^ d) → Word (d + 1 + 1) → Bool :=
  let ts := tests A (keyList d)
  let hlen : ts.length = 3 * 2 ^ d := by rw [len_tests, keylen]
  fun i pat =>
    let base : Bool :=
      if h : i.val < padding then copyPat pat
      else
        let off := i.val - padding
        let t := off / (d + 1)
        let r := off % (d + 1)
        have ht : t < ts.length := by
          rw [hlen]
          exact (Nat.div_lt_iff_lt_mul (show 0 < d + 1 by omega)).mpr (by
            have hi := i.isLt
            have hmul : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
            dsimp only [off]
            omega)
        (ts[t]'ht) ⟨r, Nat.mod_lt _ (show 0 < d + 1 by omega)⟩ pat
    if i.val = 0 then !(pat ⟨padding % (d + 1), by have := Nat.mod_lt padding (show 0 < d + 1 by omega); omega⟩) && base
    else base

lemma buildP_word_prefix (d padding : ℕ) (A : Payload d → Payload d → Bool)
    (word : Word (padding + 3 * (d + 1) * 2 ^ d + d + 1))
    (h : ℕ) (hh : h ≤ padding)
    (hok : ∀ i : Fin (padding + 3 * (d + 1) * 2 ^ d), i.val < h →
      buildP d padding A i (fun j => word (Fin.ofNat _ (i.val + j.val))) = true) :
    ∀ t : ℕ, t < h + (d + 1) →
      word (Fin.ofNat _ t) = word (Fin.ofNat _ (t % (d + 1))) := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < d + 1
    · rw [Nat.mod_eq_of_lt htw]
    · have hi : t - (d + 1) < padding + 3 * (d + 1) * 2 ^ d := by omega
      have hih : t - (d + 1) < h := by omega
      have hstep := hok ⟨t - (d + 1), hi⟩ hih
      simp only [buildP, show t - (d + 1) < padding by omega, ↓reduceDIte] at hstep
      have hcopy : copyPat (fun j : Fin (d + 1 + 1) =>
          word (Fin.ofNat _ (t - (d + 1) + j.val))) = true := by
        by_cases hz : t - (d + 1) = 0
        · simp only [hz, ↓reduceIte, Bool.and_eq_true] at hstep
          rw [hz]
          exact hstep.2
        · simp only [hz, ↓reduceIte] at hstep
          exact hstep
      simp only [copyPat, beq_iff_eq, Fin.val_last, Fin.val_zero, Nat.add_zero] at hcopy
      have heq : t - (d + 1) + (d + 1) = t := by omega
      rw [heq] at hcopy
      rw [hcopy, ih (t - (d + 1)) (by omega) (by omega)]
      have hmod : (t - (d + 1)) % (d + 1) = t % (d + 1) := by
        have h1 : t = (t - (d + 1)) + (d + 1) := by omega
        conv_rhs => rw [h1, Nat.add_mod_right]
      rw [hmod]

lemma buildP_step_reach (d padding : ℕ) (A : Payload d → Payload d → Bool)
    (word : Word (padding + 3 * (d + 1) * 2 ^ d + d + 1))
    (t : ℕ) (ht : t ≤ 3 * 2 ^ d)
    (hok : ∀ i : Fin (padding + 3 * (d + 1) * 2 ^ d), i.val < padding + t * (d + 1) →
      buildP d padding A i (fun j => word (Fin.ofNat _ (i.val + j.val))) = true) :
    Reach ((tests A (keyList d)).take t)
      (fun j : Fin (d + 1) => word (Fin.ofNat _ (padding + j.val)))
      (fun j : Fin (d + 1) => word (Fin.ofNat _ (padding + t * (d + 1) + j.val))) := by
  induction t with
  | zero =>
    simp [Reach]
  | succ t ih =>
    have htslen : (tests A (keyList d)).length = 3 * 2 ^ d := by rw [len_tests, keylen]
    have htlt : t < (tests A (keyList d)).length := by omega
    have htake : (tests A (keyList d)).take (t + 1) =
        (tests A (keyList d)).take t ++ [(tests A (keyList d))[t]'htlt] :=
      List.take_succ_eq_append_getElem htlt
    rw [htake, reach_append]
    refine ⟨fun j : Fin (d + 1) => word (Fin.ofNat _ (padding + t * (d + 1) + j.val)),
      ih (by omega) (fun i hi => hok i (by
        have hmul : t * (d + 1) ≤ (t + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) (Nat.le_succ t)
        omega)), ?_⟩
    simp only [Reach, exists_eq_right]
    intro r
    have hi : padding + t * (d + 1) + r.val < padding + 3 * (d + 1) * 2 ^ d := by
      have h1 : (t + 1) * (d + 1) ≤ 3 * 2 ^ d * (d + 1) := Nat.mul_le_mul_right (d + 1) ht
      have h2 : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
      have h3 : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
      have := r.isLt
      omega
    have hih : padding + t * (d + 1) + r.val < padding + (t + 1) * (d + 1) := by
      have : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
      have := r.isLt
      omega
    have hstep := hok ⟨padding + t * (d + 1) + r.val, hi⟩ hih
    have hnotlt : ¬ (padding + t * (d + 1) + r.val < padding) := by omega
    have hoff : padding + t * (d + 1) + r.val - padding = t * (d + 1) + r.val := by omega
    have hdiv : (t * (d + 1) + r.val) / (d + 1) = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos d),
        Nat.div_eq_of_lt r.isLt, Nat.zero_add]
    have hmod : (t * (d + 1) + r.val) % (d + 1) = r.val := by
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]
    have hfin : (⟨(padding + t * (d + 1) + r.val - padding) % (d + 1),
        Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = r := by
      apply Fin.ext; dsimp; rw [hoff, hmod]
    have hget : (tests A (keyList d))[(padding + t * (d + 1) + r.val - padding) / (d + 1)]'(by
        rw [hoff, hdiv]; exact htlt) = (tests A (keyList d))[t]'htlt := by
      congr 1; rw [hoff, hdiv]
    have hbase : ((tests A (keyList d))[t]'htlt) r
        (fun j : Fin (d + 1 + 1) => word (Fin.ofNat _ (padding + t * (d + 1) + r.val + j.val))) = true := by
      simp only [buildP, hnotlt, ↓reduceDIte] at hstep
      split_ifs at hstep
      · rw [Bool.and_eq_true] at hstep
        simpa only [hget, hfin] using hstep.2
      · simpa only [hget, hfin] using hstep
    have hsp : (fun j : Fin (d + 1 + 1) => word (Fin.ofNat _ (padding + t * (d + 1) + r.val + j.val))) =
        splice (fun j : Fin (d + 1) => word (Fin.ofNat _ (padding + t * (d + 1) + j.val)))
          (fun j : Fin (d + 1) => word (Fin.ofNat _ (padding + (t + 1) * (d + 1) + j.val))) r := by
      funext j
      unfold splice
      split
      · congr 2; dsimp; omega
      · congr 2
        have hmul : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
        dsimp; omega
    rwa [← hsp]

lemma buildP_reached_card (d padding K : ℕ) (A : Payload d → Payload d → Bool)
    (hK0 : 2 ^ (d + 1) ≤ K)
    (hK : 2 ^ d + ∑ u : Payload d, (Finset.univ.filter (fun v : Payload d => A u v = true)).card ≤ K)
    (h : ℕ) (hh : h ≤ padding + 3 * (d + 1) * 2 ^ d) :
    (((Finset.univ : Finset (Fin (padding + 3 * (d + 1) * 2 ^ d + d + 1) → Bool)).filter (fun word =>
      ∀ i : Fin (padding + 3 * (d + 1) * 2 ^ d), i.val < h →
        buildP d padding A i (fun j => word (Fin.ofNat _ (i.val + j.val))) = true)).image
      (fun x => ((fun k : Fin (d + 1) => x (Fin.ofNat _ k.val)),
        (fun l : Fin (d + 1) => x (Fin.ofNat _ (h + l.val)))))).card ≤ K := by
  let w := d + 1
  let D := 2 ^ d
  let L := padding + 3 * w * D
  let n := L + d + 1
  let pos := fun t : ℕ => Fin.ofNat (L + d + 1) t
  by_cases hh0 : h = 0
  · subst hh0
    have hsub :
        (((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
          ∀ i : Fin L, i.val < 0 → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true)).image
          (fun x => ((fun k : Fin w => x (pos k.val)), (fun l : Fin w => x (pos (0 + l.val)))))) ⊆
        (Finset.univ : Finset (State d)).image (fun a => (a, a)) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨word, _, rfl⟩
      refine Finset.mem_image.mpr ⟨fun k : Fin w => word (pos k.val), Finset.mem_univ _, ?_⟩
      ext <;> simp
    calc _ ≤ ((Finset.univ : Finset (State d)).image (fun a => (a, a))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (State d)).card := Finset.card_image_le
      _ = 2 ^ (d + 1) := by simp [State, Word]
      _ ≤ K := hK0
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh0
    let dom : Finset (Payload d × Option (Payload d)) :=
      Finset.univ.filter (fun p => (match p.2 with | none => true | some v => A p.1 v) = true)
    have hdom_card : dom.card =
        2 ^ d + ∑ u : Payload d, (Finset.univ.filter (fun v : Payload d => A u v = true)).card := by
      have h1 : dom.card = ∑ u : Payload d,
          ((Finset.univ : Finset (Option (Payload d))).filter
            (fun o => (match o with | none => true | some v => A u v) = true)).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.card_filter]
      rw [h1]
      have h2 : ∀ u : Payload d,
          ((Finset.univ : Finset (Option (Payload d))).filter
            (fun o => (match o with | none => true | some v => A u v) = true)).card =
          1 + (Finset.univ.filter (fun v : Payload d => A u v = true)).card := by
        intro u
        rw [Finset.card_filter, Fintype.sum_option, Finset.card_filter]
        simp
      simp_rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      have hcard : Fintype.card (Payload d) = 2 ^ d := by simp [Payload, Word]
      rw [hcard]
    have hbound : ∀ (F : Payload d → Option (Payload d) → State d × State d),
        (∀ word : Fin n → Bool,
          (∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true) →
          ∃ p ∈ dom, F p.1 p.2 =
            ((fun k : Fin w => word (pos k.val)), (fun l : Fin w => word (pos (h + l.val))))) →
        (((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
          ∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true)).image
          (fun x => ((fun k : Fin w => x (pos k.val)), (fun l : Fin w => x (pos (h + l.val)))))).card ≤ K := by
      intro F hF
      have hsub :
          (((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
            ∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true)).image
            (fun x => ((fun k : Fin w => x (pos k.val)), (fun l : Fin w => x (pos (h + l.val)))))) ⊆
          dom.image (fun p => F p.1 p.2) := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨word, hword, rfl⟩
        rw [Finset.mem_filter] at hword
        obtain ⟨p, hp, hpeq⟩ := hF word hword.2
        exact Finset.mem_image.mpr ⟨p, hp, hpeq⟩
      calc _ ≤ (dom.image (fun p => F p.1 p.2)).card := Finset.card_le_card hsub
        _ ≤ dom.card := Finset.card_image_le
        _ ≤ K := by rw [hdom_card]; exact hK
    have hbit0 : ∀ word : Fin n → Bool,
        (∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true) →
        word (pos (padding % w)) = false := by
      intro word hok
      have h0 := hok ⟨0, by dsimp [L, w, D]; positivity⟩ hhpos
      simp only [buildP, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', Nat.zero_add] at h0
      exact h0.1
    by_cases hpad : h ≤ padding
    · apply hbound (fun u _ =>
        (unrotState padding (mkFalse u),
          fun l => unrotState padding (mkFalse u) ⟨(h + l.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩))
      intro word hok
      let a0 : State d := fun k => word (pos k.val)
      let s0 : State d := rotState padding a0
      have hs0 : s0 0 = false := by
        simpa [s0, rotState, a0] using hbit0 word hok
      let u : Payload d := payload s0
      have hmk : mkFalse u = s0 := by
        funext i
        refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
      have ha0 : unrotState padding (mkFalse u) = a0 := by
        rw [hmk]; exact unrot_rot padding a0
      refine ⟨(u, none), by simp [dom], ?_⟩
      apply Prod.ext
      · exact ha0
      · funext l
        rw [ha0]
        exact (buildP_word_prefix d padding A word h hpad hok (h + l.val) (by have := l.isLt; omega)).symm
    · have hpadlt : padding < h := by omega
      have hpref : ∀ word : Fin n → Bool,
          (∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true) →
          (fun l : Fin w => word (pos (padding + l.val))) =
            rotState padding (fun k : Fin w => word (pos k.val)) := by
        intro word hok
        funext l
        exact buildP_word_prefix d padding A word padding (le_refl _)
          (fun i hi => hok i (by omega)) (padding + l.val) (by have := l.isLt; omega)
      let h' := h - padding
      have hh'le : h' ≤ 3 * (d + 1) * 2 ^ d := by omega
      by_cases hend : h' = 3 * (d + 1) * 2 ^ d
      · apply hbound (fun u o => match o with
          | none => (unrotState padding (mkFalse u), mkFalse u)
          | some v => (unrotState padding (mkFalse u), mkTrue v))
        intro word hok
        let a0 : State d := fun k => word (pos k.val)
        let s0 : State d := rotState padding a0
        have hs0 : s0 0 = false := by
          simpa [s0, rotState, a0] using hbit0 word hok
        let u : Payload d := payload s0
        have hmk : mkFalse u = s0 := by
          funext i; refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
        have ha0 : unrotState padding (mkFalse u) = a0 := by
          rw [hmk]; exact unrot_rot padding a0
        have h3D : padding + 3 * 2 ^ d * (d + 1) = h := by
          have : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
          omega
        have hreach := buildP_step_reach d padding A word (3 * 2 ^ d) (le_refl _)
          (fun i hi => hok i (by omega))
        have hst0 : (fun j : Fin (d + 1) => word (pos (padding + j.val))) = mkFalse u := by
          rw [hmk]; exact hpref word hok
        have hstE : (fun j : Fin (d + 1) => word (pos (padding + 3 * 2 ^ d * (d + 1) + j.val))) =
            (fun l : Fin (d + 1) => word (pos (h + l.val))) := by
          funext l; congr 2; omega
        rw [hst0, hstE] at hreach
        have hreach' := reach_take_3m A (keyList d) (2 ^ d) u _ hreach
        rcases hreach' with heq | ⟨v, hv, heq⟩
        · exact ⟨(u, none), by simp [dom], Prod.ext ha0 heq.symm⟩
        · exact ⟨(u, some v), by simp [dom, hv], Prod.ext ha0 heq.symm⟩
      · have hh'lt : h' < 3 * (d + 1) * 2 ^ d := by omega
        let t := h' / (d + 1)
        let r := h' % (d + 1)
        have hr : r < d + 1 := Nat.mod_lt h' (Nat.succ_pos d)
        have ht : t < 3 * 2 ^ d := (Nat.div_lt_iff_lt_mul (show 0 < d + 1 by omega)).mpr (by
          have : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
          omega)
        let m := t / 3
        have hm : m < 2 ^ d := by omega
        have hm_len : m < (keyList d).length := by rw [keylen]; exact hm
        let k : Payload d := (keyList d)[m]'hm_len
        have hmod3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
        have hht : h = padding + t * (d + 1) + r := by
          have hdiv := Nat.div_add_mod h' (d + 1)
          have : (d + 1) * (h' / (d + 1)) = t * (d + 1) := by dsimp [t]; ring
          dsimp [h', r] at *
          omega
        have hreach_m : ∀ word : Fin n → Bool,
            (∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true) →
            let a0 : State d := fun j => word (pos j.val)
            let u : Payload d := payload (rotState padding a0)
            let sm : State d := fun j => word (pos (padding + (3 * m) * (d + 1) + j.val))
            sm = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ sm = mkTrue v := by
          intro word hok a0 u sm
          have hs0 : (rotState padding a0) 0 = false := by
            simpa [rotState, a0] using hbit0 word hok
          have hmk : mkFalse u = rotState padding a0 := by
            funext i; refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
          have h3m_le : 3 * m ≤ t := by omega
          have hreach := buildP_step_reach d padding A word (3 * m) (by omega)
            (fun i hi => hok i (by
              have hmul : (3 * m) * (d + 1) ≤ t * (d + 1) := Nat.mul_le_mul_right (d + 1) h3m_le
              omega))
          have hst0 : (fun j : Fin (d + 1) => word (pos (padding + j.val))) = mkFalse u := by
            rw [hmk]; exact hpref word hok
          rw [hst0] at hreach
          exact reach_take_3m A (keyList d) m u sm hreach
        have hstep_t : ∀ (word : Fin n → Bool) (q : ℕ) (hq : q < t),
            (∀ i : Fin L, i.val < h → buildP d padding A i (fun j => word (pos (i.val + j.val))) = true) →
            SweepOk ((tests A (keyList d))[q]'(by rw [len_tests, keylen]; exact lt_trans hq ht))
              (fun j => word (pos (padding + q * (d + 1) + j.val)))
              (fun j => word (pos (padding + (q + 1) * (d + 1) + j.val))) := by
          intro word q hq hok j
          have hi : padding + q * (d + 1) + j.val < L := by
            have h1 : (q + 1) * (d + 1) ≤ 3 * 2 ^ d * (d + 1) := Nat.mul_le_mul_right (d + 1) (by omega)
            have h2 : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
            have h3 : (q + 1) * (d + 1) = q * (d + 1) + (d + 1) := by ring
            have := j.isLt; dsimp [L, w, D]; omega
          have hih : padding + q * (d + 1) + j.val < h := by
            have h1 : (q + 1) * (d + 1) ≤ t * (d + 1) := Nat.mul_le_mul_right (d + 1) (by omega)
            have h2 : (q + 1) * (d + 1) = q * (d + 1) + (d + 1) := by ring
            have := j.isLt; omega
          have hstep := hok ⟨padding + q * (d + 1) + j.val, hi⟩ hih
          have hnotlt : ¬ (padding + q * (d + 1) + j.val < padding) := by omega
          have hoff : padding + q * (d + 1) + j.val - padding = q * (d + 1) + j.val := by omega
          have hdiv : (q * (d + 1) + j.val) / (d + 1) = q := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos d),
              Nat.div_eq_of_lt j.isLt, Nat.zero_add]
          have hmod : (q * (d + 1) + j.val) % (d + 1) = j.val := by
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
          have hfin : (⟨(padding + q * (d + 1) + j.val - padding) % (d + 1),
              Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = j := by
            apply Fin.ext; dsimp; rw [hoff, hmod]
          have hget : (tests A (keyList d))[(padding + q * (d + 1) + j.val - padding) / (d + 1)]'(by
              rw [len_tests, keylen, hoff, hdiv]; exact lt_trans hq ht) =
              (tests A (keyList d))[q]'(by rw [len_tests, keylen]; exact lt_trans hq ht) := by
            congr 1; rw [hoff, hdiv]
          have hbase : ((tests A (keyList d))[q]'(by rw [len_tests, keylen]; exact lt_trans hq ht)) j
              (fun c : Fin (d + 1 + 1) => word (pos (padding + q * (d + 1) + j.val + c.val))) = true := by
            simp only [buildP, hnotlt, ↓reduceDIte] at hstep
            split_ifs at hstep
            · rw [Bool.and_eq_true] at hstep
              simpa only [hget, hfin] using hstep.2
            · simpa only [hget, hfin] using hstep
          have hsp : (fun c : Fin (d + 1 + 1) => word (pos (padding + q * (d + 1) + j.val + c.val))) =
              splice (fun c => word (pos (padding + q * (d + 1) + c.val)))
                (fun c => word (pos (padding + (q + 1) * (d + 1) + c.val))) j := by
            funext c; unfold splice; split
            · congr 2; dsimp; omega
            · congr 2
              have hmul : (q + 1) * (d + 1) = q * (d + 1) + (d + 1) := by ring
              dsimp; omega
          rwa [← hsp]
        have hpart_t : ∀ (word : Fin n → Bool) (j : Fin (d + 1)), j.val < r →
            (∀ i : Fin L, i.val < h → buildP d padding A i (fun c => word (pos (i.val + c.val))) = true) →
            ((tests A (keyList d))[t]'(by rw [len_tests, keylen]; exact ht)) j
              (splice (fun c => word (pos (padding + t * (d + 1) + c.val)))
                (fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))) j) = true := by
          intro word j hj hok
          have hi : padding + t * (d + 1) + j.val < L := by
            have h1 : (t + 1) * (d + 1) ≤ 3 * 2 ^ d * (d + 1) := Nat.mul_le_mul_right (d + 1) (by omega)
            have h2 : 3 * 2 ^ d * (d + 1) = 3 * (d + 1) * 2 ^ d := by ring
            have h3 : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
            have := j.isLt; dsimp [L, w, D]; omega
          have hih : padding + t * (d + 1) + j.val < h := by omega
          have hstep := hok ⟨padding + t * (d + 1) + j.val, hi⟩ hih
          have hnotlt : ¬ (padding + t * (d + 1) + j.val < padding) := by omega
          have hoff : padding + t * (d + 1) + j.val - padding = t * (d + 1) + j.val := by omega
          have hdiv : (t * (d + 1) + j.val) / (d + 1) = t := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos d),
              Nat.div_eq_of_lt j.isLt, Nat.zero_add]
          have hmod : (t * (d + 1) + j.val) % (d + 1) = j.val := by
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
          have hfin : (⟨(padding + t * (d + 1) + j.val - padding) % (d + 1),
              Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = j := by
            apply Fin.ext; dsimp; rw [hoff, hmod]
          have hget : (tests A (keyList d))[(padding + t * (d + 1) + j.val - padding) / (d + 1)]'(by
              rw [len_tests, keylen, hoff, hdiv]; exact ht) =
              (tests A (keyList d))[t]'(by rw [len_tests, keylen]; exact ht) := by
            congr 1; rw [hoff, hdiv]
          have hbase : ((tests A (keyList d))[t]'(by rw [len_tests, keylen]; exact ht)) j
              (fun c : Fin (d + 1 + 1) => word (pos (padding + t * (d + 1) + j.val + c.val))) = true := by
            simp only [buildP, hnotlt, ↓reduceDIte] at hstep
            split_ifs at hstep
            · rw [Bool.and_eq_true] at hstep
              simpa only [hget, hfin] using hstep.2
            · simpa only [hget, hfin] using hstep
          have hsp : (fun c : Fin (d + 1 + 1) => word (pos (padding + t * (d + 1) + j.val + c.val))) =
              splice (fun c => word (pos (padding + t * (d + 1) + c.val)))
                (fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))) j := by
            funext c; unfold splice; split
            · congr 2; dsimp; omega
            · congr 2
              have hmul : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
              dsimp; omega
          rwa [← hsp]
        have hmask_part : ∀ (st sb : State d),
            (∀ j : Fin (d + 1), j.val < r → maskTest k j (splice st sb j) = true) →
            (∀ j : Fin (d + 1), j.val < r → sb j = mask k st j) := by
          intro st sb hok_m j hj
          have h0 : sb 0 = st 0 := by
            have := hok_m 0 (by simp only [Fin.val_zero]; omega)
            simpa [maskTest, splice_last, splice_head] using this
          by_cases hj0 : j = 0
          · rw [hj0]; simpa [mask] using h0
          · obtain ⟨idx, hidx⟩ := Fin.exists_succ_eq.mpr hj0
            rw [← hidx]
            have h1 := hok_m idx.succ (by rw [hidx]; exact hj)
            simpa [maskTest, splice_last, splice_head, splice_tag, mask, h0] using h1
        have hwin_eq : ∀ (word : Fin n → Bool) (st sb : State d),
            st = (fun c => word (pos (padding + t * (d + 1) + c.val))) →
            sb = (fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))) →
            ∀ l : Fin (d + 1), word (pos (h + l.val)) =
              if hl : r + l.val < d + 1 then st ⟨r + l.val, hl⟩
              else sb ⟨r + l.val - (d + 1), by have := l.isLt; omega⟩ := by
          intro word st sb hst hsb l
          split
          · rename_i hl
            rw [hst]; congr 2; dsimp; omega
          · rename_i hge
            rw [hsb]; congr 2
            have hmul : (t + 1) * (d + 1) = t * (d + 1) + (d + 1) := by ring
            dsimp; omega
        rcases hmod3 with hm0 | hm1 | hm2
        · have ht_eq : t = 3 * m := by omega
          apply hbound (fun u o => match o with
            | none => (unrotState padding (mkFalse u), partialMask k r hr (mkFalse u))
            | some v => (unrotState padding (mkFalse u), partialMask k r hr (mkTrue v)))
          intro word hok
          let a0 : State d := fun j => word (pos j.val)
          let u : Payload d := payload (rotState padding a0)
          have hs0 : (rotState padding a0) 0 = false := by
            simpa [rotState, a0] using hbit0 word hok
          have hmk : mkFalse u = rotState padding a0 := by
            funext i; refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
          have ha0 : unrotState padding (mkFalse u) = a0 := by
            rw [hmk]; exact unrot_rot padding a0
          let st : State d := fun c => word (pos (padding + t * (d + 1) + c.val))
          let sb : State d := fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))
          have hsb : ∀ j : Fin (d + 1), j.val < r → sb j = mask k st j := by
            apply hmask_part st sb
            intro j hj
            have h1 := hpart_t word j hj hok
            have hget : (tests A (keyList d))[t]'(by rw [len_tests, keylen]; omega) = maskTest k := by
              have h2 := tests_getElem_0 A (keyList d) m hm_len
              simpa [ht_eq, k] using h2
            rwa [hget] at h1
          have hwin : (fun l : Fin (d + 1) => word (pos (h + l.val))) = partialMask k r hr st := by
            funext l
            rw [hwin_eq word st sb rfl rfl l]
            unfold partialMask
            split
            · rfl
            · rename_i hge
              exact hsb ⟨r + l.val - (d + 1), by have := l.isLt; omega⟩ (by dsimp; have := l.isLt; omega)
          have hrm := hreach_m word hok
          have hst_eq : st = (fun c => word (pos (padding + (3 * m) * (d + 1) + c.val))) := by
            funext c; dsimp [st]; congr 2; rw [ht_eq]
          rw [← hst_eq] at hrm
          rcases hrm with heq | ⟨v, hv, heq⟩
          · exact ⟨(u, none), by simp [dom], Prod.ext ha0 (by dsimp only; rw [hwin, heq])⟩
          · exact ⟨(u, some v), by simp only [dom, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv,
              Prod.ext ha0 (by dsimp only; rw [hwin, heq])⟩
        · have ht_eq : t = 3 * m + 1 := by omega
          apply hbound (fun u o => match o with
            | none => (unrotState padding (mkFalse u), partialStay r hr (mkFalse u))
            | some v => (unrotState padding (mkFalse u), partialStay r hr (mkTrue (diff v k))))
          intro word hok
          let a0 : State d := fun j => word (pos j.val)
          let u : Payload d := payload (rotState padding a0)
          have hs0 : (rotState padding a0) 0 = false := by
            simpa [rotState, a0] using hbit0 word hok
          have hmk : mkFalse u = rotState padding a0 := by
            funext i; refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
          have ha0 : unrotState padding (mkFalse u) = a0 := by
            rw [hmk]; exact unrot_rot padding a0
          let sm : State d := fun c => word (pos (padding + (3 * m) * (d + 1) + c.val))
          let st : State d := fun c => word (pos (padding + t * (d + 1) + c.val))
          let sb : State d := fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))
          have hst_mask : st = mask k sm := by
            have hsw := hstep_t word (3 * m) (by omega) hok
            have hget : (tests A (keyList d))[3 * m]'(by rw [len_tests, keylen]; omega) = maskTest k :=
              tests_getElem_0 A (keyList d) m hm_len
            rw [hget, mask_ok] at hsw
            have : (fun c => word (pos (padding + (3 * m + 1) * (d + 1) + c.val))) = st := by
              funext c; congr 2; rw [ht_eq]
            rwa [this] at hsw
          have hrm : sm = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ sm = mkTrue v :=
            hreach_m word hok
          have hst_cases : st = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ st = mkTrue (diff v k) := by
            rcases hrm with heq | ⟨v, hv, heq⟩
            · left; rw [hst_mask, heq]; exact mask_off k rfl
            · right; exact ⟨v, hv, by rw [hst_mask, heq]; exact mask_mkTrue k v⟩
          by_cases hr0 : r = 0
          · have hwin : (fun l : Fin (d + 1) => word (pos (h + l.val))) = st := by
              funext l; rw [hwin_eq word st sb rfl rfl l]
              simp only [hr0, Nat.zero_add, l.isLt, ↓reduceDIte]
            have hps : ∀ s : State d, partialStay r hr s = s := by
              intro s; funext l; simp [partialStay, hr0, l.isLt]
            rcases hst_cases with heq | ⟨v, hv, heq⟩
            · exact ⟨(u, none), by simp [dom], Prod.ext ha0 (by dsimp only; rw [hwin, heq, hps])⟩
            · exact ⟨(u, some v), by simp [dom, hv], Prod.ext ha0 (by dsimp only; rw [hwin, heq, hps])⟩
          · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
            have hget : (tests A (keyList d))[t]'(by rw [len_tests, keylen]; omega) = toggleTest k A := by
              have h2 := tests_getElem_1 A (keyList d) m hm_len
              simpa [ht_eq, k] using h2
            have h0 := hpart_t word 0 hrpos hok
            rw [hget] at h0
            change toggleTest k A 0 (splice st sb 0) = true at h0
            have h0' : sb 0 = st 0 ∨ (st 0 = false ∧ A (payload st) (diff (payload st) k) = true) := by
              have hpl0 : (fun j : Fin d => splice st sb 0 j.succ.castSucc) = payload st :=
                funext (splice_payload st sb)
              simp only [toggleTest, Fin.cases_zero, splice_last, splice_head, hpl0] at h0
              simpa using h0
            have hpl : ∀ (idx : Fin d), idx.succ.val < r → sb idx.succ = st idx.succ := by
              intro idx hidx
              have h1 := hpart_t word idx.succ hidx hok
              rw [hget] at h1
              change toggleTest k A idx.succ (splice st sb idx.succ) = true at h1
              simpa [toggleTest, splice_last, splice_head] using h1
            have hwin_of : ∀ (b0 : Bool), sb 0 = b0 →
                (fun l : Fin (d + 1) => word (pos (h + l.val))) = partialStay r hr (Fin.cases b0 (payload st)) := by
              intro b0 hb0
              funext l
              rw [hwin_eq word st sb rfl rfl l]
              unfold partialStay
              split
              · rename_i hl
                have hne0 : (⟨r + l.val, hl⟩ : Fin (d + 1)) ≠ 0 := by
                  intro heq; have := congrArg Fin.val heq; simp at this; omega
                obtain ⟨idx, hidx⟩ := Fin.exists_succ_eq.mpr hne0
                rw [← hidx]
                rfl
              · rename_i hge
                have hjlt : r + l.val - (d + 1) < r := by have := l.isLt; omega
                let j : Fin (d + 1) := ⟨r + l.val - (d + 1), by omega⟩
                have hjr : j.val < r := hjlt
                change sb j = Fin.cases b0 (payload st) j
                by_cases hj0 : j = 0
                · rw [hj0]; simpa using hb0
                · obtain ⟨idx, hidx⟩ := Fin.exists_succ_eq.mpr hj0
                  rw [← hidx]
                  exact hpl idx (by rw [hidx]; exact hjr)
            rcases hst_cases with heq | ⟨v, hv, heq⟩
            · cases hsb0 : sb 0
              · refine ⟨(u, none), by simp [dom], Prod.ext ha0 ?_⟩
                dsimp only
                rw [hwin_of false hsb0, heq]
                rfl
              · have hAu : A u (diff u k) = true := by
                  rw [heq, hsb0] at h0'
                  simpa [mkFalse, payload_mkFalse] using h0'
                refine ⟨(u, some (diff u k)), by simp [dom, hAu], Prod.ext ha0 ?_⟩
                dsimp only
                rw [hwin_of true hsb0, heq, payload_mkFalse, diff_self_right]
                rfl
            · have hsb0 : sb 0 = true := by
                rw [heq] at h0'
                cases hb : sb 0 <;> simp [mkTrue, hb] at h0' ⊢
              refine ⟨(u, some v), by simp [dom, hv], Prod.ext ha0 ?_⟩
              dsimp only
              rw [hwin_of true hsb0, heq, payload_mkTrue]
              rfl
        · have ht_eq : t = 3 * m + 2 := by omega
          apply hbound (fun u o => match o with
            | none => (unrotState padding (mkFalse u), partialMask k r hr (mkFalse u))
            | some v => (unrotState padding (mkFalse u), partialMask k r hr (mkTrue (diff v k))))
          intro word hok
          let a0 : State d := fun j => word (pos j.val)
          let u : Payload d := payload (rotState padding a0)
          have hs0 : (rotState padding a0) 0 = false := by
            simpa [rotState, a0] using hbit0 word hok
          have hmk : mkFalse u = rotState padding a0 := by
            funext i; refine Fin.cases (by simpa [mkFalse] using hs0.symm) (fun j => rfl) i
          have ha0 : unrotState padding (mkFalse u) = a0 := by
            rw [hmk]; exact unrot_rot padding a0
          let sm : State d := fun c => word (pos (padding + (3 * m) * (d + 1) + c.val))
          let sm1 : State d := fun c => word (pos (padding + (3 * m + 1) * (d + 1) + c.val))
          let st : State d := fun c => word (pos (padding + t * (d + 1) + c.val))
          let sb : State d := fun c => word (pos (padding + (t + 1) * (d + 1) + c.val))
          have hsm1 : sm1 = mask k sm := by
            have hsw := hstep_t word (3 * m) (by omega) hok
            have hget : (tests A (keyList d))[3 * m]'(by rw [len_tests, keylen]; omega) = maskTest k :=
              tests_getElem_0 A (keyList d) m hm_len
            rw [hget, mask_ok] at hsw
            exact hsw
          have hst_tog : st = sm1 ∨ (sm1 0 = false ∧ A (payload sm1) (diff (payload sm1) k) = true ∧ st = rise sm1) := by
            have hsw := hstep_t word (3 * m + 1) (by omega) hok
            have hget : (tests A (keyList d))[3 * m + 1]'(by rw [len_tests, keylen]; omega) = toggleTest k A :=
              tests_getElem_1 A (keyList d) m hm_len
            rw [hget, toggle_ok] at hsw
            have : (fun c => word (pos (padding + (3 * m + 1 + 1) * (d + 1) + c.val))) = st := by
              funext c; congr 2; rw [ht_eq]
            rwa [this] at hsw
          have hrm : sm = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ sm = mkTrue v :=
            hreach_m word hok
          have hsm1_cases : sm1 = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ sm1 = mkTrue (diff v k) := by
            rcases hrm with heq | ⟨v, hv, heq⟩
            · left; rw [hsm1, heq]; exact mask_off k rfl
            · right; exact ⟨v, hv, by rw [hsm1, heq]; exact mask_mkTrue k v⟩
          have hst_cases : st = mkFalse u ∨ ∃ v : Payload d, A u v = true ∧ st = mkTrue (diff v k) := by
            rcases hst_tog with hst_eq | ⟨hs0', hA', hst_rise⟩
            · rw [hst_eq]; exact hsm1_cases
            · rcases hsm1_cases with heq | ⟨v, _, heq⟩
              · right
                rw [heq] at hA' hst_rise
                rw [payload_mkFalse] at hA'
                refine ⟨diff u k, hA', ?_⟩
                rw [hst_rise]
                funext i
                refine Fin.cases rfl (fun j => by simp [rise, mkTrue, mkFalse, payload, diff]) i
              · rw [heq] at hs0'; simp [mkTrue] at hs0'
          have hsb : ∀ j : Fin (d + 1), j.val < r → sb j = mask k st j := by
            apply hmask_part st sb
            intro j hj
            have h1 := hpart_t word j hj hok
            have hget : (tests A (keyList d))[t]'(by rw [len_tests, keylen]; omega) = maskTest k := by
              have h2 := tests_getElem_2 A (keyList d) m hm_len
              simpa [ht_eq, k] using h2
            rwa [hget] at h1
          have hwin : (fun l : Fin (d + 1) => word (pos (h + l.val))) = partialMask k r hr st := by
            funext l
            rw [hwin_eq word st sb rfl rfl l]
            unfold partialMask
            split
            · rfl
            · rename_i hge
              exact hsb ⟨r + l.val - (d + 1), by have := l.isLt; omega⟩ (by dsimp; have := l.isLt; omega)
          rcases hst_cases with heq | ⟨v, hv, heq⟩
          · exact ⟨(u, none), by simp [dom], Prod.ext ha0 (by rw [hwin, heq])⟩
          · exact ⟨(u, some v), by simp [dom, hv], Prod.ext ha0 (by rw [hwin, heq])⟩

def buildQ (d padding a : ℕ) (ha : a < d) (u : Payload d)
    (j : Fin a → Bool) (k : Fin (d - a)) : Test (d + 1) :=
  let a0 := unrotState padding (mkFalse u)
  Fin.cases
    (fun pat =>
      (pat 0 == true) &&
      (pat (Fin.last (d + 1)) == a0 0) &&
      decide (∀ c : Fin a, pat ⟨c.val + 1, by omega⟩ = j c) &&
      (pat ⟨a + k.val + 1, by omega⟩ == true))
    (fun idx pat => pat (Fin.last (d + 1)) == a0 idx.succ)

def splitHi {d a : ℕ} (ha : a < d) (v : Payload d) : Fin a → Bool :=
  fun c => v ⟨c.val, by omega⟩

def splitLo {d a : ℕ} (ha : a < d) (v : Payload d) : Fin (d - a) → Bool :=
  fun k => v ⟨a + k.val, by omega⟩

def combinePayload {d a : ℕ} (ha : a < d) (j : Fin a → Bool) (lo : Fin (d - a) → Bool) : Payload d :=
  fun idx => if h : idx.val < a then j ⟨idx.val, h⟩ else lo ⟨idx.val - a, by omega⟩

lemma splitHi_combine {d a : ℕ} (ha : a < d) (j : Fin a → Bool) (lo : Fin (d - a) → Bool) :
    splitHi ha (combinePayload ha j lo) = j := by
  funext c
  simp [splitHi, combinePayload, c.isLt]

lemma splitLo_combine {d a : ℕ} (ha : a < d) (j : Fin a → Bool) (lo : Fin (d - a) → Bool) :
    splitLo ha (combinePayload ha j lo) = lo := by
  funext k
  simp only [splitLo, combinePayload, show ¬ (a + k.val < a) by omega, ↓reduceDIte]
  congr 1
  apply Fin.ext
  dsimp
  omega

lemma combine_split {d a : ℕ} (ha : a < d) (v : Payload d) :
    combinePayload ha (splitHi ha v) (splitLo ha v) = v := by
  funext idx
  simp only [combinePayload, splitHi, splitLo]
  split
  · rfl
  · congr 1; apply Fin.ext; dsimp; omega

def matrixOf {d a : ℕ} (ha : a < d)
    (x : Payload d → (Fin a → Bool) → Fin (d - a) → Bool) :
    Payload d → Payload d → Bool :=
  fun u v => decide (splitLo ha v = x u (splitHi ha v))

lemma matrixOf_row_card {d a : ℕ} (ha : a < d)
    (x : Payload d → (Fin a → Bool) → Fin (d - a) → Bool) (u : Payload d) :
    (Finset.univ.filter (fun v : Payload d => matrixOf ha x u v = true)).card = 2 ^ a := by
  have heq : Finset.univ.filter (fun v : Payload d => matrixOf ha x u v = true) =
      (Finset.univ : Finset (Fin a → Bool)).image (fun j => combinePayload ha j (x u j)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, matrixOf, decide_eq_true_eq,
      Finset.mem_image]
    constructor
    · intro hv
      refine ⟨splitHi ha v, ?_⟩
      rw [← hv, combine_split]
    · rintro ⟨j, rfl⟩
      rw [splitLo_combine, splitHi_combine]
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro j1 j2 h
    have := congrArg (splitHi ha) h
    rwa [splitHi_combine, splitHi_combine] at this

lemma build_accepts_iff (d padding a : ℕ) (ha : a < d)
    (x : Payload d → (Fin a → Bool) → Fin (d - a) → Bool)
    (u : Payload d) (j : Fin a → Bool) (k : Fin (d - a)) :
    (∃ y : Fin (padding + 3 * (d + 1) * 2 ^ d + d + 1) → Bool,
      (∀ i : Fin (padding + 3 * (d + 1) * 2 ^ d),
        buildP d padding (matrixOf ha x) i (fun c => y (Fin.ofNat _ (i.val + c.val))) = true) ∧
      ∀ r : Fin (d + 1),
        buildQ d padding a ha u j k r
          (fun z => y (Fin.ofNat _ (padding + 3 * (d + 1) * 2 ^ d + r.val + z.val))) = true) ↔
    x u j k = true := by
  let w := d + 1
  let D := 2 ^ d
  let L := padding + 3 * w * D
  let n := L + d + 1
  let pos := fun t : ℕ => Fin.ofNat (L + d + 1) t
  let A := matrixOf ha x
  constructor
  · rintro ⟨y, hP, hQ⟩
    let a0 : State d := fun c => y (pos c.val)
    let b0 : State d := fun c => y (pos (L + c.val))
    have hQa0 : a0 = unrotState padding (mkFalse u) := by
      funext c
      refine Fin.cases ?_ ?_ c
      · have h0 := hQ 0
        simp only [buildQ, Fin.cases_zero, Bool.and_eq_true, beq_iff_eq, Fin.val_last,
          Fin.val_zero, Nat.add_zero] at h0
        have hpos : pos (L + (d + 1)) = pos 0 := by
          apply Fin.ext
          change (L + (d + 1)) % (L + d + 1) = 0 % (L + d + 1)
          have : L + (d + 1) = L + d + 1 := by omega
          rw [this, Nat.mod_self, Nat.zero_mod]
        have hres := h0.1.1.2
        change y (pos (L + (d + 1))) = unrotState padding (mkFalse u) 0 at hres
        rw [hpos] at hres
        exact hres
      · intro idx
        have hr := hQ idx.succ
        simp only [buildQ, Fin.cases_succ, beq_iff_eq, Fin.val_last] at hr
        have hpos : pos (L + idx.succ.val + (d + 1)) = pos idx.succ.val := by
          apply Fin.ext
          change (L + idx.succ.val + (d + 1)) % (L + d + 1) = idx.succ.val % (L + d + 1)
          have : L + idx.succ.val + (d + 1) = idx.succ.val + (L + d + 1) := by omega
          rw [this, Nat.add_mod_right]
        change y (pos (L + idx.succ.val + (d + 1))) = unrotState padding (mkFalse u) idx.succ at hr
        rw [hpos] at hr
        exact hr
    have hQ0 := hQ 0
    simp only [buildQ, Fin.cases_zero, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Fin.val_zero, Nat.add_zero] at hQ0
    have hb0_tag : b0 0 = true := hQ0.1.1.1
    have hb0_hi : splitHi ha (payload b0) = j := by
      funext c
      exact hQ0.1.2 c
    have hb0_lo_k : splitLo ha (payload b0) k = true := hQ0.2
    have hpref : (fun c : Fin (d + 1) => y (pos (padding + c.val))) = mkFalse u := by
      have hp := buildP_word_prefix d padding A y padding (le_refl _) (fun i _ => hP i)
      funext c
      have := hp (padding + c.val) (by have := c.isLt; omega)
      change y (pos (padding + c.val)) = mkFalse u c
      rw [this]
      change a0 ⟨(padding + c.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ = mkFalse u c
      rw [hQa0]
      exact congrFun (rot_unrot padding (mkFalse u)) c
    have hreach := buildP_step_reach d padding A y (3 * D) (le_refl _) (fun i _ => hP i)
    have hstE : (fun c : Fin (d + 1) => y (pos (padding + 3 * D * (d + 1) + c.val))) = b0 := by
      funext c; congr 2; dsimp [L, w, D]; ring
    have htake : (tests A (keyList d)).take (3 * D) = tests A (keyList d) := by
      rw [List.take_of_length_le (by rw [len_tests, keylen])]
    rw [hpref, hstE, htake, reach_keyList] at hreach
    rcases hreach with heq | ⟨_, _, hA⟩
    · have := congrFun heq 0
      simp [hb0_tag, mkFalse] at this
    · rw [payload_mkFalse] at hA
      have hA' : matrixOf ha x u (payload b0) = true := hA
      simp only [matrixOf, decide_eq_true_eq, hb0_hi] at hA'
      rw [← hA']
      exact hb0_lo_k
  · intro hxk
    let v : Payload d := combinePayload ha j (x u j)
    have hAv : A u v = true := by
      simp [A, matrixOf, v, splitLo_combine, splitHi_combine]
    have hreach : Reach (tests A (keyList d)) (mkFalse u) (mkTrue v) := by
      rw [reach_keyList]
      exact Or.inr ⟨rfl, rfl, by rw [payload_mkFalse, payload_mkTrue]; exact hAv⟩
    have hex_grid : ∀ (ts : List (Test (d + 1))) (sa sb : State d),
        Reach ts sa sb →
        ∃ g : Fin (ts.length + 1) → State d,
          g 0 = sa ∧ g (Fin.last ts.length) = sb ∧
          ∀ q : Fin ts.length, SweepOk (ts[q.val]'q.isLt) (g q.castSucc) (g q.succ) := by
      intro ts
      induction ts with
      | nil =>
        intro sa sb hr
        refine ⟨fun _ => sa, rfl, hr, fun q => Fin.elim0 q⟩
      | cons t ts ih =>
        intro sa sb hr
        rcases hr with ⟨y, hy, hts⟩
        obtain ⟨g, hg0, hglast, hgstep⟩ := ih y sb hts
        refine ⟨Fin.cons sa g, rfl, hglast, fun q => ?_⟩
        refine Fin.cases ?_ ?_ q
        · simpa [hg0] using hy
        · intro q'
          exact hgstep q'
    obtain ⟨g, hg0, hglast, hgstep⟩ := hex_grid (tests A (keyList d)) (mkFalse u) (mkTrue v) hreach
    have htslen : (tests A (keyList d)).length = 3 * D := by rw [len_tests, keylen]
    let a0 : State d := unrotState padding (mkFalse u)
    let y : Fin n → Bool := fun idx =>
      if hlt : idx.val < padding then
        a0 ⟨idx.val % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩
      else
        let off := idx.val - padding
        let q := off / (d + 1)
        let r := off % (d + 1)
        have hq : q < (tests A (keyList d)).length + 1 := by
          rw [htslen]
          have h1 : off < (3 * D + 1) * (d + 1) := by
            have := idx.isLt
            have hmul : (3 * D + 1) * (d + 1) = 3 * (d + 1) * D + (d + 1) := by ring
            dsimp [n, L, w] at this
            omega
          exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos d)).mpr h1
        g ⟨q, hq⟩ ⟨r, Nat.mod_lt _ (Nat.succ_pos d)⟩
    have hy_pad : ∀ t : ℕ, t < padding + (d + 1) →
        y (pos t) = a0 ⟨t % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ := by
      intro t ht
      have htlt : t < n := by dsimp [n, L, w, D]; omega
      have hpos_val : (pos t).val = t := Nat.mod_eq_of_lt htlt
      simp only [y, hpos_val]
      split
      · rfl
      · rename_i hge
        have hoff : t - padding < d + 1 := by omega
        have hdiv : (t - padding) / (d + 1) = 0 := Nat.div_eq_of_lt hoff
        have hmod : (t - padding) % (d + 1) = t - padding := Nat.mod_eq_of_lt hoff
        have hq0 : (⟨(t - padding) / (d + 1), by
            rw [hdiv]; omega⟩ : Fin ((tests A (keyList d)).length + 1)) = 0 := by
          apply Fin.ext; exact hdiv
        have hr0 : (⟨(t - padding) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) =
            ⟨t - padding, hoff⟩ := by
          apply Fin.ext; exact hmod
        rw [hq0, hr0, hg0]
        have hrot := congrFun (rot_unrot padding (mkFalse u)) ⟨t - padding, hoff⟩
        rw [← hrot]
        simp only [rotState, a0]
        congr 1
        apply Fin.ext
        have : padding + (t - padding) = t := by omega
        simp only [this]
    have hy_grid : ∀ (q : Fin ((tests A (keyList d)).length + 1)) (r : Fin (d + 1)),
        y (pos (padding + q.val * (d + 1) + r.val)) = g q r := by
      intro q r
      have hlt : padding + q.val * (d + 1) + r.val < n := by
        have h1 : q.val ≤ 3 * D := by have := q.isLt; omega
        have h2 : q.val * (d + 1) ≤ 3 * D * (d + 1) := Nat.mul_le_mul_right (d + 1) h1
        have h3 : 3 * D * (d + 1) = 3 * (d + 1) * D := by ring
        have := r.isLt; dsimp [n, L, w]; omega
      have hpos_val : (pos (padding + q.val * (d + 1) + r.val)).val =
          padding + q.val * (d + 1) + r.val := Nat.mod_eq_of_lt hlt
      simp only [y, hpos_val, show ¬ (padding + q.val * (d + 1) + r.val < padding) by omega, ↓reduceDIte]
      have hoff : padding + q.val * (d + 1) + r.val - padding = q.val * (d + 1) + r.val := by omega
      have hdiv : (q.val * (d + 1) + r.val) / (d + 1) = q.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos d),
          Nat.div_eq_of_lt r.isLt, Nat.zero_add]
      have hmod : (q.val * (d + 1) + r.val) % (d + 1) = r.val := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]
      have hq_eq : (⟨(padding + q.val * (d + 1) + r.val - padding) / (d + 1), by
          rw [hoff, hdiv]; exact q.isLt⟩ : Fin ((tests A (keyList d)).length + 1)) = q := by
        apply Fin.ext; dsimp; rw [hoff, hdiv]
      have hr_eq : (⟨(padding + q.val * (d + 1) + r.val - padding) % (d + 1),
          Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = r := by
        apply Fin.ext; dsimp; rw [hoff, hmod]
      rw [hq_eq, hr_eq]
    refine ⟨y, ?_, ?_⟩
    · intro i
      have hbit0 : y (pos (padding % (d + 1))) = false := by
        have h1 := hy_pad (padding % (d + 1)) (by have := Nat.mod_lt padding (show 0 < d + 1 by omega); omega)
        rw [h1]
        have h2 := congrFun (rot_unrot padding (mkFalse u)) 0
        simpa [rotState, a0, Nat.mod_mod, mkFalse] using h2
      have hbase_ok : (if h : i.val < padding then
            copyPat (fun c : Fin (d + 1 + 1) => y (pos (i.val + c.val)))
          else
            let off := i.val - padding
            ((tests A (keyList d))[off / (d + 1)]'(by
              rw [htslen]
              exact (Nat.div_lt_iff_lt_mul (show 0 < d + 1 by omega)).mpr (by
                have := i.isLt
                have hmul : 3 * D * (d + 1) = 3 * (d + 1) * D := by ring
                dsimp only [D, off] at *
                omega)))
              ⟨off % (d + 1), Nat.mod_lt _ (show 0 < d + 1 by omega)⟩
              (fun c => y (pos (i.val + c.val)))) = true := by
        split
        · rename_i hlt
          simp only [copyPat, beq_iff_eq, Fin.val_last, Fin.val_zero, Nat.add_zero]
          rw [hy_pad (i.val + (d + 1)) (by omega), hy_pad i.val (by omega)]
          congr 1; apply Fin.ext; exact Nat.add_mod_right i.val (d + 1)
        · rename_i hge
          let off := i.val - padding
          let q : Fin (tests A (keyList d)).length := ⟨off / (d + 1), by
            rw [htslen]
            exact (Nat.div_lt_iff_lt_mul (show 0 < d + 1 by omega)).mpr (by
              have := i.isLt
              have hmul : 3 * D * (d + 1) = 3 * (d + 1) * D := by ring
              dsimp only [D, off] at *
              omega)⟩
          let r : Fin (d + 1) := ⟨off % (d + 1), Nat.mod_lt _ (show 0 < d + 1 by omega)⟩
          have hi_eq : i.val = padding + q.val * (d + 1) + r.val := by
            have hdiv := Nat.div_add_mod off (d + 1)
            have : (d + 1) * (off / (d + 1)) = (off / (d + 1)) * (d + 1) := Nat.mul_comm _ _
            dsimp only [q, r, off] at *
            omega
          have hsp : (fun c : Fin (d + 1 + 1) => y (pos (i.val + c.val))) =
              splice (g q.castSucc) (g q.succ) r := by
            funext c
            unfold splice
            split
            · rename_i hlt
              rw [← hy_grid q.castSucc ⟨r.val + c.val, hlt⟩]
              congr 2; dsimp; omega
            · rename_i hge'
              rw [← hy_grid q.succ ⟨r.val + c.val - (d + 1), by have := c.isLt; omega⟩]
              congr 2
              have hmul : (q.val + 1) * (d + 1) = q.val * (d + 1) + (d + 1) := by ring
              dsimp; omega
          rw [hsp]
          exact hgstep q r
      dsimp only [buildP]
      split
      · rename_i hz
        rw [Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨?_, hbase_ok⟩
        simpa [hz, pos, L, w, D] using hbit0
      · exact hbase_ok
    · intro r
      have hy_a0 : ∀ c : Fin (d + 1), y (pos c.val) = a0 c := by
        intro c
        rw [hy_pad c.val (by have := c.isLt; omega)]
        congr 1; apply Fin.ext; exact Nat.mod_eq_of_lt c.isLt
      have hy_b0 : ∀ c : Fin (d + 1), y (pos (L + c.val)) = mkTrue v c := by
        intro c
        have hL : L = padding + (Fin.last (tests A (keyList d)).length).val * (d + 1) := by
          simp only [Fin.val_last, htslen, L, w]; ring
        rw [hL, hy_grid (Fin.last (tests A (keyList d)).length) c, hglast]
      refine Fin.cases ?_ ?_ r
      · simp only [buildQ, Fin.cases_zero, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          Fin.val_zero, Nat.add_zero, Fin.val_last]
        have hposw : pos (L + (d + 1)) = pos 0 := by
          apply Fin.ext
          change (L + (d + 1)) % (L + d + 1) = 0 % (L + d + 1)
          have : L + (d + 1) = L + d + 1 := by omega
          rw [this, Nat.mod_self, Nat.zero_mod]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · have h1 := hy_b0 0
          simpa [mkTrue, pos, L, w, D] using h1
        · change y (pos (L + (d + 1))) = a0 0
          rw [hposw]; exact hy_a0 0
        · intro c
          have h1 := hy_b0 ⟨c.val + 1, by omega⟩
          have h2 : mkTrue v ⟨c.val + 1, by omega⟩ = j c := by
            have h3 : (⟨c.val + 1, by omega⟩ : Fin (d + 1)) = Fin.succ ⟨c.val, by omega⟩ := rfl
            rw [h3]
            simp [mkTrue, v, combinePayload, c.isLt]
          rw [h2] at h1
          exact h1
        · have h1 := hy_b0 ⟨a + k.val + 1, by omega⟩
          have h2 : mkTrue v ⟨a + k.val + 1, by omega⟩ = x u j k := by
            have h3 : (⟨a + k.val + 1, by omega⟩ : Fin (d + 1)) =
                Fin.succ ⟨a + k.val, by omega⟩ := rfl
            rw [h3]
            simp only [mkTrue, Fin.cases_succ, v, combinePayload,
              show ¬ (a + k.val < a) by omega, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp; omega
          rw [h1, h2, hxk]
      · intro idx
        simp only [buildQ, Fin.cases_succ, beq_iff_eq, Fin.val_last]
        have hpos : pos (L + idx.succ.val + (d + 1)) = pos idx.succ.val := by
          apply Fin.ext
          change (L + idx.succ.val + (d + 1)) % (L + d + 1) = idx.succ.val % (L + d + 1)
          have : L + idx.succ.val + (d + 1) = idx.succ.val + (L + d + 1) := by omega
          rw [this, Nat.add_mod_right]
        change y (pos (L + idx.succ.val + (d + 1))) = a0 idx.succ
        rw [hpos]
        exact hy_a0 idx.succ

lemma sum_two_pow_matches (b : ℕ) (y : Fin b → Bool) :
    ∑ x : Fin b → Bool, (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = y i)).card) =
      (3 : ℝ) ^ b := by
  have hterm : ∀ x : Fin b → Bool,
      (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = y i)).card) =
        ∏ i : Fin b, (if x i = y i then (2 : ℝ) else 1) := by
    intro x
    simp [Finset.prod_ite]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i c => if c = y i then (2 : ℝ) else 1)]
  have h1 : ∀ i : Fin b, (∑ c : Bool, if c = y i then (2 : ℝ) else 1) = 3 := by
    intro i; cases y i <;> norm_num
  simp_rw [h1]
  simp

lemma amgm_bound (b coins S : ℕ) (_hb : 1 ≤ b) (hcoins : 0 < coins)
    (enc : Fin coins → (Fin b → Bool) → Fin S)
    (dec : Fin coins → Fin S → Fin b → Bool)
    (hacc : ∀ (x : Fin b → Bool) (i : Fin b),
      2 * coins ≤ 3 * (Finset.univ.filter (fun tape : Fin coins =>
        dec tape (enc tape x) i = x i)).card) :
    2 ^ b ≤ S ^ 15 := by
  have hsum_all : 2 * coins * (b * 2 ^ b) ≤
      3 * ∑ tape : Fin coins, ∑ x : Fin b → Bool,
        (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) i = x i)).card := by
    have h1 : ∑ x : Fin b → Bool, ∑ i : Fin b, 2 * coins ≤
        ∑ x : Fin b → Bool, ∑ i : Fin b,
          3 * (Finset.univ.filter (fun tape : Fin coins =>
            dec tape (enc tape x) i = x i)).card :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun i _ => hacc x i))
    have hlhs : (∑ _x : Fin b → Bool, ∑ _i : Fin b, 2 * coins) = 2 * coins * (b * 2 ^ b) := by
      simp [Finset.sum_const, smul_eq_mul]; ring
    rw [hlhs] at h1
    refine le_trans h1 ?_
    simp_rw [← Finset.mul_sum]
    apply Nat.mul_le_mul_left 3
    have hcard : ∀ (x : Fin b → Bool) (i : Fin b),
        (Finset.univ.filter (fun tape : Fin coins => dec tape (enc tape x) i = x i)).card =
          ∑ tape : Fin coins, if dec tape (enc tape x) i = x i then 1 else 0 := by
      intro x i; rw [Finset.card_filter]
    simp_rw [hcard]
    have hswap : (∑ x : Fin b → Bool, ∑ i : Fin b, ∑ tape : Fin coins,
        if dec tape (enc tape x) i = x i then 1 else 0) =
      ∑ tape : Fin coins, ∑ x : Fin b → Bool, ∑ i : Fin b,
        if dec tape (enc tape x) i = x i then 1 else 0 := by
      trans (∑ x : Fin b → Bool, ∑ tape : Fin coins, ∑ i : Fin b,
        if dec tape (enc tape x) i = x i then 1 else 0)
      · apply Finset.sum_congr rfl; intro x _; exact Finset.sum_comm
      · exact Finset.sum_comm
    rw [hswap]
    apply le_of_eq
    apply Finset.sum_congr rfl; intro tape _
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.card_filter]
  have hex_tape : ∃ tape : Fin coins,
      2 * b * 2 ^ b ≤ 3 * ∑ x : Fin b → Bool,
        (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) i = x i)).card := by
    by_contra hnone
    push Not at hnone
    have hlt : ∑ tape : Fin coins,
        3 * ∑ x : Fin b → Bool,
          (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) i = x i)).card <
        ∑ _tape : Fin coins, 2 * b * 2 ^ b := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, hcoins⟩, Finset.mem_univ _⟩
      · intro tape _; exact hnone tape
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have : coins * (2 * b * 2 ^ b) = 2 * coins * (b * 2 ^ b) := by ring
    omega
  obtain ⟨tape, htape⟩ := hex_tape
  let m : (Fin b → Bool) → ℕ := fun x =>
    (Finset.univ.filter (fun i : Fin b => x i = dec tape (enc tape x) i)).card
  have hm_eq : ∀ x, m x =
      (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) i = x i)).card := by
    intro x; dsimp [m]; congr 1; ext i; simp [eq_comm]
  have hsum_m : 2 * b * 2 ^ b ≤ 3 * ∑ x : Fin b → Bool, m x := by
    simpa [hm_eq] using htape
  have hupper : ∑ x : Fin b → Bool, (2 : ℝ) ^ (m x) ≤ (S : ℝ) * (3 : ℝ) ^ b := by
    have h1 : ∑ x : Fin b → Bool, (2 : ℝ) ^ (m x) =
        ∑ s : Fin S, ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
          (2 : ℝ) ^ (m x) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := enc tape) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    rw [h1]
    have h2 : ∀ s : Fin S,
        ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s), (2 : ℝ) ^ (m x) ≤
          (3 : ℝ) ^ b := by
      intro s
      have hcongr : ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s), (2 : ℝ) ^ (m x) =
          ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
            (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = dec tape s i)).card) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        simp only [m, hx.2]
      rw [hcongr]
      calc ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
              (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = dec tape s i)).card)
          ≤ ∑ x : Fin b → Bool,
              (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = dec tape s i)).card) :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = (3 : ℝ) ^ b := sum_two_pow_matches b (dec tape s)
    calc ∑ s : Fin S, ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
            (2 : ℝ) ^ (m x)
        ≤ ∑ _s : Fin S, (3 : ℝ) ^ b := Finset.sum_le_sum (fun s _ => h2 s)
      _ = (S : ℝ) * (3 : ℝ) ^ b := by simp
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hw_sum : ∑ _x : Fin b → Bool, (1 : ℝ) / (2 : ℝ) ^ b = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (Fin b → Bool) = 2 ^ b := by simp
    rw [hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin b → Bool))
    (fun _ => (1 : ℝ) / (2 : ℝ) ^ b) (fun x => (2 : ℝ) ^ (m x))
    (fun _ _ => by positivity) hw_sum (fun _ _ => by positivity)
  have hlhs_gm : ∏ x : Fin b → Bool, ((2 : ℝ) ^ (m x)) ^ ((1 : ℝ) / (2 : ℝ) ^ b) =
      (2 : ℝ) ^ ((∑ x : Fin b → Bool, (m x : ℝ)) / (2 : ℝ) ^ b) := by
    have h1 : ∀ x : Fin b → Bool,
        ((2 : ℝ) ^ (m x)) ^ ((1 : ℝ) / (2 : ℝ) ^ b) =
          (2 : ℝ) ^ ((m x : ℝ) / (2 : ℝ) ^ b) := by
      intro x
      rw [← Real.rpow_natCast (2 : ℝ) (m x), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    simp_rw [h1]
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2), ← Finset.sum_div]
  rw [hlhs_gm] at hamgm
  have hrhs_am : ∑ x : Fin b → Bool, (1 : ℝ) / (2 : ℝ) ^ b * (2 : ℝ) ^ (m x) ≤
      (S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b := by
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hupper (le_of_lt h2b_pos)
  have hexp_ge : (2 : ℝ) * (b : ℝ) / 3 ≤ (∑ x : Fin b → Bool, (m x : ℝ)) / (2 : ℝ) ^ b := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) h2b_pos]
    have hcast : (2 * b * 2 ^ b : ℝ) ≤ 3 * ∑ x : Fin b → Bool, (m x : ℝ) := by
      exact_mod_cast hsum_m
    linarith
  have h2_le : (2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3) ≤ (S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_ge)
      (le_trans hamgm hrhs_am)
  have hcube : ((2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3)) ^ (3 : ℕ) ≤
      ((S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) h2_le 3
  have hcube_lhs : ((2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3)) ^ (3 : ℕ) = (4 : ℝ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : (2 : ℝ) * (b : ℝ) / 3 * (3 : ℕ) = (2 * b : ℕ) := by push_cast; ring
    rw [this, Real.rpow_natCast, pow_mul]
    norm_num
  rw [hcube_lhs, div_pow, mul_pow, le_div_iff₀ (by positivity : (0 : ℝ) < ((2 : ℝ) ^ b) ^ 3)] at hcube
  have h32 : (32 : ℝ) ^ b ≤ (27 : ℝ) ^ b * (S : ℝ) ^ 3 := by
    have h1 : (4 : ℝ) ^ b * ((2 : ℝ) ^ b) ^ 3 = (32 : ℝ) ^ b := by
      rw [← pow_mul, mul_comm b 3, pow_mul, ← mul_pow]
      norm_num
    have h2 : ((3 : ℝ) ^ b) ^ 3 = (27 : ℝ) ^ b := by
      rw [← pow_mul, mul_comm b 3, pow_mul]
      norm_num
    rw [h1, h2] at hcube
    linarith
  have h5 : ((32 : ℝ) ^ b) ^ 5 ≤ ((27 : ℝ) ^ b * (S : ℝ) ^ 3) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h32 5
  have h5_lhs : (2 : ℝ) ^ b * ((27 : ℝ) ^ b) ^ 5 ≤ ((32 : ℝ) ^ b) ^ 5 := by
    have h1 : (2 : ℝ) ^ b * ((27 : ℝ) ^ b) ^ 5 = ((2 : ℝ) * 27 ^ 5) ^ b := by
      rw [← pow_mul, mul_comm b 5, pow_mul, ← mul_pow]
    have h2 : ((32 : ℝ) ^ b) ^ 5 = ((32 : ℝ) ^ 5) ^ b := by
      rw [← pow_mul, mul_comm b 5, pow_mul]
    rw [h1, h2]
    apply pow_le_pow_left₀ (by positivity)
    norm_num
  have h5_rhs : ((27 : ℝ) ^ b * (S : ℝ) ^ 3) ^ 5 = ((27 : ℝ) ^ b) ^ 5 * (S : ℝ) ^ 15 := by
    rw [mul_pow, ← pow_mul (S : ℝ) 3 5]
  have hfinal_r : (2 : ℝ) ^ b ≤ (S : ℝ) ^ 15 := by
    have hpos27 : (0 : ℝ) < ((27 : ℝ) ^ b) ^ 5 := by positivity
    nlinarith
  exact_mod_cast hfinal_r

lemma binom_bound (d K : ℕ) (hd : 1 ≤ d) (hKlo : 2 ^ (d + 1) ≤ K) (hKhi : K ≤ 4 ^ (d + 1)) :
    let D := 2 ^ d
    let a := min (d - 1) (Nat.log2 ((K - D) / D))
    let bits := max 1 (D * 2 ^ a * (d - a))
    let U := ∑ j ∈ Finset.range (K + 1), (4 ^ (d + 1)).choose j
    U ≤ 2 ^ (8 * bits) := by
  intro D a bits U
  have hDpos : 0 < D := by positivity
  have ha_le : a ≤ d - 1 := min_le_left _ _
  have hda : 1 ≤ d - a := by omega
  have hbits_pos : 1 ≤ D * 2 ^ a * (d - a) :=
    Nat.mul_pos (Nat.mul_pos hDpos (by positivity)) hda
  have hbits : bits = D * 2 ^ a * (d - a) := max_eq_right hbits_pos
  have h4w : 4 ^ (d + 1) = 4 * D * D := by
    dsimp [D]
    rw [pow_succ, show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
    ring
  by_cases ha_eq : a = d - 1
  · have h8bits : 8 * bits = 4 ^ (d + 1) := by
      rw [hbits, ha_eq, show d - (d - 1) = 1 by omega, mul_one, h4w]
      have h2a : 2 * 2 ^ (d - 1) = D := by
        dsimp [D]
        rw [← pow_succ', Nat.sub_add_cancel hd]
      nlinarith
    rw [h8bits]
    calc U ≤ ∑ j ∈ Finset.range (4 ^ (d + 1) + 1), (4 ^ (d + 1)).choose j :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      _ = 2 ^ (4 ^ (d + 1)) := Nat.sum_range_choose (4 ^ (d + 1))
  · have ha_lt : a < d - 1 := by omega
    have hda2 : 2 ≤ d - a := by omega
    have ha_log : a = Nat.log2 ((K - D) / D) := by
      have : a = min (d - 1) (Nat.log2 ((K - D) / D)) := rfl
      omega
    have hdiv_lt : (K - D) / D < 2 ^ (a + 1) := by
      rw [ha_log]
      have hne : (K - D) / D ≠ 0 := by
        have h2w : 2 * D ≤ K := by
          simpa [D, pow_succ, mul_comm] using hKlo
        have h1 : D ≤ K - D := by omega
        exact Nat.ne_of_gt (Nat.div_pos h1 hDpos)
      exact (Nat.log2_lt hne).mp (Nat.lt_succ_self _)
    have hK_le : K ≤ 3 * D * 2 ^ a := by
      have h1 : K - D < 2 ^ (a + 1) * D := (Nat.div_lt_iff_lt_mul hDpos).mp hdiv_lt
      have h2 : 2 ^ (a + 1) * D = 2 * D * 2 ^ a := by rw [pow_succ]; ring
      have h3 : D ≤ D * 2 ^ a := Nat.le_mul_of_pos_right D (by positivity)
      have h4 : 3 * D * 2 ^ a = D * 2 ^ a + 2 * D * 2 ^ a := by ring
      omega
    let q := 2 ^ (d - a)
    have hq_pos : 0 < q := by positivity
    have h2aq : 2 ^ a * q = D := by
      dsimp [q, D]
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have h4w_q : 4 ^ (d + 1) = (4 * D * 2 ^ a) * q := by
      rw [h4w, ← h2aq]; ring
    have hnat : U * q ^ (4 ^ (d + 1) - K) ≤ (1 + q) ^ (4 ^ (d + 1)) := by
      rw [Finset.sum_mul, add_pow]
      calc ∑ j ∈ Finset.range (K + 1), (4 ^ (d + 1)).choose j * q ^ (4 ^ (d + 1) - K)
          ≤ ∑ j ∈ Finset.range (K + 1),
              1 ^ j * q ^ (4 ^ (d + 1) - j) * (4 ^ (d + 1)).choose j := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_range] at hj
            rw [one_pow, one_mul, mul_comm]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq_pos (by omega))
        _ ≤ ∑ j ∈ Finset.range (4 ^ (d + 1) + 1),
              1 ^ j * q ^ (4 ^ (d + 1) - j) * (4 ^ (d + 1)).choose j :=
            Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have hreal : (U : ℝ) ≤ (2 : ℝ) ^ (8 * bits) := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
      have hnatR : (U : ℝ) * (q : ℝ) ^ (4 ^ (d + 1) - K) ≤ (1 + (q : ℝ)) ^ (4 ^ (d + 1)) := by
        exact_mod_cast hnat
      have hU_le : (U : ℝ) ≤ (q : ℝ) ^ K * (1 + 1 / (q : ℝ)) ^ (4 ^ (d + 1)) := by
        rw [← le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ (4 ^ (d + 1) - K))] at hnatR
        refine le_trans hnatR (le_of_eq ?_)
        have h1 : (1 + (q : ℝ)) = (q : ℝ) * (1 + 1 / (q : ℝ)) := by field_simp; ring
        rw [h1, mul_pow, mul_div_right_comm, div_eq_mul_inv, ← pow_sub₀ _ (ne_of_gt hqR) (Nat.sub_le _ _)]
        have : 4 ^ (d + 1) - (4 ^ (d + 1) - K) = K := Nat.sub_sub_self hKhi
        rw [this]
      have hexp1 : (1 + 1 / (q : ℝ)) ^ (4 ^ (d + 1)) ≤ Real.exp (4 * D * 2 ^ a : ℕ) := by
        calc (1 + 1 / (q : ℝ)) ^ (4 ^ (d + 1))
            ≤ (Real.exp (1 / (q : ℝ))) ^ (4 ^ (d + 1)) := by
              apply pow_le_pow_left₀ (by positivity)
              simpa [add_comm] using Real.add_one_le_exp (1 / (q : ℝ))
          _ = Real.exp ((4 ^ (d + 1) : ℕ) * (1 / (q : ℝ))) := by
              rw [← Real.exp_nat_mul]
          _ = Real.exp (4 * D * 2 ^ a : ℕ) := by
              congr 1
              rw [h4w_q, Nat.cast_mul]
              field_simp
      have hexp2 : Real.exp (4 * D * 2 ^ a : ℕ) ≤ (2 : ℝ) ^ (8 * D * 2 ^ a) := by
        have he4 : Real.exp 1 ≤ 4 := by
          have := Real.exp_one_lt_d9
          linarith
        calc Real.exp (4 * D * 2 ^ a : ℕ)
            = (Real.exp 1) ^ (4 * D * 2 ^ a) := by rw [← Real.exp_nat_mul, mul_one]
          _ ≤ (4 : ℝ) ^ (4 * D * 2 ^ a) := pow_le_pow_left₀ (by positivity) he4 _
          _ = (2 : ℝ) ^ (8 * D * 2 ^ a) := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
              congr 1; ring
      have hqK : (q : ℝ) ^ K ≤ (2 : ℝ) ^ (3 * bits) := by
        have hq2 : (q : ℝ) = (2 : ℝ) ^ (d - a) := by dsimp [q]; push_cast; rfl
        rw [hq2, ← pow_mul]
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        rw [hbits]
        have : (d - a) * K ≤ (d - a) * (3 * D * 2 ^ a) := Nat.mul_le_mul_left _ hK_le
        linarith
      have h8le : 8 * D * 2 ^ a ≤ 4 * bits := by
        rw [hbits]
        have : 2 * (4 * D * 2 ^ a) ≤ (d - a) * (4 * D * 2 ^ a) :=
          Nat.mul_le_mul_right _ hda2
        linarith
      calc (U : ℝ)
          ≤ (q : ℝ) ^ K * (1 + 1 / (q : ℝ)) ^ (4 ^ (d + 1)) := hU_le
        _ ≤ (2 : ℝ) ^ (3 * bits) * (2 : ℝ) ^ (8 * D * 2 ^ a) :=
            mul_le_mul hqK (le_trans hexp1 hexp2) (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (3 * bits + 8 * D * 2 ^ a) := by rw [← pow_add]
        _ ≤ (2 : ℝ) ^ (8 * bits) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    exact_mod_cast hreal

lemma case_zero (padding K coins S : ℕ)
    (hcoins : 0 < coins) (hKlo : 2 ^ 1 ≤ K) (hKhi : K ≤ 4 ^ 1) :
    let w := 1
    let L := padding + 3 * 1 * 2 ^ 0
    let n := L + 0 + 1
    let pos := fun t : ℕ => Fin.ofNat (L + 0 + 1) t
    let Part := fun len : ℕ => Fin len → (Fin (w + 1) → Bool) → Bool
    let reached := fun (P : Part L) (h : ℕ) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
        ∀ i : Fin L, i.val < h → P i (fun j => word (pos (i.val + j.val))) = true)).image
        (fun x => ((fun k : Fin w => x (pos k.val)), (fun l : Fin w => x (pos (h + l.val)))))
    let accepts := fun (firstRows : Part L) (lastRows : Part w) =>
      ∃ y : Fin n → Bool,
        (∀ i : Fin L, firstRows i (fun a => y (pos (i.val + a.val))) = true) ∧
        ∀ r : Fin w, lastRows r (fun z => y (pos (L + r.val + z.val))) = true
    ∀ (send : Fin coins → Part L → Fin S) (finish : Fin coins → Fin S → Part w → Bool),
      (∀ (P : Part L) (Q : Part w), (∀ h ≤ L, (reached P h).card ≤ K) →
        2 * coins ≤ 3 * ((Finset.univ : Finset (Fin coins)).filter
          (fun tape => (finish tape (send tape P) Q = true ↔ accepts P Q))).card) →
      2 ^ (max 1 (2 ^ 0 * 2 ^ (min (0 - 1) (Nat.log2 ((K - 2 ^ 0) / 2 ^ 0))) *
        (0 - min (0 - 1) (Nat.log2 ((K - 2 ^ 0) / 2 ^ 0))))) ≤ S ^ 15 ∧
      ∑ j ∈ Finset.range (K + 1), (4 ^ 1).choose j ≤ S ^ 120 := by
  intro w L n pos Part reached accepts send finish hprot
  let P0 : Part L := fun _ _ => false
  let P1 : Part L := fun _ p => !p 0 && !p 1
  let Q : Part w := fun _ _ => true
  have hLpos : 0 < L := by dsimp [L]; omega
  have hR0 : ∀ h ≤ L, (reached P0 h).card ≤ K := by
    intro h hh
    by_cases hh0 : h = 0
    · subst hh0
      have hsub : reached P0 0 ⊆ (Finset.univ : Finset (Word w)).image (fun a => (a, a)) := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨word, _, rfl⟩
        refine Finset.mem_image.mpr ⟨fun k : Fin w => word (pos k.val), Finset.mem_univ _, ?_⟩
        ext <;> simp
      calc (reached P0 0).card
          ≤ ((Finset.univ : Finset (Word w)).image (fun a => (a, a))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Word w)).card := Finset.card_image_le
        _ = 2 ^ 1 := by simp [Word, w]
        _ ≤ K := hKlo
    · have hempty : reached P0 h = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨word, hword, _⟩
        rw [Finset.mem_filter] at hword
        have := hword.2 ⟨0, hLpos⟩ (Nat.pos_of_ne_zero hh0)
        simp [P0] at this
      rw [hempty]; simp
  have hR1 : ∀ h ≤ L, (reached P1 h).card ≤ K := by
    intro h hh
    by_cases hh0 : h = 0
    · subst hh0
      have hsub : reached P1 0 ⊆ (Finset.univ : Finset (Word w)).image (fun a => (a, a)) := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨word, _, rfl⟩
        refine Finset.mem_image.mpr ⟨fun k : Fin w => word (pos k.val), Finset.mem_univ _, ?_⟩
        ext <;> simp
      calc (reached P1 0).card
          ≤ ((Finset.univ : Finset (Word w)).image (fun a => (a, a))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Word w)).card := Finset.card_image_le
        _ = 2 ^ 1 := by simp [Word, w]
        _ ≤ K := hKlo
    · have hsub : reached P1 h ⊆ {((fun _ : Fin w => false), (fun _ : Fin w => false))} := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨word, hword, rfl⟩
        rw [Finset.mem_filter] at hword
        rw [Finset.mem_singleton]
        have h0 := hword.2 ⟨0, hLpos⟩ (Nat.pos_of_ne_zero hh0)
        have hlast := hword.2 ⟨h - 1, by omega⟩ (show h - 1 < h by omega)
        simp only [P1, Bool.and_eq_true, Bool.not_eq_true', Fin.val_zero, Nat.add_zero] at h0 hlast
        have hlast1 : word (pos h) = false := by
          have h1 : (1 : Fin (w + 1)).val = 1 := rfl
          have h2 : h - 1 + 1 = h := by omega
          have h3 := hlast.2
          rw [h1, h2] at h3
          exact h3
        apply Prod.ext
        · funext k; have hk : k = 0 := Fin.ext (by have := k.isLt; dsimp [w] at this; omega)
          subst hk; simpa using h0.1
        · funext l; have hl : l = 0 := Fin.ext (by have := l.isLt; dsimp [w] at this; omega)
          subst hl; simpa using hlast1
      calc (reached P1 h).card
          ≤ ({((fun _ : Fin w => false), (fun _ : Fin w => false))} : Finset _).card :=
            Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ ≤ K := by omega
  have hacc0 : ¬ accepts P0 Q := by
    rintro ⟨y, hy, _⟩
    have := hy ⟨0, hLpos⟩
    simp [P0] at this
  have hacc1 : accepts P1 Q := ⟨fun _ => false, fun _ => rfl, fun _ => rfl⟩
  let A0 := Finset.univ.filter (fun tape : Fin coins => finish tape (send tape P0) Q = true ↔ accepts P0 Q)
  let A1 := Finset.univ.filter (fun tape : Fin coins => finish tape (send tape P1) Q = true ↔ accepts P1 Q)
  have hc0 : 2 * coins ≤ 3 * A0.card := hprot P0 Q hR0
  have hc1 : 2 * coins ≤ 3 * A1.card := hprot P1 Q hR1
  have hinter : (A0 ∩ A1).Nonempty := by
    apply Finset.card_pos.mp
    have hu := Finset.card_union_add_card_inter A0 A1
    have hle : (A0 ∪ A1).card ≤ coins := by
      calc (A0 ∪ A1).card ≤ (Finset.univ : Finset (Fin coins)).card := Finset.card_le_univ _
        _ = coins := by simp
    omega
  obtain ⟨tape, htape⟩ := hinter
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at htape
  have hne : send tape P0 ≠ send tape P1 := by
    intro heq
    have h0 : finish tape (send tape P0) Q ≠ true := fun h => hacc0 (htape.1.2.mp h)
    have h1 : finish tape (send tape P1) Q = true := htape.2.2.mpr hacc1
    rw [heq] at h0
    exact h0 h1
  have hS2 : 2 ≤ S := by
    by_contra hlt
    have hS1 : S ≤ 1 := by omega
    apply hne
    apply Fin.ext
    have := (send tape P0).isLt
    have := (send tape P1).isLt
    omega
  have hU16 : ∑ j ∈ Finset.range (K + 1), (4 ^ 1).choose j ≤ 16 := by
    calc ∑ j ∈ Finset.range (K + 1), (4 ^ 1).choose j
        ≤ ∑ j ∈ Finset.range (4 ^ 1 + 1), (4 ^ 1).choose j :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      _ = 2 ^ (4 ^ 1) := Nat.sum_range_choose 4
      _ = 16 := by norm_num
  have hbits0 : max 1 (2 ^ 0 * 2 ^ (min (0 - 1) (Nat.log2 ((K - 2 ^ 0) / 2 ^ 0))) *
      (0 - min (0 - 1) (Nat.log2 ((K - 2 ^ 0) / 2 ^ 0)))) = 1 := by
    simp
  constructor
  · rw [hbits0, pow_one]
    calc 2 ≤ S := hS2
      _ ≤ S ^ 15 := Nat.le_self_pow (by omega) S
  · calc ∑ j ∈ Finset.range (K + 1), (4 ^ 1).choose j
        ≤ 16 := hU16
      _ ≤ 2 ^ 120 := by norm_num
      _ ≤ S ^ 120 := Nat.pow_le_pow_left hS2 120

end PEqualNP.Outside.L_clb_069_aux

open PEqualNP.Outside.L_clb_069_aux in
theorem PEqualNP.Outside.L_clb_069 : (∀ d padding K coins S : ℕ,
  let w := d + 1
  let D := 2 ^ d
  let L := padding + 3 * w * D
  let n := L + d + 1
  let pos := fun t : ℕ => Fin.ofNat (L + d + 1) t
  let Part := fun len : ℕ => Fin len → (Fin (w + 1) → Bool) → Bool
  let reached := fun (P : Part L) (h : ℕ) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun word =>
      ∀ i : Fin L, i.val < h → P i (fun j => word (pos (i.val + j.val))) = true)).image
      (fun x => ((fun k : Fin w => x (pos k.val)), (fun l : Fin w => x (pos (h + l.val)))))
  let accepts := fun (firstRows : Part L) (lastRows : Part w) =>
    ∃ y : Fin n → Bool,
      (∀ i : Fin L, firstRows i (fun a => y (pos (i.val + a.val))) = true) ∧
      ∀ r : Fin w, lastRows r (fun z => y (pos (L + r.val + z.val))) = true
  let a := min (d - 1) (Nat.log2 ((K - D) / D))
  let bits := max 1 (D * 2 ^ a * (d - a))
  let U := ∑ j ∈ Finset.range (K + 1), (4 ^ w).choose j
  0 < coins → 2 ^ w ≤ K → K ≤ 4 ^ w →
    ∀ (send : Fin coins → Part L → Fin S) (finish : Fin coins → Fin S → Part w → Bool),
      (∀ (P : Part L) (Q : Part w), (∀ h ≤ L, (reached P h).card ≤ K) →
        2 * coins ≤ 3 * ((Finset.univ : Finset (Fin coins)).filter
          (fun tape => (finish tape (send tape P) Q = true ↔ accepts P Q))).card) →
      2 ^ bits ≤ S ^ 15 ∧ U ≤ S ^ 120) := by
  intro d padding K coins S w D L n pos Part reached accepts a bits U hcoins hKlo hKhi send finish hprot
  by_cases hd0 : d = 0
  · subst hd0
    exact case_zero padding K coins S hcoins hKlo hKhi send finish hprot
  · have hd : 1 ≤ d := Nat.pos_of_ne_zero hd0
    have ha_lt : a < d := by
      have : a ≤ d - 1 := min_le_left _ _
      omega
    have hDpos : 0 < D := by positivity
    have h2a_le : D + D * 2 ^ a ≤ K := by
      have h2w : 2 * D ≤ K := by
        simpa [D, w, pow_succ, mul_comm] using hKlo
      have hdiv_pos : 1 ≤ (K - D) / D := Nat.div_pos (by omega) hDpos
      have hlog : 2 ^ Nat.log2 ((K - D) / D) ≤ (K - D) / D :=
        Nat.log2_self_le (Nat.ne_of_gt hdiv_pos)
      have hpow : 2 ^ a ≤ (K - D) / D :=
        le_trans (Nat.pow_le_pow_right (by omega) (min_le_right _ _)) hlog
      have hmul : D * 2 ^ a ≤ K - D :=
        le_trans (Nat.mul_le_mul_left D hpow) (Nat.mul_div_le (K - D) D)
      omega
    have hbits_pos : 1 ≤ D * 2 ^ a * (d - a) :=
      Nat.mul_pos (Nat.mul_pos hDpos (by positivity)) (by omega)
    have hbits_eq : bits = D * 2 ^ a * (d - a) := max_eq_right hbits_pos
    let Idx := Payload d × (Fin a → Bool) × Fin (d - a)
    have hcard_idx : Fintype.card Idx = bits := by
      rw [hbits_eq]
      simp [Idx, Payload, Word, D]
      ring
    let eIdx : Idx ≃ Fin bits := Fintype.equivFinOfCardEq hcard_idx
    let toTable : (Fin bits → Bool) → Payload d → (Fin a → Bool) → Fin (d - a) → Bool :=
      fun x u j k => x (eIdx (u, j, k))
    let enc : Fin coins → (Fin bits → Bool) → Fin S :=
      fun tape x => send tape (buildP d padding (matrixOf ha_lt (toTable x)))
    let dec : Fin coins → Fin S → Fin bits → Bool :=
      fun tape s i =>
        let p := eIdx.symm i
        finish tape s (buildQ d padding a ha_lt p.1 p.2.1 p.2.2)
    have hacc : ∀ (x : Fin bits → Bool) (i : Fin bits),
        2 * coins ≤ 3 * (Finset.univ.filter (fun tape : Fin coins =>
          dec tape (enc tape x) i = x i)).card := by
      intro x i
      let p := eIdx.symm i
      have hR : ∀ h ≤ L, (reached (buildP d padding (matrixOf ha_lt (toTable x))) h).card ≤ K := by
        intro h hh
        apply buildP_reached_card d padding K (matrixOf ha_lt (toTable x)) hKlo _ h hh
        simp_rw [matrixOf_row_card ha_lt (toTable x)]
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hcard : Fintype.card (Payload d) = D := by simp [Payload, Word, D]
        rw [hcard]
        exact h2a_le
      have hp := hprot (buildP d padding (matrixOf ha_lt (toTable x)))
        (buildQ d padding a ha_lt p.1 p.2.1 p.2.2) hR
      have hiff : ∀ tape : Fin coins,
          (finish tape (send tape (buildP d padding (matrixOf ha_lt (toTable x))))
            (buildQ d padding a ha_lt p.1 p.2.1 p.2.2) = true ↔
            accepts (buildP d padding (matrixOf ha_lt (toTable x)))
              (buildQ d padding a ha_lt p.1 p.2.1 p.2.2)) ↔
          dec tape (enc tape x) i = x i := by
        intro tape
        have hba := build_accepts_iff d padding a ha_lt (toTable x) p.1 p.2.1 p.2.2
        dsimp only [accepts, pos, L, w, D]
        rw [hba]
        have hxi : toTable x p.1 p.2.1 p.2.2 = x i := by
          simp [toTable, p]
        rw [hxi]
        change (dec tape (enc tape x) i = true ↔ x i = true) ↔ dec tape (enc tape x) i = x i
        cases dec tape (enc tape x) i <;> cases x i <;> simp
      simpa [hiff] using hp
    have hS15 : 2 ^ bits ≤ S ^ 15 :=
      amgm_bound bits coins S (by omega) hcoins enc dec hacc
    have hU8 : U ≤ 2 ^ (8 * bits) := binom_bound d K hd hKlo hKhi
    refine ⟨hS15, ?_⟩
    calc U ≤ 2 ^ (8 * bits) := hU8
      _ = (2 ^ bits) ^ 8 := by rw [← pow_mul, mul_comm]
      _ ≤ (S ^ 15) ^ 8 := Nat.pow_le_pow_left hS15 8
      _ = S ^ 120 := by rw [← pow_mul]
