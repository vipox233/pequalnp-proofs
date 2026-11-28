import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42250_aux

def xorList (l : List Bool) : Bool :=
  l.foldl xor false

def xorFin {m : Nat} (f : Fin m → Bool) : Bool :=
  (List.finRange m).foldl (fun a i => xor a (f i)) false

lemma foldl_xor_init (l : List Bool) (a : Bool) :
    l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, List.foldl_cons, Bool.false_xor, ih, ih b]
    cases a <;> cases b <;> cases bs.foldl xor false <;> rfl

lemma foldl_map_xor_init {α : Type} (l : List α) (f : α → Bool) (a : Bool) :
    l.foldl (fun s x => xor s (f x)) a = xor a (l.foldl (fun s x => xor s (f x)) false) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, Bool.false_xor, ih, ih (f x)]
    cases a <;> cases f x <;> cases xs.foldl (fun s y => xor s (f y)) false <;> rfl

lemma foldl_map_xor_append {α : Type} (l1 l2 : List α) (f : α → Bool) :
    (l1 ++ l2).foldl (fun s x => xor s (f x)) false =
      xor (l1.foldl (fun s x => xor s (f x)) false)
          (l2.foldl (fun s x => xor s (f x)) false) := by
  rw [List.foldl_append, foldl_map_xor_init]

lemma foldl_map_xor_xor {α : Type} (l : List α) (f g : α → Bool) :
    l.foldl (fun s x => xor s (xor (f x) (g x))) false =
      xor (l.foldl (fun s x => xor s (f x)) false)
          (l.foldl (fun s x => xor s (g x)) false) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [foldl_map_xor_init xs (fun y => xor (f y) (g y)), foldl_map_xor_init xs f,
      foldl_map_xor_init xs g, ih]
    cases f x <;> cases g x <;>
      cases xs.foldl (fun s y => xor s (f y)) false <;>
      cases xs.foldl (fun s y => xor s (g y)) false <;> rfl

lemma foldl_map_xor_false {α : Type} (l : List α) :
    l.foldl (fun s (_ : α) => xor s false) false = false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, Bool.false_xor, ih]

lemma foldl_map_xor_and_left {α : Type} (l : List α) (c : Bool) (f : α → Bool) :
    l.foldl (fun s x => xor s (c && f x)) false =
      (c && l.foldl (fun s x => xor s (f x)) false) := by
  cases c
  · exact foldl_map_xor_false l
  · simp

lemma foldl_map_xor_and_right {α : Type} (l : List α) (f : α → Bool) (c : Bool) :
    l.foldl (fun s x => xor s (f x && c)) false =
      (l.foldl (fun s x => xor s (f x)) false && c) := by
  cases c
  · simp only [Bool.and_false]; exact foldl_map_xor_false l
  · simp

lemma foldl_map_xor_congr {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun s x => xor s (f x)) false = l.foldl (fun s x => xor s (g x)) false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [h x List.mem_cons_self, foldl_map_xor_init xs f, foldl_map_xor_init xs g,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

lemma foldl_map_xor_eq_false {α : Type} (l : List α) (f : α → Bool)
    (h : ∀ x ∈ l, f x = false) :
    l.foldl (fun s x => xor s (f x)) false = false := by
  rw [foldl_map_xor_congr l f (fun _ => false) h, foldl_map_xor_false]

lemma foldl_map_xor_single {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (a : α) (ha : a ∈ l) (c : Bool) :
    l.foldl (fun s x => xor s (if x = a then c else false)) false = c := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons, foldl_map_xor_init]
    rcases List.mem_cons.mp ha with rfl | hmem
    · simp only [ite_true, Bool.false_xor]
      rw [foldl_map_xor_eq_false xs _ (fun y hy => by
        have hne : y ≠ a := fun he => hl.1 (he ▸ hy)
        simp [hne])]
      simp
    · have hne : x ≠ a := fun he => hl.1 (he ▸ hmem)
      simp only [hne, ite_false, Bool.false_xor]
      exact ih hl.2 hmem

lemma xorFin_xor {m : Nat} (f g : Fin m → Bool) :
    xorFin (fun i => xor (f i) (g i)) = xor (xorFin f) (xorFin g) :=
  foldl_map_xor_xor _ f g

lemma xorFin_false {m : Nat} : xorFin (fun _ : Fin m => false) = false :=
  foldl_map_xor_false _

lemma xorFin_congr {m : Nat} (f g : Fin m → Bool) (h : ∀ i, f i = g i) :
    xorFin f = xorFin g :=
  foldl_map_xor_congr _ f g (fun i _ => h i)

lemma xorFin_cast {m1 m2 : Nat} (h : m1 = m2) (f : Fin m1 → Bool) (g : Fin m2 → Bool)
    (hfg : ∀ i (hi1 : i < m1) (hi2 : i < m2), f ⟨i, hi1⟩ = g ⟨i, hi2⟩) :
    xorFin f = xorFin g := by
  subst h
  exact xorFin_congr f g (fun i => hfg i.val i.isLt i.isLt)

lemma xorFin_eq_false {m : Nat} (f : Fin m → Bool) (h : ∀ i, f i = false) :
    xorFin f = false :=
  foldl_map_xor_eq_false _ f (fun i _ => h i)

lemma xorFin_and_left {m : Nat} (c : Bool) (f : Fin m → Bool) :
    xorFin (fun i => c && f i) = (c && xorFin f) :=
  foldl_map_xor_and_left _ c f

lemma xorFin_and_right {m : Nat} (f : Fin m → Bool) (c : Bool) :
    xorFin (fun i => f i && c) = (xorFin f && c) :=
  foldl_map_xor_and_right _ f c

lemma xorFin_single {m : Nat} (j : Fin m) (c : Bool) :
    xorFin (fun i : Fin m => if i = j then c else false) = c :=
  foldl_map_xor_single (List.finRange m) (List.nodup_finRange m) j (List.mem_finRange j) c

lemma xorFin_single' {m : Nat} (j : Fin m) (f : Fin m → Bool) (h : ∀ i, i ≠ j → f i = false) :
    xorFin f = f j := by
  have heq : xorFin f = xorFin (fun i => if i = j then f j else false) :=
    xorFin_congr f _ (fun i => by by_cases hij : i = j <;> simp [hij, h])
  rw [heq, xorFin_single]

lemma xorFin_succ {m : Nat} (f : Fin (m + 1) → Bool) :
    xorFin f = xor (xorFin (fun i : Fin m => f i.castSucc)) (f (Fin.last m)) := by
  unfold xorFin
  have hfr : List.finRange (m + 1) =
      (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      by_cases hi : i < m
      · rw [List.getElem_append_left (by simp [hi])]
        apply Fin.ext
        simp
      · have hie : i = m := by simp at h1; omega
        subst hie
        rw [List.getElem_append_right (by simp)]
        simp [Fin.ext_iff]
  rw [hfr, foldl_map_xor_append]
  have h1 : ((List.finRange m).map Fin.castSucc).foldl (fun s x => xor s (f x)) false =
      (List.finRange m).foldl (fun s i => xor s (f i.castSucc)) false := by
    rw [List.foldl_map]
  rw [h1]
  simp

lemma xorFin_head_tail {m : Nat} (g : Fin (m + 1) → Bool) :
    xorFin g = xor (g ⟨0, Nat.zero_lt_succ m⟩) (xorFin (fun j : Fin m => g j.succ)) := by
  unfold xorFin
  have hfr : List.finRange (m + 1) = ⟨0, Nat.zero_lt_succ m⟩ :: (List.finRange m).map Fin.succ := by
    apply List.ext_getElem
    · simp
    · intro idx _ _; cases idx <;> apply Fin.ext <;> simp
  rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]

lemma xorFin_const (m : Nat) (c : Bool) :
    xorFin (fun _ : Fin m => c) = (c && decide (m % 2 = 1)) := by
  induction m with
  | zero => simp [xorFin]
  | succ m ih =>
    rw [xorFin_succ, ih]
    cases c
    · rfl
    · simp only [Bool.true_and]
      by_cases hm : m % 2 = 1
      · have hm1 : (m + 1) % 2 ≠ 1 := by omega
        simp [hm, hm1]
      · have hm1 : (m + 1) % 2 = 1 := by omega
        simp [hm, hm1]

lemma xorFin_first {m : Nat} (hm : 1 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (f ⟨0, by omega⟩) (xorFin (fun j : Fin (m - 1) => f ⟨j.val + 1, by omega⟩)) := by
  have he : m = (m - 1) + 1 := by omega
  rw [xorFin_cast he f (fun j : Fin ((m - 1) + 1) => f ⟨j.val, by omega⟩) (fun _ _ _ => rfl),
    xorFin_head_tail]
  apply congrArg (xor _)
  apply xorFin_congr; intro j; exact congrArg f (Fin.ext (by simp only [Fin.val_succ]))

lemma xorFin_last {m : Nat} (hm : 1 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (xorFin (fun j : Fin (m - 1) => f ⟨j.val, by omega⟩)) (f ⟨m - 1, by omega⟩) := by
  have he : m = (m - 1) + 1 := by omega
  rw [xorFin_cast he f (fun j : Fin ((m - 1) + 1) => f ⟨j.val, by omega⟩) (fun _ _ _ => rfl),
    xorFin_succ]
  rfl

lemma xorFin_ends {m : Nat} (hm : 2 ≤ m) (f : Fin m → Bool) :
    xorFin f = xor (f ⟨0, by omega⟩)
                   (xor (xorFin (fun j : Fin (m - 2) => f ⟨j.val + 1, by omega⟩))
                        (f ⟨m - 1, by omega⟩)) := by
  rw [xorFin_first (by omega) f, xorFin_last (by omega)]
  apply congrArg (xor _)
  have h1 : xorFin (fun j : Fin (m - 1 - 1) => f ⟨j.val + 1, by omega⟩) =
      xorFin (fun j : Fin (m - 2) => f ⟨j.val + 1, by omega⟩) :=
    xorFin_cast (by omega) _ _ (fun _ _ _ => rfl)
  have h2 : f ⟨m - 1 - 1 + 1, by omega⟩ = f ⟨m - 1, by omega⟩ :=
    congrArg f (Fin.ext (by dsimp only; omega))
  rw [h1, h2]

lemma xorFin_swap {a b : Nat} (f : Fin a → Fin b → Bool) :
    xorFin (fun i => xorFin (f i)) = xorFin (fun j => xorFin (fun i => f i j)) := by
  induction a with
  | zero =>
    have h1 : xorFin (fun i : Fin 0 => xorFin (f i)) = false := rfl
    have h2 : xorFin (fun j : Fin b => xorFin (fun i : Fin 0 => f i j)) = false :=
      xorFin_eq_false _ (fun _ => rfl)
    rw [h1, h2]
  | succ a ih =>
    rw [xorFin_succ]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← xorFin_xor]
    apply xorFin_congr
    intro j
    rw [xorFin_succ]

lemma xorFin_prod {a b : Nat} (hbpos : 0 < b) (f : Fin a → Fin b → Bool) :
    xorFin (fun p : Fin (a * b) =>
      f ⟨p.val / b, Nat.div_lt_of_lt_mul (Nat.mul_comm a b ▸ p.isLt)⟩
        ⟨p.val % b, Nat.mod_lt _ hbpos⟩) =
      xorFin (fun i : Fin a => xorFin (f i)) := by
  induction a with
  | zero =>
    exact (xorFin_cast (Nat.zero_mul b) _ (fun _ : Fin 0 => false) (fun _ hi _ => by omega)).trans rfl
  | succ a ih =>
    rw [xorFin_succ]
    have hmul : (a + 1) * b = a * b + b := Nat.succ_mul a b
    have hbmul : b * (a + 1) = a * b + b := by rw [Nat.mul_comm, Nat.succ_mul]
    have hsplit : ∀ (N M : Nat) (g : Fin (N + M) → Bool),
        xorFin g = xor (xorFin (fun i : Fin N => g ⟨i.val, by omega⟩))
                       (xorFin (fun j : Fin M => g ⟨N + j.val, by omega⟩)) := by
      intro N M g
      induction M with
      | zero =>
        simp only [Nat.add_zero]
        have h0 : xorFin (fun j : Fin 0 => g ⟨N + j.val, by omega⟩) = false := rfl
        rw [h0, Bool.xor_false]
        exact xorFin_congr _ _ (fun i => rfl)
      | succ M ihM =>
        rw [xorFin_succ (fun j : Fin (M + 1) => g ⟨N + j.val, by omega⟩)]
        have hgoal := xorFin_succ (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩)
        have hcast : xorFin g = xorFin (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩) :=
          xorFin_congr _ _ (fun i => rfl)
        rw [hcast, hgoal]
        have hih := ihM (fun x : Fin (N + M) => g ⟨x.val, by omega⟩)
        have hcs : xorFin (fun i : Fin (N + M) => g ⟨i.castSucc.val, by omega⟩) =
            xorFin (fun i : Fin (N + M) => g ⟨i.val, by omega⟩) :=
          xorFin_congr _ _ (fun _ => rfl)
        rw [hcs, hih]
        simp only [Fin.last, Bool.xor_assoc]
        rfl
    have hcast2 : xorFin (fun p : Fin ((a + 1) * b) =>
        f ⟨p.val / b, Nat.div_lt_of_lt_mul (Nat.mul_comm (a + 1) b ▸ p.isLt)⟩
          ⟨p.val % b, Nat.mod_lt _ hbpos⟩) =
      xorFin (fun p : Fin (a * b + b) =>
        f ⟨p.val / b, Nat.div_lt_of_lt_mul (show p.val < b * (a + 1) by omega)⟩
          ⟨p.val % b, Nat.mod_lt _ hbpos⟩) :=
      xorFin_cast hmul _ _ (fun _ _ _ => rfl)
    rw [hcast2, hsplit (a * b) b]
    congr 1
    · rw [← ih (fun i j => f i.castSucc j)]
      apply xorFin_congr
      intro p
      rfl
    · apply xorFin_congr
      intro j
      have hdiv : (a * b + j.val) / b = a := by
        rw [Nat.mul_comm, Nat.mul_add_div hbpos, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      have hmod : (a * b + j.val) % b = j.val := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      congr 1
      · exact Fin.ext hdiv
      · exact Fin.ext hmod

lemma xorFin_finset_card {k : Nat} (S : Finset (Fin k)) (f : Fin k → Bool) :
    decide ((S.filter (fun i => f i = true)).card % 2 = 1) =
      xorFin (fun i : Fin k => decide (i ∈ S) && f i) := by
  induction S using Finset.induction_on with
  | empty =>
    simp [xorFin_false]
  | @insert a s ha ih =>
    have h1 : ((insert a s).filter (fun i => f i = true)).card =
        (s.filter (fun i => f i = true)).card + (f a).toNat := by
      rw [Finset.filter_insert]
      cases hfa : f a
      · simp
      · simp only [ite_true, Bool.toNat_true]
        rw [Finset.card_insert_of_notMem (by simp [ha])]
    have h2 : decide (((s.filter (fun i => f i = true)).card + (f a).toNat) % 2 = 1) =
        xor (decide ((s.filter (fun i => f i = true)).card % 2 = 1)) (f a) := by
      cases hfa : f a
      · simp [Bool.toNat]
      · simp only [Bool.toNat, Bool.xor_true]
        by_cases hc : (s.filter (fun i => f i = true)).card % 2 = 1
        · have hc1 : ((s.filter (fun i => f i = true)).card + 1) % 2 ≠ 1 := by omega
          simp [hc, hc1]
        · have hc1 : ((s.filter (fun i => f i = true)).card + 1) % 2 = 1 := by omega
          simp [hc, hc1]
    have h3 : xorFin (fun i : Fin k => decide (i ∈ insert a s) && f i) =
        xor (xorFin (fun i : Fin k => decide (i ∈ s) && f i))
            (xorFin (fun i : Fin k => if i = a then f a else false)) := by
      rw [← xorFin_xor]
      apply xorFin_congr
      intro i
      by_cases hia : i = a
      · subst hia; simp [ha]
      · simp [hia]
    rw [h1, h2, ih, h3, xorFin_single]

lemma ite_pos {α : Type} {P : Prop} [Decidable P] {a b : α} (h : P) :
    (if P then a else b) = a := by simp [h]

lemma ite_neg {α : Type} {P : Prop} [Decidable P] {a b : α} (h : ¬P) :
    (if P then a else b) = b := by simp [h]

lemma dite_pos {α : Type} {P : Prop} [Decidable P] {a : P → α} {b : ¬P → α} (h : P) :
    (if hp : P then a hp else b hp) = a h := by simp [h]

lemma dite_neg {α : Type} {P : Prop} [Decidable P] {a : P → α} {b : ¬P → α} (h : ¬P) :
    (if hp : P then a hp else b hp) = b h := by simp [h]

lemma hk_of {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) : 0 < k := by omega

section RowAlg

variable {r k : Nat} (hk : 0 < k)

def ix (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
def add (u v : Fin k → Bool) (i : Fin k) : Bool := xor (u i) (v i)
def mix (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w (ix hk (i.val + k - 1))) (xor (w i) (w (ix hk (i.val + 1))))
def rot (x : Fin k → Bool) (i : Fin k) : Bool := x (ix hk (i.val + k - 1))
def chi (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w i) (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
def row (u x : Fin k → Bool) : Fin k → Bool :=
  add (chi hk (mix hk (add u (rot hk x)))) x
def vMask : Fin k → Bool := fun i => decide (i.val ≠ 1)
def diffFn (u x : Fin k → Bool) : Fin k → Bool :=
  add (row hk u x) (row hk (add u vMask) x)
def neededSet (r k : Nat) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k =>
    if i.val = 0 ∨ i.val = k - 1 then r % 2 = 0
    else i.val = 1 ∨ i.val = k - 2 ∨ i.val % 3 ≠ 1)

lemma ix_eq_of_lt {i : Nat} (hi : i < k) : ix hk i = ⟨i, hi⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hi)

lemma ix_mod_eq {a b : Nat} (h : a % k = b % k) : ix hk a = ix hk b :=
  Fin.ext h

lemma mix_add (w1 w2 : Fin k → Bool) :
    mix hk (add w1 w2) = add (mix hk w1) (mix hk w2) := by
  funext i; unfold mix add; dsimp only
  cases w1 (ix hk (i.val + k - 1)) <;> cases w2 (ix hk (i.val + k - 1)) <;>
    cases w1 i <;> cases w2 i <;>
    cases w1 (ix hk (i.val + 1)) <;> cases w2 (ix hk (i.val + 1)) <;> rfl

lemma mix_vMask (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    mix hk vMask i = decide (3 ≤ i.val) := by
  unfold mix vMask
  have h1 : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
    dsimp only [ix]; split_ifs with h0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  have h2 : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
    dsimp only [ix]; split_ifs with hlast
    · rw [show i.val + 1 = k by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]
  by_cases hi0 : i.val = 0
  · have hn1 : k - 1 ≠ 1 := by omega
    have hn2 : ¬(0 = k - 1) := by omega
    simp [hi0, hn1, hn2]
  · by_cases hi1 : i.val = 1
    · have hn2 : ¬(1 = k - 1) := by omega
      simp [hi1, hn2]
    · by_cases hi2 : i.val = 2
      · have hn2 : ¬(2 = k - 1) := by omega
        simp [hi2, hn2]
      · by_cases hil : i.val = k - 1
        · have hn0 : k - 1 ≠ 0 := by omega
          have hn1 : k - 1 ≠ 1 := by omega
          have hge3 : 3 ≤ k - 1 := by omega
          have hm1 : k - 1 - 1 ≠ 1 := by omega
          simp [hil, hn0, hn1, hge3, hm1]
        · have hge3 : 3 ≤ i.val := by omega
          have hne1 : i.val - 1 ≠ 1 := by omega
          simp [hi0, hi1, hil, hge3, hne1]

lemma diffFn_eq (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) (i : Fin k) :
    let w := mix hk (add u (rot hk x))
    diffFn hk u x i =
      if i.val = 0 then false
      else if i.val = 1 then !(w (ix hk 2))
      else if i.val = 2 then xor (w (ix hk 3)) (w (ix hk 4))
      else if i.val < k - 2 then !(xor (w (ix hk (i.val + 1))) (w (ix hk (i.val + 2))))
      else if i.val = k - 2 then !(w (ix hk 0))
      else true := by
  intro w
  have h1 : add (add u vMask) (rot hk x) = add (add u (rot hk x)) vMask := by
    funext j; unfold add; cases u j <;> cases vMask j <;> cases rot hk x j <;> rfl
  have h2 : diffFn hk u x i = xor (chi hk w i) (chi hk (add w (mix hk vMask)) i) := by
    unfold diffFn row
    rw [h1, mix_add hk (add u (rot hk x)) vMask]
    change xor (xor (chi hk w i) (x i)) (xor (chi hk (add w (mix hk vMask)) i) (x i)) =
      xor (chi hk w i) (chi hk (add w (mix hk vMask)) i)
    cases chi hk w i <;> cases chi hk (add w (mix hk vMask)) i <;> cases x i <;> rfl
  rw [h2]
  unfold chi add
  rw [mix_vMask hk hr hk3, mix_vMask hk hr hk3, mix_vMask hk hr hk3]
  have hp1 : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
    dsimp only [ix]; split_ifs with hl
    · rw [show i.val + 1 = k by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hp2 : (ix hk (i.val + 2)).val =
      if i.val = k - 2 then 0 else if i.val = k - 1 then 1 else i.val + 2 := by
    dsimp only [ix]; split_ifs with h1 h2
    · rw [show i.val + 2 = k by omega, Nat.mod_self]
    · rw [show i.val + 2 = 1 + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  by_cases hi0 : i.val = 0
  · have h1v : (ix hk (i.val + 1)).val = 1 := by rw [hp1]; split_ifs <;> omega
    have h2v : (ix hk (i.val + 2)).val = 2 := by rw [hp2]; split_ifs <;> omega
    rw [h1v, h2v, hi0]
    simp only [ite_true]
    have hd0 : decide (3 ≤ 0) = false := rfl
    have hd1 : decide (3 ≤ 1) = false := rfl
    have hd2 : decide (3 ≤ 2) = false := rfl
    rw [hd0, hd1, hd2]
    cases w i <;> cases w (ix hk (0 + 1)) <;> cases w (ix hk (0 + 2)) <;> rfl
  · by_cases hi1 : i.val = 1
    · have h1v : (ix hk (i.val + 1)).val = 2 := by rw [hp1]; split_ifs <;> omega
      have h2v : (ix hk (i.val + 2)).val = 3 := by rw [hp2]; split_ifs <;> omega
      have heq1 : ix hk (i.val + 1) = ix hk 2 := by rw [hi1]
      rw [h1v, h2v, heq1, ite_neg hi0, ite_pos hi1, hi1]
      have hd0 : decide (3 ≤ 1) = false := rfl
      have hd1 : decide (3 ≤ 2) = false := rfl
      have hd2 : decide (3 ≤ 3) = true := rfl
      rw [hd0, hd1, hd2]
      cases w i <;> cases w (ix hk 2) <;> cases w (ix hk (1 + 2)) <;> rfl
    · by_cases hi2 : i.val = 2
      · have h1v : (ix hk (i.val + 1)).val = 3 := by rw [hp1]; split_ifs <;> omega
        have h2v : (ix hk (i.val + 2)).val = 4 := by rw [hp2]; split_ifs <;> omega
        have heq1 : ix hk (i.val + 1) = ix hk 3 := by rw [hi2]
        have heq2 : ix hk (i.val + 2) = ix hk 4 := by rw [hi2]
        rw [h1v, h2v, heq1, heq2, ite_neg hi0, ite_neg hi1, ite_pos hi2, hi2]
        have hd0 : decide (3 ≤ 2) = false := rfl
        have hd1 : decide (3 ≤ 3) = true := rfl
        have hd2 : decide (3 ≤ 4) = true := rfl
        rw [hd0, hd1, hd2]
        cases w i <;> cases w (ix hk 3) <;> cases w (ix hk 4) <;> rfl
      · by_cases hilt : i.val < k - 2
        · have hge3 : 3 ≤ i.val := by omega
          have h1v : 3 ≤ (ix hk (i.val + 1)).val := by rw [hp1]; split_ifs <;> omega
          have h2v : 3 ≤ (ix hk (i.val + 2)).val := by rw [hp2]; split_ifs <;> omega
          rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_pos hilt,
            decide_eq_true hge3, decide_eq_true h1v, decide_eq_true h2v]
          cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk (i.val + 2)) <;> rfl
        · by_cases hik2 : i.val = k - 2
          · have hge3 : 3 ≤ i.val := by omega
            have h1v : 3 ≤ (ix hk (i.val + 1)).val := by rw [hp1]; split_ifs <;> omega
            have h2v : ¬(3 ≤ (ix hk (i.val + 2)).val) := by rw [hp2]; split_ifs; omega
            have heq2 : ix hk (i.val + 2) = ix hk 0 := ix_mod_eq hk (by rw [hik2, show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])
            rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_neg hilt, ite_pos hik2,
              decide_eq_true hge3, decide_eq_true h1v, decide_eq_false h2v, heq2]
            cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk 0) <;> rfl
          · have hik1 : i.val = k - 1 := by omega
            have hge3 : 3 ≤ i.val := by omega
            have h1v : ¬(3 ≤ (ix hk (i.val + 1)).val) := by rw [hp1]; split_ifs; omega
            have h2v : ¬(3 ≤ (ix hk (i.val + 2)).val) := by rw [hp2]; split_ifs; omega
            rw [ite_neg hi0, ite_neg hi1, ite_neg hi2, ite_neg hilt, ite_neg hik2,
              decide_eq_true hge3, decide_eq_false h1v, decide_eq_false h2v]
            cases w i <;> cases w (ix hk (i.val + 1)) <;> cases w (ix hk (i.val + 2)) <;> rfl

def resSum (r : Nat) (hk3 : k = 3 * r) (w : Fin k → Bool) (c : Nat) (hc : c < 3) : Bool :=
  xorFin (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩)

lemma resSum_mix (hr : 2 ≤ r) (hk3 : k = 3 * r) (z : Fin k → Bool) :
    resSum r hk3 (mix hk z) 0 (by omega) = xorFin z ∧
    resSum r hk3 (mix hk z) 1 (by omega) = xorFin z ∧
    resSum r hk3 (mix hk z) 2 (by omega) = xorFin z := by
  have hmod : ∀ (c : Nat) (hc : c < 3),
      resSum r hk3 (mix hk z) c hc = xorFin z := by
    intro c hc
    unfold resSum mix
    rw [xorFin_xor, xorFin_xor]

    have hpart : ∀ (f : Fin k → Bool),
        xorFin f = xor (xorFin (fun j : Fin r => f ⟨3 * j.val, by omega⟩))
                       (xor (xorFin (fun j : Fin r => f ⟨3 * j.val + 1, by omega⟩))
                            (xorFin (fun j : Fin r => f ⟨3 * j.val + 2, by omega⟩))) := by
      intro f
      have h1 : xorFin f = xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) :=
        xorFin_cast (by rw [hk3, Nat.mul_comm]) _ _ (fun _ _ _ => rfl)
      rw [h1]
      have h2 := xorFin_prod (a := r) (b := 3) (by omega) (fun j (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
      have h3 : xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) =
          xorFin (fun p : Fin (r * 3) =>
            f ⟨3 * (p.val / 3) + p.val % 3, by omega⟩) :=
        xorFin_congr _ _ (fun p => by congr 1; apply Fin.ext; dsimp; omega)
      have hfin3 : ∀ (g : Fin 3 → Bool),
          xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
        intro g; unfold xorFin
        have : List.finRange 3 = [0, 1, 2] := rfl
        rw [this]; simp
      rw [h3, show xorFin (fun p : Fin (r * 3) => f ⟨3 * (p.val / 3) + p.val % 3, by omega⟩) =
            xorFin (fun p : Fin (r * 3) =>
              (fun (j : Fin r) (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
                ⟨p.val / 3, Nat.div_lt_of_lt_mul (Nat.mul_comm r 3 ▸ p.isLt)⟩
                ⟨p.val % 3, Nat.mod_lt _ (by omega)⟩) from xorFin_congr _ _ (fun _ => rfl), h2]
      simp_rw [hfin3, xorFin_xor]
      rfl
    rw [hpart z]

    have hrot_succ : ∀ (m : Nat) (g : Fin (m + 1) → Bool),
        xorFin g = xor (g ⟨0, by omega⟩) (xorFin (fun j : Fin m => g j.succ)) := by
      intro m g; unfold xorFin
      have hfr : List.finRange (m + 1) = ⟨0, by omega⟩ :: (List.finRange m).map Fin.succ := by
        apply List.ext_getElem
        · simp
        · intro idx _ _
          cases idx <;> apply Fin.ext <;> simp
      rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]
    have hshift_prev : ∀ (c : Nat) (hc : c < 3),
        xorFin (fun j : Fin r => z (ix hk (3 * j.val + c + k - 1))) =
          xorFin (fun j : Fin r => z ⟨3 * j.val + (c + 2) % 3, by omega⟩) := by
      intro c hc
      by_cases hc0 : c = 0
      · subst hc0
        have hrot : ∀ (g : Fin r → Bool),
            xorFin (fun j : Fin r => g ⟨(j.val + r - 1) % r, Nat.mod_lt _ (by omega)⟩) = xorFin g := by
          intro g
          cases r with
          | zero => omega
          | succ r' =>
            rw [hrot_succ r', xorFin_succ g, Bool.xor_comm]
            congr 1
            · apply xorFin_congr; intro j; congr 1; apply Fin.ext
              simp only [Fin.val_succ, Fin.val_castSucc]
              rw [show j.val + 1 + (r' + 1) - 1 = j.val + (r' + 1) by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            · congr 1; apply Fin.ext; simp only [Fin.last]
              rw [Nat.zero_add, Nat.add_sub_cancel, Nat.mod_eq_of_lt (by omega)]
        have hmatch := hrot (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩)
        rw [← hmatch]
        apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        by_cases hj0 : j.val = 0
        · rw [hj0]; simp only [Nat.mul_zero, Nat.zero_add]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        · rw [show 3 * j.val + k - 1 = (3 * j.val - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), show j.val + r - 1 = (j.val - 1) + r by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      · apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        rw [show 3 * j.val + c + k - 1 = (3 * j.val + (c - 1)) + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega
    have hshift_next : ∀ (c : Nat) (hc : c < 3),
        xorFin (fun j : Fin r => z (ix hk (3 * j.val + c + 1))) =
          xorFin (fun j : Fin r => z ⟨3 * j.val + (c + 1) % 3, by omega⟩) := by
      intro c hc
      by_cases hc2 : c = 2
      · subst hc2
        have hrot : ∀ (g : Fin r → Bool),
            xorFin (fun j : Fin r => g ⟨(j.val + 1) % r, Nat.mod_lt _ (by omega)⟩) = xorFin g := by
          intro g
          cases r with
          | zero => omega
          | succ r' =>
            rw [xorFin_succ (fun j : Fin (r' + 1) => g ⟨(j.val + 1) % (r' + 1), Nat.mod_lt _ (by omega)⟩),
              hrot_succ r' g, Bool.xor_comm]
            congr 1
            · congr 1; apply Fin.ext; simp only [Fin.last]; rw [Nat.mod_self]
            · apply xorFin_congr; intro j; congr 1; apply Fin.ext
              simp only [Fin.val_castSucc, Fin.val_succ]
              rw [Nat.mod_eq_of_lt (by omega)]
        have hmatch := hrot (fun j : Fin r => z ⟨3 * j.val, by omega⟩)
        have hrhs : xorFin (fun j : Fin r => z ⟨3 * j.val + (2 + 1) % 3, by omega⟩) =
            xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) :=
          xorFin_congr _ _ (fun j => rfl)
        rw [hrhs, ← hmatch]
        apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        by_cases hjl : j.val = r - 1
        · rw [hjl, show 3 * (r - 1) + 2 + 1 = k by omega, Nat.mod_self,
            show r - 1 + 1 = r by omega, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      · apply xorFin_congr; intro j; congr 1; apply Fin.ext; dsimp [ix]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hshift_prev c hc, hshift_next c hc]
    interval_cases c
    · simp only [Nat.zero_add]
      cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
    · cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
    · cases xorFin (fun j : Fin r => z ⟨3 * j.val, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 1, by omega⟩) <;>
        cases xorFin (fun j : Fin r => z ⟨3 * j.val + 2, by omega⟩) <;> rfl
  exact ⟨hmod 0 (by omega), hmod 1 (by omega), hmod 2 (by omega)⟩

def zPair (w : Fin k → Bool) (z0 z1 : Bool) : Nat → Bool × Bool
  | 0 => (z0, z1)
  | j + 1 =>
    let p := zPair w z0 z1 j
    (p.2, xor p.1 (xor p.2 (if h : j + 1 < k then w ⟨j + 1, h⟩ else false)))

def zOf (w : Fin k → Bool) (z0 z1 : Bool) (i : Fin k) : Bool :=
  (zPair w z0 z1 i.val).1

lemma zPair_snd (w : Fin k → Bool) (z0 z1 : Bool) (j : Nat) :
    (zPair w z0 z1 (j + 1)).1 = (zPair w z0 z1 j).2 := rfl

lemma zPair_rec (w : Fin k → Bool) (z0 z1 : Bool) (j : Nat) (hj : j + 1 < k) :
    (zPair w z0 z1 (j + 2)).1 =
      xor (zPair w z0 z1 j).1 (xor (zPair w z0 z1 (j + 1)).1 (w ⟨j + 1, hj⟩)) := by
  simp only [zPair, hj, dite_true]

lemma zPair_rec_at (w : Fin k → Bool) (z0 z1 : Bool) (j j1 j2 : Nat)
    (h1 : j1 = j + 1) (h2 : j2 = j + 2) (hj1 : j1 < k) :
    (zPair w z0 z1 j2).1 =
      xor (zPair w z0 z1 j).1 (xor (zPair w z0 z1 j1).1 (w ⟨j1, hj1⟩)) := by
  subst h1; subst h2; exact zPair_rec w z0 z1 j hj1

lemma zPair_xor (w1 w2 : Fin k → Bool) (z0a z1a z0b z1b : Bool) (j : Nat) :
    zPair (add w1 w2) (xor z0a z0b) (xor z1a z1b) j =
      (xor (zPair w1 z0a z1a j).1 (zPair w2 z0b z1b j).1,
       xor (zPair w1 z0a z1a j).2 (zPair w2 z0b z1b j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [zPair, ih]
    refine Prod.ext rfl ?_
    by_cases h : j + 1 < k
    · simp only [h, dite_true, add]
      cases (zPair w1 z0a z1a j).1 <;> cases (zPair w2 z0b z1b j).1 <;>
        cases (zPair w1 z0a z1a j).2 <;> cases (zPair w2 z0b z1b j).2 <;>
        cases w1 ⟨j + 1, h⟩ <;> cases w2 ⟨j + 1, h⟩ <;> rfl
    · simp only [h, dite_false]
      cases (zPair w1 z0a z1a j).1 <;> cases (zPair w2 z0b z1b j).1 <;>
        cases (zPair w1 z0a z1a j).2 <;> cases (zPair w2 z0b z1b j).2 <;> rfl

lemma zOf_xor (w1 w2 : Fin k → Bool) (z0a z1a z0b z1b : Bool) (i : Fin k) :
    zOf (add w1 w2) (xor z0a z0b) (xor z1a z1b) i =
      xor (zOf w1 z0a z1a i) (zOf w2 z0b z1b i) := by
  unfold zOf; rw [zPair_xor]

lemma zPair_zero (z0 z1 : Bool) (j : Nat) :
    zPair (k := k) (fun _ => false) z0 z1 j =
      (if j % 3 = 0 then z0 else if j % 3 = 1 then z1 else xor z0 z1,
       if (j + 1) % 3 = 0 then z0 else if (j + 1) % 3 = 1 then z1 else xor z0 z1) := by
  induction j with
  | zero => simp [zPair]
  | succ j ih =>
    simp only [zPair, ih, dite_eq_ite, ite_self]
    refine Prod.ext rfl ?_
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have h1 : (j + 1) % 3 = 1 := by omega
      have h2 : (j + 1 + 1) % 3 = 2 := by omega
      simp [h, h1, h2]
    · have h1 : (j + 1) % 3 = 2 := by omega
      have h2 : (j + 1 + 1) % 3 = 0 := by omega
      simp [h, h1, h2]; cases z0 <;> cases z1 <;> rfl
    · have h1 : (j + 1) % 3 = 0 := by omega
      have h2 : (j + 1 + 1) % 3 = 1 := by omega
      simp [h, h1, h2]; cases z0 <;> cases z1 <;> rfl

lemma zPair_mask3 (j : Nat) (hj : j < k) :
    zPair (fun i : Fin k => decide (3 ≤ i.val)) false false j =
      (decide (4 ≤ j ∧ j % 3 = 1), decide (4 ≤ j + 1 ∧ (j + 1) % 3 = 1)) := by
  induction j with
  | zero => simp [zPair]
  | succ j ih =>
    simp only [zPair, ih (by omega), hj, dite_true]
    refine Prod.ext rfl ?_
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases h1 : j = 1
      · subst h1; simp
      · by_cases h2 : j = 2
        · subst h2; simp
        · have hge3 : 3 ≤ j + 1 := by omega
          have hge4 : 4 ≤ j + 1 := by omega
          have hge4' : 4 ≤ j + 1 + 1 := by omega
          by_cases hj3 : j = 3
          · subst hj3; simp
          · have hj4 : 4 ≤ j := by omega
            simp only [hj4, hge3, hge4, hge4', true_and, decide_true]
            have hm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
            rcases hm with h | h | h
            · have h1' : (j + 1) % 3 = 1 := by omega
              have h2' : (j + 1 + 1) % 3 = 2 := by omega
              simp [h, h1', h2']
            · have h1' : (j + 1) % 3 = 2 := by omega
              have h2' : (j + 1 + 1) % 3 = 0 := by omega
              simp [h, h1', h2']
            · have h1' : (j + 1) % 3 = 0 := by omega
              have h2' : (j + 1 + 1) % 3 = 1 := by omega
              simp [h, h1', h2']

lemma zPair_3m (w : Fin k → Bool) (z0 z1 : Bool) (m : Nat) (hm : 3 * m + 1 < k) :
    (zPair w z0 z1 (3 * m)).1 =
      xor z0 (xorFin (fun j : Fin m => xor (w ⟨3 * j.val + 1, by omega⟩) (w ⟨3 * j.val + 2, by omega⟩))) ∧
    (zPair w z0 z1 (3 * m)).2 =
      xor z1 (xorFin (fun j : Fin m => xor (w ⟨3 * j.val + 2, by omega⟩) (w ⟨3 * j.val + 3, by omega⟩))) := by
  induction m with
  | zero => simp [zPair, xorFin]
  | succ m ih =>
    rcases ih (by omega) with ⟨h1, h2⟩
    have ha : 3 * m + 1 < k := by omega
    have hb : 3 * m + 2 < k := by omega
    have hc : 3 * m + 3 < k := by omega
    have hstep1 : (zPair w z0 z1 (3 * m + 1)).1 = (zPair w z0 z1 (3 * m)).2 := rfl
    have hstep2 : (zPair w z0 z1 (3 * m + 2)).1 =
        xor (zPair w z0 z1 (3 * m)).1 (xor (zPair w z0 z1 (3 * m)).2 (w ⟨3 * m + 1, ha⟩)) := by
      simp only [zPair, ha, dite_true]
    have hstep3 : (zPair w z0 z1 (3 * m + 3)).1 =
        xor (zPair w z0 z1 (3 * m)).1 (xor (w ⟨3 * m + 1, ha⟩) (w ⟨3 * m + 2, hb⟩)) := by
      have ht := zPair_rec_at w z0 z1 (3 * m + 1) (3 * m + 2) (3 * m + 3) (by omega) (by omega) hb
      rw [ht, hstep1, hstep2]
      cases (zPair w z0 z1 (3 * m)).1 <;> cases (zPair w z0 z1 (3 * m)).2 <;>
        cases w ⟨3 * m + 1, ha⟩ <;> cases w ⟨3 * m + 2, hb⟩ <;> rfl
    have hstep4 : (zPair w z0 z1 (3 * m + 3)).2 =
        xor (zPair w z0 z1 (3 * m)).2 (xor (w ⟨3 * m + 2, hb⟩) (w ⟨3 * m + 3, hc⟩)) := by
      have ht := zPair_rec_at w z0 z1 (3 * m + 2) (3 * m + 3) (3 * m + 4) (by omega) (by omega) hc
      change (zPair w z0 z1 (3 * m + 4)).1 = _
      rw [ht, hstep2, hstep3]
      cases (zPair w z0 z1 (3 * m)).1 <;> cases (zPair w z0 z1 (3 * m)).2 <;>
        cases w ⟨3 * m + 1, ha⟩ <;> cases w ⟨3 * m + 2, hb⟩ <;> cases w ⟨3 * m + 3, hc⟩ <;> rfl
    rw [show 3 * (m + 1) = 3 * m + 3 by omega, hstep3, hstep4, h1, h2]
    constructor
    · rw [xorFin_succ]; simp only [Fin.val_castSucc, Fin.last, Bool.xor_assoc]
    · rw [xorFin_succ]; simp only [Fin.val_castSucc, Fin.last, Bool.xor_assoc]

lemma mix_zOf (hr : 2 ≤ r) (hk3 : k = 3 * r) (w : Fin k → Bool) (z0 z1 : Bool)
    (hs01 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega))
    (hs02 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega)) :
    mix hk (zOf w z0 z1) = w := by
  have hr' : r = (r - 1) + 1 := by omega
  have hsum_last : ∀ (c : Nat) (hc : c < 3),
      xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) =
        xor (resSum r hk3 w c hc) (w ⟨3 * (r - 1) + c, by omega⟩) := by
    intro c hc
    unfold resSum
    have heq : xorFin (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩) =
        xorFin (fun j : Fin ((r - 1) + 1) => w ⟨3 * j.val + c, by omega⟩) :=
      xorFin_cast hr' _ _ (fun _ _ _ => rfl)
    rw [heq, xorFin_succ]
    have hcs : xorFin (fun j : Fin (r - 1) => w ⟨3 * j.castSucc.val + c, by omega⟩) =
        xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcs]
    simp only [Fin.last]
    cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + c, by omega⟩) <;>
      cases w ⟨3 * (r - 1) + c, by omega⟩ <;> rfl
  have hsum0 : xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) =
      xor (resSum r hk3 w 0 (by omega)) (w ⟨0, by omega⟩) := by
    unfold resSum
    have heq : xorFin (fun j : Fin r => w ⟨3 * j.val + 0, by omega⟩) =
        xor (w ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩)) := by
      have hc : xorFin (fun j : Fin r => w ⟨3 * j.val + 0, by omega⟩) =
          xorFin (fun j : Fin ((r - 1) + 1) => w ⟨3 * j.val, by omega⟩) :=
        xorFin_cast hr' _ _ (fun _ _ _ => rfl)
      rw [hc]; unfold xorFin
      have hfr : List.finRange ((r - 1) + 1) = ⟨0, by omega⟩ :: (List.finRange (r - 1)).map Fin.succ := by
        apply List.ext_getElem
        · simp
        · intro idx _ _; cases idx <;> apply Fin.ext <;> simp
      rw [hfr, List.foldl_cons, foldl_map_xor_init, List.foldl_map, Bool.false_xor]
      congr 1
    rw [heq]
    cases w ⟨0, by omega⟩ <;> cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) <;> rfl
  funext i
  by_cases hi0 : i.val = 0
  · have h3m := zPair_3m w z0 z1 (r - 1) (by omega)
    have hzk1 := zPair_rec_at w z0 z1 (3 * (r - 1)) (3 * (r - 1) + 1) (k - 1) (by omega) (by omega) (by omega)
    rw [zPair_snd, h3m.1, h3m.2, xorFin_xor, xorFin_xor, hsum_last 1 (by omega), hsum0, hs01] at hzk1
    unfold mix zOf
    have hprev : ix hk (i.val + k - 1) = ⟨k - 1, by omega⟩ := by
      rw [hi0, Nat.zero_add]; exact ix_eq_of_lt hk (by omega)
    have hnext : ix hk (i.val + 1) = ⟨1, by omega⟩ := by
      rw [hi0]; exact ix_eq_of_lt hk (by omega)
    have hwi : w i = w ⟨0, hk⟩ := congrArg w (Fin.ext hi0)
    have hzi : (zPair w z0 z1 i.val).1 = z0 := by rw [hi0]; rfl
    rw [hprev, hnext, hwi, hzi]
    dsimp only
    rw [hzk1]
    have hz1 : (zPair w z0 z1 1).1 = z1 := rfl
    rw [hz1]
    cases z0 <;> cases z1 <;> cases resSum r hk3 w 1 (by omega) <;>
      cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 2, by omega⟩) <;>
      cases w ⟨3 * (r - 1) + 1, by omega⟩ <;> cases w ⟨0, hk⟩ <;> rfl
  · by_cases hil : i.val = k - 1
    · have h3m := zPair_3m w z0 z1 (r - 1) (by omega)
      have hzk2 : (zPair w z0 z1 (k - 2)).1 = (zPair w z0 z1 (3 * (r - 1))).2 := by
        rw [show k - 2 = 3 * (r - 1) + 1 by omega]; rfl
      have hzk1 := zPair_rec_at w z0 z1 (3 * (r - 1)) (3 * (r - 1) + 1) (k - 1) (by omega) (by omega) (by omega)
      rw [zPair_snd, h3m.1, h3m.2, xorFin_xor, xorFin_xor, hsum_last 1 (by omega), hsum_last 2 (by omega)] at hzk1
      rw [h3m.2, xorFin_xor, hsum_last 2 (by omega)] at hzk2
      unfold mix zOf
      have hprev : ix hk (i.val + k - 1) = ⟨k - 2, by omega⟩ := by
        rw [hil]; exact (ix_mod_eq hk (by rw [show k - 1 + k - 1 = (k - 2) + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (i.val + 1) = ⟨0, hk⟩ := by
        rw [hil]; exact (ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      have hwi : w i = w ⟨3 * (r - 1) + 2, by omega⟩ := congrArg w (Fin.ext (by dsimp; omega))
      have hzi : (zPair w z0 z1 i.val).1 = (zPair w z0 z1 (k - 1)).1 := by rw [hil]
      rw [hprev, hnext, hwi, hzi]
      dsimp only
      rw [hzk2, hzk1, ← hs01, hs02]
      have hz0 : (zPair w z0 z1 0).1 = z0 := rfl
      rw [hz0]
      cases z0 <;> cases z1 <;> cases resSum r hk3 w 2 (by omega) <;>
        cases w ⟨3 * (r - 1) + 1, by omega⟩ <;> cases w ⟨3 * (r - 1) + 2, by omega⟩ <;>
        cases xorFin (fun j : Fin (r - 1) => w ⟨3 * j.val + 3, by omega⟩) <;> rfl
    · unfold mix zOf
      have hprev : ix hk (i.val + k - 1) = ⟨i.val - 1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (i.val + 1) = ⟨i.val + 1, by omega⟩ := ix_eq_of_lt hk (by omega)
      rw [hprev, hnext]
      dsimp only
      have ht := zPair_rec_at w z0 z1 (i.val - 1) i.val (i.val + 1) (by omega) (by omega) i.isLt
      rw [ht]
      cases (zPair w z0 z1 (i.val - 1)).1 <;> cases (zPair w z0 z1 i.val).1 <;>
        cases w i <;> rfl

lemma zOf_mix (hr : 2 ≤ r) (hk3 : k = 3 * r) (z : Fin k → Bool) :
    zOf (mix hk z) (z ⟨0, hk⟩) (z ⟨1, by omega⟩) = z := by
  have haux : ∀ j (hj : j + 1 < k),
      zPair (mix hk z) (z ⟨0, hk⟩) (z ⟨1, by omega⟩) j = (z ⟨j, by omega⟩, z ⟨j + 1, hj⟩) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hj1 : j + 1 < k := by omega
      simp only [zPair, ih hj1, hj1, dite_true]
      refine Prod.ext rfl ?_
      unfold mix
      have hprev : ix hk (j + 1 + k - 1) = ⟨j, by omega⟩ :=
        (ix_mod_eq hk (by rw [show j + 1 + k - 1 = j + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      have hnext : ix hk (j + 1 + 1) = ⟨j + 2, by omega⟩ := ix_eq_of_lt hk (by omega)
      dsimp only
      rw [hprev, hnext]
      cases z ⟨j, by omega⟩ <;> cases z ⟨j + 1, hj1⟩ <;> cases z ⟨j + 2, hj⟩ <;> rfl
  funext i
  unfold zOf
  by_cases hi : i.val + 1 < k
  · rw [haux i.val hi]
  · have hil : i.val = k - 1 := by omega
    have h1 := haux (k - 2) (by omega)
    rw [hil, show k - 1 = (k - 2) + 1 by omega, zPair_snd, h1]
    exact congrArg z (Fin.ext (by dsimp only; omega))

def tWalk (d : Fin k → Bool) : Nat → Bool
  | 0 => false
  | 1 => if h : 2 < k then d ⟨2, h⟩ else false
  | j + 2 =>
    xor (tWalk d (j + 1)) (if h : j + 3 < k then !(d ⟨j + 3, h⟩) else false)

def tRaw (hr : 2 ≤ r) (hk3 : k = 3 * r) (d : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val = 0 then !(d ⟨k - 2, by omega⟩)
  else if i.val = 1 then false
  else if i.val = 2 then !(d ⟨1, by omega⟩)
  else tWalk d (i.val - 3)

def tOfD (hr : 2 ≤ r) (hk3 : k = 3 * r) (d : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val = 1 then
    xor (tRaw hr hk3 d ⟨0, hk_of hr hk3⟩)
      (xorFin (fun j : Fin (r - 1) =>
        xor (tRaw hr hk3 d ⟨3 * (j.val + 1), by omega⟩)
            (tRaw hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩)))
  else tRaw hr hk3 d i

lemma xorFin_split3 (_hr : 2 ≤ r) (hk3 : k = 3 * r) (f : Fin k → Bool) :
    xorFin f = xor (xorFin (fun j : Fin r => f ⟨3 * j.val, by omega⟩))
                   (xor (xorFin (fun j : Fin r => f ⟨3 * j.val + 1, by omega⟩))
                        (xorFin (fun j : Fin r => f ⟨3 * j.val + 2, by omega⟩))) := by
  have h1 : xorFin f = xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) :=
    xorFin_cast (by rw [hk3, Nat.mul_comm]) _ _ (fun _ _ _ => rfl)
  rw [h1]
  have h2 := xorFin_prod (a := r) (b := 3) (by omega) (fun j (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
  have h3 : xorFin (fun p : Fin (r * 3) => f ⟨p.val, by omega⟩) =
      xorFin (fun p : Fin (r * 3) =>
        (fun (j : Fin r) (q : Fin 3) => f ⟨3 * j.val + q.val, by omega⟩)
          ⟨p.val / 3, Nat.div_lt_of_lt_mul (Nat.mul_comm r 3 ▸ p.isLt)⟩
          ⟨p.val % 3, Nat.mod_lt _ (by omega)⟩) :=
    xorFin_congr _ _ (fun p => by congr 1; apply Fin.ext; dsimp; omega)
  have hfin3 : ∀ (g : Fin 3 → Bool),
      xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
    intro g; unfold xorFin
    have : List.finRange 3 = [0, 1, 2] := rfl
    rw [this]; simp
  rw [h3, h2]
  simp_rw [hfin3, xorFin_xor]
  rfl

lemma tWalk_diff (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let w := mix hk (add u (rot hk x))
    let b := w ⟨3, by omega⟩
    ∀ j (hj : j + 3 < k), tWalk (diffFn hk u x) j = xor b (w ⟨j + 3, hj⟩) := by
  intro w b j
  induction j with
  | zero => intro _; simp [tWalk, b]
  | succ j ih =>
    cases j with
    | zero =>
      intro hj
      have h2lt : 2 < k := by omega
      simp only [tWalk, h2lt, dite_true]
      have hd := diffFn_eq hk hr hk3 u x ⟨2, h2lt⟩
      dsimp only at hd
      rw [hd]
      have h3 : ix hk 3 = ⟨3, by omega⟩ := ix_eq_of_lt hk (by omega)
      have h4 : ix hk 4 = ⟨4, hj⟩ := ix_eq_of_lt hk hj
      simp only [ite_true, h3, h4]
      rfl
    | succ j =>
      intro hj
      have hj3 : j + 3 < k := by omega
      have hprev := ih (by omega)
      simp only [tWalk, hj3, dite_true]
      have hd := diffFn_eq hk hr hk3 u x ⟨j + 3, hj3⟩
      dsimp only at hd
      have hn0 : j + 3 ≠ 0 := by omega
      have hn1 : j + 3 ≠ 1 := by omega
      have hn2 : j + 3 ≠ 2 := by omega
      have hlt : j + 3 < k - 2 := by omega
      rw [hd, ite_neg hn0, ite_neg hn1, ite_neg hn2, ite_pos hlt]
      have hp1 : ix hk (j + 3 + 1) = ⟨j + 1 + 3, by omega⟩ := ix_eq_of_lt hk (by omega)
      have hp2 : ix hk (j + 3 + 2) = ⟨j + 2 + 3, hj⟩ := ix_eq_of_lt hk hj
      rw [hprev, hp1, hp2]
      dsimp only [w]
      cases b <;> cases mix hk (add u (rot hk x)) ⟨j + 1 + 3, by omega⟩ <;>
        cases mix hk (add u (rot hk x)) ⟨j + 2 + 3, hj⟩ <;> rfl

lemma tOfD_diff (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let w := mix hk (add u (rot hk x))
    let b := w ⟨3, by omega⟩
    let t := tOfD hr hk3 (diffFn hk u x)
    t ⟨3, by omega⟩ = false ∧
    w = add t (fun i => b && decide (3 ≤ i.val)) ∧
    resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega) ∧
    resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega) := by
  intro w b t
  have ht0 : tRaw hr hk3 (diffFn hk u x) ⟨0, hk⟩ = w ⟨0, hk⟩ := by
    unfold tRaw; simp only [ite_true]
    have hd := diffFn_eq hk hr hk3 u x ⟨k - 2, by omega⟩
    dsimp only at hd
    have hn0 : k - 2 ≠ 0 := by omega
    have hn1 : k - 2 ≠ 1 := by omega
    have hn2 : k - 2 ≠ 2 := by omega
    have hnlt : ¬(k - 2 < k - 2) := by omega
    rw [hd, ite_neg hn0, ite_neg hn1, ite_neg hn2, ite_neg hnlt, ite_pos rfl,
      ix_eq_of_lt hk hk, Bool.not_not]
  have ht2 : tRaw hr hk3 (diffFn hk u x) ⟨2, by omega⟩ = w ⟨2, by omega⟩ := by
    unfold tRaw
    have hn0 : (2 : Nat) ≠ 0 := by omega
    have hn1 : (2 : Nat) ≠ 1 := by omega
    rw [ite_neg hn0, ite_neg hn1, ite_pos rfl]
    have hd := diffFn_eq hk hr hk3 u x ⟨1, by omega⟩
    dsimp only at hd
    have h1n0 : (1 : Nat) ≠ 0 := by omega
    rw [hd, ite_neg h1n0, ite_pos rfl, ix_eq_of_lt hk (by omega), Bool.not_not]
  have htge3 : ∀ i : Fin k, 3 ≤ i.val → tRaw hr hk3 (diffFn hk u x) i = xor b (w i) := by
    intro i hi
    unfold tRaw
    have hn0 : i.val ≠ 0 := by omega
    have hn1 : i.val ≠ 1 := by omega
    have hn2 : i.val ≠ 2 := by omega
    rw [ite_neg hn0, ite_neg hn1, ite_neg hn2]
    have hw := tWalk_diff hk hr hk3 u x (i.val - 3) (by omega)
    rw [hw]
    congr 1; exact congrArg w (Fin.ext (by dsimp only; omega))
  have hres := resSum_mix hk hr hk3 (add u (rot hk x))
  have hres_split : ∀ (f : Fin k → Bool) (c : Nat) (hc : c < 3),
      resSum r hk3 f c hc = xor (f ⟨c, by omega⟩) (xorFin (fun j : Fin (r - 1) => f ⟨3 * (j.val + 1) + c, by omega⟩)) := by
    intro f c hc
    unfold resSum
    rw [xorFin_first (by omega)]
    dsimp only
    congr 1
    exact congrArg f (Fin.ext (by dsimp only; omega))
  have ht1 : t ⟨1, by omega⟩ = w ⟨1, by omega⟩ := by
    unfold t tOfD
    simp only [ite_true]
    rw [ht0]
    have hs01 : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) := hres.1.trans hres.2.1.symm
    rw [hres_split w 0 (by omega), hres_split w 1 (by omega)] at hs01
    have hpair : xorFin (fun j : Fin (r - 1) =>
        xor (tRaw hr hk3 (diffFn hk u x) ⟨3 * (j.val + 1), by omega⟩)
            (tRaw hr hk3 (diffFn hk u x) ⟨3 * (j.val + 1) + 1, by omega⟩)) =
      xor (xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩))
          (xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 1, by omega⟩)) := by
      rw [← xorFin_xor]
      apply xorFin_congr; intro j
      rw [htge3 ⟨3 * (j.val + 1), by omega⟩ (by dsimp only; omega),
        htge3 ⟨3 * (j.val + 1) + 1, by omega⟩ (by dsimp only; omega)]
      cases b <;> cases w ⟨3 * (j.val + 1), by omega⟩ <;> cases w ⟨3 * (j.val + 1) + 1, by omega⟩ <;> rfl
    rw [hpair]
    have h00 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 0, by omega⟩) =
        xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [h00] at hs01
    cases h0 : w ⟨0, hk⟩ <;> cases h1 : w ⟨1, by omega⟩ <;>
      cases h2 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1), by omega⟩) <;>
      cases h3 : xorFin (fun j : Fin (r - 1) => w ⟨3 * (j.val + 1) + 1, by omega⟩) <;>
      simp [h0, h1, h2, h3] at hs01 ⊢
  have hw_eq : w = add t (fun i => b && decide (3 ≤ i.val)) := by
    funext i; unfold add
    by_cases hi0 : i.val = 0
    · have hie : i = ⟨0, hk⟩ := Fin.ext hi0
      rw [hie]; dsimp only
      have ht0' : t ⟨0, hk⟩ = w ⟨0, hk⟩ := by
        unfold t tOfD; rw [ite_neg (by omega)]; exact ht0
      rw [ht0']; simp
    · by_cases hi1 : i.val = 1
      · have hie : i = ⟨1, by omega⟩ := Fin.ext hi1
        rw [hie]; dsimp only; rw [ht1]; simp
      · by_cases hi2 : i.val = 2
        · have hie : i = ⟨2, by omega⟩ := Fin.ext hi2
          rw [hie]; dsimp only
          have ht2' : t ⟨2, by omega⟩ = w ⟨2, by omega⟩ := by
            unfold t tOfD; rw [ite_neg (by omega)]; exact ht2
          rw [ht2']; simp
        · have hge3 : 3 ≤ i.val := by omega
          have hte : t i = xor b (w i) := by
            unfold t tOfD; rw [ite_neg hi1]; exact htge3 i hge3
          dsimp only; rw [hte, decide_eq_true hge3, Bool.and_true]
          cases b <;> cases w i <;> rfl
  have ht3 : t ⟨3, by omega⟩ = false := by
    unfold t tOfD
    have hn1 : (3 : Nat) ≠ 1 := by omega
    rw [ite_neg hn1, htge3 ⟨3, by omega⟩ (by dsimp only; omega)]
    exact Bool.xor_self b
  have hres_t : ∀ (c : Nat) (hc : c < 3),
      resSum r hk3 w c hc = xor (resSum r hk3 t c hc) (b && decide ((r - 1) % 2 = 1)) := by
    intro c hc
    rw [hw_eq, hres_split _ c hc, hres_split t c hc]
    unfold add; dsimp only
    have hlt3 : ¬(3 ≤ c) := by omega
    rw [decide_eq_false hlt3, Bool.and_false, Bool.xor_false, xorFin_xor]
    have hmask : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
        (b && decide ((r - 1) % 2 = 1)) := by
      have h1 : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
          xorFin (fun _ : Fin (r - 1) => b) :=
        xorFin_congr _ _ (fun j => by rw [decide_eq_true (by omega), Bool.and_true])
      rw [h1, xorFin_const]
    rw [hmask, Bool.xor_assoc]
  have hs01_t : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega) := by
    have h0 := hres_t 0 (by omega); have h1 := hres_t 1 (by omega)
    have heq : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) := hres.1.trans hres.2.1.symm
    rw [h0, h1] at heq
    cases ha : resSum r hk3 t 0 (by omega) <;> cases hb : resSum r hk3 t 1 (by omega) <;>
      cases hc : (b && decide ((r - 1) % 2 = 1)) <;> simp [ha, hb, hc] at heq ⊢
  have hs02_t : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega) := by
    have h0 := hres_t 0 (by omega); have h2 := hres_t 2 (by omega)
    have heq : resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega) := hres.1.trans hres.2.2.symm
    rw [h0, h2] at heq
    cases ha : resSum r hk3 t 0 (by omega) <;> cases hb : resSum r hk3 t 2 (by omega) <;>
      cases hc : (b && decide ((r - 1) % 2 = 1)) <;> simp [ha, hb, hc] at heq ⊢
  exact ⟨ht3, hw_eq, hs01_t, hs02_t⟩

def Q0 (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩

def Qk (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  !(t ⟨0, hk_of hr hk3⟩) && t ⟨1, by omega⟩

def Qp (r : Nat) (t : Fin k → Bool) : Bool :=
  xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))))

def QpMid (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) : Bool :=
  xor (xor (t ⟨4, by omega⟩) (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩))
    (xor (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩)
      (xorFin (fun j : Fin (r - 2) =>
        xor (t ⟨3 * (j.val + 2) + 1, by omega⟩ &&
              !(xor (t ⟨3 * (j.val + 2), by omega⟩) (t ⟨3 * (j.val + 2) + 2, by omega⟩)))
            (t ⟨3 * (j.val + 2) + 2, by omega⟩))))

def linP (r : Nat) (u t : Fin k → Bool) : Bool :=
  xorFin (fun i : Fin k =>
    decide (i ∈ neededSet r k) &&
      xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))))

lemma mem_neededSet_iff (r : Nat) (i : Fin k) :
    i ∈ neededSet r k ↔
      (if i.val = 0 ∨ i.val = k - 1 then r % 2 = 0
       else i.val = 1 ∨ i.val = k - 2 ∨ i.val % 3 ≠ 1) := by
  simp [neededSet]

lemma neededSet_c0 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) =
      if j.val = 0 then decide (r % 2 = 0) else true := by
  by_cases hj : j.val = 0
  · simp [hj, mem_neededSet_iff]
  · rw [ite_neg hj]
    apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val = 0 ∨ 3 * j.val = k - 1) := by omega
    rw [ite_neg hn]
    right; right; omega

lemma neededSet_c1 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) =
      decide (j.val = 0 ∨ j.val = r - 1) := by
  by_cases hj : j.val = 0 ∨ j.val = r - 1
  · rw [decide_eq_true hj]; apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 1 = 0 ∨ 3 * j.val + 1 = k - 1) := by omega
    rw [ite_neg hn]
    rcases hj with h0 | hl
    · left; omega
    · right; left; omega
  · rw [decide_eq_false hj]; apply decide_eq_false; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 1 = 0 ∨ 3 * j.val + 1 = k - 1) := by omega
    rw [ite_neg hn]
    omega

lemma neededSet_c2 (hr : 2 ≤ r) (hk3 : k = 3 * r) (j : Fin r) :
    decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) =
      if j.val = r - 1 then decide (r % 2 = 0) else true := by
  by_cases hj : j.val = r - 1
  · rw [ite_pos hj]
    have h1 : 3 * j.val + 2 = k - 1 := by omega
    simp [mem_neededSet_iff, h1]
  · rw [ite_neg hj]
    apply decide_eq_true; rw [mem_neededSet_iff]; dsimp only
    have hn : ¬(3 * j.val + 2 = 0 ∨ 3 * j.val + 2 = k - 1) := by omega
    rw [ite_neg hn]
    right; right; omega

lemma neededSet_res_even (hr : 2 ≤ r) (hk3 : k = 3 * r) (c : Nat) (hc : c < 3) :
    xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k)) = false := by
  interval_cases c
  · rw [xorFin_first (by omega)]
    dsimp only
    have h0 : decide (⟨3 * 0 + 0, by omega⟩ ∈ neededSet r k) = decide (r % 2 = 0) := by
      have hc0 := neededSet_c0 hr hk3 ⟨0, by omega⟩; simpa using hc0
    have ht : xorFin (fun j : Fin (r - 1) => decide (⟨3 * (j.val + 1) + 0, by omega⟩ ∈ neededSet r k)) =
        decide ((r - 1) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 1) => decide (⟨3 * (j.val + 1) + 0, by omega⟩ ∈ neededSet r k)) =
          xorFin (fun _ : Fin (r - 1) => true) :=
        xorFin_congr _ _ (fun j => by
          have hc0 := neededSet_c0 hr hk3 ⟨j.val + 1, by omega⟩
          simpa using hc0)
      rw [h1, xorFin_const, Bool.true_and]
    rw [h0, ht]
    by_cases he : r % 2 = 0
    · have ho : (r - 1) % 2 = 1 := by omega
      rw [decide_eq_true he, decide_eq_true ho]; rfl
    · have ho : ¬((r - 1) % 2 = 1) := by omega
      rw [decide_eq_false he, decide_eq_false ho]; rfl
  · rw [xorFin_ends hr]
    dsimp only
    have h0 : decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨0, by omega⟩]; simp
    have hl : decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩]; simp
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k)) = false :=
      xorFin_eq_false _ (fun j => by
        rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
        apply decide_eq_false; dsimp only; omega)
    rw [h0, hl, hm]; rfl
  · rw [xorFin_last (by omega)]
    dsimp only
    have hl : decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) = decide (r % 2 = 0) := by
      have hc2 := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      simpa using hc2
    have hm : xorFin (fun j : Fin (r - 1) => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k)) =
        decide ((r - 1) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 1) => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k)) =
          xorFin (fun _ : Fin (r - 1) => true) :=
        xorFin_congr _ _ (fun j => by
          have hc2 := neededSet_c2 hr hk3 ⟨j.val, by omega⟩
          have hne : j.val ≠ r - 1 := by omega
          simpa [hne] using hc2)
      rw [h1, xorFin_const, Bool.true_and]
    rw [hl, hm]
    by_cases he : r % 2 = 0
    · have ho : (r - 1) % 2 = 1 := by omega
      rw [decide_eq_true he, decide_eq_true ho]; rfl
    · have ho : ¬((r - 1) % 2 = 1) := by omega
      rw [decide_eq_false he, decide_eq_false ho]; rfl

lemma neededSet_zZero_cancel (hr : 2 ≤ r) (hk3 : k = 3 * r) (z0 z1 : Bool) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      zOf (fun _ => false) z0 z1 (ix hk (i.val + 1))) = false := by
  rw [xorFin_split3 hr hk3]
  have hcls : ∀ (c : Nat) (hc : c < 3) (v : Bool),
      (∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1)) = v) →
      xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) &&
        zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1))) = false := by
    intro c hc v hv
    have h1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) &&
          zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + c + 1))) =
        xorFin (fun j : Fin r => decide (⟨3 * j.val + c, by omega⟩ ∈ neededSet r k) && v) :=
      xorFin_congr _ _ (fun j => by rw [hv j])
    rw [h1, xorFin_and_right, neededSet_res_even hr hk3 c hc, Bool.false_and]
  have hv0 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 0 + 1)) = z1 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hlt : 3 * j.val + 0 + 1 < k := by omega
    have hm1 : (3 * j.val + 0 + 1) % 3 = 1 := by omega
    simp only [Nat.mod_eq_of_lt hlt, hm1]; rfl
  have hv1 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 1 + 1)) = xor z0 z1 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hlt : 3 * j.val + 1 + 1 < k := by omega
    have hm2 : (3 * j.val + 1 + 1) % 3 = 2 := by omega
    simp only [Nat.mod_eq_of_lt hlt, hm2]; rfl
  have hv2 : ∀ j : Fin r, zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 2 + 1)) = z0 := by
    intro j; unfold zOf; rw [zPair_zero]; dsimp only [ix]
    have hm0 : ((3 * j.val + 2 + 1) % k) % 3 = 0 := by
      by_cases hjl : j.val = r - 1
      · rw [show 3 * j.val + 2 + 1 = k by omega, Nat.mod_self]
      · have hlt : 3 * j.val + 2 + 1 < k := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
    simp only [hm0]; rfl
  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      zOf (fun _ => false) z0 z1 (ix hk (3 * j.val + 1))) = false := hcls 0 (by omega) z1 hv0
  have hc1 := hcls 1 (by omega) (xor z0 z1) hv1
  have hc2 := hcls 2 (by omega) z0 hv2
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]; rfl

lemma neededSet_lin_b_zero (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      xor (decide (3 ≤ i.val))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)))) = false := by
  rw [xorFin_split3 hr hk3]
  have hzmask : ∀ p : Fin k,
      zOf (fun q : Fin k => decide (3 ≤ q.val)) false false p =
        decide (4 ≤ p.val ∧ p.val % 3 = 1) := fun p => by
    unfold zOf; rw [zPair_mask3 p.val p.isLt]
  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 1)))) = false := by
    apply xorFin_eq_false; intro j
    rw [hzmask]; dsimp only [ix]
    have hlt : 3 * j.val + 1 < k := by omega
    simp only [Nat.mod_eq_of_lt hlt]
    by_cases hj : j.val = 0
    · simp [hj]
    · have h1 : 3 ≤ 3 * j.val := by omega
      have h2 : 4 ≤ 3 * j.val + 1 ∧ (3 * j.val + 1) % 3 = 1 := by omega
      rw [decide_eq_true h1, decide_eq_true h2]; simp
  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val + 1))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 1 + 1)))) = true := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * 0 + 1))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * 0 + 1 + 1)))) = false := by
      rw [hzmask]; dsimp only [ix]
      have hlt : 3 * 0 + 1 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]; simp
    have hl : (decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * (r - 1) + 1))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (r - 1) + 1 + 1)))) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩, hzmask]; dsimp only [ix]
      have hlt : 3 * (r - 1) + 1 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]
      have h1 : 3 ≤ 3 * (r - 1) + 1 := by omega
      have h2 : ¬(4 ≤ 3 * (r - 1) + 1 + 1 ∧ (3 * (r - 1) + 1 + 1) % 3 = 1) := by omega
      rw [decide_eq_true (Or.inr True.intro), decide_eq_true h1, decide_eq_false h2]; rfl
    have hm : xorFin (fun j : Fin (r - 2) =>
        decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
          xor (decide (3 ≤ 3 * (j.val + 1) + 1))
              (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 1 + 1)))) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm]; rfl
  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      xor (decide (3 ≤ 3 * j.val + 2))
          (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * j.val + 2 + 1)))) = true := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 2, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * 0 + 2))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * 0 + 2 + 1)))) = false := by
      rw [hzmask]; dsimp only [ix]
      have hlt : 3 * 0 + 2 + 1 < k := by omega
      simp only [Nat.mod_eq_of_lt hlt]; simp
    have hl : (decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) &&
        xor (decide (3 ≤ 3 * (r - 1) + 2))
            (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (r - 1) + 2 + 1)))) =
        decide (r % 2 = 0) := by
      have hn := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [ite_pos rfl] at hn
      rw [hn, hzmask]; dsimp only [ix]
      have heq : 3 * (r - 1) + 2 + 1 = k := by omega
      simp only [heq, Nat.mod_self]
      have h1 : 3 ≤ 3 * (r - 1) + 2 := by omega
      simp [h1]
    have hm : xorFin (fun j : Fin (r - 2) =>
        decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
          xor (decide (3 ≤ 3 * (j.val + 1) + 2))
              (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 2 + 1)))) =
        decide ((r - 2) % 2 = 1) := by
      have h1 : xorFin (fun j : Fin (r - 2) =>
            decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
              xor (decide (3 ≤ 3 * (j.val + 1) + 2))
                  (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (3 * (j.val + 1) + 2 + 1)))) =
          xorFin (fun _ : Fin (r - 2) => true) := by
        apply xorFin_congr; intro j
        have hn := neededSet_c2 hr hk3 ⟨j.val + 1, by omega⟩
        dsimp only at hn; rw [ite_neg (by omega)] at hn
        rw [hn, hzmask]; dsimp only [ix]
        have hlt : 3 * (j.val + 1) + 2 + 1 < k := by omega
        simp only [Nat.mod_eq_of_lt hlt]
        have h3 : 3 ≤ 3 * (j.val + 1) + 2 := by omega
        have hm0 : ¬(4 ≤ 3 * (j.val + 1) + 2 + 1 ∧ (3 * (j.val + 1) + 2 + 1) % 3 = 1) := by omega
        rw [decide_eq_true h3, decide_eq_false hm0]; rfl
      rw [h1, xorFin_const, Bool.true_and]
    rw [h0, hl, hm]
    by_cases he : r % 2 = 0
    · have hm0 : ¬((r - 2) % 2 = 1) := by omega
      rw [decide_eq_true he, decide_eq_false hm0]; rfl
    · have hm1 : (r - 2) % 2 = 1 := by omega
      rw [decide_eq_false he, decide_eq_true hm1]; rfl
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]; rfl

lemma neededSet_quad_b_one (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) (b : Bool)
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    let w := add t (fun i => b && decide (3 ≤ i.val))
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) =
    xor b (Qp hk r t) := by
  intro w
  unfold Qp
  suffices hdiff : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
          (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) = b by
    have h1 : xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))))
          (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))))) = b := by
      rw [← xorFin_xor]
      rw [← hdiff]
      apply xorFin_congr; intro i
      cases decide (i ∈ neededSet r k) <;> cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;>
        cases (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))) <;> rfl
    cases ha : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) <;>
      cases hc : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) <;>
      cases b <;> simp [ha, hc] at h1 ⊢
  have hterm : ∀ i : Fin k,
      xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
          (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2))) =
      (b && (if i.val = 0 then false
             else if i.val = 1 then !(t ⟨2, by omega⟩)
             else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
             else if i.val = k - 2 then t ⟨0, hk⟩
             else false)) := by
    intro i; unfold w add
    by_cases hi0 : i.val = 0
    · have h1 : ix hk (i.val + 1) = ⟨1, by omega⟩ := by rw [hi0]; exact ix_eq_of_lt hk (by omega)
      have h2 : ix hk (i.val + 2) = ⟨2, by omega⟩ := by rw [hi0]; exact ix_eq_of_lt hk (by omega)
      rw [h1, h2, ite_pos hi0]; simp
    · by_cases hi1 : i.val = 1
      · have h1 : ix hk (i.val + 1) = ⟨2, by omega⟩ := by rw [hi1]; exact ix_eq_of_lt hk (by omega)
        have h2 : ix hk (i.val + 2) = ⟨3, by omega⟩ := by rw [hi1]; exact ix_eq_of_lt hk (by omega)
        rw [ite_neg hi0, ite_pos hi1]
        simp only [h1, h2]
        cases b <;> cases t ⟨2, by omega⟩ <;> cases t ⟨3, by omega⟩ <;> rfl
      · by_cases hilt : i.val < k - 2
        · have h1 : (ix hk (i.val + 1)).val = i.val + 1 := by dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega)]
          have h2 : (ix hk (i.val + 2)).val = i.val + 2 := by dsimp [ix]; rw [Nat.mod_eq_of_lt (by omega)]
          rw [ite_neg hi0, ite_neg hi1, ite_pos hilt]
          simp only [h1, h2, decide_eq_true (by omega : 3 ≤ i.val + 1), decide_eq_true (by omega : 3 ≤ i.val + 2)]
          cases b <;> cases t (ix hk (i.val + 1)) <;> cases t (ix hk (i.val + 2)) <;> rfl
        · by_cases hik2 : i.val = k - 2
          · have h1 : ix hk (i.val + 1) = ⟨k - 1, by omega⟩ := by
              rw [hik2, show k - 2 + 1 = k - 1 by omega]; exact ix_eq_of_lt hk (by omega)
            have h2 : ix hk (i.val + 2) = ⟨0, hk⟩ :=
              (ix_mod_eq hk (by rw [hik2, show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
            rw [ite_neg hi0, ite_neg hi1, ite_neg hilt, ite_pos hik2]
            simp only [h1, h2, decide_eq_true (by omega : 3 ≤ k - 1)]
            cases b <;> cases t ⟨k - 1, by omega⟩ <;> cases t ⟨0, hk⟩ <;> rfl
          · have hik1 : i.val = k - 1 := by omega
            have h1 : ix hk (i.val + 1) = ⟨0, hk⟩ :=
              (ix_mod_eq hk (by rw [hik1, show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
            have h2 : ix hk (i.val + 2) = ⟨1, by omega⟩ :=
              (ix_mod_eq hk (by rw [hik1, show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
            rw [ite_neg hi0, ite_neg hi1, ite_neg hilt, ite_neg hik2]
            simp only [h1, h2]; simp
  have hfac : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
        xor (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))
            (!(t (ix hk (i.val + 1))) && t (ix hk (i.val + 2)))) =
      (b && xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
        (if i.val = 0 then false
         else if i.val = 1 then !(t ⟨2, by omega⟩)
         else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
         else if i.val = k - 2 then t ⟨0, hk⟩
         else false))) := by
    rw [← xorFin_and_left b]
    apply xorFin_congr; intro i; rw [hterm i]
    cases decide (i ∈ neededSet r k) <;> cases b <;> rfl
  rw [hfac]
  suffices hone : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      (if i.val = 0 then false
       else if i.val = 1 then !(t ⟨2, by omega⟩)
       else if i.val < k - 2 then xor (t (ix hk (i.val + 1))) (t (ix hk (i.val + 2)))
       else if i.val = k - 2 then t ⟨0, hk⟩
       else false)) = true by
    rw [hone, Bool.and_true]
  rw [xorFin_split3 hr hk3]

  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val = 0 then false
       else if 3 * j.val = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val < k - 2 then xor (t (ix hk (3 * j.val + 1))) (t (ix hk (3 * j.val + 2)))
       else if 3 * j.val = k - 2 then t ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
    rw [xorFin_first (by omega)]
    simp only [Nat.mul_zero, ite_true, Bool.and_false, Bool.false_xor]
    apply xorFin_congr; intro j
    have hn := neededSet_c0 hr hk3 ⟨j.val + 1, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * (j.val + 1) < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]

  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 1 = 0 then false
       else if 3 * j.val + 1 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val + 1 < k - 2 then xor (t (ix hk (3 * j.val + 1 + 1))) (t (ix hk (3 * j.val + 1 + 2)))
       else if 3 * j.val + 1 = k - 2 then t ⟨0, hk⟩
       else false)) =
    xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨0, by omega⟩]; simp
    have hl : decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩]; simp
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (if 3 * (j.val + 1) + 1 = 0 then false
         else if 3 * (j.val + 1) + 1 = 1 then !(t ⟨2, by omega⟩)
         else if 3 * (j.val + 1) + 1 < k - 2 then xor (t (ix hk (3 * (j.val + 1) + 1 + 1))) (t (ix hk (3 * (j.val + 1) + 1 + 2)))
         else if 3 * (j.val + 1) + 1 = k - 2 then t ⟨0, hk⟩
         else false)) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm, Bool.true_and, Bool.true_and, Bool.false_xor]
    have h00 : (3 * 0 + 1 : Nat) ≠ 0 := by omega
    have h01 : (3 * 0 + 1 : Nat) = 1 := by omega
    have hl0 : 3 * (r - 1) + 1 ≠ 0 := by omega
    have hl1 : 3 * (r - 1) + 1 ≠ 1 := by omega
    have hll : ¬(3 * (r - 1) + 1 < k - 2) := by omega
    have hlk : 3 * (r - 1) + 1 = k - 2 := by omega
    rw [ite_neg h00, ite_pos h01, ite_neg hl0, ite_neg hl1, ite_neg hll, ite_pos hlk]

  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 2 = 0 then false
       else if 3 * j.val + 2 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * j.val + 2 < k - 2 then xor (t (ix hk (3 * j.val + 2 + 1))) (t (ix hk (3 * j.val + 2 + 2)))
       else if 3 * j.val + 2 = k - 2 then t ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)) := by
    rw [xorFin_last (by omega)]; dsimp only
    have hlast : (if 3 * (r - 1) + 2 = 0 then false
       else if 3 * (r - 1) + 2 = 1 then !(t ⟨2, by omega⟩)
       else if 3 * (r - 1) + 2 < k - 2 then xor (t (ix hk (3 * (r - 1) + 2 + 1))) (t (ix hk (3 * (r - 1) + 2 + 2)))
       else if 3 * (r - 1) + 2 = k - 2 then t ⟨0, hk⟩
       else false) = false := by
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    rw [hlast, Bool.and_false, Bool.xor_false]
    apply xorFin_congr; intro j
    have hn := neededSet_c2 hr hk3 ⟨j.val, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * j.val + 2 < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    exact congrArg₂ xor (congrArg t (Fin.ext (by dsimp only; omega))) (congrArg t (Fin.ext (by dsimp only; omega)))
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]

  have hpair : xor (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩))) =
    xor (xor (resSum r hk3 t 0 (by omega)) (t ⟨0, hk⟩))
        (xor (resSum r hk3 t 2 (by omega)) (t ⟨2, by omega⟩)) := by
    have htele : xor (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
        (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩))
          (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
      rw [← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro j
      cases t ⟨3 * (j.val + 1), by omega⟩ <;> cases t ⟨3 * (j.val + 1) + 1, by omega⟩ <;>
        cases t ⟨3 * (j.val + 1) + 2, by omega⟩ <;> rfl
    have hs0 : resSum r hk3 t 0 (by omega) =
        xor (t ⟨0, hk⟩) (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩)) := by
      unfold resSum; rw [xorFin_first (by omega)]; rfl
    have hs2 : resSum r hk3 t 2 (by omega) =
        xor (t ⟨2, by omega⟩) (xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
      unfold resSum; rw [xorFin_first (by omega)]; rfl
    rw [htele, hs0, hs2]
    cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1), by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 1) => t ⟨3 * (j.val + 1) + 2, by omega⟩) <;> rfl
  have hcomm : xor (xorFin (fun j : Fin (r - 1) =>
        xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xor (xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩))
           (xorFin (fun j : Fin (r - 1) =>
             xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)))) =
    xor (xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩))
        (xor (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)))
        (xorFin (fun j : Fin (r - 1) =>
          xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)))) := by
    cases xorFin (fun j : Fin (r - 1) => xor (t ⟨3 * (j.val + 1) + 1, by omega⟩) (t ⟨3 * (j.val + 1) + 2, by omega⟩)) <;>
      cases xor (!(t ⟨2, by omega⟩)) (t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 1) => xor (t ⟨3 * (j.val + 1), by omega⟩) (t ⟨3 * (j.val + 1) + 1, by omega⟩)) <;> rfl
  rw [hcomm, hpair, hs02]
  cases resSum r hk3 t 2 (by omega) <;> cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;> rfl

lemma row_recovery (hr : 2 ≤ r) (hk3 : k = 3 * r) (u t : Fin k → Bool) (b z0 z1 : Bool)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    let w := add t (fun i => b && decide (3 ≤ i.val))
    let z := zOf w z0 z1
    let x := fun i : Fin k => xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))
    mix hk (add u (rot hk x)) = w ∧
    x ⟨0, hk⟩ = xor z1 (u ⟨1, by omega⟩) ∧
    x ⟨k - 1, by omega⟩ = xor z0 (u ⟨0, hk⟩) ∧
    row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) ∧
    row hk u x ⟨k - 1, by omega⟩ = xor (xor (xor b (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) ∧
    decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
      xor b (xor (Qp hk r t) (linP hk r u t)) := by
  intro w z x
  have hrot_x : add u (rot hk x) = z := by
    funext i; unfold add rot x
    have hidx : ix hk ((ix hk (i.val + k - 1)).val + 1) = i := by
      have hinner : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
        dsimp only [ix]; split_ifs with h0
        · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      apply Fin.ext
      change ((ix hk (i.val + k - 1)).val + 1) % k = i.val
      rw [hinner]; split_ifs with h0
      · rw [show k - 1 + 1 = k by omega, Nat.mod_self]; omega
      · rw [show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
    rw [hidx]
    cases u i <;> cases z i <;> rfl
  have hres_w : resSum r hk3 w 0 (by omega) = resSum r hk3 w 1 (by omega) ∧
      resSum r hk3 w 0 (by omega) = resSum r hk3 w 2 (by omega) := by
    have hres_c : ∀ (c : Nat) (hc : c < 3),
        resSum r hk3 w c hc = xor (resSum r hk3 t c hc) (b && decide ((r - 1) % 2 = 1)) := by
      intro c hc; unfold resSum
      rw [xorFin_first (by omega) (fun j : Fin r => w ⟨3 * j.val + c, by omega⟩),
        xorFin_first (by omega) (fun j : Fin r => t ⟨3 * j.val + c, by omega⟩)]
      unfold w add; dsimp only
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [decide_eq_false (by omega : ¬(3 ≤ c)), Bool.and_false, Bool.xor_false, xorFin_xor]
      have hm : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
          (b && decide ((r - 1) % 2 = 1)) := by
        have h1 : xorFin (fun j : Fin (r - 1) => b && decide (3 ≤ 3 * (j.val + 1) + c)) =
            xorFin (fun _ : Fin (r - 1) => b) :=
          xorFin_congr _ _ (fun j => by rw [decide_eq_true (by omega), Bool.and_true])
        rw [h1, xorFin_const]
      rw [hm, Bool.xor_assoc]
    have h0 := hres_c 0 (by omega)
    have h1 := hres_c 1 (by omega)
    have h2 := hres_c 2 (by omega)
    rw [h0, h1, h2]
    exact ⟨by rw [hs01], by rw [hs02]⟩
  have hmix : mix hk (add u (rot hk x)) = w := by
    rw [hrot_x]; exact mix_zOf hk hr hk3 w z0 z1 hres_w.1 hres_w.2
  have hx0 : x ⟨0, hk⟩ = xor z1 (u ⟨1, by omega⟩) := by
    unfold x; dsimp only; rw [ix_eq_of_lt hk (by omega)]; rfl
  have hxk : x ⟨k - 1, by omega⟩ = xor z0 (u ⟨0, hk⟩) := by
    unfold x; dsimp only
    rw [(ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)]
    rfl
  have hrow0 : row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) := by
    unfold row; rw [hmix]; unfold add chi Q0; dsimp only
    rw [ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    unfold w add; dsimp only
    rw [show decide (3 ≤ 0) = false from rfl, show decide (3 ≤ 1) = false from rfl,
      show decide (3 ≤ 2) = false from rfl]
    simp
  have hrowk : row hk u x ⟨k - 1, by omega⟩ =
      xor (xor (xor b (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) := by
    unfold row; rw [hmix]; unfold add chi Qk; dsimp only
    have h1 : ix hk (k - 1 + 1) = ⟨0, hk⟩ :=
      (ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
    have h2 : ix hk (k - 1 + 2) = ⟨1, by omega⟩ :=
      (ix_mod_eq hk (by rw [show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
    rw [h1, h2]; unfold w add; dsimp only
    rw [decide_eq_true (by omega : 3 ≤ k - 1), show decide (3 ≤ 0) = false from rfl,
      show decide (3 ≤ 1) = false from rfl]
    simp only [Bool.and_true, Bool.and_false, Bool.xor_false]
    cases b <;> cases t ⟨k - 1, by omega⟩ <;> cases (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) <;>
      cases x ⟨k - 1, by omega⟩ <;> rfl
  have hpar : decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
      xor b (xor (Qp hk r t) (linP hk r u t)) := by
    rw [xorFin_finset_card]
    have hrow_eq : ∀ i : Fin k, row hk u x i =
        xor (xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))))
          (xor (b && xor (decide (3 ≤ i.val))
                         (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1))))
            (xor (zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)))
                 (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))))) := by
      intro i; unfold row; rw [hmix]; unfold add chi
      have hz_decomp : ∀ q : Fin k, z q =
          xor (zOf t false false q)
            (xor (b && zOf (fun p : Fin k => decide (3 ≤ p.val)) false false q)
                 (zOf (fun _ => false) z0 z1 q)) := by
        intro q; unfold z w
        have h1 : add t (fun p : Fin k => b && decide (3 ≤ p.val)) =
            add (add t (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) := by
          funext p; unfold add; simp
        have h2 : zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) z0 z1 q =
            xor (zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) false false q)
                (zOf (fun _ => false) z0 z1 q) := by
          have hz := zOf_xor (add t (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) false false z0 z1 q
          simp only [Bool.false_xor] at hz
          rw [← h1] at hz; exact hz
        have h3 : zOf (add t (fun p : Fin k => b && decide (3 ≤ p.val))) false false q =
            xor (zOf t false false q) (b && zOf (fun p : Fin k => decide (3 ≤ p.val)) false false q) := by
          have hz := zOf_xor t (fun p : Fin k => b && decide (3 ≤ p.val)) false false false false q
          simp only [Bool.false_xor] at hz
          rw [hz]; congr 1
          cases b
          · simp only [Bool.false_and]
            unfold zOf; rw [zPair_zero]; simp
          · simp only [Bool.true_and]
        rw [h2, h3, Bool.xor_assoc]
      unfold x; rw [hz_decomp]
      change xor (xor (xor (t i) (b && decide (3 ≤ i.val))) (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2)))) _ = _
      cases t i <;> cases b <;> cases decide (3 ≤ i.val) <;>
        cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;>
        cases zOf t false false (ix hk (i.val + 1)) <;>
        cases zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)) <;>
        cases zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)) <;>
        cases u (ix hk (i.val + 1)) <;> rfl
    have hsplit : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && row hk u x i) =
        xor (linP hk r u t)
          (xor (b && xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                  xor (decide (3 ≤ i.val))
                      (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1)))))
            (xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                    zOf (fun _ => false) z0 z1 (ix hk (i.val + 1))))
                 (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
                    (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))))))) := by
      unfold linP
      rw [← xorFin_and_left, ← xorFin_xor, ← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro i; rw [hrow_eq i]
      cases decide (i ∈ neededSet r k) <;> cases b <;>
        cases xor (t i) (xor (zOf t false false (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))) <;>
        cases xor (decide (3 ≤ i.val)) (zOf (fun p : Fin k => decide (3 ≤ p.val)) false false (ix hk (i.val + 1))) <;>
        cases zOf (fun _ => false) z0 z1 (ix hk (i.val + 1)) <;>
        cases (!(w (ix hk (i.val + 1))) && w (ix hk (i.val + 2))) <;> rfl
    rw [hsplit, neededSet_lin_b_zero hk hr hk3, neededSet_zZero_cancel hk hr hk3,
      neededSet_quad_b_one hk hr hk3 t b hs02]
    simp only [Bool.and_false, Bool.false_xor]
    cases b <;> cases Qp hk r t <;> cases linP hk r u t <;> rfl
  exact ⟨hmix, hx0, hxk, hrow0, hrowk, hpar⟩

lemma recovery_from_record (hr : 2 ≤ r) (hk3 : k = 3 * r) (u x : Fin k → Bool) :
    let t := tOfD hr hk3 (diffFn hk u x)
    let bp := decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1)
    let b0 := row hk u x ⟨0, hk⟩
    let bk := row hk u x ⟨k - 1, by omega⟩
    let b := xor bp (xor (Qp hk r t) (linP hk r u t))
    let x0 := xor b0 (xor (t ⟨0, hk⟩) (Q0 hr hk3 t))
    let xk := xor bk (xor b (xor (t ⟨k - 1, by omega⟩) (Qk hr hk3 t)))
    let w := add t (fun i => b && decide (3 ≤ i.val))
    let z := zOf w (xor xk (u ⟨0, hk⟩)) (xor x0 (u ⟨1, by omega⟩))
    ∀ i : Fin k, x i = xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1))) := by
  intro t bp b0 bk b x0 xk w z
  let z_true := add u (rot hk x)
  let w_true := mix hk z_true
  let b_true := w_true ⟨3, by omega⟩
  have htd := tOfD_diff hk hr hk3 u x
  have hzt : z_true = zOf w_true (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) :=
    (zOf_mix hk hr hk3 z_true).symm
  have hx_eq : x = fun i : Fin k => xor (z_true (ix hk (i.val + 1))) (u (ix hk (i.val + 1))) := by
    funext i; unfold z_true add rot
    have hidx : ix hk ((ix hk (i.val + 1)).val + k - 1) = i := by
      have hinner : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
        dsimp only [ix]; split_ifs with hl
        · rw [show i.val + 1 = k by omega, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega)]
      apply Fin.ext
      change ((ix hk (i.val + 1)).val + k - 1) % k = i.val
      rw [hinner]; split_ifs with hl
      · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
      · rw [show i.val + 1 + k - 1 = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [hidx]; cases u (ix hk (i.val + 1)) <;> cases x i <;> rfl
  have hrec := row_recovery hk hr hk3 u t b_true (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) htd.2.2.1 htd.2.2.2
  have hw_eq : add t (fun i => b_true && decide (3 ≤ i.val)) = w_true := htd.2.1.symm
  have hx_eq2 : (fun i : Fin k => xor (zOf (add t (fun i => b_true && decide (3 ≤ i.val)))
      (z_true ⟨0, hk⟩) (z_true ⟨1, by omega⟩) (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))) = x := by
    rw [hw_eq, ← hzt]; exact hx_eq.symm
  have hrec_x : x ⟨0, hk⟩ = xor (z_true ⟨1, by omega⟩) (u ⟨1, by omega⟩) ∧
      x ⟨k - 1, by omega⟩ = xor (z_true ⟨0, hk⟩) (u ⟨0, hk⟩) ∧
      row hk u x ⟨0, hk⟩ = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) ∧
      row hk u x ⟨k - 1, by omega⟩ = xor (xor (xor b_true (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) ∧
      decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
        xor b_true (xor (Qp hk r t) (linP hk r u t)) := by
    dsimp only at hrec
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← congrFun hx_eq2 ⟨0, hk⟩]; exact hrec.2.1
    · rw [← congrFun hx_eq2 ⟨k - 1, by omega⟩]; exact hrec.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.2.1
    · rw [← hx_eq2]; exact hrec.2.2.2.2.2
  have hb_eq : b = b_true := by
    change xor bp (xor (Qp hk r t) (linP hk r u t)) = b_true
    rw [show bp = xor b_true (xor (Qp hk r t) (linP hk r u t)) from hrec_x.2.2.2.2]
    cases b_true <;> cases Qp hk r t <;> cases linP hk r u t <;> rfl
  have hx0_eq : x0 = x ⟨0, hk⟩ := by
    change xor b0 (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) = x ⟨0, hk⟩
    rw [show b0 = xor (xor (t ⟨0, hk⟩) (Q0 hr hk3 t)) (x ⟨0, hk⟩) from hrec_x.2.2.1]
    cases xor (t ⟨0, hk⟩) (Q0 hr hk3 t) <;> cases x ⟨0, hk⟩ <;> rfl
  have hxk_eq : xk = x ⟨k - 1, by omega⟩ := by
    change xor bk (xor b (xor (t ⟨k - 1, by omega⟩) (Qk hr hk3 t))) = x ⟨k - 1, by omega⟩
    rw [hb_eq, show bk = xor (xor (xor b_true (t ⟨k - 1, by omega⟩)) (Qk hr hk3 t)) (x ⟨k - 1, by omega⟩) from hrec_x.2.2.2.1]
    cases b_true <;> cases t ⟨k - 1, by omega⟩ <;> cases Qk hr hk3 t <;> cases x ⟨k - 1, by omega⟩ <;> rfl
  have hz0_eq : xor xk (u ⟨0, hk⟩) = z_true ⟨0, hk⟩ := by
    rw [hxk_eq, hrec_x.2.1]; cases z_true ⟨0, hk⟩ <;> cases u ⟨0, hk⟩ <;> rfl
  have hz1_eq : xor x0 (u ⟨1, by omega⟩) = z_true ⟨1, by omega⟩ := by
    rw [hx0_eq, hrec_x.1]; cases z_true ⟨1, by omega⟩ <;> cases u ⟨1, by omega⟩ <;> rfl
  have hz_eq : z = z_true := by
    unfold z w; rw [hb_eq, hz0_eq, hz1_eq, hw_eq, ← hzt]
  intro i; rw [hz_eq]; exact congrFun hx_eq i

lemma neededSet_card (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    (neededSet r k).card = 4 * (r / 2) + 2 := by
  have hk : 0 < k := by omega
  let S0 : Finset (Fin k) := (neededSet r k).filter (fun i => i.val % 3 = 0)
  let S1 : Finset (Fin k) := (neededSet r k).filter (fun i => i.val % 3 = 1)
  let S2 : Finset (Fin k) := (neededSet r k).filter (fun i => i.val % 3 = 2)
  have hunion : neededSet r k = S0 ∪ (S1 ∪ S2) := by
    ext i
    simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with h | h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr (Or.inl ⟨hi, h⟩)
      · exact Or.inr (Or.inr ⟨hi, h⟩)
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hd0 : Disjoint S0 (S1 ∪ S2) := by
    rw [Finset.disjoint_left]
    intro i h0 h12
    simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter] at h0 h12
    rcases h12 with ⟨_, h1⟩ | ⟨_, h2⟩ <;> omega
  have hd12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2
    omega
  have hcard : (neededSet r k).card = S0.card + S1.card + S2.card := by
    rw [hunion, Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12, Nat.add_assoc]
  have hf0_inj : Function.Injective (fun j : Fin r => (⟨3 * j.val, by omega⟩ : Fin k)) := by
    intro a b hab
    have hv : 3 * a.val = 3 * b.val := congrArg Fin.val hab
    exact Fin.ext (by omega)
  have hf1_inj : Function.Injective (fun j : Fin r => (⟨3 * j.val + 1, by omega⟩ : Fin k)) := by
    intro a b hab
    have hv : 3 * a.val + 1 = 3 * b.val + 1 := congrArg Fin.val hab
    exact Fin.ext (by omega)
  have hf2_inj : Function.Injective (fun j : Fin r => (⟨3 * j.val + 2, by omega⟩ : Fin k)) := by
    intro a b hab
    have hv : 3 * a.val + 2 = 3 * b.val + 2 := congrArg Fin.val hab
    exact Fin.ext (by omega)
  have hS0 : S0.card = if r % 2 = 0 then r else r - 1 := by
    let A0 : Finset (Fin r) := if r % 2 = 0 then Finset.univ else Finset.univ.erase ⟨0, by omega⟩
    have hS0_eq : S0 = A0.image (fun j : Fin r => (⟨3 * j.val, by omega⟩ : Fin k)) := by
      ext i
      simp only [S0, A0, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hi, hm0⟩
        refine ⟨⟨i.val / 3, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
        have hdec := neededSet_c0 hr hk3 ⟨i.val / 3, by omega⟩
        have hie : (⟨3 * (i.val / 3), by omega⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
        rw [hie, decide_eq_true hi] at hdec
        split_ifs with he
        · exact Finset.mem_univ _
        · rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro h0
          have hv0 : i.val / 3 = 0 := congrArg Fin.val h0
          dsimp only at hdec
          rw [ite_pos hv0] at hdec
          rw [decide_eq_false he] at hdec
          cases hdec
      · rintro ⟨j, hj, rfl⟩
        refine ⟨?_, by dsimp only; omega⟩
        have hdec := neededSet_c0 hr hk3 j
        by_cases hj0 : j.val = 0
        · split_ifs at hj with he
          · rw [ite_pos hj0, decide_eq_true he] at hdec
            exact of_decide_eq_true hdec
          · rw [Finset.mem_erase] at hj
            exact False.elim (hj.1 (Fin.ext hj0))
        · rw [ite_neg hj0] at hdec
          exact of_decide_eq_true hdec
    rw [hS0_eq, Finset.card_image_of_injective A0 hf0_inj]
    dsimp only [A0]
    split_ifs
    · rw [Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hS1 : S1.card = 2 := by
    let A1 : Finset (Fin r) := {⟨0, by omega⟩, ⟨r - 1, by omega⟩}
    have hS1_eq : S1 = A1.image (fun j : Fin r => (⟨3 * j.val + 1, by omega⟩ : Fin k)) := by
      ext i
      simp only [S1, A1, Finset.mem_filter, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hm1⟩
        refine ⟨⟨i.val / 3, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
        have hdec := neededSet_c1 hr hk3 ⟨i.val / 3, by omega⟩
        have hie : (⟨3 * (i.val / 3) + 1, by omega⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
        rw [hie, decide_eq_true hi] at hdec
        have hor : i.val / 3 = 0 ∨ i.val / 3 = r - 1 := of_decide_eq_true hdec.symm
        rcases hor with h0 | hl
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext hl)
      · rintro ⟨j, hj, rfl⟩
        refine ⟨?_, by dsimp only; omega⟩
        have hdec := neededSet_c1 hr hk3 j
        have hor : j.val = 0 ∨ j.val = r - 1 := by
          rcases hj with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        rw [decide_eq_true hor] at hdec
        exact of_decide_eq_true hdec
    rw [hS1_eq, Finset.card_image_of_injective A1 hf1_inj]
    have hne : (⟨0, by omega⟩ : Fin r) ≠ ⟨r - 1, by omega⟩ := by
      intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
    exact Finset.card_pair hne
  have hS2 : S2.card = if r % 2 = 0 then r else r - 1 := by
    let A2 : Finset (Fin r) := if r % 2 = 0 then Finset.univ else Finset.univ.erase ⟨r - 1, by omega⟩
    have hS2_eq : S2 = A2.image (fun j : Fin r => (⟨3 * j.val + 2, by omega⟩ : Fin k)) := by
      ext i
      simp only [S2, A2, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hi, hm2⟩
        refine ⟨⟨i.val / 3, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
        have hdec := neededSet_c2 hr hk3 ⟨i.val / 3, by omega⟩
        have hie : (⟨3 * (i.val / 3) + 2, by omega⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
        rw [hie, decide_eq_true hi] at hdec
        split_ifs with he
        · exact Finset.mem_univ _
        · rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro hl
          have hvl : i.val / 3 = r - 1 := congrArg Fin.val hl
          dsimp only at hdec
          rw [ite_pos hvl, decide_eq_false he] at hdec
          cases hdec
      · rintro ⟨j, hj, rfl⟩
        refine ⟨?_, by dsimp only; omega⟩
        have hdec := neededSet_c2 hr hk3 j
        by_cases hjl : j.val = r - 1
        · split_ifs at hj with he
          · rw [ite_pos hjl, decide_eq_true he] at hdec
            exact of_decide_eq_true hdec
          · rw [Finset.mem_erase] at hj
            exact False.elim (hj.1 (Fin.ext hjl))
        · rw [ite_neg hjl] at hdec
          exact of_decide_eq_true hdec
    rw [hS2_eq, Finset.card_image_of_injective A2 hf2_inj]
    dsimp only [A2]
    split_ifs
    · rw [Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hcard, hS0, hS1, hS2]
  split_ifs <;> omega

lemma ix_prev_next (i : Fin k) :
    ix hk ((ix hk (i.val + 1)).val + k - 1) = i := by
  have hinner : (ix hk (i.val + 1)).val = if i.val = k - 1 then 0 else i.val + 1 := by
    dsimp only [ix]; split_ifs with hl
    · rw [show i.val + 1 = k by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  apply Fin.ext
  change ((ix hk (i.val + 1)).val + k - 1) % k = i.val
  rw [hinner]; split_ifs with hl
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show i.val + 1 + k - 1 = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma ix_next_prev (i : Fin k) :
    ix hk ((ix hk (i.val + k - 1)).val + 1) = i := by
  have hinner : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
    dsimp only [ix]; split_ifs with h0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  apply Fin.ext
  change ((ix hk (i.val + k - 1)).val + 1) % k = i.val
  rw [hinner]; split_ifs with h0
  · rw [show k - 1 + 1 = k by omega, Nat.mod_self]; omega
  · rw [show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]

lemma add_rot_unrot (u z : Fin k → Bool) :
    add u (rot hk (fun i : Fin k => xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1))))) = z := by
  funext i; unfold add rot; dsimp only
  rw [ix_next_prev hk i]
  cases u i <;> cases z i <;> rfl

lemma row_eq_of_diff_needed (hr : 2 ≤ r) (hk3 : k = 3 * r) (u a b : Fin k → Bool)
    (hdiff : diffFn hk u a = diffFn hk u b)
    (hrow : ∀ i : Fin k, i ∈ neededSet r k → row hk u a i = row hk u b i) :
    a = b := by
  let za := add u (rot hk a)
  let zb := add u (rot hk b)
  let wa := mix hk za
  let wb := mix hk zb
  let ba := wa ⟨3, by omega⟩
  let bb := wb ⟨3, by omega⟩
  let t := tOfD hr hk3 (diffFn hk u a)
  have htda := tOfD_diff hk hr hk3 u a
  have htdb := tOfD_diff hk hr hk3 u b
  have htb : tOfD hr hk3 (diffFn hk u b) = t := by dsimp only [t]; rw [hdiff]
  have hrec_par : ∀ x : Fin k → Bool,
      let z := add u (rot hk x)
      let w := mix hk z
      let bx := w ⟨3, by omega⟩
      let tx := tOfD hr hk3 (diffFn hk u x)
      decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) =
        xor bx (xor (Qp hk r tx) (linP hk r u tx)) := by
    intro x z w bx tx
    have htd := tOfD_diff hk hr hk3 u x
    have hzt : z = zOf w (z ⟨0, hk⟩) (z ⟨1, by omega⟩) := (zOf_mix hk hr hk3 z).symm
    have hx_eq : x = fun i : Fin k => xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1))) := by
      funext i; unfold z add rot
      rw [ix_prev_next hk i]
      cases u (ix hk (i.val + 1)) <;> cases x i <;> rfl
    have hrec := row_recovery hk hr hk3 u tx bx (z ⟨0, hk⟩) (z ⟨1, by omega⟩) htd.2.2.1 htd.2.2.2
    have hw_eq : add tx (fun i => bx && decide (3 ≤ i.val)) = w := htd.2.1.symm
    have hx_eq2 : (fun i : Fin k => xor (zOf (add tx (fun i => bx && decide (3 ≤ i.val)))
        (z ⟨0, hk⟩) (z ⟨1, by omega⟩) (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))) = x := by
      rw [hw_eq, ← hzt]; exact hx_eq.symm
    dsimp only at hrec
    rw [← hx_eq2]
    exact hrec.2.2.2.2.2
  have hpa := hrec_par a
  have hpb := hrec_par b
  dsimp only at hpa hpb
  rw [htb] at hpb
  have hfilt : (neededSet r k).filter (fun i => row hk u a i = true) =
      (neededSet r k).filter (fun i => row hk u b i = true) :=
    Finset.filter_congr (fun i hi => by rw [hrow i hi])
  have hpar_eq : xor ba (xor (Qp hk r t) (linP hk r u t)) =
      xor bb (xor (Qp hk r t) (linP hk r u t)) := by
    rw [← hpa, ← hpb, hfilt]
  have hba_eq : ba = bb := by
    cases h1 : ba <;> cases h2 : bb <;> cases h3 : xor (Qp hk r t) (linP hk r u t) <;>
      simp [h1, h2, h3] at hpar_eq ⊢
  have hwa_eq : wa = wb := by
    have h1 : wa = add t (fun i => ba && decide (3 ≤ i.val)) := htda.2.1
    have h2 : wb = add t (fun i => bb && decide (3 ≤ i.val)) := by
      have h2' := htdb.2.1; rw [htb] at h2'; exact h2'
    rw [h1, h2, hba_eq]
  have ha_eq_on : ∀ i : Fin k, i ∈ neededSet r k → a i = b i := by
    intro i hi
    have hr_eq := hrow i hi
    unfold row add at hr_eq
    change xor (chi hk wa i) (a i) = xor (chi hk wb i) (b i) at hr_eq
    rw [hwa_eq] at hr_eq
    cases hc : chi hk wb i <;> cases ha : a i <;> cases hb : b i <;> simp [hc, ha, hb] at hr_eq ⊢
  have h1_mem : (⟨1, by omega⟩ : Fin k) ∈ neededSet r k := by
    have h := neededSet_c1 hr hk3 ⟨0, by omega⟩
    dsimp only at h
    exact of_decide_eq_true (by simpa using h)
  have h2_mem : (⟨2, by omega⟩ : Fin k) ∈ neededSet r k := by
    have h := neededSet_c2 hr hk3 ⟨0, by omega⟩
    have hne : (0 : Nat) ≠ r - 1 := by omega
    dsimp only at h
    rw [ite_neg hne] at h
    exact of_decide_eq_true (by simpa using h)
  have ha1 : a ⟨1, by omega⟩ = b ⟨1, by omega⟩ := ha_eq_on ⟨1, by omega⟩ h1_mem
  have ha2 : a ⟨2, by omega⟩ = b ⟨2, by omega⟩ := ha_eq_on ⟨2, by omega⟩ h2_mem
  let δ := add za zb
  have hmix_δ : mix hk δ = fun _ => false := by
    unfold δ
    rw [mix_add hk za zb]
    funext i; unfold add; change xor (wa i) (wb i) = false
    rw [hwa_eq, Bool.xor_self]
  have hδ_zero : ∀ q : Fin k, δ q = zOf (fun _ => false) (δ ⟨0, hk⟩) (δ ⟨1, by omega⟩) q := by
    intro q
    have hz := zOf_mix hk hr hk3 δ
    rw [hmix_δ] at hz
    exact (congrFun hz q).symm
  have hδ2 : δ ⟨2, by omega⟩ = false := by
    unfold δ za zb add rot
    have hix : ix hk (2 + k - 1) = ⟨1, by omega⟩ :=
      (ix_mod_eq hk (by rw [show 2 + k - 1 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
    dsimp only; rw [hix, ha1]
    cases u ⟨2, by omega⟩ <;> cases b ⟨1, by omega⟩ <;> rfl
  have hδ3 : δ ⟨3, by omega⟩ = false := by
    unfold δ za zb add rot
    have hix : ix hk (3 + k - 1) = ⟨2, by omega⟩ :=
      (ix_mod_eq hk (by rw [show 3 + k - 1 = 2 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
    dsimp only; rw [hix, ha2]
    cases u ⟨3, by omega⟩ <;> cases b ⟨2, by omega⟩ <;> rfl
  have hδ0 : δ ⟨0, hk⟩ = false := by
    have h := hδ_zero ⟨3, by omega⟩
    unfold zOf at h; rw [zPair_zero] at h
    simp only [hδ3] at h
    exact h.symm
  have hδ1 : δ ⟨1, by omega⟩ = false := by
    have h := hδ_zero ⟨2, by omega⟩
    unfold zOf at h; rw [zPair_zero] at h
    simp only [hδ2, hδ0, Bool.false_xor] at h
    exact h.symm
  have hza_eq : za = zb := by
    funext q
    have h := hδ_zero q
    unfold zOf at h; rw [zPair_zero, hδ0, hδ1] at h
    have hq : δ q = false := by
      rw [h]; dsimp only; split_ifs <;> rfl
    unfold δ add at hq
    cases h1 : za q <;> cases h2 : zb q <;> simp [h1, h2] at hq ⊢
  funext i
  have hq := congrFun hza_eq (ix hk (i.val + 1))
  unfold za zb add rot at hq
  rw [ix_prev_next hk i] at hq
  cases hu : u (ix hk (i.val + 1)) <;> cases h1 : a i <;> cases h2 : b i <;> simp [hu, h1, h2] at hq ⊢

lemma neededSet_all_xor_false (hr : 2 ≤ r) (hk3 : k = 3 * r) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k)) = false := by
  rw [xorFin_split3 hr hk3]
  have h0 := neededSet_res_even hr hk3 0 (by omega)
  have h1 := neededSet_res_even hr hk3 1 (by omega)
  have h2 := neededSet_res_even hr hk3 2 (by omega)
  have h0' : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k)) = false := by
    simpa using h0
  rw [h0', h1, h2]; rfl

lemma tOfD_resSum01 (hr : 2 ≤ r) (hk3 : k = 3 * r) (d : Fin k → Bool) :
    resSum r hk3 (tOfD hr hk3 d) 0 (by omega) = resSum r hk3 (tOfD hr hk3 d) 1 (by omega) := by
  unfold resSum
  have hl := xorFin_first (by omega : 1 ≤ r) (fun j : Fin r => tOfD hr hk3 d ⟨3 * j.val + 0, by omega⟩)
  have hr' := xorFin_first (by omega : 1 ≤ r) (fun j : Fin r => tOfD hr hk3 d ⟨3 * j.val + 1, by omega⟩)
  rw [hl, hr']
  dsimp only
  have h0 : tOfD hr hk3 d ⟨3 * 0 + 0, by omega⟩ = tRaw hr hk3 d ⟨0, hk_of hr hk3⟩ := by
    unfold tOfD; dsimp only; rw [ite_neg (by omega)]
  have h1 : tOfD hr hk3 d ⟨3 * 0 + 1, by omega⟩ =
      xor (tRaw hr hk3 d ⟨0, hk_of hr hk3⟩)
        (xorFin (fun j : Fin (r - 1) =>
          xor (tRaw hr hk3 d ⟨3 * (j.val + 1), by omega⟩)
              (tRaw hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩))) := by
    unfold tOfD; dsimp only; rw [ite_pos (by omega)]
  have ht0 : xorFin (fun j : Fin (r - 1) => tOfD hr hk3 d ⟨3 * (j.val + 1) + 0, by omega⟩) =
      xorFin (fun j : Fin (r - 1) => tRaw hr hk3 d ⟨3 * (j.val + 1), by omega⟩) :=
    xorFin_congr _ _ (fun j => by unfold tOfD; dsimp only; rw [ite_neg (by omega)]; rfl)
  have ht1 : xorFin (fun j : Fin (r - 1) => tOfD hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩) =
      xorFin (fun j : Fin (r - 1) => tRaw hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩) :=
    xorFin_congr _ _ (fun j => by unfold tOfD; dsimp only; rw [ite_neg (by omega)])
  rw [h0, h1, ht0, ht1, xorFin_xor]
  cases tRaw hr hk3 d ⟨0, hk_of hr hk3⟩ <;>
    cases xorFin (fun j : Fin (r - 1) => tRaw hr hk3 d ⟨3 * (j.val + 1), by omega⟩) <;>
    cases xorFin (fun j : Fin (r - 1) => tRaw hr hk3 d ⟨3 * (j.val + 1) + 1, by omega⟩) <;> rfl

lemma neededSet_g_sum (hr : 2 ≤ r) (hk3 : k = 3 * r) (w0 : Fin k → Bool) :
    xorFin (fun i : Fin k => decide (i ∈ neededSet r k) &&
      (if i.val = 0 then false
       else if i.val = 1 then !(w0 ⟨2, by omega⟩)
       else if i.val < k - 2 then xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2)))
       else if i.val = k - 2 then w0 ⟨0, hk⟩
       else false)) =
    xor true (xor (resSum r hk3 w0 0 (by omega)) (resSum r hk3 w0 2 (by omega))) := by
  rw [xorFin_split3 hr hk3]
  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val = 0 then false
       else if 3 * j.val = 1 then !(w0 ⟨2, by omega⟩)
       else if 3 * j.val < k - 2 then xor (w0 (ix hk (3 * j.val + 1))) (w0 (ix hk (3 * j.val + 2)))
       else if 3 * j.val = k - 2 then w0 ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (w0 ⟨3 * (j.val + 1) + 1, by omega⟩) (w0 ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
    rw [xorFin_first (by omega)]
    simp only [Nat.mul_zero, ite_true, Bool.and_false, Bool.false_xor]
    apply xorFin_congr; intro j
    have hn := neededSet_c0 hr hk3 ⟨j.val + 1, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * (j.val + 1) < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 1 = 0 then false
       else if 3 * j.val + 1 = 1 then !(w0 ⟨2, by omega⟩)
       else if 3 * j.val + 1 < k - 2 then xor (w0 (ix hk (3 * j.val + 1 + 1))) (w0 (ix hk (3 * j.val + 1 + 2)))
       else if 3 * j.val + 1 = k - 2 then w0 ⟨0, hk⟩
       else false)) =
    xor (!(w0 ⟨2, by omega⟩)) (w0 ⟨0, hk⟩) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨0, by omega⟩]; simp
    have hl : decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) = true := by
      rw [neededSet_c1 hr hk3 ⟨r - 1, by omega⟩]; simp
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (if 3 * (j.val + 1) + 1 = 0 then false
         else if 3 * (j.val + 1) + 1 = 1 then !(w0 ⟨2, by omega⟩)
         else if 3 * (j.val + 1) + 1 < k - 2 then xor (w0 (ix hk (3 * (j.val + 1) + 1 + 1))) (w0 (ix hk (3 * (j.val + 1) + 1 + 2)))
         else if 3 * (j.val + 1) + 1 = k - 2 then w0 ⟨0, hk⟩
         else false)) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm, Bool.true_and, Bool.true_and, Bool.false_xor]
    rw [ite_neg (by omega : (3 * 0 + 1 : Nat) ≠ 0), ite_pos (by omega : (3 * 0 + 1 : Nat) = 1),
      ite_neg (by omega : 3 * (r - 1) + 1 ≠ 0), ite_neg (by omega : 3 * (r - 1) + 1 ≠ 1),
      ite_neg (by omega : ¬(3 * (r - 1) + 1 < k - 2)), ite_pos (by omega : 3 * (r - 1) + 1 = k - 2)]
  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      (if 3 * j.val + 2 = 0 then false
       else if 3 * j.val + 2 = 1 then !(w0 ⟨2, by omega⟩)
       else if 3 * j.val + 2 < k - 2 then xor (w0 (ix hk (3 * j.val + 2 + 1))) (w0 (ix hk (3 * j.val + 2 + 2)))
       else if 3 * j.val + 2 = k - 2 then w0 ⟨0, hk⟩
       else false)) =
    xorFin (fun j : Fin (r - 1) =>
      xor (w0 ⟨3 * (j.val + 1), by omega⟩) (w0 ⟨3 * (j.val + 1) + 1, by omega⟩)) := by
    rw [xorFin_last (by omega)]; dsimp only
    have hlast : (if 3 * (r - 1) + 2 = 0 then false
       else if 3 * (r - 1) + 2 = 1 then !(w0 ⟨2, by omega⟩)
       else if 3 * (r - 1) + 2 < k - 2 then xor (w0 (ix hk (3 * (r - 1) + 2 + 1))) (w0 (ix hk (3 * (r - 1) + 2 + 2)))
       else if 3 * (r - 1) + 2 = k - 2 then w0 ⟨0, hk⟩
       else false) = false := by
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    rw [hlast, Bool.and_false, Bool.xor_false]
    apply xorFin_congr; intro j
    have hn := neededSet_c2 hr hk3 ⟨j.val, by omega⟩
    dsimp only at hn; rw [ite_neg (by omega)] at hn
    rw [hn, Bool.true_and,
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega : 3 * j.val + 2 < k - 2),
      ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    exact congrArg₂ xor (congrArg w0 (Fin.ext (by dsimp only; omega))) (congrArg w0 (Fin.ext (by dsimp only; omega)))
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]
  have htele : xor (xorFin (fun j : Fin (r - 1) =>
        xor (w0 ⟨3 * (j.val + 1) + 1, by omega⟩) (w0 ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xorFin (fun j : Fin (r - 1) =>
        xor (w0 ⟨3 * (j.val + 1), by omega⟩) (w0 ⟨3 * (j.val + 1) + 1, by omega⟩))) =
    xor (xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1), by omega⟩))
        (xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
    rw [← xorFin_xor, ← xorFin_xor]
    apply xorFin_congr; intro j
    cases w0 ⟨3 * (j.val + 1), by omega⟩ <;> cases w0 ⟨3 * (j.val + 1) + 1, by omega⟩ <;>
      cases w0 ⟨3 * (j.val + 1) + 2, by omega⟩ <;> rfl
  have hs0 : resSum r hk3 w0 0 (by omega) =
      xor (w0 ⟨0, hk⟩) (xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1), by omega⟩)) := by
    unfold resSum; rw [xorFin_first (by omega)]; rfl
  have hs2 : resSum r hk3 w0 2 (by omega) =
      xor (w0 ⟨2, by omega⟩) (xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1) + 2, by omega⟩)) := by
    unfold resSum; rw [xorFin_first (by omega)]; rfl
  have hcomm : xor (xorFin (fun j : Fin (r - 1) =>
        xor (w0 ⟨3 * (j.val + 1) + 1, by omega⟩) (w0 ⟨3 * (j.val + 1) + 2, by omega⟩)))
      (xor (xor (!(w0 ⟨2, by omega⟩)) (w0 ⟨0, hk⟩))
           (xorFin (fun j : Fin (r - 1) =>
             xor (w0 ⟨3 * (j.val + 1), by omega⟩) (w0 ⟨3 * (j.val + 1) + 1, by omega⟩)))) =
    xor (xor (!(w0 ⟨2, by omega⟩)) (w0 ⟨0, hk⟩))
        (xor (xorFin (fun j : Fin (r - 1) =>
          xor (w0 ⟨3 * (j.val + 1) + 1, by omega⟩) (w0 ⟨3 * (j.val + 1) + 2, by omega⟩)))
        (xorFin (fun j : Fin (r - 1) =>
          xor (w0 ⟨3 * (j.val + 1), by omega⟩) (w0 ⟨3 * (j.val + 1) + 1, by omega⟩)))) := by
    cases xorFin (fun j : Fin (r - 1) => xor (w0 ⟨3 * (j.val + 1) + 1, by omega⟩) (w0 ⟨3 * (j.val + 1) + 2, by omega⟩)) <;>
      cases xor (!(w0 ⟨2, by omega⟩)) (w0 ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 1) => xor (w0 ⟨3 * (j.val + 1), by omega⟩) (w0 ⟨3 * (j.val + 1) + 1, by omega⟩)) <;> rfl
  rw [hcomm, htele, hs0, hs2]
  cases w0 ⟨0, hk⟩ <;> cases w0 ⟨2, by omega⟩ <;>
    cases xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1), by omega⟩) <;>
    cases xorFin (fun j : Fin (r - 1) => w0 ⟨3 * (j.val + 1) + 2, by omega⟩) <;> rfl

lemma unit_witness_42250 (hr : 2 ≤ r) (hk3 : k = 3 * r) (u : Fin k → Bool)
    (i0 : Fin k) (hi0 : i0 ∈ neededSet r k) :
    ∃ x1 x2 : Fin k → Bool,
      x1 ≠ x2 ∧ diffFn hk u x1 = diffFn hk u x2 ∧
      ∀ i : Fin k, i ≠ i0 → row hk u x1 i = row hk u x2 i := by
  let a1 : Bool := decide (i0.val = 0)
  let a0 : Bool := decide (i0.val = k - 1)
  let z0 : Fin k → Bool := zOf (fun _ => false) a0 a1
  let d : Fin k → Bool := fun i =>
    xor (decide (i = i0)) (xor (decide (i.val ≠ 0)) (z0 (ix hk (i.val + 1))))
  let w0 : Fin k → Bool := tOfD hr hk3 d
  have hd0 : d ⟨0, hk⟩ = false := by
    unfold d z0 zOf; dsimp only
    rw [ix_eq_of_lt hk (by omega), zPair_zero]
    dsimp only
    have heq : decide ((⟨0, hk⟩ : Fin k) = i0) = a1 := by
      unfold a1; apply decide_eq_decide.mpr
      constructor
      · intro h; exact (congrArg Fin.val h).symm
      · intro h; exact Fin.ext h.symm
    rw [heq]; cases a1 <;> rfl
  have hdk1 : d ⟨k - 1, by omega⟩ = true := by
    unfold d z0 zOf; dsimp only
    have hix : ix hk (k - 1 + 1) = ⟨0, hk⟩ :=
      (ix_mod_eq hk (by rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
    rw [hix, zPair_zero]; dsimp only
    have heq : decide ((⟨k - 1, by omega⟩ : Fin k) = i0) = a0 := by
      unfold a0; apply decide_eq_decide.mpr
      constructor
      · intro h; exact (congrArg Fin.val h).symm
      · intro h; exact Fin.ext h.symm
    rw [heq, decide_eq_true (by omega : k - 1 ≠ 0)]
    cases a0 <;> rfl
  have hw0_0 : w0 ⟨0, hk⟩ = !(d ⟨k - 2, by omega⟩) := by
    unfold w0 tOfD tRaw; simp
  have hw0_2 : w0 ⟨2, by omega⟩ = !(d ⟨1, by omega⟩) := by
    unfold w0 tOfD tRaw; simp
  have hw0_3 : w0 ⟨3, by omega⟩ = false := by
    unfold w0 tOfD tRaw tWalk; simp
  have hw0_4 : w0 ⟨4, by omega⟩ = d ⟨2, by omega⟩ := by
    unfold w0 tOfD tRaw; dsimp only
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    have h43 : (4 : Nat) - 3 = 1 := rfl
    rw [h43]; unfold tWalk; rw [dite_pos (by omega)]
  have hw0_step : ∀ i : Fin k, 3 ≤ i.val → i.val < k - 2 →
      xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2))) = !(d i) := by
    intro i hi3 hilt
    rw [ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    unfold w0 tOfD tRaw; dsimp only
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
      ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
    have h2 : i.val + 2 - 3 = (i.val - 3) + 2 := by omega
    have h1 : i.val + 1 - 3 = (i.val - 3) + 1 := by omega
    rw [h2, h1]
    have hlt : (i.val - 3) + 3 < k := by omega
    have hstep : tWalk d ((i.val - 3) + 2) =
        xor (tWalk d ((i.val - 3) + 1)) (if h : (i.val - 3) + 3 < k then !(d ⟨(i.val - 3) + 3, h⟩) else false) := rfl
    rw [hstep, dite_pos hlt]
    have hfi : (⟨i.val - 3 + 3, hlt⟩ : Fin k) = i := Fin.ext (by dsimp only; omega)
    rw [hfi]
    cases tWalk d (i.val - 3 + 1) <;> cases d i <;> rfl
  have hd_eq_g : ∀ i : Fin k,
      d i = xor (if i.val = 0 then false
                 else if i.val = 1 then !(w0 ⟨2, by omega⟩)
                 else if i.val < k - 2 then xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2)))
                 else if i.val = k - 2 then w0 ⟨0, hk⟩
                 else false)
                (decide (3 ≤ i.val)) := by
    intro i
    by_cases h0 : i.val = 0
    · have hie : i = ⟨0, hk⟩ := Fin.ext h0
      rw [hie]; dsimp only; rw [ite_pos rfl, hd0]; rfl
    · by_cases h1 : i.val = 1
      · have hie : i = ⟨1, by omega⟩ := Fin.ext h1
        rw [hie]; dsimp only; rw [ite_neg (by omega), ite_pos rfl, hw0_2]; simp
      · by_cases h2 : i.val = 2
        · have hie : i = ⟨2, by omega⟩ := Fin.ext h2
          rw [hie]; dsimp only; rw [ite_neg (by omega), ite_neg (by omega), ite_pos (by omega),
            ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega), hw0_3, hw0_4]; simp
        · by_cases hilt : i.val < k - 2
          · rw [ite_neg h0, ite_neg h1, ite_pos hilt, decide_eq_true (by omega : 3 ≤ i.val),
              hw0_step i (by omega) hilt]
            cases d i <;> rfl
          · by_cases hk2 : i.val = k - 2
            · have hie : i = ⟨k - 2, by omega⟩ := Fin.ext hk2
              rw [hie]; dsimp only; rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_pos rfl,
                decide_eq_true (by omega : 3 ≤ k - 2), hw0_0]
              cases d ⟨k - 2, by omega⟩ <;> rfl
            · have hik1 : i.val = k - 1 := by omega
              have hie : i = ⟨k - 1, by omega⟩ := Fin.ext hik1
              rw [hie]; dsimp only; rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
                decide_eq_true (by omega : 3 ≤ k - 1), hdk1]; rfl
  have hsum_d_1 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && d i) =
      xor true (decide (r % 2 = 0)) := by
    have hsplit : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && d i) =
        xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = i0)))
          (xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i.val ≠ 0)))
               (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && z0 (ix hk (i.val + 1))))) := by
      rw [← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro i; unfold d
      cases decide (i ∈ neededSet r k) <;> cases decide (i = i0) <;>
        cases decide (i.val ≠ 0) <;> cases z0 (ix hk (i.val + 1)) <;> rfl
    have ht1 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = i0)) = true := by
      rw [xorFin_single' i0]
      · simp [hi0]
      · intro i hi; simp [hi]
    have ht2 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i.val ≠ 0)) =
        decide (r % 2 = 0) := by
      have heq : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i.val ≠ 0)) =
          xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k)))
              (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨0, hk⟩))) := by
        rw [← xorFin_xor]
        apply xorFin_congr; intro i
        by_cases h0 : i.val = 0
        · have hie : i = ⟨0, hk⟩ := Fin.ext h0
          rw [hie]; cases decide ((⟨0, hk⟩ : Fin k) ∈ neededSet r k) <;> rfl
        · have hne : i ≠ ⟨0, hk⟩ := fun h => h0 (congrArg Fin.val h)
          rw [decide_eq_true h0, decide_eq_false hne]
          cases decide (i ∈ neededSet r k) <;> rfl
      rw [heq, neededSet_all_xor_false hr hk3, Bool.false_xor, xorFin_single' ⟨0, hk⟩]
      · simp [mem_neededSet_iff]
      · intro i hi; simp [hi]
    have ht3 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && z0 (ix hk (i.val + 1))) = false :=
      neededSet_zZero_cancel hk hr hk3 a0 a1
    rw [hsplit, ht1, ht2, ht3, Bool.xor_false]
  have hsum_ge3 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (3 ≤ i.val)) =
      decide (r % 2 = 0) := by
    have heq : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (3 ≤ i.val)) =
        xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k)))
          (xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨0, hk⟩)))
            (xor (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨1, by omega⟩)))
                 (xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨2, by omega⟩))))) := by
      rw [← xorFin_xor, ← xorFin_xor, ← xorFin_xor]
      apply xorFin_congr; intro i
      by_cases h0 : i.val = 0
      · have hie : i = ⟨0, hk⟩ := Fin.ext h0
        rw [hie]
        have hn1 : (⟨0, hk⟩ : Fin k) ≠ ⟨1, by omega⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
        have hn2 : (⟨0, hk⟩ : Fin k) ≠ ⟨2, by omega⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
        rw [decide_eq_false hn1, decide_eq_false hn2]
        cases decide ((⟨0, hk⟩ : Fin k) ∈ neededSet r k) <;> rfl
      · by_cases h1 : i.val = 1
        · have hie : i = ⟨1, by omega⟩ := Fin.ext h1
          rw [hie]
          have hn0 : (⟨1, by omega⟩ : Fin k) ≠ ⟨0, hk⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
          have hn2 : (⟨1, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
          rw [decide_eq_false hn0, decide_eq_false hn2]
          cases decide ((⟨1, by omega⟩ : Fin k) ∈ neededSet r k) <;> rfl
        · by_cases h2 : i.val = 2
          · have hie : i = ⟨2, by omega⟩ := Fin.ext h2
            rw [hie]
            have hn0 : (⟨2, by omega⟩ : Fin k) ≠ ⟨0, hk⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
            have hn1 : (⟨2, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega
            rw [decide_eq_false hn0, decide_eq_false hn1]
            cases decide ((⟨2, by omega⟩ : Fin k) ∈ neededSet r k) <;> rfl
          · have hn0 : i ≠ ⟨0, hk⟩ := fun h => h0 (congrArg Fin.val h)
            have hn1 : i ≠ ⟨1, by omega⟩ := fun h => h1 (congrArg Fin.val h)
            have hn2 : i ≠ ⟨2, by omega⟩ := fun h => h2 (congrArg Fin.val h)
            rw [decide_eq_true (by omega : 3 ≤ i.val),
              decide_eq_false hn0, decide_eq_false hn1, decide_eq_false hn2]
            cases decide (i ∈ neededSet r k) <;> rfl
    rw [heq, neededSet_all_xor_false hr hk3, Bool.false_xor]
    have h0 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨0, hk⟩)) = decide (r % 2 = 0) := by
      rw [xorFin_single' ⟨0, hk⟩]; simp [mem_neededSet_iff]; intro i hi; simp [hi]
    have h1 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨1, by omega⟩)) = true := by
      rw [xorFin_single' ⟨1, by omega⟩]
      · simp only [decide_true, Bool.and_true]
        have hc1 := neededSet_c1 hr hk3 ⟨0, by omega⟩; simpa using hc1
      · intro i hi; simp [hi]
    have h2 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && decide (i = ⟨2, by omega⟩)) = true := by
      rw [xorFin_single' ⟨2, by omega⟩]
      · simp only [decide_true, Bool.and_true]
        have hc2 := neededSet_c2 hr hk3 ⟨0, by omega⟩
        have hne : (0 : Nat) ≠ r - 1 := by omega
        dsimp only at hc2; rw [ite_neg hne] at hc2
        simpa using hc2
      · intro i hi; simp [hi]
    rw [h0, h1, h2]
    cases decide (r % 2 = 0) <;> rfl
  have hsum_d_2 : xorFin (fun i : Fin k => decide (i ∈ neededSet r k) && d i) =
      xor (xor true (xor (resSum r hk3 w0 0 (by omega)) (resSum r hk3 w0 2 (by omega))))
          (decide (r % 2 = 0)) := by
    rw [← neededSet_g_sum hk hr hk3 w0, ← hsum_ge3, ← xorFin_xor]
    apply xorFin_congr; intro i
    rw [hd_eq_g i]
    cases decide (i ∈ neededSet r k) <;>
      cases (if i.val = 0 then false
             else if i.val = 1 then !(w0 ⟨2, by omega⟩)
             else if i.val < k - 2 then xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2)))
             else if i.val = k - 2 then w0 ⟨0, hk⟩
             else false) <;>
      cases decide (3 ≤ i.val) <;> rfl
  have hs01 : resSum r hk3 w0 0 (by omega) = resSum r hk3 w0 1 (by omega) :=
    tOfD_resSum01 hr hk3 d
  have hs02 : resSum r hk3 w0 0 (by omega) = resSum r hk3 w0 2 (by omega) := by
    have h := hsum_d_1.symm.trans hsum_d_2
    cases h0 : resSum r hk3 w0 0 (by omega) <;>
      cases h2 : resSum r hk3 w0 2 (by omega) <;>
      cases he : decide (r % 2 = 0) <;>
      simp [h0, h2, he] at h ⊢
  let z1 : Fin k → Bool := zOf w0 false false
  let z2 : Fin k → Bool := add z1 (add vMask z0)
  let x1 : Fin k → Bool := fun i => xor (z1 (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))
  let x2 : Fin k → Bool := fun i => xor (z2 (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))
  have hrot1 : add u (rot hk x1) = z1 := add_rot_unrot hk u z1
  have hrot2 : add u (rot hk x2) = z2 := add_rot_unrot hk u z2
  have hmix1 : mix hk z1 = w0 := mix_zOf hk hr hk3 w0 false false hs01 hs02
  have hmix_z0 : mix hk z0 = fun _ => false := by
    have hz_res : ∀ (c : Nat) (hc : c < 3), resSum r hk3 (fun _ => false) c hc = false :=
      fun c hc => xorFin_false
    exact mix_zOf hk hr hk3 (fun _ => false) a0 a1
      ((hz_res 0 (by omega)).trans (hz_res 1 (by omega)).symm)
      ((hz_res 0 (by omega)).trans (hz_res 2 (by omega)).symm)
  have hmix2 : mix hk z2 = add w0 (mix hk vMask) := by
    unfold z2
    rw [mix_add hk z1 (add vMask z0), mix_add hk vMask z0, hmix1, hmix_z0]
    funext i; unfold add; simp
  have hne : x1 ≠ x2 := by
    intro heq
    have hm : mix hk (add u (rot hk x1)) ⟨3, by omega⟩ = mix hk (add u (rot hk x2)) ⟨3, by omega⟩ := by
      rw [heq]
    rw [hrot1, hrot2, hmix1, hmix2] at hm
    unfold add at hm
    rw [mix_vMask hk hr hk3 ⟨3, by omega⟩] at hm
    dsimp only at hm
    cases hw3 : w0 ⟨3, by omega⟩ <;> simp [hw3] at hm
  have hdiff_form : ∀ x : Fin k → Bool,
      diffFn hk u x = fun i =>
        xor (chi hk (mix hk (add u (rot hk x))) i)
            (chi hk (add (mix hk (add u (rot hk x))) (mix hk vMask)) i) := by
    intro x; funext i; unfold diffFn row
    have hassoc : add (add u vMask) (rot hk x) = add (add u (rot hk x)) vMask := by
      funext j; unfold add; cases u j <;> cases vMask j <;> cases rot hk x j <;> rfl
    rw [hassoc, mix_add hk (add u (rot hk x)) vMask]
    change xor (xor (chi hk (mix hk (add u (rot hk x))) i) (x i))
      (xor (chi hk (add (mix hk (add u (rot hk x))) (mix hk vMask)) i) (x i)) =
      xor (chi hk (mix hk (add u (rot hk x))) i)
        (chi hk (add (mix hk (add u (rot hk x))) (mix hk vMask)) i)
    cases chi hk (mix hk (add u (rot hk x))) i <;>
      cases chi hk (add (mix hk (add u (rot hk x))) (mix hk vMask)) i <;>
      cases x i <;> rfl
  have hdiff_eq : diffFn hk u x1 = diffFn hk u x2 := by
    rw [hdiff_form x1, hdiff_form x2, hrot1, hrot2, hmix1, hmix2]
    have hinv : add (add w0 (mix hk vMask)) (mix hk vMask) = w0 := by
      funext i; unfold add
      cases w0 i <;> cases mix hk vMask i <;> rfl
    rw [hinv]
    funext i
    exact Bool.xor_comm _ _
  have hdiff1 : diffFn hk u x1 = d := by
    funext i
    have hd := diffFn_eq hk hr hk3 u x1 i
    dsimp only at hd
    rw [hrot1, hmix1] at hd
    rw [hd, hd_eq_g i]
    by_cases h0 : i.val = 0
    · rw [ite_pos h0, ite_pos h0]; simp [h0]
    · by_cases h1 : i.val = 1
      · rw [ite_neg h0, ite_pos h1, ite_neg h0, ite_pos h1, ix_eq_of_lt hk (by omega)]; simp [h1]
      · by_cases h2 : i.val = 2
        · rw [ite_neg h0, ite_neg h1, ite_pos h2, ite_neg h0, ite_neg h1, ite_pos (by omega : i.val < k - 2),
            h2, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]; simp
        · by_cases hilt : i.val < k - 2
          · rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_pos hilt,
              ite_neg h0, ite_neg h1, ite_pos hilt, decide_eq_true (by omega : 3 ≤ i.val)]
            cases xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2))) <;> rfl
          · by_cases hk2 : i.val = k - 2
            · rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_neg hilt, ite_pos hk2,
                ite_neg h0, ite_neg h1, ite_neg hilt, ite_pos hk2,
                decide_eq_true (by omega : 3 ≤ i.val), ix_eq_of_lt hk hk]
              cases w0 ⟨0, hk⟩ <;> rfl
            · rw [ite_neg h0, ite_neg h1, ite_neg h2, ite_neg hilt, ite_neg hk2,
                ite_neg h0, ite_neg h1, ite_neg hilt, ite_neg hk2,
                decide_eq_true (by omega : 3 ≤ i.val)]; rfl
  have hrow_xor : ∀ i : Fin k, xor (row hk u x1 i) (row hk u x2 i) = decide (i = i0) := by
    intro i
    unfold row
    rw [hrot1, hrot2, hmix1, hmix2]
    change xor (xor (chi hk w0 i) (x1 i)) (xor (chi hk (add w0 (mix hk vMask)) i) (x2 i)) = decide (i = i0)
    have hchi : xor (chi hk w0 i) (chi hk (add w0 (mix hk vMask)) i) = d i := by
      have hf := congrFun (hdiff_form x1) i
      rw [hrot1, hmix1, hdiff1] at hf
      exact hf.symm
    have hx : xor (x1 i) (x2 i) = xor (decide (i.val ≠ 0)) (z0 (ix hk (i.val + 1))) := by
      unfold x1 x2 z2 add vMask
      have hv : decide ((ix hk (i.val + 1)).val ≠ 1) = decide (i.val ≠ 0) := by
        apply decide_eq_decide.mpr
        dsimp only [ix]
        by_cases hl : i.val = k - 1
        · rw [show i.val + 1 = k by omega, Nat.mod_self]; omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hv]
      cases z1 (ix hk (i.val + 1)) <;> cases decide (i.val ≠ 0) <;>
        cases z0 (ix hk (i.val + 1)) <;> cases u (ix hk (i.val + 1)) <;> rfl
    have hrearr : xor (xor (chi hk w0 i) (x1 i)) (xor (chi hk (add w0 (mix hk vMask)) i) (x2 i)) =
        xor (xor (chi hk w0 i) (chi hk (add w0 (mix hk vMask)) i)) (xor (x1 i) (x2 i)) := by
      cases chi hk w0 i <;> cases x1 i <;> cases chi hk (add w0 (mix hk vMask)) i <;> cases x2 i <;> rfl
    rw [hrearr, hchi, hx]
    unfold d
    cases decide (i = i0) <;> cases xor (decide (i.val ≠ 0)) (z0 (ix hk (i.val + 1))) <;> rfl
  refine ⟨x1, x2, hne, hdiff_eq, ?_⟩
  intro i hi
  have hx := hrow_xor i
  rw [decide_eq_false hi] at hx
  cases h1 : row hk u x1 i <;> cases h2 : row hk u x2 i <;> simp [h1, h2] at hx ⊢

lemma inj_iff_42250 (hr : 2 ≤ r) (hk3 : k = 3 * r) (u : Fin k → Bool)
    (n : Nat) (sites : Finset (Fin n × Fin k)) :
    Function.Injective (fun x : Fin n → Fin k → Bool =>
      ((fun j : Fin n => diffFn hk u (x j)),
       (fun a : {aSite : Fin n × Fin k // aSite ∈ sites} => row hk u (x a.val.1) a.val.2))) ↔
    ∀ (j : Fin n) (i : Fin k), i ∈ neededSet r k → (j, i) ∈ sites := by
  constructor
  · intro hinj j0 i0 hi0
    by_contra hnot
    rcases unit_witness_42250 hk hr hk3 u i0 hi0 with ⟨x1, x2, hne, hdiff, hrow⟩
    let X1 : Fin n → Fin k → Bool := fun j => if j = j0 then x1 else fun _ => false
    let X2 : Fin n → Fin k → Bool := fun j => if j = j0 then x2 else fun _ => false
    have heq : X1 = X2 := by
      apply hinj
      refine Prod.ext ?_ ?_
      · funext j
        dsimp only [X1, X2]
        split_ifs
        · exact hdiff
        · rfl
      · funext a
        dsimp only [X1, X2]
        by_cases hj : a.val.1 = j0
        · rw [ite_pos hj, ite_pos hj]
          have hi : a.val.2 ≠ i0 := by
            intro hi_eq
            have hp : a.val = (j0, i0) := Prod.ext hj hi_eq
            exact hnot (hp ▸ a.property)
          exact hrow a.val.2 hi
        · rw [ite_neg hj, ite_neg hj]
    have hx := congrFun heq j0
    dsimp only [X1, X2] at hx
    rw [ite_pos rfl, ite_pos rfl] at hx
    exact hne hx
  · intro hsites X1 X2 heq
    have hdiff_all := congrArg Prod.fst heq
    have hrow_all := congrArg Prod.snd heq
    funext j
    apply row_eq_of_diff_needed hk hr hk3 u (X1 j) (X2 j)
    · exact congrFun hdiff_all j
    · intro i hi
      have hmem : (j, i) ∈ sites := hsites j i hi
      exact congrFun hrow_all ⟨(j, i), hmem⟩

end RowAlg

end PEqualNP.Outside.L_meta_42250_aux

theorem PEqualNP.Outside.L_meta_42250 :
  ∀ (r k : Nat) (hk : 0 < k), 2 ≤ r → k = 3*r →
    let W := Fin k → Bool
    let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
    let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
    let mix := fun (w : W) (i : Fin k) => xor (w (ix (i.val+k-1))) (xor (w i) (w (ix (i.val+1))))
    let rot := fun (x : W) (i : Fin k) => x (ix (i.val+k-1))
    let chi := fun (w : W) (i : Fin k) => xor (w i) (!(w (ix (i.val+1))) && w (ix (i.val+2)))
    let row := fun (u x : W) => add (chi (mix (add u (rot x)))) x
    let v : W := fun i => decide (i.val ≠ 1)
    ∀ u : W,
      let base := row u
      let diff := fun x : W => add (base x) (row (add u v) x)
      let needed : Finset (Fin k) := Finset.univ.filter (fun i =>
        if i.val = 0 ∨ i.val = k-1 then r % 2 = 0
        else i.val = 1 ∨ i.val = k-2 ∨ i.val % 3 ≠ 1)
      needed.card = 4*(r/2)+2 ∧
        ∀ (n : Nat) (sites : Finset (Fin n × Fin k)),
          Function.Injective (fun x : Fin n → W =>
            ((fun j : Fin n => diff (x j)),
             (fun a : {aSite : Fin n × Fin k // aSite ∈ sites} => base (x a.val.1) a.val.2))) ↔
          ∀ (j : Fin n) (i : Fin k), i ∈ needed → (j,i) ∈ sites := by
  intro r k hk hr hk3
  dsimp only
  intro u
  exact ⟨PEqualNP.Outside.L_meta_42250_aux.neededSet_card hr hk3,
    PEqualNP.Outside.L_meta_42250_aux.inj_iff_42250 hk hr hk3 u⟩
