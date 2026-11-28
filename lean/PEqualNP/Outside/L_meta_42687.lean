import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42687_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def valid (w : Nat) (C : Circuit) : Prop :=
  ReadsBack w C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

def depthList (w : Nat) (gs : List Gate) : List Nat :=
  gs.foldl (fun (ds : List Nat) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)

def depth (w : Nat) (C : Circuit) : Nat :=
  (depthList w C.gates).foldr max 0

def targetCount (r : Nat) : Nat :=
  if r = 2 then 2 else if r = 3 then 4 else r + 2

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

def dot {N : Nat} (u v : Fin N → Bool) : Bool :=
  xorFin (fun i => u i && v i)

lemma dot_xor_left {N : Nat} (u1 u2 v : Fin N → Bool) :
    dot (fun i => xor (u1 i) (u2 i)) v = xor (dot u1 v) (dot u2 v) := by
  unfold dot
  rw [← xorFin_xor]
  apply xorFin_congr
  intro i
  dsimp only
  cases u1 i <;> cases u2 i <;> cases v i <;> rfl

lemma dot_xor_right {N : Nat} (u v1 v2 : Fin N → Bool) :
    dot u (fun i => xor (v1 i) (v2 i)) = xor (dot u v1) (dot u v2) := by
  unfold dot
  rw [← xorFin_xor]
  apply xorFin_congr
  intro i
  dsimp only
  cases u i <;> cases v1 i <;> cases v2 i <;> rfl

lemma dot_zero_right {N : Nat} (u : Fin N → Bool) :
    dot u (fun _ => false) = false := by
  unfold dot
  exact xorFin_eq_false _ (fun i => by simp)

def eVec {N : Nat} (p : Fin N) : Fin N → Bool :=
  fun i => decide (i = p)

lemma dot_eVec {N : Nat} (u : Fin N → Bool) (p : Fin N) :
    dot u (eVec p) = u p := by
  unfold dot eVec
  rw [xorFin_single' p]
  · simp
  · intro i hi; simp [hi]

def IsAffine {N : Nat} (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ (c : Bool) (w : Fin N → Bool), ∀ y, f y = xor c (dot w y)

def pol {N : Nat} (f : (Fin N → Bool) → Bool) (a b : Fin N → Bool) : Bool :=
  xor (xor (f (fun i => xor (a i) (b i))) (f a))
      (xor (f b) (f (fun _ => false)))

def rank2 {N : Nat} (L R : Fin N → Bool) (a b : Fin N → Bool) : Bool :=
  xor (dot L a && dot R b) (dot R a && dot L b)

lemma isAffine_const {N : Nat} (c : Bool) : IsAffine (fun _ : Fin N → Bool => c) :=
  ⟨c, fun _ => false, fun y => by simp [dot, xorFin_false]⟩

lemma isAffine_coord {N : Nat} (p : Fin N) : IsAffine (fun y : Fin N → Bool => y p) :=
  ⟨false, eVec p, fun y => by
    simp only [Bool.false_xor, dot, eVec]
    rw [xorFin_single' p]
    · simp
    · intro i hi; simp [hi]⟩

lemma isAffine_xor {N : Nat} {f g : (Fin N → Bool) → Bool}
    (hf : IsAffine f) (hg : IsAffine g) :
    IsAffine (fun y => xor (f y) (g y)) := by
  rcases hf with ⟨cf, wf, hfe⟩
  rcases hg with ⟨cg, wg, hge⟩
  refine ⟨xor cf cg, fun i => xor (wf i) (wg i), fun y => ?_⟩
  dsimp only
  rw [hfe y, hge y, dot_xor_left]
  cases cf <;> cases cg <;> cases dot wf y <;> cases dot wg y <;> rfl

lemma isAffine_and_const {N : Nat} (c : Bool) {f : (Fin N → Bool) → Bool}
    (hf : IsAffine f) : IsAffine (fun y => c && f y) := by
  cases c
  · simpa using isAffine_const false
  · simpa using hf

lemma isAffine_not {N : Nat} {f : (Fin N → Bool) → Bool}
    (hf : IsAffine f) : IsAffine (fun y => !(f y)) := by
  have h := isAffine_xor (isAffine_const true) hf
  simpa only [Bool.true_xor] using h

lemma isAffine_xorFin {N m : Nat} (F : Fin m → (Fin N → Bool) → Bool)
    (hF : ∀ i, IsAffine (F i)) : IsAffine (fun y => xorFin (fun i => F i y)) := by
  induction m with
  | zero => exact isAffine_const false
  | succ m ih =>
    have h1 := ih (fun i => F i.castSucc) (fun i => hF i.castSucc)
    have h2 := hF (Fin.last m)
    have h3 := isAffine_xor h1 h2
    have heq : (fun y => xorFin (fun i => F i y)) =
        (fun y => xor (xorFin (fun i : Fin m => F i.castSucc y)) (F (Fin.last m) y)) := by
      funext y; exact xorFin_succ (fun i => F i y)
    rw [heq]; exact h3

lemma isAffine_comp {N M : Nat} {f : (Fin M → Bool) → Bool} {g : (Fin N → Bool) → (Fin M → Bool)}
    (hf : IsAffine f) (hg : ∀ i, IsAffine (fun y => g y i)) :
    IsAffine (fun y => f (g y)) := by
  rcases hf with ⟨c, w, hfe⟩
  have heq : (fun y => f (g y)) = (fun y => xor c (xorFin (fun i => w i && g y i))) := by
    funext y; exact hfe (g y)
  rw [heq]
  exact isAffine_xor (isAffine_const c) (isAffine_xorFin _ (fun i => isAffine_and_const (w i) (hg i)))

lemma pol_xor {N : Nat} (f g : (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => xor (f y) (g y)) a b = xor (pol f a b) (pol g a b) := by
  unfold pol; dsimp only
  cases f (fun i => xor (a i) (b i)) <;> cases g (fun i => xor (a i) (b i)) <;>
    cases f a <;> cases g a <;> cases f b <;> cases g b <;>
    cases f (fun _ => false) <;> cases g (fun _ => false) <;> rfl

lemma pol_and_const {N : Nat} (c : Bool) (f : (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => c && f y) a b = (c && pol f a b) := by
  cases c <;> simp [pol]

lemma pol_const {N : Nat} (c : Bool) (a b : Fin N → Bool) :
    pol (fun _ : Fin N → Bool => c) a b = false := by
  unfold pol; dsimp only; cases c <;> rfl

lemma pol_affine {N : Nat} {f : (Fin N → Bool) → Bool} (hf : IsAffine f)
    (a b : Fin N → Bool) : pol f a b = false := by
  rcases hf with ⟨c, w, hfe⟩
  unfold pol
  simp only [hfe, dot_xor_right, dot_zero_right]
  cases c <;> cases dot w a <;> cases dot w b <;> rfl

lemma pol_and_affine {N : Nat} {f g : (Fin N → Bool) → Bool}
    {cf cg : Bool} {lf lg : Fin N → Bool}
    (hf : ∀ y, f y = xor cf (dot lf y)) (hg : ∀ y, g y = xor cg (dot lg y))
    (a b : Fin N → Bool) :
    pol (fun y => f y && g y) a b = rank2 lf lg a b := by
  unfold pol rank2
  simp only [hf, hg, dot_xor_right, dot_zero_right]
  cases cf <;> cases cg <;> cases dot lf a <;> cases dot lf b <;>
    cases dot lg a <;> cases dot lg b <;> rfl

lemma gate_eval_1 (op : GateOp) (a : Bool) :
    op.eval [a] = xor (op.eval [false]) (xor (op.eval [false]) (op.eval [true]) && a) := by
  cases a <;> cases op.eval [false] <;> cases op.eval [true] <;> rfl

lemma gate_eval_2 (op : GateOp) (a b : Bool) :
    op.eval [a, b] =
      xor (op.eval [false, false])
        (xor (xor (op.eval [false, false]) (op.eval [true, false]) && a)
          (xor (xor (op.eval [false, false]) (op.eval [false, true]) && b)
            (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true])) && (a && b)))) := by
  cases a <;> cases b <;>
    cases op.eval [false, false] <;> cases op.eval [false, true] <;>
    cases op.eval [true, false] <;> cases op.eval [true, true] <;> rfl

lemma depthList_length (w : Nat) (gs : List Gate) :
    (depthList w gs).length = w + gs.length := by
  unfold depthList
  suffices ∀ (gs : List Gate) (acc : List Nat),
      (gs.foldl (fun (ds : List Nat) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]) acc).length =
      acc.length + gs.length by
    simpa [List.length_replicate] using this gs (List.replicate w 0)
  intro gs
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldr_max_le_iff (l : List Nat) (k : Nat) :
    l.foldr max 0 ≤ k ↔ ∀ x ∈ l, x ≤ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

lemma depthList_getD_le_depth (w : Nat) (gs : List Gate) (i : Nat) :
    (depthList w gs).getD i 0 ≤ (depthList w gs).foldr max 0 := by
  by_cases hi : i < (depthList w gs).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact (foldr_max_le_iff _ _).mp (le_refl _) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    omega

lemma getD_append_lt {α : Type} (l : List α) (v d : α) {i : Nat} (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

lemma getD_append_eq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

lemma circuit_depth1_decomp {N width : Nat} (C : Circuit)
    (hval : valid width C) (hdep : depth width C ≤ 1)
    (φ : (Fin N → Bool) → List Bool)
    (hlen : ∀ y, (φ y).length = width)
    (haff : ∀ i < width, IsAffine (fun y => (φ y).getD i false)) :
    ∃ (L R : Fin (C.gates.countP nonlinear) → Fin N → Bool),
      ∀ i < width + C.gates.length,
        ∃ c : Fin (C.gates.countP nonlinear) → Bool,
          ∀ a b, pol (fun y => (C.wires (φ y)).getD i false) a b =
            xorFin (fun p => c p && rank2 (L p) (R p) a b) := by
  suffices ∀ (gs : List Gate),
      ReadsBack width ⟨gs, 0⟩ →
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (depthList width gs).foldr max 0 ≤ 1 →
      ∃ (L R : Fin (gs.countP nonlinear) → Fin N → Bool),
        ∀ i < width + gs.length,
          ((depthList width gs).getD i 0 = 0 →
            IsAffine (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false)) ∧
          ∃ c : Fin (gs.countP nonlinear) → Bool,
            ∀ a b, pol (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false) a b =
              xorFin (fun p => c p && rank2 (L p) (R p) a b) by
    rcases this C.gates hval.1 hval.2 hdep with ⟨L, R, h⟩
    exact ⟨L, R, fun i hi => (h i hi).2⟩
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ _
    refine ⟨fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun i hi => ?_⟩
    simp only [List.length_nil, Nat.add_zero] at hi
    refine ⟨fun _ => haff i hi, fun p => Fin.elim0 p, fun a b => ?_⟩
    change pol (fun y => (φ y).getD i false) a b = false
    exact pol_affine (haff i hi) a b
  | append_singleton gs g ih =>
    intro hrb hfan hdm
    have hds_step : depthList width (gs ++ [g]) =
        depthList width gs ++
          [(g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
      unfold depthList; rw [List.foldl_append]; rfl
    have hds_len : (depthList width gs).length = width + gs.length := depthList_length width gs
    have hrb_gs : ReadsBack width ⟨gs, 0⟩ := by
      intro j hj i hi
      change j < gs.length at hj
      have h1 := hrb j (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt; simp only [getD_append_lt gs g _ hj]
      rw [hga] at h1
      exact h1 i hi
    have hrb_g : ∀ i ∈ g.inputs, i < width + gs.length := by
      have h1 := hrb gs.length (by simp)
      have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt; exact getD_append_eq gs g _
      rw [hga] at h1
      exact h1
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hfan_g : g.inputs.length ≤ 2 := hfan g (List.mem_append_right _ List.mem_cons_self)
    have hdm_all : ∀ x ∈ depthList width (gs ++ [g]), x ≤ 1 :=
      (foldr_max_le_iff _ 1).mp hdm
    have hdm_gs : (depthList width gs).foldr max 0 ≤ 1 := by
      rw [foldr_max_le_iff]
      intro x hx
      exact hdm_all x (by rw [hds_step]; exact List.mem_append_left _ hx)
    have hdg_le : (g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 +
        (nonlinear g).toNat ≤ 1 :=
      hdm_all _ (by rw [hds_step]; exact List.mem_append_right _ List.mem_cons_self)
    rcases ih hrb_gs hfan_gs hdm_gs with ⟨L, R, hgs⟩
    have hw_step : ∀ y, Circuit.wires ⟨gs ++ [g], 0⟩ (φ y) =
        Circuit.wires ⟨gs, 0⟩ (φ y) ++
          [g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false)] := by
      intro y; unfold Circuit.wires; rw [List.foldl_append]; rfl
    have hw_len : ∀ y, (Circuit.wires ⟨gs, 0⟩ (φ y)).length = width + gs.length := by
      intro y; unfold Circuit.wires; rw [wires_length, hlen y]
    have hcount_step : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nonlinear g <;> simp [Bool.toNat]
    cases hnl : nonlinear g
    ·
      have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear := by
        rw [hcount_step, hnl]; rfl
      refine ⟨fun p => L ⟨p.val, by omega⟩, fun p => R ⟨p.val, by omega⟩, fun i hi => ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hilt : i < width + gs.length
      · have hdi : (depthList width (gs ++ [g])).getD i 0 = (depthList width gs).getD i 0 := by
          rw [hds_step, getD_append_lt _ _ _ (by omega)]
        have hwi : ∀ y, (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false =
            (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false := fun y => by
          rw [hw_step y, getD_append_lt _ _ _ (by rw [hw_len y]; exact hilt)]
        rcases hgs i hilt with ⟨haff_i, ci, hci⟩
        refine ⟨fun hd0 => ?_, fun p => ci ⟨p.val, by omega⟩, fun a b => ?_⟩
        · have heq : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false) =
              (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false) := funext hwi
          rw [heq]; exact haff_i (hdi ▸ hd0)
        · have heq : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false) =
              (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false) := funext hwi
          rw [heq, hci a b]
          exact xorFin_cast hcnt.symm _ _ (fun _ _ _ => rfl)
      · have hieq : i = width + gs.length := by omega
        subst hieq
        have hdi : (depthList width (gs ++ [g])).getD (width + gs.length) 0 =
            (g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 := by
          rw [hds_step, ← hds_len, getD_append_eq, hnl]; simp
        have hwi : ∀ y, (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD (width + gs.length) false =
            g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false) := fun y => by
          rw [hw_step y, ← hw_len y, getD_append_eq]
        have heq_fn : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD (width + gs.length) false) =
            (fun y => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false)) :=
          funext hwi
        rcases hinp : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
        ·
          refine ⟨fun _ => ?_, fun _ => false, fun a b => ?_⟩
          · rw [heq_fn]; simp only [hinp, List.map_nil]; exact isAffine_const _
          · rw [heq_fn]; simp only [hinp, List.map_nil, pol_const, Bool.false_and, xorFin_false]
        ·
          have hi1 : i1 < width + gs.length := hrb_g i1 (by simp [hinp])
          rcases hgs i1 hi1 with ⟨haff1, c1, hc1⟩
          let k1 := xor (g.op.eval [false]) (g.op.eval [true])
          refine ⟨fun hd0 => ?_, fun p => k1 && c1 ⟨p.val, by omega⟩, fun a b => ?_⟩
          · rw [hdi, hinp] at hd0; simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero] at hd0
            rw [heq_fn]
            have hf1 : (fun y => g.op.eval ([i1].map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false)) =
                (fun y => xor (g.op.eval [false]) (k1 && (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false)) := by
              funext y; simp only [List.map_cons, List.map_nil]; exact gate_eval_1 g.op _
            rw [hinp, hf1]
            exact isAffine_xor (isAffine_const _) (isAffine_and_const k1 (haff1 hd0))
          · rw [heq_fn]
            have hf1 : (fun y => g.op.eval ([i1].map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false)) =
                (fun y => xor (g.op.eval [false]) (k1 && (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false)) := by
              funext y; simp only [List.map_cons, List.map_nil]; exact gate_eval_1 g.op _
            rw [hinp, hf1, pol_xor, pol_const, Bool.false_xor, pol_and_const, hc1 a b, ← xorFin_and_left]
            exact xorFin_cast hcnt.symm _ _ (fun j hj1 hj2 => by simp [Bool.and_assoc])
        ·
          have hrest : rest = [] := by
            rw [hinp] at hfan_g; cases rest <;> simp at hfan_g; rfl
          subst hrest
          have hi1 : i1 < width + gs.length := hrb_g i1 (by simp [hinp])
          have hi2 : i2 < width + gs.length := hrb_g i2 (by simp [hinp])
          rcases hgs i1 hi1 with ⟨haff1, c1, hc1⟩
          rcases hgs i2 hi2 with ⟨haff2, c2, hc2⟩
          have hq0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
              (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
            unfold nonlinear at hnl; rw [hinp] at hnl; simpa using hnl
          let k1 := xor (g.op.eval [false, false]) (g.op.eval [true, false])
          let k2 := xor (g.op.eval [false, false]) (g.op.eval [false, true])
          have hf2 : (fun y => g.op.eval ([i1, i2].map fun a => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD a false)) =
              (fun y => xor (g.op.eval [false, false])
                (xor (k1 && (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false)
                     (k2 && (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i2 false))) := by
            funext y; simp only [List.map_cons, List.map_nil]
            rw [gate_eval_2 g.op, hq0, Bool.false_and, Bool.xor_false]
          refine ⟨fun hd0 => ?_, fun p => xor (k1 && c1 ⟨p.val, by omega⟩) (k2 && c2 ⟨p.val, by omega⟩), fun a b => ?_⟩
          · rw [hdi, hinp] at hd0
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero] at hd0
            have hle1 := Nat.le_max_left ((depthList width gs).getD i1 0) ((depthList width gs).getD i2 0)
            have hle2 := Nat.le_max_right ((depthList width gs).getD i1 0) ((depthList width gs).getD i2 0)
            have hd1 : (depthList width gs).getD i1 0 = 0 := by omega
            have hd2 : (depthList width gs).getD i2 0 = 0 := by omega
            rw [heq_fn, hinp, hf2]
            exact isAffine_xor (isAffine_const _)
              (isAffine_xor (isAffine_and_const k1 (haff1 hd1)) (isAffine_and_const k2 (haff2 hd2)))
          · rw [heq_fn, hinp, hf2, pol_xor, pol_const, Bool.false_xor, pol_xor,
              pol_and_const, pol_and_const, hc1 a b, hc2 a b,
              ← xorFin_and_left, ← xorFin_and_left, ← xorFin_xor]
            exact xorFin_cast hcnt.symm _ _ (fun j hj1 hj2 => by
              dsimp only
              cases k1 <;> cases k2 <;> cases c1 ⟨j, hj1⟩ <;> cases c2 ⟨j, hj1⟩ <;>
                cases rank2 (L ⟨j, hj1⟩) (R ⟨j, hj1⟩) a b <;> rfl)
    ·
      have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + 1 := by
        rw [hcount_step, hnl]; rfl
      have hlen2 : g.inputs.length = 2 := by
        unfold nonlinear at hnl
        simp only [Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.1
      have hq1 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        unfold nonlinear at hnl
        simp only [Bool.and_eq_true] at hnl
        exact hnl.2
      rcases hinp : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
      · rw [hinp] at hlen2; simp at hlen2
      · rw [hinp] at hlen2; simp at hlen2
      · have hrest : rest = [] := by rw [hinp] at hlen2; cases rest <;> simp at hlen2; rfl
        subst hrest
        have hi1 : i1 < width + gs.length := hrb_g i1 (by simp [hinp])
        have hi2 : i2 < width + gs.length := hrb_g i2 (by simp [hinp])
        rw [hinp, hnl] at hdg_le
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_true] at hdg_le
        have hle1 := Nat.le_max_left ((depthList width gs).getD i1 0) ((depthList width gs).getD i2 0)
        have hle2 := Nat.le_max_right ((depthList width gs).getD i1 0) ((depthList width gs).getD i2 0)
        have hd1 : (depthList width gs).getD i1 0 = 0 := by omega
        have hd2 : (depthList width gs).getD i2 0 = 0 := by omega
        rcases (hgs i1 hi1).1 hd1 with ⟨cf1, lf1, hlf1⟩
        rcases (hgs i2 hi2).1 hd2 with ⟨cf2, lf2, hlf2⟩
        let L' : Fin ((gs ++ [g]).countP nonlinear) → Fin N → Bool :=
          fun p => if hp : p.val < gs.countP nonlinear then L ⟨p.val, hp⟩ else lf1
        let R' : Fin ((gs ++ [g]).countP nonlinear) → Fin N → Bool :=
          fun p => if hp : p.val < gs.countP nonlinear then R ⟨p.val, hp⟩ else lf2
        refine ⟨L', R', fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hilt : i < width + gs.length
        · have hdi : (depthList width (gs ++ [g])).getD i 0 = (depthList width gs).getD i 0 := by
            rw [hds_step, getD_append_lt _ _ _ (by omega)]
          have hwi : ∀ y, (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false =
              (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false := fun y => by
            rw [hw_step y, getD_append_lt _ _ _ (by rw [hw_len y]; exact hilt)]
          rcases hgs i hilt with ⟨haff_i, ci, hci⟩
          let ci' : Fin ((gs ++ [g]).countP nonlinear) → Bool :=
            fun p => if hp : p.val < gs.countP nonlinear then ci ⟨p.val, hp⟩ else false
          refine ⟨fun hd0 => ?_, ci', fun a b => ?_⟩
          · have heq : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false) =
                (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false) := funext hwi
            rw [heq]; exact haff_i (hdi ▸ hd0)
          · have heq : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD i false) =
                (fun y => (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i false) := funext hwi
            rw [heq, hci a b]
            have hstep : xorFin (fun p : Fin ((gs ++ [g]).countP nonlinear) => ci' p && rank2 (L' p) (R' p) a b) =
                xorFin (fun p : Fin (gs.countP nonlinear + 1) =>
                  ci' ⟨p.val, by omega⟩ && rank2 (L' ⟨p.val, by omega⟩) (R' ⟨p.val, by omega⟩) a b) :=
              xorFin_cast hcnt _ _ (fun _ _ _ => rfl)
            rw [hstep, xorFin_succ]
            have hlast : ci' ⟨(Fin.last (gs.countP nonlinear)).val, by simp [Fin.last, hcnt]⟩ = false := by
              simp [ci', Fin.last]
            rw [hlast, Bool.false_and, Bool.xor_false]
            apply xorFin_congr
            intro p
            simp [ci', L', R', p.isLt]
        · have hieq : i = width + gs.length := by omega
          subst hieq
          have hdi : (depthList width (gs ++ [g])).getD (width + gs.length) 0 = 1 := by
            rw [hds_step, ← hds_len, getD_append_eq, hinp, hnl]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat, hd1, hd2]
            rfl
          have hwi : ∀ y, (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD (width + gs.length) false =
              g.op.eval [(Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false,
                         (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i2 false] := fun y => by
            rw [hw_step y, ← hw_len y, getD_append_eq, hinp]; rfl
          let plast : Fin ((gs ++ [g]).countP nonlinear) := ⟨gs.countP nonlinear, by omega⟩
          refine ⟨fun hd0 => by omega, fun p => decide (p = plast), fun a b => ?_⟩
          have heq_fn : (fun y => (Circuit.wires ⟨gs ++ [g], 0⟩ (φ y)).getD (width + gs.length) false) =
              (fun y => xor (g.op.eval [false, false])
                (xor (xor (g.op.eval [false, false]) (g.op.eval [true, false]) &&
                        (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false)
                  (xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]) &&
                          (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i2 false)
                    ((Circuit.wires ⟨gs, 0⟩ (φ y)).getD i1 false &&
                     (Circuit.wires ⟨gs, 0⟩ (φ y)).getD i2 false)))) := by
            funext y; rw [hwi y, gate_eval_2 g.op, hq1, Bool.true_and]
          rw [heq_fn, pol_xor, pol_const, Bool.false_xor, pol_xor, pol_xor,
            pol_and_const, pol_and_const,
            pol_affine ⟨cf1, lf1, hlf1⟩, pol_affine ⟨cf2, lf2, hlf2⟩,
            Bool.and_false, Bool.and_false, Bool.false_xor, Bool.false_xor,
            pol_and_affine hlf1 hlf2]
          rw [xorFin_single' plast]
          · simp [L', R', plast]
          · intro p hp; simp [hp]

def InSpan {m : Nat} {α : Type} (G : Fin m → α → Bool) (f : α → Bool) : Prop :=
  ∃ c : Fin m → Bool, ∀ x, f x = xorFin (fun p => c p && G p x)

lemma inSpan_xor {m : Nat} {α : Type} {G : Fin m → α → Bool} {f g : α → Bool}
    (hf : InSpan G f) (hg : InSpan G g) :
    InSpan G (fun x => xor (f x) (g x)) := by
  rcases hf with ⟨cf, hfe⟩
  rcases hg with ⟨cg, hge⟩
  refine ⟨fun p => xor (cf p) (cg p), fun x => ?_⟩
  dsimp only
  rw [hfe x, hge x, ← xorFin_xor]
  apply xorFin_congr
  intro p
  cases cf p <;> cases cg p <;> cases G p x <;> rfl

lemma inSpan_xorFin {m d : Nat} {α : Type} {G : Fin m → α → Bool} (F : Fin d → α → Bool)
    (hF : ∀ i, InSpan G (F i)) :
    InSpan G (fun x => xorFin (fun i => F i x)) := by
  induction d with
  | zero =>
    refine ⟨fun _ => false, fun _ => ?_⟩
    dsimp only
    simp only [Bool.false_and, xorFin_false]
    rfl
  | succ d ih =>
    have h1 := ih (fun i => F i.castSucc) (fun i => hF i.castSucc)
    have h2 := hF (Fin.last d)
    rcases inSpan_xor h1 h2 with ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    have hcx := hc x
    dsimp only at hcx ⊢
    rw [xorFin_succ, hcx]

lemma steinitz_bool {m d : Nat} {α : Type} (G : Fin m → α → Bool) (U : Fin d → α → Bool)
    (hU : ∀ i, InSpan G (U i))
    (hind : ∀ a : Fin d → Bool, (∀ x, xorFin (fun i => a i && U i x) = false) → ∀ i, a i = false) :
    ∃ P : Finset (Fin m), P.card = d ∧
      ∀ f : α → Bool, InSpan G f →
        ∃ (a : Fin d → Bool) (b : Fin m → Bool),
          (∀ p ∈ P, b p = false) ∧
          ∀ x, f x = xor (xorFin (fun i => a i && U i x)) (xorFin (fun p => b p && G p x)) := by
  induction d with
  | zero =>
    refine ⟨∅, rfl, fun f hf => ?_⟩
    rcases hf with ⟨c, hc⟩
    refine ⟨fun i => i.elim0, c, (fun _ hp => nomatch hp), fun x => ?_⟩
    dsimp only
    rw [hc x]
    have h0 : xorFin (fun i : Fin 0 => i.elim0 && U i x) = false := rfl
    rw [h0, Bool.false_xor]
  | succ d ih =>
    have hU' : ∀ i : Fin d, InSpan G (U i.castSucc) := fun i => hU i.castSucc
    have hind' : ∀ a : Fin d → Bool,
        (∀ x, xorFin (fun i => a i && U i.castSucc x) = false) → ∀ i, a i = false := by
      intro a ha i
      let a' : Fin (d + 1) → Bool := fun j => if hj : j.val < d then a ⟨j.val, hj⟩ else false
      have ha' : ∀ x, xorFin (fun j => a' j && U j x) = false := by
        intro x
        rw [xorFin_succ]
        have hlast : a' (Fin.last d) = false := by simp [a']
        rw [hlast, Bool.false_and, Bool.xor_false]
        have hcast : xorFin (fun j : Fin d => a' j.castSucc && U j.castSucc x) =
            xorFin (fun j : Fin d => a j && U j.castSucc x) :=
          xorFin_congr _ _ (fun j => by simp [a', j.isLt])
        rw [hcast, ha x]
      have h0 := hind a' ha' i.castSucc
      simpa [a', i.isLt] using h0
    rcases ih (fun i => U i.castSucc) hU' hind' with ⟨P, hPcard, hPspan⟩
    rcases hPspan (U (Fin.last d)) (hU (Fin.last d)) with ⟨a0, b0, hb0P, hUlast⟩
    have hex : ∃ p0 : Fin m, b0 p0 = true := by
      by_contra hall
      push Not at hall
      let a' : Fin (d + 1) → Bool := fun j => if hj : j.val < d then a0 ⟨j.val, hj⟩ else true
      have ha' : ∀ x, xorFin (fun j => a' j && U j x) = false := by
        intro x
        rw [xorFin_succ]
        have hlast : a' (Fin.last d) = true := by simp [a']
        rw [hlast, Bool.true_and, hUlast x]
        have hbz : xorFin (fun p => b0 p && G p x) = false :=
          xorFin_eq_false _ (fun p => by
            have hp : b0 p = false := Bool.eq_false_iff.mpr (hall p)
            simp [hp])
        rw [hbz, Bool.xor_false]
        have hcast : xorFin (fun j : Fin d => a' j.castSucc && U j.castSucc x) =
            xorFin (fun j : Fin d => a0 j && U j.castSucc x) :=
          xorFin_congr _ _ (fun j => by simp [a', j.isLt])
        rw [hcast, Bool.xor_self]
      have hbad := hind a' ha' (Fin.last d)
      simp [a'] at hbad
    rcases hex with ⟨p0, hp0⟩
    have hp0_not : p0 ∉ P := fun hmem => by rw [hb0P p0 hmem] at hp0; cases hp0

    have hGp0 : ∀ x, G p0 x =
        xor (xor (U (Fin.last d) x) (xorFin (fun i : Fin d => a0 i && U i.castSucc x)))
            (xorFin (fun p => (if p = p0 then false else b0 p) && G p x)) := by
      intro x
      have hsplit : xorFin (fun p => b0 p && G p x) =
          xor (G p0 x) (xorFin (fun p => (if p = p0 then false else b0 p) && G p x)) := by
        have h1 : xorFin (fun p => b0 p && G p x) =
            xor (xorFin (fun p => if p = p0 then G p0 x else false))
                (xorFin (fun p => (if p = p0 then false else b0 p) && G p x)) := by
          rw [← xorFin_xor]
          apply xorFin_congr
          intro p
          by_cases hp : p = p0
          · subst hp; simp [hp0]
          · simp [hp]
        rw [h1, xorFin_single]
      have hU := hUlast x
      rw [hsplit] at hU
      rw [hU]
      cases xorFin (fun i : Fin d => a0 i && U i.castSucc x) <;>
        cases G p0 x <;>
        cases xorFin (fun p => (if p = p0 then false else b0 p) && G p x) <;> rfl
    refine ⟨insert p0 P, by rw [Finset.card_insert_of_notMem hp0_not, hPcard], fun f hf => ?_⟩
    rcases hPspan f hf with ⟨af, bf, hbfP, hfe⟩
    let c := bf p0
    let af' : Fin (d + 1) → Bool := fun j =>
      if hj : j.val < d then xor (af ⟨j.val, hj⟩) (c && a0 ⟨j.val, hj⟩) else c
    let bf' : Fin m → Bool := fun p =>
      if p = p0 then false else xor (bf p) (c && b0 p)
    refine ⟨af', bf', ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpP
      · simp [bf']
      · have hne : p ≠ p0 := fun he => hp0_not (he ▸ hpP)
        simp [bf', hne, hbfP p hpP, hb0P p hpP]
    · intro x
      rw [hfe x, xorFin_succ]
      have hlast : af' (Fin.last d) = c := by simp [af']
      rw [hlast]
      have hA : xorFin (fun i : Fin d => af' i.castSucc && U i.castSucc x) =
          xor (xorFin (fun i : Fin d => af i && U i.castSucc x))
              (c && xorFin (fun i : Fin d => a0 i && U i.castSucc x)) := by
        rw [← xorFin_and_left, ← xorFin_xor]
        apply xorFin_congr
        intro i
        simp only [af', Fin.val_castSucc, i.isLt, dite_true]
        cases af i <;> cases c <;> cases a0 i <;> cases U i.castSucc x <;> rfl
      have hB : xorFin (fun p => bf p && G p x) =
          xor (c && G p0 x) (xorFin (fun p => (if p = p0 then false else bf p) && G p x)) := by
        have h1 : xorFin (fun p => bf p && G p x) =
            xor (xorFin (fun p => if p = p0 then c && G p0 x else false))
                (xorFin (fun p => (if p = p0 then false else bf p) && G p x)) := by
          rw [← xorFin_xor]
          apply xorFin_congr
          intro p
          by_cases hp : p = p0
          · subst hp; simp [c]
          · simp [hp]
        rw [h1, xorFin_single]
      have hB' : xorFin (fun p => bf' p && G p x) =
          xor (xorFin (fun p => (if p = p0 then false else bf p) && G p x))
              (c && xorFin (fun p => (if p = p0 then false else b0 p) && G p x)) := by
        rw [← xorFin_and_left, ← xorFin_xor]
        apply xorFin_congr
        intro p
        by_cases hp : p = p0
        · subst hp; simp [bf']
        · simp only [bf', hp, ite_false]
          cases bf p <;> cases c <;> cases b0 p <;> cases G p x <;> rfl
      rw [hA, hB, hB', hGp0 x]
      cases c <;>
        cases U (Fin.last d) x <;>
        cases xorFin (fun i : Fin d => af i && U i.castSucc x) <;>
        cases xorFin (fun i : Fin d => a0 i && U i.castSucc x) <;>
        cases xorFin (fun p => (if p = p0 then false else bf p) && G p x) <;>
        cases xorFin (fun p => (if p = p0 then false else b0 p) && G p x) <;> rfl

lemma rank_le_of_rank2_span {N m s : Nat} (L R : Fin m → Fin N → Bool)
    (P : Finset (Fin m)) (b : Fin m → Bool) (hbP : ∀ p ∈ P, b p = false)
    (v : Fin s → Fin N → Bool)
    (hinv : ∀ c : Fin s → Bool,
      (∀ q : Fin s,
        xorFin (fun i : Fin s =>
          c i && xorFin (fun p : Fin m => b p && rank2 (L p) (R p) (v i) (v q))) = false) →
      ∀ i : Fin s, c i = false) :
    s ≤ 2 * (m - P.card) := by
  let Q := Finset.univ \ P
  have hQcard : Q.card = m - P.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ, Fintype.card_fin]
  let Φ : (Fin s → Bool) → (Q → Bool × Bool) := fun c p =>
    (xorFin (fun i => c i && dot (L p.val) (v i)),
     xorFin (fun i => c i && dot (R p.val) (v i)))
  have hinj : Function.Injective Φ := by
    intro c1 c2 heq
    let c : Fin s → Bool := fun i => xor (c1 i) (c2 i)
    have hzero : ∀ p : Fin m, b p = true →
        xorFin (fun i => c i && dot (L p) (v i)) = false ∧
        xorFin (fun i => c i && dot (R p) (v i)) = false := by
      intro p hbp
      have hpQ : p ∈ Q := by
        simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hpP; rw [hbP p hpP] at hbp; cases hbp
      have hpair := congrFun heq ⟨p, hpQ⟩
      have hL := congrArg Prod.fst hpair
      have hR := congrArg Prod.snd hpair
      dsimp only [Φ] at hL hR
      constructor
      · have h1 : xorFin (fun i => c i && dot (L p) (v i)) =
            xor (xorFin (fun i => c1 i && dot (L p) (v i)))
                (xorFin (fun i => c2 i && dot (L p) (v i))) := by
          rw [← xorFin_xor]; apply xorFin_congr; intro i; dsimp only [c]
          cases c1 i <;> cases c2 i <;> cases dot (L p) (v i) <;> rfl
        rw [h1, hL, Bool.xor_self]
      · have h1 : xorFin (fun i => c i && dot (R p) (v i)) =
            xor (xorFin (fun i => c1 i && dot (R p) (v i)))
                (xorFin (fun i => c2 i && dot (R p) (v i))) := by
          rw [← xorFin_xor]; apply xorFin_congr; intro i; dsimp only [c]
          cases c1 i <;> cases c2 i <;> cases dot (R p) (v i) <;> rfl
        rw [h1, hR, Bool.xor_self]
    have hc0 : ∀ i, c i = false := by
      apply hinv
      intro q
      have hrew : xorFin (fun i : Fin s =>
            c i && xorFin (fun p : Fin m => b p && rank2 (L p) (R p) (v i) (v q))) =
          xorFin (fun p : Fin m =>
            b p && xor (xorFin (fun i => c i && dot (L p) (v i)) && dot (R p) (v q))
                       (xorFin (fun i => c i && dot (R p) (v i)) && dot (L p) (v q))) := by
        have h1 : xorFin (fun i : Fin s =>
              c i && xorFin (fun p : Fin m => b p && rank2 (L p) (R p) (v i) (v q))) =
            xorFin (fun i : Fin s =>
              xorFin (fun p : Fin m => c i && (b p && rank2 (L p) (R p) (v i) (v q)))) :=
          xorFin_congr _ _ (fun i => (xorFin_and_left _ _).symm)
        rw [h1, xorFin_swap]
        apply xorFin_congr
        intro p
        rw [← xorFin_and_right, ← xorFin_and_right, ← xorFin_xor, ← xorFin_and_left]
        apply xorFin_congr
        intro i
        unfold rank2
        cases c i <;> cases b p <;> cases dot (L p) (v i) <;> cases dot (R p) (v q) <;>
          cases dot (R p) (v i) <;> cases dot (L p) (v q) <;> rfl
      rw [hrew]
      apply xorFin_eq_false
      intro p
      cases hbp : b p
      · rfl
      · rcases hzero p hbp with ⟨hL0, hR0⟩
        simp [hL0, hR0]
    funext i
    have hi := hc0 i
    dsimp only [c] at hi
    cases hc1 : c1 i <;> cases hc2 : c2 i <;> simp [hc1, hc2] at hi ⊢
  have hcard := Fintype.card_le_of_injective Φ hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_coe, hQcard] at hcard
  have hpow : 2 ^ s ≤ 2 ^ (2 * (m - P.card)) := by
    calc 2 ^ s ≤ (2 * 2) ^ (m - P.card) := hcard
      _ = (2 ^ 2) ^ (m - P.card) := rfl
      _ = 2 ^ (2 * (m - P.card)) := (Nat.pow_mul 2 2 (m - P.card)).symm
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

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

lemma Qp_eq_QpMid (hr : 2 ≤ r) (hk3 : k = 3 * r) (t : Fin k → Bool) (ht3 : t ⟨3, by omega⟩ = false) :
    Qp hk r t =
      xor (if r % 2 = 0 then xor (Q0 hr hk3 t) (Qk hr hk3 t) else false)
          (QpMid hk hr hk3 t) := by
  unfold Qp QpMid Q0 Qk
  rw [xorFin_split3 hr hk3]

  have hc0 : xorFin (fun j : Fin r => decide (⟨3 * j.val, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 1))) && t (ix hk (3 * j.val + 2)))) =
    xor (if r % 2 = 0 then !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩ else false)
      (xor (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩)
        (xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩))) := by
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h0 : (decide (⟨3 * 0, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 1))) && t (ix hk (3 * 0 + 2)))) =
        if r % 2 = 0 then !(t ⟨1, by omega⟩) && t ⟨2, by omega⟩ else false := by
      rw [neededSet_c0 hr hk3 ⟨0, by omega⟩, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
      dsimp only; rw [ite_pos rfl]
      by_cases h : r % 2 = 0 <;> simp [h]
    have h1 : (decide (⟨3 * (0 + 1), by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (0 + 1) + 1))) && t (ix hk (3 * (0 + 1) + 2)))) =
        (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) := by
      have hn := neededSet_c0 hr hk3 ⟨1, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    have hrest : xorFin (fun j : Fin (r - 1 - 1) =>
          decide (⟨3 * (j.val + 1 + 1), by omega⟩ ∈ neededSet r k) &&
            (!(t (ix hk (3 * (j.val + 1 + 1) + 1))) && t (ix hk (3 * (j.val + 1 + 1) + 2)))) =
        xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      have hn := neededSet_c0 hr hk3 ⟨idx + 2, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
    rw [h0, h1, hrest]

  have hc1 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 1, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 1 + 1))) && t (ix hk (3 * j.val + 1 + 2)))) =
    (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 1 + 1))) && t (ix hk (3 * 0 + 1 + 2)))) = false := by
      rw [ix_eq_of_lt hk (by omega : 3 * 0 + 1 + 2 < k),
        show (⟨3 * 0 + 1 + 2, by omega⟩ : Fin k) = ⟨3, by omega⟩ from rfl, ht3]
      simp
    have hl : (decide (⟨3 * (r - 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (r - 1) + 1 + 1))) && t (ix hk (3 * (r - 1) + 1 + 2)))) =
        (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) := by
      have hn := neededSet_c1 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [decide_eq_true (Or.inr rfl)] at hn
      have hp1 : ix hk (3 * (r - 1) + 1 + 1) = ⟨k - 1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 1 + 1 = k - 1 by omega])).trans (ix_eq_of_lt hk (by omega))
      have hp2 : ix hk (3 * (r - 1) + 1 + 2) = ⟨0, hk⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 1 + 2 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      rw [hn, Bool.true_and, hp1, hp2]
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 1, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (j.val + 1) + 1 + 1))) && t (ix hk (3 * (j.val + 1) + 1 + 2)))) = false := by
      apply xorFin_eq_false; intro j
      rw [neededSet_c1 hr hk3 ⟨j.val + 1, by omega⟩]
      have hn : ¬(j.val + 1 = 0 ∨ j.val + 1 = r - 1) := by omega
      rw [decide_eq_false hn, Bool.false_and]
    rw [h0, hl, hm]; simp

  have hc2 : xorFin (fun j : Fin r => decide (⟨3 * j.val + 2, by omega⟩ ∈ neededSet r k) &&
      (!(t (ix hk (3 * j.val + 2 + 1))) && t (ix hk (3 * j.val + 2 + 2)))) =
    xor (t ⟨4, by omega⟩)
      (xor (xorFin (fun j : Fin (r - 2) =>
          !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩))
        (if r % 2 = 0 then !(t ⟨0, hk⟩) && t ⟨1, by omega⟩ else false)) := by
    rw [xorFin_ends hr]; dsimp only
    have h0 : (decide (⟨3 * 0 + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * 0 + 2 + 1))) && t (ix hk (3 * 0 + 2 + 2)))) = t ⟨4, by omega⟩ := by
      have hn := neededSet_c2 hr hk3 ⟨0, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega : 3 * 0 + 2 + 1 < k),
        ix_eq_of_lt hk (by omega : 3 * 0 + 2 + 2 < k),
        show (⟨3 * 0 + 2 + 1, by omega⟩ : Fin k) = ⟨3, by omega⟩ from rfl, ht3]
      simp
    have hl : (decide (⟨3 * (r - 1) + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (r - 1) + 2 + 1))) && t (ix hk (3 * (r - 1) + 2 + 2)))) =
        if r % 2 = 0 then !(t ⟨0, hk⟩) && t ⟨1, by omega⟩ else false := by
      have hn := neededSet_c2 hr hk3 ⟨r - 1, by omega⟩
      dsimp only at hn; rw [ite_pos rfl] at hn
      have hp1 : ix hk (3 * (r - 1) + 2 + 1) = ⟨0, hk⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 2 + 1 = k by omega, Nat.mod_self, Nat.zero_mod])).trans (ix_eq_of_lt hk hk)
      have hp2 : ix hk (3 * (r - 1) + 2 + 2) = ⟨1, by omega⟩ :=
        (ix_mod_eq hk (by rw [show 3 * (r - 1) + 2 + 2 = 1 + k by omega, Nat.add_mod_right])).trans (ix_eq_of_lt hk (by omega))
      rw [hn, hp1, hp2]; by_cases h : r % 2 = 0 <;> simp [h]
    have hm : xorFin (fun j : Fin (r - 2) => decide (⟨3 * (j.val + 1) + 2, by omega⟩ ∈ neededSet r k) &&
        (!(t (ix hk (3 * (j.val + 1) + 2 + 1))) && t (ix hk (3 * (j.val + 1) + 2 + 2)))) =
      xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) := by
      apply xorFin_congr; intro j
      have hn := neededSet_c2 hr hk3 ⟨j.val + 1, by omega⟩
      dsimp only at hn; rw [ite_neg (by omega)] at hn
      rw [hn, Bool.true_and, ix_eq_of_lt hk (by omega), ix_eq_of_lt hk (by omega)]
      exact congrArg₂ (fun a b => !a && b) (congrArg t (Fin.ext (by dsimp only; omega))) (congrArg t (Fin.ext (by dsimp only; omega)))
    rw [h0, hl, hm]
  dsimp only at hc0 hc1 hc2 ⊢
  rw [hc0, hc1, hc2]
  have hpair : xor (xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩))
      (xorFin (fun j : Fin (r - 2) =>
        !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩)) =
    xorFin (fun j : Fin (r - 2) =>
      xor (t ⟨3 * (j.val + 2) + 1, by omega⟩ &&
            !(xor (t ⟨3 * (j.val + 2), by omega⟩) (t ⟨3 * (j.val + 2) + 2, by omega⟩)))
          (t ⟨3 * (j.val + 2) + 2, by omega⟩)) := by
    rw [← xorFin_xor]; apply xorFin_congr; intro j
    cases t ⟨3 * (j.val + 2), by omega⟩ <;> cases t ⟨3 * (j.val + 2) + 1, by omega⟩ <;>
      cases t ⟨3 * (j.val + 2) + 2, by omega⟩ <;> rfl
  rw [← hpair]
  by_cases he : r % 2 = 0
  · simp only [he, ite_true]
    cases (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) <;>
      cases (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) <;>
      cases (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) <;>
      cases t ⟨4, by omega⟩ <;>
      cases (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) <;> rfl
  · simp only [he, ite_false]
    cases (!(t ⟨4, by omega⟩) && t ⟨5, by omega⟩) <;>
      cases t ⟨4, by omega⟩ <;>
      cases (!(t ⟨k - 1, by omega⟩) && t ⟨0, hk⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2) + 1, by omega⟩) && t ⟨3 * (j.val + 2) + 2, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => !(t ⟨3 * (j.val + 2), by omega⟩) && t ⟨3 * (j.val + 2) + 1, by omega⟩) <;> rfl

lemma Qp_r2 (hr2 : r = 2) (hk3 : k = 3 * r) (t : Fin k → Bool)
    (ht3 : t ⟨3, by omega⟩ = false)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    Qp hk r t = t ⟨0, hk⟩ := by
  subst hr2; subst hk3
  rw [Qp_eq_QpMid hk (by omega) rfl t ht3]
  unfold resSum at hs01 hs02
  have hfr2 : ∀ g : Fin 2 → Bool, xorFin g = xor (g ⟨0, by omega⟩) (g ⟨1, by omega⟩) := by
    intro g; unfold xorFin; have : List.finRange 2 = [0, 1] := rfl; rw [this]; simp
  rw [hfr2, hfr2] at hs01 hs02
  dsimp only at hs01 hs02
  rw [ht3, Bool.xor_false] at hs01 hs02
  change t ⟨0, hk⟩ = xor (t ⟨1, by omega⟩) (t ⟨4, by omega⟩) at hs01
  change t ⟨0, hk⟩ = xor (t ⟨2, by omega⟩) (t ⟨5, by omega⟩) at hs02
  unfold Q0 Qk QpMid
  have h0 : ∀ f : Fin (2 - 2) → Bool, xorFin f = false := fun _ => rfl
  rw [h0]
  have heven : (if 2 % 2 = 0 then xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) else false) =
      xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (!(t ⟨0, hk⟩) && t ⟨1, by omega⟩) := rfl
  rw [heven]
  cases h0' : t ⟨0, hk⟩ <;> cases h1' : t ⟨1, by omega⟩ <;> cases h2' : t ⟨2, by omega⟩ <;>
    cases h4' : t ⟨4, by omega⟩ <;> cases h5' : t ⟨5, by omega⟩ <;>
    rw [h0', h1', h4'] at hs01 <;> rw [h0', h2', h5'] at hs02 <;>
    cases hs01 <;> cases hs02 <;> rfl

lemma Qp_r3 (hr3 : r = 3) (hk3 : k = 3 * r) (t : Fin k → Bool)
    (ht3 : t ⟨3, by omega⟩ = false)
    (hs01 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 1 (by omega))
    (hs02 : resSum r hk3 t 0 (by omega) = resSum r hk3 t 2 (by omega)) :
    Qp hk r t =
      xor (Q0 (by omega : 2 ≤ r) hk3 t)
        (xor ((xor (t ⟨5, by omega⟩) (xor (t ⟨6, by omega⟩) (t ⟨7, by omega⟩))) &&
              (xor (t ⟨0, hk⟩) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩))))
          (xor ((xor (t ⟨4, by omega⟩) (t ⟨6, by omega⟩)) &&
                (xor (t ⟨2, by omega⟩) (xor (t ⟨6, by omega⟩) (t ⟨7, by omega⟩))))
            (xor (t ⟨0, hk⟩) (t ⟨4, by omega⟩)))) := by
  subst hr3; subst hk3
  rw [Qp_eq_QpMid hk (by omega) rfl t ht3]
  unfold resSum at hs01 hs02
  have hfr3 : ∀ g : Fin 3 → Bool, xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (g ⟨2, by omega⟩)) := by
    intro g; unfold xorFin; have : List.finRange 3 = [0, 1, 2] := rfl; rw [this]; simp
  rw [hfr3, hfr3] at hs01 hs02
  dsimp only at hs01 hs02
  rw [ht3, Bool.false_xor] at hs01 hs02
  change xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩) = xor (t ⟨1, by omega⟩) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩)) at hs01
  change xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩) = xor (t ⟨2, by omega⟩) (xor (t ⟨5, by omega⟩) (t ⟨8, by omega⟩)) at hs02
  unfold Q0 QpMid
  have hfr1 : ∀ g : Fin 1 → Bool, xorFin g = g ⟨0, by omega⟩ := by
    intro g; unfold xorFin; have : List.finRange 1 = [0] := rfl; rw [this]; simp
  rw [hfr1]
  have hodd : (if 3 % 2 = 0 then xor (!(t ⟨1, by omega⟩) && t ⟨2, by omega⟩) (Qk (by omega) rfl t) else false) = false := rfl
  rw [hodd, Bool.false_xor]
  dsimp only
  have ht1 : t ⟨1, by omega⟩ = xor (xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩)) (xor (t ⟨4, by omega⟩) (t ⟨7, by omega⟩)) := by
    cases h0' : t ⟨0, hk⟩ <;> cases h1' : t ⟨1, by omega⟩ <;> cases h4' : t ⟨4, by omega⟩ <;>
      cases h6' : t ⟨6, by omega⟩ <;> cases h7' : t ⟨7, by omega⟩ <;>
      rw [h0', h1', h4', h6', h7'] at hs01 <;> cases hs01 <;> rfl
  have ht8 : t ⟨8, by omega⟩ = xor (xor (t ⟨0, hk⟩) (t ⟨6, by omega⟩)) (xor (t ⟨2, by omega⟩) (t ⟨5, by omega⟩)) := by
    cases h0' : t ⟨0, hk⟩ <;> cases h2' : t ⟨2, by omega⟩ <;> cases h5' : t ⟨5, by omega⟩ <;>
      cases h6' : t ⟨6, by omega⟩ <;> cases h8' : t ⟨8, by omega⟩ <;>
      rw [h0', h2', h5', h6', h8'] at hs02 <;> cases hs02 <;> rfl
  rw [ht1, ht8]
  cases t ⟨0, hk⟩ <;> cases t ⟨2, by omega⟩ <;> cases t ⟨4, by omega⟩ <;>
    cases t ⟨5, by omega⟩ <;> cases t ⟨6, by omega⟩ <;> cases t ⟨7, by omega⟩ <;> rfl

lemma isAffine_tWalk (j : Nat) : IsAffine (fun d : Fin k → Bool => tWalk d j) := by
  induction j with
  | zero => exact isAffine_const false
  | succ j ih =>
    cases j with
    | zero =>
      by_cases h : 2 < k
      · simpa [tWalk, h] using isAffine_coord (N := k) ⟨2, h⟩
      · simpa [tWalk, h] using isAffine_const (N := k) false
    | succ j =>
      have hterm : IsAffine (fun d : Fin k → Bool => if h : j + 3 < k then !(d ⟨j + 3, h⟩) else false) := by
        by_cases h : j + 3 < k
        · simpa [h] using isAffine_not (isAffine_coord (N := k) ⟨j + 3, h⟩)
        · simpa [h] using isAffine_const (N := k) false
      exact isAffine_xor ih hterm

lemma isAffine_tRaw (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun d : Fin k → Bool => tRaw hr hk3 d i) := by
  unfold tRaw
  split_ifs
  · exact isAffine_not (isAffine_coord _)
  · exact isAffine_const false
  · exact isAffine_not (isAffine_coord _)
  · exact isAffine_tWalk (i.val - 3)

lemma isAffine_tOfD (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun d : Fin k → Bool => tOfD hr hk3 d i) := by
  unfold tOfD
  split_ifs
  · exact isAffine_xor (isAffine_tRaw hr hk3 _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_tRaw hr hk3 _) (isAffine_tRaw hr hk3 _)))
  · exact isAffine_tRaw hr hk3 i

lemma isAffine_zPair {N : Nat} (W : (Fin N → Bool) → Fin k → Bool)
    (Z0 Z1 : (Fin N → Bool) → Bool)
    (hW : ∀ i, IsAffine (fun y => W y i)) (hZ0 : IsAffine Z0) (hZ1 : IsAffine Z1) (j : Nat) :
    IsAffine (fun y => (zPair (W y) (Z0 y) (Z1 y) j).1) ∧
    IsAffine (fun y => (zPair (W y) (Z0 y) (Z1 y) j).2) := by
  induction j with
  | zero => exact ⟨hZ0, hZ1⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have hwj : IsAffine (fun y => if h : j + 1 < k then W y ⟨j + 1, h⟩ else false) := by
      by_cases h : j + 1 < k
      · simpa [h] using hW ⟨j + 1, h⟩
      · simpa [h] using isAffine_const false
    exact isAffine_xor ih.1 (isAffine_xor ih.2 hwj)

lemma isAffine_zOf {N : Nat} (W : (Fin N → Bool) → Fin k → Bool)
    (Z0 Z1 : (Fin N → Bool) → Bool)
    (hW : ∀ i, IsAffine (fun y => W y i)) (hZ0 : IsAffine Z0) (hZ1 : IsAffine Z1) (i : Fin k) :
    IsAffine (fun y => zOf (W y) (Z0 y) (Z1 y) i) :=
  (isAffine_zPair W Z0 Z1 hW hZ0 hZ1 i.val).1

lemma isAffine_linP {N : Nat} (u : Fin k → Bool) (T : (Fin N → Bool) → Fin k → Bool)
    (hT : ∀ i, IsAffine (fun y => T y i)) :
    IsAffine (fun y => linP hk r u (T y)) := by
  unfold linP
  apply isAffine_xorFin; intro i
  apply isAffine_and_const
  exact isAffine_xor (hT i) (isAffine_xor
    (isAffine_zOf T (fun _ => false) (fun _ => false) hT (isAffine_const false) (isAffine_const false) _)
    (isAffine_const _))

end RowAlg

lemma xorFin_add_split {N M : Nat} (g : Fin (N + M) → Bool) :
    xorFin g = xor (xorFin (fun i : Fin N => g ⟨i.val, by omega⟩))
                   (xorFin (fun j : Fin M => g ⟨N + j.val, by omega⟩)) := by
  induction M with
  | zero =>
    simp only [Nat.add_zero]
    have h0 : xorFin (fun j : Fin 0 => g ⟨N + j.val, by omega⟩) = false := rfl
    rw [h0, Bool.xor_false]
    exact xorFin_congr _ _ (fun _ => rfl)
  | succ M ih =>
    rw [xorFin_succ (fun j : Fin (M + 1) => g ⟨N + j.val, by omega⟩)]
    have hgoal := xorFin_succ (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩)
    have hcast : xorFin g = xorFin (fun x : Fin (N + M + 1) => g ⟨x.val, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcast, hgoal]
    have hih := ih (fun x : Fin (N + M) => g ⟨x.val, by omega⟩)
    have hcs : xorFin (fun i : Fin (N + M) => g ⟨i.castSucc.val, by omega⟩) =
        xorFin (fun i : Fin (N + M) => g ⟨i.val, by omega⟩) :=
      xorFin_congr _ _ (fun _ => rfl)
    rw [hcs, hih]
    simp only [Fin.last, Bool.xor_assoc]
    rfl

lemma flatten_ofFn_length {n L : Nat} (f : Fin n → List Bool) (hlen : ∀ j, (f j).length = L) :
    (List.ofFn f).flatten.length = n * L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hlen 0,
      ih (fun j => f j.succ) (fun j => hlen j.succ), Nat.succ_mul, Nat.add_comm]

lemma flatten_ofFn_getD {n L : Nat} (f : Fin n → List Bool) (hlen : ∀ j, (f j).length = L)
    (j : Fin n) (p : Fin L) :
    (List.ofFn f).flatten.getD (j.val * L + p.val) false = (f j).getD p.val false := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      have hlt : p.val < (f 0).length := by rw [hlen 0]; exact p.isLt
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_left hlt, List.getD_eq_getElem _ _ hlt]
    | succ j' =>
      simp only [Fin.val_succ]
      have hidx : (j'.val + 1) * L + p.val = (f 0).length + (j'.val * L + p.val) := by
        rw [hlen 0, Nat.succ_mul]; omega
      have hlt2 : j'.val * L + p.val < (List.ofFn (fun i : Fin n => f i.succ)).flatten.length := by
        rw [flatten_ofFn_length _ (fun i => hlen i.succ)]
        have : (j'.val + 1) * L ≤ n * L := Nat.mul_le_mul_right L j'.isLt
        rw [Nat.succ_mul] at this; omega
      rw [hidx, List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left]
      rw [← List.getD_eq_getElem _ _ hlt2]
      exact ih (fun i => f i.succ) (fun i => hlen i.succ) j'

def recordFn {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) : List Bool :=
  List.ofFn (diffFn hk u x) ++
    [decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1),
     row hk u x (ix hk 0), row hk u x (ix hk (k - 1))]

lemma recordFn_length {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).length = k + 3 := by
  simp [recordFn]

lemma recordFn_getD_lt {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool)
    (p : Nat) (hp : p < k) :
    (recordFn hk r u x).getD p false = diffFn hk u x ⟨p, hp⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp; omega),
    List.getElem_append_left (by omega), List.getElem_ofFn]

lemma recordFn_getD_k {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD k false =
      decide (((neededSet r k).filter (fun i => row hk u x i = true)).card % 2 = 1) := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp [hl]

lemma recordFn_getD_k1 {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD (k + 1) false = row hk u x ⟨0, hk⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp only [hl, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [ix_eq_of_lt hk hk]

lemma recordFn_getD_k2 {k : Nat} (hk : 0 < k) (r : Nat) (u x : Fin k → Bool) :
    (recordFn hk r u x).getD (k + 2) false = row hk u x ⟨k - 1, by omega⟩ := by
  unfold recordFn
  have hl : (List.ofFn (diffFn hk u x)).length = k := List.length_ofFn
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hl]; simp),
    List.getElem_append_right (by omega)]
  simp only [hl, Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [ix_eq_of_lt hk (by omega)]

def wOfY {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) (i : Fin k) : Bool :=
  if i.val = 0 then y ⟨0, by omega⟩
  else if i.val = 1 then
    xor (y ⟨0, by omega⟩) (xor (y ⟨2, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 5, by omega⟩))))
  else if i.val = 2 then y ⟨1, by omega⟩
  else if i.val = 3 then false
  else if hi : i.val < k - 1 then y ⟨i.val - 2, by omega⟩
  else
    xor (y ⟨0, by omega⟩) (xor (y ⟨1, by omega⟩)
      (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 3, by omega⟩))))

lemma wOfY_zero {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    wOfY hr hk3 (fun _ => false) i = false := by
  unfold wOfY
  split_ifs <;> simp [xorFin_false]

lemma wOfY_xor {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (a b : Fin (k - 3) → Bool) (i : Fin k) :
    wOfY hr hk3 (fun p => xor (a p) (b p)) i = xor (wOfY hr hk3 a i) (wOfY hr hk3 b i) := by
  unfold wOfY
  split_ifs
  · rfl
  · dsimp only
    have hx : xorFin (fun j : Fin (r - 2) =>
        xor (xor (a ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 4, by omega⟩))
            (xor (a ⟨3 * j.val + 5, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 5, by omega⟩)))
          (xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩))) := by
      rw [← xorFin_xor]; apply xorFin_congr; intro j
      cases a ⟨3 * j.val + 4, by omega⟩ <;> cases b ⟨3 * j.val + 4, by omega⟩ <;>
        cases a ⟨3 * j.val + 5, by omega⟩ <;> cases b ⟨3 * j.val + 5, by omega⟩ <;> rfl
    rw [hx]
    cases a ⟨0, by omega⟩ <;> cases b ⟨0, by omega⟩ <;>
      cases a ⟨2, by omega⟩ <;> cases b ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 5, by omega⟩)) <;>
      cases xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 5, by omega⟩)) <;> rfl
  · rfl
  · rfl
  · rfl
  · dsimp only
    have hx : xorFin (fun j : Fin (r - 2) =>
        xor (xor (a ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 4, by omega⟩))
            (xor (a ⟨3 * j.val + 3, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩))) =
      xor (xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 3, by omega⟩)))
          (xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩))) := by
      rw [← xorFin_xor]; apply xorFin_congr; intro j
      cases a ⟨3 * j.val + 4, by omega⟩ <;> cases b ⟨3 * j.val + 4, by omega⟩ <;>
        cases a ⟨3 * j.val + 3, by omega⟩ <;> cases b ⟨3 * j.val + 3, by omega⟩ <;> rfl
    rw [hx]
    cases a ⟨0, by omega⟩ <;> cases b ⟨0, by omega⟩ <;>
      cases a ⟨1, by omega⟩ <;> cases b ⟨1, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => xor (a ⟨3 * j.val + 4, by omega⟩) (a ⟨3 * j.val + 3, by omega⟩)) <;>
      cases xorFin (fun j : Fin (r - 2) => xor (b ⟨3 * j.val + 4, by omega⟩) (b ⟨3 * j.val + 3, by omega⟩)) <;> rfl

lemma isAffine_wOfY {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (i : Fin k) :
    IsAffine (fun y : Fin (k - 3) → Bool => wOfY hr hk3 y i) := by
  unfold wOfY
  split_ifs
  · exact isAffine_coord _
  · exact isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_coord _) (isAffine_coord _))))
  · exact isAffine_coord _
  · exact isAffine_const false
  · exact isAffine_coord _
  · exact isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _)
      (isAffine_xorFin _ (fun j => isAffine_xor (isAffine_coord _) (isAffine_coord _))))

lemma wOfY_3 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) :
    wOfY hr hk3 y ⟨3, by omega⟩ = false := by
  unfold wOfY; simp

lemma wOfY_resSum {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (y : Fin (k - 3) → Bool) :
    resSum r hk3 (wOfY hr hk3 y) 0 (by omega) = resSum r hk3 (wOfY hr hk3 y) 1 (by omega) ∧
    resSum r hk3 (wOfY hr hk3 y) 0 (by omega) = resSum r hk3 (wOfY hr hk3 y) 2 (by omega) := by
  have hs0 : resSum r hk3 (wOfY hr hk3 y) 0 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h0 : wOfY hr hk3 y ⟨3 * 0 + 0, by omega⟩ = y ⟨0, by omega⟩ := by unfold wOfY; simp
    have h3 : wOfY hr hk3 y ⟨3 * (0 + 1) + 0, by omega⟩ = false := by unfold wOfY; simp
    have hrest : xorFin (fun j : Fin (r - 1 - 1) => wOfY hr hk3 y ⟨3 * (j.val + 1 + 1) + 0, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h0, h3, hrest, Bool.false_xor]
  have hs1 : resSum r hk3 (wOfY hr hk3 y) 1 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_first (by omega), xorFin_first (by omega)]; dsimp only
    have h1 : wOfY hr hk3 y ⟨3 * 0 + 1, by omega⟩ =
        xor (y ⟨0, by omega⟩) (xor (y ⟨2, by omega⟩)
          (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 5, by omega⟩)))) := by
      unfold wOfY; simp
    have h4 : wOfY hr hk3 y ⟨3 * (0 + 1) + 1, by omega⟩ = y ⟨2, by omega⟩ := by
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
    have hrest : xorFin (fun j : Fin (r - 1 - 1) => wOfY hr hk3 y ⟨3 * (j.val + 1 + 1) + 1, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 5, by omega⟩) := by
      refine xorFin_cast (by omega) _ _ (fun idx hi1 hi2 => ?_)
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h1, h4, hrest, xorFin_xor]
    cases y ⟨0, by omega⟩ <;> cases y ⟨2, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 5, by omega⟩) <;> rfl
  have hs2 : resSum r hk3 (wOfY hr hk3 y) 2 (by omega) =
      xor (y ⟨0, by omega⟩) (xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩)) := by
    unfold resSum
    rw [xorFin_ends hr]; dsimp only
    have h2 : wOfY hr hk3 y ⟨3 * 0 + 2, by omega⟩ = y ⟨1, by omega⟩ := by unfold wOfY; simp
    have hlast : wOfY hr hk3 y ⟨3 * (r - 1) + 2, by omega⟩ =
        xor (y ⟨0, by omega⟩) (xor (y ⟨1, by omega⟩)
          (xorFin (fun j : Fin (r - 2) => xor (y ⟨3 * j.val + 4, by omega⟩) (y ⟨3 * j.val + 3, by omega⟩)))) := by
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_neg (by omega)]
    have hmid : xorFin (fun j : Fin (r - 2) => wOfY hr hk3 y ⟨3 * (j.val + 1) + 2, by omega⟩) =
        xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 3, by omega⟩) := by
      apply xorFin_congr; intro j
      unfold wOfY; dsimp only
      rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
        dite_pos (by omega)]
      exact congrArg y (Fin.ext (by dsimp only; omega))
    rw [h2, hlast, hmid, xorFin_xor]
    cases y ⟨0, by omega⟩ <;> cases y ⟨1, by omega⟩ <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 4, by omega⟩) <;>
      cases xorFin (fun j : Fin (r - 2) => y ⟨3 * j.val + 3, by omega⟩) <;> rfl
  rw [hs0, hs1, hs2]; exact ⟨rfl, rfl⟩

def phiBlock {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r) (u : Fin k → Bool)
    (y : Fin (k - 3) → Bool) : Fin k → Bool :=
  let w0 := wOfY hr hk3 y
  let b := xor (Qp hk r w0) (linP hk r u w0)
  let w := add w0 (fun i => b && decide (3 ≤ i.val))
  let z1 := xor (u ⟨1, by omega⟩) (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0))
  let z0 := xor (u ⟨0, hk⟩) (xor b (xor (w0 ⟨k - 1, by omega⟩) (Qk hr hk3 w0)))
  let z := zOf w z0 z1
  fun i => xor (z (ix hk (i.val + 1))) (u (ix hk (i.val + 1)))

lemma phiBlock_props {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r) (u : Fin k → Bool) :
    (∀ i : Fin k, IsAffine (fun y => diffFn hk u (phiBlock hk hr hk3 u y) i)) ∧
    (∀ y, row hk u (phiBlock hk hr hk3 u y) ⟨0, hk⟩ = false) ∧
    (∀ y, row hk u (phiBlock hk hr hk3 u y) ⟨k - 1, by omega⟩ = false) ∧
    (∀ y, decide (((neededSet r k).filter (fun i => row hk u (phiBlock hk hr hk3 u y) i = true)).card % 2 = 1) = false) ∧
    (∀ a b, pol (fun y => phiBlock hk hr hk3 u y ⟨0, hk⟩) a b =
      pol (fun y => Q0 hr hk3 (wOfY hr hk3 y)) a b) ∧
    (∀ a b, pol (fun y => xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩)) a b =
      pol (fun y => Qp hk r (wOfY hr hk3 y)) a b) ∧
    (∀ a b, pol (fun y => xor (phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩)
        (xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩))) a b =
      pol (fun y => Qk hr hk3 (wOfY hr hk3 y)) a b) := by
  have hrec : ∀ y,
      let w0 := wOfY hr hk3 y
      let b := xor (Qp hk r w0) (linP hk r u w0)
      let w := add w0 (fun i => b && decide (3 ≤ i.val))
      let z1 := xor (u ⟨1, by omega⟩) (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0))
      let z0 := xor (u ⟨0, hk⟩) (xor b (xor (w0 ⟨k - 1, by omega⟩) (Qk hr hk3 w0)))
      mix hk (add u (rot hk (phiBlock hk hr hk3 u y))) = w ∧
      phiBlock hk hr hk3 u y ⟨0, hk⟩ = xor z1 (u ⟨1, by omega⟩) ∧
      phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩ = xor z0 (u ⟨0, hk⟩) ∧
      row hk u (phiBlock hk hr hk3 u y) ⟨0, hk⟩ =
        xor (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0)) (phiBlock hk hr hk3 u y ⟨0, hk⟩) ∧
      row hk u (phiBlock hk hr hk3 u y) ⟨k - 1, by omega⟩ =
        xor (xor (xor b (w0 ⟨k - 1, by omega⟩)) (Qk hr hk3 w0)) (phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩) ∧
      decide (((neededSet r k).filter (fun i => row hk u (phiBlock hk hr hk3 u y) i = true)).card % 2 = 1) =
        xor b (xor (Qp hk r w0) (linP hk r u w0)) := fun y => by
    have hrs := wOfY_resSum hr hk3 y
    exact row_recovery hk hr hk3 u (wOfY hr hk3 y) _ _ _ hrs.1 hrs.2
  have hdiff_aff : ∀ i : Fin k, IsAffine (fun y => diffFn hk u (phiBlock hk hr hk3 u y) i) := by
    intro i
    have hfun : (fun y => diffFn hk u (phiBlock hk hr hk3 u y) i) =
        (fun y =>
          let w0 := wOfY hr hk3 y
          if i.val = 0 then false
          else if i.val = 1 then !(w0 (ix hk 2))
          else if i.val = 2 then xor (w0 (ix hk 3)) (w0 (ix hk 4))
          else if i.val < k - 2 then !(xor (w0 (ix hk (i.val + 1))) (w0 (ix hk (i.val + 2))))
          else if i.val = k - 2 then !(w0 (ix hk 0))
          else true) := by
      funext y
      have hd := diffFn_eq hk hr hk3 u (phiBlock hk hr hk3 u y) i
      dsimp only at hd
      rw [hd, (hrec y).1]
      dsimp only [add]
      split_ifs with h0 h1 h2 hlt hk2
      · rfl
      · rw [ix_eq_of_lt hk (by omega : 2 < k)]; simp
      · rw [ix_eq_of_lt hk (by omega : 3 < k), ix_eq_of_lt hk (by omega : 4 < k)]; dsimp only
        rw [show decide (3 ≤ 3) = true from rfl, show decide (3 ≤ 4) = true from rfl]
        simp only [Bool.and_true]
        cases xor (Qp hk r (wOfY hr hk3 y)) (linP hk r u (wOfY hr hk3 y)) <;>
          cases wOfY hr hk3 y ⟨3, by omega⟩ <;> cases wOfY hr hk3 y ⟨4, by omega⟩ <;> rfl
      · rw [ix_eq_of_lt hk (by omega : i.val + 1 < k), ix_eq_of_lt hk (by omega : i.val + 2 < k)]; dsimp only
        rw [decide_eq_true (by omega : 3 ≤ i.val + 1), decide_eq_true (by omega : 3 ≤ i.val + 2)]
        simp only [Bool.and_true]
        cases xor (Qp hk r (wOfY hr hk3 y)) (linP hk r u (wOfY hr hk3 y)) <;>
          cases wOfY hr hk3 y ⟨i.val + 1, by omega⟩ <;> cases wOfY hr hk3 y ⟨i.val + 2, by omega⟩ <;> rfl
      · rw [ix_eq_of_lt hk hk]; simp
      · rfl
    rw [hfun]
    split_ifs
    · exact isAffine_const false
    · exact isAffine_not (isAffine_wOfY hr hk3 _)
    · exact isAffine_xor (isAffine_wOfY hr hk3 _) (isAffine_wOfY hr hk3 _)
    · exact isAffine_not (isAffine_xor (isAffine_wOfY hr hk3 _) (isAffine_wOfY hr hk3 _))
    · exact isAffine_not (isAffine_wOfY hr hk3 _)
    · exact isAffine_const true
  have hr0 : ∀ y, row hk u (phiBlock hk hr hk3 u y) ⟨0, hk⟩ = false := fun y => by
    have h := (hrec y).2.2.2.1; have hx0 := (hrec y).2.1
    rw [h, hx0]
    cases u ⟨1, by omega⟩ <;> cases wOfY hr hk3 y ⟨0, hk⟩ <;> cases Q0 hr hk3 (wOfY hr hk3 y) <;> rfl
  have hrk : ∀ y, row hk u (phiBlock hk hr hk3 u y) ⟨k - 1, by omega⟩ = false := fun y => by
    have h := (hrec y).2.2.2.2.1; have hxk := (hrec y).2.2.1
    rw [h, hxk]
    cases u ⟨0, hk⟩ <;> cases xor (Qp hk r (wOfY hr hk3 y)) (linP hk r u (wOfY hr hk3 y)) <;>
      cases wOfY hr hk3 y ⟨k - 1, by omega⟩ <;> cases Qk hr hk3 (wOfY hr hk3 y) <;> rfl
  have hrp : ∀ y, decide (((neededSet r k).filter (fun i => row hk u (phiBlock hk hr hk3 u y) i = true)).card % 2 = 1) = false := fun y => by
    rw [(hrec y).2.2.2.2.2]
    cases Qp hk r (wOfY hr hk3 y) <;> cases linP hk r u (wOfY hr hk3 y) <;> rfl
  have hx0_f : ∀ y, phiBlock hk hr hk3 u y ⟨0, hk⟩ = xor (wOfY hr hk3 y ⟨0, hk⟩) (Q0 hr hk3 (wOfY hr hk3 y)) := fun y => by
    rw [(hrec y).2.1]
    cases u ⟨1, by omega⟩ <;> cases wOfY hr hk3 y ⟨0, hk⟩ <;> cases Q0 hr hk3 (wOfY hr hk3 y) <;> rfl
  have hxk_f : ∀ y, phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩ =
      xor (xor (linP hk r u (wOfY hr hk3 y)) (wOfY hr hk3 y ⟨k - 1, by omega⟩))
          (xor (Qp hk r (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y))) := fun y => by
    rw [(hrec y).2.2.1]
    cases u ⟨0, hk⟩ <;> cases Qp hk r (wOfY hr hk3 y) <;> cases linP hk r u (wOfY hr hk3 y) <;>
      cases wOfY hr hk3 y ⟨k - 1, by omega⟩ <;> cases Qk hr hk3 (wOfY hr hk3 y) <;> rfl
  have hx3_f : ∀ y, xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩) =
      xor (xor (zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩)
               (xor (u ⟨4, by omega⟩) (xor (u ⟨1, by omega⟩) (linP hk r u (wOfY hr hk3 y)))))
          (Qp hk r (wOfY hr hk3 y)) := fun y => by
    rw [hx0_f y]
    unfold phiBlock; dsimp only
    rw [ix_eq_of_lt hk (by omega : 3 + 1 < k)]
    let w0 := wOfY hr hk3 y
    let b := xor (Qp hk r w0) (linP hk r u w0)
    let z1 := xor (u ⟨1, by omega⟩) (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0))
    let z0 := xor (u ⟨0, hk⟩) (xor b (xor (w0 ⟨k - 1, by omega⟩) (Qk hr hk3 w0)))
    have hz4 : zOf (add w0 (fun i => b && decide (3 ≤ i.val))) z0 z1 ⟨4, by omega⟩ =
        xor (zOf w0 false false ⟨4, by omega⟩) (xor b z1) := by
      have h1 : add w0 (fun p : Fin k => b && decide (3 ≤ p.val)) =
          add (add w0 (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) := by
        funext p; unfold add; simp
      have h2 := zOf_xor (add w0 (fun p : Fin k => b && decide (3 ≤ p.val))) (fun _ => false) false false z0 z1 ⟨4, by omega⟩
      simp only [Bool.false_xor] at h2; rw [← h1] at h2
      have h3 := zOf_xor w0 (fun p : Fin k => b && decide (3 ≤ p.val)) false false false false ⟨4, by omega⟩
      simp only [Bool.false_xor] at h3
      have h4 : zOf (fun p : Fin k => b && decide (3 ≤ p.val)) false false ⟨4, by omega⟩ = b := by
        cases b
        · simp only [Bool.false_and]; unfold zOf; rw [zPair_zero]; simp
        · simp only [Bool.true_and]; unfold zOf; rw [zPair_mask3 4 (by omega)]; rfl
      have h5 : zOf (fun _ : Fin k => false) z0 z1 ⟨4, by omega⟩ = z1 := by
        unfold zOf; rw [zPair_zero]; simp
      rw [h2, h3, h4, h5, Bool.xor_assoc]
    change xor (xor (zOf (add w0 (fun i => b && decide (3 ≤ i.val))) z0 z1 ⟨4, by omega⟩) (u ⟨4, by omega⟩))
      (xor (w0 ⟨0, hk⟩) (Q0 hr hk3 w0)) = _
    rw [hz4]
    dsimp only [b, z1]
    cases zOf w0 false false ⟨4, by omega⟩ <;> cases u ⟨4, by omega⟩ <;> cases u ⟨1, by omega⟩ <;>
      cases linP hk r u w0 <;> cases Qp hk r w0 <;> cases w0 ⟨0, hk⟩ <;> cases Q0 hr hk3 w0 <;> rfl
  have hpol0 : ∀ a b, pol (fun y => phiBlock hk hr hk3 u y ⟨0, hk⟩) a b =
      pol (fun y => Q0 hr hk3 (wOfY hr hk3 y)) a b := fun a b => by
    have heq : (fun y => phiBlock hk hr hk3 u y ⟨0, hk⟩) =
        (fun y => xor (wOfY hr hk3 y ⟨0, hk⟩) (Q0 hr hk3 (wOfY hr hk3 y))) := funext hx0_f
    rw [heq, pol_xor, pol_affine (isAffine_wOfY hr hk3 _), Bool.false_xor]
  have hpolp : ∀ a b, pol (fun y => xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩)) a b =
      pol (fun y => Qp hk r (wOfY hr hk3 y)) a b := fun a b => by
    have heq : (fun y => xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩)) =
        (fun y => xor (xor (zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩)
                           (xor (u ⟨4, by omega⟩) (xor (u ⟨1, by omega⟩) (linP hk r u (wOfY hr hk3 y)))))
                      (Qp hk r (wOfY hr hk3 y))) := funext hx3_f
    have haff : IsAffine (fun y => xor (zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩)
        (xor (u ⟨4, by omega⟩) (xor (u ⟨1, by omega⟩) (linP hk r u (wOfY hr hk3 y))))) :=
      isAffine_xor (isAffine_zOf (wOfY hr hk3) (fun _ => false) (fun _ => false)
          (isAffine_wOfY hr hk3) (isAffine_const false) (isAffine_const false) _)
        (isAffine_xor (isAffine_const _) (isAffine_xor (isAffine_const _)
          (isAffine_linP hk u (wOfY hr hk3) (isAffine_wOfY hr hk3))))
    rw [heq, pol_xor, pol_affine haff, Bool.false_xor]
  have hpolk : ∀ a b, pol (fun y => xor (phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩)
        (xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩))) a b =
      pol (fun y => Qk hr hk3 (wOfY hr hk3 y)) a b := fun a b => by
    have heq : (fun y => xor (phiBlock hk hr hk3 u y ⟨k - 1, by omega⟩)
          (xor (phiBlock hk hr hk3 u y ⟨3, by omega⟩) (phiBlock hk hr hk3 u y ⟨0, hk⟩))) =
        (fun y => xor (xor (xor (linP hk r u (wOfY hr hk3 y)) (wOfY hr hk3 y ⟨k - 1, by omega⟩))
                           (xor (zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩)
                                (xor (u ⟨4, by omega⟩) (xor (u ⟨1, by omega⟩) (linP hk r u (wOfY hr hk3 y))))))
                      (Qk hr hk3 (wOfY hr hk3 y))) := by
      funext y; rw [hxk_f y, hx3_f y]
      cases linP hk r u (wOfY hr hk3 y) <;> cases wOfY hr hk3 y ⟨k - 1, by omega⟩ <;>
        cases Qp hk r (wOfY hr hk3 y) <;> cases Qk hr hk3 (wOfY hr hk3 y) <;>
        cases zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩ <;>
        cases u ⟨4, by omega⟩ <;> cases u ⟨1, by omega⟩ <;> rfl
    have haff : IsAffine (fun y => xor (xor (linP hk r u (wOfY hr hk3 y)) (wOfY hr hk3 y ⟨k - 1, by omega⟩))
        (xor (zOf (wOfY hr hk3 y) false false ⟨4, by omega⟩)
             (xor (u ⟨4, by omega⟩) (xor (u ⟨1, by omega⟩) (linP hk r u (wOfY hr hk3 y)))))) :=
      isAffine_xor (isAffine_xor (isAffine_linP hk u (wOfY hr hk3) (isAffine_wOfY hr hk3)) (isAffine_wOfY hr hk3 _))
        (isAffine_xor (isAffine_zOf (wOfY hr hk3) (fun _ => false) (fun _ => false)
            (isAffine_wOfY hr hk3) (isAffine_const false) (isAffine_const false) _)
          (isAffine_xor (isAffine_const _) (isAffine_xor (isAffine_const _)
            (isAffine_linP hk u (wOfY hr hk3) (isAffine_wOfY hr hk3)))))
    rw [heq, pol_xor, pol_affine haff, Bool.false_xor]
  exact ⟨hdiff_aff, hr0, hrk, hrp, hpol0, hpolp, hpolk⟩

def Bpair {N : Nat} (f g : (Fin N → Bool) → Bool) (a b : Fin N → Bool) : Bool :=
  xor (f a && g b) (f b && g a)

lemma pol_and_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => f y && g y) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_not_and_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => !(f y) && g y) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_and_not_lin {N : Nat} (f g : (Fin N → Bool) → Bool)
    (hf : ∀ a b, f (fun i => xor (a i) (b i)) = xor (f a) (f b)) (hf0 : f (fun _ => false) = false)
    (hg : ∀ a b, g (fun i => xor (a i) (b i)) = xor (g a) (g b)) (hg0 : g (fun _ => false) = false)
    (a b : Fin N → Bool) :
    pol (fun y => f y && !(g y)) a b = Bpair f g a b := by
  unfold pol Bpair; dsimp only
  rw [hf, hg, hf0, hg0]
  cases f a <;> cases f b <;> cases g a <;> cases g b <;> rfl

lemma pol_xorFin {N m : Nat} (F : Fin m → (Fin N → Bool) → Bool) (a b : Fin N → Bool) :
    pol (fun y => xorFin (fun i => F i y)) a b = xorFin (fun i => pol (F i) a b) := by
  induction m with
  | zero => exact pol_const false a b
  | succ m ih =>
    have heq : (fun y => xorFin (fun i : Fin (m + 1) => F i y)) =
        (fun y => xor (xorFin (fun i : Fin m => F i.castSucc y)) (F (Fin.last m) y)) := by
      funext y; exact xorFin_succ (fun i => F i y)
    rw [heq, pol_xor, ih (fun i => F i.castSucc), xorFin_succ]

def w1Bit (p : Nat) : Bool := decide (p = 0 ∨ p = 2 ∨ (4 ≤ p ∧ p % 3 ≠ 0))
def wk1Bit (m p : Nat) : Bool := decide (p = 0 ∨ p = 1 ∨ (3 ≤ p ∧ p < m - 1 ∧ p % 3 ≠ 2))
def dTermBit (r m j q : Nat) : Bool :=
  xor (decide (q = 3 * j + 4)) (if j + 1 = r - 2 then wk1Bit m q else decide (q = 3 * j + 6))
def BmBit (r m p q : Nat) : Bool :=
  xor (xor (decide (p = 2) && decide (q = 3)) (decide (q = 2) && decide (p = 3)))
    (xor (xor (wk1Bit m p && decide (q = 0)) (wk1Bit m q && decide (p = 0)))
      (xor (if 5 ≤ p ∧ p % 3 = 2 then dTermBit r m ((p - 5) / 3) q else false)
           (if 5 ≤ q ∧ q % 3 = 2 then dTermBit r m ((q - 5) / 3) p else false)))
def B0Bit (p q : Nat) : Bool :=
  xor (w1Bit p && decide (q = 1)) (w1Bit q && decide (p = 1))
def BkBit (p q : Nat) : Bool :=
  xor (decide (p = 0) && w1Bit q) (decide (q = 0) && w1Bit p)
def CBit (r m : Nat) (a0 b0 : Bool) (p q : Nat) : Bool :=
  xor (BmBit r m p q) (xor (a0 && B0Bit p q) (b0 && BkBit p q))

lemma CBit_symm (r m : Nat) (a0 b0 : Bool) (p q : Nat) :
    CBit r m a0 b0 p q = CBit r m a0 b0 q p := by
  unfold CBit BmBit B0Bit BkBit
  cases (decide (p = 2) && decide (q = 3)) <;> cases (decide (q = 2) && decide (p = 3)) <;>
    cases (wk1Bit m p && decide (q = 0)) <;> cases (wk1Bit m q && decide (p = 0)) <;>
    cases (if 5 ≤ p ∧ p % 3 = 2 then dTermBit r m ((p - 5) / 3) q else false) <;>
    cases (if 5 ≤ q ∧ q % 3 = 2 then dTermBit r m ((q - 5) / 3) p else false) <;>
    cases a0 <;> cases b0 <;>
    cases (w1Bit p && decide (q = 1)) <;> cases (w1Bit q && decide (p = 1)) <;>
    cases (decide (p = 0) && w1Bit q) <;> cases (decide (q = 0) && w1Bit p) <;> rfl

lemma wOfY_eVec_0 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨0, by omega⟩ = decide (p.val = 0) := by
  unfold wOfY eVec; simp [Fin.ext_iff, eq_comm]

lemma decide_eq_decide_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    decide P = decide Q := by
  by_cases hp : P
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

lemma wOfY_eVec_2 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨2, by omega⟩ = decide (p.val = 1) := by
  unfold wOfY eVec; simp [Fin.ext_iff, eq_comm]

lemma wOfY_eVec_mid {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3))
    (i : Nat) (hi4 : 4 ≤ i) (hil : i < k - 1) :
    wOfY hr hk3 (eVec p) ⟨i, by omega⟩ = decide (p.val = i - 2) := by
  unfold wOfY eVec; dsimp only
  rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), dite_pos hil]
  simp [Fin.ext_iff, eq_comm]

lemma wOfY_eVec_1 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨1, by omega⟩ = w1Bit p.val := by
  unfold wOfY w1Bit eVec; dsimp only
  rw [ite_neg (by omega), ite_pos rfl]
  have hsum : xorFin (fun j : Fin (r - 2) =>
      xor (decide (⟨3 * j.val + 4, by omega⟩ = p)) (decide (⟨3 * j.val + 5, by omega⟩ = p))) =
      decide (4 ≤ p.val ∧ p.val % 3 ≠ 0) := by
    by_cases hp : 4 ≤ p.val ∧ p.val % 3 ≠ 0
    · rw [decide_eq_true hp]
      let j0 : Fin (r - 2) := ⟨(p.val - 4) / 3, by omega⟩
      rw [xorFin_single' j0]
      · by_cases hm : p.val % 3 = 1
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          have h2 : (⟨3 * j0.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          simp [h1, h2]
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          have h2 : (⟨3 * j0.val + 5, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          simp [h1, h2]
      · intro j hj
        have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        have hne2 : (⟨3 * j.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        simp [hne1, hne2]
    · rw [decide_eq_false hp]
      apply xorFin_eq_false; intro j
      have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hne2 : (⟨3 * j.val + 5, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      simp [hne1, hne2]
  rw [hsum]
  have h0 : decide (⟨0, by omega⟩ = p) = decide (p.val = 0) := by simp [Fin.ext_iff, eq_comm]
  have h2 : decide (⟨2, by omega⟩ = p) = decide (p.val = 2) := by simp [Fin.ext_iff, eq_comm]
  rw [h0, h2]
  by_cases hp0 : p.val = 0
  · simp [hp0]
  · by_cases hp2 : p.val = 2
    · simp [hp2]
    · by_cases hpm : 4 ≤ p.val ∧ p.val % 3 ≠ 0
      · simp [hp0, hp2, hpm]
      · simp [hp0, hp2, hpm]

lemma wOfY_eVec_k1 {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p : Fin (k - 3)) :
    wOfY hr hk3 (eVec p) ⟨k - 1, by omega⟩ = wk1Bit (k - 3) p.val := by
  unfold wOfY wk1Bit eVec; dsimp only
  rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), dite_neg (by omega)]
  have hsum : xorFin (fun j : Fin (r - 2) =>
      xor (decide (⟨3 * j.val + 4, by omega⟩ = p)) (decide (⟨3 * j.val + 3, by omega⟩ = p))) =
      decide (3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2) := by
    by_cases hp : 3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2
    · rw [decide_eq_true hp]
      let j0 : Fin (r - 2) := ⟨(p.val - 3) / 3, by omega⟩
      rw [xorFin_single' j0]
      · by_cases hm : p.val % 3 = 0
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          have h2 : (⟨3 * j0.val + 3, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          simp [h1, h2]
        · have h1 : (⟨3 * j0.val + 4, by omega⟩ : Fin (k - 3)) = p := Fin.ext (by dsimp [j0]; omega)
          have h2 : (⟨3 * j0.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
            have := congrArg Fin.val h; dsimp [j0] at this; omega
          simp [h1, h2]
      · intro j hj
        have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        have hne2 : (⟨3 * j.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
          have hv := congrArg Fin.val h; dsimp only at hv
          exact hj (Fin.ext (by dsimp [j0]; omega))
        simp [hne1, hne2]
    · rw [decide_eq_false hp]
      apply xorFin_eq_false; intro j
      have hne1 : (⟨3 * j.val + 4, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      have hne2 : (⟨3 * j.val + 3, by omega⟩ : Fin (k - 3)) ≠ p := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      simp [hne1, hne2]
  rw [hsum]
  have h0 : decide (⟨0, by omega⟩ = p) = decide (p.val = 0) := by simp [Fin.ext_iff, eq_comm]
  have h1 : decide (⟨1, by omega⟩ = p) = decide (p.val = 1) := by simp [Fin.ext_iff, eq_comm]
  rw [h0, h1]
  by_cases hp0 : p.val = 0
  · simp [hp0]
  · by_cases hp1 : p.val = 1
    · simp [hp1]
    · by_cases hpm : 3 ≤ p.val ∧ p.val < k - 3 - 1 ∧ p.val % 3 ≠ 2
      · simp [hp0, hp1, hpm]
      · simp [hp0, hp1, hpm]

lemma pol_Q0_eVec {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => Q0 hr hk3 (wOfY hr hk3 y)) (eVec p) (eVec q) = B0Bit p.val q.val := by
  unfold Q0 B0Bit
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨1, by omega⟩) (fun y => wOfY hr hk3 y ⟨2, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  unfold Bpair; dsimp only
  rw [wOfY_eVec_1, wOfY_eVec_1, wOfY_eVec_2, wOfY_eVec_2]

lemma pol_Qk_eVec {r k : Nat} (hr : 2 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => Qk hr hk3 (wOfY hr hk3 y)) (eVec p) (eVec q) = BkBit p.val q.val := by
  unfold Qk BkBit
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨0, by omega⟩) (fun y => wOfY hr hk3 y ⟨1, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  unfold Bpair; dsimp only
  rw [wOfY_eVec_0, wOfY_eVec_0, wOfY_eVec_1, wOfY_eVec_1]

lemma pol_QpMid_eVec {r k : Nat} (hk : 0 < k) (hr3 : 3 ≤ r) (hk3 : k = 3 * r) (p q : Fin (k - 3)) :
    pol (fun y => QpMid hk (by omega) hk3 (wOfY (by omega) hk3 y)) (eVec p) (eVec q) =
      BmBit r (k - 3) p.val q.val := by
  have hr : 2 ≤ r := by omega
  unfold QpMid BmBit
  rw [pol_xor, pol_xor, pol_xor, pol_xorFin]
  rw [pol_affine (isAffine_wOfY hr hk3 _), Bool.false_xor]
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨4, by omega⟩) (fun y => wOfY hr hk3 y ⟨5, by omega⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  rw [pol_not_and_lin (fun y => wOfY hr hk3 y ⟨k - 1, by omega⟩) (fun y => wOfY hr hk3 y ⟨0, hk⟩)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
    (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)]
  have h1 : Bpair (fun y => wOfY hr hk3 y ⟨4, by omega⟩) (fun y => wOfY hr hk3 y ⟨5, by omega⟩) (eVec p) (eVec q) =
      xor (decide (p.val = 2) && decide (q.val = 3)) (decide (q.val = 2) && decide (p.val = 3)) := by
    unfold Bpair; dsimp only
    rw [wOfY_eVec_mid hr hk3 p 4 (by omega) (by omega), wOfY_eVec_mid hr hk3 q 4 (by omega) (by omega),
      wOfY_eVec_mid hr hk3 p 5 (by omega) (by omega), wOfY_eVec_mid hr hk3 q 5 (by omega) (by omega)]
  have h2 : Bpair (fun y => wOfY hr hk3 y ⟨k - 1, by omega⟩) (fun y => wOfY hr hk3 y ⟨0, hk⟩) (eVec p) (eVec q) =
      xor (wk1Bit (k - 3) p.val && decide (q.val = 0)) (wk1Bit (k - 3) q.val && decide (p.val = 0)) := by
    unfold Bpair; dsimp only
    rw [wOfY_eVec_k1, wOfY_eVec_k1, wOfY_eVec_0, wOfY_eVec_0]
  have h3 : xorFin (fun j : Fin (r - 2) =>
      pol (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩ &&
                          !(xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)))
                        (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)) (eVec p) (eVec q)) =
      xor (if 5 ≤ p.val ∧ p.val % 3 = 2 then dTermBit r (k - 3) ((p.val - 5) / 3) q.val else false)
          (if 5 ≤ q.val ∧ q.val % 3 = 2 then dTermBit r (k - 3) ((q.val - 5) / 3) p.val else false) := by
    have hstep : ∀ j : Fin (r - 2),
        pol (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩ &&
                            !(xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)))
                          (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩)) (eVec p) (eVec q) =
        xor (decide (p.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val q.val)
            (decide (q.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val p.val) := by
      intro j
      rw [pol_xor, pol_affine (isAffine_wOfY hr hk3 _), Bool.xor_false]
      rw [pol_and_not_lin (fun y => wOfY hr hk3 y ⟨3 * (j.val + 2) + 1, by omega⟩)
        (fun y => xor (wOfY hr hk3 y ⟨3 * (j.val + 2), by omega⟩) (wOfY hr hk3 y ⟨3 * (j.val + 2) + 2, by omega⟩))
        (fun a b => wOfY_xor hr hk3 a b _) (wOfY_zero hr hk3 _)
        (fun a b => by rw [wOfY_xor, wOfY_xor]; cases wOfY hr hk3 a _ <;> cases wOfY hr hk3 b _ <;> cases wOfY hr hk3 a _ <;> cases wOfY hr hk3 b _ <;> rfl)
        (by rw [wOfY_zero, wOfY_zero]; rfl)]
      unfold Bpair dTermBit; dsimp only
      have ha : ∀ x : Fin (k - 3), wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2) + 1, by omega⟩ = decide (x.val = 3 * j.val + 5) := fun x => by
        rw [wOfY_eVec_mid hr hk3 x (3 * (j.val + 2) + 1) (by omega) (by omega)]
        exact congrArg (fun n => decide (x.val = n)) (by omega)
      have hb : ∀ x : Fin (k - 3), xor (wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2), by omega⟩)
          (wOfY hr hk3 (eVec x) ⟨3 * (j.val + 2) + 2, by omega⟩) =
          xor (decide (x.val = 3 * j.val + 4))
              (if j.val + 1 = r - 2 then wk1Bit (k - 3) x.val else decide (x.val = 3 * j.val + 6)) := fun x => by
        congr 1
        · rw [wOfY_eVec_mid hr hk3 x (3 * (j.val + 2)) (by omega) (by omega)]
          exact congrArg (fun n => decide (x.val = n)) (by omega)
        · by_cases hjl : j.val + 1 = r - 2
          · rw [ite_pos hjl]
            have heq : (⟨3 * (j.val + 2) + 2, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [heq, wOfY_eVec_k1]
          · rw [ite_neg hjl, wOfY_eVec_mid hr hk3 x (3 * (j.val + 2) + 2) (by omega) (by omega)]
            exact congrArg (fun n => decide (x.val = n)) (by omega)
      rw [ha p, ha q, hb p, hb q]
    rw [xorFin_congr _ _ hstep, xorFin_xor]
    have hside : ∀ x y' : Fin (k - 3),
        xorFin (fun j : Fin (r - 2) => decide (x.val = 3 * j.val + 5) && dTermBit r (k - 3) j.val y'.val) =
        if 5 ≤ x.val ∧ x.val % 3 = 2 then dTermBit r (k - 3) ((x.val - 5) / 3) y'.val else false := by
      intro x y'
      by_cases hx : 5 ≤ x.val ∧ x.val % 3 = 2
      · rw [ite_pos hx]
        let j0 : Fin (r - 2) := ⟨(x.val - 5) / 3, by omega⟩
        rw [xorFin_single' j0]
        · have heq : x.val = 3 * j0.val + 5 := by dsimp [j0]; omega
          rw [decide_eq_true heq, Bool.true_and]
        · intro j hj
          have hne : x.val ≠ 3 * j.val + 5 := fun h => hj (Fin.ext (by dsimp [j0]; omega))
          rw [decide_eq_false hne, Bool.false_and]
      · rw [ite_neg hx]
        apply xorFin_eq_false; intro j
        have hne : x.val ≠ 3 * j.val + 5 := by omega
        rw [decide_eq_false hne, Bool.false_and]
    rw [hside p q, hside q p]
  rw [h1, h2, h3]

lemma inv_CBit_r3 : ∀ (a0 b0 : Bool) (c : Fin 4 → Bool),
    (∀ q : Fin 4, xorFin (fun i : Fin 4 => c i && CBit 3 6 a0 b0 i.val q.val) = false) →
    ∀ i : Fin 4, c i = false := by
  decide

def coreIdx (p : Nat) : Nat :=
  if p = 0 then 2
  else if p = 1 then 3
  else 3 * (p / 2 + 1) - 2 + p % 2

def partner (p : Nat) : Nat :=
  if p % 2 = 0 then p + 1 else p - 1

def extraIdx (m : Nat) (a0 b0 : Bool) (e : Fin 4) : Nat :=
  match e.val with
  | 0 => 0
  | 1 => 1
  | 2 => if a0 = false ∧ b0 = false then m - 2 else m - 3
  | _ => if a0 = false then m - 1 else m - 2

def basisIdx4 (r m : Nat) (a0 b0 : Bool) (i : Fin (2 * r)) : Nat :=
  if h : i.val < 2 * r - 4 then coreIdx i.val
  else extraIdx m a0 b0 ⟨i.val - (2 * r - 4), by omega⟩

lemma coreIdx_lt {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (p : Nat) (hp : p < 2 * r - 4) :
    coreIdx p < m := by
  unfold coreIdx; split_ifs <;> omega

lemma coreIdx_mod {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (p : Nat) (hp : p < 2 * r - 4) :
    2 ≤ coreIdx p ∧ coreIdx p ≤ m - 4 ∧
    (p = 0 → coreIdx p = 2) ∧ (p = 1 → coreIdx p = 3) ∧
    (2 ≤ p → 4 ≤ coreIdx p ∧ coreIdx p % 3 = 1 + p % 2) := by
  unfold coreIdx; split_ifs <;> refine ⟨by omega, by omega, by omega, by omega, fun _ => ⟨by omega, by omega⟩⟩

lemma CBit_core_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p q : Nat) (hp : p < 2 * r - 4) (hq : q < 2 * r - 4) :
    CBit r m a0 b0 (coreIdx p) (coreIdx q) = decide (p = partner q) := by
  have hcp := coreIdx_mod hr4 hm p hp
  have hcq := coreIdx_mod hr4 hm q hq
  unfold CBit BmBit B0Bit BkBit dTermBit partner
  have hnp0 : coreIdx p ≠ 0 := by omega
  have hnp1 : coreIdx p ≠ 1 := by omega
  have hnq0 : coreIdx q ≠ 0 := by omega
  have hnq1 : coreIdx q ≠ 1 := by omega
  simp only [hnp0, hnp1, hnq0, hnq1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  by_cases hp0 : p = 0
  · subst hp0
    have hcp2 : coreIdx 0 = 2 := rfl
    rw [hcp2]
    have hnq2 : ¬(5 ≤ 2 ∧ 2 % 3 = 2) := by omega
    rw [ite_neg hnq2, Bool.false_xor]
    by_cases hq1 : q = 1
    · subst hq1; simp [coreIdx]
    · have hcq3 : coreIdx q ≠ 3 := by unfold coreIdx at *; split_ifs at * <;> omega
      have htermq : (if 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 then
          xor (decide (2 = 3 * ((coreIdx q - 5) / 3) + 4))
            (if (coreIdx q - 5) / 3 + 1 = r - 2 then wk1Bit m 2 else decide (2 = 3 * ((coreIdx q - 5) / 3) + 6))
          else false) = false := by
        (split_ifs with h1 h2 <;> simp); omega
      rw [htermq]; simp only [hcq3, decide_false, show decide (2 = 3) = false from rfl, Bool.and_false, Bool.xor_false]
      apply Eq.symm; apply decide_eq_false; intro h
      by_cases hqe : q % 2 = 0
      · rw [ite_pos hqe] at h; omega
      · rw [ite_neg hqe] at h; omega
  · by_cases hp1 : p = 1
    · subst hp1
      have hcp3 : coreIdx 1 = 3 := rfl
      rw [hcp3]
      have hnq3 : ¬(5 ≤ 3 ∧ 3 % 3 = 2) := by omega
      rw [ite_neg hnq3, Bool.false_xor]
      by_cases hq0 : q = 0
      · subst hq0; simp [coreIdx]
      · have hcq2 : coreIdx q ≠ 2 := by unfold coreIdx at *; split_ifs at * <;> omega
        have htermq : (if 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 then
            xor (decide (3 = 3 * ((coreIdx q - 5) / 3) + 4))
              (if (coreIdx q - 5) / 3 + 1 = r - 2 then wk1Bit m 3 else decide (3 = 3 * ((coreIdx q - 5) / 3) + 6))
            else false) = false := by
          (split_ifs with h1 h2 <;> simp); omega
        rw [htermq]; simp only [hcq2, decide_false, Bool.false_and, Bool.xor_false]
        apply Eq.symm; apply decide_eq_false; split_ifs <;> omega
    · by_cases hq0 : q = 0
      · subst hq0
        have hcq2 : coreIdx 0 = 2 := rfl
        rw [hcq2]
        have hcp3 : coreIdx p ≠ 3 := by unfold coreIdx at *; split_ifs at * <;> omega
        have htermp : (if 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 then
            xor (decide (2 = 3 * ((coreIdx p - 5) / 3) + 4))
              (if (coreIdx p - 5) / 3 + 1 = r - 2 then wk1Bit m 2 else decide (2 = 3 * ((coreIdx p - 5) / 3) + 6))
            else false) = false := by
          (split_ifs with h1 h2 <;> simp); omega
        rw [htermp]; simp [hcp3, hp1]
      · by_cases hq1 : q = 1
        · subst hq1
          have hcq3 : coreIdx 1 = 3 := rfl
          rw [hcq3]
          have hcp2 : coreIdx p ≠ 2 := by unfold coreIdx at *; split_ifs at * <;> omega
          have htermp : (if 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 then
              xor (decide (3 = 3 * ((coreIdx p - 5) / 3) + 4))
                (if (coreIdx p - 5) / 3 + 1 = r - 2 then wk1Bit m 3 else decide (3 = 3 * ((coreIdx p - 5) / 3) + 6))
              else false) = false := by
            (split_ifs with h1 h2 <;> simp); omega
          rw [htermp]; simp [hcp2, hp0]
        ·
          have hp2 : 2 ≤ p := by omega
          have hq2 : 2 ≤ q := by omega
          have hcp_ne2 : coreIdx p ≠ 2 := by omega
          have hcp_ne3 : coreIdx p ≠ 3 := by omega
          have hcq_ne2 : coreIdx q ≠ 2 := by omega
          have hcq_ne3 : coreIdx q ≠ 3 := by omega
          simp only [hcp_ne2, hcp_ne3, hcq_ne2, hcq_ne3, decide_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
          have hcp_ge : 4 ≤ coreIdx p ∧ coreIdx p % 3 = 1 + p % 2 := hcp.2.2.2.2 hp2
          have hcq_ge : 4 ≤ coreIdx q ∧ coreIdx q % 3 = 1 + q % 2 := hcq.2.2.2.2 hq2
          have hcp_lt : (coreIdx p - 5) / 3 + 1 < r - 2 := by unfold coreIdx at *; split_ifs at *; omega
          have hcq_lt : (coreIdx q - 5) / 3 + 1 < r - 2 := by unfold coreIdx at *; split_ifs at *; omega
          by_cases hpe : p % 2 = 0 <;> by_cases hqe : q % 2 = 0
          · have hnp : ¬(5 ≤ coreIdx p ∧ coreIdx p % 3 = 2) := by omega
            have hnq : ¬(5 ≤ coreIdx q ∧ coreIdx q % 3 = 2) := by omega
            rw [ite_neg hnp, ite_neg hnq]
            apply Eq.symm; apply decide_eq_false; split_ifs; omega
          · have hnp : ¬(5 ≤ coreIdx p ∧ coreIdx p % 3 = 2) := by omega
            have hq5 : 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 := by omega
            rw [ite_neg hnp, ite_pos hq5, Bool.false_xor, ite_neg (by omega)]
            have hne6 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 6 := by omega
            rw [decide_eq_false hne6, Bool.xor_false, ite_neg hqe]
            exact decide_eq_decide_of_iff (by unfold coreIdx at *; split_ifs at *; omega)
          · have hp5 : 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 := by omega
            have hnq : ¬(5 ≤ coreIdx q ∧ coreIdx q % 3 = 2) := by omega
            rw [ite_pos hp5, ite_neg hnq, Bool.xor_false, ite_neg (by omega)]
            have hne6 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
            rw [decide_eq_false hne6, Bool.xor_false, ite_pos hqe]
            exact decide_eq_decide_of_iff (by unfold coreIdx at *; split_ifs at *; omega)
          · have hp5 : 5 ≤ coreIdx p ∧ coreIdx p % 3 = 2 := by omega
            have hq5 : 5 ≤ coreIdx q ∧ coreIdx q % 3 = 2 := by omega
            rw [ite_pos hp5, ite_pos hq5, ite_neg (by omega), ite_neg (by omega)]
            have h1 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
            have h2 : coreIdx q ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
            have h3 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 4 := by omega
            have h4 : coreIdx p ≠ 3 * ((coreIdx q - 5) / 3) + 6 := by omega
            rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3, decide_eq_false h4]
            apply Eq.symm; apply decide_eq_false; split_ifs; omega

lemma CBit_m2_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m a0 b0 (m - 2) (coreIdx p) = false := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have h0 : m - 2 ≠ 0 := by omega
  have h1 : m - 2 ≠ 1 := by omega
  have h2 : m - 2 ≠ 2 := by omega
  have h3 : m - 2 ≠ 3 := by omega
  have h5 : ¬(5 ≤ m - 2 ∧ (m - 2) % 3 = 2) := by omega
  have hp0 : coreIdx p ≠ 0 := by omega
  have hp1 : coreIdx p ≠ 1 := by omega
  simp only [h0, h1, h2, h3, hp0, hp1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg h5, Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : m - 2 ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    have hb : m - 2 ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
    simp [ha, hb]
  · rfl

lemma CBit_one_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m false b0 1 (coreIdx p) = false := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have hp0 : coreIdx p ≠ 0 := by omega
  simp only [hp0, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg (by omega : ¬(5 ≤ 1 ∧ 1 % 3 = 2)), Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : (1 : Nat) ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    have hb : (1 : Nat) ≠ 3 * ((coreIdx p - 5) / 3) + 6 := by omega
    rw [decide_eq_false ha, decide_eq_false hb]; simp
  · simp

lemma CBit_m3_core {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (p : Nat) (hp : p < 2 * r - 4) :
    CBit r m a0 b0 (m - 3) (coreIdx p) = decide (p = 2 * r - 5) := by
  have hcp := coreIdx_mod hr4 hm p hp
  unfold CBit BmBit B0Bit BkBit dTermBit
  have h0 : m - 3 ≠ 0 := by omega
  have h1 : m - 3 ≠ 1 := by omega
  have h2 : m - 3 ≠ 2 := by omega
  have h3 : m - 3 ≠ 3 := by omega
  have h5 : ¬(5 ≤ m - 3 ∧ (m - 3) % 3 = 2) := by omega
  have hp0 : coreIdx p ≠ 0 := by omega
  have hp1 : coreIdx p ≠ 1 := by omega
  simp only [h0, h1, h2, h3, hp0, hp1, decide_false, Bool.and_false, Bool.false_and, Bool.xor_false, Bool.false_xor]
  rw [ite_neg h5, Bool.false_xor]
  split_ifs with hq5 hql
  · exfalso; unfold coreIdx at *; split_ifs at * <;> omega
  · have ha : m - 3 ≠ 3 * ((coreIdx p - 5) / 3) + 4 := by omega
    rw [decide_eq_false ha, Bool.false_xor]
    have hcp_val : coreIdx p = 3 * (p / 2) + 2 := by
      unfold coreIdx at *; split_ifs at * <;> omega
    have hp_odd : p % 2 = 1 := by
      unfold coreIdx at *; split_ifs at * <;> omega
    rw [hcp_val]
    exact decide_eq_decide_of_iff (by omega)
  · apply Eq.symm; apply decide_eq_false
    intro heq; subst heq; unfold coreIdx at hq5; split_ifs at hq5 <;> omega

lemma CBit_last_even {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool) :
    CBit r m a0 b0 0 (coreIdx (2 * r - 6)) = !b0 ∧
    CBit r m a0 b0 1 (coreIdx (2 * r - 6)) = a0 ∧
    CBit r m a0 b0 (m - 1) (coreIdx (2 * r - 6)) = true := by
  have hce : coreIdx (2 * r - 6) = m - 5 := by
    unfold coreIdx; rw [ite_neg (by omega), ite_neg (by omega)]; omega
  rw [hce]
  have hw1 : w1Bit (m - 5) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hwk1 : wk1Bit m (m - 5) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hnot5 : ¬(5 ≤ m - 5 ∧ (m - 5) % 3 = 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold CBit BmBit B0Bit BkBit; rw [hw1, hwk1, ite_neg hnot5]
    have h2 : m - 5 ≠ 2 := by omega
    have h3 : m - 5 ≠ 3 := by omega
    have h0 : m - 5 ≠ 0 := by omega
    have h1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1, ite_neg hnot5]
    have h2 : m - 5 ≠ 2 := by omega
    have h3 : m - 5 ≠ 3 := by omega
    have h0 : m - 5 ≠ 0 := by omega
    have h1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot5]
    have hm1_5 : 5 ≤ m - 1 ∧ (m - 1) % 3 = 2 := by omega
    rw [ite_pos hm1_5]
    have hdiv : (m - 1 - 5) / 3 + 1 = r - 2 := by omega
    rw [ite_pos hdiv, hwk1]
    have hne : m - 5 ≠ 3 * ((m - 1 - 5) / 3) + 4 := by omega
    have h0 : m - 1 ≠ 0 := by omega
    have h1 : m - 1 ≠ 1 := by omega
    have h2 : m - 1 ≠ 2 := by omega
    have h3 : m - 1 ≠ 3 := by omega
    have hp0 : m - 5 ≠ 0 := by omega
    have hp1 : m - 5 ≠ 1 := by omega
    simp [h0, h1, h2, h3, hp0, hp1, hne]

lemma CBit_extra_vals {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool) :
    CBit r m a0 b0 1 (m - 2) = a0 ∧
    CBit r m a0 b0 1 (m - 1) = !a0 ∧
    CBit r m a0 b0 (m - 2) 0 = !b0 ∧
    CBit r m a0 b0 (m - 2) (m - 1) = false ∧
    CBit r m a0 b0 1 (m - 3) = false ∧
    CBit r m a0 b0 (m - 3) 0 = true ∧
    CBit r m a0 b0 (m - 3) (m - 1) = true ∧
    CBit r m a0 b0 (m - 2) (m - 3) = false := by
  have hw1_m2 : w1Bit (m - 2) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hw1_m3 : w1Bit (m - 3) = false := by unfold w1Bit; apply decide_eq_false; omega
  have hw1_m1 : w1Bit (m - 1) = true := by unfold w1Bit; apply decide_eq_true; right; right; omega
  have hwk1_1 : wk1Bit m 1 = true := by unfold wk1Bit; apply decide_eq_true; right; left; rfl
  have hwk1_m2 : wk1Bit m (m - 2) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hwk1_m3 : wk1Bit m (m - 3) = true := by unfold wk1Bit; apply decide_eq_true; right; right; omega
  have hnot_m2 : ¬(5 ≤ m - 2 ∧ (m - 2) % 3 = 2) := by omega
  have hnot_m3 : ¬(5 ≤ m - 3 ∧ (m - 3) % 3 = 2) := by omega
  have hyes_m1 : 5 ≤ m - 1 ∧ (m - 1) % 3 = 2 := by omega
  have hdiv_m1 : (m - 1 - 5) / 3 + 1 = r - 2 := by omega
  have h3d4 : 3 * ((m - 1 - 5) / 3) + 4 = m - 2 := by omega
  have hm2_0 : m - 2 ≠ 0 := by omega
  have hm2_1 : m - 2 ≠ 1 := by omega
  have hm2_2 : m - 2 ≠ 2 := by omega
  have hm2_3 : m - 2 ≠ 3 := by omega
  have hm3_0 : m - 3 ≠ 0 := by omega
  have hm3_1 : m - 3 ≠ 1 := by omega
  have hm3_2 : m - 3 ≠ 2 := by omega
  have hm3_3 : m - 3 ≠ 3 := by omega
  have hm1_0 : m - 1 ≠ 0 := by omega
  have hm1_1 : m - 1 ≠ 1 := by omega
  have hm1_2 : m - 1 ≠ 2 := by omega
  have hm1_3 : m - 1 ≠ 3 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m2, ite_neg hnot_m2]
    simp [hm2_0, hm2_1, hm2_2, hm2_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [hw1_m1, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_1, h3d4]
    have h1n : (1 : Nat) ≠ m - 2 := by omega
    simp [hm1_0, hm1_1, hm1_2, hm1_3, h1n]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m2, hwk1_m2, ite_neg hnot_m2]
    simp [hm2_0, hm2_1, hm2_2, hm2_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot_m2, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_m2, h3d4]
    simp [hm2_0, hm2_1, hm2_2, hm2_3, hm1_0, hm1_1, hm1_2, hm1_3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m3, ite_neg hnot_m3]
    simp [hm3_0, hm3_1, hm3_2, hm3_3]
  · unfold CBit BmBit B0Bit BkBit; rw [hw1_m3, hwk1_m3, ite_neg hnot_m3]
    simp [hm3_0, hm3_1, hm3_2, hm3_3]
  · unfold CBit BmBit B0Bit BkBit dTermBit; rw [ite_neg hnot_m3, ite_pos hyes_m1, ite_pos hdiv_m1, hwk1_m3, h3d4]
    have hne : m - 3 ≠ m - 2 := by omega
    simp [hm3_0, hm3_1, hm3_2, hm3_3, hm1_0, hm1_1, hm1_2, hm1_3, hne]
  · unfold CBit BmBit B0Bit BkBit; rw [ite_neg hnot_m2, ite_neg hnot_m3]
    simp [hm2_0, hm2_1, hm2_2, hm2_3, hm3_0, hm3_1, hm3_2, hm3_3]

lemma inv_CBit_r4 {r m : Nat} (hr4 : 4 ≤ r) (hm : m = 3 * r - 3) (a0 b0 : Bool)
    (c : Fin (2 * r) → Bool)
    (hzero : ∀ q : Fin (2 * r),
      xorFin (fun i : Fin (2 * r) => c i && CBit r m a0 b0 (basisIdx4 r m a0 b0 i) (basisIdx4 r m a0 b0 q)) = false) :
    ∀ i : Fin (2 * r), c i = false := by
  let L := 2 * r - 4
  have h2r : 2 * r = L + 4 := by omega
  let cc : Fin L → Bool := fun p => c ⟨p.val, by omega⟩
  let ce : Fin 4 → Bool := fun e => c ⟨L + e.val, by omega⟩
  have hsplit : ∀ (q : Fin (2 * r)),
      xor (xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (basisIdx4 r m a0 b0 q)))
          (xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (basisIdx4 r m a0 b0 q))) = false := by
    intro q
    have hq := hzero q
    rw [xorFin_cast h2r _ (fun i : Fin (L + 4) => c ⟨i.val, by omega⟩ &&
        CBit r m a0 b0 (basisIdx4 r m a0 b0 ⟨i.val, by omega⟩) (basisIdx4 r m a0 b0 q)) (fun _ _ _ => rfl),
      xorFin_add_split] at hq
    rw [← hq]; congr 1
    · apply xorFin_congr; intro p
      have hbp : basisIdx4 r m a0 b0 ⟨p.val, by omega⟩ = coreIdx p.val := by
        unfold basisIdx4; dsimp only; rw [dite_pos p.isLt]
      rw [hbp]
    · apply xorFin_congr; intro e
      have hbe : basisIdx4 r m a0 b0 ⟨L + e.val, by omega⟩ = extraIdx m a0 b0 e := by
        unfold basisIdx4; dsimp only; rw [dite_neg (by omega)]
        exact congrArg (extraIdx m a0 b0) (Fin.ext (by dsimp only; omega))
      rw [hbe]
  have hpart_lt : ∀ p : Fin L, partner p.val < L := fun p => by unfold partner; split_ifs <;> omega
  have hpart_inv : ∀ p : Fin L, partner (partner p.val) = p.val := fun p => by unfold partner; split_ifs <;> omega

  have hcc : ∀ p : Fin L,
      cc p = xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val))) := by
    intro p
    let q : Fin (2 * r) := ⟨partner p.val, by have := hpart_lt p; omega⟩
    have hq := hsplit q
    have hbq : basisIdx4 r m a0 b0 q = coreIdx (partner p.val) := by
      unfold basisIdx4; dsimp only [q]; rw [dite_pos (hpart_lt p)]
    rw [hbq] at hq
    have hcore : xorFin (fun i : Fin L => cc i && CBit r m a0 b0 (coreIdx i.val) (coreIdx (partner p.val))) = cc p := by
      rw [xorFin_single' p]
      · rw [CBit_core_core hr4 hm a0 b0 p.val (partner p.val) p.isLt (hpart_lt p), hpart_inv p]; simp
      · intro i hi
        rw [CBit_core_core hr4 hm a0 b0 i.val (partner p.val) i.isLt (hpart_lt p), hpart_inv p]
        have hne : i.val ≠ p.val := fun h => hi (Fin.ext h)
        simp [hne]
    rw [hcore] at hq
    cases ha : cc p <;> cases hb : xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val))) <;>
      rw [ha, hb] at hq <;> simp at hq ⊢

  let S : Fin 4 → Fin 4 → Bool := fun e j =>
    xor (CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j))
        (xorFin (fun p : Fin L =>
          CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
          CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)))
  have hschur : ∀ j : Fin 4, xorFin (fun e : Fin 4 => ce e && S e j) = false := by
    intro j
    let q : Fin (2 * r) := ⟨L + j.val, by omega⟩
    have hq := hsplit q
    have hbq : basisIdx4 r m a0 b0 q = extraIdx m a0 b0 j := by
      unfold basisIdx4; dsimp only [q]; rw [dite_neg (by omega)]
      have hj_eq : (⟨L + j.val - L, by omega⟩ : Fin 4) = j := Fin.ext (by dsimp only; omega)
      rw [hj_eq]
    rw [hbq] at hq
    have hsub : xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) =
        xorFin (fun e : Fin 4 => ce e &&
          xorFin (fun p : Fin L =>
            CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
            CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j))) := by
      have h1 : xorFin (fun p : Fin L => cc p && CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) =
          xorFin (fun p : Fin L => xorFin (fun e : Fin 4 =>
            ce e && (CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
                     CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)))) := by
        apply xorFin_congr; intro p; rw [hcc p, ← xorFin_and_right]
        apply xorFin_congr; intro e; simp [Bool.and_assoc]
      rw [h1, xorFin_swap]
      apply xorFin_congr; intro e; rw [xorFin_and_left]
    rw [hsub, ← xorFin_xor] at hq
    rw [← hq]; apply xorFin_congr; intro e; unfold S
    cases ce e <;> cases CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) <;>
      cases xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) <;> rfl
  have hfr4 : ∀ g : Fin 4 → Bool,
      xorFin g = xor (g ⟨0, by omega⟩) (xor (g ⟨1, by omega⟩) (xor (g ⟨2, by omega⟩) (g ⟨3, by omega⟩))) := by
    intro g; unfold xorFin
    have : List.finRange 4 = [0, 1, 2, 3] := rfl
    rw [this]; simp

  have hS_zeroR : ∀ (e j : Fin 4),
      (∀ p : Fin L, CBit r m a0 b0 (extraIdx m a0 b0 j) (coreIdx p.val) = false) →
      S e j = CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) := by
    intro e j hz; unfold S
    have h0 : xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) = false :=
      xorFin_eq_false _ (fun p => by rw [CBit_symm r m a0 b0 (coreIdx p.val), hz p, Bool.and_false])
    rw [h0, Bool.xor_false]
  have hS_zeroL : ∀ (e j : Fin 4),
      (∀ p : Fin L, CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx p.val) = false) →
      S e j = CBit r m a0 b0 (extraIdx m a0 b0 e) (extraIdx m a0 b0 j) := by
    intro e j hz; unfold S
    have h0 : xorFin (fun p : Fin L => CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner p.val)) &&
        CBit r m a0 b0 (coreIdx p.val) (extraIdx m a0 b0 j)) = false :=
      xorFin_eq_false _ (fun p => by rw [hz ⟨partner p.val, hpart_lt p⟩, Bool.false_and])
    rw [h0, Bool.xor_false]
  have hS_m3R : ∀ (e j : Fin 4), extraIdx m a0 b0 j = m - 3 →
      S e j = xor (CBit r m a0 b0 (extraIdx m a0 b0 e) (m - 3))
                  (CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (2 * r - 6))) := by
    intro e j hj; unfold S; rw [hj]; congr 1
    let p0 : Fin L := ⟨2 * r - 5, by omega⟩
    rw [xorFin_single' p0]
    · rw [CBit_symm r m a0 b0 (coreIdx p0.val), CBit_m3_core hr4 hm a0 b0 p0.val p0.isLt]
      have hp0_eq : p0.val = 2 * r - 5 := rfl
      have hpart0 : partner p0.val = 2 * r - 6 := by unfold partner; dsimp [p0]; rw [ite_neg (by omega)]; omega
      rw [hp0_eq, hpart0]; simp
    · intro p hp
      rw [CBit_symm r m a0 b0 (coreIdx p.val), CBit_m3_core hr4 hm a0 b0 p.val p.isLt]
      have hne : p.val ≠ 2 * r - 5 := fun h => hp (Fin.ext h)
      simp [hne]
  have hS_m3L : ∀ (e j : Fin 4), extraIdx m a0 b0 e = m - 3 →
      S e j = xor (CBit r m a0 b0 (m - 3) (extraIdx m a0 b0 j))
                  (CBit r m a0 b0 (coreIdx (2 * r - 6)) (extraIdx m a0 b0 j)) := by
    intro e j he; unfold S; rw [he]; congr 1
    let p0 : Fin L := ⟨2 * r - 6, by omega⟩
    rw [xorFin_single' p0]
    · have hpart0 : partner p0.val = 2 * r - 5 := by unfold partner; dsimp [p0]; rw [ite_pos (by omega)]; omega
      rw [hpart0, CBit_m3_core hr4 hm a0 b0 (2 * r - 5) (by omega)]; simp [p0]
    · intro p hp
      rw [CBit_m3_core hr4 hm a0 b0 (partner p.val) (hpart_lt p)]
      have hne : partner p.val ≠ 2 * r - 5 := fun h => hp (Fin.ext (by
        have := hpart_inv p; rw [h] at this; unfold partner at this
        rw [ite_neg (by omega)] at this; dsimp [p0]; omega))
      simp [hne]
  have hself : ∀ x, CBit r m a0 b0 x x = false := fun x => by
    unfold CBit BmBit B0Bit BkBit
    cases (decide (x = 2) && decide (x = 3)) <;> cases (wk1Bit m x && decide (x = 0)) <;>
      cases (if 5 ≤ x ∧ x % 3 = 2 then dTermBit r m ((x - 5) / 3) x else false) <;>
      cases a0 <;> cases b0 <;> cases (w1Bit x && decide (x = 1)) <;>
      cases (decide (x = 0) && w1Bit x) <;> rfl
  have hex := CBit_extra_vals hr4 hm a0 b0
  have hle := CBit_last_even hr4 hm a0 b0
  have hm2z : ∀ p : Fin L, CBit r m a0 b0 (m - 2) (coreIdx p.val) = false := fun p => CBit_m2_core hr4 hm a0 b0 p.val p.isLt

  have hce0 : ∀ e : Fin 4, ce e = false := by
    have eq0 := hschur ⟨0, by omega⟩; rw [hfr4] at eq0
    have eq1 := hschur ⟨1, by omega⟩; rw [hfr4] at eq1
    have eq2 := hschur ⟨2, by omega⟩; rw [hfr4] at eq2
    have eq3 := hschur ⟨3, by omega⟩; rw [hfr4] at eq3
    cases a0 <;> cases b0
    ·
      have h1z : ∀ p : Fin L, CBit r m false false 1 (coreIdx p.val) = false := fun p => CBit_one_core hr4 hm false p.val p.isLt
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.1
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs11 : S ⟨1, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; exact hself _
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.1
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.1
      rw [hce_0, hs11, hs21, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.1
      rw [hce_0, hce_3, hs13, hs23] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hce_3, hs20] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      intro e; fin_cases e <;> assumption
    ·
      have h1z : ∀ p : Fin L, CBit r m false true 1 (coreIdx p.val) = false := fun p => CBit_one_core hr4 hm true p.val p.isLt
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m false true 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; decide
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.2.2.2.1
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm false true (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m false true (m - 1) (m - 3), hex.2.2.2.2.2.2.1, hle.2.2]
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs11 : S ⟨1, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; exact hself _
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.1
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using h1z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.1
      rw [hce_0, hs11, hs21, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using h1z)]; exact hex.2.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.2.1, CBit_symm r m false true (coreIdx _), hle.2.2]
      rw [hce_0, hce_3, hs13, hs23] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m false true (coreIdx _), hle.1]; decide
      rw [hce_0, hce_1, hce_3, hs20] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      intro e; fin_cases e <;> assumption
    ·
      have hs03 : S ⟨0, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.2.2.2
      have hs33 : S ⟨3, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      rw [hs03, hs13, hs23, hs33] at eq3
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m true false 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; rfl
      have hs12 : S ⟨1, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.1, hle.2.1]; decide
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm true false (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.2.2.2.2
      rw [hs02, hs12, hs22, hs32] at eq2
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by rw [hce_1] at eq3; simpa using eq3
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = false := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m true false (coreIdx _), hle.1]; rfl
      have hs30 : S ⟨3, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hs20, hs30] at eq0
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq0
      have hs21 : S ⟨2, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]
        rw [CBit_symm r m true false (m - 3) 1, hex.2.2.2.2.1, CBit_symm r m true false (coreIdx _) 1, hle.2.1]; decide
      rw [hce_0, hce_1, hce_3, hs21] at eq1
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq1
      intro e; fin_cases e <;> assumption
    ·
      have hs03 : S ⟨0, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.1
      have hs13 : S ⟨1, by omega⟩ ⟨3, by omega⟩ = true := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hex.1
      have hs23 : S ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.2.2.2.2.2.2.2
      have hs33 : S ⟨3, by omega⟩ ⟨3, by omega⟩ = false := by
        rw [hS_zeroR _ _ (by simpa [extraIdx] using hm2z)]; exact hself _
      rw [hs03, hs13, hs23, hs33] at eq3
      have hce_1 : ce ⟨1, by omega⟩ = false := by simpa using eq3
      have hs02 : S ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [CBit_symm r m true true 0 (m - 3), hex.2.2.2.2.2.1, hle.1]; decide
      have hs22 : S ⟨2, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_m3R _ _ rfl]; simp [extraIdx]; rw [hself, CBit_m3_core hr4 hm true true (2 * r - 6) (by omega), decide_eq_false (by omega)]
      have hs32 : S ⟨3, by omega⟩ ⟨2, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.2.2.2.2.2
      rw [hce_1, hs02, hs22, hs32] at eq2
      have hce_0 : ce ⟨0, by omega⟩ = false := by simpa using eq2
      have hs20 : S ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by
        rw [hS_m3L _ _ rfl]; simp [extraIdx]; rw [hex.2.2.2.2.2.1, CBit_symm r m true true (coreIdx _), hle.1]; decide
      have hs30 : S ⟨3, by omega⟩ ⟨0, by omega⟩ = false := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; exact hex.2.2.1
      rw [hce_0, hce_1, hs20, hs30] at eq0
      have hce_2 : ce ⟨2, by omega⟩ = false := by simpa using eq0
      have hs31 : S ⟨3, by omega⟩ ⟨1, by omega⟩ = true := by
        rw [hS_zeroL _ _ (by simpa [extraIdx] using hm2z)]; simp [extraIdx]; rw [CBit_symm]; exact hex.1
      rw [hce_0, hce_1, hce_2, hs31] at eq1
      have hce_3 : ce ⟨3, by omega⟩ = false := by simpa using eq1
      intro e; fin_cases e <;> assumption
  intro i
  by_cases hi : i.val < L
  · have hcp := hcc ⟨i.val, hi⟩
    have h0 : xorFin (fun e : Fin 4 => ce e && CBit r m a0 b0 (extraIdx m a0 b0 e) (coreIdx (partner i.val))) = false :=
      xorFin_eq_false _ (fun e => by rw [hce0 e, Bool.false_and])
    simpa [cc, h0] using hcp
  · have h := hce0 ⟨i.val - L, by omega⟩
    have heq : (⟨L + (i.val - L), by omega⟩ : Fin (2 * r)) = i := Fin.ext (by dsimp only; omega)
    simpa [ce, heq] using h

theorem lower_bound {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r)
    (u : Fin k → Bool) (n t : Nat)
    (C : Circuit) (tap : Fin n → Fin k → Nat)
    (hval : valid (n * (k + 3)) C)
    (hdep : depth (n * (k + 3)) C ≤ 1)
    (hcnt : C.gates.countP nonlinear ≤ t)
    (htap : ∀ j i, tap j i < n * (k + 3) + C.gates.length)
    (hcomp : ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
      (C.wires (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tap j i) false = x j i) :
    n * targetCount r ≤ t := by
  let m := k - 3
  have hm_pos : 0 < m := by omega
  let N := n * m
  let projBlk : Fin n → (Fin N → Bool) → (Fin m → Bool) :=
    fun j Y p => Y ⟨j.val * m + p.val, by
      have : (j.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m j.isLt
      rw [Nat.succ_mul] at this; omega⟩
  let embBlk : Fin n → (Fin m → Bool) → (Fin N → Bool) :=
    fun j v idx =>
      if h : idx.val / m = j.val then v ⟨idx.val % m, Nat.mod_lt _ hm_pos⟩ else false
  have hproj_emb : ∀ (j j' : Fin n) (v : Fin m → Bool),
      projBlk j' (embBlk j v) = if j' = j then v else (fun _ => false) := by
    intro j j' v; funext p; unfold projBlk embBlk; dsimp only
    have hdiv : (j'.val * m + p.val) / m = j'.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hm_pos, Nat.div_eq_of_lt p.isLt, Nat.add_zero]
    have hmod : (j'.val * m + p.val) % m = p.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
    by_cases hjj : j' = j
    · subst hjj; rw [ite_pos rfl, dite_pos hdiv]; exact congrArg v (Fin.ext hmod)
    · have hne : j'.val ≠ j.val := fun h => hjj (Fin.ext h)
      rw [ite_neg hjj, dite_neg (by omega)]
  let xPhi : (Fin N → Bool) → Fin n → Fin k → Bool :=
    fun Y j => phiBlock hk hr hk3 u (projBlk j Y)
  let φ : (Fin N → Bool) → List Bool :=
    fun Y => (List.ofFn (fun j : Fin n => recordFn hk r u (xPhi Y j))).flatten
  have hφ_len : ∀ Y, (φ Y).length = n * (k + 3) := fun Y =>
    flatten_ofFn_length _ (fun j => recordFn_length hk r u (xPhi Y j))
  have hpb := phiBlock_props hk hr hk3 u
  have hφ_aff : ∀ idx < n * (k + 3), IsAffine (fun Y => (φ Y).getD idx false) := by
    intro idx hidx
    have hk3_pos : 0 < k + 3 := by omega
    let j : Fin n := ⟨idx / (k + 3), Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)⟩
    let p : Fin (k + 3) := ⟨idx % (k + 3), Nat.mod_lt _ hk3_pos⟩
    have hidx_eq : idx = j.val * (k + 3) + p.val := by
      dsimp [j, p]; rw [Nat.mul_comm]; exact (Nat.div_add_mod idx (k + 3)).symm
    have hget : (fun Y => (φ Y).getD idx false) =
        (fun Y => (recordFn hk r u (xPhi Y j)).getD p.val false) := by
      funext Y; rw [hidx_eq]; exact flatten_ofFn_getD _ (fun j' => recordFn_length hk r u (xPhi Y j')) j p
    rw [hget]
    by_cases hpk : p.val < k
    · have h1 : (fun Y => (recordFn hk r u (xPhi Y j)).getD p.val false) =
          (fun Y => diffFn hk u (phiBlock hk hr hk3 u (projBlk j Y)) ⟨p.val, hpk⟩) := by
        funext Y; exact recordFn_getD_lt hk r u (xPhi Y j) p.val hpk
      rw [h1]
      exact isAffine_comp (hpb.1 ⟨p.val, hpk⟩) (fun q => isAffine_coord _)
    · by_cases hpk0 : p.val = k
      · have h1 : (fun Y => (recordFn hk r u (xPhi Y j)).getD p.val false) = fun _ => false := by
          funext Y; rw [hpk0, recordFn_getD_k]; exact hpb.2.2.2.1 (projBlk j Y)
        rw [h1]; exact isAffine_const false
      · by_cases hpk1 : p.val = k + 1
        · have h1 : (fun Y => (recordFn hk r u (xPhi Y j)).getD p.val false) = fun _ => false := by
            funext Y; rw [hpk1, recordFn_getD_k1]; exact hpb.2.1 (projBlk j Y)
          rw [h1]; exact isAffine_const false
        · have hpk2 : p.val = k + 2 := by omega
          have h1 : (fun Y => (recordFn hk r u (xPhi Y j)).getD p.val false) = fun _ => false := by
            funext Y; rw [hpk2, recordFn_getD_k2]; exact hpb.2.2.1 (projBlk j Y)
          rw [h1]; exact isAffine_const false
  rcases circuit_depth1_decomp C hval hdep φ hφ_len hφ_aff with ⟨L, R, hdecomp⟩
  let M := C.gates.countP nonlinear
  let G : Fin M → ((Fin N → Bool) × (Fin N → Bool)) → Bool :=
    fun p ab => rank2 (L p) (R p) ab.1 ab.2

  let B0Blk : Fin n → ((Fin N → Bool) × (Fin N → Bool)) → Bool :=
    fun j ab => pol (fun y => Q0 hr hk3 (wOfY hr hk3 y)) (projBlk j ab.1) (projBlk j ab.2)
  let BkBlk : Fin n → ((Fin N → Bool) × (Fin N → Bool)) → Bool :=
    fun j ab => pol (fun y => Qk hr hk3 (wOfY hr hk3 y)) (projBlk j ab.1) (projBlk j ab.2)
  let BpBlk : Fin n → ((Fin N → Bool) × (Fin N → Bool)) → Bool :=
    fun j ab => pol (fun y => Qp hk r (wOfY hr hk3 y)) (projBlk j ab.1) (projBlk j ab.2)
  have hpol_proj : ∀ (f : (Fin m → Bool) → Bool) (j : Fin n) (a b : Fin N → Bool),
      pol (fun Y => f (projBlk j Y)) a b = pol f (projBlk j a) (projBlk j b) := by
    intro f j a b; unfold pol; rfl
  have hInSpan_x : ∀ (j : Fin n) (i : Fin k),
      InSpan G (fun ab => pol (fun Y => xPhi Y j i) ab.1 ab.2) := by
    intro j i
    rcases hdecomp (tap j i) (htap j i) with ⟨c, hc⟩
    refine ⟨c, fun ab => ?_⟩
    have heq : (fun Y => (C.wires (φ Y)).getD (tap j i) false) = (fun Y => xPhi Y j i) := by
      funext Y; exact hcomp (xPhi Y) j i
    rw [← heq]; exact hc ab.1 ab.2
  have hInSpan_B0 : ∀ j : Fin n, InSpan G (B0Blk j) := by
    intro j
    rcases hInSpan_x j ⟨0, hk⟩ with ⟨c, hc⟩
    refine ⟨c, fun ab => ?_⟩
    dsimp only [B0Blk]; rw [← hpb.2.2.2.2.1, ← hpol_proj]; exact hc ab
  have hInSpan_Bp : ∀ j : Fin n, InSpan G (BpBlk j) := by
    intro j
    rcases inSpan_xor (hInSpan_x j ⟨3, by omega⟩) (hInSpan_x j ⟨0, hk⟩) with ⟨c, hc⟩
    refine ⟨c, fun ab => ?_⟩
    dsimp only [BpBlk]; rw [← hpb.2.2.2.2.2.1, ← hpol_proj]
    have hpx := hc ab; dsimp only at hpx; rw [← pol_xor] at hpx; exact hpx
  have hInSpan_Bk : ∀ j : Fin n, InSpan G (BkBlk j) := by
    intro j
    rcases inSpan_xor (hInSpan_x j ⟨k - 1, by omega⟩) (inSpan_xor (hInSpan_x j ⟨3, by omega⟩) (hInSpan_x j ⟨0, hk⟩)) with ⟨c, hc⟩
    refine ⟨c, fun ab => ?_⟩
    dsimp only [BkBlk]; rw [← hpb.2.2.2.2.2.2, ← hpol_proj]
    have hpx := hc ab; dsimp only at hpx; rw [← pol_xor, ← pol_xor] at hpx; exact hpx

  let U : Fin (2 * n) → ((Fin N → Bool) × (Fin N → Bool)) → Bool :=
    fun idx ab =>
      let j : Fin n := ⟨idx.val / 2, by omega⟩
      if idx.val % 2 = 0 then B0Blk j ab else BkBlk j ab
  have hU_span : ∀ idx : Fin (2 * n), InSpan G (U idx) := by
    intro idx; unfold U; split_ifs
    · exact hInSpan_B0 _
    · exact hInSpan_Bk _
  have hpol_zero_left : ∀ (f : (Fin m → Bool) → Bool) (v : Fin m → Bool), pol f (fun _ => false) v = false := by
    intro f v; unfold pol
    have h1 : (fun i : Fin m => xor false (v i)) = v := by funext i; exact Bool.false_xor (v i)
    rw [h1]; cases f v <;> cases f (fun _ => false) <;> rfl
  have hU_ind : ∀ a : Fin (2 * n) → Bool,
      (∀ ab, xorFin (fun idx => a idx && U idx ab) = false) → ∀ idx, a idx = false := by
    intro a ha idx
    let j : Fin n := ⟨idx.val / 2, by omega⟩
    let v1 : Fin m → Bool := if idx.val % 2 = 0 then eVec ⟨1, by omega⟩ else eVec ⟨0, by omega⟩
    let v2 : Fin m → Bool := eVec ⟨2, by omega⟩
    have hval := ha (embBlk j v1, embBlk j v2)
    rw [xorFin_single' idx] at hval
    · have hu : U idx (embBlk j v1, embBlk j v2) = true := by
        unfold U; dsimp only [B0Blk, BkBlk]
        have heq_j : (⟨idx.val / 2, by omega⟩ : Fin n) = j := rfl
        rw [heq_j, hproj_emb, hproj_emb, ite_pos rfl, ite_pos rfl]
        by_cases hm2 : idx.val % 2 = 0
        · rw [ite_pos hm2]; dsimp only [v1, v2]; rw [ite_pos hm2, pol_Q0_eVec]; dsimp only; rfl
        · rw [ite_neg hm2]; dsimp only [v1, v2]; rw [ite_neg hm2, pol_Qk_eVec]; dsimp only; rfl
      rw [hu, Bool.and_true] at hval; exact hval
    · intro idx' hne
      let j' : Fin n := ⟨idx'.val / 2, by omega⟩
      by_cases hjj : j' = j
      · have hmod_ne : idx'.val % 2 ≠ idx.val % 2 := fun h => hne (Fin.ext (by
          have hv := congrArg Fin.val hjj; dsimp [j, j'] at hv; omega))
        have hu : U idx' (embBlk j v1, embBlk j v2) = false := by
          unfold U; dsimp only [B0Blk, BkBlk]
          rw [show (⟨idx'.val / 2, by omega⟩ : Fin n) = j from hjj, hproj_emb, hproj_emb, ite_pos rfl, ite_pos rfl]
          by_cases hm2 : idx.val % 2 = 0
          · rw [ite_neg (by omega)]; dsimp only [v1, v2]; rw [ite_pos hm2, pol_Qk_eVec]; dsimp only; rfl
          · rw [ite_pos (by omega)]; dsimp only [v1, v2]; rw [ite_neg hm2, pol_Q0_eVec]; dsimp only; rfl
        rw [hu, Bool.and_false]
      · have hu : U idx' (embBlk j v1, embBlk j v2) = false := by
          unfold U; dsimp only [B0Blk, BkBlk]
          have hne' : (⟨idx'.val / 2, by omega⟩ : Fin n) ≠ j := hjj
          rw [hproj_emb, hproj_emb, ite_neg hne', ite_neg hne']
          split_ifs <;> exact hpol_zero_left _ _
        rw [hu, Bool.and_false]
  rcases steinitz_bool G U hU_span hU_ind with ⟨P, hPcard, hPspan⟩
  have h2n_le_M : 2 * n ≤ M := by
    have hle := Finset.card_le_univ P
    rw [hPcard, Fintype.card_fin] at hle; exact hle

  by_cases hr2 : r = 2
  · unfold targetCount; rw [ite_pos hr2]; omega

  have hr3 : 3 ≤ r := by omega
  have hBp_all : InSpan G (fun ab => xorFin (fun j : Fin n => BpBlk j ab)) :=
    inSpan_xorFin BpBlk hInSpan_Bp
  rcases hPspan _ hBp_all with ⟨alpha, beta, hbetaP, hBp_eq⟩

  let a0 : Fin n → Bool := fun j => xor (alpha ⟨2 * j.val, by omega⟩) (decide (r % 2 = 0))
  let b0 : Fin n → Bool := fun j => xor (alpha ⟨2 * j.val + 1, by omega⟩) (decide (r % 2 = 0))
  have hblock_form : ∀ (j : Fin n) (p q : Fin m),
      xorFin (fun idx : Fin M => beta idx && G idx (embBlk j (eVec p), embBlk j (eVec q))) =
        CBit r m (a0 j) (b0 j) p.val q.val := by
    intro j p q
    have h := hBp_eq (embBlk j (eVec p), embBlk j (eVec q))

    have hlhs : xorFin (fun j' : Fin n => BpBlk j' (embBlk j (eVec p), embBlk j (eVec q))) =
        xor (if r % 2 = 0 then xor (B0Bit p.val q.val) (BkBit p.val q.val) else false) (BmBit r m p.val q.val) := by
      rw [xorFin_single' j]
      · dsimp only [BpBlk]; rw [hproj_emb, hproj_emb, ite_pos rfl, ite_pos rfl]
        have hqp : (fun y => Qp hk r (wOfY hr hk3 y)) =
            (fun y => xor (if r % 2 = 0 then xor (Q0 hr hk3 (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y)) else false)
                          (QpMid hk hr hk3 (wOfY hr hk3 y))) := by
          funext y; exact Qp_eq_QpMid hk hr hk3 (wOfY hr hk3 y) (wOfY_3 hr hk3 y)
        rw [hqp, pol_xor, pol_QpMid_eVec hk hr3 hk3 p q]
        congr 1
        by_cases he : r % 2 = 0
        · rw [ite_pos he]
          rw [show (fun y => if r % 2 = 0 then xor (Q0 hr hk3 (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y)) else false) =
              (fun y => xor (Q0 hr hk3 (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y))) from funext fun _ => ite_pos he,
            pol_xor, pol_Q0_eVec, pol_Qk_eVec]
        · rw [ite_neg he]
          rw [show (fun y => if r % 2 = 0 then xor (Q0 hr hk3 (wOfY hr hk3 y)) (Qk hr hk3 (wOfY hr hk3 y)) else false) =
              (fun _ => false) from funext fun _ => ite_neg he, pol_const]
      · intro j' hj'; dsimp only [BpBlk]
        rw [hproj_emb, hproj_emb, ite_neg hj', ite_neg hj']; exact hpol_zero_left _ _

    have hUsum : xorFin (fun idx : Fin (2 * n) => alpha idx && U idx (embBlk j (eVec p), embBlk j (eVec q))) =
        xor (alpha ⟨2 * j.val, by omega⟩ && B0Bit p.val q.val)
            (alpha ⟨2 * j.val + 1, by omega⟩ && BkBit p.val q.val) := by
      have h1 : xorFin (fun idx : Fin (2 * n) => alpha idx && U idx (embBlk j (eVec p), embBlk j (eVec q))) =
          xorFin (fun j' : Fin n =>
            xor (alpha ⟨2 * j'.val, by omega⟩ && B0Blk j' (embBlk j (eVec p), embBlk j (eVec q)))
                (alpha ⟨2 * j'.val + 1, by omega⟩ && BkBlk j' (embBlk j (eVec p), embBlk j (eVec q)))) := by
        have hp2 := xorFin_prod (a := n) (b := 2) (by omega)
          (fun (j' : Fin n) (c : Fin 2) => alpha ⟨2 * j'.val + c.val, by omega⟩ && U ⟨2 * j'.val + c.val, by omega⟩ (embBlk j (eVec p), embBlk j (eVec q)))
        have hcast : xorFin (fun idx : Fin (2 * n) => alpha idx && U idx (embBlk j (eVec p), embBlk j (eVec q))) =
            xorFin (fun idx : Fin (n * 2) =>
              alpha ⟨2 * (idx.val / 2) + idx.val % 2, by omega⟩ &&
              U ⟨2 * (idx.val / 2) + idx.val % 2, by omega⟩ (embBlk j (eVec p), embBlk j (eVec q))) :=
          xorFin_cast (Nat.mul_comm 2 n) _ _ (fun idx h1 h2 => by
            congr 1
            · exact congrArg alpha (Fin.ext (by dsimp only; omega))
            · exact congrArg (fun x => U x _) (Fin.ext (by dsimp only; omega)))
        rw [hcast, hp2]
        apply xorFin_congr; intro j'
        have hfr2 : ∀ g : Fin 2 → Bool, xorFin g = xor (g ⟨0, by omega⟩) (g ⟨1, by omega⟩) := by
          intro g; unfold xorFin; have : List.finRange 2 = [0, 1] := rfl; rw [this]; simp
        rw [hfr2]; dsimp only [U]
        have hm0 : (2 * j'.val + 0) % 2 = 0 := by omega
        have hm1 : ¬((2 * j'.val + 1) % 2 = 0) := by omega
        have hd0 : (⟨(2 * j'.val + 0) / 2, by omega⟩ : Fin n) = j' := Fin.ext (by dsimp only; omega)
        have hd1 : (⟨(2 * j'.val + 1) / 2, by omega⟩ : Fin n) = j' := Fin.ext (by dsimp only; omega)
        rw [ite_pos hm0, ite_neg hm1, hd0, hd1]; rfl
      rw [h1, xorFin_single' j]
      · dsimp only [B0Blk, BkBlk]; rw [hproj_emb, hproj_emb, ite_pos rfl, ite_pos rfl, pol_Q0_eVec, pol_Qk_eVec]
      · intro j' hj'; dsimp only [B0Blk, BkBlk]
        rw [hproj_emb, hproj_emb, ite_neg hj', ite_neg hj', hpol_zero_left, hpol_zero_left]; simp
    rw [hlhs, hUsum] at h
    unfold CBit a0 b0
    by_cases he : r % 2 = 0
    · rw [ite_pos he] at h; rw [decide_eq_true he]
      cases ha1 : alpha ⟨2 * j.val, by omega⟩ <;> cases ha2 : alpha ⟨2 * j.val + 1, by omega⟩ <;>
        cases hb0 : B0Bit p.val q.val <;> cases hbk : BkBit p.val q.val <;> cases hbm : BmBit r m p.val q.val <;>
        cases xG : xorFin (fun idx : Fin M => beta idx && G idx (embBlk j (eVec p), embBlk j (eVec q))) <;>
        rw [ha1, ha2, hb0, hbk, hbm, xG] at h <;> simp at h ⊢
    · rw [ite_neg he] at h; rw [decide_eq_false he]
      cases ha1 : alpha ⟨2 * j.val, by omega⟩ <;> cases ha2 : alpha ⟨2 * j.val + 1, by omega⟩ <;>
        cases hb0 : B0Bit p.val q.val <;> cases hbk : BkBit p.val q.val <;> cases hbm : BmBit r m p.val q.val <;>
        cases xG : xorFin (fun idx : Fin M => beta idx && G idx (embBlk j (eVec p), embBlk j (eVec q))) <;>
        rw [ha1, ha2, hb0, hbk, hbm, xG] at h <;> simp at h ⊢

  have hcross_zero : ∀ (j j' : Fin n), j ≠ j' → ∀ (p q : Fin m),
      xorFin (fun idx : Fin M => beta idx && G idx (embBlk j (eVec p), embBlk j' (eVec q))) = false := by
    intro j j' hne p q
    have h := hBp_eq (embBlk j (eVec p), embBlk j' (eVec q))
    have hbp0 : xorFin (fun j0 : Fin n => BpBlk j0 (embBlk j (eVec p), embBlk j' (eVec q))) = false := by
      apply xorFin_eq_false; intro j0; dsimp only [BpBlk]
      rw [hproj_emb, hproj_emb]
      by_cases h0 : j0 = j
      · subst h0; rw [ite_pos rfl, ite_neg hne]
        unfold pol; dsimp only
        have h1 : (fun i => xor (eVec p i) false) = eVec p := by funext i; exact Bool.xor_false _
        rw [h1]; cases Qp hk r (wOfY hr hk3 (eVec p)) <;> cases Qp hk r (wOfY hr hk3 (fun _ => false)) <;> rfl
      · rw [ite_neg h0]; exact hpol_zero_left _ _
    have hu0 : xorFin (fun idx : Fin (2 * n) => alpha idx && U idx (embBlk j (eVec p), embBlk j' (eVec q))) = false := by
      apply xorFin_eq_false; intro idx; unfold U; dsimp only [B0Blk, BkBlk]
      rw [hproj_emb, hproj_emb]
      let j0 : Fin n := ⟨idx.val / 2, by omega⟩
      by_cases h0 : j0 = j
      · have h0' : j0 ≠ j' := fun heq => hne (h0.symm.trans heq)
        change (alpha idx && (if idx.val % 2 = 0 then pol _ (if j0 = j then eVec p else _) (if j0 = j' then eVec q else _)
                              else pol _ (if j0 = j then eVec p else _) (if j0 = j' then eVec q else _))) = false
        rw [ite_pos h0, ite_neg h0']
        have hpol_r : ∀ (f : (Fin m → Bool) → Bool), pol f (eVec p) (fun _ => false) = false := fun f => by
          unfold pol; dsimp only
          have h1 : (fun i => xor (eVec p i) false) = eVec p := by funext i; exact Bool.xor_false _
          rw [h1]; cases f (eVec p) <;> cases f (fun _ => false) <;> rfl
        split_ifs <;> rw [hpol_r, Bool.and_false]
      · change (alpha idx && (if idx.val % 2 = 0 then pol _ (if j0 = j then eVec p else _) (if j0 = j' then eVec q else _)
                              else pol _ (if j0 = j then eVec p else _) (if j0 = j' then eVec q else _))) = false
        rw [ite_neg h0]
        split_ifs <;> rw [hpol_zero_left, Bool.and_false]
    rw [hbp0, hu0, Bool.false_xor] at h; exact h.symm

  have hlift : ∀ (s : Nat) (hs_pos : 0 < s) (idxBlk : Fin n → Fin s → Fin m),
      (∀ (j : Fin n) (c : Fin s → Bool),
        (∀ q : Fin s, xorFin (fun i : Fin s => c i && CBit r m (a0 j) (b0 j) (idxBlk j i).val (idxBlk j q).val) = false) →
        ∀ i : Fin s, c i = false) →
      n * s ≤ 2 * (M - 2 * n) := by
    intro s hs_pos idxBlk hinv_blk
    let v : Fin (n * s) → Fin N → Bool := fun p =>
      let j : Fin n := ⟨p.val / s, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm s n]; exact p.isLt)⟩
      let i : Fin s := ⟨p.val % s, Nat.mod_lt _ hs_pos⟩
      embBlk j (eVec (idxBlk j i))
    have hrank := rank_le_of_rank2_span L R P beta hbetaP v (by
      intro c hc p
      let j : Fin n := ⟨p.val / s, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm s n]; exact p.isLt)⟩
      let i : Fin s := ⟨p.val % s, Nat.mod_lt _ hs_pos⟩
      let cj : Fin s → Bool := fun i' => c ⟨j.val * s + i'.val, by
        have : (j.val + 1) * s ≤ n * s := Nat.mul_le_mul_right s j.isLt
        rw [Nat.succ_mul] at this; omega⟩
      have hcj0 : ∀ i' : Fin s, cj i' = false := by
        apply hinv_blk j
        intro q
        let pq : Fin (n * s) := ⟨j.val * s + q.val, by
          have : (j.val + 1) * s ≤ n * s := Nat.mul_le_mul_right s j.isLt
          rw [Nat.succ_mul] at this; omega⟩
        have hcq := hc pq
        have hprod := xorFin_prod (a := n) (b := s) hs_pos
          (fun (j' : Fin n) (i' : Fin s) =>
            c ⟨j'.val * s + i'.val, by
              have : (j'.val + 1) * s ≤ n * s := Nat.mul_le_mul_right s j'.isLt
              rw [Nat.succ_mul] at this; omega⟩ &&
            xorFin (fun idx : Fin M => beta idx && G idx (embBlk j' (eVec (idxBlk j' i')), embBlk j (eVec (idxBlk j q)))))
        have hmatch : xorFin (fun p' : Fin (n * s) =>
              c p' && xorFin (fun idx : Fin M => beta idx && rank2 (L idx) (R idx) (v p') (v pq))) =
            xorFin (fun j' : Fin n => xorFin (fun i' : Fin s =>
              c ⟨j'.val * s + i'.val, by
                have : (j'.val + 1) * s ≤ n * s := Nat.mul_le_mul_right s j'.isLt
                rw [Nat.succ_mul] at this; omega⟩ &&
              xorFin (fun idx : Fin M => beta idx && G idx (embBlk j' (eVec (idxBlk j' i')), embBlk j (eVec (idxBlk j q)))))) := by
          rw [← hprod]; apply xorFin_congr; intro p'
          have hdiv_pq : pq.val / s = j.val := by
            dsimp [pq]; rw [Nat.mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt q.isLt, Nat.add_zero]
          have hmod_pq : pq.val % s = q.val := by
            dsimp [pq]; rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt q.isLt]
          have hvpq : v pq = embBlk j (eVec (idxBlk j q)) := by
            unfold v; dsimp only
            have hj1 : (⟨pq.val / s, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm s n]; exact pq.isLt)⟩ : Fin n) = j := Fin.ext hdiv_pq
            have hq1 : (⟨pq.val % s, Nat.mod_lt _ hs_pos⟩ : Fin s) = q := Fin.ext hmod_pq
            rw [hj1, hq1]
          have hp'_eq : (⟨p'.val / s * s + p'.val % s, by
              have hlt : p'.val / s < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm s n]; exact p'.isLt)
              have : (p'.val / s + 1) * s ≤ n * s := Nat.mul_le_mul_right s hlt
              rw [Nat.succ_mul] at this; have := Nat.mod_lt p'.val hs_pos; omega⟩ : Fin (n * s)) = p' :=
            Fin.ext (by dsimp only; rw [Nat.mul_comm]; exact Nat.div_add_mod p'.val s)
          rw [hvpq, hp'_eq]
        rw [hmatch, xorFin_single' j] at hcq
        · rw [← hcq]; apply xorFin_congr; intro i'; rw [hblock_form]
        · intro j' hj'; apply xorFin_eq_false; intro i'
          rw [hcross_zero j' j hj', Bool.and_false]
      have hp_eq : (⟨j.val * s + i.val, by
          have : (j.val + 1) * s ≤ n * s := Nat.mul_le_mul_right s j.isLt
          rw [Nat.succ_mul] at this; omega⟩ : Fin (n * s)) = p :=
        Fin.ext (by dsimp [j, i]; rw [Nat.mul_comm]; exact Nat.div_add_mod p.val s)
      have hres := hcj0 i; dsimp only [cj] at hres; rw [hp_eq] at hres; exact hres)
    rw [hPcard] at hrank; exact hrank
  by_cases hr3' : r = 3
  · have hbound := hlift 4 (by omega) (fun _ i => ⟨i.val, by omega⟩) (by
      intro j c hc i
      have hm6 : m = 6 := by omega
      have hCeq : ∀ x y, CBit r m (a0 j) (b0 j) x y = CBit 3 6 (a0 j) (b0 j) x y := fun x y => by rw [hr3', hm6]
      apply inv_CBit_r3 (a0 j) (b0 j) c
      intro q; rw [← hc q]; apply xorFin_congr; intro i'; dsimp only; rw [hCeq])
    unfold targetCount; rw [ite_neg hr2, ite_pos hr3']
    have hmul : n * 4 = 2 * (2 * n) := by omega
    omega
  · have hr4 : 4 ≤ r := by omega
    have hm3 : m = 3 * r - 3 := by omega
    have hidx_lt : ∀ (j : Fin n) (i : Fin (2 * r)), basisIdx4 r m (a0 j) (b0 j) i < m := by
      intro j i; unfold basisIdx4; split_ifs with h
      · exact coreIdx_lt hr4 hm3 i.val h
      · have hex_lt : ∀ e : Fin 4, extraIdx m (a0 j) (b0 j) e < m := fun e => by
          fin_cases e
          · simp [extraIdx]; omega
          · simp [extraIdx]; omega
          · simp [extraIdx]; split_ifs <;> omega
          · simp [extraIdx]; split_ifs <;> omega
        exact hex_lt ⟨i.val - (2 * r - 4), by omega⟩
    have hbound := hlift (2 * r) (by omega) (fun j i => ⟨basisIdx4 r m (a0 j) (b0 j) i, hidx_lt j i⟩) (by
      intro j c hc i
      exact inv_CBit_r4 hr4 hm3 (a0 j) (b0 j) c hc i)
    unfold targetCount; rw [ite_neg hr2, ite_neg hr3']
    have h1 : n * (r + 2) = n * r + 2 * n := by rw [Nat.mul_add, Nat.mul_comm n 2]
    have h2 : n * (2 * r) = 2 * (n * r) := by rw [← Nat.mul_assoc, Nat.mul_comm n 2, Nat.mul_assoc]
    omega

def Good (width : Nat) (gs : List Gate) : Prop :=
  ReadsBack width ⟨gs, 0⟩ ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (depthList width gs).foldr max 0 ≤ 1

def WireSpec (width : Nat) (gs : List Gate) (w : Nat) (d0 : Bool) (f : List Bool → Bool) : Prop :=
  w < width + gs.length ∧
  (d0 = true → (depthList width gs).getD w 0 = 0) ∧
  ∀ inp : List Bool, inp.length = width → (Circuit.wires ⟨gs, 0⟩ inp).getD w false = f inp

lemma good_nil (width : Nat) : Good width [] := by
  refine ⟨fun j hj => by simp at hj, (fun _ hg => by cases hg), ?_⟩
  rw [foldr_max_le_iff]; intro x hx
  have hmem : x ∈ List.replicate width 0 := hx
  rw [List.mem_replicate] at hmem; omega

lemma wireSpec_input (width : Nat) (w : Nat) (hw : w < width) :
    WireSpec width [] w true (fun inp => inp.getD w false) := by
  refine ⟨by simp [hw], fun _ => ?_, fun inp _ => rfl⟩
  unfold depthList
  rw [List.foldl_nil, List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_replicate]

lemma append_gate {width : Nat} (gs : List Gate) (hgood : Good width gs) (g : Gate)
    (hfan : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < width + gs.length)
    (hdg : (g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat ≤ 1) :
    Good width (gs ++ [g]) ∧
    (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat ∧
    (∀ w d0 f, WireSpec width gs w d0 f → WireSpec width (gs ++ [g]) w d0 f) ∧
    WireSpec width (gs ++ [g]) (width + gs.length)
      (decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0))
      (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) := by
  have hds_step : depthList width (gs ++ [g]) =
      depthList width gs ++ [(g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
    unfold depthList; rw [List.foldl_append]; rfl
  have hds_len : (depthList width gs).length = width + gs.length := depthList_length width gs
  have hw_step : ∀ inp, Circuit.wires ⟨gs ++ [g], 0⟩ inp =
      Circuit.wires ⟨gs, 0⟩ inp ++ [g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)] := by
    intro inp; unfold Circuit.wires; rw [List.foldl_append]; rfl
  have hw_len : ∀ inp, inp.length = width → (Circuit.wires ⟨gs, 0⟩ inp).length = width + gs.length := by
    intro inp hlen; unfold Circuit.wires; rw [wires_length, hlen]
  have hgood' : Good width (gs ++ [g]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hlt : j < gs.length
      · have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
          unfold gateAt; exact getD_append_lt gs g _ hlt
        rw [hga] at hi; exact hgood.1 j hlt i hi
      · have hjeq : j = gs.length := by omega
        subst hjeq
        have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by unfold gateAt; exact getD_append_eq gs g _
        rw [hga] at hi; exact hrb i hi
    · intro g' hg'
      rcases List.mem_append.mp hg' with hg1 | hg2
      · exact hgood.2.1 g' hg1
      · simp only [List.mem_singleton] at hg2; subst hg2; exact hfan
    · rw [foldr_max_le_iff]; intro x hx
      rw [hds_step] at hx
      rcases List.mem_append.mp hx with hx1 | hx2
      · exact (foldr_max_le_iff _ _).mp hgood.2.2 x hx1
      · simp only [List.mem_singleton] at hx2; subst hx2; exact hdg
  have hcnt : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat := by
    rw [List.countP_append, List.countP_cons, List.countP_nil]
    cases nonlinear g <;> simp [Bool.toNat]
  have hpres : ∀ w d0 f, WireSpec width gs w d0 f → WireSpec width (gs ++ [g]) w d0 f := by
    intro w d0 f hw
    have hwlt : w < width + gs.length := hw.1
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun hd0 => ?_, fun inp hlen => ?_⟩
    · rw [hds_step, getD_append_lt _ _ _ (by omega)]; exact hw.2.1 hd0
    · rw [hw_step, getD_append_lt _ _ _ (by rw [hw_len inp hlen]; exact hw.1)]; exact hw.2.2 inp hlen
  have hnew : WireSpec width (gs ++ [g]) (width + gs.length)
      (decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0))
      (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) := by
    refine ⟨by simp, fun hd0 => ?_, fun inp hlen => ?_⟩
    · rw [hds_step, ← hds_len, getD_append_eq]; exact of_decide_eq_true hd0
    · rw [hw_step, ← hw_len inp hlen, getD_append_eq]
  exact ⟨hgood', hcnt, hpres, hnew⟩

lemma addConst {width : Nat} (gs : List Gate) (hgood : Good width gs) (c : Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0 f0, WireSpec width gs w0 d0 f0 → WireSpec width gs' w0 d0 f0) ∧
      WireSpec width gs' w true (fun _ => c) := by
  let g : Gate := if c then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩
  have hnl : nonlinear g = false := by cases c <;> rfl
  have hinp : g.inputs = [] := by cases c <;> rfl
  have hstep := append_gate gs hgood g (by rw [hinp]; simp) (by rw [hinp]; intro _ h; cases h)
    (by rw [hinp, hnl]; simp)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  have hspec := hstep.2.2.2
  have hd : decide ((g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nonlinear g).toNat = 0) = true := by
    rw [hinp, hnl]; rfl
  have heval : (fun inp => g.op.eval (g.inputs.map fun a => (Circuit.wires ⟨gs, 0⟩ inp).getD a false)) = (fun _ => c) := by
    funext inp; cases c <;> rfl
  rw [hd, heval] at hspec; exact hspec

lemma addNot {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a : Nat} {d0 : Bool} {fa : List Bool → Bool} (ha : WireSpec width gs a d0 fa) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => !(fa inp)) := by
  let g : Gate := ⟨GateOp.not, [a]⟩
  have hnl : nonlinear g = false := rfl
  have hda_le : (depthList width gs).getD a 0 ≤ 1 :=
    le_trans (depthList_getD_le_depth width gs a) hgood.2.2
  have hstep := append_gate gs hgood g (by simp [g]) (by intro i hi; simp [g] at hi; subst hi; exact ha.1)
    (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero]; exact hda_le)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, fun hd0 => ?_, fun inp hlen => ?_⟩
  · have hda0 : (depthList width gs).getD a 0 = 0 := ha.2.1 hd0
    exact hstep.2.2.2.2.1 (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, hda0]; rfl)
  · rw [hstep.2.2.2.2.2 inp hlen]; simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, ha.2.2 inp hlen]

lemma addXor {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {d0a d0b : Bool} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a d0a fa) (hb : WireSpec width gs b d0b fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w (d0a && d0b) (fun inp => xor (fa inp) (fb inp)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  have hnl1 : nonlinear g1 = false := rfl
  have hda_le : (depthList width gs).getD a 0 ≤ 1 := le_trans (depthList_getD_le_depth width gs a) hgood.2.2
  have hdb_le : (depthList width gs).getD b 0 ≤ 1 := le_trans (depthList_getD_le_depth width gs b) hgood.2.2
  have hstep1 := append_gate gs hgood g1 (by simp [g1])
    (by intro i hi; simp [g1] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
    (by simp only [g1, hnl1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, Nat.max_le]; exact ⟨hda_le, hdb_le⟩)
  have hxnor : WireSpec width (gs ++ [g1]) (width + gs.length) (d0a && d0b) (fun inp => !(xor (fa inp) (fb inp))) := by
    refine ⟨hstep1.2.2.2.1, fun hd => ?_, fun inp hlen => ?_⟩
    · simp only [Bool.and_eq_true] at hd
      have hda0 := ha.2.1 hd.1; have hdb0 := hb.2.1 hd.2
      exact hstep1.2.2.2.2.1 (by simp only [g1, hnl1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_false, Nat.add_zero, hda0, hdb0]; rfl)
    · rw [hstep1.2.2.2.2.2 inp hlen]
      simp only [g1, List.map_cons, List.map_nil, ha.2.2 inp hlen, hb.2.2 inp hlen]
      cases fa inp <;> cases fb inp <;> rfl
  rcases addNot (gs ++ [g1]) hstep1.1 hxnor with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
  refine ⟨gs2, w2, hg2, by rw [hc2, hstep1.2.1, hnl1]; rfl, fun w0 d0' f0 h0 => hp2 w0 d0' f0 (hstep1.2.2.1 w0 d0' f0 h0), ?_⟩
  have heq : (fun inp => !(!(xor (fa inp) (fb inp)))) = (fun inp => xor (fa inp) (fb inp)) := by
    funext inp; exact Bool.not_not _
  rw [heq] at hw2; exact hw2

lemma addAnd0 {width : Nat} (gs : List Gate) (hgood : Good width gs)
    {a b : Nat} {fa fb : List Bool → Bool}
    (ha : WireSpec width gs a true fa) (hb : WireSpec width gs b true fb) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w false (fun inp => fa inp && fb inp) := by
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  have hnl : nonlinear g = true := rfl
  have hda0 := ha.2.1 rfl; have hdb0 := hb.2.1 rfl
  have hstep := append_gate gs hgood g (by simp [g])
    (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
    (by simp only [g, hnl, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, Bool.toNat_true, hda0, hdb0]; omega)
  refine ⟨gs ++ [g], width + gs.length, hstep.1, by rw [hstep.2.1, hnl]; rfl, hstep.2.2.1, ?_⟩
  refine ⟨hstep.2.2.2.1, (fun h => by cases h), fun inp hlen => ?_⟩
  rw [hstep.2.2.2.2.2 inp hlen]
  simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
    ha.2.2 inp hlen, hb.2.2 inp hlen]

lemma addAffine {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (c : Bool) (coeff : Fin M → Bool) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) := by
  induction M generalizing gs with
  | zero =>
    rcases addConst gs hgood c with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
    refine ⟨hw1.1, fun _ => hw1.2.1 rfl, fun inp hlen => ?_⟩
    rw [hw1.2.2 inp hlen]; exact (Bool.xor_false c).symm
  | succ M ih =>
    rcases ih gs hgood (fun p => ws p.castSucc) (fun p => vals p.castSucc)
      (fun p => hws p.castSucc) (fun p => coeff p.castSucc) with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
    cases hcl : coeff (Fin.last M)
    · refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
      refine ⟨hw1.1, hw1.2.1, fun inp hlen => ?_⟩
      rw [hw1.2.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.false_and, Bool.xor_false]
    · have hw_last : WireSpec width gs1 (ws (Fin.last M)) d0 (vals (Fin.last M)) := hp1 _ _ _ (hws (Fin.last M))
      rcases addXor gs1 hg1 hw1 hw_last with ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
      have hd0_eq : (d0 && d0) = d0 := by cases d0 <;> rfl
      rw [hd0_eq] at hw2
      refine ⟨gs2, w2, hg2, by rw [hc2, hc1], fun w0 d0' f0 h0 => hp2 _ _ _ (hp1 _ _ _ h0), ?_⟩
      refine ⟨hw2.1, hw2.2.1, fun inp hlen => ?_⟩
      rw [hw2.2.2 inp hlen]; dsimp only; rw [xorFin_succ, hcl, Bool.true_and, Bool.xor_assoc]

lemma addAffineFn {width M : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (f : (Fin M → Bool) → Bool) (hf : IsAffine f) :
    ∃ (gs' : List Gate) (w : Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      WireSpec width gs' w d0 (fun inp => f (fun p => vals p inp)) := by
  rcases hf with ⟨c, coeff, hfe⟩
  rcases addAffine gs hgood d0 ws vals hws c coeff with ⟨gs1, w1, hg1, hc1, hp1, hw1⟩
  refine ⟨gs1, w1, hg1, hc1, hp1, ?_⟩
  have heq : (fun inp => xor c (xorFin (fun p => coeff p && vals p inp))) =
      (fun inp => f (fun p => vals p inp)) := by funext inp; exact (hfe _).symm
  rw [heq] at hw1; exact hw1

lemma addAffineVec {width M K : Nat} (gs : List Gate) (hgood : Good width gs)
    (d0 : Bool) (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) d0 (vals p))
    (fs : Fin K → (Fin M → Bool) → Bool) (hfs : ∀ i, IsAffine (fs i)) :
    ∃ (gs' : List Gate) (outs : Fin K → Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      ∀ i : Fin K, WireSpec width gs' (outs i) d0 (fun inp => fs i (fun p => vals p inp)) := by
  induction K generalizing gs with
  | zero => exact ⟨gs, fun i => i.elim0, hgood, rfl, fun _ _ _ h => h, fun i => i.elim0⟩
  | succ K ih =>
    rcases ih gs hgood hws (fun i => fs i.castSucc) (fun i => hfs i.castSucc) with
      ⟨gs1, outs1, hg1, hc1, hp1, houts1⟩
    rcases addAffineFn gs1 hg1 d0 ws vals (fun p => hp1 _ _ _ (hws p)) (fs (Fin.last K)) (hfs (Fin.last K)) with
      ⟨gs2, w2, hg2, hc2, hp2, hw2⟩
    refine ⟨gs2, fun i => if hi : i.val < K then outs1 ⟨i.val, hi⟩ else w2, hg2, by rw [hc2, hc1],
      fun w0 d0' f0 h0 => hp2 _ _ _ (hp1 _ _ _ h0), fun i => ?_⟩
    by_cases hi : i.val < K
    · dsimp only; rw [dite_pos hi]
      have hie : (⟨i.val, hi⟩ : Fin K).castSucc = i := Fin.ext rfl
      have hfe : (fun inp => fs (⟨i.val, hi⟩ : Fin K).castSucc (fun p => vals p inp)) =
          (fun inp => fs i (fun p => vals p inp)) := by rw [hie]
      rw [← hfe]; exact hp2 _ _ _ (houts1 ⟨i.val, hi⟩)
    · dsimp only; rw [dite_neg hi]
      have hie : Fin.last K = i := Fin.ext (by simp [Fin.last]; omega)
      rw [← hie]; exact hw2

lemma addAndVec {width M S : Nat} (gs : List Gate) (hgood : Good width gs)
    (ws : Fin M → Nat) (vals : Fin M → List Bool → Bool)
    (hws : ∀ p, WireSpec width gs (ws p) true (vals p))
    (A B : Fin S → (Fin M → Bool) → Bool) (hA : ∀ s, IsAffine (A s)) (hB : ∀ s, IsAffine (B s)) :
    ∃ (gs' : List Gate) (prods : Fin S → Nat),
      Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + S ∧
      (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
      ∀ s : Fin S, WireSpec width gs' (prods s) false (fun inp => A s (fun p => vals p inp) && B s (fun p => vals p inp)) := by
  induction S generalizing gs with
  | zero => exact ⟨gs, fun s => s.elim0, hgood, rfl, fun _ _ _ h => h, fun s => s.elim0⟩
  | succ S ih =>
    rcases ih gs hgood hws (fun s => A s.castSucc) (fun s => B s.castSucc)
      (fun s => hA s.castSucc) (fun s => hB s.castSucc) with ⟨gs1, p1, hg1, hc1, hp1, hsp1⟩
    rcases addAffineFn gs1 hg1 true ws vals (fun p => hp1 _ _ _ (hws p)) (A (Fin.last S)) (hA (Fin.last S)) with
      ⟨gs2, wa, hg2, hc2, hp2, hwa⟩
    rcases addAffineFn gs2 hg2 true ws vals (fun p => hp2 _ _ _ (hp1 _ _ _ (hws p))) (B (Fin.last S)) (hB (Fin.last S)) with
      ⟨gs3, wb, hg3, hc3, hp3, hwb⟩
    rcases addAnd0 gs3 hg3 (hp3 _ _ _ hwa) hwb with ⟨gs4, wp, hg4, hc4, hp4, hwp⟩
    have hp_all : ∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs4 w0 d0' f0 :=
      fun w0 d0' f0 h0 => hp4 _ _ _ (hp3 _ _ _ (hp2 _ _ _ (hp1 _ _ _ h0)))
    refine ⟨gs4, fun s => if hs : s.val < S then p1 ⟨s.val, hs⟩ else wp, hg4,
      by rw [hc4, hc3, hc2, hc1]; omega, hp_all, fun s => ?_⟩
    by_cases hs : s.val < S
    · dsimp only; rw [dite_pos hs]
      have hse : (⟨s.val, hs⟩ : Fin S).castSucc = s := Fin.ext rfl
      have hfe : (fun inp => A (⟨s.val, hs⟩ : Fin S).castSucc (fun p => vals p inp) &&
            B (⟨s.val, hs⟩ : Fin S).castSucc (fun p => vals p inp)) =
          (fun inp => A s (fun p => vals p inp) && B s (fun p => vals p inp)) := by rw [hse]
      rw [← hfe]; exact hp4 _ _ _ (hp3 _ _ _ (hp2 _ _ _ (hsp1 ⟨s.val, hs⟩)))
    · dsimp only; rw [dite_neg hs]
      have hse : Fin.last S = s := Fin.ext (by simp [Fin.last]; omega)
      rw [← hse]; exact hwp

lemma addBlock {r k n : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r) (u : Fin k → Bool)
    (gs : List Gate) (hgood : Good (n * (k + 3)) gs) (j : Fin n) :
    ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
      Good (n * (k + 3)) gs' ∧
      gs'.countP nonlinear = gs.countP nonlinear + targetCount r ∧
      (∀ w0 d0' f0, WireSpec (n * (k + 3)) gs w0 d0' f0 → WireSpec (n * (k + 3)) gs' w0 d0' f0) ∧
      (∀ i : Fin k, tapJ i < n * (k + 3) + gs'.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (i : Fin k),
        (Circuit.wires ⟨gs', 0⟩ (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tapJ i) false = x j i := by
  let width := n * (k + 3)
  let baseW : Fin (k + 3) → Nat := fun p => j.val * (k + 3) + p.val
  let baseVals : Fin (k + 3) → List Bool → Bool := fun p inp => inp.getD (baseW p) false
  have hbase_lt : ∀ p : Fin (k + 3), baseW p < width := fun p => by
    dsimp [baseW, width]
    have : (j.val + 1) * (k + 3) ≤ n * (k + 3) := Nat.mul_le_mul_right (k + 3) j.isLt
    rw [Nat.succ_mul] at this; omega
  have hbase_spec : ∀ p : Fin (k + 3), WireSpec width gs (baseW p) true (baseVals p) := by
    intro p

    have h0 : ∀ (gs0 : List Gate), Good width gs0 → WireSpec width gs0 (baseW p) true (baseVals p) := by
      intro gs0
      induction gs0 using List.reverseRecOn with
      | nil => intro _; exact wireSpec_input width (baseW p) (hbase_lt p)
      | append_singleton gs0 g ih =>
        intro hg0
        have hgs0 : Good width gs0 := by
          refine ⟨fun j0 hj0 i0 hi0 => ?_, fun g' hg' => hg0.2.1 g' (List.mem_append_left _ hg'), ?_⟩
          · change j0 < gs0.length at hj0
            have h1 := hg0.1 j0 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            have hga : gateAt ⟨gs0 ++ [g], 0⟩ j0 = gateAt ⟨gs0, 0⟩ j0 := by unfold gateAt; exact getD_append_lt gs0 g _ hj0
            rw [hga] at h1; exact h1 i0 hi0
          · rw [foldr_max_le_iff]; intro x hx
            have hstep : depthList width (gs0 ++ [g]) =
                depthList width gs0 ++ [(g.inputs.map (fun a => (depthList width gs0).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
              unfold depthList; rw [List.foldl_append]; rfl
            exact (foldr_max_le_iff _ _).mp hg0.2.2 x (by rw [hstep]; exact List.mem_append_left _ hx)
        have hrb_g : ∀ i ∈ g.inputs, i < width + gs0.length := by
          have h1 := hg0.1 gs0.length (by simp)
          have hga : gateAt ⟨gs0 ++ [g], 0⟩ gs0.length = g := by unfold gateAt; exact getD_append_eq gs0 g _
          rw [hga] at h1; exact h1
        have hdg : (g.inputs.map (fun a => (depthList width gs0).getD a 0)).foldr max 0 + (nonlinear g).toNat ≤ 1 := by
          have hstep : depthList width (gs0 ++ [g]) =
              depthList width gs0 ++ [(g.inputs.map (fun a => (depthList width gs0).getD a 0)).foldr max 0 + (nonlinear g).toNat] := by
            unfold depthList; rw [List.foldl_append]; rfl
          exact (foldr_max_le_iff _ _).mp hg0.2.2 _ (by rw [hstep]; exact List.mem_append_right _ List.mem_cons_self)
        exact (append_gate gs0 hgs0 g (hg0.2.1 g (List.mem_append_right _ List.mem_cons_self)) hrb_g hdg).2.2.1 _ _ _ (ih hgs0)
    exact h0 gs hgood

  let S := targetCount r
  have hS_ge2 : 2 ≤ S := by unfold S targetCount; split_ifs <;> omega
  let dOf : (Fin (k + 3) → Bool) → (Fin k → Bool) := fun v i => v ⟨i.val, by omega⟩
  let tOf : (Fin (k + 3) → Bool) → (Fin k → Bool) := fun v => tOfD hr hk3 (dOf v)
  have htOf_aff : ∀ i : Fin k, IsAffine (fun v : Fin (k + 3) → Bool => tOf v i) := fun i =>
    isAffine_comp (isAffine_tOfD hr hk3 i) (fun q => isAffine_coord ⟨q.val, by omega⟩)
  have htExt_aff0 : ∀ i : Fin k, IsAffine (fun ve : Fin (k + 3 + S) → Bool => tOf (fun q => ve ⟨q.val, by omega⟩) i) := fun i =>
    isAffine_comp (f := fun v => tOf v i) (g := fun ve q => ve ⟨q.val, by omega⟩) (htOf_aff i) (fun q => isAffine_coord ⟨q.val, by omega⟩)

  have hbuild : ∀ (A B : Fin S → (Fin (k + 3) → Bool) → Bool),
      (∀ s, IsAffine (A s)) → (∀ s, IsAffine (B s)) →
      (∀ v, (A ⟨0, by omega⟩ v && B ⟨0, by omega⟩ v) = Q0 hr hk3 (tOf v)) →
      (∀ v, (A ⟨1, by omega⟩ v && B ⟨1, by omega⟩ v) = Qk hr hk3 (tOf v)) →
      (∃ (QpAff : (Fin (k + 3 + S) → Bool) → Bool),
        IsAffine QpAff ∧
        ∀ (x : Fin k → Bool),
          let v : Fin (k + 3) → Bool := fun p => (recordFn hk r u x).getD p.val false
          let vext : Fin (k + 3 + S) → Bool := fun p =>
            if hp : p.val < k + 3 then v ⟨p.val, hp⟩
            else A ⟨p.val - (k + 3), by omega⟩ v && B ⟨p.val - (k + 3), by omega⟩ v
          QpAff vext = Qp hk r (tOf v)) →
      ∃ (gs' : List Gate) (tapJ : Fin k → Nat),
        Good width gs' ∧ gs'.countP nonlinear = gs.countP nonlinear + S ∧
        (∀ w0 d0' f0, WireSpec width gs w0 d0' f0 → WireSpec width gs' w0 d0' f0) ∧
        (∀ i : Fin k, tapJ i < width + gs'.length) ∧
        ∀ (x : Fin n → Fin k → Bool) (i : Fin k),
          (Circuit.wires ⟨gs', 0⟩ (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tapJ i) false = x j i := by
    intro A B hA hB hQ0 hQk ⟨QpAff, hQpAff, hQp_eq⟩
    rcases addAndVec gs hgood baseW baseVals hbase_spec A B hA hB with ⟨gs1, prods, hg1, hc1, hp1, hprods⟩
    let extW : Fin (k + 3 + S) → Nat := fun p =>
      if hp : p.val < k + 3 then baseW ⟨p.val, hp⟩ else prods ⟨p.val - (k + 3), by omega⟩
    let extVals : Fin (k + 3 + S) → List Bool → Bool := fun p inp =>
      if hp : p.val < k + 3 then baseVals ⟨p.val, hp⟩ inp
      else A ⟨p.val - (k + 3), by omega⟩ (fun q => baseVals q inp) &&
           B ⟨p.val - (k + 3), by omega⟩ (fun q => baseVals q inp)
    have hext_spec : ∀ p : Fin (k + 3 + S), WireSpec width gs1 (extW p) false (extVals p) := by
      intro p; unfold extW extVals
      by_cases hp : p.val < k + 3
      · rw [dite_pos hp]
        have hs := hp1 _ _ _ (hbase_spec ⟨p.val, hp⟩)
        refine ⟨hs.1, (fun h => by cases h), fun inp hlen => ?_⟩
        dsimp only; rw [dite_pos hp]; exact hs.2.2 inp hlen
      · rw [dite_neg hp]
        have hs := hprods ⟨p.val - (k + 3), by omega⟩
        refine ⟨hs.1, (fun h => by cases h), fun inp hlen => ?_⟩
        dsimp only; rw [dite_neg hp]; exact hs.2.2 inp hlen

    let vOfExt : (Fin (k + 3 + S) → Bool) → (Fin (k + 3) → Bool) := fun ve q => ve ⟨q.val, by omega⟩
    let tExt : (Fin (k + 3 + S) → Bool) → Fin k → Bool := fun ve => tOf (vOfExt ve)
    let bExt : (Fin (k + 3 + S) → Bool) → Bool := fun ve =>
      xor (ve ⟨k, by omega⟩) (xor (QpAff ve) (linP hk r u (tExt ve)))
    let x0Ext : (Fin (k + 3 + S) → Bool) → Bool := fun ve =>
      xor (ve ⟨k + 1, by omega⟩) (xor (tExt ve ⟨0, hk⟩) (ve ⟨k + 3, by omega⟩))
    let xkExt : (Fin (k + 3 + S) → Bool) → Bool := fun ve =>
      xor (ve ⟨k + 2, by omega⟩) (xor (bExt ve) (xor (tExt ve ⟨k - 1, by omega⟩) (ve ⟨k + 3 + 1, by omega⟩)))
    let wExt : (Fin (k + 3 + S) → Bool) → Fin k → Bool := fun ve i =>
      xor (tExt ve i) (bExt ve && decide (3 ≤ i.val))
    let recExt : Fin k → (Fin (k + 3 + S) → Bool) → Bool := fun i ve =>
      xor (zOf (wExt ve) (xor (xkExt ve) (u ⟨0, hk⟩)) (xor (x0Ext ve) (u ⟨1, by omega⟩)) (ix hk (i.val + 1)))
          (u (ix hk (i.val + 1)))
    have htExt_aff : ∀ i, IsAffine (fun ve => tExt ve i) := fun i => htExt_aff0 i
    have hbExt_aff : IsAffine bExt :=
      isAffine_xor (isAffine_coord _) (isAffine_xor hQpAff (isAffine_linP hk u tExt htExt_aff))
    have hx0Ext_aff : IsAffine x0Ext :=
      isAffine_xor (isAffine_coord _) (isAffine_xor (htExt_aff _) (isAffine_coord _))
    have hxkExt_aff : IsAffine xkExt :=
      isAffine_xor (isAffine_coord _) (isAffine_xor hbExt_aff (isAffine_xor (htExt_aff _) (isAffine_coord _)))
    have hwExt_aff : ∀ i, IsAffine (fun ve => wExt ve i) := fun i => by
      unfold wExt
      have h1 : IsAffine (fun ve => bExt ve && decide (3 ≤ i.val)) := by
        cases decide (3 ≤ i.val)
        · simpa using isAffine_const false
        · simpa using hbExt_aff
      exact isAffine_xor (htExt_aff i) h1
    have hrec_aff : ∀ i, IsAffine (recExt i) := fun i =>
      isAffine_xor (isAffine_zOf wExt (fun ve => xor (xkExt ve) (u ⟨0, hk⟩)) (fun ve => xor (x0Ext ve) (u ⟨1, by omega⟩))
        hwExt_aff (isAffine_xor hxkExt_aff (isAffine_const _)) (isAffine_xor hx0Ext_aff (isAffine_const _)) _)
        (isAffine_const _)
    rcases addAffineVec gs1 hg1 false extW extVals hext_spec recExt hrec_aff with ⟨gs2, tapJ, hg2, hc2, hp2, htapJ⟩
    refine ⟨gs2, tapJ, hg2, by rw [hc2, hc1], fun w0 d0' f0 h0 => hp2 _ _ _ (hp1 _ _ _ h0),
      fun i => (htapJ i).1, fun x i => ?_⟩
    let inp := (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten
    have hinp_len : inp.length = width := flatten_ofFn_length _ (fun j' => recordFn_length hk r u (x j'))
    rw [(htapJ i).2.2 inp hinp_len]
    have hbase_eq : ∀ p : Fin (k + 3), baseVals p inp = (recordFn hk r u (x j)).getD p.val false := fun p =>
      flatten_ofFn_getD (fun j' => recordFn hk r u (x j')) (fun j' => recordFn_length hk r u (x j')) j p
    let v : Fin (k + 3) → Bool := fun p => (recordFn hk r u (x j)).getD p.val false
    have hv_eq : (fun p : Fin (k + 3) => baseVals p inp) = v := funext hbase_eq
    have hd_eq : dOf v = diffFn hk u (x j) := by
      funext q; exact recordFn_getD_lt hk r u (x j) q.val q.isLt
    have ht_eq : tOf v = tOfD hr hk3 (diffFn hk u (x j)) := by unfold tOf; rw [hd_eq]
    let ve : Fin (k + 3 + S) → Bool := fun p => extVals p inp
    have hve_v : vOfExt ve = v := by
      funext q; unfold vOfExt ve extVals; dsimp only; rw [dite_pos q.isLt, hbase_eq q]
    have hve_eq : ve = (fun p : Fin (k + 3 + S) =>
        if hp : p.val < k + 3 then v ⟨p.val, hp⟩
        else A ⟨p.val - (k + 3), by omega⟩ v && B ⟨p.val - (k + 3), by omega⟩ v) := by
      funext p; unfold ve extVals; split_ifs with hp
      · exact hbase_eq ⟨p.val, hp⟩
      · rw [hv_eq]
    have hq0_v : ve ⟨k + 3, by omega⟩ = Q0 hr hk3 (tOf v) := by
      rw [hve_eq]; dsimp only; rw [dite_neg (by omega)]
      have hidx : (⟨k + 3 - (k + 3), by omega⟩ : Fin S) = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hidx]; exact hQ0 v
    have hqk_v : ve ⟨k + 3 + 1, by omega⟩ = Qk hr hk3 (tOf v) := by
      rw [hve_eq]; dsimp only; rw [dite_neg (by omega)]
      have hidx : (⟨k + 3 + 1 - (k + 3), by omega⟩ : Fin S) = ⟨1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hidx]; exact hQk v
    have hqp_v : QpAff ve = Qp hk r (tOf v) := by rw [hve_eq]; exact hQp_eq (x j)
    have hvk : ve ⟨k, by omega⟩ = decide (((neededSet r k).filter (fun q => row hk u (x j) q = true)).card % 2 = 1) := by
      rw [hve_eq]; dsimp only; rw [dite_pos (by omega)]; exact recordFn_getD_k hk r u (x j)
    have hvk1 : ve ⟨k + 1, by omega⟩ = row hk u (x j) ⟨0, hk⟩ := by
      rw [hve_eq]; dsimp only; rw [dite_pos (by omega)]; exact recordFn_getD_k1 hk r u (x j)
    have hvk2 : ve ⟨k + 2, by omega⟩ = row hk u (x j) ⟨k - 1, by omega⟩ := by
      rw [hve_eq]; dsimp only; rw [dite_pos (by omega)]; exact recordFn_getD_k2 hk r u (x j)
    change recExt i ve = x j i
    unfold recExt wExt x0Ext xkExt bExt tExt
    rw [hve_v, hq0_v, hqk_v, hqp_v, hvk, hvk1, hvk2, ht_eq]
    exact (recovery_from_record hk hr hk3 u (x j) i).symm

  by_cases hr2 : r = 2
  · have hS2 : S = 2 := by unfold S targetCount; rw [ite_pos hr2]
    let A : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
      if s.val = 0 then !(tOf v ⟨1, by omega⟩) else !(tOf v ⟨0, hk⟩)
    let B : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
      if s.val = 0 then tOf v ⟨2, by omega⟩ else tOf v ⟨1, by omega⟩
    exact hbuild A B
      (fun s => by unfold A; split_ifs <;> exact isAffine_not (htOf_aff _))
      (fun s => by unfold B; split_ifs <;> exact htOf_aff _)
      (fun v => by simp [A, B, Q0]) (fun v => by simp [A, B, Qk])
      ⟨fun ve => tOf (fun q => ve ⟨q.val, by omega⟩) ⟨0, hk⟩,
        htExt_aff0 ⟨0, hk⟩,
        fun x => by
          intro v vext
          have hve_v : (fun q : Fin (k + 3) => vext ⟨q.val, by omega⟩) = v := by
            funext q; dsimp only [vext]; rw [dite_pos q.isLt]
          dsimp only; rw [hve_v]
          have hd_eq : dOf v = diffFn hk u x := by
            funext q; exact recordFn_getD_lt hk r u x q.val q.isLt
          have ht_eq : tOf v = tOfD hr hk3 (diffFn hk u x) := by unfold tOf; rw [hd_eq]
          rw [ht_eq]
          have htd := tOfD_diff hk hr hk3 u x
          exact (Qp_r2 hk hr2 hk3 _ htd.1 htd.2.2.1 htd.2.2.2).symm⟩
  · by_cases hr3 : r = 3
    · have hS4 : S = 4 := by unfold S targetCount; rw [ite_neg hr2, ite_pos hr3]
      let A : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
        if s.val = 0 then !(tOf v ⟨1, by omega⟩)
        else if s.val = 1 then !(tOf v ⟨0, hk⟩)
        else if s.val = 2 then xor (tOf v ⟨5, by omega⟩) (xor (tOf v ⟨6, by omega⟩) (tOf v ⟨7, by omega⟩))
        else xor (tOf v ⟨4, by omega⟩) (tOf v ⟨6, by omega⟩)
      let B : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
        if s.val = 0 then tOf v ⟨2, by omega⟩
        else if s.val = 1 then tOf v ⟨1, by omega⟩
        else if s.val = 2 then xor (tOf v ⟨0, hk⟩) (xor (tOf v ⟨4, by omega⟩) (tOf v ⟨7, by omega⟩))
        else xor (tOf v ⟨2, by omega⟩) (xor (tOf v ⟨6, by omega⟩) (tOf v ⟨7, by omega⟩))
      exact hbuild A B
        (fun s => by
          unfold A; split_ifs
          · exact isAffine_not (htOf_aff _)
          · exact isAffine_not (htOf_aff _)
          · exact isAffine_xor (htOf_aff _) (isAffine_xor (htOf_aff _) (htOf_aff _))
          · exact isAffine_xor (htOf_aff _) (htOf_aff _))
        (fun s => by
          unfold B; split_ifs
          · exact htOf_aff _
          · exact htOf_aff _
          · exact isAffine_xor (htOf_aff _) (isAffine_xor (htOf_aff _) (htOf_aff _))
          · exact isAffine_xor (htOf_aff _) (isAffine_xor (htOf_aff _) (htOf_aff _)))
        (fun v => by simp [A, B, Q0]) (fun v => by simp [A, B, Qk])
        ⟨fun ve => xor (ve ⟨k + 3, by omega⟩)
            (xor (ve ⟨k + 3 + 2, by omega⟩)
              (xor (ve ⟨k + 3 + 3, by omega⟩)
                (xor (tOf (fun q => ve ⟨q.val, by omega⟩) ⟨0, hk⟩)
                     (tOf (fun q => ve ⟨q.val, by omega⟩) ⟨4, by omega⟩)))),
          isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _) (isAffine_xor (isAffine_coord _)
            (isAffine_xor (htExt_aff0 _) (htExt_aff0 _)))),
          fun x => by
            intro v vext
            have hve_v : (fun q : Fin (k + 3) => vext ⟨q.val, by omega⟩) = v := by
              funext q; dsimp only [vext]; rw [dite_pos q.isLt]
            have hv0 : vext ⟨k + 3, by omega⟩ = (!(tOf v ⟨1, by omega⟩) && tOf v ⟨2, by omega⟩) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B]
            have hv2 : vext ⟨k + 3 + 2, by omega⟩ =
                (xor (tOf v ⟨5, by omega⟩) (xor (tOf v ⟨6, by omega⟩) (tOf v ⟨7, by omega⟩)) &&
                 xor (tOf v ⟨0, hk⟩) (xor (tOf v ⟨4, by omega⟩) (tOf v ⟨7, by omega⟩))) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B, show k + 3 + 2 - (k + 3) = 2 by omega]
            have hv3 : vext ⟨k + 3 + 3, by omega⟩ =
                (xor (tOf v ⟨4, by omega⟩) (tOf v ⟨6, by omega⟩) &&
                 xor (tOf v ⟨2, by omega⟩) (xor (tOf v ⟨6, by omega⟩) (tOf v ⟨7, by omega⟩))) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B, show k + 3 + 3 - (k + 3) = 3 by omega]
            have hd_eq : dOf v = diffFn hk u x := by
              funext q; exact recordFn_getD_lt hk r u x q.val q.isLt
            have ht_eq : tOf v = tOfD hr hk3 (diffFn hk u x) := by unfold tOf; rw [hd_eq]
            have htd := tOfD_diff hk hr hk3 u x
            have hq3 := Qp_r3 hk hr3 hk3 _ htd.1 htd.2.2.1 htd.2.2.2
            unfold Q0 at hq3
            dsimp only
            rw [hve_v, hv0, hv2, hv3, ht_eq]
            exact hq3.symm⟩
    ·
      have hr4 : 4 ≤ r := by omega
      have hSr : S = r + 2 := by unfold S targetCount; rw [ite_neg hr2, ite_neg hr3]
      let A : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
        if s.val = 0 then !(tOf v ⟨1, by omega⟩)
        else if s.val = 1 then !(tOf v ⟨0, hk⟩)
        else if s.val = 2 then !(tOf v ⟨4, by omega⟩)
        else if s.val = 3 then !(tOf v ⟨k - 1, by omega⟩)
        else tOf v ⟨3 * (s.val - 4 + 2) + 1, by omega⟩
      let B : Fin S → (Fin (k + 3) → Bool) → Bool := fun s v =>
        if s.val = 0 then tOf v ⟨2, by omega⟩
        else if s.val = 1 then tOf v ⟨1, by omega⟩
        else if s.val = 2 then tOf v ⟨5, by omega⟩
        else if s.val = 3 then tOf v ⟨0, hk⟩
        else !(xor (tOf v ⟨3 * (s.val - 4 + 2), by omega⟩) (tOf v ⟨3 * (s.val - 4 + 2) + 2, by omega⟩))
      exact hbuild A B
        (fun s => by
          unfold A; split_ifs
          · exact isAffine_not (htOf_aff _)
          · exact isAffine_not (htOf_aff _)
          · exact isAffine_not (htOf_aff _)
          · exact isAffine_not (htOf_aff _)
          · exact htOf_aff _)
        (fun s => by
          unfold B; split_ifs
          · exact htOf_aff _
          · exact htOf_aff _
          · exact htOf_aff _
          · exact htOf_aff _
          · exact isAffine_not (isAffine_xor (htOf_aff _) (htOf_aff _)))
        (fun v => by simp [A, B, Q0]) (fun v => by simp [A, B, Qk])
        ⟨fun ve =>
            let tv := tOf (fun q => ve ⟨q.val, by omega⟩)
            xor (if r % 2 = 0 then xor (ve ⟨k + 3, by omega⟩) (ve ⟨k + 3 + 1, by omega⟩) else false)
              (xor (xor (tv ⟨4, by omega⟩) (ve ⟨k + 3 + 2, by omega⟩))
                (xor (ve ⟨k + 3 + 3, by omega⟩)
                  (xorFin (fun idx : Fin (r - 2) =>
                    xor (ve ⟨k + 3 + 4 + idx.val, by omega⟩) (tv ⟨3 * (idx.val + 2) + 2, by omega⟩))))),
          by
            apply isAffine_xor
            · by_cases he : r % 2 = 0
              · rw [show (fun y : Fin (k + 3 + S) → Bool => if r % 2 = 0 then xor (y ⟨k + 3, by omega⟩) (y ⟨k + 3 + 1, by omega⟩) else false) =
                    (fun y => xor (y ⟨k + 3, by omega⟩) (y ⟨k + 3 + 1, by omega⟩)) from funext fun _ => ite_pos he]
                exact isAffine_xor (isAffine_coord _) (isAffine_coord _)
              · rw [show (fun y : Fin (k + 3 + S) → Bool => if r % 2 = 0 then xor (y ⟨k + 3, by omega⟩) (y ⟨k + 3 + 1, by omega⟩) else false) =
                    (fun _ => false) from funext fun _ => ite_neg he]
                exact isAffine_const false
            · apply isAffine_xor
              · exact isAffine_xor (htExt_aff0 _) (isAffine_coord _)
              · exact isAffine_xor (isAffine_coord _)
                  (isAffine_xorFin _ (fun idx => isAffine_xor (isAffine_coord _) (htExt_aff0 _))),
          fun x => by
            intro v vext
            have hve_v : (fun q : Fin (k + 3) => vext ⟨q.val, by omega⟩) = v := by
              funext q; dsimp only [vext]; rw [dite_pos q.isLt]
            have hd_eq : dOf v = diffFn hk u x := by
              funext q; exact recordFn_getD_lt hk r u x q.val q.isLt
            have ht_eq : tOf v = tOfD hr hk3 (diffFn hk u x) := by unfold tOf; rw [hd_eq]
            have hv0 : vext ⟨k + 3, by omega⟩ = (!(tOf v ⟨1, by omega⟩) && tOf v ⟨2, by omega⟩) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B]
            have hv1 : vext ⟨k + 3 + 1, by omega⟩ = (!(tOf v ⟨0, hk⟩) && tOf v ⟨1, by omega⟩) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B, show k + 3 + 1 - (k + 3) = 1 by omega]
            have hv2 : vext ⟨k + 3 + 2, by omega⟩ = (!(tOf v ⟨4, by omega⟩) && tOf v ⟨5, by omega⟩) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B, show k + 3 + 2 - (k + 3) = 2 by omega]
            have hv3 : vext ⟨k + 3 + 3, by omega⟩ = (!(tOf v ⟨k - 1, by omega⟩) && tOf v ⟨0, hk⟩) := by
              dsimp only [vext]; rw [dite_neg (by omega)]; simp [A, B, show k + 3 + 3 - (k + 3) = 3 by omega]
            have hvmid : ∀ idx : Fin (r - 2),
                vext ⟨k + 3 + 4 + idx.val, by omega⟩ =
                (tOf v ⟨3 * (idx.val + 2) + 1, by omega⟩ &&
                  !(xor (tOf v ⟨3 * (idx.val + 2), by omega⟩) (tOf v ⟨3 * (idx.val + 2) + 2, by omega⟩))) := by
              intro idx; dsimp only [vext]; rw [dite_neg (by omega)]; unfold A B; dsimp only
              rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
              congr 1
              · exact congrArg (tOf v) (Fin.ext (by dsimp only; omega))
              · congr 1; congr 1
                · exact congrArg (tOf v) (Fin.ext (by dsimp only; omega))
                · exact congrArg (tOf v) (Fin.ext (by dsimp only; omega))
            have htd := tOfD_diff hk hr hk3 u x
            dsimp only
            rw [hve_v, hv2, hv3]
            have hqp := Qp_eq_QpMid hk hr hk3 (tOfD hr hk3 (diffFn hk u x)) htd.1
            rw [← ht_eq] at hqp
            rw [hqp]
            unfold Q0 Qk QpMid
            congr 1
            · by_cases he : r % 2 = 0
              · rw [ite_pos he, ite_pos he, hv0, hv1]
              · rw [ite_neg he, ite_neg he]
            · congr 1; congr 1; apply xorFin_congr; intro idx; rw [hvmid idx]⟩

theorem upper_bound {r k : Nat} (hk : 0 < k) (hr : 2 ≤ r) (hk3 : k = 3 * r)
    (u : Fin k → Bool) (n t : Nat) (ht : n * targetCount r ≤ t) :
    ∃ (C : Circuit) (tap : Fin n → Fin k → Nat),
      valid (n * (k + 3)) C ∧ depth (n * (k + 3)) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t ∧
      (∀ j i, tap j i < n * (k + 3) + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        (C.wires (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tap j i) false = x j i := by
  let width := n * (k + 3)
  suffices ∀ m (hm : m ≤ n),
      ∃ (gs : List Gate) (tap : Fin m → Fin k → Nat),
        Good width gs ∧ gs.countP nonlinear = m * targetCount r ∧
        (∀ j : Fin m, ∀ i : Fin k, tap j i < width + gs.length) ∧
        ∀ (x : Fin n → Fin k → Bool) (j : Fin m) (i : Fin k),
          (Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tap j i) false =
            x ⟨j.val, by omega⟩ i by
    rcases this n (le_refl n) with ⟨gs, tap, hgood, hcnt, htap, hcomp⟩
    exact ⟨⟨gs, 0⟩, tap, ⟨hgood.1, hgood.2.1⟩, hgood.2.2, by dsimp only; omega, htap, hcomp⟩
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], fun j => j.elim0, good_nil width, by simp, fun j => j.elim0, fun _ j => j.elim0⟩
  | succ m ih =>
    intro hm
    rcases ih (by omega) with ⟨gs1, tap1, hg1, hc1, htap1, hcomp1⟩
    rcases addBlock hk hr hk3 u gs1 hg1 ⟨m, by omega⟩ with ⟨gs2, tapM, hg2, hc2, hp2, htapM, hcompM⟩

    have hpres_tap : ∀ (x : Fin n → Fin k → Bool) (j : Fin m) (i : Fin k),
        (Circuit.wires ⟨gs2, 0⟩ (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten).getD (tap1 j i) false =
          x ⟨j.val, by omega⟩ i := by
      intro x j i
      let inp := (List.ofFn (fun j' : Fin n => recordFn hk r u (x j'))).flatten
      have hlen : inp.length = width := flatten_ofFn_length _ (fun j' => recordFn_length hk r u (x j'))
      have hws : WireSpec width gs1 (tap1 j i) false (fun inp' => (Circuit.wires ⟨gs1, 0⟩ inp').getD (tap1 j i) false) :=
        ⟨htap1 j i, (fun h => by cases h), fun _ _ => rfl⟩
      rw [(hp2 _ _ _ hws).2.2 inp hlen]
      exact hcomp1 x j i
    have hpres_lt : ∀ (j : Fin m) (i : Fin k), tap1 j i < width + gs2.length := fun j i =>
      (hp2 (tap1 j i) false (fun inp' => (Circuit.wires ⟨gs1, 0⟩ inp').getD (tap1 j i) false)
        ⟨htap1 j i, (fun h => by cases h), fun _ _ => rfl⟩).1
    refine ⟨gs2, fun j i => if hj : j.val < m then tap1 ⟨j.val, hj⟩ i else tapM i, hg2,
      by rw [hc2, hc1, Nat.succ_mul], fun j i => ?_, fun x j i => ?_⟩
    · by_cases hj : j.val < m
      · dsimp only; rw [dite_pos hj]; exact hpres_lt ⟨j.val, hj⟩ i
      · dsimp only; rw [dite_neg hj]; exact htapM i
    · by_cases hj : j.val < m
      · dsimp only; rw [dite_pos hj]; exact hpres_tap x ⟨j.val, hj⟩ i
      · dsimp only; rw [dite_neg hj]
        have hjm : (⟨m, by omega⟩ : Fin n) = ⟨j.val, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [← hjm]; exact hcompM x i

end PEqualNP.Outside.L_meta_42687_aux

theorem PEqualNP.Outside.L_meta_42687 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2
  let depth := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (C.gates.foldl (fun (ds : List Nat) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate w 0)).foldr max 0
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
      let record := fun (x : W) => List.ofFn (diff x) ++
        [decide ((needed.filter (fun i => base x i)).card % 2 = 1), base x (ix 0), base x (ix (k-1))]
      ∀ (n t : Nat),
        let width := n*(k+3)
        let U := Fin n → W
        let data := fun (x : U) => (List.ofFn (fun j : Fin n => record (x j))).flatten
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin k → Nat),
          valid width C ∧ depth width C ≤ 1 ∧ C.gates.countP nonlinear ≤ t ∧
          (∀ j i, tap j i < width+C.gates.length) ∧
          ∀ (x : U) (j : Fin n) (i : Fin k), (C.wires (data x)).getD (tap j i) false = x j i) ↔
        n*(if r = 2 then 2 else if r = 3 then 4 else r+2) ≤ t := by
  intro nonlinear valid depth r k hk hr hk3 W ix add mix rot chi row v u base diff needed record n t width U data
  constructor
  · rintro ⟨C, tap, hval, hdep, hcnt, htap, hcomp⟩
    exact PEqualNP.Outside.L_meta_42687_aux.lower_bound hk hr hk3 u n t C tap hval hdep hcnt htap hcomp
  · intro ht
    exact PEqualNP.Outside.L_meta_42687_aux.upper_bound hk hr hk3 u n t ht
