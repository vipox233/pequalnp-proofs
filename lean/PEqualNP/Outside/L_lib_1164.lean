import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1164_aux

lemma mod_add_left_cancel {M a b c : Nat} (hb : b < M) (hc : c < M)
    (h : (a + b) % M = (a + c) % M) : b = c := by
  have ha : a % M < M := Nat.mod_lt a (by omega)
  have h1 : (a % M + b) % M = (a % M + c) % M := by
    calc (a % M + b) % M = (a + b) % M := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      _ = (a + c) % M := h
      _ = (a % M + c) % M := by symm; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hb' : (a % M + b) % M = if a % M + b < M then a % M + b else a % M + b - M := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hc' : (a % M + c) % M = if a % M + c < M then a % M + c else a % M + c - M := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hb', hc'] at h1
  split_ifs at h1 <;> omega

lemma mod_add_right_cancel {M a b c : Nat} (ha : a < M) (hb : b < M)
    (h : (a + c) % M = (b + c) % M) : a = b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact mod_add_left_cancel ha hb h

def addF {m : Nat} (a b : Fin (m + 1)) : Fin (m + 1) :=
  ⟨(a.val + b.val) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

def negF {m : Nat} (a : Fin (m + 1)) : Fin (m + 1) :=
  ⟨(m + 1 - a.val) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

def subF {m : Nat} (a b : Fin (m + 1)) : Fin (m + 1) :=
  addF a (negF b)

def zeroF {m : Nat} : Fin (m + 1) :=
  ⟨0, Nat.succ_pos m⟩

lemma addF_assoc {m : Nat} (a b c : Fin (m + 1)) :
    addF (addF a b) c = addF a (addF b c) := by
  apply Fin.ext
  dsimp [addF]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
  symm
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma addF_comm {m : Nat} (a b : Fin (m + 1)) :
    addF a b = addF b a := by
  apply Fin.ext
  dsimp [addF]
  rw [Nat.add_comm]

lemma addF_zero {m : Nat} (a : Fin (m + 1)) :
    addF a zeroF = a := by
  apply Fin.ext
  dsimp [addF, zeroF]
  exact Nat.mod_eq_of_lt a.isLt

lemma addF_negF {m : Nat} (a : Fin (m + 1)) :
    addF a (negF a) = zeroF := by
  apply Fin.ext
  dsimp [addF, negF, zeroF]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hle : a.val ≤ m + 1 := Nat.le_of_lt a.isLt
  rw [Nat.add_sub_of_le hle, Nat.mod_self]

lemma addF_subF {m : Nat} (a b : Fin (m + 1)) :
    addF b (subF a b) = a := by
  dsimp [subF]
  rw [addF_comm a (negF b), ← addF_assoc, addF_negF, addF_comm, addF_zero]

lemma subF_addF {m : Nat} (a b : Fin (m + 1)) :
    subF (addF b a) b = a := by
  dsimp [subF]
  rw [addF_comm b a, addF_assoc, addF_negF, addF_zero]

def zeroX {m n : Nat} : Fin n → Fin (m + 1) :=
  fun _ => zeroF

def addX {m n : Nat} (x y : Fin n → Fin (m + 1)) : Fin n → Fin (m + 1) :=
  fun i => addF (x i) (y i)

def negX {m n : Nat} (x : Fin n → Fin (m + 1)) : Fin n → Fin (m + 1) :=
  fun i => negF (x i)

def subX {m n : Nat} (x y : Fin n → Fin (m + 1)) : Fin n → Fin (m + 1) :=
  fun i => subF (x i) (y i)

lemma addX_assoc {m n : Nat} (x y z : Fin n → Fin (m + 1)) :
    addX (addX x y) z = addX x (addX y z) := by
  funext i; exact addF_assoc (x i) (y i) (z i)

lemma addX_comm {m n : Nat} (x y : Fin n → Fin (m + 1)) :
    addX x y = addX y x := by
  funext i; exact addF_comm (x i) (y i)

lemma addX_zero {m n : Nat} (x : Fin n → Fin (m + 1)) :
    addX x zeroX = x := by
  funext i; exact addF_zero (x i)

lemma addX_subX {m n : Nat} (x y : Fin n → Fin (m + 1)) :
    addX y (subX x y) = x := by
  funext i; exact addF_subF (x i) (y i)

lemma subX_addX {m n : Nat} (x y : Fin n → Fin (m + 1)) :
    subX (addX y x) y = x := by
  funext i; exact subF_addF (x i) (y i)

lemma addX_left_inj {m n : Nat} (x₀ : Fin n → Fin (m + 1)) :
    Function.Injective (addX x₀) := by
  intro u v h
  have := congrArg (fun z => subX z x₀) h
  rwa [subX_addX, subX_addX] at this

def dotOf {m n : Nat} (a x : Fin n → Fin (m + 1)) : Nat :=
  (Finset.univ : Finset (Fin n)).sum (fun i => (a i).val * (x i).val) % (m + 1)

lemma dotOf_lt {m n : Nat} (a x : Fin n → Fin (m + 1)) :
    dotOf a x < m + 1 :=
  Nat.mod_lt _ (Nat.succ_pos m)

lemma dotOf_zero {m n : Nat} (a : Fin n → Fin (m + 1)) :
    dotOf a zeroX = 0 := by
  simp [dotOf, zeroX, zeroF]

lemma sum_mul_addF_mod {m n : Nat} (a x y : Fin n → Fin (m + 1)) (S : Finset (Fin n)) :
    (S.sum (fun i => (a i).val * (addF (x i) (y i)).val)) % (m + 1) =
    (S.sum (fun i => (a i).val * (x i).val) + S.sum (fun i => (a i).val * (y i).val)) % (m + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    have hterm : ((a j).val * (addF (x j) (y j)).val) % (m + 1) =
        ((a j).val * (x j).val + (a j).val * (y j).val) % (m + 1) := by
      dsimp [addF]
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add]
    calc
      ((a j).val * (addF (x j) (y j)).val + S.sum (fun i => (a i).val * (addF (x i) (y i)).val)) % (m + 1)
          = (((a j).val * (addF (x j) (y j)).val) % (m + 1) +
             (S.sum (fun i => (a i).val * (addF (x i) (y i)).val)) % (m + 1)) % (m + 1) := Nat.add_mod _ _ _
      _ = (((a j).val * (x j).val + (a j).val * (y j).val) % (m + 1) +
           (S.sum (fun i => (a i).val * (x i).val) + S.sum (fun i => (a i).val * (y i).val)) % (m + 1)) % (m + 1) := by
            rw [hterm, ih]
      _ = (((a j).val * (x j).val + (a j).val * (y j).val) +
           (S.sum (fun i => (a i).val * (x i).val) + S.sum (fun i => (a i).val * (y i).val))) % (m + 1) := by
            rw [← Nat.add_mod]
      _ = ((a j).val * (x j).val + S.sum (fun i => (a i).val * (x i).val) +
           ((a j).val * (y j).val + S.sum (fun i => (a i).val * (y i).val))) % (m + 1) := by
            congr 1; omega

lemma dotOf_add {m n : Nat} (a x y : Fin n → Fin (m + 1)) :
    dotOf a (addX x y) = (dotOf a x + dotOf a y) % (m + 1) := by
  dsimp [dotOf, addX]
  rw [sum_mul_addF_mod, Nat.add_mod]

lemma dotOf_eq_iff_sub_zero {m n : Nat} (a x y : Fin n → Fin (m + 1)) :
    dotOf a x = dotOf a y ↔ dotOf a (subX x y) = 0 := by
  have hx : dotOf a x = (dotOf a y + dotOf a (subX x y)) % (m + 1) := by
    have h1 : addX y (subX x y) = x := addX_subX x y
    conv_lhs => rw [← h1]
    exact dotOf_add a y (subX x y)
  constructor
  · intro heq
    have hmod : (dotOf a y + dotOf a (subX x y)) % (m + 1) = (dotOf a y + 0) % (m + 1) := by
      rw [← hx, heq, Nat.add_zero, Nat.mod_eq_of_lt (dotOf_lt a y)]
    exact mod_add_left_cancel (dotOf_lt a (subX x y)) (Nat.succ_pos m) hmod
  · intro hz
    rw [hx, hz, Nat.add_zero, Nat.mod_eq_of_lt (dotOf_lt a y)]

lemma dotOf_add_zero {m n : Nat} (a u v : Fin n → Fin (m + 1))
    (hu : dotOf a u = 0) (hv : dotOf a v = 0) : dotOf a (addX u v) = 0 := by
  rw [dotOf_add, hu, hv]; simp

lemma dotOf_sub_zero {m n : Nat} (a u v : Fin n → Fin (m + 1))
    (hu : dotOf a u = 0) (hv : dotOf a v = 0) : dotOf a (subX u v) = 0 := by
  rw [← dotOf_eq_iff_sub_zero, hu, hv]

lemma dotOf_add_eq_of_zero {m n : Nat} (a x u : Fin n → Fin (m + 1))
    (hu : dotOf a u = 0) : dotOf a (addX x u) = dotOf a x := by
  rw [dotOf_add, hu, Nat.add_zero, Nat.mod_eq_of_lt (dotOf_lt a x)]

def addOut (m : Nat) {h : Nat} (u v : Fin h → Nat) : Fin h → Nat :=
  fun j => (u j + v j) % (m + 1)

lemma addOut_left_inj {m h : Nat} (u v₁ v₂ : Fin h → Nat)
    (hv₁ : ∀ j, v₁ j < m + 1) (hv₂ : ∀ j, v₂ j < m + 1)
    (heq : addOut m u v₁ = addOut m u v₂) : v₁ = v₂ := by
  funext j
  exact mod_add_left_cancel (hv₁ j) (hv₂ j) (congrFun heq j)

lemma card_eq_sum_fibers {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ x ∈ s, f x ∈ t) :
    s.card = t.sum (fun y => (s.filter (fun x => f x = y)).card) := by
  classical
  induction t using Finset.induction_on generalizing s with
  | empty =>
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa using hf x hx)
    simp [hs]
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have hsplit : s = s.filter (fun x => f x = a) ∪ s.filter (fun x => f x ≠ a) := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]; by_cases h : f x = a <;> simp [h]
    have hdisj : Disjoint (s.filter (fun x => f x = a)) (s.filter (fun x => f x ≠ a)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hcard : s.card = (s.filter (fun x => f x = a)).card + (s.filter (fun x => f x ≠ a)).card := by
      conv_lhs => rw [hsplit]
      exact Finset.card_union_of_disjoint hdisj
    rw [hcard, ih (s.filter (fun x => f x ≠ a)) (fun x hx => by
      rcases Finset.mem_filter.mp hx with ⟨hxs, hne⟩
      rcases Finset.mem_insert.mp (hf x hxs) with heq | ht
      · exact absurd heq hne
      · exact ht)]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    congr 1; ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxs, _⟩, rfl⟩; exact ⟨hxs, rfl⟩
    · rintro ⟨hxs, rfl⟩; exact ⟨⟨hxs, fun h => ha (h ▸ hy)⟩, rfl⟩

lemma sum_lt_sum_strict {α : Type*} (s : Finset α) (f g : α → Nat)
    (hne : s.Nonempty) (hlt : ∀ x ∈ s, f x < g x) :
    s.sum f < s.sum g := by
  classical
  rcases hne with ⟨a, ha⟩
  rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ ha]
  have h1 : f a < g a := hlt a ha
  have h2 : (s.erase a).sum f ≤ (s.erase a).sum g :=
    Finset.sum_le_sum fun x hx => le_of_lt (hlt x (Finset.mem_of_mem_erase hx))
  exact Nat.add_lt_add_of_lt_of_le h1 h2

def readoutOf {m n g b : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (i : Option (Fin g)) (x : Fin n → Fin (m + 1)) (j : Fin b) : Nat :=
  i.elim 0 (fun a => dotOf (A a j) x)

def goalOf {m n h : Nat} (B : Fin h → Fin n → Fin (m + 1))
    (x : Fin n → Fin (m + 1)) (j : Fin h) : Nat :=
  dotOf (B j) x

lemma goalOf_add {m n h : Nat} (B : Fin h → Fin n → Fin (m + 1))
    (x y : Fin n → Fin (m + 1)) :
    goalOf B (addX x y) = addOut m (goalOf B x) (goalOf B y) := by
  funext j
  exact dotOf_add (B j) x y

lemma goalOf_lt {m n h : Nat} (B : Fin h → Fin n → Fin (m + 1))
    (x : Fin n → Fin (m + 1)) (j : Fin h) :
    goalOf B x j < m + 1 :=
  dotOf_lt (B j) x

def kerOf {m n g b : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (M : Finset (Fin g)) : Finset (Fin n → Fin (m + 1)) :=
  (Finset.univ : Finset (Fin n → Fin (m + 1))).filter
    (fun x => ∀ a ∈ M, ∀ j : Fin b, dotOf (A a j) x = 0)

lemma zeroX_mem_kerOf {m n g b : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (M : Finset (Fin g)) : zeroX ∈ kerOf A M := by
  simp [kerOf, dotOf_zero]

lemma addX_mem_kerOf {m n g b : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (M : Finset (Fin g)) {u v : Fin n → Fin (m + 1)}
    (hu : u ∈ kerOf A M) (hv : v ∈ kerOf A M) : addX u v ∈ kerOf A M := by
  simp only [kerOf, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv ⊢
  intro a ha j
  exact dotOf_add_zero (A a j) u v (hu a ha j) (hv a ha j)

lemma subX_mem_kerOf {m n g b : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (M : Finset (Fin g)) {u v : Fin n → Fin (m + 1)}
    (hu : u ∈ kerOf A M) (hv : v ∈ kerOf A M) : subX u v ∈ kerOf A M := by
  simp only [kerOf, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv ⊢
  intro a ha j
  exact dotOf_sub_zero (A a j) u v (hu a ha j) (hv a ha j)

def runPair {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x : Fin n → Fin (m + 1)) (l : List (Fin k)) :
    List (Fin b → Nat) × Finset (Fin g) :=
  l.foldl (fun st j =>
    let q := askc j st.1
    (st.1 ++ [readoutOf A q x], match q with | none => st.2 | some a => insert a st.2))
    ([], ∅)

lemma runPair_fst {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x : Fin n → Fin (m + 1)) (l : List (Fin k)) :
    (runPair A askc x l).1 =
      l.foldl (fun hist j => hist ++ [readoutOf A (askc j hist) x]) [] := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l idx ih =>
    simp only [runPair, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

lemma runPair_len {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x : Fin n → Fin (m + 1)) (l : List (Fin k)) :
    (runPair A askc x l).1.length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l idx ih =>
    simp only [runPair, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

lemma runPair_append_singleton {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x : Fin n → Fin (m + 1)) (l : List (Fin k)) (idx : Fin k) :
    runPair A askc x (l ++ [idx]) =
      let st := runPair A askc x l
      let q := askc idx st.1
      (st.1 ++ [readoutOf A q x], match q with | none => st.2 | some a => insert a st.2) := by
  simp [runPair, List.foldl_append]

lemma runPair_card_le {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x : Fin n → Fin (m + 1)) (l : List (Fin k)) :
    (runPair A askc x l).2.card ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [runPair]
  | append_singleton l idx ih =>
    rw [runPair_append_singleton, List.length_append, List.length_singleton]
    dsimp only
    cases askc idx (runPair A askc x l).1 with
    | none => dsimp only; omega
    | some a =>
      dsimp only
      have := Finset.card_insert_le a (runPair A askc x l).2
      omega

lemma runPair_coset_iff {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (askc : Fin k → List (Fin b → Nat) → Option (Fin g))
    (x y : Fin n → Fin (m + 1)) (l : List (Fin k)) :
    (runPair A askc y l).1 = (runPair A askc x l).1 ↔
      ∀ a ∈ (runPair A askc x l).2, ∀ j : Fin b, dotOf (A a j) (subX y x) = 0 := by
  induction l using List.reverseRecOn with
  | nil => simp [runPair]
  | append_singleton l idx ih =>
    have hlen : (runPair A askc y l).1.length = (runPair A askc x l).1.length := by
      rw [runPair_len, runPair_len]
    rw [runPair_append_singleton, runPair_append_singleton]
    dsimp only
    constructor
    · intro heq
      have hinj := List.append_inj heq hlen
      have hpref : (runPair A askc y l).1 = (runPair A askc x l).1 := hinj.1
      have hlast : readoutOf A (askc idx (runPair A askc y l).1) y =
          readoutOf A (askc idx (runPair A askc x l).1) x := (List.cons.inj hinj.2).1
      have hih := ih.mp hpref
      rw [hpref] at hlast
      cases hq : askc idx (runPair A askc x l).1 with
      | none => exact hih
      | some a₀ =>
        intro a ha j
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · rw [hq] at hlast
          have hj := congrFun hlast j
          dsimp [readoutOf] at hj
          exact (dotOf_eq_iff_sub_zero (A a j) y x).mp hj
        · exact hih a ha' j
    · intro hall
      cases hq : askc idx (runPair A askc x l).1 with
      | none =>
        rw [hq] at hall
        have hpref : (runPair A askc y l).1 = (runPair A askc x l).1 := ih.mpr hall
        rw [hpref, hq]
        rfl
      | some a₀ =>
        rw [hq] at hall
        have hpref : (runPair A askc y l).1 = (runPair A askc x l).1 :=
          ih.mpr (fun a ha j => hall a (Finset.mem_insert_of_mem ha) j)
        rw [hpref, hq]
        congr 1; congr 1
        funext j
        dsimp [readoutOf]
        exact (dotOf_eq_iff_sub_zero (A a₀ j) y x).mpr (hall a₀ (Finset.mem_insert_self a₀ _) j)

lemma runPair_snd_const {m n g b k : Nat} (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (f : Fin k → Option (Fin g)) (x : Fin n → Fin (m + 1)) (l : List (Fin k)) (a : Fin g) :
    a ∈ (runPair A (fun j _ => f j) x l).2 ↔ ∃ j ∈ l, f j = some a := by
  induction l using List.reverseRecOn with
  | nil => simp [runPair]
  | append_singleton l idx ih =>
    rw [runPair_append_singleton]
    dsimp only
    cases hf : f idx with
    | none =>
      rw [ih]
      constructor
      · rintro ⟨j, hj, hfj⟩; exact ⟨j, List.mem_append_left _ hj, hfj⟩
      · rintro ⟨j, hj, hfj⟩
        rcases List.mem_append.mp hj with hjl | hji
        · exact ⟨j, hjl, hfj⟩
        · rw [List.mem_singleton.mp hji] at hfj
          rw [hf] at hfj; cases hfj
    | some a₀ =>
      rw [Finset.mem_insert, ih]
      constructor
      · rintro (rfl | ⟨j, hj, hfj⟩)
        · exact ⟨idx, List.mem_append_right _ (List.mem_singleton_self _), hf⟩
        · exact ⟨j, List.mem_append_left _ hj, hfj⟩
      · rintro ⟨j, hj, hfj⟩
        rcases List.mem_append.mp hj with hjl | hji
        · exact Or.inr ⟨j, hjl, hfj⟩
        · rw [List.mem_singleton.mp hji] at hfj
          rw [hf] at hfj
          exact Or.inl (Option.some.inj hfj).symm

lemma leaf_hits_bound {m n g b h : Nat}
    (A : Fin g → Fin b → Fin n → Fin (m + 1))
    (B : Fin h → Fin n → Fin (m + 1))
    (M : Finset (Fin g)) (x₀ : Fin n → Fin (m + 1)) (S : Finset (Fin h → Nat)) :
    let leaf := (kerOf A M).image (addX x₀)
    let D := ((kerOf A M).image (goalOf B)).card
    D * (leaf.filter (fun x => goalOf B x ∈ S)).card ≤ S.card * leaf.card := by
  classical
  intro leaf D
  let K := kerOf A M
  let K0 := K.filter (fun u => goalOf B u = goalOf B zeroX)
  have hfiber : ∀ y : Fin h → Nat, (∃ x₁ ∈ leaf, goalOf B x₁ = y) →
      (leaf.filter (fun x => goalOf B x = y)).card = K0.card := by
    rintro y ⟨x₁, hx₁_leaf, hx₁_y⟩
    rcases Finset.mem_image.mp hx₁_leaf with ⟨u₁, hu₁K, rfl⟩
    symm
    refine Finset.card_nbij (fun u => addX (addX x₀ u₁) u) ?_ ?_ ?_
    · intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huK, hu0⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · dsimp only
        rw [addX_assoc]
        exact Finset.mem_image.mpr ⟨addX u₁ u, addX_mem_kerOf A M hu₁K huK, rfl⟩
      · funext j
        have hzj : dotOf (B j) u = 0 := by
          have := congrFun hu0 j
          dsimp [goalOf] at this
          rw [dotOf_zero] at this
          exact this
        have := congrFun hx₁_y j
        dsimp [goalOf] at this ⊢
        rw [dotOf_add_eq_of_zero (B j) _ u hzj, this]
    · intro u _ v _ huv
      exact addX_left_inj (addX x₀ u₁) huv
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hx_leaf, hx_y⟩
      rcases Finset.mem_image.mp hx_leaf with ⟨u₂, hu₂K, rfl⟩
      let u := subX u₂ u₁
      have huK : u ∈ K := subX_mem_kerOf A M hu₂K hu₁K
      have heqx : addX (addX x₀ u₁) u = addX x₀ u₂ := by
        rw [addX_assoc, addX_subX]
      have hu0 : goalOf B u = goalOf B zeroX := by
        funext j
        have h1 : dotOf (B j) (addX x₀ u₂) = dotOf (B j) (addX x₀ u₁) := by
          have ha := congrFun hx_y j
          have hb := congrFun hx₁_y j
          dsimp [goalOf] at ha hb
          rw [ha, hb]
        have h2 : dotOf (B j) (subX (addX x₀ u₂) (addX x₀ u₁)) = 0 :=
          (dotOf_eq_iff_sub_zero (B j) _ _).mp h1
        have hsub : subX (addX x₀ u₂) (addX x₀ u₁) = u := by
          apply addX_left_inj (addX x₀ u₁)
          rw [addX_subX, heqx]
        rw [hsub] at h2
        dsimp [goalOf]
        rw [dotOf_zero, h2]
      exact ⟨u, Finset.mem_filter.mpr ⟨huK, hu0⟩, heqx⟩
  have hleaf_img_card : (leaf.image (goalOf B)).card = D := by
    symm
    refine Finset.card_nbij (fun v => addOut m (goalOf B x₀) v) ?_ ?_ ?_
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨u, huK, rfl⟩
      refine Finset.mem_image.mpr ⟨addX x₀ u, Finset.mem_image.mpr ⟨u, huK, rfl⟩, ?_⟩
      exact goalOf_add B x₀ u
    · intro v₁ hv₁ v₂ hv₂ heq
      rcases Finset.mem_image.mp hv₁ with ⟨u₁, _, rfl⟩
      rcases Finset.mem_image.mp hv₂ with ⟨u₂, _, rfl⟩
      exact addOut_left_inj (goalOf B x₀) _ _ (goalOf_lt B u₁) (goalOf_lt B u₂) heq
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx_leaf, rfl⟩
      rcases Finset.mem_image.mp hx_leaf with ⟨u, huK, rfl⟩
      exact ⟨goalOf B u, Finset.mem_image.mpr ⟨u, huK, rfl⟩, (goalOf_add B x₀ u).symm⟩
  have hleaf_card : leaf.card = D * K0.card := by
    have hsum := card_eq_sum_fibers leaf (leaf.image (goalOf B)) (goalOf B)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    rw [hsum]
    have hconst : (leaf.image (goalOf B)).sum (fun y => (leaf.filter (fun x => goalOf B x = y)).card) =
        (leaf.image (goalOf B)).sum (fun _ => K0.card) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rcases Finset.mem_image.mp hy with ⟨x₁, hx₁, rfl⟩
      exact hfiber (goalOf B x₁) ⟨x₁, hx₁, rfl⟩
    rw [hconst, Finset.sum_const, smul_eq_mul, hleaf_img_card]
  have hhit_le : (leaf.filter (fun x => goalOf B x ∈ S)).card ≤ S.card * K0.card := by
    have hsum := card_eq_sum_fibers (leaf.filter (fun x => goalOf B x ∈ S)) S (goalOf B)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [hsum]
    calc
      S.sum (fun y => ((leaf.filter (fun x => goalOf B x ∈ S)).filter (fun x => goalOf B x = y)).card)
          ≤ S.sum (fun _ => K0.card) := by
            refine Finset.sum_le_sum fun y hy => ?_
            have hsub : (leaf.filter (fun x => goalOf B x ∈ S)).filter (fun x => goalOf B x = y) ⊆
                leaf.filter (fun x => goalOf B x = y) := by
              intro x hx
              rcases Finset.mem_filter.mp hx with ⟨hx1, hxy⟩
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx1).1, hxy⟩
            calc
              ((leaf.filter (fun x => goalOf B x ∈ S)).filter (fun x => goalOf B x = y)).card
                  ≤ (leaf.filter (fun x => goalOf B x = y)).card := Finset.card_le_card hsub
              _ ≤ K0.card := by
                  by_cases hex : ∃ x₁ ∈ leaf, goalOf B x₁ = y
                  · rw [hfiber y hex]
                  · have hemp : leaf.filter (fun x => goalOf B x = y) = ∅ :=
                      Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hex ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩)
                    simp [hemp]
      _ = S.card * K0.card := by rw [Finset.sum_const, smul_eq_mul]
  calc
    D * (leaf.filter (fun x => goalOf B x ∈ S)).card
        ≤ D * (S.card * K0.card) := Nat.mul_le_mul_left D hhit_le
    _ = S.card * (D * K0.card) := by ring
    _ = S.card * leaf.card := by rw [hleaf_card]

theorem main :
∀ (m n g b h k L s q : Nat), 0 < q → s ≤ q →
  let F := Fin (m + 1)
  let X := Fin n → F
  let Reply := Fin b → Nat
  let Output := Fin h → Nat
  let cube := (Finset.univ : Finset X)
  let bits := (Finset.univ : Finset (Fin n))
  ∀ (A : Fin g → Fin b → Fin n → F) (B : Fin h → Fin n → F),
  let dot := fun (a : Fin n → F) (x : X) =>
    bits.sum (fun i => (a i).val * (x i).val) % (m + 1)
  let readout := fun (i : Option (Fin g)) (x : X) (j : Fin b) =>
    i.elim 0 (fun a => dot (A a j) x)
  let goal := fun (x : X) (j : Fin h) => dot (B j) x
  let uncertainty := fun (M : Finset (Fin g)) =>
    ((cube.filter (fun x => ∀ a ∈ M, ∀ j : Fin b, dot (A a j) x = 0)).image goal).card
  ( (∃ N : Nat, 0 < N ∧
      ∃ ask : Fin N → Fin k → List Reply → Option (Fin g),
      ∃ out : Fin N → List Reply → Finset Output,
      (∀ c z, (out c z).card ≤ L) ∧ ∀ x : X,
        let wins := (Finset.univ : Finset (Fin N)).filter (fun c =>
          goal x ∈ out c ((List.finRange k).foldl (fun hist j =>
            hist ++ [readout (ask c j hist) x]) ([] : List Reply)))
        s * N ≤ q * wins.card) ↔
    ∃ M : Finset (Fin g), M.card ≤ k ∧ s * uncertainty M ≤ q * L ) := by
  classical
  intro m n g b h k L s q hq_pos hsq
  dsimp only
  intro A B
  change (∃ N : Nat, 0 < N ∧
      ∃ ask : Fin N → Fin k → List (Fin b → Nat) → Option (Fin g),
      ∃ out : Fin N → List (Fin b → Nat) → Finset (Fin h → Nat),
      (∀ c z, (out c z).card ≤ L) ∧ ∀ x : Fin n → Fin (m + 1),
        s * N ≤ q * ((Finset.univ : Finset (Fin N)).filter (fun c =>
          goalOf B x ∈ out c ((List.finRange k).foldl (fun hist j =>
            hist ++ [readoutOf A (ask c j hist) x]) ([] : List (Fin b → Nat))))).card) ↔
    ∃ M : Finset (Fin g), M.card ≤ k ∧ s * ((kerOf A M).image (goalOf B)).card ≤ q * L
  constructor
  · rintro ⟨N, hN_pos, ask, out, hout_card, hwin⟩
    by_contra hno
    push Not at hno
    let cube : Finset (Fin n → Fin (m + 1)) := Finset.univ
    let tr : Fin N → (Fin n → Fin (m + 1)) → List (Fin b → Nat) :=
      fun c x => (runPair A (ask c) x (List.finRange k)).1
    have htr_eq : ∀ c x,
        (List.finRange k).foldl (fun hist j =>
          hist ++ [readoutOf A (ask c j hist) x]) ([] : List (Fin b → Nat)) = tr c x :=
      fun c x => (runPair_fst A (ask c) x (List.finRange k)).symm
    have hseed_lt : ∀ c : Fin N,
        q * (cube.filter (fun x => goalOf B x ∈ out c (tr c x))).card < s * cube.card := by
      intro c
      let Zc := cube.image (tr c)
      have hZc_ne : Zc.Nonempty := ⟨tr c zeroX, Finset.mem_image.mpr ⟨zeroX, Finset.mem_univ _, rfl⟩⟩
      have htot_card : cube.card = Zc.sum (fun z => (cube.filter (fun x => tr c x = z)).card) :=
        card_eq_sum_fibers cube Zc (tr c) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hhit_card : (cube.filter (fun x => goalOf B x ∈ out c (tr c x))).card =
          Zc.sum (fun z => ((cube.filter (fun x => tr c x = z)).filter (fun x => goalOf B x ∈ out c z)).card) := by
        have h1 := card_eq_sum_fibers (cube.filter (fun x => goalOf B x ∈ out c (tr c x))) Zc (tr c)
          (fun x hx => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
        rw [h1]
        refine Finset.sum_congr rfl fun z _ => ?_
        congr 1; ext x
        simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hmem, rfl⟩; exact ⟨rfl, hmem⟩
        · rintro ⟨rfl, hmem⟩; exact ⟨hmem, rfl⟩
      rw [hhit_card, htot_card, Finset.mul_sum, Finset.mul_sum]
      refine sum_lt_sum_strict Zc _ _ hZc_ne ?_
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x₀, _, rfl⟩
      let M := (runPair A (ask c) x₀ (List.finRange k)).2
      have hMk : M.card ≤ k := by
        have := runPair_card_le A (ask c) x₀ (List.finRange k)
        rwa [List.length_finRange] at this
      have hM_lt : q * L < s * ((kerOf A M).image (goalOf B)).card := hno M hMk
      have hleaf_eq : cube.filter (fun x => tr c x = tr c x₀) = (kerOf A M).image (addX x₀) := by
        ext x
        simp only [cube, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, kerOf]
        rw [show tr c x = tr c x₀ ↔ ∀ a ∈ M, ∀ j : Fin b, dotOf (A a j) (subX x x₀) = 0 from
          runPair_coset_iff A (ask c) x₀ x (List.finRange k)]
        constructor
        · intro hsub
          exact ⟨subX x x₀, hsub, addX_subX x x₀⟩
        · rintro ⟨u, hu, rfl⟩
          rwa [subX_addX]
      let leaf := (kerOf A M).image (addX x₀)
      let D := ((kerOf A M).image (goalOf B)).card
      have hD_pos : 0 < D :=
        Finset.card_pos.mpr ⟨goalOf B zeroX, Finset.mem_image.mpr ⟨zeroX, zeroX_mem_kerOf A M, rfl⟩⟩
      have hleaf_pos : 0 < leaf.card :=
        Finset.card_pos.mpr ⟨x₀, Finset.mem_image.mpr ⟨zeroX, zeroX_mem_kerOf A M, addX_zero x₀⟩⟩
      have hbound := leaf_hits_bound A B M x₀ (out c (tr c x₀))
      have hS_le : (out c (tr c x₀)).card ≤ L := hout_card c (tr c x₀)
      rw [hleaf_eq]
      have hmul : D * (q * (leaf.filter (fun x => goalOf B x ∈ out c (tr c x₀))).card) <
          D * (s * leaf.card) := by
        calc
          D * (q * (leaf.filter (fun x => goalOf B x ∈ out c (tr c x₀))).card)
              = q * (D * (leaf.filter (fun x => goalOf B x ∈ out c (tr c x₀))).card) := by ring
          _ ≤ q * ((out c (tr c x₀)).card * leaf.card) := Nat.mul_le_mul_left q hbound
          _ ≤ q * (L * leaf.card) := Nat.mul_le_mul_left q (Nat.mul_le_mul_right leaf.card hS_le)
          _ = (q * L) * leaf.card := by ring
          _ < (s * D) * leaf.card := Nat.mul_lt_mul_of_pos_right hM_lt hleaf_pos
          _ = D * (s * leaf.card) := by ring
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hN_ne : (Finset.univ : Finset (Fin N)).Nonempty :=
      ⟨⟨0, hN_pos⟩, Finset.mem_univ _⟩
    have hsum_lt : (Finset.univ : Finset (Fin N)).sum
        (fun c => q * (cube.filter (fun x => goalOf B x ∈ out c (tr c x))).card) <
        (Finset.univ : Finset (Fin N)).sum (fun _ => s * cube.card) :=
      sum_lt_sum_strict Finset.univ _ _ hN_ne (fun c _ => hseed_lt c)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
    have hsum_ge : cube.sum (fun _ => s * N) ≤
        cube.sum (fun x => q * ((Finset.univ : Finset (Fin N)).filter (fun c => goalOf B x ∈ out c (tr c x))).card) :=
      Finset.sum_le_sum fun x _ => by simpa only [htr_eq] using hwin x
    rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum_ge
    have hswap : cube.sum (fun x => ((Finset.univ : Finset (Fin N)).filter (fun c => goalOf B x ∈ out c (tr c x))).card) =
        (Finset.univ : Finset (Fin N)).sum (fun c => (cube.filter (fun x => goalOf B x ∈ out c (tr c x))).card) := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap] at hsum_ge
    have heq_rhs : cube.card * (s * N) = N * (s * cube.card) := by ring
    omega
  · rintro ⟨M, hMk, hMbound⟩
    let G := (kerOf A M).image (goalOf B)
    let D := G.card
    have hD_pos : 0 < D :=
      Finset.card_pos.mpr ⟨goalOf B zeroX, Finset.mem_image.mpr ⟨zeroX, zeroX_mem_kerOf A M, rfl⟩⟩
    let ml := M.toList
    have hml_len : ml.length = M.card := Finset.length_toList M
    let gl := G.toList
    have hgl_len : gl.length = D := Finset.length_toList G
    let ask_fn : Fin k → Option (Fin g) := fun j => ml[j.val]?
    let ask : Fin D → Fin k → List (Fin b → Nat) → Option (Fin g) := fun _ j _ => ask_fn j
    let tr : (Fin n → Fin (m + 1)) → List (Fin b → Nat) :=
      fun x => (runPair A (fun j _ => ask_fn j) x (List.finRange k)).1
    have htr_snd : ∀ x : Fin n → Fin (m + 1),
        (runPair A (fun j _ => ask_fn j) x (List.finRange k)).2 = M := by
      intro x
      ext a
      rw [runPair_snd_const]
      constructor
      · rintro ⟨j, _, hj⟩
        dsimp [ask_fn] at hj
        rcases List.getElem?_eq_some_iff.mp hj with ⟨hjl, rfl⟩
        exact Finset.mem_toList.mp (List.getElem_mem hjl)
      · intro ha
        have haml : a ∈ ml := Finset.mem_toList.mpr ha
        rcases List.mem_iff_getElem.mp haml with ⟨i, hi, rfl⟩
        have hik : i < k := by omega
        refine ⟨⟨i, hik⟩, List.mem_finRange _, ?_⟩
        dsimp [ask_fn]
        exact List.getElem?_eq_getElem hi
    let out : Fin D → List (Fin b → Nat) → Finset (Fin h → Nat) := fun c z =>
      if hz : ∃ x₀ : Fin n → Fin (m + 1), tr x₀ = z then
        let x₀ := Classical.choose hz
        (Finset.range (min L D)).image (fun i =>
          addOut m (goalOf B x₀) (gl[(c.val + i) % D]'(by rw [hgl_len]; exact Nat.mod_lt _ hD_pos)))
      else ∅
    refine ⟨D, hD_pos, ask, out, ?_, ?_⟩
    · intro c z
      dsimp only [out]
      split_ifs with hz
      · calc
          ((Finset.range (min L D)).image _).card ≤ (Finset.range (min L D)).card := Finset.card_image_le
          _ = min L D := Finset.card_range _
          _ ≤ L := Nat.min_le_left L D
      · simp
    · intro x
      have htr_fold : ∀ c : Fin D,
          (List.finRange k).foldl (fun hist j =>
            hist ++ [readoutOf A (ask c j hist) x]) ([] : List (Fin b → Nat)) = tr x :=
        fun c => (runPair_fst A (fun j _ => ask_fn j) x (List.finRange k)).symm
      have hex : ∃ x₀ : Fin n → Fin (m + 1), tr x₀ = tr x := ⟨x, rfl⟩
      let x₀ := Classical.choose hex
      have hx₀_tr : tr x₀ = tr x := Classical.choose_spec hex
      have hsub_ker : subX x x₀ ∈ kerOf A M := by
        simp only [kerOf, Finset.mem_filter, Finset.mem_univ, true_and]
        have hcos := (runPair_coset_iff A (fun j _ => ask_fn j) x₀ x (List.finRange k)).mp hx₀_tr.symm
        rw [htr_snd x₀] at hcos
        exact hcos
      have hgoal_mem : goalOf B (subX x x₀) ∈ gl :=
        Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨subX x x₀, hsub_ker, rfl⟩)
      rcases List.mem_iff_getElem.mp hgoal_mem with ⟨r, hr_lt, hr_eq⟩
      have hrD : r < D := by omega
      let hitSeed : Nat → Fin D := fun i => ⟨(r + D - i) % D, Nat.mod_lt _ hD_pos⟩
      have hhit_inj : Set.InjOn hitSeed (Finset.range (min L D)) := by
        intro i₁ hi₁ i₂ hi₂ heq
        have h1 : i₁ < D := lt_of_lt_of_le (Finset.mem_range.mp hi₁) (Nat.min_le_right L D)
        have h2 : i₂ < D := lt_of_lt_of_le (Finset.mem_range.mp hi₂) (Nat.min_le_right L D)
        have hval : (r + D - i₁) % D = (r + D - i₂) % D := congrArg Fin.val heq
        have hmod1 : ((r + D - i₁) + i₁) % D = r := by
          have : r + D - i₁ + i₁ = r + D := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hrD]
        have hmod2 : ((r + D - i₂) + i₂) % D = r := by
          have : r + D - i₂ + i₂ = r + D := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hrD]
        have hsame : ((r + D - i₁) % D + i₁) % D = ((r + D - i₁) % D + i₂) % D := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hmod1]
          rw [hval, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hmod2]
        exact mod_add_left_cancel h1 h2 hsame
      have hsub_wins : (Finset.range (min L D)).image hitSeed ⊆
          (Finset.univ : Finset (Fin D)).filter (fun c =>
            goalOf B x ∈ out c ((List.finRange k).foldl (fun hist j =>
              hist ++ [readoutOf A (ask c j hist) x]) ([] : List (Fin b → Nat)))) := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
        have hiD : i < D := lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.min_le_right L D)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, htr_fold]
        dsimp only [out]
        rw [dif_pos hex]
        refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
        have hidx : ((hitSeed i).val + i) % D = r := by
          dsimp [hitSeed]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : r + D - i + i = r + D := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hrD]
        have hgl_get : gl[((hitSeed i).val + i) % D]'(by rw [hgl_len]; exact Nat.mod_lt _ hD_pos) =
            goalOf B (subX x x₀) := by
          simpa only [hidx] using hr_eq
        rw [hgl_get, ← goalOf_add B x₀ (subX x x₀), addX_subX x x₀]
      have hwins_ge : min L D ≤ ((Finset.univ : Finset (Fin D)).filter (fun c =>
          goalOf B x ∈ out c ((List.finRange k).foldl (fun hist j =>
            hist ++ [readoutOf A (ask c j hist) x]) ([] : List (Fin b → Nat))))).card := by
        calc
          min L D = (Finset.range (min L D)).card := (Finset.card_range _).symm
          _ = ((Finset.range (min L D)).image hitSeed).card := (Finset.card_image_of_injOn hhit_inj).symm
          _ ≤ _ := Finset.card_le_card hsub_wins
      have hsd_le : s * D ≤ q * min L D := by
        by_cases hLD : L ≤ D
        · rw [Nat.min_eq_left hLD]
          exact hMbound
        · rw [Nat.min_eq_right (Nat.le_of_not_le hLD)]
          exact Nat.mul_le_mul_right D hsq
      exact hsd_le.trans (Nat.mul_le_mul_left q hwins_ge)

end PEqualNP.Outside.L_lib_1164_aux

theorem PEqualNP.Outside.L_lib_1164 : ∀ (m n g b h k L s q : Nat), 0 < q → s ≤ q →
  let F := Fin (m + 1)
  let X := Fin n → F
  let Reply := Fin b → Nat
  let Output := Fin h → Nat
  let cube := (Finset.univ : Finset X)
  let bits := (Finset.univ : Finset (Fin n))
  ∀ (A : Fin g → Fin b → Fin n → F) (B : Fin h → Fin n → F),
  let dot := fun (a : Fin n → F) (x : X) =>
    bits.sum (fun i => (a i).val * (x i).val) % (m + 1)
  let readout := fun (i : Option (Fin g)) (x : X) (j : Fin b) =>
    i.elim 0 (fun a => dot (A a j) x)
  let goal := fun (x : X) (j : Fin h) => dot (B j) x
  let uncertainty := fun (M : Finset (Fin g)) =>
    ((cube.filter (fun x => ∀ a ∈ M, ∀ j : Fin b, dot (A a j) x = 0)).image goal).card
  ( (∃ N : Nat, 0 < N ∧
      ∃ ask : Fin N → Fin k → List Reply → Option (Fin g),
      ∃ out : Fin N → List Reply → Finset Output,
      (∀ c z, (out c z).card ≤ L) ∧ ∀ x : X,
        let wins := (Finset.univ : Finset (Fin N)).filter (fun c =>
          goal x ∈ out c ((List.finRange k).foldl (fun hist j =>
            hist ++ [readout (ask c j hist) x]) ([] : List Reply)))
        s * N ≤ q * wins.card) ↔
    ∃ M : Finset (Fin g), M.card ≤ k ∧ s * uncertainty M ≤ q * L ) :=
  PEqualNP.Outside.L_lib_1164_aux.main
