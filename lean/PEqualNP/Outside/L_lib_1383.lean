import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1383_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

noncomputable def value (V : ℕ → Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map V)

lemma value_and (V : ℕ → Bool) (u v : ℕ) :
    value V ⟨GateOp.and, [u, v]⟩ = (V u && V v) := by
  simp [value, GateOp.eval]

lemma value_or (V : ℕ → Bool) (u v : ℕ) :
    value V ⟨GateOp.or, [u, v]⟩ = (V u || V v) := by
  simp [value, GateOp.eval]

lemma value_not (V : ℕ → Bool) (u : ℕ) :
    value V ⟨GateOp.not, [u]⟩ = !(V u) := by
  simp [value, GateOp.eval]

def gAnd (u v : ℕ) : Gate := ⟨GateOp.and, [u, v]⟩
def gOr (u v : ℕ) : Gate := ⟨GateOp.or, [u, v]⟩
def gNot (u : ℕ) : Gate := ⟨GateOp.not, [u]⟩

def PosFanInTwo (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma posFanInTwo_to_FanInTwo (gs : List Gate) (h : PosFanInTwo gs) : FanInTwo ⟨gs, 0⟩ := by
  intro g hg
  rcases h g hg with ⟨h1 | h1, h2⟩
  · exact ⟨Or.inl h1, h2⟩
  · exact ⟨Or.inr (Or.inl h1), h2⟩

lemma posFanInTwo_append {gs1 gs2 : List Gate} (h1 : PosFanInTwo gs1) (h2 : PosFanInTwo gs2) :
    PosFanInTwo (gs1 ++ gs2) := by
  intro g hg
  rcases List.mem_append.mp hg with hm | hm
  · exact h1 g hm
  · exact h2 g hm

lemma nc_append (gs1 gs2 : List Gate) :
    notCount ⟨gs1 ++ gs2, 0⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append, List.length_append]

lemma nc_cons (g : Gate) (gs : List Gate) :
    notCount ⟨g :: gs, 0⟩ = (match g.op with | GateOp.not => 1 | _ => 0) + notCount ⟨gs, 0⟩ := by
  unfold notCount
  cases hg : g.op <;> simp [hg, Nat.add_comm]

lemma posFanInTwo_nc {gs : List Gate} (h : PosFanInTwo gs) : notCount ⟨gs, 0⟩ = 0 := by
  unfold notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  have ho := (h g hg).1
  rcases ho with ho | ho <;> simp [ho]

def run (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun idx => w.getD idx false))]) init

lemma wires_eq (gs : List Gate) (out : ℕ) (init : List Bool) :
    (Circuit.mk gs out).wires init = run gs init := rfl

lemma getD_append_left' {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_right' {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma run_len (gs : List Gate) (init : List Bool) :
    (run gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons]
    change (run gs (init ++ [g.op.eval _])).length = _
    rw [ih, List.length_append, List.length_singleton, List.length_cons]
    omega

inductive RB : ℕ → List Gate → Prop
  | nil (b : ℕ) : RB b []
  | cons {b : ℕ} {g : Gate} {gs : List Gate} :
      (∀ v ∈ g.inputs, v < b) → RB (b + 1) gs → RB b (g :: gs)

lemma RB.append {b : ℕ} {gs1 gs2 : List Gate} (h1 : RB b gs1) (h2 : RB (b + gs1.length) gs2) :
    RB b (gs1 ++ gs2) := by
  induction h1 with
  | nil b => simpa using h2
  | cons hv _ ih =>
    simp only [List.cons_append]
    refine RB.cons hv (ih ?_)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

lemma RB.append' {b1 b2 : ℕ} {gs1 gs2 : List Gate} (h1 : RB b1 gs1) (h2 : RB b2 gs2)
    (heq : b2 = b1 + gs1.length) : RB b1 (gs1 ++ gs2) :=
  RB.append h1 (heq ▸ h2)

lemma RB.mono {b1 b2 : ℕ} {gs : List Gate} (hle : b1 ≤ b2) (h : RB b1 gs) : RB b2 gs := by
  induction h generalizing b2 with
  | nil _ => exact RB.nil _
  | cons hv _ ih => exact RB.cons (fun v hvin => lt_of_lt_of_le (hv v hvin) hle) (ih (Nat.add_le_add_right hle 1))

lemma ReadsBack_to_RB (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) : RB N C.gates := by
  suffices ∀ (k : ℕ) (gs : List Gate), gs = C.gates.drop k →
      (∀ j (hj : j < gs.length), ∀ v ∈ (gs[j]'hj).inputs, v < N + k + j) → RB (N + k) gs by
    simpa using this 0 C.gates (by simp) (fun j hj v hv => by
      have := hRB j (by simpa using hj) v
      unfold gateAt at this
      rw [List.getD_eq_getElem _ _ hj] at this
      exact this hv)
  intro k gs
  induction gs generalizing k with
  | nil => intro _ _; exact RB.nil _
  | cons g gs ih =>
    intro hdrop hlt
    refine RB.cons ?_ ?_
    · intro v hv
      have := hlt 0 (by simp) v hv
      simpa using this
    · have h1 := ih (k + 1) (by
        have := congrArg List.tail hdrop
        simpa [List.tail_drop] using this) (fun j hj v hv => by
        have := hlt (j + 1) (by simp; omega) v hv
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
      simpa [Nat.add_assoc] using h1

lemma RB_to_ReadsBack (N : ℕ) (C : Circuit) (hRB : RB N C.gates) : ReadsBack N C := by
  have aux : ∀ (b : ℕ) (gs : List Gate), RB b gs →
      ∀ j (hj : j < gs.length), ∀ v ∈ (gs[j]'hj).inputs, v < b + j := by
    intro b gs h
    induction h with
    | nil _ => intro j hj; simp at hj
    | cons hv _ ih =>
      intro j hj v hvin
      cases j with
      | zero => simpa using hv v hvin
      | succ j' =>
        have := ih j' (by simpa using hj) v hvin
        omega
  intro j hj v hv
  unfold gateAt at hv
  rw [List.getD_eq_getElem _ _ hj] at hv
  exact aux N C.gates hRB j hj v hv

def Cons (V : ℕ → Bool) : ℕ → List Gate → Prop
  | _, [] => True
  | b, g :: gs => V b = value V g ∧ Cons V (b + 1) gs

lemma Cons.left {V : ℕ → Bool} {b : ℕ} {gs1 gs2 : List Gate} (h : Cons V b (gs1 ++ gs2)) :
    Cons V b gs1 := by
  induction gs1 generalizing b with
  | nil => trivial
  | cons g gs1 ih =>
    simp only [List.cons_append, Cons] at h ⊢
    exact ⟨h.1, ih h.2⟩

lemma Cons.right' {V : ℕ → Bool} {b b2 : ℕ} {gs1 gs2 : List Gate} (h : Cons V b (gs1 ++ gs2))
    (heq : b2 = b + gs1.length) : Cons V b2 gs2 := by
  subst heq
  induction gs1 generalizing b with
  | nil => simpa using h
  | cons g gs1 ih =>
    simp only [List.cons_append, Cons] at h
    have := ih h.2
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

lemma Cons.single {V : ℕ → Bool} {b : ℕ} {g : Gate} (h : Cons V b [g]) : V b = value V g :=
  h.1

lemma run_spec (gs : List Gate) (init : List Bool) (hRB : RB init.length gs) :
    (∀ u < init.length, (run gs init).getD u false = init.getD u false) ∧
    Cons (fun u => (run gs init).getD u false) init.length gs := by
  induction gs generalizing init with
  | nil => exact ⟨fun _ _ => rfl, trivial⟩
  | cons g gs ih =>
    cases hRB with
    | cons hv htail =>
      let bit := g.op.eval (g.inputs.map (fun idx => init.getD idx false))
      let init' := init ++ [bit]
      have hlen : init'.length = init.length + 1 := by simp [init']
      have ih' := ih init' (hlen ▸ htail)
      have hrun : run (g :: gs) init = run gs init' := rfl
      rw [hrun]
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [ih'.1 u (by omega)]
        exact List.getD_append init [bit] false u hu
      · refine ⟨?_, ?_⟩
        · change (run gs init').getD init.length false = value (fun u => (run gs init').getD u false) g
          rw [ih'.1 init.length (by omega)]
          have hget : init'.getD init.length false = bit := by simp [init']
          rw [hget]
          unfold value
          dsimp only [bit]
          congr 1
          exact List.map_congr_left fun idx hidx => by
            have hlt := hv idx hidx
            rw [ih'.1 idx (by omega), getD_append_left' init [bit] idx false hlt]
        · simpa [hlen] using ih'.2

section Forward

def groupList {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) : List ℕ :=
  (((Finset.univ : Finset (Fin n)).filter (fun i => color i = j)).image Fin.val).sort (· ≤ ·)

lemma groupList_len {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) :
    (groupList color j).length = ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j)).card := by
  rw [groupList, Finset.length_sort, Finset.card_image_of_injective _ Fin.val_injective]

lemma groupList_sum_len {n d : ℕ} (color : Fin n → Fin d) :
    (Finset.univ : Finset (Fin d)).sum (fun j => (groupList color j).length) = n := by
  simp_rw [groupList_len]
  have := Finset.card_eq_sum_card_fiberwise (f := color) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin d))) (fun x _ => Finset.mem_univ _)
  simpa using this.symm

lemma groupList_pos {n d : ℕ} (color : Fin n → Fin d) (hsurj : Function.Surjective color) (j : Fin d) :
    1 ≤ (groupList color j).length := by
  rw [groupList_len]
  refine Finset.card_pos.2 ?_
  obtain ⟨i, hi⟩ := hsurj j
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩

lemma groupList_sorted {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) :
    (groupList color j).Pairwise (· < ·) := by
  have hs := (((Finset.univ : Finset (Fin n)).filter (fun i => color i = j)).image Fin.val).pairwise_sort (· ≤ ·)
  have hnd := (((Finset.univ : Finset (Fin n)).filter (fun i => color i = j)).image Fin.val).sort_nodup (· ≤ ·)
  exact (hs.and hnd).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)

lemma groupList_mem {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) (k : ℕ) :
    k ∈ groupList color j ↔ ∃ hk : k < n, color ⟨k, hk⟩ = j := by
  simp only [groupList, Finset.mem_sort, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k', hk'⟩, hc, rfl⟩; exact ⟨hk', hc⟩
  · rintro ⟨hk, hc⟩; exact ⟨⟨k, hk⟩, hc, rfl⟩

lemma groupList_lt {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) {k : ℕ} (hk : k ∈ groupList color j) :
    k < n := ((groupList_mem color j k).1 hk).1

lemma step_eq_of_no_color {n d : ℕ} (color : Fin n → Fin d)
    (X : Fin (n + 1) → Fin d → Bool)
    (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j)
    (j : Fin d) {a b : ℕ} (ha : a ≤ b) (hb : b ≤ n)
    (hno : ∀ i : Fin n, a ≤ i.val → i.val < b → color i ≠ j) :
    X ⟨a, by omega⟩ j = X ⟨b, by omega⟩ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih' := ih (by omega) (by omega) (fun i h1 h2 => hno i h1 (by omega))
    have hstep : X ⟨a + k, by omega⟩ j = X ⟨a + k + 1, by omega⟩ j := by
      by_contra hne
      have hc := (hX ⟨a + k, by omega⟩ j).1 hne
      exact hno ⟨a + k, by omega⟩ (by dsimp; omega) (by dsimp; omega) hc
    exact ih'.trans hstep

lemma eval_runs_count {n : ℕ} (X : Fin (n + 1) → Bool) (is : List ℕ)
    (hsorted : is.Pairwise (· < ·)) (hbnd : ∀ k ∈ is, k < n) :
    (∀ i : Fin n, (X i.castSucc ≠ X i.succ) ↔ i.val ∈ is) →
    ∀ l : Fin (n + 1),
      X l = xor (X 0) (decide ((is.filter (· < l.val)).length % 2 = 1)) := by
  intro hflip l
  obtain ⟨v, hv⟩ := l
  induction v with
  | zero =>
    have h0 : (⟨0, hv⟩ : Fin (n + 1)) = 0 := rfl
    simp [h0]
  | succ v ih =>
    have ih' := ih (by omega)
    let iv : Fin n := ⟨v, by omega⟩
    have hprev : (⟨v, by omega⟩ : Fin (n + 1)) = iv.castSucc := rfl
    have hnext : (⟨v + 1, hv⟩ : Fin (n + 1)) = iv.succ := rfl
    have hfilt : (is.filter (· < v + 1)).length =
        (is.filter (· < v)).length + if v ∈ is then 1 else 0 := by
      clear hprev hnext ih ih' hflip
      induction is with
      | nil => simp
      | cons a as iha =>
        have hnd := (List.pairwise_cons.1 hsorted).1
        have hpa := (List.pairwise_cons.1 hsorted).2
        have iha' := iha hpa (fun k hk => hbnd k (List.mem_cons_of_mem _ hk))
        by_cases ha_eq : a = v
        · subst ha_eq
          have hnot : a ∉ as := fun hm => absurd (hnd a hm) (lt_irrefl _)
          rw [List.filter_cons, List.filter_cons]
          have hlt1 : decide (a < a + 1) = true := decide_eq_true (Nat.lt_succ_self a)
          have hlt0 : decide (a < a) = false := decide_eq_false (lt_irrefl a)
          rw [hlt1, hlt0]
          simp only [↓reduceIte, Bool.false_eq_true, List.length_cons, List.mem_cons,
            hnot, or_false]
          have hf1 : as.filter (· < a + 1) = as.filter (· < a) := by
            apply List.filter_congr
            intro x hx
            have := hnd x hx
            simp [show ¬ (x < a + 1) by omega, show ¬ (x < a) by omega]
          rw [hf1]
        · have hne : v ≠ a := Ne.symm ha_eq
          simp only [List.filter_cons, List.mem_cons, hne, false_or]
          by_cases hav : a < v
          · have hav1 : a < v + 1 := by omega
            simp only [hav, decide_true, ↓reduceIte, hav1, List.length_cons]
            rw [iha']
            omega
          · have hav1 : ¬ (a < v + 1) := by omega
            simp only [hav, decide_false, Bool.false_eq_true, ↓reduceIte, hav1]
            exact iha'
    have hcv : (iv.castSucc : ℕ) = v := rfl
    have hsv : (iv.succ : ℕ) = v + 1 := rfl
    by_cases hmem : v ∈ is
    · have hf : X iv.castSucc ≠ X iv.succ := (hflip iv).2 hmem
      rw [hprev] at ih'
      rw [hnext]
      have hne_bool : X iv.succ = !X iv.castSucc := by
        cases h1 : X iv.castSucc <;> cases h2 : X iv.succ <;> simp_all
      rw [hne_bool, ih', hcv, hsv, hfilt, if_pos hmem]
      change (!(X 0 ^^ decide ((is.filter (· < v)).length % 2 = 1))) =
        (X 0 ^^ decide (((is.filter (· < v)).length + 1) % 2 = 1))
      cases X 0 <;> cases hmod : (is.filter (· < v)).length % 2 == 0 <;>
        simp_all [Nat.add_mod] <;> omega
    · have heq : X iv.castSucc = X iv.succ := by
        by_contra hne
        exact hmem ((hflip iv).1 hne)
      rw [hprev] at ih'
      rw [hnext, ← heq, ih', hcv, hsv, hfilt]
      simp [hmem]

def buildFalse (f0 : ℕ) : ℕ → List ℕ → List Gate × ℕ
  | _, [] => ([], f0)
  | _, [i0] => ([], i0)
  | base, i0 :: i1 :: rest =>
    let gnot := gNot i1
    let gand := gAnd i0 base
    match rest with
    | [] => ([gnot, gand], base + 1)
    | _ :: _ =>
      let sub := buildFalse f0 (base + 2) rest
      let gor := gOr (base + 1) sub.2
      ([gnot, gand] ++ sub.1 ++ [gor], base + 2 + sub.1.length)

lemma buildFalse_pos_nc (f0 : ℕ) : ∀ base is,
    (buildFalse f0 base is).1.length - notCount ⟨(buildFalse f0 base is).1, 0⟩ = is.length - 1 ∧
    notCount ⟨(buildFalse f0 base is).1, 0⟩ = is.length / 2 := by
  intro base is
  match is with
  | [] => simp [buildFalse, notCount]
  | [i0] => simp [buildFalse, notCount]
  | i0 :: i1 :: rest =>
    cases hrest : rest with
    | nil =>
      subst hrest
      simp [buildFalse, notCount, gNot, gAnd]
    | cons i2 rest' =>
      subst hrest
      have ih := buildFalse_pos_nc f0 (base + 2) (i2 :: rest')
      simp only [buildFalse]
      have hlen : ([gNot i1, gAnd i0 base] ++ (buildFalse f0 (base + 2) (i2 :: rest')).1 ++
          [gOr (base + 1) (buildFalse f0 (base + 2) (i2 :: rest')).2]).length =
          2 + (buildFalse f0 (base + 2) (i2 :: rest')).1.length + 1 := by
        simp [List.length_append]
        omega
      have hnc : notCount ⟨[gNot i1, gAnd i0 base] ++ (buildFalse f0 (base + 2) (i2 :: rest')).1 ++
          [gOr (base + 1) (buildFalse f0 (base + 2) (i2 :: rest')).2], 0⟩ =
          1 + notCount ⟨(buildFalse f0 (base + 2) (i2 :: rest')).1, 0⟩ := by
        rw [nc_append, nc_append, nc_cons, nc_cons, nc_cons]
        simp [notCount, gNot, gAnd, gOr]
      rw [hlen, hnc]
      simp only [List.length_cons] at ih ⊢
      have hnc_le : notCount ⟨(buildFalse f0 (base + 2) (i2 :: rest')).1, 0⟩ ≤
          (buildFalse f0 (base + 2) (i2 :: rest')).1.length := by
        unfold notCount; exact List.length_filter_le _ _
      omega

lemma buildFalse_rb_out (n f0 : ℕ) (hf0 : f0 < n + 2) :
    ∀ base is, n + 2 ≤ base → (∀ k ∈ is, k < n) →
    RB base (buildFalse f0 base is).1 ∧
    (buildFalse f0 base is).2 < base + (buildFalse f0 base is).1.length := by
  intro base is hbase hlt
  match is with
  | [] => exact ⟨RB.nil _, by simp [buildFalse]; omega⟩
  | [i0] => exact ⟨RB.nil _, by simp [buildFalse]; have := hlt i0 (by simp); omega⟩
  | i0 :: i1 :: rest =>
    have hi0 : i0 < base := lt_of_lt_of_le (hlt i0 (by simp)) (by omega)
    have hi1 : i1 < base := lt_of_lt_of_le (hlt i1 (by simp)) (by omega)
    cases hrest : rest with
    | nil =>
      subst hrest
      simp only [buildFalse]
      refine ⟨RB.cons (fun v hv => by simp [gNot] at hv; subst hv; exact hi1)
        (RB.cons (fun v hv => by simp [gAnd] at hv; rcases hv with rfl | rfl <;> omega)
        (RB.nil _)), ?_⟩
      simp
    | cons i2 rest' =>
      subst hrest
      have ih := buildFalse_rb_out n f0 hf0 (base + 2) (i2 :: rest') (by omega)
        (fun k hk => hlt k (by simp [hk]))
      simp only [buildFalse]
      have hrb12 : RB base [gNot i1, gAnd i0 base] :=
        RB.cons (fun v hv => by simp [gNot] at hv; subst hv; exact hi1)
          (RB.cons (fun v hv => by simp [gAnd] at hv; rcases hv with rfl | rfl <;> omega) (RB.nil _))
      have hrb123 : RB base ([gNot i1, gAnd i0 base] ++ (buildFalse f0 (base + 2) (i2 :: rest')).1) :=
        RB.append hrb12 ih.1
      have hrb_all : RB base (([gNot i1, gAnd i0 base] ++ (buildFalse f0 (base + 2) (i2 :: rest')).1) ++
          [gOr (base + 1) (buildFalse f0 (base + 2) (i2 :: rest')).2]) := by
        refine RB.append' (b2 := base + 2 + (buildFalse f0 (base + 2) (i2 :: rest')).1.length)
          hrb123 (RB.cons (fun v hv => ?_) (RB.nil _)) ?_
        · simp [gOr] at hv
          rcases hv with rfl | rfl
          · omega
          · exact ih.2
        · simp [List.length_append]; omega
      refine ⟨by simpa [List.append_assoc] using hrb_all, ?_⟩
      simp [List.length_append]; omega

lemma buildFalse_eval (n f0 : ℕ) (V : ℕ → Bool) (hVf0 : V f0 = false) (l : Fin (n + 1))
    (hVin : ∀ i < n, V i = decide (i < l.val)) :
    ∀ base is, is.Pairwise (· < ·) → (∀ k ∈ is, k < n) →
    Cons V base (buildFalse f0 base is).1 →
    V (buildFalse f0 base is).2 = decide ((is.filter (· < l.val)).length % 2 = 1) := by
  intro base is hpair hlt hC
  match is with
  | [] => simp [buildFalse, hVf0]
  | [i0] =>
    simp only [buildFalse, List.filter_cons]
    rw [hVin i0 (hlt i0 (by simp))]
    by_cases h : i0 < l.val <;> simp [h]
  | i0 :: i1 :: rest =>
    have h01 : i0 < i1 := (List.pairwise_cons.1 hpair).1 i1 (by simp)
    have hi0 := hVin i0 (hlt i0 (by simp))
    have hi1 := hVin i1 (hlt i1 (by simp))
    cases hrest : rest with
    | nil =>
      subst hrest
      simp only [buildFalse, Cons, gNot, gAnd] at hC ⊢
      rcases hC with ⟨hnot, hand, _⟩
      rw [hand, value_and, hnot, value_not, hi0, hi1]
      simp only [List.filter_cons, List.filter_nil]
      by_cases h0 : i0 < l.val <;> by_cases h1 : i1 < l.val
      · simp [h0, h1]
      · simp [h0, h1]
      · omega
      · simp [h0, h1]
    | cons i2 rest' =>
      subst hrest
      have hrest_gt : ∀ k ∈ (i2 :: rest'), i1 < k := fun k hk =>
        (List.pairwise_cons.1 (List.pairwise_cons.1 hpair).2).1 k hk
      simp only [buildFalse] at hC ⊢
      have hC12 : Cons V base [gNot i1, gAnd i0 base] := hC.left.left
      have hCsub : Cons V (base + 2) (buildFalse f0 (base + 2) (i2 :: rest')).1 :=
        hC.left.right' (b2 := base + 2) rfl
      have hCor : Cons V (base + 2 + (buildFalse f0 (base + 2) (i2 :: rest')).1.length)
          [gOr (base + 1) (buildFalse f0 (base + 2) (i2 :: rest')).2] :=
        hC.right' (b2 := base + 2 + (buildFalse f0 (base + 2) (i2 :: rest')).1.length)
          (by simp [List.length_append]; omega)
      have ih := buildFalse_eval n f0 V hVf0 l hVin (base + 2) (i2 :: rest')
        (List.pairwise_cons.1 (List.pairwise_cons.1 hpair).2).2
        (fun k hk => hlt k (by simp [hk])) hCsub
      simp only [gNot, gAnd, gOr] at hCor hC12 ⊢
      rw [hCor.single, value_or, hC12.2.1, value_and, hC12.1, value_not, hi0, hi1, ih]
      by_cases h0 : i0 < l.val <;> by_cases h1 : i1 < l.val
      · have hflen : ((i0 :: i1 :: i2 :: rest').filter (· < l.val)).length =
            ((i2 :: rest').filter (· < l.val)).length + 1 + 1 := by
          rw [List.filter_cons, List.filter_cons]
          simp [h0, h1]
        rw [hflen]
        have hparity : (((i2 :: rest').filter (· < l.val)).length + 1 + 1) % 2 =
            ((i2 :: rest').filter (· < l.val)).length % 2 := by omega
        rw [hparity]
        rcases Nat.mod_two_eq_zero_or_one ((i2 :: rest').filter (· < l.val)).length with hm | hm <;>
          simp [hm, h0, h1]
      · have hnil : (i2 :: rest').filter (· < l.val) = [] := by
          rw [List.filter_eq_nil_iff]
          intro k hk
          have := hrest_gt k hk
          simp [show ¬ (k < l.val) by omega]
        simp [List.filter_cons, h0, h1, hnil]
      · omega
      · have hnil : (i2 :: rest').filter (· < l.val) = [] := by
          rw [List.filter_eq_nil_iff]
          intro k hk
          have := hrest_gt k hk
          simp [show ¬ (k < l.val) by omega]
        simp [List.filter_cons, h0, h1, hnil]

def buildGroup (f0 : ℕ) (b0 bN : Bool) (base : ℕ) (is : List ℕ) : List Gate × (ℕ × ℕ) :=
  match b0 with
  | false =>
    let sub := buildFalse f0 base is
    (sub.1, (sub.2, f0))
  | true =>
    match bN with
    | false =>

      let sub := buildFalse f0 base is
      (sub.1 ++ [gNot sub.2], (base + sub.1.length, sub.2))
    | true =>

      match is with
      | [] => ([], (f0, f0))
      | i0 :: rest =>
        let gnot0 := gNot i0
        let sub := buildFalse f0 (base + 1) rest
        let gor := gOr base sub.2
        ([gnot0] ++ sub.1 ++ [gor], (base + 1 + sub.1.length, f0))

lemma buildGroup_stats (f0 : ℕ) (b0 bN : Bool) (base : ℕ) (is : List ℕ) (hne : 1 ≤ is.length)
    (heven : b0 = bN → is.length % 2 = 0) (hodd : b0 ≠ bN → is.length % 2 = 1) :
    (buildGroup f0 b0 bN base is).1.length - notCount ⟨(buildGroup f0 b0 bN base is).1, 0⟩ = is.length - 1 ∧
    notCount ⟨(buildGroup f0 b0 bN base is).1, 0⟩ =
      (if b0 then (is.length + 1) / 2 else is.length / 2) := by
  cases b0 with
  | false =>
    have h := buildFalse_pos_nc f0 base is
    simpa [buildGroup] using h
  | true =>
    cases bN with
    | false =>
      have h := buildFalse_pos_nc f0 base is
      have hmod := hodd (by decide)
      simp only [buildGroup, List.length_append, List.length_singleton]
      have hnc : notCount ⟨(buildFalse f0 base is).1 ++ [gNot (buildFalse f0 base is).2], 0⟩ =
          notCount ⟨(buildFalse f0 base is).1, 0⟩ + 1 := by
        rw [nc_append, nc_cons]; simp [notCount, gNot]
      rw [hnc]
      simp only [↓reduceIte]
      have hnc_le : notCount ⟨(buildFalse f0 base is).1, 0⟩ ≤ (buildFalse f0 base is).1.length := by
        unfold notCount; exact List.length_filter_le _ _
      omega
    | true =>
      cases is with
      | nil => simp at hne
      | cons i0 rest =>
        have h := buildFalse_pos_nc f0 (base + 1) rest
        have hmod := heven rfl
        simp only [buildGroup, List.length_append, List.length_singleton] at *
        have hnc : notCount ⟨[gNot i0] ++ (buildFalse f0 (base + 1) rest).1 ++ [gOr base (buildFalse f0 (base + 1) rest).2], 0⟩ =
            1 + notCount ⟨(buildFalse f0 (base + 1) rest).1, 0⟩ := by
          rw [nc_append, nc_append, nc_cons, nc_cons]
          simp [notCount, gNot, gOr]
        rw [hnc]
        simp only [↓reduceIte, List.length_cons] at hmod ⊢
        have hnc_le : notCount ⟨(buildFalse f0 (base + 1) rest).1, 0⟩ ≤ (buildFalse f0 (base + 1) rest).1.length := by
          unfold notCount; exact List.length_filter_le _ _
        omega

lemma buildGroup_rb_out (n f0 : ℕ) (hf0 : f0 < n + 2) (b0 bN : Bool) (base : ℕ) (is : List ℕ)
    (hbase : n + 2 ≤ base) (hlt : ∀ k ∈ is, k < n) :
    RB base (buildGroup f0 b0 bN base is).1 ∧
    (buildGroup f0 b0 bN base is).2.1 < base + (buildGroup f0 b0 bN base is).1.length ∧
    (buildGroup f0 b0 bN base is).2.2 < base + (buildGroup f0 b0 bN base is).1.length := by
  cases b0 with
  | false =>
    have h := buildFalse_rb_out n f0 hf0 base is hbase hlt
    exact ⟨h.1, h.2, by simp [buildGroup]; omega⟩
  | true =>
    cases bN with
    | false =>
      have h := buildFalse_rb_out n f0 hf0 base is hbase hlt
      simp only [buildGroup, List.length_append, List.length_singleton]
      refine ⟨RB.append h.1 (RB.cons (fun v hv => by simp [gNot] at hv; subst hv; exact h.2) (RB.nil _)),
        by omega, by omega⟩
    | true =>
      cases is with
      | nil => exact ⟨RB.nil _, by simp [buildGroup]; omega, by simp [buildGroup]; omega⟩
      | cons i0 rest =>
        have hi0 : i0 < base := lt_of_lt_of_le (hlt i0 (by simp)) (by omega)
        have h := buildFalse_rb_out n f0 hf0 (base + 1) rest (by omega) (fun k hk => hlt k (by simp [hk]))
        simp only [buildGroup]
        have hrb1 : RB base [gNot i0] :=
          RB.cons (fun v hv => by simp [gNot] at hv; subst hv; exact hi0) (RB.nil _)
        have hrb12 := RB.append hrb1 h.1
        have hrb123 : RB base (([gNot i0] ++ (buildFalse f0 (base + 1) rest).1) ++
            [gOr base (buildFalse f0 (base + 1) rest).2]) := by
          refine RB.append' (b2 := base + 1 + (buildFalse f0 (base + 1) rest).1.length)
            hrb12 (RB.cons (fun v hv => ?_) (RB.nil _)) ?_
          · simp [gOr] at hv
            rcases hv with rfl | rfl
            · omega
            · exact h.2
          · simp [List.length_append]; omega
        refine ⟨by simpa [List.append_assoc] using hrb123, ?_, ?_⟩
        · simp [List.length_append]; omega
        · simp [List.length_append]; omega

lemma buildGroup_eval (n f0 : ℕ) (V : ℕ → Bool) (hVf0 : V f0 = false) (l : Fin (n + 1))
    (hVin : ∀ i < n, V i = decide (i < l.val)) (b0 bN : Bool) (base : ℕ) (is : List ℕ)
    (hne : 1 ≤ is.length)
    (hpair : is.Pairwise (· < ·)) (hlt : ∀ k ∈ is, k < n)
    (hC : Cons V base (buildGroup f0 b0 bN base is).1) :
    V (buildGroup f0 b0 bN base is).2.1 = xor b0 (decide ((is.filter (· < l.val)).length % 2 = 1)) ∧
    V (buildGroup f0 b0 bN base is).2.2 =
      (if b0 = true ∧ bN = false then !(xor b0 (decide ((is.filter (· < l.val)).length % 2 = 1))) else false) := by
  cases b0 with
  | false =>
    simp only [buildGroup, Bool.false_eq_true, false_and, ↓reduceIte]
    have hev := buildFalse_eval n f0 V hVf0 l hVin base is hpair hlt hC
    rw [hev, hVf0]
    simp
  | true =>
    cases bN with
    | false =>
      simp only [buildGroup] at hC ⊢
      have hC1 : Cons V base (buildFalse f0 base is).1 := hC.left
      have hC2 : Cons V (base + (buildFalse f0 base is).1.length) [gNot (buildFalse f0 base is).2] :=
        hC.right' rfl
      have hev := buildFalse_eval n f0 V hVf0 l hVin base is hpair hlt hC1
      change V (base + (buildFalse f0 base is).1.length) = _ ∧ V (buildFalse f0 base is).2 = _
      have hnot_eq := hC2.single
      simp only [gNot] at hnot_eq
      rw [hnot_eq, value_not, hev]
      simp
    | true =>
      cases is with
      | nil => simp at hne
      | cons i0 rest =>
        simp only [buildGroup, and_false, ↓reduceIte] at hC ⊢
        have hC1 : Cons V base [gNot i0] := hC.left.left
        have hCsub : Cons V (base + 1) (buildFalse f0 (base + 1) rest).1 :=
          hC.left.right' rfl
        have hCor : Cons V (base + 1 + (buildFalse f0 (base + 1) rest).1.length)
            [gOr base (buildFalse f0 (base + 1) rest).2] :=
          hC.right' (by simp [List.length_append]; omega)
        have hev := buildFalse_eval n f0 V hVf0 l hVin (base + 1) rest
          (List.pairwise_cons.1 hpair).2 (fun k hk => hlt k (by simp [hk])) hCsub
        change V (base + 1 + (buildFalse f0 (base + 1) rest).1.length) = _ ∧ V f0 = _
        have h1eq := hC1.single
        have h2eq := hCor.single
        simp only [gNot, gOr] at h1eq h2eq
        rw [h2eq, value_or, h1eq, value_not, hVin i0 (hlt i0 (by simp)), hev, hVf0]
        refine ⟨?_, rfl⟩
        by_cases h0 : i0 < l.val
        · simp [List.filter_cons, h0]
          cases hmod : (rest.filter (· < l.val)).length % 2 == 1 <;> simp_all <;> omega
        · have hnil : rest.filter (· < l.val) = [] := by
            rw [List.filter_eq_nil_iff]
            intro k hk
            have hlt0 := (List.pairwise_cons.1 hpair).1 k hk
            simp [show ¬ (k < l.val) by omega]
          simp [List.filter_cons, h0, hnil]

lemma buildFalse_fan (f0 : ℕ) : ∀ base is, FanInTwo ⟨(buildFalse f0 base is).1, 0⟩ := by
  intro base is
  match is with
  | [] => intro g hg; simp [buildFalse] at hg
  | [_] => intro g hg; simp [buildFalse] at hg
  | i0 :: i1 :: rest =>
    cases hrest : rest with
    | nil =>
      intro g hg
      simp only [buildFalse, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp [gNot, gAnd]
    | cons i2 rest' =>
      have ih := buildFalse_fan f0 (base + 2) (i2 :: rest')
      intro g hg
      simp only [buildFalse, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ((rfl | rfl) | hg) | rfl
      · simp [gNot]
      · simp [gAnd]
      · exact ih g hg
      · simp [gOr]

lemma buildGroup_fan (f0 : ℕ) (b0 bN : Bool) (base : ℕ) (is : List ℕ) :
    FanInTwo ⟨(buildGroup f0 b0 bN base is).1, 0⟩ := by
  cases b0 with
  | false => exact buildFalse_fan f0 base is
  | true =>
    cases bN with
    | false =>
      intro g hg
      simp only [buildGroup, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl
      · exact buildFalse_fan f0 base is g hg
      · simp [gNot]
    | true =>
      cases is with
      | nil => intro g hg; simp [buildGroup] at hg
      | cons i0 rest =>
        intro g hg
        simp only [buildGroup, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (rfl | hg) | rfl
        · simp [gNot]
        · exact buildFalse_fan f0 (base + 1) rest g hg
        · simp [gOr]

def groupLoop (n d : ℕ) (color : Fin n → Fin d) (X : Fin (n + 1) → Fin d → Bool) :
    (k : ℕ) → k ≤ d → ℕ → List Gate × (Fin d → ℕ × ℕ)
  | 0, _, _ => ([], fun _ => (n, n))
  | k + 1, hk, base =>
    let j : Fin d := ⟨k, hk⟩
    let prev := groupLoop n d color X k (Nat.le_of_lt hk) base
    let cur := buildGroup n (X 0 j) (X (Fin.last n) j) (base + prev.1.length) (groupList color j)
    (prev.1 ++ cur.1, fun j' => if j'.val = k then cur.2 else prev.2 j')

lemma groupLoop_fan (n d : ℕ) (color : Fin n → Fin d) (X : Fin (n + 1) → Fin d → Bool) :
    ∀ k (hk : k ≤ d) base, FanInTwo ⟨(groupLoop n d color X k hk base).1, 0⟩ := by
  intro k
  induction k with
  | zero => intro _ _ g hg; simp [groupLoop] at hg
  | succ k ih =>
    intro hk base g hg
    simp only [groupLoop, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih _ _ g hg
    · exact buildGroup_fan n _ _ _ _ g hg

lemma groupLoop_rb_out (n d : ℕ) (color : Fin n → Fin d) (X : Fin (n + 1) → Fin d → Bool) :
    ∀ k (hk : k ≤ d) base, n + 2 ≤ base →
    RB base (groupLoop n d color X k hk base).1 ∧
    (∀ j : Fin d, j.val < k →
      ((groupLoop n d color X k hk base).2 j).1 < base + (groupLoop n d color X k hk base).1.length ∧
      ((groupLoop n d color X k hk base).2 j).2 < base + (groupLoop n d color X k hk base).1.length) := by
  intro k
  induction k with
  | zero => intro _ base _; exact ⟨RB.nil _, fun j hj => by omega⟩
  | succ k ih =>
    intro hk base hbase
    obtain ⟨hrb1, ho1⟩ := ih (Nat.le_of_lt hk) base hbase
    set b1 := base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length
    obtain ⟨hrb2, h21, h22⟩ := buildGroup_rb_out n n (by omega)
      (X 0 ⟨k, hk⟩) (X (Fin.last n) ⟨k, hk⟩) b1 (groupList color ⟨k, hk⟩)
      (by omega) (fun u hu => groupList_lt color ⟨k, hk⟩ hu)
    refine ⟨RB.append hrb1 hrb2, fun j hj => ?_⟩
    simp only [groupLoop, List.length_append]
    split_ifs with heq
    · dsimp only [b1] at h21 h22; omega
    · obtain ⟨ha, hb⟩ := ho1 j (by omega)
      omega

lemma groupLoop_eval (n d : ℕ) (color : Fin n → Fin d) (hsurj : Function.Surjective color)
    (X : Fin (n + 1) → Fin d → Bool)
    (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j)
    (V : ℕ → Bool) (l : Fin (n + 1))
    (hVf0 : V n = false) (hVin : ∀ i < n, V i = decide (i < l.val)) :
    ∀ k (hk : k ≤ d) base, Cons V base (groupLoop n d color X k hk base).1 →
    ∀ j : Fin d, j.val < k →
      V ((groupLoop n d color X k hk base).2 j).1 = X l j ∧
      V ((groupLoop n d color X k hk base).2 j).2 =
        (if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false) := by
  intro k
  induction k with
  | zero => intro _ _ _ j hj; omega
  | succ k ih =>
    intro hk base hC j hj
    simp only [groupLoop] at hC ⊢
    by_cases heq : j.val = k
    · have hjeq : j = ⟨k, hk⟩ := Fin.ext heq
      subst hjeq
      simp only [ite_true]
      have hev := buildGroup_eval n n V hVf0 l hVin (X 0 ⟨k, hk⟩) (X (Fin.last n) ⟨k, hk⟩)
        (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length)
        (groupList color ⟨k, hk⟩) (groupList_pos color hsurj ⟨k, hk⟩)
        (groupList_sorted color ⟨k, hk⟩)
        (fun u hu => groupList_lt color ⟨k, hk⟩ hu) (hC.right' rfl)
      have hruns := eval_runs_count (fun l => X l ⟨k, hk⟩) (groupList color ⟨k, hk⟩)
        (groupList_sorted color ⟨k, hk⟩) (fun u hu => groupList_lt color ⟨k, hk⟩ hu)
        (fun i => by rw [hX i ⟨k, hk⟩, groupList_mem]; exact ⟨fun h => ⟨i.isLt, h⟩, fun ⟨_, h⟩ => h⟩) l
      rw [← hruns] at hev
      exact hev
    · simp only [heq, ite_false]
      exact ih (Nat.le_of_lt hk) base hC.left j (by omega)

lemma group_falls_eq (n d : ℕ) (color : Fin n → Fin d) (hsurj : Function.Surjective color)
    (X : Fin (n + 1) → Fin d → Bool)
    (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j)
    (j : Fin d) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card =
      (if X 0 j then ((groupList color j).length + 1) / 2 else (groupList color j).length / 2) := by
  let R := ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true)).card
  let F := ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card
  have hsum : F + R = (groupList color j).length := by
    rw [groupList_len, ← Finset.card_union_of_disjoint]
    · congr 1; ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨hc, _, _⟩ | ⟨hc, _, _⟩) <;> exact hc
      · intro hc
        have hne := (hX i j).2 hc
        cases h1 : X i.castSucc j <;> cases h2 : X i.succ j <;> simp_all
    · rw [Finset.disjoint_left]; intro i h1 h2; simp_all
  have hdiff : ∀ (m : ℕ) (hm : m ≤ n),
      (((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true)).card : ℤ) -
      (((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card : ℤ) =
      (if X ⟨m, by omega⟩ j then 1 else 0) - (if X 0 j then 1 else 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
      simp [h0]
    | succ m ih =>
      intro hm
      have ih' := ih (Nat.le_of_lt hm)
      let im : Fin n := ⟨m, hm⟩
      have hlt_iff : ∀ i : Fin n, i.val < m + 1 ↔ i.val < m ∨ i = im := by
        intro i; simp [im, Fin.ext_iff]; omega
      have hs1 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m + 1 ∧ color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true)) =
          ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true)) ∪
          (if color im = j ∧ X im.castSucc j = false ∧ X im.succ j = true then {im} else ∅) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hlt_iff]
        split_ifs with hc
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨h1 | rfl, h2, h3, h4⟩
            · exact Or.inl ⟨h1, h2, h3, h4⟩
            · exact Or.inr rfl
          · rintro (⟨h1, h2, h3, h4⟩ | rfl)
            · exact ⟨Or.inl h1, h2, h3, h4⟩
            · exact ⟨Or.inr rfl, hc⟩
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · rintro ⟨h1 | rfl, h2, h3, h4⟩
            · exact ⟨h1, h2, h3, h4⟩
            · exact False.elim (hc ⟨h2, h3, h4⟩)
          · rintro ⟨h1, h2, h3, h4⟩
            exact ⟨Or.inl h1, h2, h3, h4⟩
      have hs2 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m + 1 ∧ color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)) =
          ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)) ∪
          (if color im = j ∧ X im.castSucc j = true ∧ X im.succ j = false then {im} else ∅) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hlt_iff]
        split_ifs with hc
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨h1 | rfl, h2, h3, h4⟩
            · exact Or.inl ⟨h1, h2, h3, h4⟩
            · exact Or.inr rfl
          · rintro (⟨h1, h2, h3, h4⟩ | rfl)
            · exact ⟨Or.inl h1, h2, h3, h4⟩
            · exact ⟨Or.inr rfl, hc⟩
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · rintro ⟨h1 | rfl, h2, h3, h4⟩
            · exact ⟨h1, h2, h3, h4⟩
            · exact False.elim (hc ⟨h2, h3, h4⟩)
          · rintro ⟨h1, h2, h3, h4⟩
            exact ⟨Or.inl h1, h2, h3, h4⟩
      have hd1 : Disjoint ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true))
          (if color im = j ∧ X im.castSucc j = false ∧ X im.succ j = true then {im} else ∅) := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        split_ifs at hi2 <;> simp_all [im]
      have hd2 : Disjoint ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false))
          (if color im = j ∧ X im.castSucc j = true ∧ X im.succ j = false then {im} else ∅) := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        split_ifs at hi2 <;> simp_all [im]
      rw [hs1, hs2, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
      have him_c : (⟨m, by omega⟩ : Fin (n + 1)) = im.castSucc := rfl
      have him_s : (⟨m + 1, by omega⟩ : Fin (n + 1)) = im.succ := rfl
      rw [him_c] at ih'
      rw [him_s]
      by_cases hcol : color im = j
      · have hne := (hX im j).2 hcol
        cases h1 : X im.castSucc j <;> cases h2 : X im.succ j <;> simp_all <;> omega
      · have heq : X im.castSucc j = X im.succ j := by
          by_contra hne; exact hcol ((hX im j).1 hne)
        simp [hcol, heq] at ih' ⊢; omega
  have hfull := hdiff n le_rfl
  have hfn : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n ∧ color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true) =
      (Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = false ∧ X i.succ j = true) := by
    ext i; simp [i.isLt]
  have hfn2 : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n ∧ color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false) =
      (Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false) := by
    ext i; simp [i.isLt]
  rw [hfn, hfn2] at hfull
  have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hlast] at hfull
  cases h0 : X 0 j <;> cases hN : X (Fin.last n) j <;> simp_all <;> omega

lemma groupLoop_stats (n d : ℕ) (color : Fin n → Fin d) (hsurj : Function.Surjective color)
    (X : Fin (n + 1) → Fin d → Bool) (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j) :
    ∀ k (hk : k ≤ d) base,
    (groupLoop n d color X k hk base).1.length - notCount ⟨(groupLoop n d color X k hk base).1, 0⟩ =
      (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < k then (groupList color j).length - 1 else 0) ∧
    notCount ⟨(groupLoop n d color X k hk base).1, 0⟩ =
      (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < k then
        ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card
      else 0) := by
  intro k
  induction k with
  | zero => intro _ _; simp [groupLoop, notCount]
  | succ k ih =>
    intro hk base
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_lt hk) base
    set jk : Fin d := ⟨k, hk⟩
    have hruns := eval_runs_count (fun l => X l jk) (groupList color jk) (groupList_sorted color jk)
      (fun u hu => groupList_lt color jk hu)
      (fun i => by rw [hX i jk, groupList_mem]; exact ⟨fun h => ⟨i.isLt, h⟩, fun ⟨_, h⟩ => h⟩) (Fin.last n)
    have hfilt_n : (groupList color jk).filter (· < (Fin.last n).val) = groupList color jk := by
      rw [List.filter_eq_self]
      intro u hu; simp [Fin.val_last]; exact groupList_lt color jk hu
    rw [hfilt_n] at hruns
    have heven_jk : X 0 jk = X (Fin.last n) jk → (groupList color jk).length % 2 = 0 := by
      intro heq
      rw [hruns] at heq
      cases h0 : X 0 jk <;> rw [h0] at heq <;> simp at heq <;> exact heq
    have hodd_jk : X 0 jk ≠ X (Fin.last n) jk → (groupList color jk).length % 2 = 1 := by
      intro hne
      rw [hruns] at hne
      cases h0 : X 0 jk <;> rw [h0] at hne <;> simp at hne <;> exact hne
    have hst := buildGroup_stats n (X 0 jk) (X (Fin.last n) jk)
      (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length)
      (groupList color jk) (groupList_pos color hsurj jk) heven_jk hodd_jk
    have hfg := group_falls_eq n d color hsurj X hX jk
    simp only [groupLoop, List.length_append]
    have hnc_add : notCount ⟨(groupLoop n d color X k (Nat.le_of_lt hk) base).1 ++
        (buildGroup n (X 0 jk) (X (Fin.last n) jk)
          (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1, 0⟩ =
        notCount ⟨(groupLoop n d color X k (Nat.le_of_lt hk) base).1, 0⟩ +
        notCount ⟨(buildGroup n (X 0 jk) (X (Fin.last n) jk)
          (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1, 0⟩ :=
      nc_append _ _
    have hnc_le1 : notCount ⟨(groupLoop n d color X k (Nat.le_of_lt hk) base).1, 0⟩ ≤
        (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length := by
      unfold notCount; exact List.length_filter_le _ _
    have hnc_le2 : notCount ⟨(buildGroup n (X 0 jk) (X (Fin.last n) jk)
        (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1, 0⟩ ≤
        (buildGroup n (X 0 jk) (X (Fin.last n) jk)
          (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1.length := by
      unfold notCount; exact List.length_filter_le _ _
    have hsplit_sum : ∀ (F : Fin d → ℕ),
        (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < k + 1 then F j else 0) =
        (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < k then F j else 0) + F jk := by
      intro F
      have hs : F jk = (Finset.univ : Finset (Fin d)).sum (fun j => if j = jk then F j else 0) := by simp
      rw [hs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj1 : j.val < k
      · have hne : j ≠ jk := fun h => by have := congrArg Fin.val h; simp [jk] at this; omega
        simp [hj1, hne, show j.val < k + 1 by omega]
      · by_cases hj2 : j = jk
        · subst hj2; simp [jk]
        · have hjne : j.val ≠ k := fun h => hj2 (Fin.ext h)
          simp [hj1, hj2, show ¬ (j.val < k + 1) by omega]
    rw [hnc_add, hsplit_sum, hsplit_sum]
    refine ⟨?_, ?_⟩
    · have hst1 := hst.1
      change _ = (Finset.univ.sum fun j => if j.val < k then (groupList color j).length - 1 else 0) + ((groupList color jk).length - 1)
      have hlen_sub : (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length -
          notCount { gates := (groupLoop n d color X k (Nat.le_of_lt hk) base).1, output := 0 } +
          ((buildGroup n (X 0 jk) (X (Fin.last n) jk)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1.length -
          notCount { gates := (buildGroup n (X 0 jk) (X (Fin.last n) jk)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1, output := 0 }) =
          ((groupLoop n d color X k (Nat.le_of_lt hk) base).1.length +
          (buildGroup n (X 0 jk) (X (Fin.last n) jk)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1.length) -
          (notCount { gates := (groupLoop n d color X k (Nat.le_of_lt hk) base).1, output := 0 } +
          notCount { gates := (buildGroup n (X 0 jk) (X (Fin.last n) jk)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color jk)).1, output := 0 }) := by
        omega
      dsimp only [jk] at hst1 hnc_le2 ⊢
      change (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length +
          (buildGroup n (X 0 ⟨k, hk⟩) (X (Fin.last n) ⟨k, hk⟩)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color ⟨k, hk⟩)).1.length -
          (notCount { gates := (groupLoop n d color X k (Nat.le_of_lt hk) base).1, output := 0 } +
          notCount { gates := (buildGroup n (X 0 ⟨k, hk⟩) (X (Fin.last n) ⟨k, hk⟩)
            (base + (groupLoop n d color X k (Nat.le_of_lt hk) base).1.length) (groupList color ⟨k, hk⟩)).1, output := 0 }) =
          (Finset.univ.sum fun j => if j.val < k then (groupList color j).length - 1 else 0) + ((groupList color ⟨k, hk⟩).length - 1)
      omega
    · rw [ih2, hst.2, hfg]

def remapGate (wmap : ℕ → ℕ) (base inN : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun u => if u < inN then wmap u else base + (u - inN))⟩

def remapList (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate) : List Gate :=
  gs.map (remapGate wmap base inN)

lemma remapList_len (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate) :
    (remapList wmap base inN gs).length = gs.length := List.length_map _

lemma remapList_nc (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate) :
    notCount ⟨remapList wmap base inN gs, 0⟩ = notCount ⟨gs, 0⟩ := by
  unfold notCount remapList
  rw [List.filter_map]
  simp only [Function.comp_def, remapGate, List.length_map]
  rfl

lemma remapList_fan (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate) (hfan : FanInTwo ⟨gs, 0⟩) :
    FanInTwo ⟨remapList wmap base inN gs, 0⟩ := by
  intro g hg
  simp only [remapList, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨ho, hl⟩ := hfan g' hg'
  exact ⟨ho, by simpa [remapGate] using hl⟩

lemma remapList_rb (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate)
    (hmap : ∀ u < inN, wmap u < base) (hRB : RB inN gs) :
    RB base (remapList wmap base inN gs) := by
  suffices ∀ (k : ℕ) (gs' : List Gate), RB (inN + k) gs' → RB (base + k) (remapList wmap base inN gs') by
    simpa using this 0 gs (by simpa using hRB)
  intro k gs' h
  induction gs' generalizing k with
  | nil => exact RB.nil _
  | cons g gs' ih =>
    cases h with
    | cons hv htail =>
      simp only [remapList, List.map_cons]
      refine RB.cons ?_ ?_
      · intro v hv'
        simp only [remapGate, List.mem_map] at hv'
        obtain ⟨u, hu, rfl⟩ := hv'
        have hul := hv u hu
        split_ifs with hlt
        · exact lt_of_lt_of_le (hmap u hlt) (by omega)
        · omega
      · exact ih (k + 1) (by simpa [Nat.add_assoc] using htail)

lemma remapList_eval (wmap : ℕ → ℕ) (base inN : ℕ) (gs : List Gate)
    (W V : ℕ → Bool) (hmap : ∀ u < inN, V (wmap u) = W u)
    (hRB : RB inN gs)
    (hCW : Cons W inN gs) (hCV : Cons V base (remapList wmap base inN gs)) :
    ∀ k < gs.length, V (base + k) = W (inN + k) := by
  suffices ∀ (offset : ℕ) (gs' : List Gate), RB (inN + offset) gs' →
      Cons W (inN + offset) gs' →
      Cons V (base + offset) (remapList wmap base inN gs') →
      (∀ u < offset, V (base + u) = W (inN + u)) →
      ∀ k < gs'.length, V (base + offset + k) = W (inN + offset + k) by
    simpa using this 0 gs (by simpa using hRB) hCW hCV (fun u hu => by omega)
  intro offset gs'
  induction gs' generalizing offset with
  | nil => intro _ _ _ _ k hk; simp at hk
  | cons g gs' ih =>
    intro hRB' hCW' hCV' hprev k hk
    cases hRB' with
    | cons hv htail =>
      simp only [remapList, List.map_cons, Cons] at hCW' hCV'
      have hhead : V (base + offset) = W (inN + offset) := by
        rw [hCV'.1, hCW'.1]
        unfold value remapGate
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        dsimp only [Function.comp_def]
        have hu_lt := hv u hu
        split_ifs with hlt
        · exact hmap u hlt
        · have hlt2 : u - inN < offset := by omega
          have heq := hprev (u - inN) hlt2
          rw [heq, show inN + (u - inN) = u by omega]
      cases k with
      | zero => simpa using hhead
      | succ k' =>
        have hprev' : ∀ u < offset + 1, V (base + u) = W (inN + u) := by
          intro u hu
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | rfl
          · exact hprev u hlt
          · exact hhead
        have ih' := ih (offset + 1) (by simpa [Nat.add_assoc] using htail)
          (by simpa [Nat.add_assoc] using hCW'.2)
          (by simpa [remapList, Nat.add_assoc] using hCV'.2)
          hprev' k' (by simp at hk; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'

lemma rhs_to_lhs (n d a b : ℕ) (color : Fin n → Fin d) (X : Fin (n + 1) → Fin d → Bool)
    (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (hd : 0 < d) (hsurj : Function.Surjective color)
    (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j)
    (k : ℕ) (D : Circuit) (out : Fin (a + 1) → ℕ)
    (hfb : ((Finset.univ : Finset (Fin n)).filter (fun i =>
      X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card + k ≤ b)
    (hfanD : FanInTwo D) (hRBD : ReadsBack (2 * d + 2) D)
    (houtD_lt : D.output < 2 * d + 2 + D.size)
    (hposD : D.size - notCount D ≤ d - 1)
    (hnegD : notCount D ≤ k)
    (hout_lt : ∀ t, out t < 2 * d + 2 + D.size)
    (hout_eval : ∀ l t, (D.wires (List.ofFn (X l) ++ List.ofFn (fun j =>
      if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false) ++ [false, true])).getD (out t) false = W t l) :
    ∃ (C : Circuit) (tap : Fin d → ℕ) (out' : Fin (a + 1) → ℕ),
      (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        C.size - notCount C ≤ n - 1 ∧ notCount C ≤ b) ∧
      (∀ j, tap j < n + 2 + C.size) ∧ (∀ t, out' t < n + 2 + C.size) ∧
      (∀ l j, (C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true])).getD (tap j) false = X l j) ∧
      ∀ l t, (C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true])).getD (out' t) false = W t l := by
  let tLoop := groupLoop n d color X d le_rfl (n + 2)
  let base2 := n + 2 + tLoop.1.length
  let wmap : ℕ → ℕ := fun u =>
    if h1 : u < d then (tLoop.2 ⟨u, h1⟩).1
    else if h2 : u < 2 * d then (tLoop.2 ⟨u - d, by omega⟩).2
    else if u = 2 * d then n
    else n + 1
  let remD := remapList wmap base2 (2 * d + 2) D.gates
  let C : Circuit := ⟨tLoop.1 ++ remD, 0⟩
  let tap : Fin d → ℕ := fun j => (tLoop.2 j).1
  let out' : Fin (a + 1) → ℕ := fun t =>
    if out t < 2 * d + 2 then wmap (out t) else base2 + (out t - (2 * d + 2))
  have hrb1_out := groupLoop_rb_out n d color X d le_rfl (n + 2) le_rfl
  have hrb1 : RB (n + 2) tLoop.1 := hrb1_out.1
  have htap_lt_loop : ∀ j : Fin d, (tLoop.2 j).1 < base2 ∧ (tLoop.2 j).2 < base2 :=
    fun j => hrb1_out.2 j j.isLt
  have hwmap_lt : ∀ u < 2 * d + 2, wmap u < base2 := by
    intro u hu
    dsimp only [wmap]
    split_ifs with h1 h2 h3
    · exact (htap_lt_loop ⟨u, h1⟩).1
    · exact (htap_lt_loop ⟨u - d, by omega⟩).2
    · change n < n + 2 + tLoop.1.length; omega
    · change n + 1 < n + 2 + tLoop.1.length; omega
  have hRBD' : RB (2 * d + 2) D.gates := ReadsBack_to_RB (2 * d + 2) D hRBD
  have hrb2 : RB base2 remD := remapList_rb wmap base2 (2 * d + 2) D.gates hwmap_lt hRBD'
  have hrbC : RB (n + 2) C.gates := RB.append hrb1 hrb2
  have hfanC : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with hg | hg
    · exact groupLoop_fan n d color X d le_rfl (n + 2) g hg
    · exact remapList_fan wmap base2 (2 * d + 2) D.gates hfanD g hg
  have hCsize : C.size = tLoop.1.length + D.size := by
    simp [C, Circuit.size, remD, remapList_len]
  have hncC : notCount C = notCount ⟨tLoop.1, 0⟩ + notCount D := by
    change notCount ⟨tLoop.1 ++ remD, 0⟩ = notCount ⟨tLoop.1, 0⟩ + notCount ⟨D.gates, 0⟩
    rw [nc_append, remapList_nc]
  have hstats := groupLoop_stats n d color hsurj X hX d le_rfl (n + 2)
  have hsum_len : (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < d then (groupList color j).length - 1 else 0) = n - d := by
    have hs1 : (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < d then (groupList color j).length - 1 else 0) =
        (Finset.univ : Finset (Fin d)).sum (fun j => (groupList color j).length - 1) :=
      Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    rw [hs1]
    have hpos : ∀ j : Fin d, 1 ≤ (groupList color j).length := fun j => groupList_pos color hsurj j
    have hadd : (Finset.univ : Finset (Fin d)).sum (fun j => (groupList color j).length - 1) + d =
        (Finset.univ : Finset (Fin d)).sum (fun j => (groupList color j).length) := by
      have hd_sum : d = (Finset.univ : Finset (Fin d)).sum (fun _ : Fin d => 1) := by simp
      conv_lhs => rhs; rw [hd_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hpos j; omega
    have htot := groupList_sum_len color
    omega
  have hfalls_sum : (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < d then
      ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card else 0) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card := by
    have hs1 : (Finset.univ : Finset (Fin d)).sum (fun j => if j.val < d then
        ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card else 0) =
        (Finset.univ : Finset (Fin d)).sum (fun j =>
        ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card) :=
      Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    rw [hs1]
    have hfib := Finset.card_eq_sum_card_fiberwise (f := color)
      (s := (Finset.univ : Finset (Fin n)).filter (fun i => X i.castSucc (color i) = true ∧ X i.succ (color i) = false))
      (t := (Finset.univ : Finset (Fin d))) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, h1, h2⟩; rw [hc]; exact ⟨⟨h1, h2⟩, rfl⟩
    · rintro ⟨⟨h1, h2⟩, hc⟩; rw [← hc]; exact ⟨rfl, h1, h2⟩
  have hpos1 : tLoop.1.length - notCount ⟨tLoop.1, 0⟩ = n - d := hstats.1.trans hsum_len
  have hneg1 : notCount ⟨tLoop.1, 0⟩ = ((Finset.univ : Finset (Fin n)).filter (fun i =>
      X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card := hstats.2.trans hfalls_sum
  have hdn : d ≤ n := by
    have h1 := groupList_sum_len color
    have h2 : (Finset.univ : Finset (Fin d)).sum (fun _ : Fin d => 1) ≤
        (Finset.univ : Finset (Fin d)).sum (fun j => (groupList color j).length) :=
      Finset.sum_le_sum fun j _ => groupList_pos color hsurj j
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at h2
    omega
  have hnc_le1 : notCount ⟨tLoop.1, 0⟩ ≤ tLoop.1.length := by unfold notCount; exact List.length_filter_le _ _
  have hnc_leD : notCount D ≤ D.size := by unfold notCount Circuit.size; exact List.length_filter_le _ _
  refine ⟨C, tap, out', ⟨hfanC, RB_to_ReadsBack (n + 2) C hrbC, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · change 0 < n + 2 + C.size; omega
  · rw [hCsize, hncC]; omega
  · rw [hncC, hneg1]; omega
  · intro j; change (tLoop.2 j).1 < n + 2 + C.size; have := (htap_lt_loop j).1; omega
  · intro t
    dsimp only [out']
    split_ifs with hlt
    · have := hwmap_lt (out t) hlt; omega
    · have := hout_lt t; rw [hCsize]; dsimp only [base2]; omega
  · intro l j
    let act := List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]
    have hact_len : act.length = n + 2 := by simp [act]
    have hspec := run_spec C.gates act (by simpa [hact_len] using hrbC)
    have hCW : Cons (fun u => (C.wires act).getD u false) (n + 2) C.gates := by
      change Cons (fun u => (run C.gates act).getD u false) (n + 2) C.gates
      rw [← hact_len]
      exact hspec.2
    have hV0 : (C.wires act).getD n false = false := by
      change (run C.gates act).getD n false = false
      rw [hspec.1 n (by rw [hact_len]; omega)]
      dsimp only [act]
      rw [getD_append_right' _ _ _ _ (by simp)]
      simp
    have hVin : ∀ i < n, (C.wires act).getD i false = decide (i < l.val) := by
      intro i hi
      change (run C.gates act).getD i false = decide (i < l.val)
      rw [hspec.1 i (by rw [hact_len]; omega)]
      dsimp only [act]
      rw [getD_append_left' _ _ _ _ (by simp [hi])]
      simp [hi]
    exact (groupLoop_eval n d color hsurj X hX (fun u => (C.wires act).getD u false) l hV0 hVin d le_rfl (n + 2) hCW.left j j.isLt).1
  · intro l t
    let act := List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]
    let log := List.ofFn (X l) ++ List.ofFn (fun j =>
      if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false) ++ [false, true]
    have hact_len : act.length = n + 2 := by simp [act]
    have hlog_len : log.length = 2 * d + 2 := by simp [log]; omega
    have hspecC := run_spec C.gates act (by simpa [hact_len] using hrbC)
    have hspecD := run_spec D.gates log (by simpa [hlog_len] using hRBD')
    have hCC : Cons (fun u => (C.wires act).getD u false) (n + 2) C.gates := by
      change Cons (fun u => (run C.gates act).getD u false) (n + 2) C.gates
      rw [← hact_len]
      exact hspecC.2
    have hCD : Cons (fun u => (D.wires log).getD u false) (2 * d + 2) D.gates := by
      change Cons (fun u => (run D.gates log).getD u false) (2 * d + 2) D.gates
      rw [← hlog_len]
      exact hspecD.2
    have hV0 : (C.wires act).getD n false = false := by
      change (run C.gates act).getD n false = false
      rw [hspecC.1 n (by rw [hact_len]; omega)]
      dsimp only [act]
      rw [getD_append_right' _ _ _ _ (by simp)]; simp
    have hV1 : (C.wires act).getD (n + 1) false = true := by
      change (run C.gates act).getD (n + 1) false = true
      rw [hspecC.1 (n + 1) (by rw [hact_len]; omega)]
      dsimp only [act]
      rw [getD_append_right' _ _ _ _ (by simp)]; simp
    have hVin : ∀ i < n, (C.wires act).getD i false = decide (i < l.val) := by
      intro i hi
      change (run C.gates act).getD i false = decide (i < l.val)
      rw [hspecC.1 i (by rw [hact_len]; omega)]
      dsimp only [act]
      rw [getD_append_left' _ _ _ _ (by simp [hi])]; simp [hi]
    have hgl := groupLoop_eval n d color hsurj X hX (fun u => (C.wires act).getD u false) l hV0 hVin d le_rfl (n + 2) hCC.left
    have hlog_in : ∀ u < 2 * d + 2, (C.wires act).getD (wmap u) false = (D.wires log).getD u false := by
      intro u hu
      have hDu : (D.wires log).getD u false = log.getD u false := by
        change (run D.gates log).getD u false = log.getD u false
        exact hspecD.1 u (by rw [hlog_len]; exact hu)
      rw [hDu]
      dsimp only [wmap]
      split_ifs with h1 h2 h3
      · have hje := (hgl ⟨u, h1⟩ h1).1
        rw [hje]
        symm
        dsimp only [log]
        rw [getD_append_left' _ _ _ _ (by simp; omega), getD_append_left' _ _ _ _ (by simp [h1])]
        simp [h1]
      · have hj : u - d < d := by omega
        have hje := (hgl ⟨u - d, hj⟩ hj).2
        rw [hje]
        symm
        dsimp only [log]
        have hlt_app : u < (List.ofFn (X l) ++ List.ofFn (fun j =>
            if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false)).length := by
          simp; omega
        rw [getD_append_left' _ _ _ _ hlt_app, getD_append_right' _ _ _ _ (by simp; omega)]
        simp [hj]
      · subst h3
        rw [hV0]
        symm
        dsimp only [log]
        rw [getD_append_right' _ _ _ _ (by simp; omega)]
        simp [show 2 * d - (d + d) = 0 by omega]
      · have hu_eq : u = 2 * d + 1 := by omega
        subst hu_eq
        rw [hV1]
        symm
        dsimp only [log]
        rw [getD_append_right' _ _ _ _ (by simp; omega)]
        simp [show 2 * d + 1 - (d + d) = 1 by omega]
    have hrem_eval := remapList_eval wmap base2 (2 * d + 2) D.gates
      (fun u => (D.wires log).getD u false) (fun u => (C.wires act).getD u false)
      hlog_in hRBD' hCD (hCC.right' rfl)
    rw [← hout_eval l t]
    dsimp only [out']
    split_ifs with hlt
    · exact hlog_in (out t) hlt
    · have hk : out t - (2 * d + 2) < D.gates.length := by
        have := hout_lt t; change out t < 2 * d + 2 + D.gates.length at this; omega
      have hev := hrem_eval (out t - (2 * d + 2)) hk
      rw [show 2 * d + 2 + (out t - (2 * d + 2)) = out t by omega] at hev
      exact hev

end Forward

section Backward

private def decGateOp : DecidableEq GateOp
  | .and, .and => isTrue rfl
  | .or, .or => isTrue rfl
  | .not, .not => isTrue rfl
  | .mod m1, .mod m2 => if h : m1 = m2 then isTrue (h ▸ rfl) else isFalse (fun hh => by cases hh; exact h rfl)
  | .maj, .maj => isTrue rfl
  | .and, .or | .and, .not | .and, .mod _ | .and, .maj
  | .or, .and | .or, .not | .or, .mod _ | .or, .maj
  | .not, .and | .not, .or | .not, .mod _ | .not, .maj
  | .mod _, .and | .mod _, .or | .mod _, .not | .mod _, .maj
  | .maj, .and | .maj, .or | .maj, .not | .maj, .mod _ =>
    isFalse (fun h => by cases h)

local instance : DecidableEq GateOp := decGateOp

def effInputs (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma value_eff (V : ℕ → Bool) (g : Gate) :
    value V g = g.op.eval ((effInputs g).map V) := by
  cases h : g.op <;> simp [value, effInputs, h, GateOp.eval]
  cases g.inputs <;> rfl

lemma effInputs_mem {g : Gate} {u : ℕ} (hu : u ∈ effInputs g) : u ∈ g.inputs := by
  cases h : g.op <;> simp [effInputs, h] at hu
  · exact hu
  · exact hu
  · exact List.mem_of_mem_take hu
  · exact hu
  · exact hu

lemma effInputs_len_not {g : Gate} (h : g.op = GateOp.not) : (effInputs g).length ≤ 1 := by
  simp [effInputs, h]

lemma effInputs_len_pos {C : Circuit} (hfan : FanInTwo C) {w N : ℕ} (hN : N ≤ w) (hw : w < N + C.size)
    (hnot : (gateAt C (w - N)).op ≠ GateOp.not) :
    ((gateAt C (w - N)).op = GateOp.and ∨ (gateAt C (w - N)).op = GateOp.or) ∧
    (effInputs (gateAt C (w - N))).length ≤ 2 := by
  have hmem : gateAt C (w - N) ∈ C.gates := by
    unfold gateAt
    have hj : w - N < C.gates.length := by change w - N < C.size; omega
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨ho, hl⟩ := hfan _ hmem
  rcases ho with ho | ho | ho
  · refine ⟨Or.inl ho, ?_⟩; simp [effInputs, ho]; exact hl
  · refine ⟨Or.inr ho, ?_⟩; simp [effInputs, ho]; exact hl
  · exact absurd ho hnot

def effCh (N : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  if w < N then [] else (effInputs (gateAt C (w - N))).filter (· < w)

lemma effCh_lt (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ effCh N C w) : u < w := by
  unfold effCh at hu
  split_ifs at hu with h
  · simp at hu
  · simp only [List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2

lemma effCh_ge (N : ℕ) (C : Circuit) (w u : ℕ) (hu : u ∈ effCh N C w) : N ≤ w := by
  unfold effCh at hu
  split_ifs at hu with h
  · simp at hu
  · omega

lemma effCh_eq_effInputs (N : ℕ) (C : Circuit) (hRB : ReadsBack N C)
    {w : ℕ} (hN : N ≤ w) (hw : w < N + C.size) :
    effCh N C w = effInputs (gateAt C (w - N)) := by
  unfold effCh
  rw [if_neg (by omega), List.filter_eq_self]
  intro u hu
  simp only [decide_eq_true_eq]
  have hrb := hRB (w - N) (by change w - N < C.size; omega) u (effInputs_mem hu)
  omega

def reach (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  insert w (((effCh N C w).toFinset.attach).biUnion (fun ⟨u, _⟩ =>
    if h : u < w then reach N C u else ∅))
termination_by w
decreasing_by exact h

lemma reach_eq (N : ℕ) (C : Circuit) (w : ℕ) :
    reach N C w = insert w ((effCh N C w).toFinset.biUnion (reach N C)) := by
  rw [reach]
  congr 1; ext z
  simp only [Finset.mem_biUnion, Finset.mem_attach, List.mem_toFinset, true_and, Subtype.exists]
  constructor
  · rintro ⟨u, hu, hz⟩
    split_ifs at hz with hlt
    · exact ⟨u, hu, hz⟩
    · simp at hz
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu, by simp [effCh_lt N C w u hu, hz]⟩

lemma self_mem_reach (N : ℕ) (C : Circuit) (w : ℕ) : w ∈ reach N C w := by
  rw [reach_eq]; exact Finset.mem_insert_self _ _

lemma mem_reach_le (N : ℕ) (C : Circuit) : ∀ w z, z ∈ reach N C w → z ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z hz
    rw [reach_eq] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact le_rfl
    · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz'
      obtain ⟨u, hu, hzu⟩ := hz'
      have hul := effCh_lt N C w u hu
      exact le_trans (ih u hul z hzu) (Nat.le_of_lt hul)

lemma reach_trans (N : ℕ) (C : Circuit) :
    ∀ w z, z ∈ reach N C w → reach N C z ⊆ reach N C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z hz x hx
    rw [reach_eq] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hx
    · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz'
      obtain ⟨u, hu, hzu⟩ := hz'
      have hul := effCh_lt N C w u hu
      have hsub := ih u hul z hzu hx
      rw [reach_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu, hsub⟩)

lemma mem_reach_parent (N : ℕ) (C : Circuit) :
    ∀ w z, z ∈ reach N C w → z ≠ w → ∃ p ∈ reach N C w, z ∈ effCh N C p := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z hz hne
    rw [reach_eq] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact absurd rfl hne
    · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz'
      obtain ⟨u, hu, hzu⟩ := hz'
      by_cases hzu_eq : z = u
      · subst hzu_eq; exact ⟨w, self_mem_reach N C w, hu⟩
      · obtain ⟨p, hp, hzp⟩ := ih u (effCh_lt N C w u hu) z hzu hzu_eq
        have hu_mem : u ∈ reach N C w := by
          rw [reach_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu, self_mem_reach N C u⟩)
        exact ⟨p, reach_trans N C w u hu_mem hp, hzp⟩

def leaves (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val ∈ reach (n + 2) C w)

lemma mem_leaves (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ leaves n C w ↔ i.val ∈ reach (n + 2) C w := by
  simp [leaves]

lemma leaves_card_eq (n : ℕ) (C : Circuit) (w : ℕ) :
    (leaves n C w).card = ((reach (n + 2) C w).filter (· < n)).card := by
  unfold leaves
  refine Finset.card_bij (fun i _ => i.val) (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi, i.isLt⟩)
    (fun a _ b _ h => Fin.ext h)
    (fun k hk => by
      simp only [Finset.mem_filter] at hk
      exact ⟨⟨k, hk.2⟩, by simp [hk.1], rfl⟩)

lemma leaves_mono (n : ℕ) (C : Circuit) {w z : ℕ} (hz : z ∈ reach (n + 2) C w) :
    leaves n C z ⊆ leaves n C w := by
  intro i hi
  rw [mem_leaves] at hi ⊢
  exact reach_trans (n + 2) C w z hz hi

lemma leaves_of_lt_n (n : ℕ) (C : Circuit) {w : ℕ} (hw : w < n) :
    leaves n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_leaves, reach_eq]
  have hemp : effCh (n + 2) C w = [] := by unfold effCh; simp [show w < n + 2 by omega]
  simp [hemp, Fin.ext_iff]

lemma leaves_of_const (n : ℕ) (C : Circuit) {w : ℕ} (h1 : n ≤ w) (h2 : w < n + 2) :
    leaves n C w = ∅ := by
  ext i
  rw [mem_leaves, reach_eq]
  have hemp : effCh (n + 2) C w = [] := by unfold effCh; simp [h2]
  simp only [hemp, List.toFinset_nil, Finset.biUnion_empty, Finset.mem_insert,
    Finset.notMem_empty, or_false, iff_false]
  omega

lemma leaves_of_ge (n : ℕ) (C : Circuit) {w : ℕ} (hN : n + 2 ≤ w) :
    leaves n C w = (effCh (n + 2) C w).toFinset.biUnion (leaves n C) := by
  ext i
  simp only [mem_leaves, Finset.mem_biUnion, List.mem_toFinset]
  rw [reach_eq]
  simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro (heq | h)
    · have := i.isLt; omega
    · exact h
  · exact Or.inr

def wireVal (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

lemma wireVal_lt_N (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    {w : ℕ} (hw : w < N) : wireVal C x w = x.getD w false := by
  have hspec := run_spec C.gates x (hx ▸ ReadsBack_to_RB N C hRB)
  change (run C.gates x).getD w false = x.getD w false
  exact hspec.1 w (hx ▸ hw)

lemma wireVal_gate (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    {w : ℕ} (hN : N ≤ w) (hw : w < N + C.size) :
    wireVal C x w = value (wireVal C x) (gateAt C (w - N)) := by
  have hRB' := ReadsBack_to_RB N C hRB
  have hspec := run_spec C.gates x (hx ▸ hRB')
  have hC : Cons (wireVal C x) N C.gates := by
    change Cons (fun u => (run C.gates x).getD u false) N C.gates
    rw [← hx]; exact hspec.2
  suffices ∀ (k : ℕ) (gs : List Gate), gs = C.gates.drop k → Cons (wireVal C x) (N + k) gs →
      ∀ j (hj : j < gs.length), wireVal C x (N + k + j) = value (wireVal C x) (gs[j]'hj) by
    have hlt : w - N < C.gates.length := by change w - N < C.size; omega
    have res := this 0 C.gates (by simp) (by simpa using hC) (w - N) hlt
    have hweq : N + 0 + (w - N) = w := by omega
    rw [hweq] at res
    rw [res]
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hlt]
  intro k gs
  induction gs generalizing k with
  | nil => intro _ _ j hj; simp at hj
  | cons g gs ih =>
    intro hdrop hCg j hj
    cases j with
    | zero => simpa using hCg.1
    | succ j' =>
      have ih' := ih (k + 1) (by have := congrArg List.tail hdrop; simpa [List.tail_drop] using this)
        (by simpa [Nat.add_assoc] using hCg.2) j' (by simp at hj; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'

lemma eval_eq_of_agree_on_leaves (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (x y : List Bool) (hx : x.length = n + 2) (hy : y.length = n + 2)
    (hc0 : x.getD n false = y.getD n false) (hc1 : x.getD (n + 1) false = y.getD (n + 1) false) :
    ∀ w < n + 2 + C.size,
    (∀ i ∈ leaves n C w, x.getD i.val false = y.getD i.val false) →
    wireVal C x w = wireVal C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hagree
    by_cases hwn : w < n
    · rw [wireVal_lt_N (n + 2) C hRB x hx (by omega), wireVal_lt_N (n + 2) C hRB y hy (by omega)]
      exact hagree ⟨w, hwn⟩ (by rw [leaves_of_lt_n n C hwn]; exact Finset.mem_singleton_self _)
    · by_cases hwN : w < n + 2
      · rw [wireVal_lt_N (n + 2) C hRB x hx hwN, wireVal_lt_N (n + 2) C hRB y hy hwN]
        have hcases : w = n ∨ w = n + 1 := by omega
        rcases hcases with rfl | rfl <;> assumption
      · have hN : n + 2 ≤ w := by omega
        rw [wireVal_gate (n + 2) C hRB x hx hN hw, wireVal_gate (n + 2) C hRB y hy hN hw]
        rw [value_eff, value_eff]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_ch : u ∈ effCh (n + 2) C w := by
          rw [effCh_eq_effInputs (n + 2) C hRB hN hw]; exact hu
        have hu_lt := effCh_lt (n + 2) C w u hu_ch
        apply ih u hu_lt (by omega)
        intro i hi
        apply hagree i
        rw [leaves_of_ge n C hN]
        exact Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu_ch, hi⟩

lemma actual_len (n : ℕ) (l : Fin (n + 1)) :
    (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]).length = n + 2 := by
  simp

lemma actual_agree_except (n : ℕ) (i : Fin n) :
    let act := fun l : Fin (n + 1) => List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]
    (act i.castSucc).getD n false = (act i.succ).getD n false ∧
    (act i.castSucc).getD (n + 1) false = (act i.succ).getD (n + 1) false ∧
    ∀ k : Fin n, k ≠ i → (act i.castSucc).getD k.val false = (act i.succ).getD k.val false := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [getD_append_right' _ _ _ _ (by simp), getD_append_right' _ _ _ _ (by simp)]; simp
  · rw [getD_append_right' _ _ _ _ (by simp), getD_append_right' _ _ _ _ (by simp)]; simp
  · intro k hk
    rw [getD_append_left' _ _ _ _ (by simp [k.isLt]), getD_append_left' _ _ _ _ (by simp [k.isLt])]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, k.isLt, ↓reduceDIte, Option.getD_some]
    have hki : k.val ≠ i.val := fun h => hk (Fin.ext h)
    have hc : (i.castSucc : ℕ) = i.val := rfl
    have hs : (i.succ : ℕ) = i.val + 1 := rfl
    rw [hc, hs]
    congr 1
    exact propext (by omega)

lemma wireVal_eq_of_not_mem_leaves (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    {w : ℕ} (hw : w < n + 2 + C.size) {i : Fin n} (hi : i ∉ leaves n C w) :
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]) w =
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]) w := by
  obtain ⟨h1, h2, h3⟩ := actual_agree_except n i
  apply eval_eq_of_agree_on_leaves n C hRB _ _ (actual_len n i.castSucc) (actual_len n i.succ) h1 h2 w hw
  intro k hk
  exact h3 k (fun hki => hi (hki ▸ hk))

def fallsOf (n : ℕ) (f : Fin (n + 1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f i.castSucc = true ∧ f i.succ = false)).card

def risesOf (n : ℕ) (f : Fin (n + 1) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f i.castSucc = false ∧ f i.succ = true)).card

lemma fallsOf_not (n : ℕ) (f : Fin (n + 1) → Bool) :
    fallsOf n (fun l => !(f l)) = risesOf n f := by
  unfold fallsOf risesOf
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases f i.castSucc <;> cases f i.succ <;> simp

lemma rises_sub_falls (n : ℕ) (f : Fin (n + 1) → Bool) :
    (risesOf n f : ℤ) - (fallsOf n f : ℤ) =
    (if f (Fin.last n) then 1 else 0) - (if f 0 then 1 else 0) := by
  have hdiff : ∀ (m : ℕ) (hm : m ≤ n),
      (((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = false ∧ f i.succ = true)).card : ℤ) -
      (((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = true ∧ f i.succ = false)).card : ℤ) =
      (if f ⟨m, by omega⟩ then 1 else 0) - (if f 0 then 1 else 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
      simp [h0]
    | succ m ih =>
      intro hm
      have ih' := ih (Nat.le_of_lt hm)
      let im : Fin n := ⟨m, hm⟩
      have hlt_iff : ∀ i : Fin n, i.val < m + 1 ↔ i.val < m ∨ i = im := by
        intro i; simp [im, Fin.ext_iff]; omega
      have hs1 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m + 1 ∧ f i.castSucc = false ∧ f i.succ = true)) =
          ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = false ∧ f i.succ = true)) ∪
          (if f im.castSucc = false ∧ f im.succ = true then {im} else ∅) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hlt_iff]
        split_ifs with hc
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨h1 | rfl, h2, h3⟩; exact Or.inl ⟨h1, h2, h3⟩; exact Or.inr rfl
          · rintro (⟨h1, h2, h3⟩ | rfl); exact ⟨Or.inl h1, h2, h3⟩; exact ⟨Or.inr rfl, hc⟩
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · rintro ⟨h1 | rfl, h2, h3⟩; exact ⟨h1, h2, h3⟩; exact False.elim (hc ⟨h2, h3⟩)
          · rintro ⟨h1, h2, h3⟩; exact ⟨Or.inl h1, h2, h3⟩
      have hs2 : ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m + 1 ∧ f i.castSucc = true ∧ f i.succ = false)) =
          ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = true ∧ f i.succ = false)) ∪
          (if f im.castSucc = true ∧ f im.succ = false then {im} else ∅) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hlt_iff]
        split_ifs with hc
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨h1 | rfl, h2, h3⟩; exact Or.inl ⟨h1, h2, h3⟩; exact Or.inr rfl
          · rintro (⟨h1, h2, h3⟩ | rfl); exact ⟨Or.inl h1, h2, h3⟩; exact ⟨Or.inr rfl, hc⟩
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · rintro ⟨h1 | rfl, h2, h3⟩; exact ⟨h1, h2, h3⟩; exact False.elim (hc ⟨h2, h3⟩)
          · rintro ⟨h1, h2, h3⟩; exact ⟨Or.inl h1, h2, h3⟩
      have hd1 : Disjoint ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = false ∧ f i.succ = true))
          (if f im.castSucc = false ∧ f im.succ = true then {im} else ∅) := by
        rw [Finset.disjoint_left]; intro i hi1 hi2; split_ifs at hi2 <;> simp_all [im]
      have hd2 : Disjoint ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m ∧ f i.castSucc = true ∧ f i.succ = false))
          (if f im.castSucc = true ∧ f im.succ = false then {im} else ∅) := by
        rw [Finset.disjoint_left]; intro i hi1 hi2; split_ifs at hi2 <;> simp_all [im]
      rw [hs1, hs2, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
      have him_c : (⟨m, by omega⟩ : Fin (n + 1)) = im.castSucc := rfl
      have him_s : (⟨m + 1, by omega⟩ : Fin (n + 1)) = im.succ := rfl
      rw [him_c] at ih'
      rw [him_s]
      cases h1 : f im.castSucc <;> cases h2 : f im.succ <;> simp_all <;> omega
  have hf := hdiff n le_rfl
  have h1 : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n ∧ f i.castSucc = false ∧ f i.succ = true) =
      (Finset.univ : Finset (Fin n)).filter (fun i => f i.castSucc = false ∧ f i.succ = true) := by
    ext i; simp [i.isLt]
  have h2 : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n ∧ f i.castSucc = true ∧ f i.succ = false) =
      (Finset.univ : Finset (Fin n)).filter (fun i => f i.castSucc = true ∧ f i.succ = false) := by
    ext i; simp [i.isLt]
  rw [h1, h2] at hf
  exact hf

lemma fallsOf_and (n : ℕ) (a b : Fin (n + 1) → Bool) :
    fallsOf n (fun l => a l && b l) ≤ fallsOf n a + fallsOf n b := by
  unfold fallsOf
  calc ((Finset.univ : Finset (Fin n)).filter (fun i => (a i.castSucc && b i.castSucc) = true ∧
      (a i.succ && b i.succ) = false)).card
      ≤ (((Finset.univ : Finset (Fin n)).filter (fun i => a i.castSucc = true ∧ a i.succ = false)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun i => b i.castSucc = true ∧ b i.succ = false))).card := by
        refine Finset.card_le_card fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        cases ha1 : a i.castSucc <;> cases hb1 : b i.castSucc <;>
          cases ha2 : a i.succ <;> cases hb2 : b i.succ <;> simp_all
    _ ≤ _ := Finset.card_union_le _ _

lemma fallsOf_or (n : ℕ) (a b : Fin (n + 1) → Bool) :
    fallsOf n (fun l => a l || b l) ≤ fallsOf n a + fallsOf n b := by
  unfold fallsOf
  calc ((Finset.univ : Finset (Fin n)).filter (fun i => (a i.castSucc || b i.castSucc) = true ∧
      (a i.succ || b i.succ) = false)).card
      ≤ (((Finset.univ : Finset (Fin n)).filter (fun i => a i.castSucc = true ∧ a i.succ = false)) ∪
        ((Finset.univ : Finset (Fin n)).filter (fun i => b i.castSucc = true ∧ b i.succ = false))).card := by
        refine Finset.card_le_card fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        cases ha1 : a i.castSucc <;> cases hb1 : b i.castSucc <;>
          cases ha2 : a i.succ <;> cases hb2 : b i.succ <;> simp_all
    _ ≤ _ := Finset.card_union_le _ _

lemma allPos_card (n : ℕ) (C : Circuit) :
    (((Finset.range C.size).image (· + (n + 2))).filter
      (fun w => (gateAt C (w - (n + 2))).op ≠ GateOp.not)).card = C.size - notCount C := by
  have h1 : (((Finset.range C.size).image (· + (n + 2))).filter
      (fun w => (gateAt C (w - (n + 2))).op ≠ GateOp.not)).card =
      ((Finset.range C.size).filter (fun idx => (gateAt C idx).op ≠ GateOp.not)).card := by
    refine Finset.card_bij (fun w _ => w - (n + 2)) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hw ⊢
      rcases hw with ⟨⟨idx, hidx, rfl⟩, hne⟩
      refine ⟨by omega, ?_⟩
      simpa using hne
    · intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hw1 hw2
      omega
    · intro idx hidx
      simp only [Finset.mem_filter, Finset.mem_range] at hidx
      refine ⟨idx + (n + 2), ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      exact ⟨⟨idx, hidx.1, rfl⟩, by simpa using hidx.2⟩
  rw [h1]
  have hsplit : ((Finset.range C.size).filter (fun idx => (gateAt C idx).op ≠ GateOp.not)).card +
      ((Finset.range C.size).filter (fun idx => (gateAt C idx).op = GateOp.not)).card = C.size := by
    have hu : ((Finset.range C.size).filter (fun idx => (gateAt C idx).op ≠ GateOp.not)) ∪
        ((Finset.range C.size).filter (fun idx => (gateAt C idx).op = GateOp.not)) = Finset.range C.size := by
      ext idx; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]; tauto
    have hd : Disjoint ((Finset.range C.size).filter (fun idx => (gateAt C idx).op ≠ GateOp.not))
        ((Finset.range C.size).filter (fun idx => (gateAt C idx).op = GateOp.not)) := by
      rw [Finset.disjoint_left]; intro idx h1 h2; simp_all
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]
  have hnc_eq : ((Finset.range C.size).filter (fun idx => (gateAt C idx).op = GateOp.not)).card = notCount C := by
    have haux : ∀ gs : List Gate,
        ((Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨GateOp.or, []⟩).op = GateOp.not)).card =
        (gs.filter (fun g => decide (g.op = GateOp.not))).length := by
      intro gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.length_cons]
        have hbi : ((Finset.range (gs.length + 1)).filter
            (fun idx => ((g :: gs).getD idx ⟨GateOp.or, []⟩).op = GateOp.not)) =
            (match g.op with | GateOp.not => {0} | _ => ∅) ∪
            (((Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨GateOp.or, []⟩).op = GateOp.not)).image (· + 1)) := by
          ext idx
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
          cases idx with
          | zero => cases hg : g.op <;> simp [hg]
          | succ idx' => cases hg : g.op <;> simp [hg, Finset.mem_singleton, Nat.succ_eq_add_one]
        have hd : Disjoint (match g.op with | GateOp.not => {0} | _ => ∅)
            (((Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨GateOp.or, []⟩).op = GateOp.not)).image (· + 1)) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          cases hg : g.op <;> simp [hg] at hx1 hx2
          omega
        rw [hbi, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (fun a b h => by omega), ih]
        cases hg : g.op <;> simp [hg, Nat.add_comm]
    unfold notCount Circuit.size gateAt at *
    refine (haux C.gates).trans ?_
    congr 1
    apply List.filter_congr
    intro g _
    cases hg : g.op <;> simp [hg]
  omega

lemma list_card_two_eq {l : List ℕ} (hl : l.length ≤ 2) (hfc : l.toFinset.card = 2) :
    ∃ u1 u2, l = [u1, u2] ∧ u1 ≠ u2 := by
  match l with
  | [] => simp at hfc
  | [_] => simp at hfc
  | [u1, u2] =>
    refine ⟨u1, u2, rfl, ?_⟩
    intro heq; subst heq; simp at hfc
  | _ :: _ :: _ :: _ => simp at hl

lemma list_card_one_eq {l : List ℕ} (hl : l.length ≤ 1) (hfc : l.toFinset.card = 1) :
    ∃ u, l = [u] := by
  match l with
  | [] => simp at hfc
  | [u] => exact ⟨u, rfl⟩
  | _ :: _ :: _ => simp at hl

structure VProps (n : ℕ) (C : Circuit) (out0 : ℕ) : Prop where
  hout0 : out0 < n + 2 + C.size
  hn_pos : 1 ≤ n
  hV_in : (reach (n + 2) C out0).filter (· < n) = Finset.range n
  hV_const : (reach (n + 2) C out0).filter (fun w => n ≤ w ∧ w < n + 2) = ∅
  hV_pos_all : (reach (n + 2) C out0).filter (fun w => n + 2 ≤ w ∧ (gateAt C (w - (n + 2))).op ≠ GateOp.not) =
    ((Finset.range C.size).image (· + (n + 2))).filter (fun w => (gateAt C (w - (n + 2))).op ≠ GateOp.not)
  hdeg : ∀ u ∈ (reach (n + 2) C out0).erase out0,
    ((reach (n + 2) C out0).filter (fun w => u ∈ effCh (n + 2) C w)).card = 1
  hnot_ch : ∀ w ∈ reach (n + 2) C out0, n + 2 ≤ w → (gateAt C (w - (n + 2))).op = GateOp.not →
    ∃ u, effCh (n + 2) C w = [u] ∧ u ∈ reach (n + 2) C out0
  hpos_ch : ∀ w ∈ reach (n + 2) C out0, n + 2 ≤ w → (gateAt C (w - (n + 2))).op ≠ GateOp.not →
    ∃ u1 u2, effCh (n + 2) C w = [u1, u2] ∧ u1 ≠ u2 ∧ u1 ∈ reach (n + 2) C out0 ∧ u2 ∈ reach (n + 2) C out0

lemma V_structure (n : ℕ) (C : Circuit) (out0 : ℕ) (hn : 1 ≤ n)
    (hfan : FanInTwo C) (hRB : ReadsBack (n + 2) C) (hout0 : out0 < n + 2 + C.size)
    (hposC : C.size - notCount C ≤ n - 1) (hleaves : leaves n C out0 = Finset.univ) :
    VProps n C out0 := by
  let N := n + 2
  let V := reach N C out0
  let V_in := V.filter (· < n)
  let V_const := V.filter (fun w => n ≤ w ∧ w < N)
  let V_not := V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op = GateOp.not)
  let V_pos := V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)
  let AllPos := ((Finset.range C.size).image (· + N)).filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not)
  have hV_lt : ∀ w ∈ V, w < N + C.size := fun w hw => lt_of_le_of_lt (mem_reach_le N C out0 w hw) hout0
  have hVin_eq : V_in = Finset.range n := by
    ext k
    simp only [V_in, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hk
      have hi : (⟨k, hk⟩ : Fin n) ∈ leaves n C out0 := by rw [hleaves]; exact Finset.mem_univ _
      rw [mem_leaves] at hi
      exact ⟨hi, hk⟩
  have hVin_card : V_in.card = n := by rw [hVin_eq, Finset.card_range]
  have hVpos_sub : V_pos ⊆ AllPos := by
    intro w hw
    simp only [V_pos, AllPos, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hw ⊢
    have hlt := hV_lt w hw.1
    have hNw : N ≤ w := hw.2.1
    exact ⟨⟨w - N, by omega, by omega⟩, hw.2.2⟩
  have hAllPos_card : AllPos.card = C.size - notCount C := allPos_card n C
  have hVpos_le : V_pos.card ≤ n - 1 := le_trans (Finset.card_le_card hVpos_sub) (hAllPos_card ▸ hposC)
  have hpart_card : V.card = V_in.card + V_const.card + V_not.card + V_pos.card := by
    have h12 : V_in ∪ V_const = V.filter (· < N) := by
      ext w; simp only [V_in, V_const, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, by omega⟩
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        by_cases h3 : w < n
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨h1, by omega, h2⟩
    have d12 : Disjoint V_in V_const := by
      rw [Finset.disjoint_left]; intro w ha hb; simp only [V_in, V_const, Finset.mem_filter] at ha hb; omega
    have h34 : V_not ∪ V_pos = V.filter (N ≤ ·) := by
      ext w; simp only [V_not, V_pos, Finset.mem_union, Finset.mem_filter]; tauto
    have d34 : Disjoint V_not V_pos := by
      rw [Finset.disjoint_left]; intro w ha hb; simp only [V_not, V_pos, Finset.mem_filter] at ha hb; exact hb.2.2 ha.2.2
    have hall : V.filter (· < N) ∪ V.filter (N ≤ ·) = V := by
      ext w; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun h => by by_cases hlt : w < N <;> [exact Or.inl ⟨h, hlt⟩; exact Or.inr ⟨h, by omega⟩]⟩
    have dall : Disjoint (V.filter (· < N)) (V.filter (N ≤ ·)) := by
      rw [Finset.disjoint_left]; intro w ha hb; simp only [Finset.mem_filter] at ha hb; omega
    rw [← hall, Finset.card_union_of_disjoint dall, ← h12, ← h34,
      Finset.card_union_of_disjoint d12, Finset.card_union_of_disjoint d34]
    omega
  have hch_sub : ∀ w ∈ V, ∀ u ∈ effCh N C w, u ∈ V.erase out0 := by
    intro w hw u hu
    have hu_lt := effCh_lt N C w u hu
    have hw_le := mem_reach_le N C out0 w hw
    have hu_mem : u ∈ V := reach_trans N C out0 w hw (by
      rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu, self_mem_reach N C u⟩))
    exact Finset.mem_erase.2 ⟨by omega, hu_mem⟩
  have hdeg_ge : ∀ u ∈ V.erase out0, 1 ≤ (V.filter (fun w => u ∈ effCh N C w)).card := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨p, hp, hup⟩ := mem_reach_parent N C out0 u hu.2 hu.1
    exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hp, hup⟩⟩
  have hdouble : ∑ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card =
      ∑ w ∈ V, (effCh N C w).toFinset.card := by
    calc ∑ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card
        = ∑ u ∈ V.erase out0, ∑ w ∈ V, if u ∈ effCh N C w then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_; rw [Finset.card_filter]
      _ = ∑ w ∈ V, ∑ u ∈ V.erase out0, if u ∈ effCh N C w then 1 else 0 := Finset.sum_comm
      _ = ∑ w ∈ V, ((V.erase out0).filter (fun u => u ∈ effCh N C w)).card := by
          refine Finset.sum_congr rfl fun w _ => ?_; rw [Finset.card_filter]
      _ = ∑ w ∈ V, (effCh N C w).toFinset.card := by
          refine Finset.sum_congr rfl fun w hw => ?_
          congr 1; ext u
          simp only [Finset.mem_filter, List.mem_toFinset]
          exact ⟨fun h => h.2, fun hu => ⟨hch_sub w hw u hu, hu⟩⟩
  have hsplit_V_sum : ∑ w ∈ V, (effCh N C w).toFinset.card =
      ∑ w ∈ V_not, (effCh N C w).toFinset.card + ∑ w ∈ V_pos, (effCh N C w).toFinset.card := by
    have h34 : V_not ∪ V_pos = V.filter (N ≤ ·) := by
      ext w; simp only [V_not, V_pos, Finset.mem_union, Finset.mem_filter]; tauto
    have d34 : Disjoint V_not V_pos := by
      rw [Finset.disjoint_left]; intro w ha hb; simp only [V_not, V_pos, Finset.mem_filter] at ha hb; exact hb.2.2 ha.2.2
    have hall : V.filter (· < N) ∪ V.filter (N ≤ ·) = V := by
      ext w; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun h => by by_cases hlt : w < N <;> [exact Or.inl ⟨h, hlt⟩; exact Or.inr ⟨h, by omega⟩]⟩
    have dall : Disjoint (V.filter (· < N)) (V.filter (N ≤ ·)) := by
      rw [Finset.disjoint_left]; intro w ha hb; simp only [Finset.mem_filter] at ha hb; omega
    have hzero : ∑ w ∈ V.filter (· < N), (effCh N C w).toFinset.card = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter] at hw
      have hemp : effCh N C w = [] := by unfold effCh; simp [hw.2]
      simp [hemp]
    rw [← hall, Finset.sum_union dall, hzero, zero_add, ← h34, Finset.sum_union d34]
  have hch_bound : ∑ w ∈ V, (effCh N C w).toFinset.card ≤ V_not.card + 2 * V_pos.card := by
    rw [hsplit_V_sum]
    have hle1 : ∑ w ∈ V_not, (effCh N C w).toFinset.card ≤ V_not.card := by
      calc ∑ w ∈ V_not, (effCh N C w).toFinset.card
          ≤ ∑ _w ∈ V_not, 1 := Finset.sum_le_sum fun w hw => by
            rw [Finset.mem_filter] at hw
            rw [effCh_eq_effInputs N C hRB hw.2.1 (hV_lt w hw.1)]
            exact le_trans (List.toFinset_card_le _) (effInputs_len_not hw.2.2)
        _ = V_not.card := by simp
    have hle2 : ∑ w ∈ V_pos, (effCh N C w).toFinset.card ≤ 2 * V_pos.card := by
      calc ∑ w ∈ V_pos, (effCh N C w).toFinset.card
          ≤ ∑ _w ∈ V_pos, 2 := Finset.sum_le_sum fun w hw => by
            rw [Finset.mem_filter] at hw
            rw [effCh_eq_effInputs N C hRB hw.2.1 (hV_lt w hw.1)]
            exact le_trans (List.toFinset_card_le _) (effInputs_len_pos hfan hw.2.1 (hV_lt w hw.1) hw.2.2).2
        _ = 2 * V_pos.card := by simp [mul_comm]
    omega
  have hsum_ge_erase : (V.erase out0).card ≤ ∑ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card := by
    calc (V.erase out0).card = ∑ _u ∈ V.erase out0, 1 := by simp
      _ ≤ ∑ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card := Finset.sum_le_sum hdeg_ge
  have herase_card : (V.erase out0).card = V.card - 1 := Finset.card_erase_of_mem (self_mem_reach N C out0)
  have hVconst_eq : V_const.card = 0 := by omega
  have hVpos_eq_n : V_pos.card = n - 1 := by omega
  have hVpos_eq_all : V_pos = AllPos := Finset.eq_of_subset_of_card_le hVpos_sub (by omega)
  have hdeg_sum_eq : ∑ u ∈ V.erase out0, 1 = ∑ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]; omega
  have hdeg_one : ∀ u ∈ V.erase out0, (V.filter (fun w => u ∈ effCh N C w)).card = 1 := by
    have hiff := (Finset.sum_eq_sum_iff_of_le (s := V.erase out0)
      (f := fun _ => 1) (g := fun u => (V.filter (fun w => u ∈ effCh N C w)).card) hdeg_ge).1 hdeg_sum_eq
    exact fun u hu => (hiff u hu).symm
  have hsplit_eq : ∑ w ∈ V_not, (effCh N C w).toFinset.card + ∑ w ∈ V_pos, (effCh N C w).toFinset.card =
      V_not.card + 2 * V_pos.card := by
    omega
  have hle1 : ∀ w ∈ V_not, (effCh N C w).toFinset.card ≤ 1 := fun w hw => by
    rw [Finset.mem_filter] at hw
    rw [effCh_eq_effInputs N C hRB hw.2.1 (hV_lt w hw.1)]
    exact le_trans (List.toFinset_card_le _) (effInputs_len_not hw.2.2)
  have hle2 : ∀ w ∈ V_pos, (effCh N C w).toFinset.card ≤ 2 := fun w hw => by
    rw [Finset.mem_filter] at hw
    rw [effCh_eq_effInputs N C hRB hw.2.1 (hV_lt w hw.1)]
    exact le_trans (List.toFinset_card_le _) (effInputs_len_pos hfan hw.2.1 (hV_lt w hw.1) hw.2.2).2
  have hsum1 : ∑ w ∈ V_not, (effCh N C w).toFinset.card = V_not.card := by
    have : ∑ w ∈ V_not, (effCh N C w).toFinset.card ≤ V_not.card := by
      calc _ ≤ ∑ _w ∈ V_not, 1 := Finset.sum_le_sum hle1
        _ = _ := by simp
    have : ∑ w ∈ V_pos, (effCh N C w).toFinset.card ≤ 2 * V_pos.card := by
      calc _ ≤ ∑ _w ∈ V_pos, 2 := Finset.sum_le_sum hle2
        _ = _ := by simp [mul_comm]
    omega
  have hsum2 : ∑ w ∈ V_pos, (effCh N C w).toFinset.card = 2 * V_pos.card := by omega
  have hnot_fc : ∀ w ∈ V_not, (effCh N C w).toFinset.card = 1 := by
    have hiff := (Finset.sum_eq_sum_iff_of_le (s := V_not) (f := fun w => (effCh N C w).toFinset.card)
      (g := fun _ => 1) hle1).1 (by simpa using hsum1)
    exact hiff
  have hpos_fc : ∀ w ∈ V_pos, (effCh N C w).toFinset.card = 2 := by
    have hiff := (Finset.sum_eq_sum_iff_of_le (s := V_pos) (f := fun w => (effCh N C w).toFinset.card)
      (g := fun _ => 2) hle2).1 (by simpa [mul_comm] using hsum2)
    exact hiff
  refine ⟨hout0, hn, hVin_eq, Finset.card_eq_zero.1 hVconst_eq, hVpos_eq_all, hdeg_one, ?_, ?_⟩
  · intro w hw hN hnot
    have hw_not : w ∈ V_not := Finset.mem_filter.2 ⟨hw, hN, hnot⟩
    have hlen : (effCh N C w).length ≤ 1 := by
      rw [effCh_eq_effInputs N C hRB hN (hV_lt w hw)]; exact effInputs_len_not hnot
    obtain ⟨u, hu⟩ := list_card_one_eq hlen (hnot_fc w hw_not)
    have huV := (Finset.mem_erase.1 (hch_sub w hw u (by rw [hu]; simp))).2
    exact ⟨u, hu, huV⟩
  · intro w hw hN hnot
    have hw_pos : w ∈ V_pos := Finset.mem_filter.2 ⟨hw, hN, hnot⟩
    have hlen : (effCh N C w).length ≤ 2 := by
      rw [effCh_eq_effInputs N C hRB hN (hV_lt w hw)]; exact (effInputs_len_pos hfan hN (hV_lt w hw) hnot).2
    obtain ⟨u1, u2, hu, hne⟩ := list_card_two_eq hlen (hpos_fc w hw_pos)
    have hu1V := (Finset.mem_erase.1 (hch_sub w hw u1 (by rw [hu]; simp))).2
    have hu2V := (Finset.mem_erase.1 (hch_sub w hw u2 (by rw [hu]; simp))).2
    exact ⟨u1, u2, hu, hne, hu1V, hu2V⟩

lemma V_disjoint_children (n : ℕ) (C : Circuit) (out0 : ℕ) (vp : VProps n C out0)
    {w u1 u2 : ℕ} (hw : w ∈ reach (n + 2) C out0) (hch : effCh (n + 2) C w = [u1, u2]) (hne : u1 ≠ u2) :
    Disjoint (reach (n + 2) C u1) (reach (n + 2) C u2) := by
  classical
  let N := n + 2
  let V := reach N C out0
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb heq
  subst heq
  let S := reach N C u1 ∩ reach N C u2
  have hSne : S.Nonempty := ⟨a, Finset.mem_inter.2 ⟨ha, hb⟩⟩
  let m := S.max' hSne
  have hmS : m ∈ S := Finset.max'_mem S hSne
  have hm1 : m ∈ reach N C u1 := (Finset.mem_inter.1 hmS).1
  have hm2 : m ∈ reach N C u2 := (Finset.mem_inter.1 hmS).2
  have hu1_lt : u1 < w := effCh_lt N C w u1 (by rw [hch]; simp)
  have hu2_lt : u2 < w := effCh_lt N C w u2 (by rw [hch]; simp)
  have hm_lt : m < w := lt_of_le_of_lt (mem_reach_le N C u1 m hm1) hu1_lt
  have hw_le : w ≤ out0 := mem_reach_le N C out0 w hw
  have hm_erase : m ∈ V.erase out0 := Finset.mem_erase.2 ⟨by omega,
    reach_trans N C out0 w hw (reach_trans N C w u1
      (by rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u1, by rw [hch]; simp, self_mem_reach N C u1⟩)) hm1)⟩
  have hdeg1 : ((reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z)).card = 1 :=
    vp.hdeg m hm_erase
  by_cases hm_u1 : m = u1
  · have hm_ne_u2 : m ≠ u2 := hm_u1 ▸ hne
    obtain ⟨p2, hp2_reach, hp2_ch⟩ := mem_reach_parent N C u2 m hm2 hm_ne_u2
    have hp2_le : p2 ≤ u2 := mem_reach_le N C u2 p2 hp2_reach
    have hp2V : p2 ∈ V := reach_trans N C out0 w hw (reach_trans N C w u2
      (by rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u2, by rw [hch]; simp, self_mem_reach N C u2⟩)) hp2_reach)
    have hw_mem : w ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
      Finset.mem_filter.2 ⟨hw, by rw [hch, hm_u1]; simp⟩
    have hp2_mem : p2 ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
      Finset.mem_filter.2 ⟨hp2V, hp2_ch⟩
    have hcard : 2 ≤ ((reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z)).card :=
      Finset.one_lt_card.2 ⟨w, hw_mem, p2, hp2_mem, by omega⟩
    omega
  · by_cases hm_u2 : m = u2
    · obtain ⟨p1, hp1_reach, hp1_ch⟩ := mem_reach_parent N C u1 m hm1 hm_u1
      have hp1_le : p1 ≤ u1 := mem_reach_le N C u1 p1 hp1_reach
      have hp1V : p1 ∈ V := reach_trans N C out0 w hw (reach_trans N C w u1
        (by rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u1, by rw [hch]; simp, self_mem_reach N C u1⟩)) hp1_reach)
      have hw_mem : w ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
        Finset.mem_filter.2 ⟨hw, by rw [hch, hm_u2]; simp⟩
      have hp1_mem : p1 ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
        Finset.mem_filter.2 ⟨hp1V, hp1_ch⟩
      have hcard : 2 ≤ ((reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z)).card :=
        Finset.one_lt_card.2 ⟨w, hw_mem, p1, hp1_mem, by omega⟩
      omega
    · obtain ⟨p1, hp1_reach, hp1_ch⟩ := mem_reach_parent N C u1 m hm1 hm_u1
      obtain ⟨p2, hp2_reach, hp2_ch⟩ := mem_reach_parent N C u2 m hm2 hm_u2
      have hp1V : p1 ∈ V := reach_trans N C out0 w hw (reach_trans N C w u1
        (by rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u1, by rw [hch]; simp, self_mem_reach N C u1⟩)) hp1_reach)
      have hp2V : p2 ∈ V := reach_trans N C out0 w hw (reach_trans N C w u2
        (by rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u2, by rw [hch]; simp, self_mem_reach N C u2⟩)) hp2_reach)
      have hp1_mem : p1 ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
        Finset.mem_filter.2 ⟨hp1V, hp1_ch⟩
      have hp2_mem : p2 ∈ (reach (n + 2) C out0).filter (fun z => m ∈ effCh (n + 2) C z) :=
        Finset.mem_filter.2 ⟨hp2V, hp2_ch⟩
      have hp_eq : p1 = p2 := by
        by_contra hne_p
        have hcard := Finset.one_lt_card.2 ⟨p1, hp1_mem, p2, hp2_mem, hne_p⟩
        omega
      have hp1S : p1 ∈ S := Finset.mem_inter.2 ⟨hp1_reach, hp_eq ▸ hp2_reach⟩
      have hle_max := Finset.le_max' S p1 hp1S
      have hmlt := effCh_lt N C p1 m hp1_ch
      omega

lemma V_leaves_nonempty (n : ℕ) (C : Circuit) (out0 : ℕ) (vp : VProps n C out0) :
    ∀ w ∈ reach (n + 2) C out0, (leaves n C w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [leaves_of_lt_n n C hwn]; exact ⟨⟨w, hwn⟩, Finset.mem_singleton_self _⟩
    · have hnot_const : ¬(n ≤ w ∧ w < n + 2) := fun hc => by
        have hm : w ∈ (reach (n + 2) C out0).filter (fun z => n ≤ z ∧ z < n + 2) := Finset.mem_filter.2 ⟨hw, hc⟩
        rw [vp.hV_const] at hm; simp at hm
      have hN : n + 2 ≤ w := by omega
      by_cases hnot : (gateAt C (w - (n + 2))).op = GateOp.not
      · obtain ⟨u, hu_ch, huV⟩ := vp.hnot_ch w hw hN hnot
        have hu_lt : u < w := effCh_lt (n + 2) C w u (by rw [hu_ch]; simp)
        obtain ⟨i, hi⟩ := ih u hu_lt huV
        have hu_mem : u ∈ reach (n + 2) C w := by
          rw [reach_eq]; exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.2 ⟨u, by rw [hu_ch]; simp, self_mem_reach (n + 2) C u⟩)
        exact ⟨i, leaves_mono n C hu_mem hi⟩
      · obtain ⟨u1, u2, hu_ch, _, hu1V, _⟩ := vp.hpos_ch w hw hN hnot
        have hu_lt : u1 < w := effCh_lt (n + 2) C w u1 (by rw [hu_ch]; simp)
        obtain ⟨i, hi⟩ := ih u1 hu_lt hu1V
        have hu_mem : u1 ∈ reach (n + 2) C w := by
          rw [reach_eq]; exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.2 ⟨u1, by rw [hu_ch]; simp, self_mem_reach (n + 2) C u1⟩)
        exact ⟨i, leaves_mono n C hu_mem hi⟩

lemma V_no_toggle_up (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0) (i : Fin n) :
    ∀ r ∈ reach (n + 2) C out0, ∀ w ∈ reach (n + 2) C r,
    i ∈ leaves n C w →
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]) w =
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]) w →
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]) r =
    wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]) r := by
  let x1 := List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]
  let x2 := List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr w hw hi_w hweq
    by_cases hwr : w = r
    · subst hwr; exact hweq
    · have hr_lt : r < n + 2 + C.size := lt_of_le_of_lt (mem_reach_le (n + 2) C out0 r hr) vp.hout0
      have hr_not_n : ¬ r < n := fun hrn => by
        rw [reach_eq] at hw
        have hemp : effCh (n + 2) C r = [] := by unfold effCh; simp [show r < n + 2 by omega]
        simp [hemp] at hw
        exact hwr hw
      have hnot_const : ¬(n ≤ r ∧ r < n + 2) := fun hc => by
        have hm : r ∈ (reach (n + 2) C out0).filter (fun z => n ≤ z ∧ z < n + 2) := Finset.mem_filter.2 ⟨hr, hc⟩
        rw [vp.hV_const] at hm; simp at hm
      have hN : n + 2 ≤ r := by omega
      rw [reach_eq] at hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact absurd rfl hwr
      · simp only [Finset.mem_biUnion, List.mem_toFinset] at hw'
        obtain ⟨u, hu_ch, hwu⟩ := hw'
        by_cases hnot : (gateAt C (r - (n + 2))).op = GateOp.not
        · obtain ⟨u0, hu0, hu0V⟩ := vp.hnot_ch r hr hN hnot
          have hu_eq : u = u0 := by rw [hu0] at hu_ch; simp at hu_ch; exact hu_ch
          rw [hu_eq] at hwu
          have hu0_lt : u0 < r := effCh_lt (n + 2) C r u0 (by rw [hu0]; simp)
          have ihu := ih u0 hu0_lt hu0V w hwu hi_w hweq
          rw [wireVal_gate (n + 2) C hRB x1 (actual_len n i.castSucc) hN hr_lt,
              wireVal_gate (n + 2) C hRB x2 (actual_len n i.succ) hN hr_lt,
              value_eff, value_eff]
          have heff : effInputs (gateAt C (r - (n + 2))) = [u0] := by
            rw [← effCh_eq_effInputs (n + 2) C hRB hN hr_lt]; exact hu0
          rw [heff]
          simp [hnot, GateOp.eval]
          exact ihu
        · obtain ⟨u1, u2, hu12, hne, hu1V, hu2V⟩ := vp.hpos_ch r hr hN hnot
          have hdisj := V_disjoint_children n C out0 vp hr hu12 hne
          have hdisj_l : Disjoint (leaves n C u1) (leaves n C u2) := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            rw [mem_leaves] at hk1 hk2
            exact Finset.disjoint_left.1 hdisj hk1 hk2
          have hu1_lt : u1 < r := effCh_lt (n + 2) C r u1 (by rw [hu12]; simp)
          have hu2_lt : u2 < r := effCh_lt (n + 2) C r u2 (by rw [hu12]; simp)
          have heff : effInputs (gateAt C (r - (n + 2))) = [u1, u2] := by
            rw [← effCh_eq_effInputs (n + 2) C hRB hN hr_lt]; exact hu12
          have heq12 : wireVal C x1 u1 = wireVal C x2 u1 ∧ wireVal C x1 u2 = wireVal C x2 u2 := by
            rw [hu12] at hu_ch; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_ch
            rcases hu_ch with h_u1 | h_u2
            · rw [h_u1] at hwu
              have hi_u1 : i ∈ leaves n C u1 := leaves_mono n C hwu hi_w
              have hi_nu2 : i ∉ leaves n C u2 := fun hi2 => Finset.disjoint_left.1 hdisj_l hi_u1 hi2
              refine ⟨ih u1 hu1_lt hu1V w hwu hi_w hweq,
                wireVal_eq_of_not_mem_leaves n C hRB (lt_trans hu2_lt hr_lt) hi_nu2⟩
            · rw [h_u2] at hwu
              have hi_u2 : i ∈ leaves n C u2 := leaves_mono n C hwu hi_w
              have hi_nu1 : i ∉ leaves n C u1 := fun hi1 => Finset.disjoint_left.1 hdisj_l hi1 hi_u2
              refine ⟨wireVal_eq_of_not_mem_leaves n C hRB (lt_trans hu1_lt hr_lt) hi_nu1,
                ih u2 hu2_lt hu2V w hwu hi_w hweq⟩
          rw [wireVal_gate (n + 2) C hRB x1 (actual_len n i.castSucc) hN hr_lt,
              wireVal_gate (n + 2) C hRB x2 (actual_len n i.succ) hN hr_lt,
              value_eff, value_eff, heff]
          simp [heq12.1, heq12.2]

lemma V_toggles_iff (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0)
    (hW0 : ∀ i : Fin n,
      wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]) out0 ≠
      wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]) out0)
    {w : ℕ} (hw : w ∈ reach (n + 2) C out0) (i : Fin n) :
    (wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.castSucc.val)) ++ [false, true]) w ≠
     wireVal C (List.ofFn (fun k : Fin n => decide (k.val < i.succ.val)) ++ [false, true]) w) ↔
    i ∈ leaves n C w := by
  constructor
  · intro hne
    by_contra hni
    exact hne (wireVal_eq_of_not_mem_leaves n C hRB (lt_of_le_of_lt (mem_reach_le (n + 2) C out0 w hw) vp.hout0) hni)
  · intro hi heq
    exact hW0 i (V_no_toggle_up n C hRB out0 vp i out0 (self_mem_reach (n + 2) C out0) w hw hi heq)

lemma V_falls_le_notCount (n : ℕ) (C : Circuit) (hfan : FanInTwo C) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0) :
    ∀ w ∈ reach (n + 2) C out0,
    fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w) ≤
      ((reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not)).card := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hf0 : fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w) = 0 := by
        unfold fallsOf
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        dsimp only
        rw [wireVal_lt_N (n + 2) C hRB _ (actual_len n i.castSucc) (by omega),
            wireVal_lt_N (n + 2) C hRB _ (actual_len n i.succ) (by omega),
            getD_append_left' _ _ _ _ (by simp [hwn]),
            getD_append_left' _ _ _ _ (by simp [hwn])]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hwn, ↓reduceDIte, Option.getD_some]
        have hc : (i.castSucc : ℕ) = i.val := rfl
        have hs : (i.succ : ℕ) = i.val + 1 := rfl
        rw [hc, hs]
        intro ⟨h1, h2⟩
        simp at h1 h2
        omega
      omega
    · have hnot_const : ¬(n ≤ w ∧ w < n + 2) := fun hc => by
        have hm : w ∈ (reach (n + 2) C out0).filter (fun z => n ≤ z ∧ z < n + 2) := Finset.mem_filter.2 ⟨hw, hc⟩
        rw [vp.hV_const] at hm; simp at hm
      have hN : n + 2 ≤ w := by omega
      have hw_lt : w < n + 2 + C.size := lt_of_le_of_lt (mem_reach_le (n + 2) C out0 w hw) vp.hout0
      by_cases hnot : (gateAt C (w - (n + 2))).op = GateOp.not
      · obtain ⟨u, hu, huV⟩ := vp.hnot_ch w hw hN hnot
        have hu_lt : u < w := effCh_lt (n + 2) C w u (by rw [hu]; simp)
        have ihu := ih u hu_lt huV
        have heval : ∀ l : Fin (n + 1),
            wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w =
            !(wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u) := by
          intro l
          rw [wireVal_gate (n + 2) C hRB _ (actual_len n l) hN hw_lt, value_eff]
          have heff : effInputs (gateAt C (w - (n + 2))) = [u] := by
            rw [← effCh_eq_effInputs (n + 2) C hRB hN hw_lt]; exact hu
          rw [heff, hnot]
          simp [GateOp.eval]
        simp_rw [heval]
        rw [fallsOf_not]
        have hsub := rises_sub_falls n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u)
        have hr_le : risesOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u) ≤
            fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u) + 1 := by
          split_ifs at hsub <;> omega
        have hrw : reach (n + 2) C w = insert w (reach (n + 2) C u) := by
          rw [reach_eq, hu]; simp
        have hreach_eq : (reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not) =
            insert w ((reach (n + 2) C u).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not)) := by
          ext z
          simp only [hrw, Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hzu, hz1, hz2⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hzu, hz1, hz2⟩
          · rintro (rfl | ⟨hzu, hz1, hz2⟩)
            · exact ⟨Or.inl rfl, hN, hnot⟩
            · exact ⟨Or.inr hzu, hz1, hz2⟩
        have hw_notin : w ∉ (reach (n + 2) C u).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not) := by
          intro hm
          have hle := mem_reach_le (n + 2) C u w (Finset.mem_filter.1 hm).1
          omega
        rw [hreach_eq, Finset.card_insert_of_notMem hw_notin]
        omega
      · obtain ⟨u1, u2, hu12, hne, hu1V, hu2V⟩ := vp.hpos_ch w hw hN hnot
        have hu1_lt : u1 < w := effCh_lt (n + 2) C w u1 (by rw [hu12]; simp)
        have hu2_lt : u2 < w := effCh_lt (n + 2) C w u2 (by rw [hu12]; simp)
        have ih1 := ih u1 hu1_lt hu1V
        have ih2 := ih u2 hu2_lt hu2V
        have hdisj := V_disjoint_children n C out0 vp hw hu12 hne
        have heff : effInputs (gateAt C (w - (n + 2))) = [u1, u2] := by
          rw [← effCh_eq_effInputs (n + 2) C hRB hN hw_lt]; exact hu12
        have hop := (effInputs_len_pos hfan hN hw_lt hnot).1
        have hfalls_le : fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w) ≤
            fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u1) +
            fallsOf n (fun l => wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u2) := by
          rcases hop with hand | hor
          · have heval : ∀ l : Fin (n + 1),
                wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w =
                (wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u1 &&
                 wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u2) := by
              intro l
              rw [wireVal_gate (n + 2) C hRB _ (actual_len n l) hN hw_lt, value_eff, heff, hand]
              simp [GateOp.eval]
            simp_rw [heval]
            exact fallsOf_and _ _ _
          · have heval : ∀ l : Fin (n + 1),
                wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) w =
                (wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u1 ||
                 wireVal C (List.ofFn (fun k : Fin n => decide (k.val < l.val)) ++ [false, true]) u2) := by
              intro l
              rw [wireVal_gate (n + 2) C hRB _ (actual_len n l) hN hw_lt, value_eff, heff, hor]
              simp [GateOp.eval]
            simp_rw [heval]
            exact fallsOf_or _ _ _
        have hrw : reach (n + 2) C w = insert w (reach (n + 2) C u1 ∪ reach (n + 2) C u2) := by
          rw [reach_eq, hu12]; simp
        have hreach_eq : (reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not) =
            (reach (n + 2) C u1).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not) ∪
            (reach (n + 2) C u2).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not) := by
          ext z
          simp only [hrw, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
          constructor
          · rintro ⟨rfl | hzu1 | hzu2, hz1, hz2⟩
            · exact absurd hz2 hnot
            · exact Or.inl ⟨hzu1, hz1, hz2⟩
            · exact Or.inr ⟨hzu2, hz1, hz2⟩
          · rintro (⟨hzu1, hz1, hz2⟩ | ⟨hzu2, hz1, hz2⟩)
            · exact ⟨Or.inr (Or.inl hzu1), hz1, hz2⟩
            · exact ⟨Or.inr (Or.inr hzu2), hz1, hz2⟩
        have hdisj_f : Disjoint ((reach (n + 2) C u1).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not))
            ((reach (n + 2) C u2).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op = GateOp.not)) :=
          Finset.disjoint_filter_filter hdisj
        rw [hreach_eq, Finset.card_union_of_disjoint hdisj_f]
        omega

lemma V_pos_card_eq_leaves (n : ℕ) (C : Circuit) (out0 : ℕ) (vp : VProps n C out0) :
    ∀ w ∈ reach (n + 2) C out0,
    ((reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not)).card + 1 =
      (leaves n C w).card := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [leaves_of_lt_n n C hwn, Finset.card_singleton]
      have hemp : (reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz
        have := mem_reach_le (n + 2) C w z hz
        omega
      rw [hemp, Finset.card_empty]
    · have hnot_const : ¬(n ≤ w ∧ w < n + 2) := fun hc => by
        have hm : w ∈ (reach (n + 2) C out0).filter (fun z => n ≤ z ∧ z < n + 2) := Finset.mem_filter.2 ⟨hw, hc⟩
        rw [vp.hV_const] at hm; simp at hm
      have hN : n + 2 ≤ w := by omega
      by_cases hnot : (gateAt C (w - (n + 2))).op = GateOp.not
      · obtain ⟨u, hu, huV⟩ := vp.hnot_ch w hw hN hnot
        have hu_lt : u < w := effCh_lt (n + 2) C w u (by rw [hu]; simp)
        have ihu := ih u hu_lt huV
        have hrw : reach (n + 2) C w = insert w (reach (n + 2) C u) := by
          rw [reach_eq, hu]; simp
        have hreq : (reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) =
            (reach (n + 2) C u).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) := by
          ext z
          simp only [hrw, Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hzu, hz1, hz2⟩
            · exact absurd hnot hz2
            · exact ⟨hzu, hz1, hz2⟩
          · rintro ⟨hzu, hz1, hz2⟩
            exact ⟨Or.inr hzu, hz1, hz2⟩
        have hleq : leaves n C w = leaves n C u := by
          rw [leaves_of_ge n C hN, hu]
          simp
        rw [hreq, hleq]
        exact ihu
      · obtain ⟨u1, u2, hu12, hne, hu1V, hu2V⟩ := vp.hpos_ch w hw hN hnot
        have hu1_lt : u1 < w := effCh_lt (n + 2) C w u1 (by rw [hu12]; simp)
        have hu2_lt : u2 < w := effCh_lt (n + 2) C w u2 (by rw [hu12]; simp)
        have ih1 := ih u1 hu1_lt hu1V
        have ih2 := ih u2 hu2_lt hu2V
        have hdisj := V_disjoint_children n C out0 vp hw hu12 hne
        have hrw : reach (n + 2) C w = insert w (reach (n + 2) C u1 ∪ reach (n + 2) C u2) := by
          rw [reach_eq, hu12]; simp
        have hreq : (reach (n + 2) C w).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) =
            insert w ((reach (n + 2) C u1).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) ∪
            (reach (n + 2) C u2).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not)) := by
          ext z
          simp only [hrw, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
          constructor
          · rintro ⟨rfl | hzu1 | hzu2, hz1, hz2⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨hzu1, hz1, hz2⟩)
            · exact Or.inr (Or.inr ⟨hzu2, hz1, hz2⟩)
          · rintro (rfl | ⟨hzu1, hz1, hz2⟩ | ⟨hzu2, hz1, hz2⟩)
            · exact ⟨Or.inl rfl, hN, hnot⟩
            · exact ⟨Or.inr (Or.inl hzu1), hz1, hz2⟩
            · exact ⟨Or.inr (Or.inr hzu2), hz1, hz2⟩
        have hw_notin : w ∉ (reach (n + 2) C u1).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) ∪
            (reach (n + 2) C u2).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not) := by
          simp only [Finset.mem_union, Finset.mem_filter]
          rintro (⟨h1, _⟩ | ⟨h2, _⟩)
          · have := mem_reach_le (n + 2) C u1 w h1; omega
          · have := mem_reach_le (n + 2) C u2 w h2; omega
        have hdisj_f : Disjoint ((reach (n + 2) C u1).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not))
            ((reach (n + 2) C u2).filter (fun z => n + 2 ≤ z ∧ (gateAt C (z - (n + 2))).op ≠ GateOp.not)) :=
          Finset.disjoint_filter_filter hdisj
        have hleq : leaves n C w = leaves n C u1 ∪ leaves n C u2 := by
          rw [leaves_of_ge n C hN, hu12]
          simp
        have hdisj_l : Disjoint (leaves n C u1) (leaves n C u2) := by
          rw [Finset.disjoint_left]; intro k hk1 hk2
          rw [mem_leaves] at hk1 hk2
          exact Finset.disjoint_left.1 hdisj hk1 hk2
        rw [hreq, Finset.card_insert_of_notMem hw_notin, Finset.card_union_of_disjoint hdisj_f,
          hleq, Finset.card_union_of_disjoint hdisj_l]
        omega

def chainOut (N : ℕ) (C : Circuit) (V : Finset ℕ) (w : ℕ) : Finset ℕ :=
  if w ∈ V ∨ w < N then ∅
  else match effCh N C w with
    | [u] => if hu : u < w then insert w (chainOut N C V u) else {w}
    | _ => {w}
termination_by w
decreasing_by exact hu

def rootInV (N : ℕ) (C : Circuit) (V : Finset ℕ) (w : ℕ) : Option ℕ :=
  if w ∈ V then some w
  else if w < N then none
  else match effCh N C w with
    | [u] => if hu : u < w then rootInV N C V u else none
    | _ => none
termination_by w
decreasing_by exact hu

lemma chainOut_props (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0) :
    let N := n + 2
    let V := reach N C out0
    ∀ w < N + C.size,
      (∀ z ∈ chainOut N C V w, z ∉ V ∧ N ≤ z ∧ z ≤ w ∧ (gateAt C (z - N)).op = GateOp.not ∧
        rootInV N C V z = rootInV N C V w) ∧
      (∀ r, rootInV N C V w = some r → r ∈ V ∧ r ≤ w ∧
        (∀ x : List Bool, x.length = N →
          wireVal C x w = xor (wireVal C x r) (decide ((chainOut N C V w).card % 2 = 1))) ∧
        (∀ z ∈ reach N C w ∩ V, z ∈ reach N C r)) ∧
      (rootInV N C V w = none →
        (∀ z ∈ reach N C w, z ∉ V) ∧
        (∀ x y : List Bool, x.length = N → y.length = N →
          x.getD n false = y.getD n false → x.getD (n + 1) false = y.getD (n + 1) false →
          wireVal C x w = wireVal C y w)) := by
  intro N V w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwV : w ∈ V
    · have hc : chainOut N C V w = ∅ := by rw [chainOut]; simp [hwV]
      have hr : rootInV N C V w = some w := by rw [rootInV]; simp [hwV]
      rw [hc, hr]
      refine ⟨fun z hz => by simp at hz, fun r hr_eq => ?_, fun hnone => by simp at hnone⟩
      cases hr_eq
      exact ⟨hwV, le_rfl, fun _ _ => by simp, fun z hz => (Finset.mem_inter.1 hz).1⟩
    · by_cases hwN : w < N
      · have hc : chainOut N C V w = ∅ := by rw [chainOut]; simp [hwN]
        have hr : rootInV N C V w = none := by rw [rootInV]; simp [hwV, hwN]
        rw [hc, hr]
        refine ⟨fun z hz => by simp at hz, fun r hr_eq => by simp at hr_eq, fun _ => ⟨?_, ?_⟩⟩
        · intro z hz
          rw [reach_eq] at hz
          have hemp : effCh N C w = [] := by unfold effCh; simp [hwN]
          simp only [hemp, List.toFinset_nil, Finset.biUnion_empty, Finset.mem_insert,
            Finset.notMem_empty, or_false] at hz
          subst hz; exact hwV
        · intro x y hx hy hxn hyn
          have hwn : ¬ w < n := fun hlt => hwV (by
            have : w ∈ V.filter (· < n) := by rw [vp.hV_in]; exact Finset.mem_range.2 hlt
            exact (Finset.mem_filter.1 this).1)
          rw [wireVal_lt_N N C hRB x hx hwN, wireVal_lt_N N C hRB y hy hwN]
          have hcases : w = n ∨ w = n + 1 := by omega
          rcases hcases with rfl | rfl <;> assumption
      · have hNw : N ≤ w := by omega
        have hw_not : (gateAt C (w - N)).op = GateOp.not := by
          by_contra hpos
          have hmem : w ∈ ((Finset.range C.size).image (· + N)).filter (fun z => (gateAt C (z - N)).op ≠ GateOp.not) := by
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
            exact ⟨⟨w - N, by omega, by omega⟩, hpos⟩
          rw [← vp.hV_pos_all] at hmem
          exact hwV (Finset.mem_filter.1 hmem).1
        have hlen : (effCh N C w).length ≤ 1 := by
          rw [effCh_eq_effInputs N C hRB hNw hw]
          exact effInputs_len_not hw_not
        match hch : effCh N C w with
        | [] =>
          have hc : chainOut N C V w = {w} := by rw [chainOut]; simp [hwV, hwN, hch]
          have hr : rootInV N C V w = none := by rw [rootInV]; simp [hwV, hwN, hch]
          rw [hc, hr]
          refine ⟨fun z hz => ?_, fun r hr_eq => by simp at hr_eq, fun _ => ⟨?_, ?_⟩⟩
          · rw [Finset.mem_singleton] at hz; rw [hz]
            exact ⟨hwV, hNw, le_rfl, hw_not, hr⟩
          · intro z hz
            rw [reach_eq, hch] at hz
            simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.mem_insert,
              Finset.notMem_empty, or_false] at hz
            subst hz; exact hwV
          · intro x y hx hy _ _
            rw [wireVal_gate N C hRB x hx hNw hw, wireVal_gate N C hRB y hy hNw hw, value_eff, value_eff]
            have heff : effInputs (gateAt C (w - N)) = [] := by
              rw [← effCh_eq_effInputs N C hRB hNw hw]; exact hch
            rw [heff]; rfl
        | [u] =>
          have hu_lt : u < w := effCh_lt N C w u (by rw [hch]; simp)
          have ihu := ih u hu_lt (by omega)
          have hc : chainOut N C V w = insert w (chainOut N C V u) := by
            conv_lhs => rw [chainOut]
            simp [hwV, hwN, hch, hu_lt]
          have hr : rootInV N C V w = rootInV N C V u := by
            conv_lhs => rw [rootInV]
            simp [hwV, hwN, hch, hu_lt]
          have hw_notin_u : w ∉ chainOut N C V u := fun hm => by
            have := (ihu.1 w hm).2.2.1; omega
          have hreach_w : reach N C w = insert w (reach N C u) := by
            rw [reach_eq, hch]; simp
          refine ⟨fun z hz => ?_, fun r hr_eq => ?_, fun hnone => ?_⟩
          · rw [hc, Finset.mem_insert] at hz
            rcases hz with rfl | hzu
            · exact ⟨hwV, hNw, le_rfl, hw_not, rfl⟩
            · obtain ⟨h1, h2, h3, h4, h5⟩ := ihu.1 z hzu
              exact ⟨h1, h2, le_trans h3 (Nat.le_of_lt hu_lt), h4, h5.trans hr.symm⟩
          · rw [hr] at hr_eq
            obtain ⟨hrV, hru, hev_u, hsub_u⟩ := ihu.2.1 r hr_eq
            refine ⟨hrV, le_trans hru (Nat.le_of_lt hu_lt), fun x hx => ?_, fun z hz => ?_⟩
            · rw [wireVal_gate N C hRB x hx hNw hw, value_eff]
              have heff : effInputs (gateAt C (w - N)) = [u] := by
                rw [← effCh_eq_effInputs N C hRB hNw hw]; exact hch
              rw [heff, hw_not, GateOp.eval]
              simp only [List.map_cons, List.map_nil, List.headD_cons]
              rw [hev_u x hx, hc, Finset.card_insert_of_notMem hw_notin_u]
              rcases Nat.mod_two_eq_zero_or_one (chainOut N C V u).card with hm | hm
              · have hm1 : ((chainOut N C V u).card + 1) % 2 = 1 := by omega
                cases wireVal C x r <;> simp [hm, hm1]
              · have hm1 : ((chainOut N C V u).card + 1) % 2 = 0 := by omega
                cases wireVal C x r <;> simp [hm, hm1]
            · simp only [hreach_w, Finset.mem_inter, Finset.mem_insert] at hz
              rcases hz with ⟨rfl | hzu, hzV⟩
              · exact absurd hzV hwV
              · exact hsub_u z (Finset.mem_inter.2 ⟨hzu, hzV⟩)
          · rw [hr] at hnone
            obtain ⟨hnone1, hnone2⟩ := ihu.2.2 hnone
            refine ⟨fun z hz => ?_, fun x y hx hy hxn hyn => ?_⟩
            · rw [hreach_w, Finset.mem_insert] at hz
              rcases hz with rfl | hzu
              · exact hwV
              · exact hnone1 z hzu
            · rw [wireVal_gate N C hRB x hx hNw hw, wireVal_gate N C hRB y hy hNw hw, value_eff, value_eff]
              have heff : effInputs (gateAt C (w - N)) = [u] := by
                rw [← effCh_eq_effInputs N C hRB hNw hw]; exact hch
              rw [heff]; simp [hnone2 x y hx hy hxn hyn]
        | _ :: _ :: _ => rw [hch] at hlen; simp at hlen

lemma rootInV_of_mem_reach_not_mem (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0) :
    let N := n + 2
    let V := reach N C out0
    ∀ r < N + C.size, ∀ w ∈ reach N C r, w ∉ V → rootInV N C V r = rootInV N C V w := by
  intro N V r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr w hw hwV
    by_cases hrV : r ∈ V
    · exfalso; exact hwV (reach_trans N C out0 r hrV hw)
    · by_cases hwr : w = r
      · subst hwr; rfl
      · by_cases hrN : r < N
        · exfalso
          rw [reach_eq] at hw
          have hemp : effCh N C r = [] := by unfold effCh; simp [hrN]
          simp [hemp] at hw
          exact hwr hw
        · have hNr : N ≤ r := by omega
          have hr_not : (gateAt C (r - N)).op = GateOp.not := by
            by_contra hpos
            have hmem : r ∈ ((Finset.range C.size).image (· + N)).filter (fun z => (gateAt C (z - N)).op ≠ GateOp.not) := by
              simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
              exact ⟨⟨r - N, by omega, by omega⟩, hpos⟩
            rw [← vp.hV_pos_all] at hmem
            exact hrV (Finset.mem_filter.1 hmem).1
          have hlen : (effCh N C r).length ≤ 1 := by
            rw [effCh_eq_effInputs N C hRB hNr hr]
            exact effInputs_len_not hr_not
          match hch : effCh N C r with
          | [] =>
            exfalso
            rw [reach_eq, hch] at hw
            simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.mem_insert,
              Finset.notMem_empty, or_false] at hw
            exact hwr hw
          | [u] =>
            have hu_lt : u < r := effCh_lt N C r u (by rw [hch]; simp)
            have hw_u : w ∈ reach N C u := by
              rw [reach_eq, hch] at hw
              simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
                Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left, Finset.mem_insert] at hw
              rcases hw with rfl | hwu
              · exact absurd rfl hwr
              · exact hwu
            have hroot_r : rootInV N C V r = rootInV N C V u := by
              conv_lhs => rw [rootInV]
              simp [hrV, hrN, hch, hu_lt]
            rw [hroot_r]
            exact ih u hu_lt (by omega) w hw_u hwV
          | _ :: _ :: _ => rw [hch] at hlen; simp at hlen

def descendV (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if N ≤ w ∧ (gateAt C (w - N)).op = GateOp.not then
    match effCh N C w with
    | [u] => if hu : u < w then descendV N C u else w
    | _ => w
  else w
termination_by w
decreasing_by exact hu

def chainInV (N : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if N ≤ w ∧ (gateAt C (w - N)).op = GateOp.not then
    match effCh N C w with
    | [u] => if hu : u < w then insert w (chainInV N C u) else {w}
    | _ => {w}
  else ∅
termination_by w
decreasing_by exact hu

lemma chainInV_props (n : ℕ) (C : Circuit) (hRB : ReadsBack (n + 2) C)
    (out0 : ℕ) (vp : VProps n C out0) :
    let N := n + 2
    let V := reach N C out0
    ∀ w ∈ V,
      let b := descendV N C w
      b ∈ V ∧ ¬(N ≤ b ∧ (gateAt C (b - N)).op = GateOp.not) ∧ b ≤ w ∧
      leaves n C b = leaves n C w ∧
      reach N C w = reach N C b ∪ chainInV N C w ∧
      (∀ z ∈ chainInV N C w, z ∈ V ∧ N ≤ z ∧ (gateAt C (z - N)).op = GateOp.not ∧
        b < z ∧ z ≤ w ∧ leaves n C z = leaves n C w ∧ descendV N C z = b) ∧
      (∀ x : List Bool, x.length = N →
        wireVal C x w = xor (wireVal C x b) (decide ((chainInV N C w).card % 2 = 1))) := by
  intro N V w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hnot : N ≤ w ∧ (gateAt C (w - N)).op = GateOp.not
    · obtain ⟨u, hu, huV⟩ := vp.hnot_ch w hw hnot.1 hnot.2
      have hu_lt : u < w := effCh_lt N C w u (by rw [hu]; simp)
      have ihu := ih u hu_lt huV
      have hd : descendV N C w = descendV N C u := by
        conv_lhs => rw [descendV]; rw [if_pos hnot, hu]; simp [hu_lt]
      have hc : chainInV N C w = insert w (chainInV N C u) := by
        conv_lhs => rw [chainInV]; rw [if_pos hnot, hu]; simp [hu_lt]
      have hw_notin : w ∉ chainInV N C u := fun hm => by
        have := (ihu.2.2.2.2.2.1 w hm).2.2.2.2.1; omega
      have hw_notin_b : w ∉ reach N C (descendV N C u) := fun hm => by
        have h1 := mem_reach_le N C (descendV N C u) w hm
        have h2 := ihu.2.2.1
        omega
      have hl_eq : leaves n C w = leaves n C u := by
        rw [leaves_of_ge n C hnot.1, hu]; simp
      have hrw : reach N C w = insert w (reach N C u) := by
        rw [reach_eq, hu]; simp
      have hw_lt : w < N + C.size := lt_of_le_of_lt (mem_reach_le N C out0 w hw) vp.hout0
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hd]; exact ihu.1
      · rw [hd]; exact ihu.2.1
      · rw [hd]; exact le_trans ihu.2.2.1 (Nat.le_of_lt hu_lt)
      · rw [hd, hl_eq]; exact ihu.2.2.2.1
      · rw [hd, hc, hrw, ihu.2.2.2.2.1, ← Finset.union_insert]
      · intro z hz
        rw [hc, Finset.mem_insert] at hz
        rcases hz with rfl | hzu
        · refine ⟨hw, hnot.1, hnot.2, ?_, le_rfl, rfl, rfl⟩
          rw [hd]
          exact lt_of_le_of_lt ihu.2.2.1 hu_lt
        · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ihu.2.2.2.2.2.1 z hzu
          exact ⟨h1, h2, h3, hd ▸ h4, le_trans h5 (Nat.le_of_lt hu_lt), hl_eq ▸ h6, h7.trans hd.symm⟩
      · intro x hx
        rw [wireVal_gate N C hRB x hx hnot.1 hw_lt, value_eff]
        have heff : effInputs (gateAt C (w - N)) = [u] := by
          rw [← effCh_eq_effInputs N C hRB hnot.1 hw_lt]; exact hu
        rw [heff, hnot.2, GateOp.eval]
        simp only [List.map_cons, List.map_nil, List.headD_cons]
        rw [ihu.2.2.2.2.2.2 x hx, hd, hc, Finset.card_insert_of_notMem hw_notin]
        rcases Nat.mod_two_eq_zero_or_one (chainInV N C u).card with hm | hm
        · have hm1 : ((chainInV N C u).card + 1) % 2 = 1 := by omega
          cases wireVal C x (descendV N C u) <;> simp [hm, hm1]
        · have hm1 : ((chainInV N C u).card + 1) % 2 = 0 := by omega
          cases wireVal C x (descendV N C u) <;> simp [hm, hm1]
    · have hd : descendV N C w = w := by rw [descendV]; simp [hnot]
      have hc : chainInV N C w = ∅ := by rw [chainInV]; simp [hnot]
      rw [hd, hc]
      exact ⟨hw, hnot, le_rfl, rfl, by simp, fun z hz => by simp at hz, fun _ _ => by simp⟩

lemma lhs_to_rhs (n d a b : ℕ) (color : Fin n → Fin d) (X : Fin (n + 1) → Fin d → Bool)
    (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (hd : 0 < d) (hsurj : Function.Surjective color)
    (hX : ∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j)
    (hW0 : ∀ i : Fin n, W 0 i.castSucc ≠ W 0 i.succ)
    (hW : ∀ t (i j : Fin n), color i = color j →
      ((W t i.castSucc ≠ W t i.succ) ↔ (W t j.castSucc ≠ W t j.succ)))
    (C : Circuit) (tap : Fin d → ℕ) (out : Fin (a + 1) → ℕ)
    (hfanC : FanInTwo C) (hRBC : ReadsBack (n + 2) C)
    (houtC : C.output < n + 2 + C.size)
    (hposC : C.size - notCount C ≤ n - 1) (hnegC : notCount C ≤ b)
    (htap_lt : ∀ j, tap j < n + 2 + C.size) (hout_lt : ∀ t, out t < n + 2 + C.size)
    (htap_eval : ∀ l j, wireVal C (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]) (tap j) = X l j)
    (hout_eval : ∀ l t, wireVal C (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]) (out t) = W t l) :
    ∃ (k : ℕ) (D : Circuit) (out' : Fin (a + 1) → ℕ),
      ((Finset.univ : Finset (Fin n)).filter (fun i =>
        X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card + k ≤ b ∧
      FanInTwo D ∧ ReadsBack (2 * d + 2) D ∧ D.output < 2 * d + 2 + D.size ∧
      D.size - notCount D ≤ d - 1 ∧ notCount D ≤ k ∧
      (∀ t, out' t < 2 * d + 2 + D.size) ∧
      ∀ l t, (D.wires (List.ofFn (X l) ++ List.ofFn (fun j =>
        if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false) ++ [false, true])).getD (out' t) false = W t l := by
  classical
  let N := n + 2
  let act : Fin (n + 1) → List Bool := fun l =>
    List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]
  have hn_pos : 1 ≤ n := by
    obtain ⟨i0, _⟩ := hsurj ⟨0, hd⟩
    exact Nat.succ_le_of_lt i0.pos
  have hleaves_out0 : leaves n C (out 0) = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hni
    have heq := wireVal_eq_of_not_mem_leaves n C hRBC (hout_lt 0) hni
    rw [hout_eval i.castSucc 0, hout_eval i.succ 0] at heq
    exact hW0 i heq
  have vp := V_structure n C (out 0) hn_pos hfanC hRBC (hout_lt 0) hposC hleaves_out0
  let V := reach N C (out 0)
  have hW0_wire : ∀ i : Fin n, wireVal C (act i.castSucc) (out 0) ≠ wireVal C (act i.succ) (out 0) := by
    intro i; rw [hout_eval i.castSucc 0, hout_eval i.succ 0]; exact hW0 i
  have hco := chainOut_props n C hRBC (out 0) vp
  have hci := chainInV_props n C hRBC (out 0) vp
  have htap_some : ∀ j : Fin d, (rootInV N C V (tap j)).isSome := by
    intro j
    cases hr : rootInV N C V (tap j) with
    | some r => rfl
    | none =>
      exfalso
      obtain ⟨i0, hi0⟩ := hsurj j
      have hconst := ((hco (tap j) (htap_lt j)).2.2 hr).2 (act i0.castSucc) (act i0.succ)
        (actual_len n i0.castSucc) (actual_len n i0.succ)
        (actual_agree_except n i0).1 (actual_agree_except n i0).2.1
      rw [htap_eval i0.castSucc j, htap_eval i0.succ j] at hconst
      exact (hX i0 j).2 hi0 hconst
  let rj : Fin d → ℕ := fun j => (rootInV N C V (tap j)).get (htap_some j)
  have hrj_eq : ∀ j, rootInV N C V (tap j) = some (rj j) := fun j => Option.some_get (htap_some j) |>.symm
  have hrj_V : ∀ j, rj j ∈ V := fun j => ((hco (tap j) (htap_lt j)).2.1 (rj j) (hrj_eq j)).1
  have hrj_leaves : ∀ j, leaves n C (rj j) = Finset.univ.filter (fun i : Fin n => color i = j) := by
    intro j
    ext i
    rw [← V_toggles_iff n C hRBC (out 0) vp hW0_wire (hrj_V j) i]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hX i j]
    have hev1 := ((hco (tap j) (htap_lt j)).2.1 (rj j) (hrj_eq j)).2.2.1 (act i.castSucc) (actual_len n i.castSucc)
    have hev2 := ((hco (tap j) (htap_lt j)).2.1 (rj j) (hrj_eq j)).2.2.1 (act i.succ) (actual_len n i.succ)
    rw [htap_eval i.castSucc j] at hev1
    rw [htap_eval i.succ j] at hev2
    rw [hev1, hev2]
    cases decide ((chainOut N C V (tap j)).card % 2 = 1) <;>
      cases wireVal C (act i.castSucc) (rj j) <;> cases wireVal C (act i.succ) (rj j) <;> simp
  let base : Fin d → ℕ := fun j => descendV N C (rj j)
  let inChain : Fin d → Finset ℕ := fun j => chainInV N C (rj j)
  let outChain : Fin d → Finset ℕ := fun j => chainOut N C V (tap j)
  let chainNots : Fin d → Finset ℕ := fun j => inChain j ∪ outChain j
  have hbase_V : ∀ j, base j ∈ V := fun j => (hci (rj j) (hrj_V j)).1
  have hbase_not_not : ∀ j, ¬(N ≤ base j ∧ (gateAt C (base j - N)).op = GateOp.not) :=
    fun j => (hci (rj j) (hrj_V j)).2.1
  have hbase_leaves : ∀ j, leaves n C (base j) = Finset.univ.filter (fun i : Fin n => color i = j) :=
    fun j => ((hci (rj j) (hrj_V j)).2.2.2.1).trans (hrj_leaves j)
  have hbase_eval : ∀ j l, wireVal C (act l) (base j) =
      xor (X l j) (decide ((chainNots j).card % 2 = 1)) := by
    intro j l
    have h1 := ((hco (tap j) (htap_lt j)).2.1 (rj j) (hrj_eq j)).2.2.1 (act l) (actual_len n l)
    have h2 := (hci (rj j) (hrj_V j)).2.2.2.2.2.2 (act l) (actual_len n l)
    rw [htap_eval l j] at h1
    have hdisj_io : Disjoint (inChain j) (outChain j) := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      exact ((hco (tap j) (htap_lt j)).1 z hz2).1 ((hci (rj j) (hrj_V j)).2.2.2.2.2.1 z hz1).1
    have hcard : (chainNots j).card = (inChain j).card + (outChain j).card :=
      Finset.card_union_of_disjoint hdisj_io
    rw [h2] at h1
    rw [hcard]
    dsimp only [base, inChain, outChain, V, N] at h1 ⊢
    rcases Nat.mod_two_eq_zero_or_one (chainInV (n + 2) C (rj j)).card with hm1 | hm1 <;>
      rcases Nat.mod_two_eq_zero_or_one (chainOut (n + 2) C (reach (n + 2) C (out 0)) (tap j)).card with hm2 | hm2
    · have hm3 : ((chainInV (n + 2) C (rj j)).card + (chainOut (n + 2) C (reach (n + 2) C (out 0)) (tap j)).card) % 2 = 0 := by omega
      cases hxl : X l j <;> cases hbv : wireVal C (act l) (descendV (n + 2) C (rj j)) <;>
        simp [hxl, hbv, hm1, hm2, hm3] at h1 ⊢
    · have hm3 : ((chainInV (n + 2) C (rj j)).card + (chainOut (n + 2) C (reach (n + 2) C (out 0)) (tap j)).card) % 2 = 1 := by omega
      cases hxl : X l j <;> cases hbv : wireVal C (act l) (descendV (n + 2) C (rj j)) <;>
        simp [hxl, hbv, hm1, hm2, hm3] at h1 ⊢
    · have hm3 : ((chainInV (n + 2) C (rj j)).card + (chainOut (n + 2) C (reach (n + 2) C (out 0)) (tap j)).card) % 2 = 1 := by omega
      cases hxl : X l j <;> cases hbv : wireVal C (act l) (descendV (n + 2) C (rj j)) <;>
        simp [hxl, hbv, hm1, hm2, hm3] at h1 ⊢
    · have hm3 : ((chainInV (n + 2) C (rj j)).card + (chainOut (n + 2) C (reach (n + 2) C (out 0)) (tap j)).card) % 2 = 0 := by omega
      cases hxl : X l j <;> cases hbv : wireVal C (act l) (descendV (n + 2) C (rj j)) <;>
        simp [hxl, hbv, hm1, hm2, hm3] at h1 ⊢
  have hchain_nots_prop : ∀ j, ∀ z ∈ chainNots j,
      N ≤ z ∧ z < N + C.size ∧ (gateAt C (z - N)).op = GateOp.not ∧
      (∀ l, wireVal C (act l) z = X l j ∨ wireVal C (act l) z = !(X l j)) ∧
      (∃ b_z : Bool, ∀ l, wireVal C (act l) z = if b_z then X l j else !(X l j)) := by
    intro j z hz
    rcases Finset.mem_union.1 hz with hzin | hzout
    · obtain ⟨hzV, hzN, hzop, _, _, _, hdesc⟩ := (hci (rj j) (hrj_V j)).2.2.2.2.2.1 z hzin
      have hz_lt : z < N + C.size := lt_of_le_of_lt (mem_reach_le N C (out 0) z hzV) (hout_lt 0)
      have hz_ev : ∀ l, wireVal C (act l) z = xor (wireVal C (act l) (base j)) (decide ((chainInV N C z).card % 2 = 1)) := by
        intro l
        have := (hci z hzV).2.2.2.2.2.2 (act l) (actual_len n l)
        rwa [hdesc] at this
      refine ⟨hzN, hz_lt, hzop, ?_, ?_⟩
      · intro l
        rw [hz_ev l, hbase_eval j l]
        cases X l j <;> cases decide ((chainNots j).card % 2 = 1) <;> cases decide ((chainInV N C z).card % 2 = 1) <;> simp
      · refine ⟨(decide ((chainNots j).card % 2 = 1) == decide ((chainInV N C z).card % 2 = 1)), fun l => ?_⟩
        rw [hz_ev l, hbase_eval j l]
        cases X l j <;> cases decide ((chainNots j).card % 2 = 1) <;> cases decide ((chainInV N C z).card % 2 = 1) <;> simp
    · obtain ⟨_, hzN, hz_le, hzop, hzroot⟩ := (hco (tap j) (htap_lt j)).1 z hzout
      have hz_lt : z < N + C.size := lt_of_le_of_lt hz_le (htap_lt j)
      have hzroot' : rootInV N C V z = some (rj j) := hzroot.trans (hrj_eq j)
      have hz_ev : ∀ l, wireVal C (act l) z = xor (wireVal C (act l) (rj j)) (decide ((chainOut N C V z).card % 2 = 1)) :=
        fun l => ((hco z hz_lt).2.1 (rj j) hzroot').2.2.1 (act l) (actual_len n l)
      have hrj_ev : ∀ l, wireVal C (act l) (rj j) = xor (wireVal C (act l) (base j)) (decide ((inChain j).card % 2 = 1)) :=
        fun l => (hci (rj j) (hrj_V j)).2.2.2.2.2.2 (act l) (actual_len n l)
      refine ⟨hzN, hz_lt, hzop, ?_, ?_⟩
      · intro l
        rw [hz_ev l, hrj_ev l, hbase_eval j l]
        cases X l j <;> cases decide ((chainNots j).card % 2 = 1) <;>
          cases decide ((inChain j).card % 2 = 1) <;> cases decide ((chainOut N C V z).card % 2 = 1) <;> simp
      · refine ⟨xor (!(decide ((chainNots j).card % 2 = 1) != decide ((inChain j).card % 2 = 1)))
          (decide ((chainOut N C V z).card % 2 = 1)), fun l => ?_⟩
        rw [hz_ev l, hrj_ev l, hbase_eval j l]
        cases X l j <;> cases decide ((chainNots j).card % 2 = 1) <;>
          cases decide ((inChain j).card % 2 = 1) <;> cases decide ((chainOut N C V z).card % 2 = 1) <;> simp
  have hbase_disj : Pairwise (fun j1 j2 => Disjoint (reach N C (base j1)) (reach N C (base j2))) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]; intro z hz1 hz2
    obtain ⟨i, hi⟩ := V_leaves_nonempty n C (out 0) vp z (reach_trans N C (out 0) (base j1) (hbase_V j1) hz1)
    have hi1 : i ∈ leaves n C (base j1) := leaves_mono n C hz1 hi
    have hi2 : i ∈ leaves n C (base j2) := leaves_mono n C hz2 hi
    rw [hbase_leaves j1, Finset.mem_filter] at hi1
    rw [hbase_leaves j2, Finset.mem_filter] at hi2
    exact hne (hi1.2.symm.trans hi2.2)
  have hchain_disj : Pairwise (fun j1 j2 => Disjoint (chainNots j1) (chainNots j2)) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]; intro z hz1 hz2
    rcases Finset.mem_union.1 hz1 with h1in | h1out
    · have hzV := ((hci (rj j1) (hrj_V j1)).2.2.2.2.2.1 z h1in).1
      rcases Finset.mem_union.1 hz2 with h2in | h2out
      · have hl1 := ((hci (rj j1) (hrj_V j1)).2.2.2.2.2.1 z h1in).2.2.2.2.2.1
        have hl2 := ((hci (rj j2) (hrj_V j2)).2.2.2.2.2.1 z h2in).2.2.2.2.2.1
        have hle := hl1.symm.trans hl2
        rw [hrj_leaves j1, hrj_leaves j2] at hle
        obtain ⟨i, hi⟩ := hsurj j1
        have him : i ∈ Finset.univ.filter (fun i : Fin n => color i = j1) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
        rw [hle, Finset.mem_filter] at him
        exact hne (hi.symm.trans him.2)
      · exact ((hco (tap j2) (htap_lt j2)).1 z h2out).1 hzV
    · have hzNV := ((hco (tap j1) (htap_lt j1)).1 z h1out).1
      rcases Finset.mem_union.1 hz2 with h2in | h2out
      · exact hzNV ((hci (rj j2) (hrj_V j2)).2.2.2.2.2.1 z h2in).1
      · have hr1 := ((hco (tap j1) (htap_lt j1)).1 z h1out).2.2.2.2.trans (hrj_eq j1)
        have hr2 := ((hco (tap j2) (htap_lt j2)).1 z h2out).2.2.2.2.trans (hrj_eq j2)
        have hreq : rj j1 = rj j2 := Option.some.inj (hr1.symm.trans hr2)
        obtain ⟨i, hi⟩ := hsurj j1
        have him : i ∈ leaves n C (rj j1) := by rw [hrj_leaves j1, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
        rw [hreq, hrj_leaves j2, Finset.mem_filter] at him
        exact hne (hi.symm.trans him.2)
  have hbase_chain_disj : ∀ j1 j2, Disjoint (reach N C (base j1)) (chainNots j2) := by
    intro j1 j2
    rw [Finset.disjoint_left]; intro z hz1 hz2
    rcases Finset.mem_union.1 hz2 with h2in | h2out
    · have hl_z : leaves n C z = Finset.univ.filter (fun i : Fin n => color i = j2) := by
        rw [((hci (rj j2) (hrj_V j2)).2.2.2.2.2.1 z h2in).2.2.2.2.2.1, hrj_leaves j2]
      have hsub := leaves_mono n C hz1
      rw [hbase_leaves j1, hl_z] at hsub
      obtain ⟨i, hi⟩ := hsurj j2
      have hij : j1 = j2 := by
        have hm : i ∈ Finset.univ.filter (fun i : Fin n => color i = j1) :=
          hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        exact ((Finset.mem_filter.1 hm).2).symm.trans hi
      subst hij
      have hlt_b := ((hci (rj j1) (hrj_V j1)).2.2.2.2.2.1 z h2in).2.2.2.1
      have hle_b := mem_reach_le N C (base j1) z hz1
      dsimp only [base, N] at hle_b
      omega
    · exact ((hco (tap j2) (htap_lt j2)).1 z h2out).1 (reach_trans N C (out 0) (base j1) (hbase_V j1) hz1)
  let elim : Finset ℕ := Finset.univ.biUnion (fun j : Fin d => reach N C (base j) ∪ chainNots j)
  let allReach : Finset ℕ := Finset.univ.biUnion (fun t : Fin (a + 1) => reach N C (out t))
  let keep : Finset ℕ := (allReach \ elim).filter (N ≤ ·)
  have hkeep_lt : ∀ w ∈ keep, N ≤ w ∧ w < N + C.size := by
    intro w hw
    simp only [keep, Finset.mem_filter, Finset.mem_sdiff, allReach, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨⟨⟨t, hwt⟩, _⟩, hNw⟩
    exact ⟨hNw, lt_of_le_of_lt (mem_reach_le N C (out t) w hwt) (hout_lt t)⟩
  have hno_strict_sub : ∀ z ∈ allReach, ∀ j : Fin d, z ∈ reach N C (base j) \ {base j} →
      (∃ w ∈ keep, z ∈ effCh N C w) ∨ (∃ t : Fin (a + 1), z = out t) → False := by
    intro z hz j hstrict hsrc
    have hz_lt_base : (leaves n C z).Nonempty ∧ (leaves n C z).card < (leaves n C (base j)).card := by
      have hz_reach := (Finset.mem_sdiff.1 hstrict).1
      have hz_ne := Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hstrict).2
      have hbn : ¬ base j < n := fun hlt => by
        rw [reach_eq] at hz_reach
        have hemp : effCh N C (base j) = [] := by unfold effCh; simp [show base j < N by omega]
        simp [hemp] at hz_reach
        exact hz_ne hz_reach
      have hb_not_const : ¬(n ≤ base j ∧ base j < N) := fun hc => by
        have hm : base j ∈ V.filter (fun y => n ≤ y ∧ y < N) := Finset.mem_filter.2 ⟨hbase_V j, hc⟩
        rw [vp.hV_const] at hm; simp at hm
      have hbN : N ≤ base j := by omega
      have hb_pos : (gateAt C (base j - N)).op ≠ GateOp.not := fun ho => hbase_not_not j ⟨hbN, ho⟩
      obtain ⟨u1, u2, hu12, hne, hu1V, hu2V⟩ := vp.hpos_ch (base j) (hbase_V j) hbN hb_pos
      have hdisj := V_disjoint_children n C (out 0) vp (hbase_V j) hu12 hne
      have hdisj_l : Disjoint (leaves n C u1) (leaves n C u2) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        rw [mem_leaves] at hk1 hk2
        exact Finset.disjoint_left.1 hdisj hk1 hk2
      have hleq : leaves n C (base j) = leaves n C u1 ∪ leaves n C u2 := by
        rw [leaves_of_ge n C hbN, hu12]; simp
      have hne1 := V_leaves_nonempty n C (out 0) vp u1 hu1V
      have hne2 := V_leaves_nonempty n C (out 0) vp u2 hu2V
      have hcard_tot : (leaves n C (base j)).card = (leaves n C u1).card + (leaves n C u2).card := by
        rw [hleq, Finset.card_union_of_disjoint hdisj_l]
      have hzV : z ∈ V := reach_trans N C (out 0) (base j) (hbase_V j) hz_reach
      refine ⟨V_leaves_nonempty n C (out 0) vp z hzV, ?_⟩
      rw [reach_eq, hu12] at hz_reach
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left] at hz_reach
      rcases hz_reach with rfl | hzu1 | hzu2
      · exact absurd rfl hz_ne
      · have hle := Finset.card_le_card (leaves_mono n C hzu1)
        have hpos2 := Finset.card_pos.2 hne2
        omega
      · have hle := Finset.card_le_card (leaves_mono n C hzu2)
        have hpos1 := Finset.card_pos.2 hne1
        omega
    have hzV : z ∈ V := reach_trans N C (out 0) (base j) (hbase_V j) (Finset.mem_sdiff.1 hstrict).1
    have hV_not_union : (∃ t : Fin (a + 1), rootInV N C V (out t) = some z) → False := by
      rintro ⟨t, hrt⟩
      have ht_toggle : ∀ i1 i2 : Fin n, color i1 = color i2 →
          (i1 ∈ leaves n C z ↔ i2 ∈ leaves n C z) := by
        intro i1 i2 hc
        rw [← V_toggles_iff n C hRBC (out 0) vp hW0_wire hzV i1,
            ← V_toggles_iff n C hRBC (out 0) vp hW0_wire hzV i2]
        have hev1 := ((hco (out t) (hout_lt t)).2.1 z hrt).2.2.1 (act i1.castSucc) (actual_len n i1.castSucc)
        have hev2 := ((hco (out t) (hout_lt t)).2.1 z hrt).2.2.1 (act i1.succ) (actual_len n i1.succ)
        have hev3 := ((hco (out t) (hout_lt t)).2.1 z hrt).2.2.1 (act i2.castSucc) (actual_len n i2.castSucc)
        have hev4 := ((hco (out t) (hout_lt t)).2.1 z hrt).2.2.1 (act i2.succ) (actual_len n i2.succ)
        have ho1 := hout_eval i1.castSucc t
        have ho2 := hout_eval i1.succ t
        have ho3 := hout_eval i2.castSucc t
        have ho4 := hout_eval i2.succ t
        change wireVal C (act i1.castSucc) (out t) = W t i1.castSucc at ho1
        change wireVal C (act i1.succ) (out t) = W t i1.succ at ho2
        change wireVal C (act i2.castSucc) (out t) = W t i2.castSucc at ho3
        change wireVal C (act i2.succ) (out t) = W t i2.succ at ho4
        rw [ho1] at hev1
        rw [ho2] at hev2
        rw [ho3] at hev3
        rw [ho4] at hev4
        have hWt := hW t i1 i2 hc
        rw [hev1, hev2, hev3, hev4] at hWt
        dsimp only [act] at hWt
        have hxor : ∀ x y c : Bool, ((x ^^ c) ≠ (y ^^ c)) = (x ≠ y) := by
          intro x y c; cases x <;> cases y <;> cases c <;> simp
        simpa [hxor] using hWt
      obtain ⟨i1, hi1⟩ := hz_lt_base.1
      have hi1_col : color i1 = j := by
        have hsub := leaves_mono n C (Finset.mem_sdiff.1 hstrict).1 hi1
        rw [hbase_leaves j, Finset.mem_filter] at hsub
        exact hsub.2
      have hsub_base : leaves n C (base j) ⊆ leaves n C z := by
        intro i2 hi2
        rw [hbase_leaves j, Finset.mem_filter] at hi2
        exact (ht_toggle i1 i2 (hi1_col.trans hi2.2.symm)).1 hi1
      have hcard_ge := Finset.card_le_card hsub_base
      have := hz_lt_base.2
      omega
    rcases hsrc with ⟨w, hw_keep, hzw⟩ | ⟨t, rfl⟩
    · have hw_all := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw_keep).1).1
      have hw_nelim := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw_keep).1).2
      have hwN := (Finset.mem_filter.1 hw_keep).2
      by_cases hwV : w ∈ V
      · have hz_reach := (Finset.mem_sdiff.1 hstrict).1
        have hz_ne := Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hstrict).2
        obtain ⟨p, hp_reach, hzp⟩ := mem_reach_parent N C (base j) z hz_reach hz_ne
        have hpV : p ∈ V := reach_trans N C (out 0) (base j) (hbase_V j) hp_reach
        have hz_le : z < base j := lt_of_lt_of_le (effCh_lt N C p z hzp) (mem_reach_le N C (base j) p hp_reach)
        have hz_erase : z ∈ V.erase (out 0) := Finset.mem_erase.2 ⟨by
          have := mem_reach_le N C (out 0) (base j) (hbase_V j); omega, hzV⟩
        have hdeg := vp.hdeg z hz_erase
        have hpw : p = w := by
          by_contra hne_pw
          have hcard : 2 ≤ (V.filter (fun q => z ∈ effCh N C q)).card :=
            Finset.one_lt_card.2 ⟨p, Finset.mem_filter.2 ⟨hpV, hzp⟩, w, Finset.mem_filter.2 ⟨hwV, hzw⟩, hne_pw⟩
          dsimp only [V, N] at hcard
          omega
        subst hpw
        exact hw_nelim (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union.2 (Or.inl hp_reach)⟩)
      · obtain ⟨t, ht_reach⟩ := Finset.mem_biUnion.1 hw_all
        rcases ht_reach with ⟨_, ht_reach⟩
        have hwt_lt : w < N + C.size := lt_of_le_of_lt (mem_reach_le N C (out t) w ht_reach) (hout_lt t)
        have hw_not : (gateAt C (w - N)).op = GateOp.not := by
          by_contra hpos
          have hmem : w ∈ ((Finset.range C.size).image (· + N)).filter (fun q => (gateAt C (q - N)).op ≠ GateOp.not) := by
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
            exact ⟨⟨w - N, by omega, by omega⟩, hpos⟩
          rw [← vp.hV_pos_all] at hmem
          exact hwV (Finset.mem_filter.1 hmem).1
        have hlen : (effCh N C w).length ≤ 1 := by
          rw [effCh_eq_effInputs N C hRBC hwN hwt_lt]
          exact effInputs_len_not hw_not
        have hch_w : effCh N C w = [z] := by
          match hch : effCh N C w with
          | [] => rw [hch] at hzw; simp at hzw
          | [u] => rw [hch] at hzw; simp at hzw; rw [hzw]
          | _ :: _ :: _ => rw [hch] at hlen; simp at hlen
        have hzw_lt := effCh_lt N C w z hzw
        have hw_root : rootInV N C V w = some z := by
          rw [rootInV]; simp [hwV, show ¬ w < N by omega, hch_w, hzw_lt]
          rw [rootInV, if_pos hzV]
        have hrt := (rootInV_of_mem_reach_not_mem n C hRBC (out 0) vp (out t) (hout_lt t) w ht_reach hwV).trans hw_root
        exact hV_not_union ⟨t, hrt⟩
    · have hrt : rootInV N C V (out t) = some (out t) := by rw [rootInV, if_pos hzV]
      exact hV_not_union ⟨t, hrt⟩
  have hclosed_elim_or_const : ∀ z ∈ allReach,
      ((∃ w ∈ keep, z ∈ effCh N C w) ∨ (∃ t : Fin (a + 1), z = out t)) →
      z ∈ keep ∨ z = n ∨ z = n + 1 ∨ (∃ j : Fin d, z ∈ insert (base j) (chainNots j)) := by
    intro z hz hsrc
    by_cases hzk : z ∈ keep
    · exact Or.inl hzk
    · by_cases hzN : N ≤ z
      · have hze : z ∈ elim := by
          by_contra hne
          exact hzk (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hz, hne⟩, hzN⟩)
        dsimp only [elim] at hze
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hze
        obtain ⟨j, hzj⟩ := hze
        rcases Finset.mem_union.1 hzj with hzb | hzc
        · by_cases hzb_eq : z = base j
          · subst hzb_eq; exact Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_insert_self _ _⟩))
          · exfalso; exact hno_strict_sub z hz j (Finset.mem_sdiff.2 ⟨hzb, Finset.notMem_singleton.2 hzb_eq⟩) hsrc
        · exact Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_insert_of_mem hzc⟩))
      · by_cases hzn : z < n
        · have hj := color ⟨z, hzn⟩
          have hmem_l : (⟨z, hzn⟩ : Fin n) ∈ leaves n C (base (color ⟨z, hzn⟩)) := by
            rw [hbase_leaves (color ⟨z, hzn⟩), Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
          rw [mem_leaves] at hmem_l
          by_cases hzb_eq : z = base (color ⟨z, hzn⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨color ⟨z, hzn⟩, hzb_eq ▸ Finset.mem_insert_self _ _⟩))
          · exfalso; exact hno_strict_sub z hz (color ⟨z, hzn⟩) (Finset.mem_sdiff.2 ⟨hmem_l, Finset.notMem_singleton.2 hzb_eq⟩) hsrc
        · have hcases : z = n ∨ z = n + 1 := by omega
          rcases hcases with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
  let negColors : List (Fin d) :=
    (Finset.univ.filter (fun j : Fin d => ¬(X 0 j = true ∧ X (Fin.last n) j = false) ∧ 1 ≤ (chainNots j).card)).sort (· ≤ ·)
  let negGates : List Gate := negColors.map (fun j => gNot j.val)
  let baseD : ℕ := 2 * d + 2 + negGates.length
  let keepList : List ℕ := keep.sort (· ≤ ·)
  have hkeepList_mem : ∀ w, w ∈ keepList ↔ w ∈ keep := fun w => Finset.mem_sort _
  have hkeepList_sorted : keepList.Pairwise (· < ·) :=
    ((keep.pairwise_sort (· ≤ ·)).and (keep.sort_nodup (· ≤ ·))).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  have hnegColors_mem : ∀ j : Fin d, j ∈ negColors ↔
      ¬(X 0 j = true ∧ X (Fin.last n) j = false) ∧ 1 ≤ (chainNots j).card := by
    intro j; simp [negColors, Finset.mem_sort]
  have hnegColors_nodup : negColors.Nodup := Finset.sort_nodup _ _
  let jOf : ℕ → Fin d := fun w =>
    if h : ∃ j : Fin d, w ∈ insert (base j) (chainNots j) then Classical.choose h else ⟨0, hd⟩
  have hjOf_eq : ∀ (j : Fin d) (w : ℕ), w ∈ insert (base j) (chainNots j) → jOf w = j := by
    intro j w hw
    have hex : ∃ j' : Fin d, w ∈ insert (base j') (chainNots j') := ⟨j, hw⟩
    simp only [jOf, dif_pos hex]
    have hj' := Classical.choose_spec hex
    by_contra hne
    rcases Finset.mem_insert.1 hw with rfl | hwc <;> rcases Finset.mem_insert.1 hj' with hjb' | hjc'
    · exact Finset.disjoint_left.1 (hbase_disj hne) (self_mem_reach N C _) (hjb' ▸ self_mem_reach N C _)
    · exact Finset.disjoint_left.1 (hbase_chain_disj j (Classical.choose hex)) (self_mem_reach N C _) hjc'
    · exact Finset.disjoint_left.1 (hbase_chain_disj (Classical.choose hex) j) (hjb' ▸ self_mem_reach N C _) hwc
    · exact Finset.disjoint_left.1 (hchain_disj (Ne.symm hne)) hwc hjc'
  have hbase_chain_val : ∀ (j : Fin d) (w : ℕ), w ∈ insert (base j) (chainNots j) →
      ∃ b_w : Bool, ∀ l, wireVal C (act l) w = if b_w then X l j else !(X l j) := by
    intro j w hw
    rcases Finset.mem_insert.1 hw with rfl | hwc
    · refine ⟨!(decide ((chainNots j).card % 2 = 1)), fun l => ?_⟩
      rw [hbase_eval j l]
      cases X l j <;> cases decide ((chainNots j).card % 2 = 1) <;> simp
    · exact (hchain_nots_prop j w hwc).2.2.2.2
  have hneg_mem_of_neg : ∀ (j : Fin d) (w : ℕ), w ∈ insert (base j) (chainNots j) →
      wireVal C (act 0) w ≠ X 0 j → ¬(X 0 j = true ∧ X (Fin.last n) j = false) → j ∈ negColors := by
    intro j w hw hne hcond
    rw [hnegColors_mem]
    refine ⟨hcond, ?_⟩
    by_contra hlt1
    have h0 : (chainNots j).card = 0 := by omega
    have hce : chainNots j = ∅ := Finset.card_eq_zero.1 h0
    rw [hce, insert_empty_eq, Finset.mem_singleton] at hw
    subst hw
    have hev := hbase_eval j 0
    rw [h0] at hev
    simp at hev
    exact hne hev
  let wmap : ℕ → ℕ := fun w =>
    if w ∈ keep then baseD + keepList.idxOf w
    else if w = n then 2 * d
    else if w = n + 1 then 2 * d + 1
    else
      let j := jOf w
      if wireVal C (act 0) w = X 0 j then j.val
      else if X 0 j = true ∧ X (Fin.last n) j = false then d + j.val
      else 2 * d + 2 + negColors.idxOf j
  have hwmap_nkeep : ∀ w, w ∉ keep →
      (w = n ∨ w = n + 1 ∨ ∃ j : Fin d, w ∈ insert (base j) (chainNots j)) → wmap w < baseD := by
    intro w hnk hw
    dsimp only [wmap]
    rw [if_neg hnk]
    rcases hw with rfl | rfl | ⟨j, hjw⟩
    · simp [baseD]; omega
    · have heqn : n + 1 ≠ n := by omega
      simp [heqn, baseD]; omega
    · by_cases heq1 : w = n
      · subst heq1; simp [baseD]; omega
      · by_cases heq2 : w = n + 1
        · subst heq2; have heq1' : n + 1 ≠ n := by omega
          simp [heq1', baseD]; omega
        · simp only [heq1, heq2, ite_false]
          rw [hjOf_eq j w hjw]
          split_ifs with hpos hcond
          · have := j.isLt; dsimp only [baseD]; omega
          · have := j.isLt; dsimp only [baseD]; omega
          · have hmem := hneg_mem_of_neg j w hjw hpos hcond
            have hidx := List.idxOf_lt_length_iff.2 hmem
            dsimp only [baseD, negGates]
            rw [List.length_map]
            omega
  let keepGates : List Gate :=
    keepList.map (fun w => ⟨(gateAt C (w - N)).op, (effInputs (gateAt C (w - N))).map wmap⟩)
  let D : Circuit := ⟨negGates ++ keepGates, 0⟩
  let out' : Fin (a + 1) → ℕ := fun t => wmap (out t)
  let k : ℕ := notCount D
  have hkeep_closed : ∀ w ∈ keep, ∀ u ∈ effInputs (gateAt C (w - N)),
      u ∈ keep ∨ u = n ∨ u = n + 1 ∨ ∃ j : Fin d, u ∈ insert (base j) (chainNots j) := by
    intro w hw u hu
    obtain ⟨hwN, hw_lt⟩ := hkeep_lt w hw
    have hu_ch : u ∈ effCh N C w := by rw [effCh_eq_effInputs N C hRBC hwN hw_lt]; exact hu
    have hw_all : w ∈ allReach := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw).1).1
    obtain ⟨t, ht_reach⟩ := Finset.mem_biUnion.1 hw_all
    have hu_reach : u ∈ allReach := by
      refine Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, ?_⟩
      exact reach_trans N C (out t) w ht_reach.2 (by
        rw [reach_eq]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu_ch, self_mem_reach N C u⟩))
    exact hclosed_elim_or_const u hu_reach (Or.inl ⟨w, hw, hu_ch⟩)
  have hout_closed : ∀ t : Fin (a + 1),
      out t ∈ keep ∨ out t = n ∨ out t = n + 1 ∨ ∃ j : Fin d, out t ∈ insert (base j) (chainNots j) := by
    intro t
    have hot_all : out t ∈ allReach := Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, self_mem_reach N C (out t)⟩
    exact hclosed_elim_or_const (out t) hot_all (Or.inr ⟨t, rfl⟩)
  have hRB_neg : RB (2 * d + 2) negGates := by
    suffices ∀ (offset : ℕ) (js : List (Fin d)), RB (2 * d + 2 + offset) (js.map (fun j => gNot j.val)) by
      simpa using this 0 negColors
    intro offset js
    induction js generalizing offset with
    | nil => exact RB.nil _
    | cons j js ih =>
      simp only [List.map_cons]
      refine RB.cons (fun v hv => ?_) (by simpa [Nat.add_assoc] using ih (offset + 1))
      simp [gNot] at hv; subst hv; have := j.isLt; omega
  have hRB_keep : RB baseD keepGates := by
    suffices ∀ (pref suf : List ℕ), pref ++ suf = keepList →
        RB (baseD + pref.length) (suf.map (fun w => ⟨(gateAt C (w - N)).op, (effInputs (gateAt C (w - N))).map wmap⟩)) by
      simpa using this [] keepList rfl
    intro pref suf
    induction suf generalizing pref with
    | nil => intro _; exact RB.nil _
    | cons w suf ih =>
      intro hcat
      simp only [List.map_cons]
      have hw_mem : w ∈ keep := by
        rw [← hkeepList_mem, ← hcat]
        simp
      obtain ⟨hwN, hw_lt⟩ := hkeep_lt w hw_mem
      refine RB.cons ?_ ?_
      · intro v hv
        simp only [List.mem_map] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        have hu_ch : u ∈ effCh N C w := by rw [effCh_eq_effInputs N C hRBC hwN hw_lt]; exact hu
        have hu_lt_w : u < w := effCh_lt N C w u hu_ch
        rcases hkeep_closed w hw_mem u hu with huk | huc
        · have hidx_lt : keepList.idxOf u < keepList.idxOf w := by
            have hu_mem_l : u ∈ keepList := (hkeepList_mem u).2 huk
            have hw_mem_l : w ∈ keepList := (hkeepList_mem w).2 hw_mem
            have hget_u : keepList[keepList.idxOf u]'(List.idxOf_lt_length_iff.2 hu_mem_l) = u :=
              List.getElem_idxOf (List.idxOf_lt_length_iff.2 hu_mem_l)
            have hget_w : keepList[keepList.idxOf w]'(List.idxOf_lt_length_iff.2 hw_mem_l) = w :=
              List.getElem_idxOf (List.idxOf_lt_length_iff.2 hw_mem_l)
            by_contra hge
            have hle : keepList.idxOf w ≤ keepList.idxOf u := by omega
            rcases Nat.eq_or_lt_of_le hle with heq | hlt
            · have hopt : keepList[keepList.idxOf w]? = keepList[keepList.idxOf u]? :=
                congrArg (fun i => keepList[i]?) heq
              rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hw_mem_l),
                  List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hu_mem_l), hget_w, hget_u] at hopt
              injection hopt with hwu
              omega
            · have hlt2 := List.pairwise_iff_getElem.1 hkeepList_sorted (keepList.idxOf w) (keepList.idxOf u)
                (List.idxOf_lt_length_iff.2 hw_mem_l) (List.idxOf_lt_length_iff.2 hu_mem_l) hlt
              rw [hget_w, hget_u] at hlt2
              omega
          have hw_idx : keepList.idxOf w = pref.length := by
            have hnd := keep.sort_nodup (· ≤ ·)
            change keepList.Nodup at hnd
            have hcat' : pref ++ w :: suf = keepList := hcat
            rw [← hcat'] at hnd ⊢
            have hlen_p : pref.length < (pref ++ w :: suf).length := by simp
            have h := List.Nodup.idxOf_getElem hnd pref.length hlen_p
            simpa using h
          dsimp only [wmap]
          rw [if_pos huk]
          omega
        · have hwmap_lt := hwmap_nkeep u (fun huk => by

            rcases huc with rfl | rfl | ⟨j, huj⟩
            · exact absurd (hkeep_lt _ huk).1 (by omega)
            · exact absurd (hkeep_lt _ huk).1 (by omega)
            · have huk_nelim := (Finset.mem_sdiff.1 (Finset.mem_filter.1 huk).1).2
              apply huk_nelim
              refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, ?_⟩
              rcases Finset.mem_insert.1 huj with rfl | hjc
              · exact Finset.mem_union.2 (Or.inl (self_mem_reach N C _))
              · exact Finset.mem_union.2 (Or.inr hjc)) huc
          omega
      · have hih := ih (pref ++ [w]) (by simpa [List.append_assoc] using hcat)
        simpa [List.length_append, Nat.add_assoc] using hih
  have hRBD' : RB (2 * d + 2) D.gates := RB.append hRB_neg (by simpa [baseD] using hRB_keep)
  have hfanD : FanInTwo D := by
    intro g hg
    simp only [D, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [negGates, List.mem_map] at hg
      obtain ⟨j, _, rfl⟩ := hg
      simp [gNot]
    · simp only [keepGates, List.mem_map] at hg
      obtain ⟨w, hw_mem, rfl⟩ := hg
      obtain ⟨hwN, hw_lt⟩ := hkeep_lt w ((hkeepList_mem w).1 hw_mem)
      by_cases hnot : (gateAt C (w - N)).op = GateOp.not
      · refine ⟨Or.inr (Or.inr hnot), ?_⟩
        simp only [List.length_map]
        exact le_trans (effInputs_len_not hnot) (by omega)
      · obtain ⟨ho, hl⟩ := effInputs_len_pos hfanC hwN hw_lt hnot
        exact ⟨ho.elim Or.inl (fun h => Or.inr (Or.inl h)), by simpa using hl⟩
  have hDsize_pos : D.size - notCount D ≤ d - 1 := by
    have hnc_D : notCount D = negGates.length + (keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not)).card := by
      change notCount ⟨negGates ++ keepGates, 0⟩ = _
      rw [nc_append]
      have hnc_neg : notCount ⟨negGates, 0⟩ = negGates.length := by
        unfold notCount
        rw [List.filter_eq_self.2 (fun g hg => by
          simp only [negGates, List.mem_map] at hg
          obtain ⟨j, _, rfl⟩ := hg
          simp [gNot])]
      have hnc_keep : notCount ⟨keepGates, 0⟩ = (keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not)).card := by
        unfold notCount keepGates
        rw [List.filter_map, List.length_map]
        have hnodup := keep.sort_nodup (· ≤ ·)
        trans (keepList.filter (fun w => decide ((gateAt C (w - N)).op = GateOp.not))).length
        · congr 1; apply List.filter_congr; intro w _
          cases h : (gateAt C (w - N)).op <;> simp [h]
        · rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ hnodup)]
          congr 1; ext w
          simp [keepList]
      rw [hnc_neg, hnc_keep]
    have hkeep_pos : keepGates.length - (keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not)).card =
        (keep.filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not)).card := by
      have hlen : keepGates.length = keep.card := by simp [keepGates, keepList]
      rw [hlen]
      have hsplit : (keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not)).card +
          (keep.filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not)).card = keep.card := by
        have hu : keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not) ∪
            keep.filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not) = keep := by
          ext w; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        have hd : Disjoint (keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not))
            (keep.filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not)) := by
          rw [Finset.disjoint_left]; intro w h1 h2; simp only [Finset.mem_filter] at h1 h2; exact h2.2 h1.2
        rw [← Finset.card_union_of_disjoint hd, hu]
      omega
    have hVpos_sub_keep : keep.filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not) ⊆
        (V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)) \
        Finset.univ.biUnion (fun j : Fin d => (reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw ⊢
      obtain ⟨hw_keep, hne⟩ := hw
      obtain ⟨hwN, hw_lt⟩ := hkeep_lt w hw_keep
      have hw_allpos : w ∈ ((Finset.range C.size).image (· + N)).filter (fun z => (gateAt C (z - N)).op ≠ GateOp.not) := by
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨w - N, by omega, by omega⟩, hne⟩
      dsimp only [N] at hw_allpos
      rw [← vp.hV_pos_all] at hw_allpos
      refine ⟨Finset.mem_filter.1 hw_allpos, ?_⟩
      rintro ⟨j, hj_reach, _⟩
      exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw_keep).1).2
        (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union.2 (Or.inl hj_reach)⟩)
    have hVpos_card : (V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)).card = n - 1 := by
      have h1 := V_pos_card_eq_leaves n C (out 0) vp (out 0) (self_mem_reach N C (out 0))
      rw [hleaves_out0, Finset.card_univ, Fintype.card_fin] at h1
      change (V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)).card + 1 = n at h1
      omega
    have hsub_pos_sum : (Finset.univ.biUnion (fun j : Fin d =>
        (reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not))).card = n - d := by
      rw [Finset.card_biUnion (fun j1 _ j2 _ hne => Finset.disjoint_filter_filter (hbase_disj hne))]
      have hterm : ∀ j : Fin d, ((reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)).card + 1 =
          (leaves n C (base j)).card := fun j => V_pos_card_eq_leaves n C (out 0) vp (base j) (hbase_V j)
      have hsum_leaves : ∑ j : Fin d, (leaves n C (base j)).card = n := by
        simp_rw [hbase_leaves]
        have := Finset.card_eq_sum_card_fiberwise (f := color) (s := (Finset.univ : Finset (Fin n)))
          (t := (Finset.univ : Finset (Fin d))) (fun _ _ => Finset.mem_univ _)
        simpa using this.symm
      have hge1 : ∀ j : Fin d, 1 ≤ (leaves n C (base j)).card := fun j => by
        obtain ⟨i, hi⟩ := hsurj j
        exact Finset.card_pos.2 ⟨i, by rw [hbase_leaves j, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩⟩
      have hadd : ∑ j : Fin d, ((reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not)).card + d = n := by
        have hd_sum : d = ∑ _ : Fin d, 1 := by simp
        conv_lhs => rhs; rw [hd_sum]
        rw [← Finset.sum_add_distrib, ← hsum_leaves]
        exact Finset.sum_congr rfl fun j _ => hterm j
      omega
    have hle_sdiff := Finset.card_le_card hVpos_sub_keep
    have hle_sub : (Finset.univ.biUnion (fun j : Fin d =>
        (reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not))) ⊆
        V.filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op ≠ GateOp.not) := by
      intro w hw
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter] at hw ⊢
      rcases hw with ⟨j, hw1, hw2, hw3⟩
      exact ⟨reach_trans N C (out 0) (base j) (hbase_V j) hw1, hw2, hw3⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hle_sub, hVpos_card, hsub_pos_sum] at hle_sdiff
    have hDsize : D.size = negGates.length + keepGates.length := by simp [D, Circuit.size]
    omega
  have hfalls_budget : ((Finset.univ : Finset (Fin n)).filter (fun i =>
      X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card + k ≤ b := by
    let AllNot : Finset ℕ := ((Finset.range C.size).image (· + N)).filter (fun w => (gateAt C (w - N)).op = GateOp.not)
    have hAllNot_card : AllNot.card = notCount C := by
      have hsplit : (((Finset.range C.size).image (· + N)).filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not)).card +
          AllNot.card = ((Finset.range C.size).image (· + N)).card := by
        have hu : ((Finset.range C.size).image (· + N)).filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not) ∪
            AllNot = (Finset.range C.size).image (· + N) := by
          ext w; simp only [AllNot, Finset.mem_union, Finset.mem_filter]; tauto
        have hd : Disjoint (((Finset.range C.size).image (· + N)).filter (fun w => (gateAt C (w - N)).op ≠ GateOp.not))
            AllNot := by
          rw [Finset.disjoint_left]; intro w h1 h2; simp only [AllNot, Finset.mem_filter] at h1 h2; exact h1.2 h2.2
        rw [← Finset.card_union_of_disjoint hd, hu]
      rw [allPos_card n C, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range] at hsplit
      have hnc_le : notCount C ≤ C.size := by unfold notCount Circuit.size; exact List.length_filter_le _ _
      omega
    let keepNot := keep.filter (fun w => (gateAt C (w - N)).op = GateOp.not)
    let subNot : Fin d → Finset ℕ := fun j => (reach N C (base j)).filter (fun w => N ≤ w ∧ (gateAt C (w - N)).op = GateOp.not)
    have hsub_all : ∀ w ∈ keepNot ∪ (Finset.univ.biUnion (fun j : Fin d => subNot j ∪ chainNots j)), w ∈ AllNot := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        keepNot, subNot, AllNot, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hw ⊢
      rcases hw with ⟨hw_keep, hw_op⟩ | ⟨j, ⟨hw_r, hwN, hw_op⟩ | hw_c⟩
      · obtain ⟨hwN, hw_lt⟩ := hkeep_lt w hw_keep
        exact ⟨⟨w - N, by omega, by omega⟩, hw_op⟩
      · have hw_lt : w < N + C.size := lt_of_le_of_lt (mem_reach_le N C (out 0) w (reach_trans N C (out 0) (base j) (hbase_V j) hw_r)) (hout_lt 0)
        exact ⟨⟨w - N, by omega, by omega⟩, hw_op⟩
      · obtain ⟨hwN, hw_lt, hw_op, _⟩ := hchain_nots_prop j w hw_c
        exact ⟨⟨w - N, by omega, by omega⟩, hw_op⟩
    have hdisj_keep : Disjoint keepNot (Finset.univ.biUnion (fun j : Fin d => subNot j ∪ chainNots j)) := by
      rw [Finset.disjoint_left]; intro w hw1 hw2
      simp only [keepNot, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, subNot] at hw1 hw2
      rcases hw2 with ⟨j, ⟨hwr, _⟩ | hwc⟩
      · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw1.1).1).2
          (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union.2 (Or.inl hwr)⟩)
      · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hw1.1).1).2
          (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union.2 (Or.inr hwc)⟩)
    have hdisj_j : Pairwise (fun j1 j2 => Disjoint (subNot j1 ∪ chainNots j1) (subNot j2 ∪ chainNots j2)) := by
      intro j1 j2 hne
      rw [Finset.disjoint_left]; intro z hz1 hz2
      simp only [Finset.mem_union, Finset.mem_filter, subNot] at hz1 hz2
      rcases hz1 with ⟨h1r, _⟩ | h1c <;> rcases hz2 with ⟨h2r, _⟩ | h2c
      · exact Finset.disjoint_left.1 (hbase_disj hne) h1r h2r
      · exact Finset.disjoint_left.1 (hbase_chain_disj j1 j2) h1r h2c
      · exact Finset.disjoint_left.1 (hbase_chain_disj j2 j1) h2r h1c
      · exact Finset.disjoint_left.1 (hchain_disj hne) h1c h2c
    have hdisj_sc : ∀ j, Disjoint (subNot j) (chainNots j) :=
      fun j => Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (hbase_chain_disj j j)
    have hsum_not : keepNot.card + ∑ j : Fin d, ((subNot j).card + (chainNots j).card) ≤ notCount C := by
      rw [← hAllNot_card]
      calc keepNot.card + ∑ j : Fin d, ((subNot j).card + (chainNots j).card)
          = keepNot.card + ∑ j : Fin d, (subNot j ∪ chainNots j).card := by
            congr 1; exact Finset.sum_congr rfl fun j _ => (Finset.card_union_of_disjoint (hdisj_sc j)).symm
        _ = keepNot.card + (Finset.univ.biUnion (fun j : Fin d => subNot j ∪ chainNots j)).card := by
            rw [Finset.card_biUnion (fun j1 _ j2 _ hne => hdisj_j hne)]
        _ = (keepNot ∪ Finset.univ.biUnion (fun j : Fin d => subNot j ∪ chainNots j)).card :=
            (Finset.card_union_of_disjoint hdisj_keep).symm
        _ ≤ AllNot.card := Finset.card_le_card hsub_all
    have hfalls_j : ∀ j : Fin d,
        ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card +
          (if j ∈ negColors then 1 else 0) ≤ (subNot j).card + (chainNots j).card := by
      intro j
      have hfalls_eq_f : ((Finset.univ : Finset (Fin n)).filter (fun i => color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card =
          fallsOf n (fun l => X l j) := by
        unfold fallsOf; congr 1; ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨(hX i j).1 (by simp [h1, h2]), h1, h2⟩
      rw [hfalls_eq_f]
      have htree := V_falls_le_notCount n C hfanC hRBC (out 0) vp (base j) (hbase_V j)
      change fallsOf n (fun l => wireVal C (act l) (base j)) ≤ (subNot j).card at htree
      by_cases hpar : (chainNots j).card % 2 = 0
      · have heval_eq : (fun l => wireVal C (act l) (base j)) = (fun l => X l j) := by
          ext l; rw [hbase_eval j l]; simp [hpar]
        rw [heval_eq] at htree
        split_ifs with hm
        · rw [hnegColors_mem] at hm; omega
        · omega
      · have hodd : (chainNots j).card % 2 = 1 := by omega
        have hpos_cn : 1 ≤ (chainNots j).card := by omega
        have heval_eq : (fun l => wireVal C (act l) (base j)) = (fun l => !(X l j)) := by
          ext l; rw [hbase_eval j l]; simp [hodd]
        rw [heval_eq, fallsOf_not] at htree
        have hsub := rises_sub_falls n (fun l => X l j)
        by_cases hcond : X 0 j = true ∧ X (Fin.last n) j = false
        · have hneg_n : j ∉ negColors := by rw [hnegColors_mem]; tauto
          rw [if_neg hneg_n]
          simp [hcond.1, hcond.2] at hsub
          omega
        · have hneg_y : j ∈ negColors := by rw [hnegColors_mem]; exact ⟨hcond, hpos_cn⟩
          rw [if_pos hneg_y]
          have hle_fr : fallsOf n (fun l => X l j) ≤ risesOf n (fun l => X l j) := by
            cases h0 : X 0 j <;> cases hN : X (Fin.last n) j <;> simp [h0, hN] at hsub hcond <;> omega
          omega
    have hnegColors_card : negColors.length = ∑ j : Fin d, if j ∈ negColors then 1 else 0 := by
      have hs : (∑ j : Fin d, if j ∈ negColors then 1 else 0) = (Finset.univ.filter (· ∈ negColors)).card := by
        rw [Finset.card_filter]
      rw [hs, ← List.toFinset_card_of_nodup hnegColors_nodup]
      congr 1; ext j; simp
    have hnc_D : k = negColors.length + keepNot.card := by
      change notCount ⟨negGates ++ keepGates, 0⟩ = _
      rw [nc_append]
      have hnc_neg : notCount ⟨negGates, 0⟩ = negColors.length := by
        unfold notCount
        rw [List.filter_eq_self.2 (fun g hg => by
          simp only [negGates, List.mem_map] at hg
          obtain ⟨j, _, rfl⟩ := hg
          simp [gNot])]
        simp [negGates]
      have hnc_keep : notCount ⟨keepGates, 0⟩ = keepNot.card := by
        unfold notCount keepGates keepNot
        rw [List.filter_map, List.length_map]
        have hnodup := keep.sort_nodup (· ≤ ·)
        trans (keepList.filter (fun w => decide ((gateAt C (w - N)).op = GateOp.not))).length
        · congr 1; apply List.filter_congr; intro w _
          cases h : (gateAt C (w - N)).op <;> simp [h]
        · rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ hnodup)]
          congr 1; ext w; simp [keepList]
      rw [hnc_neg, hnc_keep]
    have hfalls_tot : ((Finset.univ : Finset (Fin n)).filter (fun i =>
        X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card =
        ∑ j : Fin d, ((Finset.univ : Finset (Fin n)).filter (fun i =>
          color i = j ∧ X i.castSucc j = true ∧ X i.succ j = false)).card := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := color)
        (s := (Finset.univ : Finset (Fin n)).filter (fun i => X i.castSucc (color i) = true ∧ X i.succ (color i) = false))
        (t := (Finset.univ : Finset (Fin d))) (fun _ _ => Finset.mem_univ _)
      rw [hfib]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, hc⟩; rw [hc] at h1 h2; exact ⟨hc, h1, h2⟩
      · rintro ⟨hc, h1, h2⟩; rw [← hc] at h1 h2; exact ⟨⟨h1, h2⟩, hc⟩
    have hsum_j := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) fun j _ => hfalls_j j
    rw [Finset.sum_add_distrib, ← hnegColors_card, ← hfalls_tot] at hsum_j
    omega
  refine ⟨k, D, out', hfalls_budget, hfanD, RB_to_ReadsBack (2 * d + 2) D hRBD', ?_, hDsize_pos, le_rfl, ?_, ?_⟩
  · change 0 < 2 * d + 2 + D.size; omega
  · intro t
    rcases hout_closed t with hk | hcn
    · dsimp only [out', wmap]
      rw [if_pos hk]
      have hidx := List.idxOf_lt_length_iff.2 ((hkeepList_mem _).2 hk)
      change baseD + keepList.idxOf (out t) < 2 * d + 2 + (negGates ++ keepGates).length
      simp [baseD, keepGates]
      omega
    · have := hwmap_nkeep (out t) (fun hk => by
        rcases hcn with h1 | h2 | ⟨j, hj⟩
        · exact absurd (hkeep_lt _ hk).1 (by omega)
        · exact absurd (hkeep_lt _ hk).1 (by omega)
        · apply (Finset.mem_sdiff.1 (Finset.mem_filter.1 hk).1).2
          refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, ?_⟩
          rcases Finset.mem_insert.1 hj with hjb | hjc
          · rw [hjb]; exact Finset.mem_union.2 (Or.inl (self_mem_reach N C _))
          · exact Finset.mem_union.2 (Or.inr hjc)) hcn
      dsimp only [out']
      change wmap (out t) < 2 * d + 2 + (negGates ++ keepGates).length
      dsimp only [baseD] at this
      simp; omega
  · intro l t
    let log := List.ofFn (X l) ++ List.ofFn (fun j =>
      if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false) ++ [false, true]
    have hlog_len : log.length = 2 * d + 2 := by simp [log]; omega
    have hspecD := run_spec D.gates log (by simpa [hlog_len] using hRBD')
    have hCD : Cons (wireVal D log) (2 * d + 2) D.gates := by
      change Cons (fun u => (run D.gates log).getD u false) (2 * d + 2) D.gates
      rw [← hlog_len]; exact hspecD.2
    have hCD_neg : Cons (wireVal D log) (2 * d + 2) negGates := hCD.left
    have hCD_keep : Cons (wireVal D log) baseD keepGates := hCD.right' rfl
    have hneg_eval : ∀ j ∈ negColors, wireVal D log (2 * d + 2 + negColors.idxOf j) = !(X l j) := by
      intro j hj
      have hidx_lt : negColors.idxOf j < negColors.length := List.idxOf_lt_length_iff.2 hj
      suffices ∀ (pref suf : List (Fin d)), pref ++ suf = negColors →
          Cons (wireVal D log) (2 * d + 2 + pref.length) (suf.map (fun q => gNot q.val)) →
          ∀ (q : Fin d), q ∈ suf → q ∉ pref →
            wireVal D log (2 * d + 2 + pref.length + suf.idxOf q) = !(X l q) by
        have hres := this [] negColors rfl (by simpa using hCD_neg) j hj (by simp)
        simpa using hres
      intro pref suf
      induction suf generalizing pref with
      | nil => intro _ _ q hq; simp at hq
      | cons q0 suf ih =>
        intro hcat hCs q hq hq_np
        simp only [List.map_cons, Cons] at hCs
        by_cases heq : q = q0
        · subst heq
          simp only [List.idxOf_cons_self, Nat.add_zero]
          rw [hCs.1]
          simp only [gNot, value_not]
          have hq_in : wireVal D log q.val = X l q := by
            change (run D.gates log).getD q.val false = X l q
            rw [hspecD.1 q.val (by rw [hlog_len]; have := q.isLt; omega)]
            dsimp only [log]
            rw [getD_append_left' _ _ _ _ (by simp; omega), getD_append_left' _ _ _ _ (by simp [q.isLt])]
            simp [q.isLt]
          rw [hq_in]
        · have hidx_q : (q0 :: suf).idxOf q = 1 + suf.idxOf q := by
            rw [List.idxOf_cons_ne _ (Ne.symm heq)]; omega
          rw [hidx_q]
          have hih := ih (pref ++ [q0]) (by simpa [List.append_assoc] using hcat)
            (by simpa [List.length_append, Nat.add_assoc] using hCs.2) q
            (by simp [heq] at hq; exact hq) (fun hm => by
              simp at hm; rcases hm with h1 | rfl; exact hq_np h1; exact heq rfl)
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
    have hD_eval_all : ∀ w,
        (w ∈ keep ∨ w = n ∨ w = n + 1 ∨ ∃ j : Fin d, w ∈ insert (base j) (chainNots j)) →
        wireVal D log (wmap w) = wireVal C (act l) w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_c
        by_cases hwk : w ∈ keep
        · obtain ⟨hwN, hw_lt⟩ := hkeep_lt w hwk
          have hgate_eq : wireVal D log (baseD + keepList.idxOf w) =
              value (wireVal D log) ⟨(gateAt C (w - N)).op, (effInputs (gateAt C (w - N))).map wmap⟩ := by
            suffices ∀ (pref suf : List ℕ), pref ++ suf = keepList →
                Cons (wireVal D log) (baseD + pref.length)
                  (suf.map (fun z => ⟨(gateAt C (z - N)).op, (effInputs (gateAt C (z - N))).map wmap⟩)) →
                ∀ z ∈ suf, z ∉ pref →
                  wireVal D log (baseD + pref.length + suf.idxOf z) =
                  value (wireVal D log) ⟨(gateAt C (z - N)).op, (effInputs (gateAt C (z - N))).map wmap⟩ by
              have hres := this [] keepList rfl (by simpa using hCD_keep) w ((hkeepList_mem w).2 hwk) (by simp)
              simpa using hres
            intro pref suf
            induction suf generalizing pref with
            | nil => intro _ _ z hz; simp at hz
            | cons z0 suf ihs =>
              intro hcat hCs z hz hz_np
              simp only [List.map_cons, Cons] at hCs
              by_cases heq : z = z0
              · subst heq; simpa using hCs.1
              · have hidx_z : (z0 :: suf).idxOf z = 1 + suf.idxOf z := by
                  rw [List.idxOf_cons_ne _ (Ne.symm heq)]; omega
                rw [hidx_z]
                have hih := ihs (pref ++ [z0]) (by simpa [List.append_assoc] using hcat)
                  (by simpa [List.length_append, Nat.add_assoc] using hCs.2) z
                  (by simp [heq] at hz; exact hz) (fun hm => by
                    simp at hm; rcases hm with h1 | rfl; exact hz_np h1; exact heq rfl)
                simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
          dsimp only [wmap]
          rw [if_pos hwk, hgate_eq, wireVal_gate N C hRBC (act l) (actual_len n l) hwN hw_lt, value_eff, value_eff]
          have heff_map : effInputs (Gate.mk (gateAt C (w - N)).op
              ((effInputs (gateAt C (w - N))).map wmap)) =
              (effInputs (gateAt C (w - N))).map wmap := by
            cases hop : (gateAt C (w - N)).op <;> simp [effInputs, hop, ← List.map_take, List.take_take]
          change (gateAt C (w - N)).op.eval ((effInputs (Gate.mk (gateAt C (w - N)).op
              ((effInputs (gateAt C (w - N))).map wmap))).map (wireVal D log)) =
              (gateAt C (w - N)).op.eval ((effInputs (gateAt C (w - N))).map (wireVal C (act l)))
          rw [heff_map, List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hu_ch : u ∈ effCh N C w := by rw [effCh_eq_effInputs N C hRBC hwN hw_lt]; exact hu
          exact ih u (effCh_lt N C w u hu_ch) (hkeep_closed w hwk u hu)
        · dsimp only [wmap]
          rw [if_neg hwk]
          rcases hw_c with hk | hwn | hwn1 | ⟨j, hjw⟩
          · exact absurd hk hwk
          · rw [hwn]
            simp only [ite_true]
            rw [wireVal_lt_N N C hRBC (act l) (actual_len n l) (by omega)]
            have hdn : (run D.gates log).getD (2 * d) false = log.getD (2 * d) false :=
              hspecD.1 (2 * d) (by rw [hlog_len]; omega)
            change (run D.gates log).getD (2 * d) false = (act l).getD n false
            rw [hdn]
            dsimp only [log, act]
            rw [getD_append_right' _ _ _ _ (by simp; omega), getD_append_right' _ _ _ _ (by simp)]
            simp [show 2 * d - (d + d) = 0 by omega]
          · rw [hwn1]
            have heqn : n + 1 ≠ n := by omega
            simp only [heqn, ite_false, ite_true]
            rw [wireVal_lt_N N C hRBC (act l) (actual_len n l) (by omega)]
            have hd1 : (run D.gates log).getD (2 * d + 1) false = log.getD (2 * d + 1) false :=
              hspecD.1 (2 * d + 1) (by rw [hlog_len]; omega)
            change (run D.gates log).getD (2 * d + 1) false = (act l).getD (n + 1) false
            rw [hd1]
            dsimp only [log, act]
            rw [getD_append_right' _ _ _ _ (by simp; omega), getD_append_right' _ _ _ _ (by simp)]
            simp [show 2 * d + 1 - (d + d) = 1 by omega]
          · by_cases heq1 : w = n
            · rw [heq1] at hjw
              have hc : n ∈ V.filter (fun z => n ≤ z ∧ z < N) := Finset.mem_filter.2 ⟨
                reach_trans N C (out 0) (base j) (hbase_V j)
                  (by rcases Finset.mem_insert.1 hjw with hjb | hjc
                      · rw [hjb]; exact self_mem_reach N C _
                      · exact absurd ((hchain_nots_prop j n hjc).1) (by omega)),
                le_rfl, by omega⟩
              rw [vp.hV_const] at hc; simp at hc
            · by_cases heq2 : w = n + 1
              · rw [heq2] at hjw
                have hc : n + 1 ∈ V.filter (fun z => n ≤ z ∧ z < N) := Finset.mem_filter.2 ⟨
                  reach_trans N C (out 0) (base j) (hbase_V j)
                    (by rcases Finset.mem_insert.1 hjw with hjb | hjc
                        · rw [hjb]; exact self_mem_reach N C _
                        · exact absurd ((hchain_nots_prop j (n + 1) hjc).1) (by omega)),
                  by omega, by omega⟩
                rw [vp.hV_const] at hc; simp at hc
              · simp only [heq1, heq2, ite_false]
                rw [hjOf_eq j w hjw]
                obtain ⟨b_w, hbw⟩ := hbase_chain_val j w hjw
                by_cases hpos : wireVal C (act 0) w = X 0 j
                · have hbw_t : b_w = true := by
                    have hbw0 := hbw 0
                    rw [hpos] at hbw0
                    cases b_w <;> cases hx0 : X 0 j <;> simp [hx0] at hbw0 ⊢
                  subst hbw_t
                  rw [if_pos hpos, hbw l]
                  simp only [ite_true]
                  change (run D.gates log).getD j.val false = X l j
                  rw [hspecD.1 j.val (by rw [hlog_len]; have := j.isLt; omega)]
                  dsimp only [log]
                  rw [getD_append_left' _ _ _ _ (by simp; omega), getD_append_left' _ _ _ _ (by simp [j.isLt])]
                  simp [j.isLt]
                · have hbw_f : b_w = false := by
                    have hbw0 := hbw 0
                    cases b_w
                    · rfl
                    · simp only [ite_true] at hbw0; exact absurd hbw0 hpos
                  subst hbw_f
                  rw [if_neg hpos, hbw l]
                  simp only [Bool.false_eq_true, ite_false]
                  by_cases hcond : X 0 j = true ∧ X (Fin.last n) j = false
                  · rw [if_pos hcond]
                    change (run D.gates log).getD (d + j.val) false = !(X l j)
                    rw [hspecD.1 (d + j.val) (by rw [hlog_len]; have := j.isLt; omega)]
                    dsimp only [log]
                    have hlt_app : d + j.val < (List.ofFn (X l) ++ List.ofFn (fun j =>
                        if X 0 j = true ∧ X (Fin.last n) j = false then !(X l j) else false)).length := by simp
                    rw [getD_append_left' _ _ _ _ hlt_app, getD_append_right' _ _ _ _ (by simp)]
                    simp [j.isLt, hcond.1, hcond.2]
                  · rw [if_neg hcond]
                    exact hneg_eval j (hneg_mem_of_neg j w hjw hpos hcond)
    change wireVal D log (wmap (out t)) = W t l
    rw [← hout_eval l t]
    exact hD_eval_all (out t) (hout_closed t)

end Backward

end PEqualNP.Outside.L_lib_1383_aux

theorem PEqualNP.Outside.L_lib_1383 : (∀ (n d a b : Nat) (color : Fin n → Fin d) (X : Fin (n+1) → Fin d → Bool)
    (W : Fin (a+1) → Fin (n+1) → Bool),
  0 < d → Function.Surjective color →
  (∀ i j, (X i.castSucc j ≠ X i.succ j) ↔ color i = j) →
  (∀ i : Fin n, W 0 i.castSucc ≠ W 0 i.succ) →
  (∀ t (i j : Fin n), color i = color j →
    ((W t i.castSucc ≠ W t i.succ) ↔ (W t j.castSucc ≠ W t j.succ))) →
  let neg := PEqualNP.NotBracket.notCount
  let valid := fun (h p k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
    C.output < h+2+C.size ∧ C.size-neg C ≤ p ∧ neg C ≤ k
  let actual := fun (l : Fin (n+1)) =>
    List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true]
  let logical := fun (l : Fin (n+1)) =>
    List.ofFn (X l) ++ List.ofFn (fun j => if X 0 j = true ∧ X (Fin.last n) j = false
      then !(X l j) else false) ++ [false,true]
  let falls := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    X i.castSucc (color i) = true ∧ X i.succ (color i) = false)).card
  (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin d → Nat) (out : Fin (a+1) → Nat),
    valid n (n-1) b C ∧ (∀ j, tap j < n+2+C.size) ∧ (∀ t, out t < n+2+C.size) ∧
    (∀ l j, (C.wires (actual l)).getD (tap j) false = X l j) ∧
    ∀ l t, (C.wires (actual l)).getD (out t) false = W t l) ↔
  ∃ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (a+1) → Nat),
    falls+k ≤ b ∧ valid (2*d) (d-1) k D ∧ (∀ t, out t < 2*d+2+D.size) ∧
    ∀ l t, (D.wires (logical l)).getD (out t) false = W t l) := by
  intro n d a b color X W hd hsurj hX hW0 hW
  dsimp only
  constructor
  · rintro ⟨C, tap, out, ⟨hfanC, hRBC, houtC, hposC, hnegC⟩, htap_lt, hout_lt, htap_eval, hout_eval⟩
    obtain ⟨k, D, out', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      PEqualNP.Outside.L_lib_1383_aux.lhs_to_rhs n d a b color X W hd hsurj hX hW0 hW
        C tap out hfanC hRBC houtC hposC hnegC htap_lt hout_lt htap_eval hout_eval
    exact ⟨k, D, out', h1, ⟨h2, h3, h4, h5, h6⟩, h7, h8⟩
  · rintro ⟨k, D, out, hfb, ⟨hfanD, hRBD, houtD_lt, hposD, hnegD⟩, hout_lt, hout_eval⟩
    exact PEqualNP.Outside.L_lib_1383_aux.rhs_to_lhs n d a b color X W hd hsurj hX
      k D out hfb hfanD hRBD houtD_lt hposD hnegD hout_lt hout_eval
