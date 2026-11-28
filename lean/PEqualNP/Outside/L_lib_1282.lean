import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

private local instance : DecidableEq GateOp := fun a b => by
  cases a with
  | and => cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
  | or => cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
  | not => cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
  | maj => cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
  | mod m1 =>
    cases b with
    | mod m2 => exact if h : m1 = m2 then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
    | _ => exact isFalse (by intro h; cases h)

private lemma mem_of_mem_set {α : Type} {l : List α} {k : ℕ} {v x : α} (h : x ∈ l.set k v) :
    x = v ∨ x ∈ l := by
  rw [List.mem_iff_getElem] at h
  rcases h with ⟨i, hi, rfl⟩
  rw [List.length_set] at hi
  by_cases hik : i = k
  · left; subst hik; simp
  · right; rw [List.getElem_set_ne (Ne.symm hik)]; exact List.getElem_mem hi

private def Valid (m : ℕ) (gs : List Gate) : Prop :=
  FanInTwo ⟨gs, 0⟩ ∧ ReadsBack m ⟨gs, 0⟩

private def evalW (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ x).getD w false

private lemma wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x =
    Circuit.wires ⟨gs₂, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    have : (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gs).length =
        x.length + gs.length := ih
    omega

private lemma evalW_of_prefix {gs₁ gs₂ : List Gate} (hpre : gs₁ <+: gs₂) (x : List Bool) {w : ℕ}
    (hw : w < x.length + gs₁.length) :
    evalW gs₂ x w = evalW gs₁ x w := by
  rcases hpre with ⟨suf, rfl⟩
  simp only [evalW, wires_append]
  induction suf using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton suf g ih =>
    let cur := Circuit.wires ⟨suf, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x)
    have hlen : w < cur.length := by simp only [cur, wires_length]; omega
    have hstep : Circuit.wires ⟨suf ++ [g], 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) =
        cur ++ [g.op.eval (g.inputs.map fun i => cur.getD i false)] := by
      simp [cur, Circuit.wires, List.foldl_append]
    rw [hstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private lemma evalW_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    evalW (gs ++ [g]) x (x.length + gs.length) =
    g.op.eval (g.inputs.map (evalW gs x)) := by
  let cur := Circuit.wires ⟨gs, 0⟩ x
  have hlen : cur.length = x.length + gs.length := wires_length gs x
  have hstep : Circuit.wires ⟨gs ++ [g], 0⟩ x =
      cur ++ [g.op.eval (g.inputs.map fun i => cur.getD i false)] := by
    simp [cur, Circuit.wires, List.foldl_append]
  simp only [evalW, hstep]
  rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _)]
  simp [cur]
  rfl

private lemma valid_snoc {m : ℕ} {gs : List Gate} (hv : Valid m gs) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < m + gs.length) :
    Valid m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hv.1 g' h1
    · simp only [List.mem_singleton] at h2; subst h2; exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    simp only [gateAt, List.getD_eq_getElem?_getD] at hi
    by_cases hlt : j < gs.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hv.2 j hlt i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
    · have heq : j = gs.length := by omega
      subst heq
      rw [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some] at hi
      exact hin i hi

private lemma notCount_snoc (gs : List Gate) (g : Gate) :
    notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ + if g.op = GateOp.not then 1 else 0 := by
  simp only [notCount, List.filter_append, List.length_append]
  cases h : g.op <;> simp [h]

private def addAnd (m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], m + gs.length)

private def addOr (m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], m + gs.length)

private def addNot (m : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], m + gs.length)

private lemma addAnd_spec {m : ℕ} {gs : List Gate} {a b : ℕ}
    (hv : Valid m gs) (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let res := addAnd m gs a b
    gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs.length + 1 ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ res.2 < m + res.1.length ∧
    ∀ x : List Bool, x.length = m → evalW res.1 x res.2 = (evalW gs x a && evalW gs x b) := by
  refine ⟨List.prefix_append _ _, ?_, by simp [addAnd], ?_, by simp [addAnd], ?_⟩
  · exact valid_snoc hv _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  · simp [addAnd, notCount_snoc]
  · intro x hx
    simp only [addAnd, ← hx, evalW_snoc_last, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true]

private lemma addOr_spec {m : ℕ} {gs : List Gate} {a b : ℕ}
    (hv : Valid m gs) (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let res := addOr m gs a b
    gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs.length + 1 ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ res.2 < m + res.1.length ∧
    ∀ x : List Bool, x.length = m → evalW res.1 x res.2 = (evalW gs x a || evalW gs x b) := by
  refine ⟨List.prefix_append _ _, ?_, by simp [addOr], ?_, by simp [addOr], ?_⟩
  · exact valid_snoc hv _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  · simp [addOr, notCount_snoc]
  · intro x hx
    simp only [addOr, ← hx, evalW_snoc_last, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false]

private lemma addNot_spec {m : ℕ} {gs : List Gate} {a : ℕ}
    (hv : Valid m gs) (ha : a < m + gs.length) :
    let res := addNot m gs a
    gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs.length + 1 ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧ res.2 < m + res.1.length ∧
    ∀ x : List Bool, x.length = m → evalW res.1 x res.2 = !(evalW gs x a) := by
  refine ⟨List.prefix_append _ _, ?_, by simp [addNot], ?_, by simp [addNot], ?_⟩
  · exact valid_snoc hv _ (by simp) (by simp) (by intro i hi; simp at hi; subst hi; omega)
  · simp [addNot, notCount_snoc]
  · intro x hx
    simp only [addNot, ← hx, evalW_snoc_last, GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons]

private def addOrList (m : ℕ) (wFalse : ℕ) : List ℕ → List Gate → List Gate × ℕ
  | [], gs => (gs, wFalse)
  | w :: ws, gs =>
    let r1 := addOrList m wFalse ws gs
    addOr m r1.1 w r1.2

private lemma addOrList_spec (m wFalse : ℕ) (ws : List ℕ) (gs : List Gate)
    (hv : Valid m gs) (hF : wFalse < m + gs.length) (hws : ∀ w ∈ ws, w < m + gs.length) :
    let res := addOrList m wFalse ws gs
    gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs.length + ws.length ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ res.2 < m + res.1.length ∧
    ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
      evalW res.1 x res.2 = ws.any (evalW gs x) := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨List.prefix_refl _, hv, by simp [addOrList], rfl, hF, ?_⟩
    intro x _ hFval
    simpa [addOrList] using hFval
  | cons w ws ih =>
    have hws' : ∀ u ∈ ws, u < m + gs.length := fun u hu => hws u (List.mem_cons_of_mem w hu)
    have hw : w < m + gs.length := hws w List.mem_cons_self
    obtain ⟨hpre1, hv1, hlen1, hnot1, hlt1, heval1⟩ := ih gs hv hF hws'
    have hw1 : w < m + (addOrList m wFalse ws gs).1.length := by omega
    obtain ⟨hpre2, hv2, hlen2, hnot2, hlt2, heval2⟩ := addOr_spec hv1 hw1 hlt1
    refine ⟨hpre1.trans hpre2, hv2, by simp [addOrList, hlen2, hlen1]; omega,
      by simp [addOrList, hnot2, hnot1], hlt2, ?_⟩
    intro x hx hFval
    change evalW (addOr m (addOrList m wFalse ws gs).1 w (addOrList m wFalse ws gs).2).1 x
      (addOr m (addOrList m wFalse ws gs).1 w (addOrList m wFalse ws gs).2).2 = _
    rw [heval2 x hx, evalW_of_prefix hpre1 x (by omega), heval1 x hx hFval]
    simp

private lemma foldl_range_spec {m : ℕ} (k : ℕ)
    (step : List Gate × List ℕ → ℕ → List Gate × List ℕ)
    (cost : ℕ) (P : ℕ → List Gate → ℕ → Prop)
    (gs₀ : List Gate) (hv₀ : Valid m gs₀)
    (hstep : ∀ (i : ℕ) (hi : i < k) (gs : List Gate) (acc : List ℕ),
      gs₀ <+: gs → Valid m gs →
      let r := step (gs, acc) i
      gs <+: r.1 ∧ Valid m r.1 ∧ r.1.length = gs.length + cost ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∃ w, r.2 = acc ++ [w] ∧ w < m + r.1.length ∧ P i r.1 w)
    (hP_mono : ∀ i gs₁ gs₂ w, gs₁ <+: gs₂ → w < m + gs₁.length → P i gs₁ w → P i gs₂ w) :
    let res := (List.range k).foldl step (gs₀, [])
    gs₀ <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs₀.length + k * cost ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs₀, 0⟩ ∧ res.2.length = k ∧
    (∀ w ∈ res.2, w < m + res.1.length) ∧
    (∀ i (hi : i < res.2.length), P i res.1 (res.2[i]'hi)) := by
  suffices hgen : ∀ j ≤ k,
      let res := (List.range j).foldl step (gs₀, [])
      gs₀ <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs₀.length + j * cost ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs₀, 0⟩ ∧ res.2.length = j ∧
      (∀ w ∈ res.2, w < m + res.1.length) ∧
      (∀ i (hi : i < res.2.length), P i res.1 (res.2[i]'hi)) by
    exact hgen k (le_refl k)
  intro j hj
  induction j with
  | zero =>
    refine ⟨List.prefix_refl _, hv₀, by simp, rfl, rfl, by simp, fun i hi => by simp at hi⟩
  | succ j ih =>
    obtain ⟨hpre, hv, hlen, hnot, hacc_len, hlt, hP⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cur := (List.range j).foldl step (gs₀, [])
    have hcur_eq : (cur.1, cur.2) = cur := rfl
    have hs := hstep j (by omega) cur.1 cur.2 hpre hv
    rw [hcur_eq] at hs
    obtain ⟨hpre', hv', hlen', hnot', w, hw_eq, hw_lt, hw_P⟩ := hs
    refine ⟨hpre.trans hpre', hv', by rw [hlen', hlen]; ring, by rw [hnot', hnot],
      by rw [hw_eq, List.length_append, List.length_singleton, hacc_len], ?_, ?_⟩
    · intro u hu
      rw [hw_eq, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu1 | rfl
      · have := hlt u hu1; omega
      · exact hw_lt
    · intro i hi
      have hlen_res : (step cur j).2.length = j + 1 := by
        rw [hw_eq, List.length_append, List.length_singleton, hacc_len]
      by_cases hij : i < j
      · have hget : (step cur j).2[i]'hi = cur.2[i]'(by omega) := by
          simp only [hw_eq, List.getElem_append_left (show i < cur.2.length by omega)]
        rw [hget]
        exact hP_mono i cur.1 (step cur j).1 _ hpre' (hlt _ (List.getElem_mem _)) (hP i (by omega))
      · have heq : i = j := by omega
        have hget : (step cur j).2[i]'hi = w := by
          simp only [hw_eq, List.getElem_append_right (show cur.2.length ≤ i by omega),
            hacc_len, show i - j = 0 by omega, List.getElem_cons_zero]
        rw [hget, heq]
        exact hw_P

private def IsSortedDesc : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (b = true → a = true) ∧ IsSortedDesc (b :: rest)

private lemma isSortedDesc_iff_getElem (l : List Bool) :
    IsSortedDesc l ↔ ∀ i j (hi : i < l.length) (hj : j < l.length), i ≤ j → l[j] = true → l[i] = true := by
  induction l with
  | nil => simp [IsSortedDesc]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [IsSortedDesc, List.length_singleton, true_iff]
      intro i j hi hj _ hj1
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0; subst hj0; exact hj1
    | cons b rest' =>
      simp only [IsSortedDesc]
      rw [ih]
      constructor
      · rintro ⟨hab, hrest⟩ i j hi hj hij hj1
        cases i with
        | zero =>
          cases j with
          | zero => exact hj1
          | succ j' =>
            have hb : (b :: rest')[0]'(by simp) = true :=
              hrest 0 j' (by simp) (by simpa using hj) (Nat.zero_le _) (by simpa using hj1)
            exact hab hb
        | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
            exact hrest i' j' (by simpa using hi) (by simpa using hj) (by omega) (by simpa using hj1)
      · intro h
        refine ⟨fun hb => h 0 1 (by simp) (by simp) (by omega) hb, ?_⟩
        intro i j hi hj hij hj1
        exact h (i + 1) (j + 1) (by simpa using hi) (by simpa using hj) (by omega) hj1

private def invertSorted (m wFalse : ℕ) : ℕ → List ℕ → List Gate → List Gate × List ℕ
  | 0, _, gs => (gs, [])
  | b + 1, ws, gs =>
    if ws.length = 0 then (gs, [])
    else
      let mid := ws.length / 2
      let wMid := ws.getD mid wFalse
      let r1 := addNot m gs wMid
      let nmid := r1.2
      let foldStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc i =>
        let wi := ws.getD i wFalse
        let wr := ws.getD (mid + 1 + i) wFalse
        let ra := addAnd m acc.1 wi nmid
        let ro := addOr m ra.1 ra.2 wr
        (ro.1, acc.2 ++ [ro.2])
      let r2 := (List.range mid).foldl foldStep (r1.1, [])
      let r3 := invertSorted m wFalse b r2.2 r2.1
      let nz := r3.2
      let leftStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc i =>
        let ra := addAnd m acc.1 (nz.getD i wFalse) nmid
        (ra.1, acc.2 ++ [ra.2])
      let r4 := (List.range mid).foldl leftStep (r3.1, [])
      let rightStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc j =>
        let ro := addOr m acc.1 (nz.getD j wFalse) nmid
        (ro.1, acc.2 ++ [ro.2])
      let r5 := (List.range (ws.length - 1 - mid)).foldl rightStep (r4.1, [])
      (r5.1, r4.2 ++ [nmid] ++ r5.2)

private lemma getD_mem_lt {m k : ℕ} {l : List ℕ} {d : ℕ}
    (hd : d < m + k) (hl : ∀ w ∈ l, w < m + k) (i : ℕ) :
    l.getD i d < m + k := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    exact hd

private lemma invertSorted_spec (m wFalse : ℕ) :
    ∀ (b : ℕ) (ws : List ℕ) (gs : List Gate),
      ws.length < 2 ^ b → Valid m gs → wFalse < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      let res := invertSorted m wFalse b ws gs
      gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length ≤ gs.length + 4 * ws.length ∧
      notCount ⟨res.1, 0⟩ ≤ notCount ⟨gs, 0⟩ + b ∧
      res.2.length = ws.length ∧
      (∀ w ∈ res.2, w < m + res.1.length) ∧
      ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
        IsSortedDesc (ws.map (evalW gs x)) →
        res.2.map (evalW res.1 x) = (ws.map (evalW gs x)).map Bool.not := by
  intro b
  induction b with
  | zero =>
    intro ws gs hlt hv _ _
    have h0 : ws.length = 0 := Nat.lt_one_iff.mp (by simpa using hlt)
    have hnil : ws = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    refine ⟨List.prefix_refl _, hv, by simp [invertSorted], by simp [invertSorted],
      rfl, by simp [invertSorted], fun _ _ _ _ => rfl⟩
  | succ b ih =>
    intro ws gs hlt hv hF hws
    by_cases h0 : ws.length = 0
    · have hnil : ws = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil
      refine ⟨List.prefix_refl _, hv, by simp [invertSorted], by simp [invertSorted],
        rfl, by simp [invertSorted], fun _ _ _ _ => rfl⟩
    · simp only [invertSorted, if_neg h0]
      set mid := ws.length / 2
      have hmid_lt : mid < ws.length := by omega
      have hmid_pow : mid < 2 ^ b := by rw [pow_succ] at hlt; omega
      have hright_le : ws.length - 1 - mid ≤ mid := by omega
      let wMid := ws.getD mid wFalse
      have hwMid_eq : wMid = ws[mid]'hmid_lt := by
        simp [wMid, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmid_lt]
      have hwMid_lt : wMid < m + gs.length := hwMid_eq ▸ hws _ (List.getElem_mem hmid_lt)
      obtain ⟨hpre1, hv1, hlen1, hnot1, hnmid_lt, heval1⟩ := addNot_spec hv hwMid_lt
      set r1 := addNot m gs wMid

      let foldStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc i =>
        let wi := ws.getD i wFalse
        let wr := ws.getD (mid + 1 + i) wFalse
        let ra := addAnd m acc.1 wi r1.2
        let ro := addOr m ra.1 ra.2 wr
        (ro.1, acc.2 ++ [ro.2])
      let Pz : ℕ → List Gate → ℕ → Prop := fun i gs' w =>
        ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
          evalW gs' x w = ((evalW gs x (ws.getD i wFalse) && !(evalW gs x wMid)) ||
            evalW gs x (ws.getD (mid + 1 + i) wFalse))
      have hfold := foldl_range_spec mid foldStep 2 Pz r1.1 hv1 (by
        intro i _ gs' acc hpre' hv'
        have hlen_le : r1.1.length ≤ gs'.length := hpre'.length_le
        have hwi : ws.getD i wFalse < m + gs'.length :=
          lt_of_lt_of_le (getD_mem_lt hF hws i) (by omega)
        have hwr : ws.getD (mid + 1 + i) wFalse < m + gs'.length :=
          lt_of_lt_of_le (getD_mem_lt hF hws (mid + 1 + i)) (by omega)
        have hnmid' : r1.2 < m + gs'.length := by omega
        obtain ⟨hpa, hva, hla, hna, hwa, hea⟩ := addAnd_spec hv' hwi hnmid'
        have hwr' : ws.getD (mid + 1 + i) wFalse < m + (addAnd m gs' (ws.getD i wFalse) r1.2).1.length := by omega
        obtain ⟨hpo, hvo, hlo, hno, hwo, heo⟩ := addOr_spec hva hwa hwr'
        refine ⟨hpa.trans hpo, hvo, by simp only [foldStep]; omega,
          by simp only [foldStep]; rw [hno, hna],
          (addOr m (addAnd m gs' (ws.getD i wFalse) r1.2).1 (addAnd m gs' (ws.getD i wFalse) r1.2).2 (ws.getD (mid + 1 + i) wFalse)).2,
          rfl, hwo, ?_⟩
        intro x hx _
        rw [heo x hx, hea x hx]
        have h1 : evalW gs' x (ws.getD i wFalse) = evalW gs x (ws.getD i wFalse) :=
          evalW_of_prefix (hpre1.trans hpre') x (by rw [hx]; exact getD_mem_lt hF hws i)
        have h2 : evalW gs' x r1.2 = !(evalW gs x wMid) := by
          rw [evalW_of_prefix hpre' x (by rw [hx]; exact hnmid_lt), heval1 x hx]
        have h3 : evalW (addAnd m gs' (ws.getD i wFalse) r1.2).1 x (ws.getD (mid + 1 + i) wFalse) =
            evalW gs x (ws.getD (mid + 1 + i) wFalse) :=
          evalW_of_prefix ((hpre1.trans hpre').trans hpa) x (by rw [hx]; exact getD_mem_lt hF hws (mid + 1 + i))
        rw [h1, h2, h3]) (by
        intro i gs₁ gs₂ w hpre hw hP x hx hFv
        rw [evalW_of_prefix hpre x (by rw [hx]; exact hw), hP x hx hFv])
      obtain ⟨hpre2, hv2, hlen2, hnot2, hr2_len, hr2_lt, hr2_P⟩ := hfold
      set r2 := (List.range mid).foldl foldStep (r1.1, [])
      have hF2 : wFalse < m + r2.1.length := by omega

      obtain ⟨hpre3, hv3, hlen3, hnot3, hr3_len, hr3_lt, hr3_eval⟩ :=
        ih r2.2 r2.1 (by omega) hv2 hF2 hr2_lt
      set r3 := invertSorted m wFalse b r2.2 r2.1
      have hpre13 : gs <+: r3.1 := (hpre1.trans hpre2).trans hpre3
      have hlen13 : r1.1.length ≤ r3.1.length := (hpre2.trans hpre3).length_le
      have hF3 : wFalse < m + r3.1.length := by omega

      let leftStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc i =>
        let ra := addAnd m acc.1 (r3.2.getD i wFalse) r1.2
        (ra.1, acc.2 ++ [ra.2])
      let PL : ℕ → List Gate → ℕ → Prop := fun i gs' w =>
        ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
          evalW gs' x w = (evalW r3.1 x (r3.2.getD i wFalse) && !(evalW gs x wMid))
      have hleft := foldl_range_spec mid leftStep 1 PL r3.1 hv3 (by
        intro i _ gs' acc hpre' hv'
        have hlen_le : r3.1.length ≤ gs'.length := hpre'.length_le
        have hnz : r3.2.getD i wFalse < m + gs'.length :=
          lt_of_lt_of_le (getD_mem_lt hF3 hr3_lt i) (by omega)
        have hnmid' : r1.2 < m + gs'.length := by omega
        obtain ⟨hpa, hva, hla, hna, hwa, hea⟩ := addAnd_spec hv' hnz hnmid'
        refine ⟨hpa, hva, by simp only [leftStep]; omega, hna,
          (addAnd m gs' (r3.2.getD i wFalse) r1.2).2, rfl, hwa, ?_⟩
        intro x hx _
        rw [hea x hx]
        have h1 : evalW gs' x (r3.2.getD i wFalse) = evalW r3.1 x (r3.2.getD i wFalse) :=
          evalW_of_prefix hpre' x (by rw [hx]; exact getD_mem_lt hF3 hr3_lt i)
        have h2 : evalW gs' x r1.2 = !(evalW gs x wMid) := by
          rw [evalW_of_prefix ((hpre2.trans hpre3).trans hpre') x (by rw [hx]; exact hnmid_lt), heval1 x hx]
        rw [h1, h2]) (by
        intro i gs₁ gs₂ w hpre hw hP x hx hFv
        rw [evalW_of_prefix hpre x (by rw [hx]; exact hw), hP x hx hFv])
      obtain ⟨hpre4, hv4, hlen4, hnot4, hr4_len, hr4_lt, hr4_P⟩ := hleft
      set r4 := (List.range mid).foldl leftStep (r3.1, [])

      let rightStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc j =>
        let ro := addOr m acc.1 (r3.2.getD j wFalse) r1.2
        (ro.1, acc.2 ++ [ro.2])
      let PR : ℕ → List Gate → ℕ → Prop := fun j gs' w =>
        ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
          evalW gs' x w = (evalW r3.1 x (r3.2.getD j wFalse) || !(evalW gs x wMid))
      have hright := foldl_range_spec (ws.length - 1 - mid) rightStep 1 PR r4.1 hv4 (by
        intro j _ gs' acc hpre' hv'
        have hlen_le : r4.1.length ≤ gs'.length := hpre'.length_le
        have hlen34 : r3.1.length ≤ r4.1.length := hpre4.length_le
        have hnz : r3.2.getD j wFalse < m + gs'.length :=
          lt_of_lt_of_le (getD_mem_lt hF3 hr3_lt j) (by omega)
        have hnmid' : r1.2 < m + gs'.length := by omega
        obtain ⟨hpo, hvo, hlo, hno, hwo, heo⟩ := addOr_spec hv' hnz hnmid'
        refine ⟨hpo, hvo, by simp only [rightStep]; omega, hno,
          (addOr m gs' (r3.2.getD j wFalse) r1.2).2, rfl, hwo, ?_⟩
        intro x hx _
        rw [heo x hx]
        have h1 : evalW gs' x (r3.2.getD j wFalse) = evalW r3.1 x (r3.2.getD j wFalse) :=
          evalW_of_prefix (hpre4.trans hpre') x (by rw [hx]; exact getD_mem_lt hF3 hr3_lt j)
        have h2 : evalW gs' x r1.2 = !(evalW gs x wMid) := by
          rw [evalW_of_prefix (((hpre2.trans hpre3).trans hpre4).trans hpre') x (by rw [hx]; exact hnmid_lt), heval1 x hx]
        rw [h1, h2]) (by
        intro j gs₁ gs₂ w hpre hw hP x hx hFv
        rw [evalW_of_prefix hpre x (by rw [hx]; exact hw), hP x hx hFv])
      obtain ⟨hpre5, hv5, hlen5, hnot5, hr5_len, hr5_lt, hr5_P⟩ := hright
      set r5 := (List.range (ws.length - 1 - mid)).foldl rightStep (r4.1, [])
      refine ⟨(hpre13.trans hpre4).trans hpre5, hv5, ?_, ?_, ?_, ?_, ?_⟩
      ·

        omega
      · omega
      · simp only [List.length_append, List.length_singleton, hr4_len, hr5_len]; omega
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        have hlen45 : r4.1.length ≤ r5.1.length := hpre5.length_le
        have hlen15 : r1.1.length ≤ r5.1.length := ((hpre2.trans hpre3).trans hpre4).trans hpre5 |>.length_le
        rcases hw with (hw4 | rfl) | hw5
        · have := hr4_lt w hw4; omega
        · omega
        · exact hr5_lt w hw5
      · intro x hx hFv hsort

        have hsort_idx := (isSortedDesc_iff_getElem (ws.map (evalW gs x))).mp hsort
        have hz_eval : ∀ i (hi : i < mid),
            evalW r2.1 x (r2.2[i]'(by omega)) =
            if evalW gs x wMid = true then evalW gs x (ws.getD (mid + 1 + i) wFalse)
            else evalW gs x (ws.getD i wFalse) := by
          intro i hi
          rw [hr2_P i (by omega) x hx hFv]
          cases hmid_v : evalW gs x wMid with
          | true =>
            simp only [Bool.not_true, Bool.and_false, Bool.false_or, ↓reduceIte]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
            have hwr_false : evalW gs x (ws.getD (mid + 1 + i) wFalse) = false := by
              by_cases hlt_r : mid + 1 + i < ws.length
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_r, Option.getD_some]
                by_contra htrue
                have ht : evalW gs x (ws[mid + 1 + i]'hlt_r) = true := by
                  cases hv : evalW gs x (ws[mid + 1 + i]'hlt_r) <;> simp_all
                have hmid_t := hsort_idx mid (mid + 1 + i) (by simp; omega) (by simp; omega) (by omega)
                  (by simpa using ht)
                simp only [List.getElem_map] at hmid_t
                rw [← hwMid_eq, hmid_v] at hmid_t
                cases hmid_t
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, hFv]
            rw [hwr_false, Bool.or_false]
        have hz_sorted : IsSortedDesc (r2.2.map (evalW r2.1 x)) := by
          rw [isSortedDesc_iff_getElem]
          intro i j hi hj hij hj1
          simp only [List.length_map, hr2_len] at hi hj
          simp only [List.getElem_map] at hj1 ⊢
          rw [hz_eval i hi]
          rw [hz_eval j hj] at hj1
          split_ifs at hj1 ⊢ with hmid_v
          · by_cases hjr : mid + 1 + j < ws.length
            · have hir : mid + 1 + i < ws.length := by omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some] at hj1
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir, Option.getD_some]
              have := hsort_idx (mid + 1 + i) (mid + 1 + j) (by simp; omega) (by simp; omega) (by omega)
                (by simpa using hj1)
              simpa using this
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, hFv] at hj1
              cases hj1
          · have hir : i < ws.length := by omega
            have hjr : j < ws.length := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some] at hj1
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir, Option.getD_some]
            have := hsort_idx i j (by simp; omega) (by simp; omega) hij (by simpa using hj1)
            simpa using this
        have hF2v : evalW r2.1 x wFalse = false := by
          rw [evalW_of_prefix (hpre1.trans hpre2) x (by rw [hx]; exact hF), hFv]
        have hnz_eq := hr3_eval x hx hF2v hz_sorted
        have hnz_get : ∀ i (hi : i < mid),
            evalW r3.1 x (r3.2.getD i wFalse) =
            !(if evalW gs x wMid = true then evalW gs x (ws.getD (mid + 1 + i) wFalse)
              else evalW gs x (ws.getD i wFalse)) := by
          intro i hi
          have hi3 : i < r3.2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi3, Option.getD_some]
          have hget := congrArg (fun l => l[i]?) hnz_eq
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi3,
            List.getElem?_eq_getElem (show i < r2.2.length by omega), Option.map_some, Option.some.injEq] at hget
          rw [hget, hz_eval i hi]

        apply List.ext_getElem
        · simp only [List.length_map, List.length_append, List.length_singleton, hr4_len, hr5_len]; omega
        · intro idx hidx1 hidx2
          simp only [List.length_map] at hidx2
          simp only [List.getElem_map]
          by_cases hlt_mid : idx < mid
          · have hget_l : (r4.2 ++ [r1.2] ++ r5.2)[idx]'(by simp [hr4_len, hr5_len]; omega) =
                r4.2[idx]'(by omega) := by
              rw [List.getElem_append_left (by simp [hr4_len]; omega), List.getElem_append_left (by omega)]
            rw [hget_l, evalW_of_prefix hpre5 x (by rw [hx]; exact hr4_lt _ (List.getElem_mem _)),
              hr4_P idx (by omega) x hx hFv, hnz_get idx hlt_mid]
            cases hmid_v : evalW gs x wMid with
            | true =>
              simp only [Bool.not_true, Bool.and_false]
              have hidx_t := hsort_idx idx mid (by simp; omega) (by simp; omega) (by omega)
                (by simp [← hwMid_eq, hmid_v])
              simp only [List.getElem_map] at hidx_t
              rw [hidx_t]; rfl
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx2, Option.getD_some]
          · by_cases heq_mid : idx = mid
            · subst heq_mid
              have hget_m : (r4.2 ++ [r1.2] ++ r5.2)[mid]'(by simp [hr4_len]) = r1.2 := by
                rw [List.getElem_append_left (by simp [hr4_len]), List.getElem_append_right (by omega)]
                simp [hr4_len]
              rw [hget_m, evalW_of_prefix (((hpre2.trans hpre3).trans hpre4).trans hpre5) x (by rw [hx]; exact hnmid_lt),
                heval1 x hx, hwMid_eq]
            · have hgt_mid : mid < idx := by omega
              let j := idx - mid - 1
              have hj_lt : j < ws.length - 1 - mid := by omega
              have hget_r : (r4.2 ++ [r1.2] ++ r5.2)[idx]'(by simp [hr4_len, hr5_len]; omega) =
                  r5.2[j]'(by omega) := by
                rw [List.getElem_append_right (by simp [hr4_len]; omega)]
                have hsub : idx - (r4.2 ++ [r1.2]).length = j := by simp [hr4_len, j]; omega
                simp only [hsub]
              rw [hget_r, hr5_P j (by omega) x hx hFv, hnz_get j (by omega)]
              have hidx_eq : mid + 1 + j = idx := by omega
              cases hmid_v : evalW gs x wMid with
              | true =>
                simp only [↓reduceIte, Bool.not_true, Bool.or_false, hidx_eq]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx2, Option.getD_some]
              | false =>
                simp only [Bool.not_false, Bool.or_true]
                have hidx_f : evalW gs x (ws[idx]'hidx2) = false := by
                  by_contra ht
                  have htr : evalW gs x (ws[idx]'hidx2) = true := by
                    cases hv : evalW gs x (ws[idx]'hidx2) <;> simp_all
                  have hmid_t := hsort_idx mid idx (by simp; omega) (by simp; omega) (by omega) (by simpa using htr)
                  simp only [List.getElem_map] at hmid_t
                  rw [← hwMid_eq, hmid_v] at hmid_t
                  cases hmid_t
                rw [hidx_f]; rfl

private def applyBoolComp (j : ℕ) (l : List Bool) : List Bool :=
  if hj : j + 1 < l.length then
    let a := l[j]'(by omega)
    let b := l[j + 1]'hj
    (l.set j (a || b)).set (j + 1) (a && b)
  else l

private def applyBoolComps : List ℕ → List Bool → List Bool
  | [], l => l
  | j :: rest, l => applyBoolComps rest (applyBoolComp j l)

private lemma applyBoolComp_length (j : ℕ) (l : List Bool) :
    (applyBoolComp j l).length = l.length := by
  unfold applyBoolComp
  split_ifs <;> simp

private lemma applyBoolComps_length (cs : List ℕ) (l : List Bool) :
    (applyBoolComps cs l).length = l.length := by
  induction cs generalizing l with
  | nil => rfl
  | cons j rest ih => simp only [applyBoolComps, ih, applyBoolComp_length]

private lemma applyBoolComps_append (cs₁ cs₂ : List ℕ) (l : List Bool) :
    applyBoolComps (cs₁ ++ cs₂) l = applyBoolComps cs₂ (applyBoolComps cs₁ l) := by
  induction cs₁ generalizing l with
  | nil => rfl
  | cons j rest ih => simp only [List.cons_append, applyBoolComps, ih]

private def bubbleComps (k : ℕ) : List ℕ :=
  (List.replicate k (List.range (k - 1))).flatten

private lemma bubbleComps_length (k : ℕ) : (bubbleComps k).length ≤ k * k := by
  simp only [bubbleComps, List.length_flatten, List.map_replicate, List.length_range,
    List.sum_replicate, smul_eq_mul]
  exact Nat.mul_le_mul_left k (Nat.sub_le k 1)

private lemma bubble_pass_spec (k : ℕ) (l : List Bool) (hl : l.length = k + 1) :
    (applyBoolComps (List.range k) l).length = k + 1 ∧
    ((∀ i (hi : i < k + 1), l[i]'(by omega) = true) →
      applyBoolComps (List.range k) l = l) ∧
    ((∃ i, ∃ hi : i < k + 1, l[i]'(by omega) = false) →
      (applyBoolComps (List.range k) l)[k]'(by rw [applyBoolComps_length, hl]; omega) = false) := by

  induction k generalizing l with
  | zero =>
    refine ⟨by simpa [applyBoolComps] using hl, fun _ => rfl, ?_⟩
    rintro ⟨i, hi, hfi⟩
    have : i = 0 := by omega
    subst this; simpa [applyBoolComps] using hfi
  | succ k ih =>

    simp only [List.range_succ, applyBoolComps_append]

    have hsplit : l = l.take (k + 1) ++ [l[k + 1]'(by omega)] := by
      have h1 := List.take_append_drop (k + 1) l
      have hdrop : l.drop (k + 1) = [l[k + 1]'(by omega)] := by
        apply List.ext_getElem
        · simp [hl]
        · intro idx h1 h2
          simp only [List.length_singleton] at h2
          have : idx = 0 := by omega
          subst this; simp
      have h2 := h1.symm
      rw [hdrop] at h2
      exact h2
    have hpass_append : ∀ (cs : List ℕ) (p : List Bool) (v : Bool),
        (∀ c ∈ cs, c + 1 < p.length) →
        applyBoolComps cs (p ++ [v]) = applyBoolComps cs p ++ [v] := by
      intro cs
      induction cs with
      | nil => intros; rfl
      | cons c rest ihr =>
        intro p v hc
        have hc0 : c + 1 < p.length := hc c List.mem_cons_self
        have hcomp : applyBoolComp c (p ++ [v]) = applyBoolComp c p ++ [v] := by
          simp only [applyBoolComp, show c + 1 < (p ++ [v]).length by simp; omega,
            hc0, ↓reduceDIte]
          rw [List.getElem_append_left (by omega), List.getElem_append_left hc0,
            List.set_append_left _ _ (by omega), List.set_append_left _ _ (by simp; omega)]
        simp only [applyBoolComps, hcomp]
        exact ihr (applyBoolComp c p) v (fun c' hc' => by
          rw [applyBoolComp_length]; exact hc c' (List.mem_cons_of_mem c hc'))
    have htake_len : (l.take (k + 1)).length = k + 1 := List.length_take_of_le (by omega)
    have hpref_eq : applyBoolComps (List.range k) l =
        applyBoolComps (List.range k) (l.take (k + 1)) ++ [l[k + 1]'(by omega)] := by
      conv_lhs => rw [hsplit]
      exact hpass_append (List.range k) (l.take (k + 1)) (l[k + 1]'(by omega))
        (fun c hc => by rw [List.mem_range] at hc; omega)
    obtain ⟨hlen_p, hall_p, hfalse_p⟩ := ih (l.take (k + 1)) htake_len
    set p' := applyBoolComps (List.range k) (l.take (k + 1))
    set last := l[k + 1]'(by omega)
    have hlast_step : applyBoolComps [k] (p' ++ [last]) =
        ((p' ++ [last]).set k (p'[k]'(by omega) || last)).set (k + 1) (p'[k]'(by omega) && last) := by
      simp only [applyBoolComps, applyBoolComp, show k + 1 < (p' ++ [last]).length by simp [hlen_p],
        ↓reduceDIte]
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      simp [hlen_p]
    refine ⟨by rw [hpref_eq, applyBoolComps_length]; simp [hlen_p], ?_, ?_⟩
    · intro hall
      have hp_all : ∀ i (hi : i < k + 1), (l.take (k + 1))[i]'(by omega) = true := by
        intro i hi; rw [List.getElem_take]; exact hall i (by omega)
      have hp'_eq : p' = l.take (k + 1) := hall_p hp_all
      have hlast_t : last = true := hall (k + 1) (by omega)
      have hpk_t : p'[k]'(by omega) = true := by
        simp only [hp'_eq, List.getElem_take]; exact hall k (by omega)
      rw [hpref_eq, hlast_step, hlast_t, hpk_t]
      simp only [Bool.or_true, Bool.and_true]
      apply List.ext_getElem
      · simp [hlen_p, hl]
      · intro i hi1 hi2
        by_cases h1 : i = k + 1
        · subst h1; simp [hlen_p, hall (k + 1) (by omega)]
        · rw [List.getElem_set_ne (by omega)]
          by_cases h2 : i = k
          · subst i; simp [hlen_p, hall k (by omega)]
          · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by omega)]
            simp [hp'_eq, List.getElem_take]
    · rintro ⟨i, hi, hfi⟩
      simp only [hpref_eq, hlast_step]
      have hget_last : (((p' ++ [last]).set k (p'[k]'(by omega) || last)).set (k + 1) (p'[k]'(by omega) && last))[k + 1]'(by
          simp [hlen_p]) = (p'[k]'(by omega) && last) := by
        simp [hlen_p]
      rw [hget_last]
      by_cases hil : i = k + 1
      · subst hil; simp [last, hfi]
      · have hpf : p'[k]'(by omega) = false := hfalse_p ⟨i, by omega, by simpa [List.getElem_take] using hfi⟩
        simp [hpf]

private lemma bubbleComps_sorts (k : ℕ) (l : List Bool) (hl : l.length = k) :
    IsSortedDesc (applyBoolComps (bubbleComps k) l) := by

  suffices hgen : ∀ (k p : ℕ) (l : List Bool), l.length = k → k ≤ p →
      IsSortedDesc (applyBoolComps (List.replicate p (List.range (k - 1))).flatten l) by
    exact hgen k k l hl (le_refl k)
  intro k
  induction k with
  | zero =>
    intro p l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    have : applyBoolComps (List.replicate p (List.range 0)).flatten [] = [] := by
      simp [applyBoolComps]
    rw [this]; trivial
  | succ k ih =>
    intro p l hl hkp
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [List.replicate_succ, List.flatten_cons, applyBoolComps_append]
    simp only [Nat.add_sub_cancel]
    obtain ⟨hlen1, hall1, hfalse1⟩ := bubble_pass_spec k l hl
    set l1 := applyBoolComps (List.range k) l
    by_cases hall : ∀ i (hi : i < k + 1), l[i]'(by omega) = true
    ·
      have hstay : ∀ (cs : List ℕ) (u : List Bool),
          (∀ i (hi : i < u.length), u[i]'hi = true) →
          ∀ i (hi : i < (applyBoolComps cs u).length), (applyBoolComps cs u)[i]'hi = true := by
        intro cs
        induction cs with
        | nil => intro u hu; exact hu
        | cons c rest ihr =>
          intro u hu
          apply ihr
          intro i hi
          rw [applyBoolComp_length] at hi
          simp only [applyBoolComp]
          split_ifs with hc
          · by_cases h1 : i = c + 1
            · subst i; simp [hu c (by omega), hu (c + 1) hc]
            · rw [List.getElem_set_ne (by omega)]
              by_cases h2 : i = c
              · subst i; simp [hu c (by omega), hu (c + 1) hc]
              · rw [List.getElem_set_ne (by omega)]; exact hu i hi
          · exact hu i hi
      have hall_fin := hstay (List.replicate p' (List.range k)).flatten l1
        (by rw [hall1 hall]; intro i hi; exact hall i (by omega))
      rw [isSortedDesc_iff_getElem]
      intro i _ hi _ _ _
      exact hall_fin i hi
    · push_neg at hall
      obtain ⟨i₀, hi₀, hne⟩ := hall
      have hfi₀ : l[i₀]'(by omega) = false := by
        cases hv : l[i₀]'(by omega) <;> simp_all
      have hlast_f : l1[k]'(by omega) = false := hfalse1 ⟨i₀, hi₀, hfi₀⟩

      have hpass_false : ∀ (u : List Bool), u.length = k →
          applyBoolComps (List.range k) (u ++ [false]) =
          applyBoolComps (List.range (k - 1)) u ++ [false] := by
        intro u hu
        cases k with
        | zero =>
          have : u = [] := List.eq_nil_of_length_eq_zero hu
          subst this; rfl
        | succ k' =>
          simp only [Nat.add_sub_cancel]
          simp only [List.range_succ, applyBoolComps_append]
          have hpass_app : ∀ (cs : List ℕ) (q : List Bool),
              (∀ c ∈ cs, c + 1 < q.length) →
              applyBoolComps cs (q ++ [false]) = applyBoolComps cs q ++ [false] := by
            intro cs
            induction cs with
            | nil => intros; rfl
            | cons c rest ihr =>
              intro q hc
              have hc0 : c + 1 < q.length := hc c List.mem_cons_self
              have hcomp : applyBoolComp c (q ++ [false]) = applyBoolComp c q ++ [false] := by
                simp only [applyBoolComp, show c + 1 < (q ++ [false]).length by simp; omega, hc0, ↓reduceDIte]
                rw [List.getElem_append_left (by omega), List.getElem_append_left hc0,
                  List.set_append_left _ _ (by omega), List.set_append_left _ _ (by simp; omega)]
              simp only [applyBoolComps, hcomp]
              exact ihr (applyBoolComp c q) (fun c' hc' => by
                rw [applyBoolComp_length]; exact hc c' (List.mem_cons_of_mem c hc'))
          rw [hpass_app (List.range k') u (fun c hc => by rw [List.mem_range] at hc; omega)]
          set u' := applyBoolComps (List.range k') u
          have hu' : u'.length = k' + 1 := by rw [applyBoolComps_length, hu]
          simp only [applyBoolComps, applyBoolComp, show k' + 1 < (u' ++ [false]).length by simp [hu'],
            ↓reduceDIte]
          rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
          simp only [hu', Nat.sub_self, List.getElem_cons_zero, Bool.or_false, Bool.and_false]
          apply List.ext_getElem
          · simp [hu']
          · intro idx h1 h2
            by_cases hlast : idx = k' + 1
            · subst hlast; simp [hu']
            · rw [List.getElem_set_ne (by omega)]
              by_cases hk' : idx = k'
              · subst hk'; simp [hu']
              · rw [List.getElem_set_ne (by omega)]
      have hrep_false : ∀ (r : ℕ) (u : List Bool), u.length = k →
          applyBoolComps (List.replicate r (List.range k)).flatten (u ++ [false]) =
          applyBoolComps (List.replicate r (List.range (k - 1))).flatten u ++ [false] := by
        intro r
        induction r with
        | zero => intros; rfl
        | succ r ihr =>
          intro u hu
          rw [List.replicate_succ, List.flatten_cons, applyBoolComps_append, hpass_false u hu,
            List.replicate_succ, List.flatten_cons, applyBoolComps_append]
          exact ihr _ (by rw [applyBoolComps_length, hu])
      have hl1_split : l1 = l1.take k ++ [false] := by
        apply List.ext_getElem
        · simp [hlen1]
        · intro idx h1 h2
          by_cases hk : idx < k
          · rw [List.getElem_append_left (by simp [hlen1]; omega), List.getElem_take]
          · have heq : idx = k := by omega
            subst heq
            rw [List.getElem_append_right (by simp [hlen1])]
            simp [hlen1, hlast_f]
      rw [hl1_split, hrep_false p' (l1.take k) (List.length_take_of_le (by omega))]
      have hsort_pref := ih p' (l1.take k) (List.length_take_of_le (by omega)) (by omega)
      rw [isSortedDesc_iff_getElem] at hsort_pref ⊢
      intro i j hi hj hij hj1
      have hlen_p : (applyBoolComps (List.replicate p' (List.range (k - 1))).flatten (l1.take k)).length = k := by
        rw [applyBoolComps_length, List.length_take_of_le (by omega)]
      have hj_lt : j < k := by
        by_contra hge
        have heq : j = k := by simp [hlen_p] at hj; omega
        subst heq
        rw [List.getElem_append_right (by omega)] at hj1
        simp [hlen_p] at hj1
      rw [List.getElem_append_left (by omega)] at hj1 ⊢
      exact hsort_pref i j (by omega) (by omega) hij hj1

private def runCompsAndInvert (m wFalse b : ℕ) : List ℕ → List ℕ → List Gate → List Gate × List ℕ
  | [], ws, gs => invertSorted m wFalse b ws gs
  | j :: rest, ws, gs =>
    if hj : j + 1 < ws.length then
      let a := ws[j]'(by omega)
      let bw := ws[j + 1]'hj
      let rOr := addOr m gs a bw
      let rAnd := addAnd m rOr.1 a bw
      let ws' := (ws.set j rOr.2).set (j + 1) rAnd.2
      let rRec := runCompsAndInvert m wFalse b rest ws' rAnd.1
      let na' := rRec.2.getD j wFalse
      let nb' := rRec.2.getD (j + 1) wFalse
      let r1 := addAnd m rRec.1 bw nb'
      let r2 := addOr m r1.1 na' r1.2
      let r3 := addAnd m r2.1 a nb'
      let r4 := addOr m r3.1 na' r3.2
      (r4.1, (rRec.2.set j r2.2).set (j + 1) r4.2)
    else
      runCompsAndInvert m wFalse b rest ws gs

private lemma runCompsAndInvert_spec (m wFalse b : ℕ) :
    ∀ (cs : List ℕ) (ws : List ℕ) (gs : List Gate),
      ws.length < 2 ^ b → Valid m gs → wFalse < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      let res := runCompsAndInvert m wFalse b cs ws gs
      gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length ≤ gs.length + 6 * cs.length + 4 * ws.length ∧
      notCount ⟨res.1, 0⟩ ≤ notCount ⟨gs, 0⟩ + b ∧
      res.2.length = ws.length ∧
      (∀ w ∈ res.2, w < m + res.1.length) ∧
      ∀ x : List Bool, x.length = m → evalW gs x wFalse = false →
        IsSortedDesc (applyBoolComps cs (ws.map (evalW gs x))) →
        res.2.map (evalW res.1 x) = (ws.map (evalW gs x)).map Bool.not := by
  intro cs
  induction cs with
  | nil =>
    intro ws gs hlt hv hF hws
    simpa [runCompsAndInvert, applyBoolComps] using invertSorted_spec m wFalse b ws gs hlt hv hF hws
  | cons j rest ih =>
    intro ws gs hlt hv hF hws
    by_cases hj : j + 1 < ws.length
    · simp only [runCompsAndInvert, hj, ↓reduceDIte]
      set a := ws[j]'(by omega)
      set bw := ws[j + 1]'hj
      have ha_lt : a < m + gs.length := hws _ (List.getElem_mem _)
      have hb_lt : bw < m + gs.length := hws _ (List.getElem_mem _)
      obtain ⟨hpreO, hvO, hlenO, hnotO, hwO, hevalO⟩ := addOr_spec (a := a) (b := bw) hv ha_lt hb_lt
      set rOr := addOr m gs a bw
      obtain ⟨hpreA, hvA, hlenA, hnotA, hwA, hevalA⟩ := addAnd_spec (a := a) (b := bw) hvO (by omega) (by omega)
      set rAnd := addAnd m rOr.1 a bw
      set ws' := (ws.set j rOr.2).set (j + 1) rAnd.2
      have hws'_len : ws'.length = ws.length := by simp [ws']
      have hws'_lt : ∀ w ∈ ws', w < m + rAnd.1.length := by
        intro w hw
        rcases mem_of_mem_set hw with rfl | hw1
        · exact hwA
        · rcases mem_of_mem_set hw1 with rfl | hw2
          · omega
          · have := hws w hw2; omega
      obtain ⟨hpreR, hvR, hlenR, hnotR, hrR_len, hrR_lt, hrR_eval⟩ :=
        ih ws' rAnd.1 (by omega) hvA (by omega) hws'_lt
      set rRec := runCompsAndInvert m wFalse b rest ws' rAnd.1
      have hpre_gsR : gs <+: rRec.1 := (hpreO.trans hpreA).trans hpreR
      have hlen_gsR : gs.length ≤ rRec.1.length := hpre_gsR.length_le
      have hFR : wFalse < m + rRec.1.length := by omega
      set na' := rRec.2.getD j wFalse
      set nb' := rRec.2.getD (j + 1) wFalse
      have hna'_lt : na' < m + rRec.1.length := getD_mem_lt hFR hrR_lt j
      have hnb'_lt : nb' < m + rRec.1.length := getD_mem_lt hFR hrR_lt (j + 1)
      obtain ⟨hpre1, hv1, hlen1, hnot1, hw1, heval1⟩ := addAnd_spec (a := bw) (b := nb') hvR (by omega) hnb'_lt
      set r1 := addAnd m rRec.1 bw nb'
      obtain ⟨hpre2, hv2, hlen2, hnot2, hw2, heval2⟩ := addOr_spec (a := na') (b := r1.2) hv1 (by omega) hw1
      set r2 := addOr m r1.1 na' r1.2
      obtain ⟨hpre3, hv3, hlen3, hnot3, hw3, heval3⟩ := addAnd_spec (a := a) (b := nb') hv2 (by omega) (by omega)
      set r3 := addAnd m r2.1 a nb'
      obtain ⟨hpre4, hv4, hlen4, hnot4, hw4, heval4⟩ := addOr_spec (a := na') (b := r3.2) hv3 (by omega) hw3
      set r4 := addOr m r3.1 na' r3.2
      have hpre_R4 : rRec.1 <+: r4.1 := ((hpre1.trans hpre2).trans hpre3).trans hpre4
      refine ⟨hpre_gsR.trans hpre_R4, hv4, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · omega
      · simp [hrR_len, hws'_len]
      · intro w hw
        rcases mem_of_mem_set hw with rfl | hw1'
        · exact hw4
        · rcases mem_of_mem_set hw1' with rfl | hw2'
          · omega
          · have := hrR_lt w hw2'; omega
      · intro x hx hFv hsort

        have hws'_map : ws'.map (evalW rAnd.1 x) = applyBoolComp j (ws.map (evalW gs x)) := by
          apply List.ext_getElem
          · simp [ws', applyBoolComp_length]
          · intro idx h1 h2
            simp only [List.length_map, hws'_len] at h1
            simp only [List.getElem_map, applyBoolComp, show j + 1 < (ws.map (evalW gs x)).length by simp; omega,
              ↓reduceDIte]
            by_cases h_j1 : idx = j + 1
            · subst h_j1
              simp only [ws']
              rw [List.getElem_set_self, List.getElem_set_self, hevalA x hx,
                evalW_of_prefix hpreO x (by rw [hx]; exact ha_lt),
                evalW_of_prefix hpreO x (by rw [hx]; exact hb_lt)]
            · simp only [ws']
              rw [List.getElem_set_ne (show j + 1 ≠ idx by omega),
                List.getElem_set_ne (show j + 1 ≠ idx by omega)]
              by_cases h_j : idx = j
              · subst h_j
                rw [List.getElem_set_self, List.getElem_set_self,
                  evalW_of_prefix hpreA x (by rw [hx]; exact hwO), hevalO x hx]
              · rw [List.getElem_set_ne (show j ≠ idx by omega),
                  List.getElem_set_ne (show j ≠ idx by omega),
                  evalW_of_prefix (hpreO.trans hpreA) x (by rw [hx]; exact hws _ (List.getElem_mem _))]
                simp
        have hFAv : evalW rAnd.1 x wFalse = false := by
          rw [evalW_of_prefix (hpreO.trans hpreA) x (by rw [hx]; exact hF), hFv]
        have hrec_eq : rRec.2.map (evalW rRec.1 x) = (ws'.map (evalW rAnd.1 x)).map Bool.not :=
          hrR_eval x hx hFAv (by simpa only [applyBoolComps, hws'_map] using hsort)

        have hna'_val : evalW rRec.1 x na' = !(evalW gs x a || evalW gs x bw) := by
          have hlt_j : j < rRec.2.length := by omega
          have hget := congrArg (fun l => l[j]?) hrec_eq
          simp only [na', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_j, Option.getD_some]
          rw [hws'_map] at hget
          simp only [List.getElem?_map, List.getElem?_eq_getElem hlt_j,
            List.getElem?_eq_getElem (show j < (applyBoolComp j (ws.map (evalW gs x))).length by
              rw [applyBoolComp_length]; simp; omega),
            Option.map_some, Option.some.injEq] at hget
          rw [hget]
          simp [applyBoolComp, hj, a, bw]
        have hnb'_val : evalW rRec.1 x nb' = !(evalW gs x a && evalW gs x bw) := by
          have hlt_j1 : j + 1 < rRec.2.length := by omega
          have hget := congrArg (fun l => l[j + 1]?) hrec_eq
          simp only [nb', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_j1, Option.getD_some]
          rw [hws'_map] at hget
          simp only [List.getElem?_map, List.getElem?_eq_getElem hlt_j1,
            List.getElem?_eq_getElem (show j + 1 < (applyBoolComp j (ws.map (evalW gs x))).length by
              rw [applyBoolComp_length]; simp; omega),
            Option.map_some, Option.some.injEq] at hget
          rw [hget]
          simp [applyBoolComp, hj, a, bw]

        apply List.ext_getElem
        · simp [hrR_len, hws'_len]
        · intro idx h1 h2
          simp only [List.length_map] at h2
          simp only [List.getElem_map]
          by_cases h_j1 : idx = j + 1
          · subst h_j1
            rw [List.getElem_set_self]
            rw [heval4 x hx, heval3 x hx,
              evalW_of_prefix ((hpre1.trans hpre2).trans hpre3) x (by rw [hx]; exact hna'_lt),
              evalW_of_prefix (hpre_gsR.trans (hpre1.trans hpre2)) x (by rw [hx]; exact ha_lt),
              evalW_of_prefix (hpre1.trans hpre2) x (by rw [hx]; exact hnb'_lt),
              hna'_val, hnb'_val]
            change (!(evalW gs x a || evalW gs x bw) || (evalW gs x a && !(evalW gs x a && evalW gs x bw))) = !(evalW gs x bw)
            cases evalW gs x a <;> cases evalW gs x bw <;> rfl
          · rw [List.getElem_set_ne (by omega)]
            by_cases h_j : idx = j
            · subst h_j
              rw [List.getElem_set_self]
              rw [evalW_of_prefix (hpre3.trans hpre4) x (by rw [hx]; exact hw2),
                heval2 x hx, heval1 x hx,
                evalW_of_prefix (w := na') hpre1 x (by rw [hx]; exact hna'_lt),
                evalW_of_prefix (w := bw) hpre_gsR x (by rw [hx]; exact hb_lt),
                hna'_val, hnb'_val]
              change (!(evalW gs x a || evalW gs x bw) || (evalW gs x bw && !(evalW gs x a && evalW gs x bw))) = !(evalW gs x a)
              cases evalW gs x a <;> cases evalW gs x bw <;> rfl
            · rw [List.getElem_set_ne (by omega)]
              rw [evalW_of_prefix hpre_R4 x (by rw [hx]; exact hrR_lt _ (List.getElem_mem _))]
              have hlt_i : idx < rRec.2.length := by omega
              have hget := congrArg (fun l => l[idx]?) hrec_eq
              rw [hws'_map] at hget
              simp only [List.getElem?_map, List.getElem?_eq_getElem hlt_i,
                List.getElem?_eq_getElem (show idx < (applyBoolComp j (ws.map (evalW gs x))).length by
                  rw [applyBoolComp_length]; simp; omega),
                Option.map_some, Option.some.injEq] at hget
              rw [hget]
              simp only [applyBoolComp, show j + 1 < (ws.map (evalW gs x)).length by simp; omega,
                ↓reduceDIte]
              rw [List.getElem_set_ne (show j + 1 ≠ idx by omega),
                List.getElem_set_ne (show j ≠ idx by omega), List.getElem_map]
    · simp only [runCompsAndInvert, hj, ↓reduceDIte]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih ws gs hlt hv hF hws
      refine ⟨h1, h2, by simp only [List.length_cons]; omega, h4, h5, h6, ?_⟩
      intro x hx hFv hsort
      apply h7 x hx hFv
      simpa only [applyBoolComps, applyBoolComp, show ¬ (j + 1 < (ws.map (evalW gs x)).length) by simp [hj],
        ↓reduceDIte] using hsort

private lemma size_combine {lFin lInv lC1 lPairs lC0 lCol lFinR lBub lCtrl lRP lDisj lTail n s d : ℕ}
    (h1 : lFin ≤ lInv + lFinR * (n + 2))
    (h2 : lInv ≤ lC1 + 6 * lBub + 4 * lCtrl)
    (h3 : lC1 = lPairs + lRP)
    (h4 : lPairs = lC0 + lDisj)
    (h5 : lC0 = lCol + lTail)
    (h6 : lCol ≤ s * n)
    (h7 : lFinR = n)
    (h8 : lCtrl = s + 2)
    (h9 : lBub ≤ (s + 2) * (s + 2))
    (h10 : lRP = lDisj)
    (h11 : lDisj ≤ n * n)
    (h12 : lTail ≤ n)
    (h13 : s ≤ d) :
    lFin ≤ 64 * (n + d + 2) ^ 2 := by
  have ha : lFin ≤ s * n + n + n * n + n * n + 6 * ((s + 2) * (s + 2)) + 4 * (s + 2) + n * (n + 2) := by
    subst h3; subst h4; subst h5; subst h7; subst h8; subst h10; omega
  nlinarith

end PEqualNP.Outside.L_lib_1282_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_lib_1282 : (∀ (d t s b : Nat), 2≤t → 2*t+s≤d → d<3*t → s+2<2^b →
  let V := {u : Finset (Fin d) // u.card=t}
  let n := Fintype.card V
  let E := fun j : Fin n => ((Fintype.equivFin V).symm j).val
  let X := Finset (Fin n)
  let tail := fun j => ∀ i ∈ E j, s ≤ i.val
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output<n+2+C.size ∧ PEqualNP.NotBracket.notCount C≤b ∧ C.size≤64*(n+d+2)^2 ∧
    let f := fun (x : X) (j : Fin n) =>
      (C.wires (List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true])).getD (tap j).val false
    (∀ x j, (∀ i ∈ x, Disjoint (E i) (E j)) → f x j=true) ∧ (∀ x j, j∈x → f x j=false) ∧
    ((Finset.univ : X).filter tail).card=(d-s).choose t ∧
    ∀ j, (¬tail j → ∀ u v, u⊆v → f v j=true → f u j=true) ∧
      (tail j → ∃ k a, f {k} j=false ∧ f {k,a} j=true)) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.NotBracket PEqualNP.Outside.L_lib_1282_aux in
  intro d t s b ht h2ts hd3t hsb V n E X tail
  classical

  have htail_card : ((Finset.univ : X).filter tail).card = (d - s).choose t := by
    let tailPts : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => s ≤ i.val)
    have htp_card : tailPts.card = d - s := by
      let emb : Fin (d - s) ↪ Fin d := ⟨fun k => ⟨s + k.val, by omega⟩, fun a b h => by
        ext; have := congrArg Fin.val h; simp at this; omega⟩
      have heq : (Finset.univ : Finset (Fin (d - s))).map emb = tailPts := by
        ext i
        simp only [Finset.mem_map, Finset.mem_univ, true_and, tailPts, Finset.mem_filter, emb,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨k, rfl⟩; change s ≤ s + k.val; omega
        · intro hi; exact ⟨⟨i.val - s, by omega⟩, Fin.ext (by change s + (i.val - s) = i.val; omega)⟩
      rw [← heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hbij : ((Finset.univ : X).filter tail).card = (tailPts.powersetCard t).card := by
      apply Finset.card_bij (fun j _ => E j)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Finset.mem_powersetCard]
        refine ⟨fun i hi => by simp [tailPts, hj i hi], ((Fintype.equivFin V).symm j).property⟩
      · intro j₁ _ j₂ _ hE
        have hsub : (Fintype.equivFin V).symm j₁ = (Fintype.equivFin V).symm j₂ := Subtype.ext hE
        exact (Fintype.equivFin V).symm.injective hsub
      · intro S hS
        rw [Finset.mem_powersetCard] at hS
        refine ⟨(Fintype.equivFin V) ⟨S, hS.2⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, tail, E, Equiv.symm_apply_apply]
          intro i hi; exact (Finset.mem_filter.mp (hS.1 hi)).2
        · simp [E]
    rw [hbij, Finset.card_powersetCard, htp_card]

  have hex_col : ∀ j : Fin n, ¬ tail j → ∃ r : Fin s, (⟨r.val, by omega⟩ : Fin d) ∈ E j := by
    intro j hnt
    simp only [tail, not_forall, not_le] at hnt
    rcases hnt with ⟨i, hi, his⟩
    exact ⟨⟨i.val, his⟩, by convert hi⟩
  let col : Fin n → ℕ := fun j =>
    if h : ¬ tail j then (Classical.choose (hex_col j h)).val else s
  have hcol_mem : ∀ j : Fin n, ¬ tail j → ∃ h : col j < d, (⟨col j, h⟩ : Fin d) ∈ E j := by
    intro j hnt
    have hspec := Classical.choose_spec (hex_col j hnt)
    refine ⟨by simp only [col, dif_pos hnt]; have := (Classical.choose (hex_col j hnt)).isLt; omega, ?_⟩
    simpa only [col, dif_pos hnt] using hspec
  have hcol_lt : ∀ j : Fin n, ¬ tail j → col j < s := by
    intro j hnt
    simp only [col, dif_pos hnt]
    exact (Classical.choose (hex_col j hnt)).isLt

  let m := n + 2
  have hv0 : Valid m [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  have hF0 : n < m + ([] : List Gate).length := by simp [m]
  have heval_false : ∀ (gs : List Gate) (x : X),
      evalW gs (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) n = false := by
    intro gs x
    rw [evalW_of_prefix List.nil_prefix _ (by simp)]
    simp only [evalW, Circuit.wires, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have heval_in : ∀ (gs : List Gate) (x : X) (i : Fin n),
      evalW gs (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) i.val = decide (i ∈ x) := by
    intro gs x i
    rw [evalW_of_prefix List.nil_prefix _ (by simp; omega)]
    simp only [evalW, Circuit.wires, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
    simp

  let colorList : ℕ → List ℕ := fun r =>
    (List.finRange n).filterMap (fun i => if ¬ tail i ∧ col i = r then some i.val else none)
  have hcolorList_len : ∀ r, (colorList r).length ≤ n := by
    intro r
    calc (colorList r).length ≤ (List.finRange n).length := List.length_filterMap_le _ _
      _ = n := List.length_finRange
  have hcolorList_lt : ∀ r w, w ∈ colorList r → w < m := by
    intro r w hw
    simp only [colorList, List.mem_filterMap] at hw
    rcases hw with ⟨i, _, hi⟩
    split_ifs at hi with h
    simp only [Option.some.injEq] at hi; subst hi; omega
  let colorStep : List Gate × List ℕ → ℕ → List Gate × List ℕ := fun acc r =>
    let res := addOrList m n (colorList r) acc.1
    (res.1, acc.2 ++ [res.2])

  have hcol_build : ∀ k ≤ s,
      let res := (List.range k).foldl colorStep ([], [])
      Valid m res.1 ∧ res.1.length ≤ k * n ∧ notCount ⟨res.1, 0⟩ = 0 ∧
      res.2.length = k ∧ (∀ w ∈ res.2, w < m + res.1.length) ∧
      ∀ (x : X) (r : ℕ) (hr : r < res.2.length),
        evalW res.1 (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (res.2[r]'hr) =
        decide (∃ i ∈ x, ¬ tail i ∧ col i = r) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨hv0, by simp, by simp [notCount], rfl, by simp, fun _ _ hr => by simp at hr⟩
    | succ k ih =>
      obtain ⟨hv, hlen, hnot, hacc_len, hlt, heval⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set cur := (List.range k).foldl colorStep ([], [])
      obtain ⟨hpre, hv', hlen', hnot', hw', heval'⟩ :=
        addOrList_spec m n (colorList k) cur.1 hv (by omega) (fun w hw => by have := hcolorList_lt k w hw; omega)
      refine ⟨hv', ?_, by simp only [colorStep]; rw [hnot', hnot],
        by simp only [colorStep, List.length_append, List.length_singleton, hacc_len], ?_, ?_⟩
      · simp only [colorStep, hlen']
        have := hcolorList_len k
        calc cur.1.length + (colorList k).length ≤ k * n + n := by omega
          _ = (k + 1) * n := by ring
      · intro w hw
        simp only [colorStep, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw1 | rfl
        · have := hlt w hw1; simp only [colorStep]; omega
        · exact hw'
      · intro x r hr
        let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
        have hxL_len : xL.length = m := by simp [xL, m]
        by_cases hrk : r < k
        · have hget : (colorStep cur k).2[r]'hr = cur.2[r]'(by omega) := by
            simp only [colorStep, List.getElem_append_left (show r < cur.2.length by omega)]
          rw [hget, evalW_of_prefix hpre xL (by rw [hxL_len]; exact hlt _ (List.getElem_mem _))]
          exact heval x r (by omega)
        · have heq : r = k := by simp [colorStep, hacc_len] at hr; omega
          have hget : (colorStep cur k).2[r]'hr = (addOrList m n (colorList k) cur.1).2 := by
            simp only [colorStep, List.getElem_append_right (show cur.2.length ≤ r by omega),
              hacc_len, show r - k = 0 by omega, List.getElem_cons_zero]
          rw [hget, heq, heval' xL hxL_len (heval_false cur.1 x)]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨w, hw, hwt⟩
            simp only [colorList, List.mem_filterMap] at hw
            rcases hw with ⟨i, _, hi⟩
            split_ifs at hi with hc
            simp only [Option.some.injEq] at hi; subst hi
            rw [heval_in cur.1 x i, decide_eq_true_eq] at hwt
            exact ⟨i, hwt, hc⟩
          · rintro ⟨i, hix, hnt, hci⟩
            refine ⟨i.val, ?_, by rw [heval_in cur.1 x i]; simp [hix]⟩
            simp only [colorList, List.mem_filterMap]
            exact ⟨i, List.mem_finRange i, by simp [hnt, hci]⟩
  obtain ⟨hvCol, hlenCol, hnotCol, hrCol_len, hrCol_lt, hrCol_eval⟩ := hcol_build s (le_refl s)
  set rCol := (List.range s).foldl colorStep ([], [])

  let tailList : List ℕ := (List.finRange n).filterMap (fun i => if tail i then some i.val else none)
  have htailList_len : tailList.length ≤ n := by
    calc tailList.length ≤ (List.finRange n).length := List.length_filterMap_le _ _
      _ = n := List.length_finRange
  have htailList_lt : ∀ w ∈ tailList, w < m + rCol.1.length := by
    intro w hw
    simp only [tailList, List.mem_filterMap] at hw
    rcases hw with ⟨i, _, hi⟩
    split_ifs at hi <;> simp_all; omega
  obtain ⟨hpreC0, hvC0, hlenC0, hnotC0, hwC0_lt, hevalC0⟩ :=
    addOrList_spec m n tailList rCol.1 hvCol (by omega) htailList_lt
  set rC0 := addOrList m n tailList rCol.1

  let disjPairs : List (Fin n × Fin n) :=
    ((List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))).filter
      (fun p => decide (tail p.1 ∧ tail p.2 ∧ Disjoint (E p.1) (E p.2)))
  have hdisjPairs_len : disjPairs.length ≤ n * n := by
    calc disjPairs.length
        ≤ ((List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))).length :=
          List.length_filter_le _ _
      _ = n * n := by
          simp [List.length_flatMap, List.length_finRange]
  let pairStep : List Gate × List ℕ → (Fin n × Fin n) → List Gate × List ℕ := fun acc p =>
    let ra := addAnd m acc.1 p.1.val p.2.val
    (ra.1, acc.2 ++ [ra.2])
  have hpair_build : ∀ (ps : List (Fin n × Fin n)) (gs : List Gate),
      Valid m gs →
      let res := ps.foldl pairStep (gs, [])
      gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length = gs.length + ps.length ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      (∀ w ∈ res.2, w < m + res.1.length) ∧
      ∀ (x : X),
        res.2.any (evalW res.1 (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])) =
        decide (∃ p ∈ ps, p.1 ∈ x ∧ p.2 ∈ x) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil =>
      intro gs hv
      exact ⟨List.prefix_refl _, hv, by simp, rfl, by simp, fun _ => by simp⟩
    | append_singleton ps p ih =>
      intro gs hv
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hpre, hv', hlen', hnot', hlt', heval'⟩ := ih gs hv
      set cur := ps.foldl pairStep (gs, [])
      obtain ⟨hpa, hva, hla, hna, hwa, hea⟩ := addAnd_spec (a := p.1.val) (b := p.2.val) hv'
        (show p.1.val < m + cur.1.length by omega) (show p.2.val < m + cur.1.length by omega)
      refine ⟨hpre.trans hpa, hva, by simp only [pairStep, hla, hlen', List.length_append, List.length_singleton]; omega,
        by simp only [pairStep, hna, hnot'], ?_, ?_⟩
      · intro w hw
        simp only [pairStep, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw1 | rfl
        · have := hlt' w hw1; simp only [pairStep]; omega
        · exact hwa
      · intro x
        let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
        have hxL_len : xL.length = m := by simp [xL, m]
        simp only [pairStep, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
        have hany_eq : cur.2.any (evalW (addAnd m cur.1 p.1.val p.2.val).1 xL) = cur.2.any (evalW cur.1 xL) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          exact exists_congr fun w => and_congr_right fun hw => by
            rw [evalW_of_prefix hpa xL (by rw [hxL_len]; exact hlt' w hw)]
        rw [hany_eq, heval' x, hea xL hxL_len, heval_in cur.1 x p.1, heval_in cur.1 x p.2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_append,
          List.mem_singleton]
        constructor
        · rintro (⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨q, Or.inl hq, h1, h2⟩
          · exact ⟨p, Or.inr rfl, h1, h2⟩
        · rintro ⟨q, hq | rfl, h1, h2⟩
          · exact Or.inl ⟨q, hq, h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
  obtain ⟨hpreP, hvP, hlenP, hnotP, hwP_lt, hevalP⟩ := hpair_build disjPairs rC0.1 hvC0
  set rPairs := disjPairs.foldl pairStep (rC0.1, [])
  obtain ⟨hpreC1, hvC1, hlenC1, hnotC1, hwC1_lt, hevalC1⟩ :=
    addOrList_spec m n rPairs.2 rPairs.1 hvP (by omega) hwP_lt
  set rC1 := addOrList m n rPairs.2 rPairs.1

  let ctrlWires : List ℕ := rCol.2 ++ [rC0.2, rC1.2]
  have hctrl_len : ctrlWires.length = s + 2 := by simp [ctrlWires, hrCol_len]
  have hctrl_lt : ∀ w ∈ ctrlWires, w < m + rC1.1.length := by
    intro w hw
    have h1 : rCol.1.length ≤ rC1.1.length := ((hpreC0.trans hpreP).trans hpreC1).length_le
    have h2 : rC0.1.length ≤ rC1.1.length := (hpreP.trans hpreC1).length_le
    simp only [ctrlWires, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw1 | rfl | rfl
    · have := hrCol_lt w hw1; omega
    · omega
    · exact hwC1_lt
  obtain ⟨hpreInv, hvInv, hlenInv, hnotInv, hrInv_len, hrInv_lt, hrInv_eval⟩ :=
    runCompsAndInvert_spec m n b (bubbleComps (s + 2)) ctrlWires rC1.1 (by omega) hvC1 (by omega) hctrl_lt
  set rInv := runCompsAndInvert m n b (bubbleComps (s + 2)) ctrlWires rC1.1

  have hnc0_lt : rInv.2.getD s n < m + rInv.1.length := getD_mem_lt (by omega) hrInv_lt s
  have hnc1_lt : rInv.2.getD (s + 1) n < m + rInv.1.length := getD_mem_lt (by omega) hrInv_lt (s + 1)

  let disjList : Fin n → List ℕ := fun j =>
    (List.finRange n).filterMap (fun i => if tail i ∧ Disjoint (E i) (E j) then some i.val else none)
  have hdisjList_len : ∀ j, (disjList j).length ≤ n := by
    intro j
    calc (disjList j).length ≤ (List.finRange n).length := List.length_filterMap_le _ _
      _ = n := List.length_finRange
  have hdisjList_lt : ∀ j w, w ∈ disjList j → w < m := by
    intro j w hw
    simp only [disjList, List.mem_filterMap] at hw
    rcases hw with ⟨i, _, hi⟩
    split_ifs at hi <;> simp_all; omega
  let tapStep : List Gate × List ℕ → Fin n → List Gate × List ℕ := fun acc j =>
    if tail j then
      let rD := addOrList m n (disjList j) acc.1
      let rA := addAnd m rD.1 rD.2 (rInv.2.getD (s + 1) n)
      let rO := addOr m rA.1 (rInv.2.getD s n) rA.2
      (rO.1, acc.2 ++ [rO.2])
    else
      (acc.1, acc.2 ++ [rInv.2.getD (col j) n])

  have hrInv_vals : ∀ (x : X),
      let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
      (∀ r (hr : r < s), evalW rInv.1 xL (rInv.2.getD r n) = !decide (∃ i ∈ x, ¬ tail i ∧ col i = r)) ∧
      evalW rInv.1 xL (rInv.2.getD s n) = !decide (∃ i ∈ x, tail i) ∧
      evalW rInv.1 xL (rInv.2.getD (s + 1) n) = !decide (∃ i ∈ x, ∃ i' ∈ x, tail i ∧ tail i' ∧ Disjoint (E i) (E i')) := by
    intro x
    let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
    have hxL_len : xL.length = m := by simp [xL, m]
    have hsort : IsSortedDesc (applyBoolComps (bubbleComps (s + 2)) (ctrlWires.map (evalW rC1.1 xL))) :=
      bubbleComps_sorts (s + 2) _ (by simp [hctrl_len])
    have hinv := hrInv_eval xL hxL_len (heval_false rC1.1 x) hsort
    have hget_inv : ∀ idx (hidx : idx < s + 2),
        evalW rInv.1 xL (rInv.2.getD idx n) = !(evalW rC1.1 xL (ctrlWires[idx]'(by omega))) := by
      intro idx hidx
      have hidx1 : idx < rInv.2.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx1, Option.getD_some]
      have hg := congrArg (fun l => l[idx]?) hinv
      simp only [List.getElem?_map, List.getElem?_eq_getElem hidx1,
        List.getElem?_eq_getElem (show idx < ctrlWires.length by omega), Option.map_some,
        Option.some.injEq] at hg
      exact hg
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rw [hget_inv r (by omega)]
      have hcw : ctrlWires[r]'(by omega) = rCol.2[r]'(by omega) := by
        simp only [ctrlWires, List.getElem_append_left (show r < rCol.2.length by omega)]
      rw [hcw, evalW_of_prefix ((hpreC0.trans hpreP).trans hpreC1) xL (by rw [hxL_len]; exact hrCol_lt _ (List.getElem_mem _)),
        hrCol_eval x r (by omega)]
    · rw [hget_inv s (by omega)]
      have hcw : ctrlWires[s]'(by omega) = rC0.2 := by
        simp only [ctrlWires, List.getElem_append_right (show rCol.2.length ≤ s by omega),
          hrCol_len, Nat.sub_self, List.getElem_cons_zero]
      rw [hcw, evalW_of_prefix (hpreP.trans hpreC1) xL (by rw [hxL_len]; exact hwC0_lt),
        hevalC0 xL hxL_len (heval_false rCol.1 x)]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, hwt⟩
        simp only [tailList, List.mem_filterMap] at hw
        rcases hw with ⟨i, _, hi⟩
        split_ifs at hi with ht'
        simp only [Option.some.injEq] at hi; subst hi
        rw [heval_in rCol.1 x i, decide_eq_true_eq] at hwt
        exact ⟨i, hwt, ht'⟩
      · rintro ⟨i, hix, ht'⟩
        refine ⟨i.val, ?_, by rw [heval_in rCol.1 x i]; simp [hix]⟩
        simp only [tailList, List.mem_filterMap]
        exact ⟨i, List.mem_finRange i, by simp [ht']⟩
    · rw [hget_inv (s + 1) (by omega)]
      have hcw : ctrlWires[s + 1]'(by omega) = rC1.2 := by
        simp only [ctrlWires, List.getElem_append_right (show rCol.2.length ≤ s + 1 by omega),
          hrCol_len]
        have hsub : s + 1 - s = 1 := by omega
        simp only [hsub, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hcw, hevalC1 xL hxL_len (heval_false rPairs.1 x), hevalP x]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, disjPairs, List.mem_filter, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and]
      constructor
      · rintro ⟨⟨i, i'⟩, ⟨⟨a, b, hab⟩, hprop⟩, hi, hi'⟩
        exact ⟨i, hi, i', hi', hprop⟩
      · rintro ⟨i, hi, i', hi', hprop⟩
        exact ⟨(i, i'), ⟨⟨i, i', rfl⟩, hprop⟩, hi, hi'⟩

  have htap_build : ∀ (js : List (Fin n)) (gs : List Gate),
      rInv.1 <+: gs → Valid m gs →
      let res := js.foldl tapStep (gs, [])
      gs <+: res.1 ∧ Valid m res.1 ∧ res.1.length ≤ gs.length + js.length * (n + 2) ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ res.2.length = js.length ∧
      (∀ w ∈ res.2, w < m + res.1.length) ∧
      ∀ (x : X) (idx : ℕ) (hidx : idx < js.length) (hidx2 : idx < res.2.length),
        let j := js[idx]'hidx
        evalW res.1 (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]) (res.2[idx]'hidx2) =
        if tail j then
          (!decide (∃ i ∈ x, tail i)) ||
            (decide (∃ i ∈ x, tail i ∧ Disjoint (E i) (E j)) &&
              !decide (∃ i ∈ x, ∃ i' ∈ x, tail i ∧ tail i' ∧ Disjoint (E i) (E i')))
        else
          !decide (∃ i ∈ x, ¬ tail i ∧ col i = col j) := by
    intro js
    induction js using List.reverseRecOn with
    | nil =>
      intro gs _ hv
      exact ⟨List.prefix_refl _, hv, by simp, rfl, rfl, by simp, fun _ _ h _ => by simp at h⟩
    | append_singleton js j ih =>
      intro gs hpre_inv hv
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hpre, hv', hlen', hnot', hacc_len, hlt', heval'⟩ := ih gs hpre_inv hv
      set cur := js.foldl tapStep (gs, [])
      have hpre_i : rInv.1 <+: cur.1 := hpre_inv.trans hpre
      have hlen_i : rInv.1.length ≤ cur.1.length := hpre_i.length_le
      by_cases htj : tail j
      · simp only [tapStep, if_pos htj]
        obtain ⟨hpreD, hvD, hlenD, hnotD, hwD, hevalD⟩ :=
          addOrList_spec m n (disjList j) cur.1 hv' (by omega) (fun w hw => by have := hdisjList_lt j w hw; omega)
        set rD := addOrList m n (disjList j) cur.1
        obtain ⟨hpreA, hvA, hlenA, hnotA, hwA, hevalA⟩ :=
          addAnd_spec (a := rD.2) (b := rInv.2.getD (s + 1) n) hvD hwD (by omega)
        set rA := addAnd m rD.1 rD.2 (rInv.2.getD (s + 1) n)
        obtain ⟨hpreO, hvO, hlenO, hnotO, hwO, hevalO⟩ :=
          addOr_spec (a := rInv.2.getD s n) (b := rA.2) hvA (by omega) hwA
        set rO := addOr m rA.1 (rInv.2.getD s n) rA.2
        have hstep_pre : cur.1 <+: rO.1 := (hpreD.trans hpreA).trans hpreO
        refine ⟨hpre.trans hstep_pre, hvO, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          rw [hlenO, hlenA, hlenD]
          have := hdisjList_len j
          calc cur.1.length + (disjList j).length + 1 + 1
              ≤ gs.length + js.length * (n + 2) + n + 2 := by omega
            _ = gs.length + (js.length + 1) * (n + 2) := by ring
        · rw [hnotO, hnotA, hnotD, hnot']
        · simp [hacc_len]
        · intro w hw
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw1 | rfl
          · have := hlt' w hw1; rw [hlenO, hlenA, hlenD]; omega
          · exact hwO
        · intro x idx hidx hidx2
          let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
          have hxL_len : xL.length = m := by simp [xL, m]
          by_cases hlt_idx : idx < js.length
          · have hget_w : (cur.2 ++ [rO.2])[idx]'hidx2 = cur.2[idx]'(by omega) :=
              List.getElem_append_left (by omega)
            have hget_j : (js ++ [j])[idx]'hidx = js[idx]'hlt_idx := List.getElem_append_left hlt_idx
            rw [hget_w, hget_j, evalW_of_prefix hstep_pre xL (by rw [hxL_len]; exact hlt' _ (List.getElem_mem _))]
            exact heval' x idx hlt_idx (by omega)
          · have heq_idx : idx = js.length := by simp at hidx; omega
            subst heq_idx
            have hget_w : (cur.2 ++ [rO.2])[js.length]'hidx2 = rO.2 := by
              rw [List.getElem_append_right (by omega)]; simp [hacc_len]
            have hget_j : (js ++ [j])[js.length]'hidx = j := by
              rw [List.getElem_append_right (le_refl _)]; simp
            rw [hget_w, hget_j, if_pos htj]
            obtain ⟨_, hnc0_v, hnc1_v⟩ := hrInv_vals x
            rw [hevalO xL hxL_len, hevalA xL hxL_len,
              evalW_of_prefix (w := rInv.2.getD s n) ((hpre_i.trans hpreD).trans hpreA) xL (by rw [hxL_len]; exact hnc0_lt),
              evalW_of_prefix (w := rInv.2.getD (s + 1) n) (hpre_i.trans hpreD) xL (by rw [hxL_len]; exact hnc1_lt),
              hnc0_v, hnc1_v, hevalD xL hxL_len (heval_false cur.1 x)]
            congr 2
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨w, hw, hwt⟩
              simp only [disjList, List.mem_filterMap] at hw
              rcases hw with ⟨i, _, hi⟩
              split_ifs at hi with hcond
              simp only [Option.some.injEq] at hi; subst hi
              rw [heval_in cur.1 x i, decide_eq_true_eq] at hwt
              exact ⟨i, hwt, hcond⟩
            · rintro ⟨i, hix, hcond⟩
              refine ⟨i.val, ?_, by rw [heval_in cur.1 x i]; simp [hix]⟩
              simp only [disjList, List.mem_filterMap]
              exact ⟨i, List.mem_finRange i, by simp [hcond]⟩
      · simp only [tapStep, if_neg htj]
        have hcol_lt' : col j < s := hcol_lt j htj
        have hw_col : rInv.2.getD (col j) n < m + cur.1.length :=
          lt_of_lt_of_le (getD_mem_lt (by omega) hrInv_lt (col j)) (by omega)
        refine ⟨hpre, hv', ?_, hnot', by simp [hacc_len], ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton]
          calc cur.1.length ≤ gs.length + js.length * (n + 2) := hlen'
            _ ≤ gs.length + (js.length + 1) * (n + 2) := by rw [Nat.add_mul, one_mul]; omega
        · intro w hw
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw1 | rfl
          · exact hlt' w hw1
          · exact hw_col
        · intro x idx hidx hidx2
          let xL := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]
          have hxL_len : xL.length = m := by simp [xL, m]
          by_cases hlt_idx : idx < js.length
          · have hget_w : (cur.2 ++ [rInv.2.getD (col j) n])[idx]'hidx2 = cur.2[idx]'(by omega) :=
              List.getElem_append_left (by omega)
            have hget_j : (js ++ [j])[idx]'hidx = js[idx]'hlt_idx := List.getElem_append_left hlt_idx
            rw [hget_w, hget_j]
            exact heval' x idx hlt_idx (by omega)
          · have heq_idx : idx = js.length := by simp at hidx; omega
            subst heq_idx
            have hget_w : (cur.2 ++ [rInv.2.getD (col j) n])[js.length]'hidx2 = rInv.2.getD (col j) n := by
              rw [List.getElem_append_right (by omega)]; simp [hacc_len]
            have hget_j : (js ++ [j])[js.length]'hidx = j := by
              rw [List.getElem_append_right (le_refl _)]; simp
            rw [hget_w, hget_j, if_neg htj,
              evalW_of_prefix hpre_i xL (by rw [hxL_len]; exact getD_mem_lt (by omega) hrInv_lt (col j))]
            exact (hrInv_vals x).1 (col j) hcol_lt'
  obtain ⟨hpreFin, hvFin, hlenFin, hnotFin, hrFin_len, hrFin_lt, hrFin_eval⟩ :=
    htap_build (List.finRange n) rInv.1 (List.prefix_refl _) hvInv
  set rFin := (List.finRange n).foldl tapStep (rInv.1, [])

  let C : Circuit := ⟨rFin.1, 0⟩
  have hC_size : C.size ≤ 64 * (n + d + 2) ^ 2 := by
    have hbubble := bubbleComps_length (s + 2)
    have hsd : s ≤ d := by omega
    have hrPairs_len : rPairs.2.length = disjPairs.length := by
      have hlen_p : ∀ (ps : List (Fin n × Fin n)) (gs : List Gate),
          (ps.foldl pairStep (gs, [])).2.length = ps.length := by
        intro ps
        induction ps using List.reverseRecOn with
        | nil => intro gs; rfl
        | append_singleton ps p ih =>
          intro gs; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          simp [pairStep, ih]
      exact hlen_p disjPairs rC0.1
    exact size_combine hlenFin hlenInv hlenC1 hlenP hlenC0 hlenCol List.length_finRange
      hctrl_len hbubble hrPairs_len hdisjPairs_len htailList_len hsd
  have hC_not : notCount C ≤ b := by
    change notCount ⟨rFin.1, 0⟩ ≤ b
    omega
  let tap : Fin n → Fin (n + 2 + C.size) := fun j =>
    ⟨rFin.2[j.val]'(by rw [hrFin_len, List.length_finRange]; exact j.isLt),
      hrFin_lt _ (List.getElem_mem _)⟩
  have hf_eq : ∀ (x : X) (j : Fin n),
      (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true])).getD (tap j).val false =
      if tail j then
        (!decide (∃ i ∈ x, tail i)) ||
          (decide (∃ i ∈ x, tail i ∧ Disjoint (E i) (E j)) &&
            !decide (∃ i ∈ x, ∃ i' ∈ x, tail i ∧ tail i' ∧ Disjoint (E i) (E i')))
      else
        !decide (∃ i ∈ x, ¬ tail i ∧ col i = col j) := by
    intro x j
    have h := hrFin_eval x j.val (by rw [List.length_finRange]; exact j.isLt)
      (by rw [hrFin_len, List.length_finRange]; exact j.isLt)
    simpa only [List.getElem_finRange, Fin.cast_mk, Fin.eta, C, tap, evalW] using h
  refine ⟨C, tap, hvFin.1, hvFin.2, by simp [C], hC_not, hC_size, ?_, ?_, htail_card, ?_⟩
  ·
    intro x j hdisj
    dsimp only
    rw [hf_eq x j]
    by_cases htj : tail j
    · rw [if_pos htj]
      by_cases hex : ∃ i ∈ x, tail i
      · rcases hex with ⟨i₀, hi₀x, hi₀t⟩
        have hdisj_i₀ : ∃ i ∈ x, tail i ∧ Disjoint (E i) (E j) := ⟨i₀, hi₀x, hi₀t, hdisj i₀ hi₀x⟩
        have hno_pair : ¬ (∃ i ∈ x, ∃ i' ∈ x, tail i ∧ tail i' ∧ Disjoint (E i) (E i')) := by
          rintro ⟨i₁, hi₁x, i₂, hi₂x, _, _, h12⟩
          have h1j : Disjoint (E i₁) (E j) := hdisj i₁ hi₁x
          have h2j : Disjoint (E i₂) (E j) := hdisj i₂ hi₂x
          have hcard_u : (E i₁ ∪ E i₂ ∪ E j).card = 3 * t := by
            have h12_j : Disjoint (E i₁ ∪ E i₂) (E j) := Finset.disjoint_union_left.mpr ⟨h1j, h2j⟩
            rw [Finset.card_union_of_disjoint h12_j, Finset.card_union_of_disjoint h12,
              ((Fintype.equivFin V).symm i₁).property, ((Fintype.equivFin V).symm i₂).property,
              ((Fintype.equivFin V).symm j).property]
            omega
          have hle_d : (E i₁ ∪ E i₂ ∪ E j).card ≤ d := by
            calc (E i₁ ∪ E i₂ ∪ E j).card ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_univ _
              _ = d := Fintype.card_fin d
          omega
        simp [hdisj_i₀, hno_pair]
      · simp [hex]
    · rw [if_neg htj]
      have hno : ¬ (∃ i ∈ x, ¬ tail i ∧ col i = col j) := by
        rintro ⟨i, hix, hnti, hcol_eq⟩
        obtain ⟨h1, hm1⟩ := hcol_mem i hnti
        obtain ⟨h2, hm2⟩ := hcol_mem j htj
        have hpt : (⟨col j, h2⟩ : Fin d) ∈ E i := by
          convert hm1 using 1; exact Fin.ext hcol_eq.symm
        exact Finset.disjoint_left.mp (hdisj i hix) hpt hm2
      simp [hno]
  ·
    intro x j hjx
    dsimp only
    rw [hf_eq x j]
    by_cases htj : tail j
    · rw [if_pos htj]
      have hex : ∃ i ∈ x, tail i := ⟨j, hjx, htj⟩
      by_cases hd : ∃ i ∈ x, tail i ∧ Disjoint (E i) (E j)
      · rcases hd with ⟨i₀, hi₀x, hi₀t, hdisj⟩
        have hpair : ∃ i ∈ x, ∃ i' ∈ x, tail i ∧ tail i' ∧ Disjoint (E i) (E i') :=
          ⟨i₀, hi₀x, j, hjx, hi₀t, htj, hdisj⟩
        simp [hex, hpair]
      · simp [hex, hd]
    · rw [if_neg htj]
      have hex : ∃ i ∈ x, ¬ tail i ∧ col i = col j := ⟨j, hjx, htj, rfl⟩
      simp [hex]
  ·
    intro j
    refine ⟨?_, ?_⟩
    · intro hntj u v huv hfv
      dsimp only at hfv ⊢
      rw [hf_eq v j, if_neg hntj] at hfv
      rw [hf_eq u j, if_neg hntj]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hfv ⊢
      rintro ⟨i, hiu, hnti, hci⟩
      exact hfv ⟨i, huv hiu, hnti, hci⟩
    · intro htj

      let tailPts : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => s ≤ i.val)
      have htp_card : tailPts.card = d - s := by
        let emb : Fin (d - s) ↪ Fin d :=
          ⟨fun k => ⟨s + k.val, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
        have heq : (Finset.univ : Finset (Fin (d - s))).map emb = tailPts := by
          ext i
          simp only [Finset.mem_map, Finset.mem_univ, true_and, tailPts, Finset.mem_filter, emb]
          constructor
          · rintro ⟨k, rfl⟩; exact Nat.le_add_right s k.val
          · intro hi; exact ⟨⟨i.val - s, by omega⟩, Fin.ext (by show s + (i.val - s) = i.val; omega)⟩
        rw [← heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      have hEj_sub : E j ⊆ tailPts := fun i hi => by simp [tailPts, htj i hi]
      have hEj_card : (E j).card = t := ((Fintype.equivFin V).symm j).property
      have hrem_card : t ≤ (tailPts \ E j).card := by
        rw [Finset.card_sdiff_of_subset hEj_sub, htp_card, hEj_card]; omega
      obtain ⟨Sa, hSa_sub, hSa_card⟩ := Finset.exists_subset_card_eq hrem_card
      let a : Fin n := (Fintype.equivFin V) ⟨Sa, hSa_card⟩
      have hEa : E a = Sa := by simp [E, a]
      have hta : tail a := by
        intro i hi; rw [hEa] at hi
        exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hSa_sub hi)).1).2
      have hdisj_aj : Disjoint (E a) (E j) := by
        rw [hEa, Finset.disjoint_left]
        intro i hi
        exact (Finset.mem_sdiff.mp (hSa_sub hi)).2

      obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (E j).card by omega)
      obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < (E a).card by rw [hEa, hSa_card]; omega)
      have hpq : p ≠ q := fun heq => Finset.disjoint_left.mp hdisj_aj (heq ▸ hq) hp

      have hU_sub : ({p, q} : Finset (Fin d)) ⊆ E j ∪ E a := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_left _ hp
        · exact Finset.mem_union_right _ hq
      have hU_card : t - 2 ≤ ((E j ∪ E a) \ {p, q}).card := by
        rw [Finset.card_sdiff_of_subset hU_sub, Finset.card_union_of_disjoint hdisj_aj.symm,
          Finset.card_pair hpq, hEj_card, hEa, hSa_card]
        omega
      obtain ⟨R, hR_sub, hR_card⟩ := Finset.exists_subset_card_eq hU_card
      let Sk : Finset (Fin d) := insert p (insert q R)
      have hpR : p ∉ R := fun h => (Finset.mem_sdiff.mp (hR_sub h)).2 (by simp)
      have hqR : q ∉ R := fun h => (Finset.mem_sdiff.mp (hR_sub h)).2 (by simp)
      have hSk_card : Sk.card = t := by
        simp only [Sk, Finset.card_insert_of_notMem (show p ∉ insert q R by simp [hpq, hpR]),
          Finset.card_insert_of_notMem hqR, hR_card]
        omega
      let k : Fin n := (Fintype.equivFin V) ⟨Sk, hSk_card⟩
      have hEk : E k = Sk := by simp [E, k]
      have htk : tail k := by
        intro z hz
        rw [hEk] at hz
        simp only [Sk, Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzR
        · exact htj z hp
        · exact hta z hq
        · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp (hR_sub hzR)).1 with h1 | h2
          · exact htj z h1
          · exact hta z h2
      have hnot_kj : ¬ Disjoint (E k) (E j) := by
        intro hd
        exact Finset.disjoint_left.mp hd (by simp [hEk, Sk]) hp
      have hnot_ka : ¬ Disjoint (E k) (E a) := by
        intro hd
        exact Finset.disjoint_left.mp hd (by simp [hEk, Sk]) hq
      have hnot_self : ∀ u : Fin n, ¬ Disjoint (E u) (E u) := by
        intro u hd
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (E u).card by
          rw [((Fintype.equivFin V).symm u).property]; omega)
        exact Finset.disjoint_left.mp hd hz hz
      refine ⟨k, a, ?_, ?_⟩
      ·
        dsimp only
        rw [hf_eq {k} j, if_pos htj]
        have h1 : ∃ i ∈ ({k} : Finset (Fin n)), tail i := ⟨k, Finset.mem_singleton_self k, htk⟩
        have h2 : ¬ (∃ i ∈ ({k} : Finset (Fin n)), tail i ∧ Disjoint (E i) (E j)) := by
          rintro ⟨i, hi, _, hd⟩
          simp only [Finset.mem_singleton] at hi; subst hi
          exact hnot_kj hd
        simp [h1, h2]
      ·
        dsimp only
        rw [hf_eq {k, a} j, if_pos htj]
        have h1 : ∃ i ∈ ({k, a} : Finset (Fin n)), tail i ∧ Disjoint (E i) (E j) :=
          ⟨a, Finset.mem_insert_of_mem (Finset.mem_singleton_self a), hta, hdisj_aj⟩
        have h2 : ¬ (∃ i ∈ ({k, a} : Finset (Fin n)), ∃ i' ∈ ({k, a} : Finset (Fin n)), tail i ∧ tail i' ∧ Disjoint (E i) (E i')) := by
          rintro ⟨i, hi, i', hi', _, _, hd⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
          rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
          · exact hnot_self k hd
          · exact hnot_ka hd
          · exact hnot_ka hd.symm
          · exact hnot_self a hd
        simp [h1, h2]
