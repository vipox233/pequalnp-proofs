import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_1275_aux

open PEqualNP.CircuitLowerBounds

def GateOK (m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

def evalWires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def wVal (gs : List Gate) (inp : List Bool) (i : ℕ) : Bool :=
  (evalWires gs inp).getD i false

lemma evalWires_length (gs : List Gate) (inp : List Bool) :
    (evalWires gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp; omega

lemma evalWires_append (g1 g2 : List Gate) (inp : List Bool) :
    evalWires (g1 ++ g2) inp = evalWires g2 (evalWires g1 inp) := by
  simp [evalWires, List.foldl_append]

lemma evalWires_prefix_getD (g1 g2 : List Gate) (inp : List Bool) {i : ℕ}
    (hi : i < inp.length + g1.length) :
    wVal (g1 ++ g2) inp i = wVal g1 inp i := by
  unfold wVal
  rw [evalWires_append]
  have hiw : i < (evalWires g1 inp).length := by rw [evalWires_length]; exact hi
  generalize evalWires g1 inp = w at hiw ⊢
  induction g2 generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp; omega
    rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiw]

lemma evalWires_input (gs : List Gate) (inp : List Bool) {i : ℕ} (hi : i < inp.length) :
    wVal gs inp i = inp.getD i false := by
  have h := evalWires_prefix_getD [] gs inp (i := i) (by simpa using hi)
  simpa [wVal, evalWires] using h

lemma notCnt_append (g1 g2 : List Gate) : notCnt (g1 ++ g2) = notCnt g1 + notCnt g2 := by
  simp [notCnt, List.filter_append]

lemma GateOK_nil (m : ℕ) : GateOK m [] := by
  refine ⟨by simp, fun j hj => by simp at hj⟩

lemma GateOK_append_gate {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < m + gs.length) :
    GateOK m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hgs.1 g' hg'
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

lemma wVal_append_gate (gs : List Gate) (g : Gate) (inp : List Bool) :
    wVal (gs ++ [g]) inp (inp.length + gs.length) =
    g.op.eval (g.inputs.map fun i => wVal gs inp i) := by
  unfold wVal
  rw [evalWires_append]
  have hlen : (evalWires gs inp).length = inp.length + gs.length := evalWires_length gs inp
  generalize evalWires gs inp = w at hlen ⊢
  simp only [evalWires, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, ← hlen]
  rw [List.getElem?_append_right le_rfl]
  simp

lemma mkAnd_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a && wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.and, [a, b]⟩ (Or.inl rfl) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkOr_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.or, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a || wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.or, [a, b]⟩ (Or.inr (Or.inl rfl)) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkNot_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.not, [a]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = !(wVal gs inp a)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.not, [a]⟩ (Or.inr (Or.inr rfl)) (by simp)
      (by intro i hi; simp at hi; subst hi; exact ha),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

def Extends (gs gs' : List Gate) : Prop := ∃ suf, gs' = gs ++ suf

lemma Extends.refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma Extends.trans {g1 g2 g3 : List Gate} (h1 : Extends g1 g2) (h2 : Extends g2 g3) :
    Extends g1 g3 := by
  rcases h1 with ⟨s1, rfl⟩; rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by simp [List.append_assoc]⟩

lemma Extends.length_le {g1 g2 : List Gate} (h : Extends g1 g2) : g1.length ≤ g2.length := by
  rcases h with ⟨s, rfl⟩; simp

lemma Extends.wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    {i : ℕ} (hi : i < inp.length + g1.length) :
    wVal g2 inp i = wVal g1 inp i := by
  rcases h with ⟨s, rfl⟩
  exact evalWires_prefix_getD g1 s inp hi

lemma Extends.map_wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < inp.length + g1.length) :
    ws.map (wVal g2 inp) = ws.map (wVal g1 inp) := by
  apply List.map_congr_left
  intro w hw
  exact h.wVal_eq inp (hws w hw)

lemma mkAnd_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a && wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkAnd_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkOr_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a || wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkOr_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkNot_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = !(wVal gs inp a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkNot_step hgs ha
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

def IsSortedDesc (L : List Bool) : Prop :=
  L = List.replicate (L.count true) true ++ List.replicate (L.length - L.count true) false

def IsBitonic (L : List Bool) : Prop :=
  ∃ (a b : ℕ), a ≤ b ∧ b ≤ L.length ∧
    (L = List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (L.length - b) true ∨
     L = List.replicate a false ++ List.replicate (b - a) true ++ List.replicate (L.length - b) false)

lemma count_true_le_length (L : List Bool) : L.count true ≤ L.length :=
  List.count_le_length

lemma getElem_isSortedDesc {L : List Bool} (hS : IsSortedDesc L) {i : ℕ} (hi : i < L.length) :
    L[i] = decide (i < L.count true) := by
  have hlen : L.count true ≤ L.length := count_true_le_length L
  have hget : L[i]? = some (decide (i < L.count true)) := by
    conv_lhs => rw [hS]
    by_cases hic : i < L.count true
    · rw [List.getElem?_append_left (by simp [hic])]
      simp [hic]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      rw [List.getElem?_replicate]
      simp [hic, (by omega : i - L.count true < L.length - L.count true)]
  have := List.getElem?_eq_getElem hi
  rw [this] at hget
  exact Option.some.inj hget

lemma isSortedDesc_iff_getElem (L : List Bool) :
    IsSortedDesc L ↔ ∀ (i : ℕ) (hi : i < L.length), L[i] = decide (i < L.count true) := by
  constructor
  · intro hS i hi; exact getElem_isSortedDesc hS hi
  · intro h
    unfold IsSortedDesc
    have hlen : L.count true ≤ L.length := count_true_le_length L
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      rw [h i hi1]
      by_cases hic : i < L.count true
      · rw [List.getElem_append_left (by simp [hic])]
        simp [hic]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [hic]

lemma isSortedDesc_of_all_false {L : List Bool} (h : ∀ b ∈ L, b = false) : IsSortedDesc L := by
  have hc : L.count true = 0 := by
    rw [List.count_eq_zero]
    intro hmem; exact Bool.noConfusion (h true hmem)
  rw [isSortedDesc_iff_getElem]
  intro i hi
  rw [hc]; simp [h L[i] (List.getElem_mem hi)]

lemma isSortedDesc_of_all_true {L : List Bool} (h : ∀ b ∈ L, b = true) : IsSortedDesc L := by
  have hc : L.count true = L.length := by
    induction L with
    | nil => simp
    | cons x xs ih =>
      have hx : x = true := h x (by simp)
      subst hx
      simp [ih (fun b hb => h b (by simp [hb]))]
  rw [isSortedDesc_iff_getElem]
  intro i hi
  rw [hc]; simp [hi, h L[i] (List.getElem_mem hi)]

lemma isBitonic_of_sorted_append_rev {L1 L2 : List Bool} (h1 : IsSortedDesc L1) (h2 : IsSortedDesc L2) :
    IsBitonic (L1 ++ L2.reverse) := by
  let c1 := L1.count true
  let c2 := L2.count true
  have hc1 : c1 ≤ L1.length := count_true_le_length L1
  have hc2 : c2 ≤ L2.length := count_true_le_length L2
  refine ⟨c1, L1.length + (L2.length - c2), by omega, by simp, Or.inl ?_⟩
  conv_lhs => rw [h1, h2]
  rw [List.reverse_append, List.reverse_replicate, List.reverse_replicate]
  simp only [List.length_append, List.length_reverse]
  have h1' : L1.length + (L2.length - c2) - c1 = (L1.length - c1) + (L2.length - c2) := by omega
  have h2' : L1.length + L2.length - (L1.length + (L2.length - c2)) = c2 := by omega
  rw [h1', h2']
  dsimp only [c1, c2]
  rw [List.replicate_add]
  simp only [List.append_assoc]

lemma isBitonic_map_not {L : List Bool} (h : IsBitonic L) : IsBitonic (L.map (!·)) := by
  rcases h with ⟨a, b, hab, hbl, hL | hL⟩
  · refine ⟨a, b, hab, by simp [hbl], Or.inr ?_⟩
    conv_lhs => rw [hL]
    simp [List.map_append, List.map_replicate]
  · refine ⟨a, b, hab, by simp [hbl], Or.inl ?_⟩
    conv_lhs => rw [hL]
    simp [List.map_append, List.map_replicate]

lemma count_true_ofFn_eq (n : ℕ) (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i : Fin n, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    cases f 0 <;> simp [Nat.add_comm]

lemma count_true_ofFn_or_and (h : ℕ) (L : List Bool) (hL : L.length = 2 * h) :
    (List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)).count true +
    (List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)).count true =
    L.count true := by
  rw [count_true_ofFn_eq, count_true_ofFn_eq, ← Finset.sum_add_distrib]
  have hsum : ∑ i : Fin h,
      ((if (L.getD i.1 false || L.getD (i.1 + h) false) then 1 else 0) +
       (if (L.getD i.1 false && L.getD (i.1 + h) false) then 1 else 0)) =
      ∑ i : Fin h, ((if L.getD i.1 false then 1 else 0) + (if L.getD (i.1 + h) false then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    cases L.getD i.1 false <;> cases L.getD (i.1 + h) false <;> rfl
  rw [hsum, Finset.sum_add_distrib]
  have htake : (L.take h).count true = ∑ i : Fin h, if L.getD i.1 false then 1 else 0 := by
    have hEq : L.take h = List.ofFn (fun i : Fin h => L.getD i.1 false) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        have hih : i < h := by simp at hi2; exact hi2
        simp only [List.getElem_take, List.getElem_ofFn, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [hEq, count_true_ofFn_eq]
  have hdrop : (L.drop h).count true = ∑ i : Fin h, if L.getD (i.1 + h) false then 1 else 0 := by
    have hEq : L.drop h = List.ofFn (fun i : Fin h => L.getD (i.1 + h) false) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        have hih : i < h := by simp at hi2; exact hi2
        simp only [List.getElem_drop, List.getElem_ofFn, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega)]
        simp [Nat.add_comm]
    rw [hEq, count_true_ofFn_eq]
  rw [← htake, ← hdrop, ← List.count_append, List.take_append_drop]

lemma bitonic_layer_type1 {h a b : ℕ} (hab : a ≤ b) (hbl : b ≤ 2 * h) :
    let L := List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (2 * h - b) true
    let hi := List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)
    let lo := List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)
    IsBitonic hi ∧ IsBitonic lo ∧
    ((∀ x ∈ lo, x = false) ∨ (∀ x ∈ hi, x = true)) := by
  intro L hi lo
  have hLlen : L.length = 2 * h := by simp [L]; omega
  have hLget : ∀ idx < 2 * h, L.getD idx false = decide (idx < a ∨ b ≤ idx) := by
    intro idx hidx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : idx < L.length)]
    dsimp only [Option.getD_some, L]
    by_cases h1 : idx < a
    · rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_left (by simp; omega)]
      simp [h1]
    · by_cases h2 : idx < b
      · rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_right (by simp; omega)]
        simp [h1, h2]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [h1, (by omega : b ≤ idx)]
  have hget_ext : ∀ (M : List Bool) (a' b' : ℕ), a' ≤ b' → b' ≤ h → M.length = h →
      (∀ i < h, M.getD i false = decide (i < a' ∨ b' ≤ i)) →
      M = List.replicate a' true ++ List.replicate (b' - a') false ++ List.replicate (h - b') true := by
    intro M a' b' ha' hb' hMl hMg
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      have := hMg i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1] at this
      dsimp only [Option.getD_some] at this
      rw [this]
      by_cases h1 : i < a'
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
        simp [h1]
      · by_cases h2 : i < b'
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp [h1, h2]
        · rw [List.getElem_append_right (by simp; omega)]
          simp [h1, (by omega : b' ≤ i)]
  have hget_ext2 : ∀ (M : List Bool) (a' b' : ℕ), a' ≤ b' → b' ≤ h → M.length = h →
      (∀ i < h, M.getD i false = decide (a' ≤ i ∧ i < b')) →
      M = List.replicate a' false ++ List.replicate (b' - a') true ++ List.replicate (h - b') false := by
    intro M a' b' ha' hb' hMl hMg
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      have := hMg i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1] at this
      dsimp only [Option.getD_some] at this
      rw [this]
      by_cases h1 : i < a'
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
        simp [h1]
      · by_cases h2 : i < b'
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp [(by omega : a' ≤ i), h2]
        · rw [List.getElem_append_right (by simp; omega)]
          simp [h2]
  by_cases hba : h ≤ b - a
  ·
    have hloF : ∀ x ∈ lo, x = false := by
      intro x hx
      simp only [lo, List.mem_ofFn] at hx
      rcases hx with ⟨i, rfl⟩
      rw [hLget i.1 (by omega), hLget (i.1 + h) (by omega)]
      have hnot : ¬ ((i.1 < a ∨ b ≤ i.1) ∧ (i.1 + h < a ∨ b ≤ i.1 + h)) := by omega
      cases h1 : decide (i.1 < a ∨ b ≤ i.1) <;> cases h2 : decide (i.1 + h < a ∨ b ≤ i.1 + h)
      · rfl
      · rfl
      · rfl
      · exfalso
        exact hnot ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
    have hlo_eq : lo = List.replicate 0 true ++ List.replicate (h - 0) false ++ List.replicate (h - h) true := by
      apply hget_ext lo 0 h (by omega) le_rfl (by simp [lo])
      intro i hi'
      have hmem : lo.getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]
        exact hloF _ (List.getElem_mem _)
      rw [hmem]; simp; omega
    have hhi_eq : hi = List.replicate a true ++ List.replicate ((b - h) - a) false ++ List.replicate (h - (b - h)) true := by
      apply hget_ext hi a (b - h) (by omega) (by omega) (by simp [hi])
      intro i hi'
      have hgi : hi.getD i false = (L.getD i false || L.getD (i + h) false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]; omega)]
        simp [hi]
      rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    exact ⟨⟨a, b - h, by omega, by simp [hi]; omega, Or.inl (by simpa [hi] using hhi_eq)⟩,
      ⟨0, h, by omega, by simp [lo], Or.inl (by simpa [lo] using hlo_eq)⟩,
      Or.inl hloF⟩
  ·
    have hhiT : ∀ x ∈ hi, x = true := by
      intro x hx
      simp only [hi, List.mem_ofFn] at hx
      rcases hx with ⟨i, rfl⟩
      rw [hLget i.1 (by omega), hLget (i.1 + h) (by omega)]
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      omega
    have hhi_eq : hi = List.replicate h true ++ List.replicate (h - h) false ++ List.replicate (h - h) true := by
      apply hget_ext hi h h le_rfl le_rfl (by simp [hi])
      intro i hi'
      have hmem : hi.getD i false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]; omega)]
        exact hhiT _ (List.getElem_mem _)
      rw [hmem]; simp [hi']
    have hlo_bit : IsBitonic lo := by
      by_cases hbh : b ≤ h
      · refine ⟨a, b, hab, by simp [lo]; omega, Or.inl ?_⟩
        simpa [lo] using hget_ext lo a b hab hbh (by simp [lo]) (fun i hi' => by
          have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
          rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
          apply Bool.eq_iff_iff.2
          simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
      · by_cases hah : h ≤ a
        · refine ⟨a - h, b - h, by omega, by simp [lo]; omega, Or.inl ?_⟩
          simpa [lo] using hget_ext lo (a - h) (b - h) (by omega) (by omega) (by simp [lo]) (fun i hi' => by
            have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
            rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
            apply Bool.eq_iff_iff.2
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
        · refine ⟨b - h, a, by omega, by simp [lo]; omega, Or.inr ?_⟩
          simpa [lo] using hget_ext2 lo (b - h) a (by omega) (by omega) (by simp [lo]) (fun i hi' => by
            have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
            rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
            apply Bool.eq_iff_iff.2
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
    exact ⟨⟨h, h, le_rfl, by simp [hi], Or.inl (by simpa [hi] using hhi_eq)⟩, hlo_bit, Or.inr hhiT⟩

lemma bitonic_layer {h : ℕ} {L : List Bool} (hL : L.length = 2 * h) (hB : IsBitonic L) :
    let hi := List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)
    let lo := List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)
    IsBitonic hi ∧ IsBitonic lo ∧
    ((∀ x ∈ lo, x = false) ∨ (∀ x ∈ hi, x = true)) := by
  rcases hB with ⟨a, b, hab, hbl, hEq | hEq⟩
  · rw [hL] at hbl hEq
    subst hEq
    exact bitonic_layer_type1 hab hbl
  · rw [hL] at hbl hEq
    let L' := List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (2 * h - b) true
    have hLmap : L = L'.map (!·) := by
      rw [hEq]; simp [L', List.map_append, List.map_replicate]
    have h1 := bitonic_layer_type1 hab hbl
    dsimp only at h1 ⊢
    have hL'len : L'.length = 2 * h := by simp [L']; omega
    have hget : ∀ idx < 2 * h, L.getD idx false = !(L'.getD idx false) := by
      intro idx hidx
      rw [hLmap]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hL'len]; omega),
          List.getElem?_eq_getElem (by omega : idx < L'.length)]
      simp
    have hhi_eq : List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) =
        (List.ofFn (fun i : Fin h => L'.getD i.1 false && L'.getD (i.1 + h) false)).map (!·) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn, List.getElem_map]
        rw [hget i (by omega), hget (i + h) (by omega)]
        cases L'.getD i false <;> cases L'.getD (i + h) false <;> rfl
    have hlo_eq : List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false) =
        (List.ofFn (fun i : Fin h => L'.getD i.1 false || L'.getD (i.1 + h) false)).map (!·) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn, List.getElem_map]
        rw [hget i (by omega), hget (i + h) (by omega)]
        cases L'.getD i false <;> cases L'.getD (i + h) false <;> rfl
    rw [hhi_eq, hlo_eq]
    refine ⟨isBitonic_map_not h1.2.1, isBitonic_map_not h1.1, ?_⟩
    rcases h1.2.2 with hloF | hhiT
    · right; intro x hx
      simp only [List.mem_map] at hx; rcases hx with ⟨y, hy, rfl⟩
      rw [hloF y hy]; rfl
    · left; intro x hx
      simp only [List.mem_map] at hx; rcases hx with ⟨y, hy, rfl⟩
      rw [hhiT y hy]; rfl

lemma isSortedDesc_append_of_const {L1 L2 : List Bool}
    (h1 : IsSortedDesc L1) (h2 : IsSortedDesc L2)
    (hconst : (∀ x ∈ L2, x = false) ∨ (∀ x ∈ L1, x = true)) :
    IsSortedDesc (L1 ++ L2) := by
  have hc1 := count_true_le_length L1
  have hc2 := count_true_le_length L2
  rcases hconst with hF | hT
  · have hc20 : L2.count true = 0 := by
      rw [List.count_eq_zero]; intro hm; exact Bool.noConfusion (hF true hm)
    unfold IsSortedDesc at h1 h2 ⊢
    rw [List.count_append, hc20, add_zero, List.length_append]
    conv_lhs => rw [h1, h2]
    rw [hc20]; simp only [List.replicate_zero, List.nil_append, Nat.sub_zero, List.append_assoc]
    rw [← List.replicate_add]
    congr 2; omega
  · have hc1l : L1.count true = L1.length := by
      have hall : ∀ (M : List Bool), (∀ x ∈ M, x = true) → M.count true = M.length := by
        intro M hM
        induction M with
        | nil => simp
        | cons x xs ih =>
          have hx : x = true := hM x (by simp); subst hx
          simp [ih (fun b hb => hM b (by simp [hb]))]
      exact hall L1 hT
    unfold IsSortedDesc at h1 h2 ⊢
    rw [List.count_append, hc1l, List.length_append]
    conv_lhs => rw [h1, h2]
    rw [hc1l]; simp only [Nat.sub_self, List.replicate_zero, List.append_nil, ← List.append_assoc]
    rw [← List.replicate_add]
    have hsub : L1.length + L2.length - (L1.length + L2.count true) = L2.length - L2.count true := by omega
    rw [hsub]

lemma rev_comp_eq (a b : Bool) :
    ((!(a || b)) || (b && !(a && b))) = !a ∧
    ((!(a || b)) || (a && !(a && b))) = !b := by
  cases a <;> cases b <;> decide

lemma exists_comp_layer {m : ℕ} : ∀ (h : ℕ) (gs : List Gate) (as bs : List ℕ),
    GateOK m gs → as.length = h → bs.length = h →
    (∀ w ∈ as, w < m + gs.length) → (∀ w ∈ bs, w < m + gs.length) →
    ∃ (gs1 : List Gate) (hi lo : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + 2 * h ∧
      hi.length = h ∧ lo.length = h ∧
      (∀ w ∈ hi, w < m + gs1.length) ∧ (∀ w ∈ lo, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m →
        hi.map (wVal gs1 inp) = List.ofFn (fun i : Fin h => wVal gs inp (as.getD i.1 0) || wVal gs inp (bs.getD i.1 0)) ∧
        lo.map (wVal gs1 inp) = List.ofFn (fun i : Fin h => wVal gs inp (as.getD i.1 0) && wVal gs inp (bs.getD i.1 0))) ∧
      (∀ (gs2 : List Gate) (cHi cLo : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cHi.length = h → cLo.length = h →
        (∀ w ∈ cHi, w < m + gs2.length) → (∀ w ∈ cLo, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rA rB : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 4 * h ∧
          rA.length = h ∧ rB.length = h ∧
          (∀ w ∈ rA, w < m + gs3.length) ∧ (∀ w ∈ rB, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cHi.map (wVal gs2 inp) = (hi.map (wVal gs1 inp)).map (!·) →
            cLo.map (wVal gs2 inp) = (lo.map (wVal gs1 inp)).map (!·) →
            rA.map (wVal gs3 inp) = (as.map (wVal gs inp)).map (!·) ∧
            rB.map (wVal gs3 inp) = (bs.map (wVal gs inp)).map (!·)) := by
  intro h
  induction h with
  | zero =>
    intro gs as bs hgs has hbs _ _
    cases as; swap; simp at has
    cases bs; swap; simp at hbs
    refine ⟨gs, [], [], Extends.refl gs, hgs, rfl, by omega, rfl, rfl,
      by simp, by simp, fun _ _ => by simp, ?_⟩
    intro gs2 cHi cLo _ hgs2 hcH hcL _ _
    cases cHi; swap; simp at hcH
    cases cLo; swap; simp at hcL
    exact ⟨gs2, [], [], Extends.refl gs2, hgs2, rfl, by omega, rfl, rfl,
      by simp, by simp, fun _ _ _ _ => by simp⟩
  | succ k ih =>
    intro gs as bs hgs has hbs hasW hbsW
    cases as with
    | nil => simp at has
    | cons a as' =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at has hbs
        have ha : a < m + gs.length := hasW a (by simp)
        have hb : b < m + gs.length := hbsW b (by simp)
        obtain ⟨hgsA, hncA, hlenA, hu_lt, hevalA⟩ := mkOr_step hgs ha hb
        let gsA := gs ++ [⟨GateOp.or, [a, b]⟩]
        let u := m + gs.length
        have ha' : a < m + gsA.length := by simp [gsA]; omega
        have hb' : b < m + gsA.length := by simp [gsA]; omega
        obtain ⟨hgsB, hncB, hlenB, hv_lt, hevalB⟩ := mkAnd_step hgsA ha' hb'
        let gsB := gsA ++ [⟨GateOp.and, [a, b]⟩]
        let v := m + gsA.length
        have hext0B : Extends gs gsB := Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩
        have hlen0B : gsB.length = gs.length + 2 := by simp [gsB, gsA]
        obtain ⟨gs1, hi', lo', hextB1, hgs1, hnc1, hlen1, hhi'l, hlo'l, hhi'W, hlo'W, heval1, hrev1⟩ :=
          ih gsB as' bs' hgsB has hbs
            (fun w hw => by have := hasW w (by simp [hw]); omega)
            (fun w hw => by have := hbsW w (by simp [hw]); omega)
        have hext01 : Extends gs gs1 := hext0B.trans hextB1
        have hlenB' : gsB.length = gsA.length + 1 := hlenB
        have hlenA' : gsA.length = gs.length + 1 := hlenA
        have hu_lt1 : u < m + gs1.length := by have := hextB1.length_le; dsimp only [u]; omega
        have hv_lt1 : v < m + gs1.length := by have := hextB1.length_le; dsimp only [v]; omega
        have hnc01 : notCnt gs1 = notCnt gs := by rw [hnc1]; exact hncB.trans hncA
        refine ⟨gs1, u :: hi', v :: lo', hext01, hgs1, hnc01, by omega,
          by simp [hhi'l], by simp [hlo'l],
          fun w hw => by simp at hw; rcases hw with rfl | hw; exact hu_lt1; exact hhi'W w hw,
          fun w hw => by simp at hw; rcases hw with rfl | hw; exact hv_lt1; exact hlo'W w hw,
          ?_, ?_⟩
        · intro inp hinp
          have h1 := heval1 inp hinp
          have hA := hevalA inp hinp
          have hB := hevalB inp hinp
          have hu_val : wVal gs1 inp u = (wVal gs inp a || wVal gs inp b) := by
            have h1' : wVal gs1 inp u = wVal gsB inp u := hextB1.wVal_eq inp (by dsimp only [u]; omega)
            have h2' : wVal gsB inp u = wVal gsA inp u := hB.1 u (by dsimp only [u]; omega)
            rw [h1', h2', hA.2]
          have hv_val : wVal gs1 inp v = (wVal gs inp a && wVal gs inp b) := by
            have h1' : wVal gs1 inp v = wVal gsB inp v := hextB1.wVal_eq inp (by dsimp only [v]; omega)
            rw [h1', hB.2, hA.1 a ha, hA.1 b hb]
          have hsub : ∀ w ∈ as', wVal gsB inp w = wVal gs inp w := fun w hw =>
            hext0B.wVal_eq inp (by have := hasW w (by simp [hw]); omega)
          have hsubB : ∀ w ∈ bs', wVal gsB inp w = wVal gs inp w := fun w hw =>
            hext0B.wVal_eq inp (by have := hbsW w (by simp [hw]); omega)
          constructor
          · rw [List.map_cons, hu_val, h1.1, List.ofFn_succ]
            congr 1
            apply List.ext_getElem (by simp)
            intro i hi1 hi2
            have hik : i < k := by simp at hi1; exact hi1
            simp only [List.getElem_ofFn]
            have ha_mem : as'.getD i 0 ∈ as' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hb_mem : bs'.getD i 0 ∈ bs' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            rw [hsub _ ha_mem, hsubB _ hb_mem]
            simp [List.getD_eq_getElem?_getD]
          · rw [List.map_cons, hv_val, h1.2, List.ofFn_succ]
            congr 1
            apply List.ext_getElem (by simp)
            intro i hi1 hi2
            have hik : i < k := by simp at hi1; exact hi1
            simp only [List.getElem_ofFn]
            have ha_mem : as'.getD i 0 ∈ as' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hb_mem : bs'.getD i 0 ∈ bs' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            rw [hsub _ ha_mem, hsubB _ hb_mem]
            simp [List.getD_eq_getElem?_getD]
        · intro gs2 cHi cLo hext12 hgs2 hcH hcL hcHW hcLW
          cases cHi with
          | nil => simp at hcH
          | cons ub cHi' =>
            cases cLo with
            | nil => simp at hcL
            | cons vb cLo' =>
              simp only [List.length_cons, Nat.add_right_cancel_iff] at hcH hcL
              have hub : ub < m + gs2.length := hcHW ub (by simp)
              have hvb : vb < m + gs2.length := hcLW vb (by simp)
              have hext02 : Extends gs gs2 := hext01.trans hext12
              have ha2 : a < m + gs2.length := by have := hext02.length_le; omega
              have hb2 : b < m + gs2.length := by have := hext02.length_le; omega

              obtain ⟨hg1, hn1, hl1, ht1, he1⟩ := mkAnd_step hgs2 hb2 hvb
              let g1 := gs2 ++ [⟨GateOp.and, [b, vb]⟩]
              let t1 := m + gs2.length
              have hg1l : g1.length = gs2.length + 1 := hl1
              obtain ⟨hg2, hn2, hl2, habar, he2⟩ := mkOr_step hg1 (by omega : ub < m + g1.length) ht1
              let g2 := g1 ++ [⟨GateOp.or, [ub, t1]⟩]
              let abar := m + g1.length
              have hg2l : g2.length = g1.length + 1 := hl2
              obtain ⟨hg3, hn3, hl3, ht2, he3⟩ := mkAnd_step hg2 (by omega : a < m + g2.length) (by omega : vb < m + g2.length)
              let g3 := g2 ++ [⟨GateOp.and, [a, vb]⟩]
              let t2 := m + g2.length
              have hg3l : g3.length = g2.length + 1 := hl3
              obtain ⟨hg4, hn4, hl4, hbbar, he4⟩ := mkOr_step hg3 (by omega : ub < m + g3.length) ht2
              let g4 := g3 ++ [⟨GateOp.or, [ub, t2]⟩]
              let bbar := m + g3.length
              have hg4l : g4.length = g3.length + 1 := hl4
              have hext24 : Extends gs2 g4 :=
                Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩))
              have hlen24 : g4.length = gs2.length + 4 := by omega
              obtain ⟨gs3, rA', rB', hext43, hgs3, hnc3, hlen3, hrAl, hrBl, hrAW, hrBW, hev3⟩ :=
                hrev1 g4 cHi' cLo' (hext12.trans hext24) hg4 hcH hcL
                  (fun w hw => by have := hcHW w (by simp [hw]); omega)
                  (fun w hw => by have := hcLW w (by simp [hw]); omega)
              have hext23 : Extends gs2 gs3 := hext24.trans hext43
              have habar3 : abar < m + gs3.length := by have := hext43.length_le; dsimp only [abar]; omega
              have hbbar3 : bbar < m + gs3.length := by have := hext43.length_le; dsimp only [bbar]; omega
              have hnc23 : notCnt gs3 = notCnt gs2 := by rw [hnc3]; exact hn4.trans (hn3.trans (hn2.trans hn1))
              refine ⟨gs3, abar :: rA', bbar :: rB', hext23, hgs3, hnc23, by omega,
                by simp [hrAl], by simp [hrBl],
                fun w hw => by simp at hw; rcases hw with rfl | hw; exact habar3; exact hrAW w hw,
                fun w hw => by simp at hw; rcases hw with rfl | hw; exact hbbar3; exact hrBW w hw,
                ?_⟩
              intro inp hinp hcHiEq hcLoEq
              simp only [List.map_cons, List.cons.injEq] at hcHiEq hcLoEq
              have hA := hevalA inp hinp
              have hB := hevalB inp hinp
              have hu_val : wVal gs1 inp u = (wVal gs inp a || wVal gs inp b) := by
                rw [hextB1.wVal_eq inp (by dsimp only [u]; omega), hB.1 u (by dsimp only [u]; omega), hA.2]
              have hv_val : wVal gs1 inp v = (wVal gs inp a && wVal gs inp b) := by
                rw [hextB1.wVal_eq inp (by dsimp only [v]; omega), hB.2, hA.1 a ha, hA.1 b hb]
              have hub_val : wVal gs2 inp ub = !(wVal gs inp a || wVal gs inp b) := by
                rw [hcHiEq.1, hu_val]
              have hvb_val : wVal gs2 inp vb = !(wVal gs inp a && wVal gs inp b) := by
                rw [hcLoEq.1, hv_val]
              have ha_val2 : wVal gs2 inp a = wVal gs inp a := hext02.wVal_eq inp (by omega)
              have hb_val2 : wVal gs2 inp b = wVal gs inp b := hext02.wVal_eq inp (by omega)
              have hE1 := he1 inp hinp; have hE2 := he2 inp hinp
              have hE3 := he3 inp hinp; have hE4 := he4 inp hinp
              have habar_val : wVal gs3 inp abar = !(wVal gs inp a) := by
                rw [hext43.wVal_eq inp (by dsimp only [abar]; omega),
                  hE4.1 abar (by dsimp only [abar]; omega), hE3.1 abar (by dsimp only [abar]; omega),
                  hE2.2, hE1.1 ub (by omega), hE1.2, hub_val, hvb_val, hb_val2]
                exact (rev_comp_eq _ _).1
              have hbbar_val : wVal gs3 inp bbar = !(wVal gs inp b) := by
                rw [hext43.wVal_eq inp (by dsimp only [bbar]; omega), hE4.2,
                  hE3.1 ub (by omega), hE2.1 ub (by omega), hE1.1 ub (by omega),
                  hE3.2, hE2.1 a (by omega), hE1.1 a (by omega),
                  hE2.1 vb (by omega), hE1.1 vb (by omega),
                  hub_val, hvb_val, ha_val2]
                exact (rev_comp_eq _ _).2
              have hcHi4 : cHi'.map (wVal g4 inp) = (hi'.map (wVal gs1 inp)).map (!·) := by
                rw [hext24.map_wVal_eq inp cHi' (fun w hw => by have := hcHW w (by simp [hw]); omega)]
                exact hcHiEq.2
              have hcLo4 : cLo'.map (wVal g4 inp) = (lo'.map (wVal gs1 inp)).map (!·) := by
                rw [hext24.map_wVal_eq inp cLo' (fun w hw => by have := hcLW w (by simp [hw]); omega)]
                exact hcLoEq.2
              have hsub3 := hev3 inp hinp hcHi4 hcLo4
              have hmapA : as'.map (wVal gsB inp) = as'.map (wVal gs inp) :=
                hext0B.map_wVal_eq inp as' (fun w hw => by have := hasW w (by simp [hw]); omega)
              have hmapB : bs'.map (wVal gsB inp) = bs'.map (wVal gs inp) :=
                hext0B.map_wVal_eq inp bs' (fun w hw => by have := hbsW w (by simp [hw]); omega)
              rw [hmapA, hmapB] at hsub3
              exact ⟨by rw [List.map_cons, List.map_cons, List.map_cons, habar_val, hsub3.1],
                     by rw [List.map_cons, List.map_cons, List.map_cons, hbbar_val, hsub3.2]⟩

lemma exists_bm {m : ℕ} : ∀ (k : ℕ) (gs : List Gate) (ws : List ℕ),
    GateOK m gs → ws.length = 2 ^ k → (∀ w ∈ ws, w < m + gs.length) →
    ∃ (gs1 : List Gate) (ys : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + k * 2 ^ k ∧
      ys.length = 2 ^ k ∧ (∀ w ∈ ys, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m → IsBitonic (ws.map (wVal gs inp)) →
        IsSortedDesc (ys.map (wVal gs1 inp)) ∧
        (ys.map (wVal gs1 inp)).count true = (ws.map (wVal gs inp)).count true) ∧
      (∀ (gs2 : List Gate) (cs : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cs.length = 2 ^ k → (∀ w ∈ cs, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rs : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 2 * k * 2 ^ k ∧
          rs.length = 2 ^ k ∧ (∀ w ∈ rs, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cs.map (wVal gs2 inp) = (ys.map (wVal gs1 inp)).map (!·) →
            rs.map (wVal gs3 inp) = (ws.map (wVal gs inp)).map (!·)) := by
  intro k
  induction k with
  | zero =>
    intro gs ws hgs hwl hwsW
    refine ⟨gs, ws, Extends.refl gs, hgs, rfl, by simp, hwl, hwsW, ?_, ?_⟩
    · intro inp _ _
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil =>
          refine ⟨?_, rfl⟩
          cases h : wVal gs inp w <;> simp [IsSortedDesc, h]
        | cons _ _ => simp at hwl
    · intro gs2 cs _ hgs2 hcsl hcsW
      exact ⟨gs2, cs, Extends.refl gs2, hgs2, rfl, by simp, hcsl, hcsW, fun inp _ h => h⟩
  | succ k ih =>
    intro gs ws hgs hwl hwsW
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    let h := 2 ^ k
    let wsL := ws.take h
    let wsR := ws.drop h
    have hwsEq : ws = wsL ++ wsR := (List.take_append_drop h ws).symm
    have hLlen : wsL.length = h := by simp [wsL, hwl, hpow, h]
    have hRlen : wsR.length = h := by simp [wsR, hwl, hpow, h]
    obtain ⟨gsA, hi, lo, hext0A, hgsA, hncA, hlenA, hhil, hlol, hhiW, hloW, hevA, hrevA⟩ :=
      exists_comp_layer h gs wsL wsR hgs hLlen hRlen
        (fun w hw => hwsW w (List.mem_of_mem_take hw))
        (fun w hw => hwsW w (List.mem_of_mem_drop hw))
    obtain ⟨gsB, yHi, hextAB, hgsB, hncB, hlenB, hyHil, hyHiW, hevB, hrevB⟩ :=
      ih gsA hi hgsA hhil hhiW
    obtain ⟨gsC, yLo, hextBC, hgsC, hncC, hlenC, hyLol, hyLoW, hevC, hrevC⟩ :=
      ih gsB lo hgsB hlol (fun w hw => by have := hextAB.length_le; have := hloW w hw; omega)
    have hext0C : Extends gs gsC := hext0A.trans (hextAB.trans hextBC)
    have hlenC_bound : gsC.length ≤ gs.length + (k + 1) * 2 ^ (k + 1) := by
      have h1 : (k + 1) * 2 ^ (k + 1) = 2 * h + k * 2 ^ k + k * 2 ^ k := by dsimp only [h]; ring
      omega
    refine ⟨gsC, yHi ++ yLo, hext0C, hgsC, by omega, hlenC_bound,
      by simp [hyHil, hyLol, hpow],
      fun w hw => by
        simp only [List.mem_append] at hw
        rcases hw with hw | hw
        · have := hextBC.length_le; have := hyHiW w hw; omega
        · exact hyLoW w hw,
      ?_, ?_⟩
    · intro inp hinp hBit
      let L := ws.map (wVal gs inp)
      have hLlen' : L.length = 2 * h := by simp [L, hwl, hpow, h]; omega
      have hA := hevA inp hinp
      have hhiEq : hi.map (wVal gsA inp) =
          List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) := by
        rw [hA.1]
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn]
        have h1 : wVal gs inp (wsL.getD i 0) = L.getD i false := by
          simp only [List.getD_eq_getElem?_getD, L, wsL]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow]; omega)]
          simp
        have h2 : wVal gs inp (wsR.getD i 0) = L.getD (i + h) false := by
          simp only [List.getD_eq_getElem?_getD, L, wsR]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega)]
          simp [Nat.add_comm]
        rw [h1, h2]
      have hloEq : lo.map (wVal gsA inp) =
          List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false) := by
        rw [hA.2]
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn]
        have h1 : wVal gs inp (wsL.getD i 0) = L.getD i false := by
          simp only [List.getD_eq_getElem?_getD, L, wsL]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow]; omega)]
          simp
        have h2 : wVal gs inp (wsR.getD i 0) = L.getD (i + h) false := by
          simp only [List.getD_eq_getElem?_getD, L, wsR]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega)]
          simp [Nat.add_comm]
        rw [h1, h2]
      have hlay := bitonic_layer hLlen' hBit
      have hloB : lo.map (wVal gsB inp) = lo.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp lo (fun w hw => by have := hloW w hw; omega)
      have hB := hevB inp hinp (by rw [hhiEq]; exact hlay.1)
      have hC := hevC inp hinp (by rw [hloB, hloEq]; exact hlay.2.1)
      have hyHiC : yHi.map (wVal gsC inp) = yHi.map (wVal gsB inp) :=
        hextBC.map_wVal_eq inp yHi (fun w hw => by have := hyHiW w hw; omega)
      have hcntTot : (yHi.map (wVal gsB inp)).count true + (yLo.map (wVal gsC inp)).count true =
          L.count true := by
        rw [hB.2, hC.2, hloB, hhiEq, hloEq]
        exact count_true_ofFn_or_and h L hLlen'
      rw [List.map_append, hyHiC]
      refine ⟨?_, by rw [List.count_append]; exact hcntTot⟩
      apply isSortedDesc_append_of_const hB.1 hC.1
      rcases hlay.2.2 with hloF | hhiT
      · left
        have hcnt0 : (yLo.map (wVal gsC inp)).count true = 0 := by
          rw [hC.2, hloB, hloEq, List.count_eq_zero]
          intro hm; exact Bool.noConfusion (hloF true hm)
        intro x hx
        cases x
        · rfl
        · exfalso; exact (List.count_eq_zero.1 hcnt0) hx
      · right
        have hcntH : (yHi.map (wVal gsB inp)).count true = (yHi.map (wVal gsB inp)).length := by
          rw [hB.2, hhiEq, List.length_map, hyHil]
          have hc : (List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)).count true = h := by
            have hall : List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) = List.replicate h true := by
              apply List.ext_getElem (by simp)
              intro i hi1 hi2
              simp only [List.getElem_replicate]
              exact hhiT _ (List.getElem_mem hi1)
            rw [hall]; simp
          exact hc
        intro x hx
        cases x
        · exfalso
          have h1 := hB.1
          unfold IsSortedDesc at h1
          rw [hcntH, Nat.sub_self, List.replicate_zero, List.append_nil] at h1
          rw [h1] at hx; simp at hx
        · rfl
    · intro gs2 cs hextC2 hgs2 hcsl hcsW
      let cHi := cs.take h
      let cLo := cs.drop h
      have hcHil : cHi.length = h := by simp [cHi, hcsl, hpow, h]
      have hcLol : cLo.length = h := by simp [cLo, hcsl, hpow, h]
      obtain ⟨gs3, rHi, hext23, hgs3, hnc3, hlen3, hrHil, hrHiW, hev3⟩ :=
        hrevB gs2 cHi (hextBC.trans hextC2) hgs2 hcHil
          (fun w hw => hcsW w (List.mem_of_mem_take hw))
      obtain ⟨gs4, rLo, hext34, hgs4, hnc4, hlen4, hrLol, hrLoW, hev4⟩ :=
        hrevC gs3 cLo (hextC2.trans hext23) hgs3 hcLol
          (fun w hw => by have := hext23.length_le; have := hcsW w (List.mem_of_mem_drop hw); omega)
      obtain ⟨gs5, rL, rR, hext45, hgs5, hnc5, hlen5, hrLl, hrRl, hrLW, hrRW, hev5⟩ :=
        hrevA gs4 rHi rLo (hextAB.trans (hextBC.trans (hextC2.trans (hext23.trans hext34)))) hgs4 hrHil hrLol
          (fun w hw => by have := hext34.length_le; have := hrHiW w hw; omega)
          hrLoW
      have hext25 : Extends gs2 gs5 := hext23.trans (hext34.trans hext45)
      have hlen5_bound : gs5.length ≤ gs2.length + 2 * (k + 1) * 2 ^ (k + 1) := by
        have h1 : 2 * (k + 1) * 2 ^ (k + 1) = 4 * h + 2 * k * 2 ^ k + 2 * k * 2 ^ k := by dsimp only [h]; ring
        omega
      refine ⟨gs5, rL ++ rR, hext25, hgs5, by omega, hlen5_bound,
        by simp [hrLl, hrRl, hpow, h],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · exact hrLW w hw
          · exact hrRW w hw,
        ?_⟩
      intro inp hinp hcsEq
      rw [List.map_append, List.map_append] at hcsEq
      have hcsEq2 : cHi.map (wVal gs2 inp) ++ cLo.map (wVal gs2 inp) =
          (yHi.map (wVal gsC inp)).map (!·) ++ (yLo.map (wVal gsC inp)).map (!·) := by
        rw [← List.map_append, List.take_append_drop]; exact hcsEq
      have hspl := List.append_inj hcsEq2 (by simp [hcHil, hyHil, h])
      have hyHiC : yHi.map (wVal gsC inp) = yHi.map (wVal gsB inp) :=
        hextBC.map_wVal_eq inp yHi (fun w hw => by have := hyHiW w hw; omega)
      have hrHiEq : rHi.map (wVal gs3 inp) = (hi.map (wVal gsA inp)).map (!·) :=
        hev3 inp hinp (by rw [← hyHiC]; exact hspl.1)
      have hcLo3 : cLo.map (wVal gs3 inp) = (yLo.map (wVal gsC inp)).map (!·) := by
        rw [hext23.map_wVal_eq inp cLo (fun w hw => by have := hcsW w (List.mem_of_mem_drop hw); omega)]
        exact hspl.2
      have hrLoEq : rLo.map (wVal gs4 inp) = (lo.map (wVal gsA inp)).map (!·) := by
        have h := hev4 inp hinp hcLo3
        rw [hextAB.map_wVal_eq inp lo (fun w hw => by have := hloW w hw; omega)] at h
        exact h
      have hrHi4 : rHi.map (wVal gs4 inp) = (hi.map (wVal gsA inp)).map (!·) := by
        rw [hext34.map_wVal_eq inp rHi (fun w hw => by have := hrHiW w hw; omega)]
        exact hrHiEq
      have h5 := hev5 inp hinp hrHi4 hrLoEq
      rw [List.map_append, h5.1, h5.2, ← List.map_append, ← List.map_append, List.take_append_drop]

lemma win_merge_step (K m A B t : ℕ) (ht : t < m) (hB : B ≤ m) :
    let cA := if K ≤ A then 2 * m else if A + 2 * m ≤ K then 0 else A + 2 * m - K
    decide (m + t < cA + B) = decide (K + 1 + t ≤ A + B + m) := by
  dsimp only
  split_ifs <;> simp only [decide_eq_decide] <;> omega

lemma count_win_spec (K s A : ℕ) (L : List Bool) (hL : L.length = s)
    (hget : ∀ (t : ℕ) (ht : t < s), L[t]'(by omega) = decide (K + 1 + t ≤ A + s)) :
    IsSortedDesc L ∧
    L.count true = if K ≤ A then s else if A + s ≤ K then 0 else A + s - K := by
  let c := if K ≤ A then s else if A + s ≤ K then 0 else A + s - K
  have hc_le : c ≤ s := by dsimp only [c]; split_ifs <;> omega
  have hiff : ∀ t < s, (K + 1 + t ≤ A + s) ↔ t < c := by
    intro t ht; dsimp only [c]; split_ifs <;> omega
  have hEq : L = List.replicate c true ++ List.replicate (s - c) false := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      rw [hget i (by omega)]
      by_cases hic : i < c
      · rw [List.getElem_append_left (by simp [hic])]
        simp [(hiff i (by omega)).2 hic]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [show ¬ (K + 1 + i ≤ A + s) from fun h => hic ((hiff i (by omega)).1 h)]
  have hcnt : L.count true = c := by rw [hEq]; simp [List.count_replicate]
  refine ⟨?_, hcnt⟩
  unfold IsSortedDesc
  rw [hcnt, hL]; exact hEq

lemma exists_sort_full {m : ℕ} (wF : ℕ) (hwF : wF < m) : ∀ (k : ℕ) (gs : List Gate) (ws : List ℕ),
    GateOK m gs → ws.length = 2 ^ k → (∀ w ∈ ws, w < m + gs.length) →
    ∃ (gs1 : List Gate) (ys : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + k * (k + 1) * 2 ^ k ∧
      ys.length = 2 ^ k ∧ (∀ w ∈ ys, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m →
        IsSortedDesc (ys.map (wVal gs1 inp)) ∧
        (ys.map (wVal gs1 inp)).count true = (ws.map (wVal gs inp)).count true) ∧
      (∀ (gs2 : List Gate) (cs : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cs.length = 2 ^ k → (∀ w ∈ cs, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rs : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 2 * k * (k + 1) * 2 ^ k ∧
          rs.length = 2 ^ k ∧ (∀ w ∈ rs, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cs.map (wVal gs2 inp) = (ys.map (wVal gs1 inp)).map (!·) →
            rs.map (wVal gs3 inp) = (ws.map (wVal gs inp)).map (!·)) ∧
      (∀ (K : ℕ) (gs2 : List Gate) (win : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → win.length = 2 ^ k → (∀ w ∈ win, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (leaves : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 4 * k * (k + 2) * 2 ^ k ∧
          leaves.length = 2 ^ k ∧ (∀ w ∈ leaves, w < m + gs3.length) ∧
          ∀ (inp : List Bool) (A : ℕ), inp.length = m → inp.getD wF false = false →
            (∀ t < 2 ^ k, wVal gs2 inp (win.getD t 0) = decide (K + 1 + t ≤ A + 2 ^ k)) →
            ∀ j < 2 ^ k,
              wVal gs3 inp (leaves.getD j 0) =
              decide (K ≤ A + ((ws.map (wVal gs inp)).count true -
                if wVal gs inp (ws.getD j 0) then 1 else 0))) := by
  intro k
  induction k with
  | zero =>
    intro gs ws hgs hwl hwsW
    refine ⟨gs, ws, Extends.refl gs, hgs, rfl, by simp, hwl, hwsW, ?_, ?_, ?_⟩
    · intro inp _
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil => refine ⟨by cases h : wVal gs inp w <;> simp [IsSortedDesc, h], rfl⟩
        | cons _ _ => simp at hwl
    · intro gs2 cs _ hgs2 hcsl hcsW
      exact ⟨gs2, cs, Extends.refl gs2, hgs2, rfl, by simp, hcsl, hcsW, fun _ _ h => h⟩
    · intro K gs2 win _ hgs2 hwinl hwinW
      refine ⟨gs2, win, Extends.refl gs2, hgs2, rfl, by simp, hwinl, hwinW, ?_⟩
      intro inp A _ _ hwinSpec j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have h0 := hwinSpec 0 (by omega)
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil =>
          rw [h0]
          cases h : wVal gs inp w <;> simp [h]
        | cons _ _ => simp at hwl
  | succ k ih =>
    intro gs ws hgs hwl hwsW
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    let h := 2 ^ k
    let wsL := ws.take h
    let wsR := ws.drop h
    have hLlen : wsL.length = h := by simp [wsL, hwl, hpow, h]
    have hRlen : wsR.length = h := by simp [wsR, hwl, hpow, h]
    obtain ⟨gsA, ysL, hext0A, hgsA, hncA, hlenA, hyLl, hyLW, hevA, hrevA, hwinA⟩ :=
      ih gs wsL hgs hLlen (fun w hw => hwsW w (List.mem_of_mem_take hw))
    obtain ⟨gsB, ysR, hextAB, hgsB, hncB, hlenB, hyRl, hyRW, hevB, hrevB, hwinB⟩ :=
      ih gsA wsR hgsA hRlen
        (fun w hw => by have := hext0A.length_le; have := hwsW w (List.mem_of_mem_drop hw); omega)
    obtain ⟨gsC, ys, hextBC, hgsC, hncC, hlenC, hysl, hysW, hevC, hrevC⟩ :=
      exists_bm (k + 1) gsB (ysL ++ ysR.reverse) hgsB
        (by simp [hyLl, hyRl, hpow])
        (fun w hw => by
          simp only [List.mem_append, List.mem_reverse] at hw
          rcases hw with hw | hw
          · have := hextAB.length_le; have := hyLW w hw; omega
          · exact hyRW w hw)
    have hext0B : Extends gs gsB := hext0A.trans hextAB
    have hext0C : Extends gs gsC := hext0B.trans hextBC
    have hlenC_bound : gsC.length ≤ gs.length + (k + 1) * (k + 2) * 2 ^ (k + 1) := by
      have h1 : (k + 1) * (k + 2) * 2 ^ (k + 1) =
          k * (k + 1) * 2 ^ k + k * (k + 1) * 2 ^ k + (k + 1) * 2 ^ (k + 1) + 2 * (k + 1) * 2 ^ k := by
        ring
      omega
    refine ⟨gsC, ys, hext0C, hgsC, by omega, hlenC_bound, hysl, hysW, ?_, ?_, ?_⟩
    · intro inp hinp
      have hA := hevA inp hinp
      have hB := hevB inp hinp
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      have hyLB : ysL.map (wVal gsB inp) = ysL.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
      have hBit : IsBitonic ((ysL ++ ysR.reverse).map (wVal gsB inp)) := by
        rw [List.map_append, List.map_reverse, hyLB]
        exact isBitonic_of_sorted_append_rev hA.1 hB.1
      have hC := hevC inp hinp hBit
      refine ⟨hC.1, ?_⟩
      rw [hC.2, List.map_append, List.map_reverse, hyLB, List.count_append, List.count_reverse,
        hA.2, hB.2, hwsRA, ← List.count_append, ← List.map_append, List.take_append_drop]
    · intro gs2 cs hextC2 hgs2 hcsl hcsW
      obtain ⟨gs3, cBit, hext23, hgs3, hnc3, hlen3, hcBitl, hcBitW, hev3⟩ :=
        hrevC gs2 cs hextC2 hgs2 hcsl hcsW
      let cL := cBit.take h
      let cR := (cBit.drop h).reverse
      have hcLl : cL.length = h := by simp [cL, hcBitl, hpow, h]
      have hcRl : cR.length = h := by simp [cR, hcBitl, hpow, h]
      obtain ⟨gs4, rL, hext34, hgs4, hnc4, hlen4, hrLl, hrLW, hev4⟩ :=
        hrevA gs3 cL (hextAB.trans (hextBC.trans (hextC2.trans hext23))) hgs3 hcLl
          (fun w hw => hcBitW w (List.mem_of_mem_take hw))
      obtain ⟨gs5, rR, hext45, hgs5, hnc5, hlen5, hrRl, hrRW, hev5⟩ :=
        hrevB gs4 cR (hextBC.trans (hextC2.trans (hext23.trans hext34))) hgs4 hcRl
          (fun w hw => by
            have := hext34.length_le
            have := hcBitW w (List.mem_of_mem_drop (List.mem_reverse.1 hw)); omega)
      have hext25 : Extends gs2 gs5 := hext23.trans (hext34.trans hext45)
      have hlen5_bound : gs5.length ≤ gs2.length + 2 * (k + 1) * (k + 2) * 2 ^ (k + 1) := by
        have h1 : 2 * (k + 1) * (k + 2) * 2 ^ (k + 1) =
            2 * (k + 1) * 2 ^ (k + 1) + 2 * k * (k + 1) * 2 ^ k + 2 * k * (k + 1) * 2 ^ k +
            4 * (k + 1) * 2 ^ k := by
          ring
        omega
      refine ⟨gs5, rL ++ rR, hext25, hgs5, by omega, hlen5_bound,
        by simp [hrLl, hrRl, hpow],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · have := hext45.length_le; have := hrLW w hw; omega
          · exact hrRW w hw,
        ?_⟩
      intro inp hinp hcsEq
      have h3 := hev3 inp hinp hcsEq
      rw [List.map_append, List.map_reverse, List.map_append, List.map_reverse] at h3
      have h3' : cL.map (wVal gs3 inp) ++ (cBit.drop h).map (wVal gs3 inp) =
          (ysL.map (wVal gsB inp)).map (!·) ++ ((ysR.map (wVal gsB inp)).map (!·)).reverse := by
        rw [← List.map_append, List.take_append_drop]; exact h3
      have hspl := List.append_inj h3' (by simp [hcLl, hyLl, h])
      have hyLB : ysL.map (wVal gsB inp) = ysL.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
      have h4 := hev4 inp hinp (by rw [← hyLB]; exact hspl.1)
      have hcR4 : cR.map (wVal gs4 inp) = (ysR.map (wVal gsB inp)).map (!·) := by
        rw [hext34.map_wVal_eq inp cR (fun w hw => by
          have := hcBitW w (List.mem_of_mem_drop (List.mem_reverse.1 hw)); omega)]
        simp only [cR, List.map_reverse]
        rw [hspl.2, List.reverse_reverse]
      have h5 := hev5 inp hinp hcR4
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      rw [hwsRA] at h5
      have hrL5 : rL.map (wVal gs5 inp) = rL.map (wVal gs4 inp) :=
        hext45.map_wVal_eq inp rL (fun w hw => by have := hrLW w hw; omega)
      rw [List.map_append, hrL5, h4, h5, ← List.map_append, ← List.map_append, List.take_append_drop]
    · intro K gs2 win hextC2 hgs2 hwinl hwinW
      have hpow2 : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      have hextB2 : Extends gsB gs2 := hextBC.trans hextC2
      have hextA2 : Extends gsA gs2 := hextAB.trans hextB2
      let padR := ysR ++ List.replicate h wF
      let padL := ysL ++ List.replicate h wF
      have hpadRl : padR.length = 2 ^ (k + 1) := by simp [padR, hyRl, hpow, h]
      have hpadLl : padL.length = 2 ^ (k + 1) := by simp [padL, hyLl, hpow, h]

      obtain ⟨gs3, mL, hext23, hgs3, hnc3, hlen3, hmLl, hmLW, hev3, _⟩ :=
        exists_bm (k + 2) gs2 (win ++ padR.reverse) hgs2
          (by simp [hwinl, hpadRl, hpow2])
          (fun w hw => by
            simp only [List.mem_append, List.mem_reverse, padR, List.mem_replicate] at hw
            rcases hw with hw | (hw | ⟨_, rfl⟩)
            · exact hwinW w hw
            · have := hextB2.length_le; have := hyRW w hw; omega
            · omega)

      obtain ⟨gs4, mR, hext34, hgs4, hnc4, hlen4, hmRl, hmRW, hev4, _⟩ :=
        exists_bm (k + 2) gs3 (win ++ padL.reverse) hgs3
          (by simp [hwinl, hpadLl, hpow2])
          (fun w hw => by
            simp only [List.mem_append, List.mem_reverse, padL, List.mem_replicate] at hw
            rcases hw with hw | (hw | ⟨_, rfl⟩)
            · have := hext23.length_le; have := hwinW w hw; omega
            · have := hext23.length_le; have := hextA2.length_le; have := hyLW w hw; omega
            · omega)
      let winForL := (mL.drop h).take h
      let winForR := (mR.drop h).take h
      have hwfLl : winForL.length = h := by simp [winForL, hmLl, hpow2, hpow, h]; omega
      have hwfRl : winForR.length = h := by simp [winForR, hmRl, hpow2, hpow, h]; omega
      obtain ⟨gs5, leavesL, hext45, hgs5, hnc5, hlen5, hlLl, hlLW, hev5⟩ :=
        hwinA K gs4 winForL (hextA2.trans (hext23.trans hext34)) hgs4 hwfLl
          (fun w hw => by
            have := hext34.length_le
            have := hmLW w (List.mem_of_mem_drop (List.mem_of_mem_take hw)); omega)
      obtain ⟨gs6, leavesR, hext56, hgs6, hnc6, hlen6, hlRl, hlRW, hev6⟩ :=
        hwinB K gs5 winForR (hextB2.trans (hext23.trans (hext34.trans hext45))) hgs5 hwfRl
          (fun w hw => by
            have := hext45.length_le
            have := hmRW w (List.mem_of_mem_drop (List.mem_of_mem_take hw)); omega)
      have hext26 : Extends gs2 gs6 := hext23.trans (hext34.trans (hext45.trans hext56))
      have hlen6_bound : gs6.length ≤ gs2.length + 4 * (k + 1) * (k + 3) * 2 ^ (k + 1) := by
        have h1 : 4 * (k + 1) * (k + 3) * 2 ^ (k + 1) =
            (k + 2) * 2 ^ (k + 2) + (k + 2) * 2 ^ (k + 2) +
            4 * k * (k + 2) * 2 ^ k + 4 * k * (k + 2) * 2 ^ k + 8 * (k + 1) * 2 ^ k := by
          ring
        omega
      refine ⟨gs6, leavesL ++ leavesR, hext26, hgs6, by omega, hlen6_bound,
        by simp [hlLl, hlRl, hpow],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · have := hext56.length_le; have := hlLW w hw; omega
          · exact hlRW w hw,
        ?_⟩
      intro inp A hinp hwFval hwinSpec j hj
      have hA_sort := hevA inp hinp
      have hB_sort := hevB inp hinp
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      have hcntW : (ws.map (wVal gs inp)).count true =
          (wsL.map (wVal gs inp)).count true + (wsR.map (wVal gs inp)).count true := by
        rw [← List.count_append, ← List.map_append, List.take_append_drop]
      have hwin_s := count_win_spec K (2 ^ (k + 1)) A (win.map (wVal gs2 inp)) (by simp [hwinl])
        (fun t ht => by
          have h1 := hwinSpec t ht
          simp only [List.getD_eq_getElem?_getD] at h1
          rw [List.getElem?_eq_getElem (by omega : t < win.length)] at h1
          simpa using h1)
      have hwF2 : wVal gs2 inp wF = false := by rw [evalWires_input gs2 inp (by omega), hwFval]
      have hwF3 : wVal gs3 inp wF = false := by rw [evalWires_input gs3 inp (by omega), hwFval]

      have hpadR_s : IsSortedDesc (padR.map (wVal gs2 inp)) ∧
          (padR.map (wVal gs2 inp)).count true = (wsR.map (wVal gs inp)).count true := by
        have hyR2 : ysR.map (wVal gs2 inp) = ysR.map (wVal gsB inp) :=
          hextB2.map_wVal_eq inp ysR (fun w hw => by have := hyRW w hw; omega)
        rw [List.map_append, hyR2, List.map_replicate, hwF2]
        refine ⟨isSortedDesc_append_of_const hB_sort.1
            (isSortedDesc_of_all_false (fun x hx => (List.mem_replicate.1 hx).2))
            (Or.inl (fun x hx => (List.mem_replicate.1 hx).2)), ?_⟩
        simp [List.count_replicate, hB_sort.2, hwsRA]
      have hmL_s := hev3 inp hinp (by
        rw [List.map_append, List.map_reverse]
        exact isBitonic_of_sorted_append_rev hwin_s.1 hpadR_s.1)
      have hmL_cnt : (mL.map (wVal gs3 inp)).count true =
          (if K ≤ A then 2 * h else if A + 2 * h ≤ K then 0 else A + 2 * h - K) +
          (wsR.map (wVal gs inp)).count true := by
        rw [hmL_s.2, List.map_append, List.map_reverse, List.count_append, List.count_reverse,
          hwin_s.2, hpadR_s.2]
        have : 2 ^ (k + 1) = 2 * h := by dsimp only [h]; ring
        rw [this]
      have hwfL_spec : ∀ t < h,
          wVal gs4 inp (winForL.getD t 0) =
          decide (K + 1 + t ≤ (A + (wsR.map (wVal gs inp)).count true) + h) := by
        intro t ht
        have hgt : winForL.getD t 0 = mL[h + t]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < winForL.length)]
          simp [winForL, List.getElem_take, List.getElem_drop]
        rw [hgt]
        have hwmem : mL[h + t]'(by omega) ∈ mL := List.getElem_mem _
        rw [hext34.wVal_eq inp (by have := hmLW _ hwmem; omega)]
        have hgetM := getElem_isSortedDesc hmL_s.1 (i := h + t) (by simp [hmLl, hpow2, hpow, h]; omega)
        simp only [List.getElem_map] at hgetM
        rw [hgetM, hmL_cnt]
        have hBle : (wsR.map (wVal gs inp)).count true ≤ h := by
          have := count_true_le_length (wsR.map (wVal gs inp)); simpa [hRlen] using this
        exact win_merge_step K h A _ t ht hBle

      have hwin3 : win.map (wVal gs3 inp) = win.map (wVal gs2 inp) :=
        hext23.map_wVal_eq inp win (fun w hw => by have := hwinW w hw; omega)
      have hpadL_s : IsSortedDesc (padL.map (wVal gs3 inp)) ∧
          (padL.map (wVal gs3 inp)).count true = (wsL.map (wVal gs inp)).count true := by
        have hyL3 : ysL.map (wVal gs3 inp) = ysL.map (wVal gsA inp) :=
          (hextA2.trans hext23).map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
        rw [List.map_append, hyL3, List.map_replicate, hwF3]
        refine ⟨isSortedDesc_append_of_const hA_sort.1
            (isSortedDesc_of_all_false (fun x hx => (List.mem_replicate.1 hx).2))
            (Or.inl (fun x hx => (List.mem_replicate.1 hx).2)), ?_⟩
        simp [List.count_replicate, hA_sort.2]
      have hmR_s := hev4 inp hinp (by
        rw [List.map_append, List.map_reverse, hwin3]
        exact isBitonic_of_sorted_append_rev hwin_s.1 hpadL_s.1)
      have hmR_cnt : (mR.map (wVal gs4 inp)).count true =
          (if K ≤ A then 2 * h else if A + 2 * h ≤ K then 0 else A + 2 * h - K) +
          (wsL.map (wVal gs inp)).count true := by
        rw [hmR_s.2, List.map_append, List.map_reverse, hwin3, List.count_append, List.count_reverse,
          hwin_s.2, hpadL_s.2]
        have : 2 ^ (k + 1) = 2 * h := by dsimp only [h]; ring
        rw [this]
      have hwfR_spec : ∀ t < h,
          wVal gs5 inp (winForR.getD t 0) =
          decide (K + 1 + t ≤ (A + (wsL.map (wVal gs inp)).count true) + h) := by
        intro t ht
        have hgt : winForR.getD t 0 = mR[h + t]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < winForR.length)]
          simp [winForR, List.getElem_take, List.getElem_drop]
        rw [hgt]
        have hwmem : mR[h + t]'(by omega) ∈ mR := List.getElem_mem _
        rw [hext45.wVal_eq inp (by have := hmRW _ hwmem; omega)]
        have hgetM := getElem_isSortedDesc hmR_s.1 (i := h + t) (by simp [hmRl, hpow2, hpow, h]; omega)
        simp only [List.getElem_map] at hgetM
        rw [hgetM, hmR_cnt]
        have hBle : (wsL.map (wVal gs inp)).count true ≤ h := by
          have := count_true_le_length (wsL.map (wVal gs inp)); simpa [hLlen] using this
        exact win_merge_step K h A _ t ht hBle
      by_cases hjh : j < h
      · have hgetL : (leavesL ++ leavesR).getD j 0 = leavesL.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < leavesL.length)]
        rw [hgetL]
        have hmemL : leavesL.getD j 0 ∈ leavesL := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext56.wVal_eq inp (by have := hlLW _ hmemL; omega)]
        rw [hev5 inp (A + (wsR.map (wVal gs inp)).count true) hinp hwFval hwfL_spec j hjh]
        have hwsj : wsL.getD j 0 = ws.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem (by omega : j < wsL.length),
              List.getElem?_eq_getElem (by omega : j < ws.length)]
          simp [wsL, List.getElem_take]
        rw [hwsj, hcntW]
        have h1 : (if wVal gs inp (ws.getD j 0) then 1 else 0) ≤ (wsL.map (wVal gs inp)).count true := by
          cases hb : wVal gs inp (ws.getD j 0)
          · simp
          · simp only [↓reduceIte]
            have hmemL' : wsL.getD j 0 ∈ wsL := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hmem : true ∈ wsL.map (wVal gs inp) := by
              rw [← hb, ← hwsj]; exact List.mem_map_of_mem hmemL'
            exact List.count_pos_iff.2 hmem
        simp only [decide_eq_decide]; omega
      · have hgetR : (leavesL ++ leavesR).getD j 0 = leavesR.getD (j - h) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : leavesL.length ≤ j)]
          congr 2; omega
        rw [hgetR]
        rw [hev6 inp (A + (wsL.map (wVal gs inp)).count true) hinp hwFval hwfR_spec (j - h) (by omega)]
        have hwsj : wsR.getD (j - h) 0 = ws.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem (by omega : j - h < wsR.length),
              List.getElem?_eq_getElem (by omega : j < ws.length)]
          simp only [wsR, List.getElem_drop, Option.getD_some]
          congr 1; omega
        rw [hwsj, hwsRA, hcntW]
        have hmem_ws : ws.getD j 0 ∈ ws := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hwr : wVal gsA inp (ws.getD j 0) = wVal gs inp (ws.getD j 0) :=
          hext0A.wVal_eq inp (by have := hwsW _ hmem_ws; omega)
        rw [hwr]
        have h1 : (if wVal gs inp (ws.getD j 0) then 1 else 0) ≤ (wsR.map (wVal gs inp)).count true := by
          cases hb : wVal gs inp (ws.getD j 0)
          · simp
          · simp only [↓reduceIte]
            have hmemR' : wsR.getD (j - h) 0 ∈ wsR := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hmem : true ∈ wsR.map (wVal gs inp) := by
              rw [← hb, ← hwsj]; exact List.mem_map_of_mem hmemR'
            exact List.count_pos_iff.2 hmem
        simp only [decide_eq_decide]; omega

def codeSet {q n : ℕ} (z : Finset (Fin q)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    i.val = 2 * q + 2 ∨
    (i.val / 2 < q ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
    (i.val / 2 = q ∧ i.val % 2 = z.card % 2)

def codeElem {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) (j : Fin (q + 2)) : Fin n :=
  if hj : j.val < q then
    ⟨2 * j.val + (if (⟨j.val, hj⟩ : Fin q) ∈ z then 1 else 0), by split_ifs <;> omega⟩
  else if j.val = q then
    ⟨2 * q + z.card % 2, by omega⟩
  else
    ⟨2 * q + 2, by omega⟩

lemma codeElem_div_two {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) (j : Fin (q + 2)) :
    (codeElem hn z j).val / 2 = j.val := by
  unfold codeElem
  split_ifs with h1 h2
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only; omega

lemma codeElem_injective {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    Function.Injective (codeElem hn z) := by
  intro j1 j2 h
  have h1 := codeElem_div_two hn z j1
  have h2 := codeElem_div_two hn z j2
  rw [h] at h1
  exact Fin.ext (h1.symm.trans h2)

lemma codeElem_mem_codeSet {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) (j : Fin (q + 2)) :
    codeElem hn z j ∈ codeSet z := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold codeElem
  by_cases h1 : j.val < q
  · simp only [h1, ↓reduceDIte]
    by_cases h2 : (⟨j.val, h1⟩ : Fin q) ∈ z
    · simp only [h2, ↓reduceIte]
      right; left
      have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
      have hmod : (2 * j.val + 1) % 2 = 1 := by omega
      rw [hdiv, hmod]
      refine ⟨h1, ?_⟩
      have hex : ∃ t ∈ z, t.val = j.val := ⟨⟨j.val, h1⟩, h2, rfl⟩
      simp [hex]
    · simp only [h2, ↓reduceIte]
      right; left
      have hdiv : (2 * j.val + 0) / 2 = j.val := by omega
      have hmod : (2 * j.val + 0) % 2 = 0 := by omega
      rw [hdiv, hmod]
      refine ⟨h1, ?_⟩
      have hnex : ¬ ∃ t ∈ z, t.val = j.val := by
        rintro ⟨t, ht, htv⟩
        have hteq : t = ⟨j.val, h1⟩ := Fin.ext htv
        subst hteq; exact h2 ht
      simp [hnex]
  · simp only [h1, ↓reduceDIte]
    by_cases h2 : j.val = q
    · simp only [h2, ↓reduceIte]
      right; right
      constructor <;> omega
    · simp only [h2, ↓reduceIte]
      left; trivial

lemma codeSet_eq_image {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (codeSet z : Finset (Fin n)) = Finset.univ.image (codeElem hn z) := by
  ext i
  constructor
  · intro hi
    simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rcases hi with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨⟨q + 1, by omega⟩, Fin.ext ?_⟩
      unfold codeElem
      simp [h1]
    · refine ⟨⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
      unfold codeElem
      simp only [h1, ↓reduceDIte]
      have hiff : (⟨i.val / 2, h1⟩ : Fin q) ∈ z ↔ ∃ t ∈ z, t.val = i.val / 2 := by
        constructor
        · intro h; exact ⟨⟨i.val / 2, h1⟩, h, rfl⟩
        · rintro ⟨t, ht, htv⟩; have hteq : t = ⟨i.val / 2, h1⟩ := Fin.ext htv; subst hteq; exact ht
      by_cases hm : (⟨i.val / 2, h1⟩ : Fin q) ∈ z
      · have hm2 : ∃ t ∈ z, t.val = i.val / 2 := hiff.1 hm
        simp only [hm2, ↓reduceIte] at h2
        simp only [hm, ↓reduceIte]; omega
      · have hm2 : ¬ ∃ t ∈ z, t.val = i.val / 2 := fun h => hm (hiff.2 h)
        simp only [hm2, ↓reduceIte] at h2
        simp only [hm, ↓reduceIte]; omega
    · refine ⟨⟨q, by omega⟩, Fin.ext ?_⟩
      unfold codeElem
      simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte]
      omega
  · intro hi
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
    rcases hi with ⟨j, rfl⟩
    exact codeElem_mem_codeSet hn z j

lemma card_codeSet {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (codeSet (n := n) z).card = q + 2 := by
  rw [codeSet_eq_image hn z, Finset.card_image_of_injective _ (codeElem_injective hn z),
    Finset.card_univ, Fintype.card_fin]

lemma mem_codeSet_data_even {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) (t : Fin q) :
    (⟨2 * t.val, by omega⟩ : Fin n) ∈ codeSet z ↔ t ∉ z := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : 2 * t.val ≠ 2 * q + 2 := by omega
  have h2 : 2 * t.val / 2 = t.val := by omega
  have h3 : 2 * t.val % 2 = 0 := by omega
  have h4 : t.val ≠ q := by omega
  simp only [h1, h2, h3, h4, t.isLt, true_and, false_or, false_and, or_false]
  have hiff : (∃ u ∈ z, u.val = t.val) ↔ t ∈ z := by
    constructor
    · rintro ⟨u, hu, huv⟩; have hueq : u = t := Fin.ext huv; subst hueq; exact hu
    · intro h; exact ⟨t, h, rfl⟩
  split_ifs with h
  · simp [hiff.1 h]
  · simp [show t ∉ z from fun ht => h (hiff.2 ht)]

lemma mem_codeSet_data_odd {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) (t : Fin q) :
    (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ codeSet z ↔ t ∈ z := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : 2 * t.val + 1 ≠ 2 * q + 2 := by omega
  have h2 : (2 * t.val + 1) / 2 = t.val := by omega
  have h3 : (2 * t.val + 1) % 2 = 1 := by omega
  have h4 : t.val ≠ q := by omega
  simp only [h1, h2, h3, h4, t.isLt, true_and, false_or, false_and, or_false]
  have hiff : (∃ u ∈ z, u.val = t.val) ↔ t ∈ z := by
    constructor
    · rintro ⟨u, hu, huv⟩; have hueq : u = t := Fin.ext huv; subst hueq; exact hu
    · intro h; exact ⟨t, h, rfl⟩
  split_ifs with h
  · simp [hiff.1 h]
  · simp [show t ∉ z from fun ht => h (hiff.2 ht)]

lemma mem_codeSet_par_even {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (⟨2 * q, by omega⟩ : Fin n) ∈ codeSet z ↔ z.card % 2 = 0 := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : 2 * q ≠ 2 * q + 2 := by omega
  have h2 : 2 * q / 2 = q := by omega
  have h3 : 2 * q % 2 = 0 := by omega
  simp only [h1, h2, h3, lt_irrefl, false_and, false_or, true_and]
  exact eq_comm

lemma mem_codeSet_par_odd {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (⟨2 * q + 1, by omega⟩ : Fin n) ∈ codeSet z ↔ z.card % 2 = 1 := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : 2 * q + 1 ≠ 2 * q + 2 := by omega
  have h2 : (2 * q + 1) / 2 = q := by omega
  have h3 : (2 * q + 1) % 2 = 1 := by omega
  simp only [h1, h2, h3, lt_irrefl, false_and, false_or, true_and]
  exact eq_comm

lemma mem_codeSet_probe {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (⟨2 * q + 2, by omega⟩ : Fin n) ∈ codeSet z := by
  simp [codeSet]

lemma not_mem_codeSet_last {q n : ℕ} (hn : n = 2 * q + 4) (z : Finset (Fin q)) :
    (⟨2 * q + 3, by omega⟩ : Fin n) ∉ codeSet z := by
  simp only [codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

lemma codeSet_injective {q n : ℕ} (hn : n = 2 * q + 4) :
    Function.Injective (codeSet (q := q) (n := n)) := by
  intro z1 z2 h
  ext t
  rw [← mem_codeSet_data_odd hn z1 t, h, mem_codeSet_data_odd hn z2 t]

lemma codeSet_inter_le {q n : ℕ} (hn : n = 2 * q + 4) {z1 z2 : Finset (Fin q)} (hne : z1 ≠ z2) :
    (codeSet (n := n) z1 ∩ codeSet (n := n) z2).card ≤ q := by
  have hsub : (codeSet (n := n) z1 ∩ codeSet (n := n) z2) ⊆
      (Finset.univ.filter fun j : Fin (q + 2) => codeElem hn z1 j = codeElem hn z2 j).image (codeElem hn z1) := by
    intro i hi
    rw [Finset.mem_inter, codeSet_eq_image hn z1, codeSet_eq_image hn z2] at hi
    rcases Finset.mem_image.1 hi.1 with ⟨j1, _, rfl⟩
    rcases Finset.mem_image.1 hi.2 with ⟨j2, _, h2⟩
    have hj : j1 = j2 := by
      have d1 := codeElem_div_two hn z1 j1
      have d2 := codeElem_div_two hn z2 j2
      rw [h2] at d2
      exact Fin.ext (d1.symm.trans d2)
    subst hj
    exact Finset.mem_image.2 ⟨j1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2.symm⟩, rfl⟩
  have htwo : ∃ j1 j2 : Fin (q + 2), j1 ≠ j2 ∧
      codeElem hn z1 j1 ≠ codeElem hn z2 j1 ∧ codeElem hn z1 j2 ≠ codeElem hn z2 j2 := by
    have hneS : (symmDiff z1 z2).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      exact hne (symmDiff_eq_bot.1 hemp)
    rcases hneS with ⟨t1, ht1⟩
    have hdiff1 : codeElem hn z1 ⟨t1.val, by omega⟩ ≠ codeElem hn z2 ⟨t1.val, by omega⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [codeElem, t1.isLt, ↓reduceDIte] at hv
      rw [Finset.mem_symmDiff] at ht1
      rcases ht1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2] at hv
      · simp [h1, h2] at hv
    by_cases h2ex : ∃ t2 ∈ symmDiff z1 z2, t2 ≠ t1
    · rcases h2ex with ⟨t2, ht2, ht21⟩
      have hdiff2 : codeElem hn z1 ⟨t2.val, by omega⟩ ≠ codeElem hn z2 ⟨t2.val, by omega⟩ := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [codeElem, t2.isLt, ↓reduceDIte] at hv
        rw [Finset.mem_symmDiff] at ht2
        rcases ht2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2] at hv
        · simp [h1, h2] at hv
      refine ⟨⟨t1.val, by omega⟩, ⟨t2.val, by omega⟩, ?_, hdiff1, hdiff2⟩
      intro heq; exact ht21 (Fin.ext (congrArg Fin.val heq).symm)
    · push Not at h2ex
      have hpar : z1.card % 2 ≠ z2.card % 2 := by
        rw [Finset.mem_symmDiff] at ht1
        rcases ht1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have heq : z1 = insert t1 z2 := by
            ext u
            by_cases hu : u = t1
            · subst hu; simp [h1]
            · simp only [Finset.mem_insert, hu, false_or]
              by_contra hneq
              have : u ∈ symmDiff z1 z2 := by
                rw [Finset.mem_symmDiff]
                tauto
              exact hu (h2ex u this)
          rw [heq, Finset.card_insert_of_notMem h2]; omega
        · have heq : z2 = insert t1 z1 := by
            ext u
            by_cases hu : u = t1
            · subst hu; simp [h1]
            · simp only [Finset.mem_insert, hu, false_or]
              by_contra hneq
              have : u ∈ symmDiff z1 z2 := by
                rw [Finset.mem_symmDiff]
                tauto
              exact hu (h2ex u this)
          rw [heq, Finset.card_insert_of_notMem h2]; omega
      have hdiffQ : codeElem hn z1 ⟨q, by omega⟩ ≠ codeElem hn z2 ⟨q, by omega⟩ := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [codeElem, lt_irrefl, ↓reduceDIte, ↓reduceIte] at hv
        omega
      refine ⟨⟨t1.val, by omega⟩, ⟨q, by omega⟩, ?_, hdiff1, hdiffQ⟩
      intro heq
      have := congrArg Fin.val heq
      dsimp only at this; omega
  rcases htwo with ⟨j1, j2, hj12, hd1, hd2⟩
  have hflt : (Finset.univ.filter fun j : Fin (q + 2) => codeElem hn z1 j = codeElem hn z2 j) ⊆
      (Finset.univ.erase j1).erase j2 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨fun h => hd2 (h ▸ hj), fun h => hd1 (h ▸ hj)⟩
  calc (codeSet (n := n) z1 ∩ codeSet (n := n) z2).card
      ≤ ((Finset.univ.filter fun j : Fin (q + 2) => codeElem hn z1 j = codeElem hn z2 j).image (codeElem hn z1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun j : Fin (q + 2) => codeElem hn z1 j = codeElem hn z2 j).card :=
        Finset.card_image_le
    _ ≤ ((Finset.univ.erase j1).erase j2).card := Finset.card_le_card hflt
    _ = q := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hj12.symm, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega

lemma mem_of_fin_val_eq {n : ℕ} {x : Finset (Fin n)} {a b : Fin n} (h : a.val = b.val) (ha : a ∈ x) : b ∈ x := by
  have heq : a = b := Fin.ext h
  exact heq ▸ ha

lemma pigeonhole_pairs {q n : ℕ} (hn : n = 2 * q + 4) {y : Finset (Fin n)} (hy : y.card = q + 2)
    (hlast : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ y)
    (hnodbl : ∀ t : Fin (q + 1), ¬ ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y)) :
    (⟨2 * q + 2, by omega⟩ : Fin n) ∈ y ∧
    ∀ t : Fin (q + 1), ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ↔ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∉ y) := by
  let phi : Fin n → Fin (q + 2) := fun i => ⟨i.val / 2, by omega⟩
  have hinj : Set.InjOn phi (y : Set (Fin n)) := by
    intro a ha b hb hphi
    have hd : a.val / 2 = b.val / 2 := congrArg Fin.val hphi
    by_contra hne
    have hvn : a.val ≠ b.val := fun h => hne (Fin.ext h)
    by_cases hq : a.val / 2 < q + 1
    · have hpair : (⟨2 * (a.val / 2), by omega⟩ : Fin n) ∈ y ∧ (⟨2 * (a.val / 2) + 1, by omega⟩ : Fin n) ∈ y := by
        have hcases : (a.val = 2 * (a.val / 2) ∧ b.val = 2 * (a.val / 2) + 1) ∨
            (b.val = 2 * (a.val / 2) ∧ a.val = 2 * (a.val / 2) + 1) := by omega
        rcases hcases with ⟨ha1, hb1⟩ | ⟨hb1, ha1⟩
        · exact ⟨mem_of_fin_val_eq ha1 ha, mem_of_fin_val_eq hb1 hb⟩
        · exact ⟨mem_of_fin_val_eq hb1 hb, mem_of_fin_val_eq ha1 ha⟩
      exact hnodbl ⟨a.val / 2, hq⟩ hpair
    · have hcases : a.val = 2 * q + 3 ∨ b.val = 2 * q + 3 := by omega
      rcases hcases with ha1 | hb1
      · exact hlast (mem_of_fin_val_eq ha1 ha)
      · exact hlast (mem_of_fin_val_eq hb1 hb)
  have hcard : (y.image phi).card = Fintype.card (Fin (q + 2)) := by
    rw [Finset.card_image_of_injOn hinj, hy, Fintype.card_fin]
  have huniv : y.image phi = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hmem : ∀ k : Fin (q + 2), ∃ i ∈ y, i.val / 2 = k.val := by
    intro k
    have hk : k ∈ y.image phi := by rw [huniv]; exact Finset.mem_univ k
    rcases Finset.mem_image.1 hk with ⟨i, hi, hik⟩
    exact ⟨i, hi, congrArg Fin.val hik⟩
  constructor
  · rcases hmem ⟨q + 1, by omega⟩ with ⟨i, hi, hid⟩
    dsimp only at hid
    have hiv : i.val = 2 * q + 2 := by
      by_contra hne
      have h3 : i.val = 2 * q + 3 := by omega
      exact hlast (mem_of_fin_val_eq h3 hi)
    exact mem_of_fin_val_eq hiv hi
  · intro t
    rcases hmem ⟨t.val, by omega⟩ with ⟨i, hi, hid⟩
    dsimp only at hid
    have hor : (⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∨ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y := by
      have : i.val = 2 * t.val ∨ i.val = 2 * t.val + 1 := by omega
      rcases this with h0 | h1
      · left; exact mem_of_fin_val_eq h0 hi
      · right; exact mem_of_fin_val_eq h1 hi
    have hnd := hnodbl t
    constructor
    · intro h0 h1; exact hnd ⟨h0, h1⟩
    · intro h1; rcases hor with h0 | h1'; exact h0; exact absurd h1' h1

lemma parity_wrong_of_ne_codeSet {q n : ℕ} (hn : n = 2 * q + 4) {y : Finset (Fin n)} (hy : y.card = q + 2)
    (hy_nl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ y)
    (hy_ndbl : ∀ t : Fin (q + 1), ¬ ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y))
    (hcode : ∀ z : Finset (Fin q), y ≠ codeSet z) :
    let z : Finset (Fin q) := Finset.univ.filter fun t => (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y
    ((⟨2 * q, by omega⟩ : Fin n) ∈ y ∧ z.card % 2 = 1) ∨
    ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ y ∧ z.card % 2 = 0) := by
  intro z
  have hpig := pigeonhole_pairs hn hy hy_nl hy_ndbl
  have hpq := hpig.2 ⟨q, by omega⟩
  by_contra hok
  push Not at hok
  apply hcode z
  ext i
  by_cases h1 : i.val = 2 * q + 3
  · have hi : i = ⟨2 * q + 3, by omega⟩ := Fin.ext h1
    rw [hi]; simp [hy_nl, not_mem_codeSet_last hn z]
  · by_cases h2 : i.val = 2 * q + 2
    · have hi : i = ⟨2 * q + 2, by omega⟩ := Fin.ext h2
      rw [hi]; simp [hpig.1, mem_codeSet_probe hn z]
    · by_cases h3 : i.val = 2 * q
      · have hi : i = ⟨2 * q, by omega⟩ := Fin.ext h3
        rw [hi, mem_codeSet_par_even hn z]
        constructor
        · intro hm; have := hok.1 hm; omega
        · intro hmod
          by_contra hnm
          have hm1 : (⟨2 * q + 1, by omega⟩ : Fin n) ∈ y := by
            by_contra hnm1; exact hnm (hpq.2 hnm1)
          exact hok.2 hm1 hmod
      · by_cases h4 : i.val = 2 * q + 1
        · have hi : i = ⟨2 * q + 1, by omega⟩ := Fin.ext h4
          rw [hi, mem_codeSet_par_odd hn z]
          constructor
          · intro hm; have := hok.2 hm; omega
          · intro hmod
            by_contra hnm
            have hm0 : (⟨2 * q, by omega⟩ : Fin n) ∈ y := hpq.2 hnm
            exact hok.1 hm0 hmod
        · have htlt : i.val / 2 < q := by omega
          let t : Fin q := ⟨i.val / 2, htlt⟩
          have h1t : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y ↔ t ∈ z := by simp [z]
          by_cases hev : i.val % 2 = 0
          · have hi : i = ⟨2 * t.val, by omega⟩ := Fin.ext (by dsimp only [t]; omega)
            rw [hi, mem_codeSet_data_even hn z t]
            exact (hpig.2 ⟨t.val, by omega⟩).trans (not_congr h1t)
          · have hi : i = ⟨2 * t.val + 1, by omega⟩ := Fin.ext (by dsimp only [t]; omega)
            rw [hi, mem_codeSet_data_odd hn z t]; exact h1t

def RVal {q n : ℕ} (r : ℕ) (f : Finset (Fin q) → Bool) (x : Finset (Fin n)) : ℕ :=
  if ∃ z : Finset (Fin q), f z = false ∧ x = codeSet z then r - 1 else min r x.card

def gainVal {q n : ℕ} (r : ℕ) (f : Finset (Fin q) → Bool) (x : Finset (Fin n)) (j : Fin n) : Bool :=
  decide (RVal r f x < RVal r f (insert j x))

lemma RVal_le {q n : ℕ} (r : ℕ) (f : Finset (Fin q) → Bool) (x : Finset (Fin n)) :
    RVal r f x ≤ r := by
  unfold RVal; split_ifs <;> omega

lemma RVal_eq_of_card_le_rm2 {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : x.card ≤ r - 2) :
    RVal r f x = x.card := by
  unfold RVal
  have hnex : ¬ ∃ z : Finset (Fin q), f z = false ∧ x = codeSet z := by
    rintro ⟨z, _, rfl⟩
    have := card_codeSet hn z; omega
  simp only [hnex, ↓reduceIte]
  omega

lemma RVal_eq_rm1_of_card_rm1 {q r n : ℕ} (hr : r = q + 2)
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : x.card = r - 1) :
    RVal r f x = r - 1 := by
  unfold RVal
  split_ifs <;> omega

lemma RVal_eq_r_of_card_gt {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : r < x.card) :
    RVal r f x = r := by
  unfold RVal
  have hnex : ¬ ∃ z : Finset (Fin q), f z = false ∧ x = codeSet z := by
    rintro ⟨z, _, rfl⟩
    have := card_codeSet hn z; omega
  simp only [hnex, ↓reduceIte]
  omega

lemma RVal_eq_r_iff {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) (x : Finset (Fin n)) :
    RVal r f x = r ↔ (r < x.card ∨ (x.card = r ∧ ∀ z, x = codeSet z → f z = true)) := by
  unfold RVal
  split_ifs with h
  · rcases h with ⟨z, hfz, rfl⟩
    have hc := card_codeSet hn z
    constructor
    · intro h1; omega
    · rintro (h1 | ⟨_, h2⟩)
      · omega
      · have := h2 z rfl; rw [hfz] at this; cases this
  · push Not at h
    constructor
    · intro hmin
      have hle : r ≤ x.card := by omega
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inl hlt
      · right; refine ⟨heq.symm, fun z hz => ?_⟩
        cases hfz : f z
        · exact absurd hz (h z hfz)
        · rfl
    · rintro (hlt | ⟨heq, _⟩) <;> omega

lemma RVal_le_rm2_iff {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) (x : Finset (Fin n)) :
    RVal r f x ≤ r - 2 ↔ x.card ≤ r - 2 := by
  unfold RVal
  split_ifs with h
  · rcases h with ⟨z, _, rfl⟩
    have := card_codeSet hn z; omega
  · omega

lemma RVal_mono {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) {x y : Finset (Fin n)} (hxy : x ⊆ y) :
    RVal r f x ≤ RVal r f y := by
  have hcle : x.card ≤ y.card := Finset.card_le_card hxy
  by_cases hy : r < y.card
  · rw [RVal_eq_r_of_card_gt hr hn f hy]; exact RVal_le r f x
  · by_cases hyeq : y.card = r
    · by_cases hxeq : x = y
      · subst hxeq; exact le_rfl
      · have hxlt : x.card < y.card := Finset.card_lt_card (lt_of_le_of_ne hxy hxeq)
        have hrx : RVal r f x ≤ r - 1 := by
          unfold RVal; split_ifs <;> omega
        have hry : r - 1 ≤ RVal r f y := by
          unfold RVal; split_ifs <;> omega
        omega
    · have hyle : y.card ≤ r - 1 := by omega
      unfold RVal
      have hnex : ¬ ∃ z : Finset (Fin q), f z = false ∧ x = codeSet z := by
        rintro ⟨z, _, rfl⟩; have := card_codeSet hn z; omega
      have hney : ¬ ∃ z : Finset (Fin q), f z = false ∧ y = codeSet z := by
        rintro ⟨z, _, rfl⟩; have := card_codeSet hn z; omega
      simp only [hnex, hney, ↓reduceIte]; omega

lemma card_insert_eq_card_erase_add_one {α : Type*} [DecidableEq α] (x : Finset α) (j : α) :
    (insert j x).card = (x.erase j).card + 1 := by
  by_cases hj : j ∈ x
  · rw [Finset.insert_eq_of_mem hj, Finset.card_erase_add_one hj]
  · rw [Finset.erase_eq_of_notMem hj, Finset.card_insert_of_notMem hj]

lemma gainVal_of_le_rm2 {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : RVal r f x ≤ r - 2) (j : Fin n) :
    gainVal r f x j = decide (j ∉ x) := by
  have hcx : x.card ≤ r - 2 := (RVal_le_rm2_iff hr hn f x).1 hx
  have hrx : RVal r f x = x.card := RVal_eq_of_card_le_rm2 hr hn f hcx
  have hrins : RVal r f (insert j x) = (insert j x).card := by
    by_cases hj : j ∈ x
    · rw [Finset.insert_eq_of_mem hj]; exact hrx
    · have hc2 : (insert j x).card = x.card + 1 := Finset.card_insert_of_notMem hj
      by_cases hlt : x.card + 1 ≤ r - 2
      · exact RVal_eq_of_card_le_rm2 hr hn f (by omega)
      · have heq : (insert j x).card = r - 1 := by omega
        rw [RVal_eq_rm1_of_card_rm1 hr f heq, heq]
  unfold gainVal
  rw [hrx, hrins]
  by_cases hj : j ∈ x
  · rw [Finset.insert_eq_of_mem hj]; simp [hj]
  · rw [Finset.card_insert_of_notMem hj]; simp [hj]

lemma gainVal_of_eq_rm1 {q r n : ℕ} (hr : r = q + 2)
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : RVal r f x = r - 1) (j : Fin n) :
    gainVal r f x j = decide (RVal r f (insert j x) = r) := by
  unfold gainVal
  rw [hx]
  have hle := RVal_le r f (insert j x)
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  omega

lemma gainVal_of_eq_r {q n : ℕ} {r : ℕ}
    (f : Finset (Fin q) → Bool) {x : Finset (Fin n)} (hx : RVal r f x = r) (j : Fin n) :
    gainVal r f x j = false := by
  unfold gainVal
  rw [hx]
  have hle := RVal_le r f (insert j x)
  simp only [decide_eq_false_iff_not]; omega

def inpVec (m : ℕ) (x : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).length = m + 2 := by
  simp [inpVec]

lemma inpVec_getD_lt (m : ℕ) (x : Finset (Fin m)) (i : Fin m) :
    (inpVec m x).getD i.val false = decide (i ∈ x) := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp : i.val < (List.ofFn (fun j : Fin m => decide (j ∈ x))).length)]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

lemma inpVec_getD_m (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD m false = false := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m)]
  simp

lemma inpVec_getD_m1 (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD (m + 1) false = true := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m + 1)]
  simp

lemma exists_map_build {m : ℕ} (c len : ℕ) (gs0 : List Gate) (P : ℕ → List Gate → ℕ → Prop)
    (hP_mono : ∀ i < len, ∀ gs1 gs2 w, w < m + gs1.length → Extends gs1 gs2 → P i gs1 w → P i gs2 w)
    (hstep : ∀ i < len, ∀ gs, Extends gs0 gs → GateOK m gs →
      ∃ gs' w, Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + c ∧ w < m + gs'.length ∧ P i gs' w)
    (hgs0 : GateOK m gs0) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
      gs'.length ≤ gs0.length + c * len ∧ ws.length = len ∧
      (∀ w ∈ ws, w < m + gs'.length) ∧
      ∀ i < len, P i gs' (ws.getD i 0) := by
  suffices h : ∀ k ≤ len,
      ∃ (gs' : List Gate) (ws : List ℕ),
        Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
        gs'.length ≤ gs0.length + c * k ∧ ws.length = k ∧
        (∀ w ∈ ws, w < m + gs'.length) ∧
        ∀ i < k, P i gs' (ws.getD i 0) from h len le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨gs0, [], Extends.refl gs0, hgs0, rfl, by simp, rfl, by simp, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨gs1, ws1, hext01, hgs1, hnc1, hlen1, hwl1, hwsW1, hP1⟩ := ih (by omega)
    obtain ⟨gs2, wk, hext12, hgs2, hnc2, hlen2, hwk, hPk⟩ := hstep k (by omega) gs1 hext01 hgs1
    refine ⟨gs2, ws1 ++ [wk], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by have hmul : c * (k + 1) = c * k + c := by ring
         omega,
      by simp [hwl1],
      fun w hw => by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hext12.length_le; have := hwsW1 w hw; omega
        · exact hwk,
      ?_⟩
    intro i hi
    by_cases hik : i < k
    · have hget : (ws1 ++ [wk]).getD i 0 = ws1.getD i 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ws1.length)]
      rw [hget]
      have hmem : ws1.getD i 0 ∈ ws1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hP_mono i (by omega) gs1 gs2 _ (hwsW1 _ hmem) hext12 (hP1 i hik)
    · have hieq : i = k := by omega
      rw [hieq]
      have hget : (ws1 ++ [wk]).getD k 0 = wk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ws1.length ≤ k)]
        simp [hwl1]
      rw [hget]
      exact hPk

lemma exists_map_build_pair {m : ℕ} (c len : ℕ) (gs0 : List Gate) (P : ℕ → List Gate → ℕ × ℕ → Prop)
    (hP_mono : ∀ i < len, ∀ gs1 gs2 p, p.1 < m + gs1.length → p.2 < m + gs1.length → Extends gs1 gs2 → P i gs1 p → P i gs2 p)
    (hstep : ∀ i < len, ∀ gs, Extends gs0 gs → GateOK m gs →
      ∃ gs' p, Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + c ∧ p.1 < m + gs'.length ∧ p.2 < m + gs'.length ∧ P i gs' p)
    (hgs0 : GateOK m gs0) :
    ∃ (gs' : List Gate) (ps : List (ℕ × ℕ)),
      Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
      gs'.length ≤ gs0.length + c * len ∧ ps.length = len ∧
      (∀ p ∈ ps, p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
      ∀ i < len, P i gs' (ps.getD i (0, 0)) := by
  suffices h : ∀ k ≤ len,
      ∃ (gs' : List Gate) (ps : List (ℕ × ℕ)),
        Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
        gs'.length ≤ gs0.length + c * k ∧ ps.length = k ∧
        (∀ p ∈ ps, p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
        ∀ i < k, P i gs' (ps.getD i (0, 0)) from h len le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨gs0, [], Extends.refl gs0, hgs0, rfl, by simp, rfl, by simp, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨gs1, ps1, hext01, hgs1, hnc1, hlen1, hpl1, hpsW1, hP1⟩ := ih (by omega)
    obtain ⟨gs2, pk, hext12, hgs2, hnc2, hlen2, hpk1, hpk2, hPk⟩ := hstep k (by omega) gs1 hext01 hgs1
    refine ⟨gs2, ps1 ++ [pk], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by have hmul : c * (k + 1) = c * k + c := by ring
         omega,
      by simp [hpl1],
      fun p hp => by
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · have := hext12.length_le; have := hpsW1 p hp; omega
        · exact ⟨hpk1, hpk2⟩,
      ?_⟩
    intro i hi
    by_cases hik : i < k
    · have hget : (ps1 ++ [pk]).getD i (0, 0) = ps1.getD i (0, 0) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ps1.length)]
      rw [hget]
      have hmem : ps1.getD i (0, 0) ∈ ps1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have hw := hpsW1 _ hmem
      exact hP_mono i (by omega) gs1 gs2 _ hw.1 hw.2 hext12 (hP1 i hik)
    · have hieq : i = k := by omega
      rw [hieq]
      have hget : (ps1 ++ [pk]).getD k (0, 0) = pk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ps1.length ≤ k)]
        simp [hpl1]
      rw [hget]
      exact hPk

def drXorVal (p1 p2 : Bool × Bool) : Bool × Bool :=
  ((p1.1 && p2.2) || (p1.2 && p2.1), (p1.1 && p2.1) || (p1.2 && p2.2))

lemma drXorVal_assoc (p1 p2 p3 : Bool × Bool) :
    drXorVal (drXorVal p1 p2) p3 = drXorVal p1 (drXorVal p2 p3) := by
  rcases p1 with ⟨a, b⟩; rcases p2 with ⟨c, d⟩; rcases p3 with ⟨e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

lemma drXorVal_id_left (p : Bool × Bool) : drXorVal (false, true) p = p := by
  rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide

lemma drXorVal_id_right (p : Bool × Bool) : drXorVal p (false, true) = p := by
  rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide

lemma drXorVal_zero_left (p : Bool × Bool) : drXorVal (false, false) p = (false, false) := by
  rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide

lemma drXorVal_zero_right (p : Bool × Bool) : drXorVal p (false, false) = (false, false) := by
  rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide

def drFold (ps : List (Bool × Bool)) : Bool × Bool :=
  ps.foldl drXorVal (false, true)

lemma drFold_foldl_shift (acc : Bool × Bool) (ps : List (Bool × Bool)) :
    ps.foldl drXorVal acc = drXorVal acc (drFold ps) := by
  induction ps generalizing acc with
  | nil => simp [drFold, drXorVal_id_right]
  | cons p ps ih =>
    simp only [drFold, List.foldl_cons] at ih ⊢
    rw [ih (drXorVal acc p), ih (drXorVal (false, true) p), drXorVal_id_left, drXorVal_assoc]

lemma drFold_cons (p : Bool × Bool) (ps : List (Bool × Bool)) :
    drFold (p :: ps) = drXorVal p (drFold ps) := by
  simp only [drFold, List.foldl_cons, drXorVal_id_left]
  exact drFold_foldl_shift p ps

lemma drFold_append (l1 l2 : List (Bool × Bool)) :
    drFold (l1 ++ l2) = drXorVal (drFold l1) (drFold l2) := by
  induction l1 with
  | nil => simp [drFold, drXorVal_id_left]
  | cons p l1 ih => rw [List.cons_append, drFold_cons, drFold_cons, ih, drXorVal_assoc]

lemma drFold_of_mem_zero {ps : List (Bool × Bool)} (h : (false, false) ∈ ps) :
    drFold ps = (false, false) := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rw [drFold_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact drXorVal_zero_left _
    · rw [ih h']; exact drXorVal_zero_right _

lemma drFold_of_comp (bs : List Bool) :
    drFold (bs.map fun b => (b, !b)) =
      (decide (bs.count true % 2 = 1), decide (bs.count true % 2 = 0)) := by
  induction bs with
  | nil => simp [drFold]
  | cons b bs ih =>
    rw [List.map_cons, drFold_cons, ih, List.count_cons]
    have hmod : bs.count true % 2 = 0 ∨ bs.count true % 2 = 1 := by omega
    cases b
    · rcases hmod with h | h <;> simp [drXorVal, h]
    · rcases hmod with h | h
      · have h1 : (bs.count true + 1) % 2 = 1 := by omega
        simp [drXorVal, h, h1]
      · have h1 : (bs.count true + 1) % 2 = 0 := by omega
        simp [drXorVal, h, h1]

lemma exists_drXor {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a ab b bb : ℕ}
    (ha : a < m + gs.length) (hab : ab < m + gs.length)
    (hb : b < m + gs.length) (hbb : bb < m + gs.length) :
    ∃ (gs' : List Gate) (p : ℕ × ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
      gs'.length ≤ gs.length + 6 ∧ p.1 < m + gs'.length ∧ p.2 < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        (wVal gs' inp p.1, wVal gs' inp p.2) =
        drXorVal (wVal gs inp a, wVal gs inp ab) (wVal gs inp b, wVal gs inp bb) := by
  obtain ⟨hg1, hn1, hl1, hw1, he1⟩ := mkAnd_step hgs ha hbb
  let g1 := gs ++ [⟨GateOp.and, [a, bb]⟩]
  let w1 := m + gs.length
  have hg1l : g1.length = gs.length + 1 := hl1
  obtain ⟨hg2, hn2, hl2, hw2, he2⟩ := mkAnd_step hg1 (by omega : ab < m + g1.length) (by omega : b < m + g1.length)
  let g2 := g1 ++ [⟨GateOp.and, [ab, b]⟩]
  let w2 := m + g1.length
  have hg2l : g2.length = g1.length + 1 := hl2
  obtain ⟨hg3, hn3, hl3, hw3, he3⟩ := mkOr_step hg2 (by omega : w1 < m + g2.length) hw2
  let g3 := g2 ++ [⟨GateOp.or, [w1, w2]⟩]
  let wpos := m + g2.length
  have hg3l : g3.length = g2.length + 1 := hl3
  obtain ⟨hg4, hn4, hl4, hw4, he4⟩ := mkAnd_step hg3 (by omega : a < m + g3.length) (by omega : b < m + g3.length)
  let g4 := g3 ++ [⟨GateOp.and, [a, b]⟩]
  let w4 := m + g3.length
  have hg4l : g4.length = g3.length + 1 := hl4
  obtain ⟨hg5, hn5, hl5, hw5, he5⟩ := mkAnd_step hg4 (by omega : ab < m + g4.length) (by omega : bb < m + g4.length)
  let g5 := g4 ++ [⟨GateOp.and, [ab, bb]⟩]
  let w5 := m + g4.length
  have hg5l : g5.length = g4.length + 1 := hl5
  obtain ⟨hg6, hn6, hl6, hw6, he6⟩ := mkOr_step hg5 (by omega : w4 < m + g5.length) hw5
  let g6 := g5 ++ [⟨GateOp.or, [w4, w5]⟩]
  let wneg := m + g5.length
  have hg6l : g6.length = g5.length + 1 := hl6
  have hext : Extends gs g6 :=
    Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩
      (Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩))))
  have hnc : notCnt g6 = notCnt gs := hn6.trans (hn5.trans (hn4.trans (hn3.trans (hn2.trans hn1))))
  refine ⟨g6, (wpos, wneg), hext, hg6, hnc, by omega, by dsimp only [wpos]; omega, hw6, ?_⟩
  intro inp hinp
  have e1 := he1 inp hinp; have e2 := he2 inp hinp; have e3 := he3 inp hinp
  have e4 := he4 inp hinp; have e5 := he5 inp hinp; have e6 := he6 inp hinp
  simp only [Prod.mk.injEq, drXorVal]
  refine ⟨?_, ?_⟩
  · rw [e6.1 wpos (by dsimp only [wpos]; omega), e5.1 wpos (by dsimp only [wpos]; omega),
      e4.1 wpos (by dsimp only [wpos]; omega), e3.2, e2.1 w1 (by dsimp only [w1]; omega),
      e1.2, e2.2, e1.1 ab hab, e1.1 b hb]
  · rw [e6.2, e5.1 w4 (by dsimp only [w4]; omega), e4.2, e5.2,
      e4.1 ab (by omega), e3.1 ab (by omega), e2.1 ab (by omega), e1.1 ab hab,
      e4.1 bb (by omega), e3.1 bb (by omega), e2.1 bb (by omega), e1.1 bb hbb,
      e3.1 a (by omega), e2.1 a (by omega), e1.1 a ha,
      e3.1 b (by omega), e2.1 b (by omega), e1.1 b hb]

lemma exists_drPref {m : ℕ} (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m) :
    ∀ (ps : List (ℕ × ℕ)) (gs : List Gate), GateOK m gs →
      (∀ p ∈ ps, p.1 < m + gs.length ∧ p.2 < m + gs.length) →
      ∃ (gs' : List Gate) (pref : List (ℕ × ℕ)),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + 6 * ps.length ∧ pref.length = ps.length + 1 ∧
        (∀ p ∈ pref, p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
        ∀ inp : List Bool, inp.length = m →
          inp.getD wF false = false → inp.getD wT false = true →
          ∀ k ≤ ps.length,
            let p := pref.getD k (0, 0)
            (wVal gs' inp p.1, wVal gs' inp p.2) =
            drFold ((ps.take k).map fun q => (wVal gs inp q.1, wVal gs inp q.2)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil =>
    intro gs hgs _
    refine ⟨gs, [(wF, wT)], Extends.refl gs, hgs, rfl, by simp, rfl,
      fun p hp => by simp at hp; rcases hp with rfl; omega, ?_⟩
    intro inp hinp hF hT k hk
    simp only [List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      List.take_zero, List.map_nil, drFold, List.foldl_nil]
    rw [evalWires_input gs inp (by omega), evalWires_input gs inp (by omega), hF, hT]
  | append_singleton ps1 q ih =>
    intro gs hgs hpsW
    obtain ⟨gs1, pref1, hext01, hgs1, hnc1, hlen1, hpl1, hpW1, hev1⟩ :=
      ih gs hgs (fun p hp => hpsW p (by simp [hp]))
    let lastP := pref1.getD ps1.length (0, 0)
    have hlast_mem : lastP ∈ pref1 := by
      dsimp only [lastP]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have hlastW := hpW1 lastP hlast_mem
    have hqW := hpsW q (by simp)
    have hle01 := hext01.length_le
    obtain ⟨gs2, newP, hext12, hgs2, hnc2, hlen2, hnp1, hnp2, hev2⟩ :=
      exists_drXor hgs1 hlastW.1 hlastW.2 (by omega : q.1 < m + gs1.length) (by omega : q.2 < m + gs1.length)
    refine ⟨gs2, pref1 ++ [newP], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [List.length_append, List.length_singleton]; omega,
      by simp [hpl1],
      fun p hp => by
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · have := hext12.length_le; have := hpW1 p hp; omega
        · exact ⟨hnp1, hnp2⟩,
      ?_⟩
    intro inp hinp hF hT k hk
    simp only [List.length_append, List.length_singleton] at hk
    dsimp only
    by_cases hkle : k ≤ ps1.length
    · have hget : (pref1 ++ [newP]).getD k (0, 0) = pref1.getD k (0, 0) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < pref1.length)]
      rw [hget]
      have hmem : pref1.getD k (0, 0) ∈ pref1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have hw := hpW1 _ hmem
      rw [hext12.wVal_eq inp (by omega), hext12.wVal_eq inp (by omega)]
      rw [hev1 inp hinp hF hT k hkle]
      rw [List.take_append_of_le_length hkle]
    · have hkeq : k = ps1.length + 1 := by omega
      subst hkeq
      have hget : (pref1 ++ [newP]).getD (ps1.length + 1) (0, 0) = newP := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : pref1.length ≤ ps1.length + 1)]
        simp [hpl1]
      rw [hget, hev2 inp hinp, hev1 inp hinp hF hT ps1.length le_rfl]
      rw [hext01.wVal_eq inp (by omega), hext01.wVal_eq inp (by omega)]
      rw [List.take_of_length_le (l := ps1 ++ [q]) (by simp), List.take_length, List.map_append, List.map_singleton,
        drFold_append, drFold_cons]
      simp [drFold, drXorVal_id_right]

lemma exists_drSuff {m : ℕ} (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m) :
    ∀ (ps : List (ℕ × ℕ)) (gs : List Gate), GateOK m gs →
      (∀ p ∈ ps, p.1 < m + gs.length ∧ p.2 < m + gs.length) →
      ∃ (gs' : List Gate) (suff : List (ℕ × ℕ)),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + 6 * ps.length ∧ suff.length = ps.length + 1 ∧
        (∀ p ∈ suff, p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
        ∀ inp : List Bool, inp.length = m →
          inp.getD wF false = false → inp.getD wT false = true →
          ∀ k ≤ ps.length,
            let p := suff.getD k (0, 0)
            (wVal gs' inp p.1, wVal gs' inp p.2) =
            drFold ((ps.drop k).map fun q => (wVal gs inp q.1, wVal gs inp q.2)) := by
  intro ps
  induction ps with
  | nil =>
    intro gs hgs _
    refine ⟨gs, [(wF, wT)], Extends.refl gs, hgs, rfl, by simp, rfl,
      fun p hp => by simp at hp; rcases hp with rfl; omega, ?_⟩
    intro inp hinp hF hT k hk
    simp only [List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      List.drop_nil, List.map_nil, drFold, List.foldl_nil]
    rw [evalWires_input gs inp (by omega), evalWires_input gs inp (by omega), hF, hT]
  | cons q ps1 ih =>
    intro gs hgs hpsW
    obtain ⟨gs1, suff1, hext01, hgs1, hnc1, hlen1, hsl1, hsW1, hev1⟩ :=
      ih gs hgs (fun p hp => hpsW p (by simp [hp]))
    let headS := suff1.getD 0 (0, 0)
    have hhead_mem : headS ∈ suff1 := by
      dsimp only [headS]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have hheadW := hsW1 headS hhead_mem
    have hqW := hpsW q (by simp)
    have hle01 := hext01.length_le
    obtain ⟨gs2, newP, hext12, hgs2, hnc2, hlen2, hnp1, hnp2, hev2⟩ :=
      exists_drXor hgs1 (by omega : q.1 < m + gs1.length) (by omega : q.2 < m + gs1.length) hheadW.1 hheadW.2
    refine ⟨gs2, newP :: suff1, hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [List.length_cons]; omega,
      by simp [hsl1],
      fun p hp => by
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hnp1, hnp2⟩
        · have := hext12.length_le; have := hsW1 p hp; omega,
      ?_⟩
    intro inp hinp hF hT k hk
    dsimp only
    cases k with
    | zero =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        List.drop_zero, List.map_cons]
      rw [hev2 inp hinp, hext01.wVal_eq inp (by omega), hext01.wVal_eq inp (by omega)]
      have h0 := hev1 inp hinp hF hT 0 (Nat.zero_le _)
      simp only [List.drop_zero] at h0
      rw [h0, ← drFold_cons]
    | succ k' =>
      have hk' : k' ≤ ps1.length := by simp at hk; omega
      have hget : (newP :: suff1).getD (k' + 1) (0, 0) = suff1.getD k' (0, 0) := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget]
      have hmem : suff1.getD k' (0, 0) ∈ suff1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have hw := hsW1 _ hmem
      rw [hext12.wVal_eq inp (by omega), hext12.wVal_eq inp (by omega)]
      simpa [List.drop_succ_cons] using hev1 inp hinp hF hT k' hk'

lemma exists_sim_D_mono_aux {m : ℕ} (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m) :
    ∀ (dg : List Gate) (gs : List Gate) (drW : List (ℕ × ℕ)),
      GateOK m gs →
      (∀ g ∈ dg, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ j < dg.length, ∀ i ∈ (dg.getD j ⟨GateOp.or, []⟩).inputs, i < drW.length + j) →
      (∀ p ∈ drW, p.1 < m + gs.length ∧ p.2 < m + gs.length) →
      ∃ (gs' : List Gate) (drW' : List (ℕ × ℕ)),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + 2 * dg.length ∧
        drW'.length = drW.length + dg.length ∧
        (∀ p ∈ drW', p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
        ∀ (inpC wD : List Bool), inpC.length = m → inpC.getD wF false = false → inpC.getD wT false = true →
          wD.length = drW.length →
          (∀ i < drW.length,
            wVal gs inpC (drW.getD i (0, 0)).1 = wD.getD i false ∧
            wVal gs inpC (drW.getD i (0, 0)).2 = !(wD.getD i false)) →
          ∀ i < drW'.length,
            wVal gs' inpC (drW'.getD i (0, 0)).1 = (evalWires dg wD).getD i false ∧
            wVal gs' inpC (drW'.getD i (0, 0)).2 = !((evalWires dg wD).getD i false) := by
  intro dg
  induction dg with
  | nil =>
    intro gs drW hgs _ _ hdrW
    exact ⟨gs, drW, Extends.refl gs, hgs, rfl, by simp, by simp, hdrW,
      fun inpC wD _ _ _ _ hagree i hi => hagree i (by simpa using hi)⟩
  | cons g dg' ih =>
    intro gs drW hgs hdg1 hdg2 hdrW
    have hg1 := hdg1 g (by simp)
    have hgin : ∀ i ∈ g.inputs, i < drW.length := by
      have h0 := hdg2 0 (by simp)
      simpa [List.getD_eq_getElem?_getD] using h0

    have hstep : ∃ (gs1 : List Gate) (uv : ℕ × ℕ),
        Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
        gs1.length ≤ gs.length + 2 ∧ uv.1 < m + gs1.length ∧ uv.2 < m + gs1.length ∧
        ∀ (inpC wD : List Bool), inpC.length = m → inpC.getD wF false = false → inpC.getD wT false = true →
          wD.length = drW.length →
          (∀ i < drW.length,
            wVal gs inpC (drW.getD i (0, 0)).1 = wD.getD i false ∧
            wVal gs inpC (drW.getD i (0, 0)).2 = !(wD.getD i false)) →
          wVal gs1 inpC uv.1 = g.op.eval (g.inputs.map fun i => wD.getD i false) ∧
          wVal gs1 inpC uv.2 = !(g.op.eval (g.inputs.map fun i => wD.getD i false)) := by
      rcases g with ⟨op, ins⟩
      dsimp only at hg1 hgin
      have hlen2 : ins.length ≤ 2 := hg1.2
      have hpair_lt : ∀ i ∈ ins, (drW.getD i (0, 0)).1 < m + gs.length ∧ (drW.getD i (0, 0)).2 < m + gs.length := by
        intro i hi
        have hilt := hgin i hi
        have hmem : drW.getD i (0, 0) ∈ drW := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]; exact List.getElem_mem _
        exact hdrW _ hmem
      rcases hg1.1 with rfl | rfl | rfl
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wT, wF), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | [a], _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          refine ⟨gs, drW.getD a (0, 0), Extends.refl gs, hgs, rfl, by omega, hpa.1, hpa.2, ?_⟩
          intro inpC wD _ _ _ _ hag
          simpa [GateOp.eval] using hag a ha
        | [a, b], _, hgin', hplt =>
          have ha := hgin' a (by simp); have hb := hgin' b (by simp)
          have hpa := hplt a (by simp); have hpb := hplt b (by simp)
          let pa := drW.getD a (0, 0); let pb := drW.getD b (0, 0)
          obtain ⟨hgA, hnA, hlA, hu, heA⟩ := mkAnd_step hgs hpa.1 hpb.1
          let gsA := gs ++ [⟨GateOp.and, [pa.1, pb.1]⟩]
          let u := m + gs.length
          have hgsAl : gsA.length = gs.length + 1 := hlA
          obtain ⟨hgB, hnB, hlB, hv, heB⟩ := mkOr_step hgA (by dsimp only [pa]; omega : pa.2 < m + gsA.length) (by dsimp only [pb]; omega : pb.2 < m + gsA.length)
          let gsB := gsA ++ [⟨GateOp.or, [pa.2, pb.2]⟩]
          let v := m + gsA.length
          refine ⟨gsB, (u, v), Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩, hgB, hnB.trans hnA,
            by simp [gsB, gsA], by dsimp only [u]; simp [gsB, gsA], hv, ?_⟩
          intro inpC wD hinp _ _ _ hag
          have eA := heA inpC hinp; have eB := heB inpC hinp
          have haga := hag a ha; have hagb := hag b hb
          constructor
          · rw [eB.1 u (by dsimp only [u]; omega), eA.2, haga.1, hagb.1]; simp [GateOp.eval]
          · rw [eB.2, eA.1 pa.2 hpa.2, eA.1 pb.2 hpb.2, haga.2, hagb.2]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            cases wD.getD a false <;> cases wD.getD b false <;> rfl
        | _ :: _ :: _ :: _, hlen2', _, _ => simp at hlen2'
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wF, wT), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | [a], _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          refine ⟨gs, drW.getD a (0, 0), Extends.refl gs, hgs, rfl, by omega, hpa.1, hpa.2, ?_⟩
          intro inpC wD _ _ _ _ hag
          simpa [GateOp.eval] using hag a ha
        | [a, b], _, hgin', hplt =>
          have ha := hgin' a (by simp); have hb := hgin' b (by simp)
          have hpa := hplt a (by simp); have hpb := hplt b (by simp)
          let pa := drW.getD a (0, 0); let pb := drW.getD b (0, 0)
          obtain ⟨hgA, hnA, hlA, hu, heA⟩ := mkOr_step hgs hpa.1 hpb.1
          let gsA := gs ++ [⟨GateOp.or, [pa.1, pb.1]⟩]
          let u := m + gs.length
          have hgsAl : gsA.length = gs.length + 1 := hlA
          obtain ⟨hgB, hnB, hlB, hv, heB⟩ := mkAnd_step hgA (by dsimp only [pa]; omega : pa.2 < m + gsA.length) (by dsimp only [pb]; omega : pb.2 < m + gsA.length)
          let gsB := gsA ++ [⟨GateOp.and, [pa.2, pb.2]⟩]
          let v := m + gsA.length
          refine ⟨gsB, (u, v), Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩, hgB, hnB.trans hnA,
            by simp [gsB, gsA], by dsimp only [u]; simp [gsB, gsA], hv, ?_⟩
          intro inpC wD hinp _ _ _ hag
          have eA := heA inpC hinp; have eB := heB inpC hinp
          have haga := hag a ha; have hagb := hag b hb
          constructor
          · rw [eB.1 u (by dsimp only [u]; omega), eA.2, haga.1, hagb.1]; simp [GateOp.eval]
          · rw [eB.2, eA.1 pa.2 hpa.2, eA.1 pb.2 hpb.2, haga.2, hagb.2]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            cases wD.getD a false <;> cases wD.getD b false <;> rfl
        | _ :: _ :: _ :: _, hlen2', _, _ => simp at hlen2'
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wT, wF), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | a :: _, _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          let pa := drW.getD a (0, 0)
          refine ⟨gs, (pa.2, pa.1), Extends.refl gs, hgs, rfl, by omega, hpa.2, hpa.1, ?_⟩
          intro inpC wD _ _ _ _ hag
          have haga := hag a ha
          dsimp only [pa]
          rw [haga.1, haga.2]
          simp [GateOp.eval]
    obtain ⟨gs1, uv, hext01, hgs1, hnc1, hlen1, huv1, huv2, hev1⟩ := hstep
    obtain ⟨gs2, drW2, hext12, hgs2, hnc2, hlen2, hdrl2, hdrW2, hev2⟩ :=
      ih gs1 (drW ++ [uv]) hgs1
        (fun g' hg' => hdg1 g' (by simp [hg']))
        (fun j hj i hi => by
          have h := hdg2 (j + 1) (by simp; omega) i (by simpa [List.getD_eq_getElem?_getD] using hi)
          simp only [List.length_append, List.length_singleton]; omega)
        (fun p hp => by
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · have := hext01.length_le; have := hdrW p hp; omega
          · exact ⟨huv1, huv2⟩)
    refine ⟨gs2, drW2, hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [List.length_cons]; omega,
      by simp only [List.length_append, List.length_singleton] at hdrl2
         simp only [List.length_cons]; omega,
      hdrW2, ?_⟩
    intro inpC wD hinp hF hT hwDl hag i hi
    simp only [evalWires, List.foldl_cons]
    have hstep_ev := hev1 inpC wD hinp hF hT hwDl hag
    have hag1 : ∀ k < (drW ++ [uv]).length,
        wVal gs1 inpC ((drW ++ [uv]).getD k (0, 0)).1 = (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false ∧
        wVal gs1 inpC ((drW ++ [uv]).getD k (0, 0)).2 = !((wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false) := by
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < drW.length
      · have h1 : (drW ++ [uv]).getD k (0, 0) = drW.getD k (0, 0) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        have h2 : (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false = wD.getD k false := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < wD.length)]
        rw [h1, h2]
        have hmem : drW.getD k (0, 0) ∈ drW := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
        have hpk := hdrW _ hmem
        rw [hext01.wVal_eq inpC (by omega), hext01.wVal_eq inpC (by omega)]
        exact hag k hlt
      · have hkeq : k = drW.length := by omega
        subst hkeq
        have h1 : (drW ++ [uv]).getD drW.length (0, 0) = uv := by
          simp [List.getD_eq_getElem?_getD]
        have h2 : (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD drW.length false =
            g.op.eval (g.inputs.map fun j => wD.getD j false) := by
          simp [List.getD_eq_getElem?_getD, hwDl]
        rw [h1, h2]
        exact hstep_ev
    exact hev2 inpC (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]) hinp hF hT
      (by simp [hwDl]) hag1 i hi

lemma exists_b_decoder_aux {m : ℕ} (b : ℕ) (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m)
    (T : List ℕ) (hTl : T.length = 2 ^ b) :
    ∀ (d : ℕ) (_hd : d ≤ b) (gs : List Gate), GateOK m gs →
      (∀ w ∈ T, w < m + gs.length) →
      ∃ (gs' : List Gate) (eqP : List ℕ),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + d ∧
        gs'.length ≤ gs.length + 5 * 2 ^ d ∧ eqP.length = 2 ^ d ∧
        (∀ w ∈ eqP, w < m + gs'.length) ∧
        ∀ (inp : List Bool) (v : ℕ), inp.length = m →
          inp.getD wF false = false → inp.getD wT false = true →
          v < 2 ^ b →
          (∀ k, 1 ≤ k → k < 2 ^ b → wVal gs inp (T.getD k 0) = decide (k ≤ v)) →
          ∀ u < 2 ^ d, wVal gs' inp (eqP.getD u 0) = decide (v / 2 ^ (b - d) = u) := by
  intro d
  induction d with
  | zero =>
    intro _ gs hgs _
    refine ⟨gs, [wT], Extends.refl gs, hgs, by simp, by simp, by simp,
      fun w hw => by simp at hw; subst hw; omega, ?_⟩
    intro inp v hinp _ hT hv _ u hu
    have hu0 : u = 0 := by omega
    subst hu0
    have hdiv : v / 2 ^ b = 0 := Nat.div_eq_of_lt hv
    simp only [Nat.sub_zero, hdiv, decide_true, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    rw [evalWires_input gs inp (by omega), hT]
  | succ d ih =>
    intro hdb gs hgs hTW
    obtain ⟨gs1, eqP, hext01, hgs1, hnc1, hlen1, heqPl, heqPW, hev1⟩ :=
      ih (by omega) gs hgs hTW
    let p := b - (d + 1)
    have hbd : b - d = p + 1 := by dsimp only [p]; omega

    have hbp_build : ∀ (cnt : ℕ) (_hcnt : cnt ≤ 2 ^ d) (gsA : List Gate),
        Extends gs1 gsA → GateOK m gsA →
        ∃ (gsB : List Gate) (acc : ℕ),
          Extends gsA gsB ∧ GateOK m gsB ∧ notCnt gsB = notCnt gsA ∧
          gsB.length ≤ gsA.length + 2 * cnt ∧ acc < m + gsB.length ∧
          ∀ (inp : List Bool), inp.length = m → inp.getD wF false = false →
            wVal gsB inp acc = decide (∃ u < cnt,
              wVal gs1 inp (eqP.getD u 0) = true ∧
              wVal gs inp (T.getD (u * 2 ^ (p + 1) + 2 ^ p) 0) = true) := by
      intro cnt
      induction cnt with
      | zero =>
        intro _ gsA _ hgsA
        refine ⟨gsA, wF, Extends.refl gsA, hgsA, rfl, by simp, by omega, ?_⟩
        intro inp hinp hF
        rw [evalWires_input gsA inp (by omega), hF]
        simp
      | succ c ihc =>
        intro hc gsA hext1A hgsA
        obtain ⟨gsB, acc, hextAB, hgsB, hncB, hlenB, haccW, hevB⟩ := ihc (by omega) gsA hext1A hgsA
        have hext1B : Extends gs1 gsB := hext1A.trans hextAB
        have hext0B : Extends gs gsB := hext01.trans hext1B
        let eu := eqP.getD c 0
        have heu_mem : eu ∈ eqP := by
          dsimp only [eu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have heuW : eu < m + gsB.length := by have := hext1B.length_le; have := heqPW _ heu_mem; omega
        have hidx_lt : c * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
          have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
          have h2 : c + 1 ≤ 2 ^ d := hc
          have h3 : (c + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) := Nat.mul_le_mul_right _ h2
          have h4 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
          have h5 : 0 < 2 ^ p := Nat.two_pow_pos p
          nlinarith
        let tu := T.getD (c * 2 ^ (p + 1) + 2 ^ p) 0
        have htu_mem : tu ∈ T := by
          dsimp only [tu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have htuW : tu < m + gsB.length := by have := hext0B.length_le; have := hTW _ htu_mem; omega
        obtain ⟨hgC, hnC, hlC, hwC, heC⟩ := mkAnd_step hgsB heuW htuW
        let gsC := gsB ++ [⟨GateOp.and, [eu, tu]⟩]
        let wC := m + gsB.length
        have hgsCl : gsC.length = gsB.length + 1 := hlC
        obtain ⟨hgD, hnD, hlD, hwD, heD⟩ := mkOr_step hgC (by omega : acc < m + gsC.length) hwC
        let gsD := gsC ++ [⟨GateOp.or, [acc, wC]⟩]
        let wD := m + gsC.length
        refine ⟨gsD, wD, hextAB.trans (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩), hgD,
          hnD.trans (hnC.trans hncB), by simp only [gsD, gsC, List.length_append, List.length_singleton]; omega, hwD, ?_⟩
        intro inp hinp hF
        have eC := heC inp hinp; have eD := heD inp hinp
        rw [eD.2, eC.1 acc haccW, eC.2, hevB inp hinp hF,
          hext1B.wVal_eq inp (by have := heqPW _ heu_mem; omega),
          hext0B.wVal_eq inp (by have := hTW _ htu_mem; omega)]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨u, hu, h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨u, by omega, h1, h2⟩
          · exact ⟨c, by omega, h1, h2⟩
        · rintro ⟨u, hu, h1, h2⟩
          by_cases huc : u < c
          · exact Or.inl ⟨u, huc, h1, h2⟩
          · have : u = c := by omega
            subst this; exact Or.inr ⟨h1, h2⟩
    obtain ⟨gs2, bp, hext12, hgs2, hnc2, hlen2, hbpW, hev_bp⟩ := hbp_build (2 ^ d) le_rfl gs1 (Extends.refl gs1) hgs1

    obtain ⟨hgs3, hnc3, hlen3, hnbpW, hev3⟩ := mkNot_step hgs2 hbpW
    let gs3 := gs2 ++ [⟨GateOp.not, [bp]⟩]
    let nbp := m + gs2.length
    have hext23 : Extends gs2 gs3 := ⟨_, rfl⟩
    have hext13 : Extends gs1 gs3 := hext12.trans hext23
    have hgs3l : gs3.length = gs2.length + 1 := hlen3

    have hbp3 : bp < m + gs3.length := by omega
    obtain ⟨gs4, nextP, hext34, hgs4, hnc4, hlen4, hnextl, hnextW, hnextP⟩ :=
      exists_map_build (m := m) 1 (2 ^ (d + 1)) gs3
        (fun u gsX w => ∀ (inp : List Bool), inp.length = m →
          wVal gsX inp w = (wVal gs1 inp (eqP.getD (u / 2) 0) &&
            if u % 2 = 0 then wVal gs3 inp nbp else wVal gs3 inp bp))
        (fun u _ gsA gsB w hw hext hP inp hinp => by rw [hext.wVal_eq inp (by omega)]; exact hP inp hinp)
        (fun u hu gsA hext3A hgsA => by
          have hud : u / 2 < 2 ^ d := by
            have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          let eu := eqP.getD (u / 2) 0
          have heu_mem : eu ∈ eqP := by
            dsimp only [eu]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
          have hext1A : Extends gs1 gsA := hext13.trans hext3A
          have heuA : eu < m + gsA.length := by have := hext1A.length_le; have := heqPW _ heu_mem; omega
          let bitW := if u % 2 = 0 then nbp else bp
          have hbitA : bitW < m + gsA.length := by
            have := hext3A.length_le; dsimp only [bitW]; split_ifs <;> omega
          obtain ⟨hgB, hnB, hlB, hwB, heB⟩ := mkAnd_step hgsA heuA hbitA
          refine ⟨gsA ++ [⟨GateOp.and, [eu, bitW]⟩], m + gsA.length, ⟨_, rfl⟩, hgB, hnB, by omega, hwB, ?_⟩
          intro inp hinp
          rw [(heB inp hinp).2, hext1A.wVal_eq inp (by have := heqPW _ heu_mem; omega)]
          congr 1
          dsimp only [bitW]
          split_ifs
          · exact hext3A.wVal_eq inp (by omega)
          · exact hext3A.wVal_eq inp (by omega))
        hgs3
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hlen_tot : gs4.length ≤ gs.length + 5 * 2 ^ (d + 1) := by omega
    have hnc_tot : notCnt gs4 = notCnt gs + (d + 1) := by rw [hnc4, hnc3, hnc2, hnc1]; omega
    refine ⟨gs4, nextP, hext01.trans (hext13.trans hext34), hgs4, hnc_tot, hlen_tot, hnextl, hnextW, ?_⟩
    intro inp v hinp hF hT hv hTspec u hu
    rw [hnextP u hu inp hinp]
    have hud : u / 2 < 2 ^ d := by omega
    have heq_u2 : wVal gs1 inp (eqP.getD (u / 2) 0) = decide (v / 2 ^ (p + 1) = u / 2) := by
      rw [hev1 inp v hinp hF hT hv hTspec (u / 2) hud, hbd]
    have hbp_val : wVal gs2 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [hev_bp inp hinp hF]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have hvp_lt : v / 2 ^ (p + 1) < 2 ^ d := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        omega
      have hidx_pos : 1 ≤ (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p := by
        have := Nat.two_pow_pos p; omega
      have hidx_lt : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        have h2 : (v / 2 ^ (p + 1) + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
        have h4 := Nat.two_pow_pos p
        nlinarith
      have hiff_arith : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p ≤ v ↔ (v / 2 ^ p) % 2 = 1 := by
        have hm := Nat.div_add_mod v (2 ^ p)
        have hmlt := Nat.mod_lt v (Nat.two_pow_pos p)
        have hm2 := Nat.div_add_mod (v / 2 ^ p) 2
        have hm2lt : (v / 2 ^ p) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hp2 : 2 ^ (p + 1) = 2 * 2 ^ p := by ring
        rw [hdiv2, hp2]
        generalize 2 ^ p = P at hm hmlt ⊢
        generalize v / P = A at hm hm2 hm2lt ⊢
        have hA2 : A % 2 = 0 ∨ A % 2 = 1 := by omega
        rcases hA2 with h0 | h1
        · have hAeq : A = 2 * (A / 2) := by omega
          have hmul : A / 2 * (2 * P) = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h0, hmul]
          constructor
          · intro h; omega
          · intro h; omega
        · have hAeq : A = 2 * (A / 2) + 1 := by omega
          have hmul : A / 2 * (2 * P) + P = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h1, hmul]
          constructor
          · intro _; rfl
          · intro _; omega
      constructor
      · rintro ⟨w, hw, hw1, hw2⟩
        rw [hev1 inp v hinp hF hT hv hTspec w hw, hbd, decide_eq_true_eq] at hw1
        subst hw1
        rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq] at hw2
        exact hiff_arith.1 hw2
      · intro hmod
        refine ⟨v / 2 ^ (p + 1), hvp_lt, ?_, ?_⟩
        · rw [hev1 inp v hinp hF hT hv hTspec _ hvp_lt, hbd]; simp
        · rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq]
          exact hiff_arith.2 hmod
    have hbp3_val : wVal gs3 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [(hev3 inp hinp).1 bp hbpW, hbp_val]
    have hnbp3_val : wVal gs3 inp nbp = decide ((v / 2 ^ p) % 2 = 0) := by
      rw [(hev3 inp hinp).2, hbp_val]
      have hmod2 : (v / 2 ^ p) % 2 = 0 ∨ (v / 2 ^ p) % 2 = 1 := by omega
      rcases hmod2 with h | h <;> simp [h]
    have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [heq_u2, hbp3_val, hnbp3_val, hdiv2]
    split_ifs with hpar
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega

lemma exists_prefix_or {m : ℕ} (ws : List ℕ) :
    ∀ (k : ℕ) (_hk : k < ws.length) (gs : List Gate), GateOK m gs →
      (∀ w ∈ ws, w < m + gs.length) →
      ∃ (gs' : List Gate) (leW : List ℕ),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + k ∧ leW.length = k + 1 ∧
        (∀ w ∈ leW, w < m + gs'.length) ∧
        ∀ inp : List Bool, inp.length = m →
          ∀ j ≤ k, wVal gs' inp (leW.getD j 0) = decide (∃ i ≤ j, wVal gs inp (ws.getD i 0) = true) := by
  intro k
  induction k with
  | zero =>
    intro hk gs hgs hwsW
    have hw0_mem : ws.getD 0 0 ∈ ws := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    refine ⟨gs, [ws.getD 0 0], Extends.refl gs, hgs, rfl, by simp, rfl,
      fun w hw => by simp at hw; subst hw; exact hwsW _ hw0_mem, ?_⟩
    intro inp _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      Nat.le_zero, exists_eq_left]
    cases wVal gs inp (ws.getD 0 0) <;> rfl
  | succ k ih =>
    intro hk gs hgs hwsW
    obtain ⟨gs1, leW1, hext01, hgs1, hnc1, hlen1, hl1, hW1, hev1⟩ := ih (by omega) gs hgs hwsW
    let prev := leW1.getD k 0
    have hprev_mem : prev ∈ leW1 := by
      dsimp only [prev]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    let cur := ws.getD (k + 1) 0
    have hcur_mem : cur ∈ ws := by
      dsimp only [cur]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    have hcur1 : cur < m + gs1.length := by have := hext01.length_le; have := hwsW _ hcur_mem; omega
    obtain ⟨hgs2, hnc2, hlen2, hw2, hev2⟩ := mkOr_step hgs1 (hW1 _ hprev_mem) hcur1
    let gs2 := gs1 ++ [⟨GateOp.or, [prev, cur]⟩]
    let w2 := m + gs1.length
    have hext12 : Extends gs1 gs2 := ⟨_, rfl⟩
    refine ⟨gs2, leW1 ++ [w2], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [gs2, List.length_append, List.length_singleton]; omega,
      by simp [hl1],
      fun w hw => by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hext12.length_le; have := hW1 w hw; omega
        · exact hw2,
      ?_⟩
    intro inp hinp j hj
    by_cases hjk : j ≤ k
    · have hget : (leW1 ++ [w2]).getD j 0 = leW1.getD j 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < leW1.length)]
      rw [hget]
      have hmem : leW1.getD j 0 ∈ leW1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      rw [hext12.wVal_eq inp (by have := hW1 _ hmem; omega)]
      exact hev1 inp hinp j hjk
    · have hjeq : j = k + 1 := by omega
      subst hjeq
      have hget : (leW1 ++ [w2]).getD (k + 1) 0 = w2 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : leW1.length ≤ k + 1)]
        simp [hl1]
      rw [hget, (hev2 inp hinp).2, hev1 inp hinp k le_rfl,
        hext01.wVal_eq inp (by have := hwsW _ hcur_mem; omega)]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, hv⟩ | hv)
        · exact ⟨i, by omega, hv⟩
        · exact ⟨k + 1, le_rfl, hv⟩
      · rintro ⟨i, hi, hv⟩
        by_cases hik : i ≤ k
        · exact Or.inl ⟨i, hik, hv⟩
        · have : i = k + 1 := by omega
          subst this; exact Or.inr hv

def xDataList {q n : ℕ} (hn : n = 2 * q + 4) (x : Finset (Fin n)) : List (Bool × Bool) :=
  List.ofFn fun t : Fin q =>
    (decide ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x), decide ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x))

lemma count_true_ofFn_mem {q : ℕ} (z : Finset (Fin q)) :
    (List.ofFn fun t : Fin q => decide (t ∈ z)).count true = z.card := by
  rw [count_true_ofFn_eq]
  have h1 : (∑ t : Fin q, if decide (t ∈ z) = true then 1 else 0) =
      ∑ t : Fin q, if t ∈ z then 1 else 0 := by
    apply Finset.sum_congr rfl; intro t _; simp
  rw [h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp

lemma drFold_xDataList_of_agree {q n : ℕ} (hn : n = 2 * q + 4) {x : Finset (Fin n)} {z : Finset (Fin q)}
    (hag : ∀ t : Fin q, ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
                        ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z)) :
    drFold (xDataList hn x) = (decide (z.card % 2 = 1), decide (z.card % 2 = 0)) := by
  have heq : xDataList hn x = (List.ofFn fun t : Fin q => decide (t ∈ z)).map (fun b => (b, !b)) := by
    apply List.ext_getElem
    · simp [xDataList]
    · intro i hi1 hi2
      have hiq : i < q := by simp [xDataList] at hi1; exact hi1
      simp only [xDataList, List.getElem_ofFn, List.getElem_map, Prod.mk.injEq]
      have h := hag ⟨i, hiq⟩
      constructor
      · apply Bool.eq_iff_iff.2; simp [h.1]
      · apply Bool.eq_iff_iff.2; simp [h.2]
  rw [heq, drFold_of_comp, count_true_ofFn_mem]

lemma drFold_xDataList_skip_of_agree {q n : ℕ} (hn : n = 2 * q + 4) {x : Finset (Fin n)}
    {z : Finset (Fin q)} (t0 : Fin q)
    (hag : ∀ t : Fin q, t ≠ t0 →
      ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
      ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z)) :
    drFold ((xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1)) =
      (decide ((z.erase t0).card % 2 = 1), decide ((z.erase t0).card % 2 = 0)) := by
  let L := List.ofFn fun t : Fin q => decide (t ∈ z)
  have hLlen : L.length = q := by simp [L]
  have heq : (xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1) =
      (L.take t0.val ++ L.drop (t0.val + 1)).map (fun b => (b, !b)) := by
    apply List.ext_getElem
    · simp [xDataList, L]
    · intro i hi1 hi2
      have hlen1 : ((xDataList hn x).take t0.val).length = t0.val := by simp [xDataList]
      have hlen2 : (L.take t0.val).length = t0.val := by simp [L]
      by_cases hit : i < t0.val
      · rw [List.getElem_append_left (by omega), List.getElem_map, List.getElem_append_left (by omega)]
        simp only [xDataList, L, List.getElem_take, List.getElem_ofFn, Prod.mk.injEq]
        have hne : (⟨i, by omega⟩ : Fin q) ≠ t0 := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
        have h := hag ⟨i, by omega⟩ hne
        exact ⟨Bool.eq_iff_iff.2 (by simp [h.1]), Bool.eq_iff_iff.2 (by simp [h.2])⟩
      · rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_append_right (by omega)]
        simp only [xDataList, L, List.getElem_drop, List.getElem_ofFn, Prod.mk.injEq, hlen2]
        have hidx_lt : t0.val + 1 + (i - t0.val) < q := by
          simp only [List.length_append, List.length_take, List.length_drop, xDataList, List.length_ofFn] at hi1
          omega
        have hne : (⟨t0.val + 1 + (i - t0.val), hidx_lt⟩ : Fin q) ≠ t0 := fun h => by
          have := congrArg Fin.val h; dsimp only at this; omega
        have h := hag ⟨t0.val + 1 + (i - t0.val), hidx_lt⟩ hne
        exact ⟨Bool.eq_iff_iff.2 (by simp [h.1]), Bool.eq_iff_iff.2 (by simp [h.2])⟩
  rw [heq, drFold_of_comp]
  have hLsplit : L = L.take t0.val ++ L[t0.val]'(by omega) :: L.drop (t0.val + 1) := by
    have h1 := (List.take_append_drop t0.val L).symm
    have h2 : L.drop t0.val = L[t0.val]'(by omega) :: L.drop (t0.val + 1) := List.drop_eq_getElem_cons (by omega)
    rw [h2] at h1; exact h1
  have hcnt : (L.take t0.val ++ L.drop (t0.val + 1)).count true = (z.erase t0).card := by
    have htot := count_true_ofFn_mem z
    change L.count true = z.card at htot
    conv_lhs at htot => rw [hLsplit]
    rw [List.count_append, List.count_cons] at htot
    rw [List.count_append]
    have hget : L[t0.val]'(by omega) = decide (t0 ∈ z) := by simp [L]
    rw [hget] at htot
    by_cases hm : t0 ∈ z
    · simp only [hm, decide_true, beq_self_eq_true, ↓reduceIte] at htot
      have := Finset.card_erase_of_mem hm; omega
    · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at htot
      rw [Finset.erase_eq_of_notMem hm]; omega
  rw [hcnt]

lemma drFold_xDataList_skip_of_missing {q n : ℕ} (hn : n = 2 * q + 4) {x : Finset (Fin n)}
    (t0 t1 : Fin q) (hne : t1 ≠ t0)
    (h1 : (⟨2 * t1.val + 1, by omega⟩ : Fin n) ∉ x)
    (h0 : (⟨2 * t1.val, by omega⟩ : Fin n) ∉ x) :
    drFold ((xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1)) = (false, false) := by
  apply drFold_of_mem_zero
  have hval : (xDataList hn x)[t1.val]'(by simp [xDataList]) = (false, false) := by
    simp [xDataList, h1, h0]
  rw [List.mem_append]
  have htv : t1.val ≠ t0.val := fun h => hne (Fin.ext h)
  by_cases hlt : t1.val < t0.val
  · left
    have hlen : t1.val < ((xDataList hn x).take t0.val).length := by simp [xDataList]; omega
    have hg : ((xDataList hn x).take t0.val)[t1.val]'hlen = (false, false) := by
      rw [List.getElem_take, hval]
    rw [← hg]; exact List.getElem_mem hlen
  · right
    have hlen : t1.val - (t0.val + 1) < ((xDataList hn x).drop (t0.val + 1)).length := by simp [xDataList]; omega
    have hg : ((xDataList hn x).drop (t0.val + 1))[t1.val - (t0.val + 1)]'hlen = (false, false) := by
      rw [List.getElem_drop]
      have hidx : t0.val + 1 + (t1.val - (t0.val + 1)) = t1.val := by omega
      simp only [hidx]; exact hval
    rw [← hg]; exact List.getElem_mem hlen

lemma exists_zHat_and_fVal {q n : ℕ} (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool) (D : Circuit)
    (hDok : GateOK (q + 2) D.gates) (hDout : D.output < q + 2 + D.gates.length)
    (hDeval : ∀ z : Finset (Fin q), (evalWires D.gates (inpVec q z)).getD D.output false = f z)
    (gs6 : List Gate) (hgs6 : GateOK (n + 2) gs6)
    (pOther : List (ℕ × ℕ)) (hpOl : pOther.length = q)
    (hpOW : ∀ p ∈ pOther, p.1 < n + 2 + gs6.length ∧ p.2 < n + 2 + gs6.length)
    (hpO_ev : ∀ t < q, ∀ x : Finset (Fin n),
      (wVal gs6 (inpVec n x) (pOther.getD t (0, 0)).1, wVal gs6 (inpVec n x) (pOther.getD t (0, 0)).2) =
      drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1))) :
    ∃ (gs8 : List Gate) (fVal : ℕ),
      Extends gs6 gs8 ∧ GateOK (n + 2) gs8 ∧ notCnt gs8 = notCnt gs6 ∧
      gs8.length ≤ gs6.length + 8 * q + 2 * D.gates.length ∧
      fVal < n + 2 + gs8.length ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin q)) (j : Fin n),
        insert j x = codeSet z → wVal gs8 (inpVec n x) fVal = f z := by
  let m := n + 2
  let wF := n
  let wT := n + 1
  let wPe := 2 * q
  let wPo := 2 * q + 1
  have hwF : wF < m := by dsimp only [wF, m]; omega
  have hwT : wT < m := by dsimp only [wT, m]; omega
  obtain ⟨gs7, zHat, hext67, hgs7, hnc7, hlen7, hzHatl, hzHatW, hzHat_ev⟩ :=
    exists_map_build_pair (m := m) 8 q gs6
      (fun t gsX p => ∀ x : Finset (Fin n),
        let po := drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1))
        let pe := decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x)
        let p_o := decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x)
        wVal gsX (inpVec n x) p.1 =
          ((inpVec n x).getD (2 * t + 1) false || ((po.1 && pe) || (po.2 && p_o))) ∧
        wVal gsX (inpVec n x) p.2 =
          ((inpVec n x).getD (2 * t) false || ((po.1 && p_o) || (po.2 && pe))))
      (fun t _ gsA gsB p hp1 hp2 hext hP x => by
        rw [hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega),
          hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hP x)
      (fun t ht gsA hext6A hgsA => by
        let pot := pOther.getD t (0, 0)
        have hpot_m : pot ∈ pOther := by
          dsimp only [pot]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hpotA : pot.1 < m + gsA.length ∧ pot.2 < m + gsA.length := by
          have := hext6A.length_le; have := hpOW _ hpot_m; dsimp only [m]; omega
        obtain ⟨g1, a1, hx1, hg1, hn1, hl1, hw1, he1⟩ := mkAnd_ex hgsA hpotA.1 (b := wPe) (by dsimp only [wPe, m]; omega)
        obtain ⟨g2, a2, hx2, hg2, hn2, hl2, hw2, he2⟩ := mkAnd_ex hg1 (by omega : pot.2 < m + g1.length) (b := wPo) (by dsimp only [wPo, m]; omega)
        obtain ⟨g3, recP, hx3, hg3, hn3, hl3, hw3, he3⟩ := mkOr_ex hg2 (by omega : a1 < m + g2.length) hw2
        obtain ⟨g4, zP, hx4, hg4, hn4, hl4, hw4, he4⟩ := mkOr_ex hg3 (a := 2 * t + 1) (by dsimp only [m]; omega) hw3
        obtain ⟨g5, b1, hx5, hg5, hn5, hl5, hw5, he5⟩ := mkAnd_ex hg4 (by omega : pot.1 < m + g4.length) (b := wPo) (by dsimp only [wPo, m]; omega)
        obtain ⟨g6, b2, hx6, hg6, hn6, hl6, hw6, he6⟩ := mkAnd_ex hg5 (by omega : pot.2 < m + g5.length) (b := wPe) (by dsimp only [wPe, m]; omega)
        obtain ⟨g7, recN, hx7, hg7, hn7, hl7, hw7, he7⟩ := mkOr_ex hg6 (by omega : b1 < m + g6.length) hw6
        obtain ⟨g8, zN, hx8, hg8, hn8, hl8, hw8, he8⟩ := mkOr_ex hg7 (a := 2 * t) (by dsimp only [m]; omega) hw7
        have hx48 : Extends g4 g8 := hx5.trans (hx6.trans (hx7.trans hx8))
        have hxA4 : Extends gsA g4 := hx1.trans (hx2.trans (hx3.trans hx4))
        have hxA5 : Extends gsA g5 := hxA4.trans hx5
        have hxA8 : Extends gsA g8 := hxA4.trans hx48
        have hncA8 : notCnt g8 = notCnt gsA :=
          hn8.trans (hn7.trans (hn6.trans (hn5.trans (hn4.trans (hn3.trans (hn2.trans hn1))))))
        refine ⟨g8, (zP, zN), hxA8, hg8, hncA8, by omega, by omega, hw8, ?_⟩
        intro x
        have hinp : (inpVec n x).length = m := inpVec_length n x
        have hpot_val : (wVal gsA (inpVec n x) pot.1, wVal gsA (inpVec n x) pot.2) =
            drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1)) := by
          rw [hext6A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hpot_m; omega),
            hext6A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hpot_m; omega)]
          exact hpO_ev t ht x
        have hpot1 : wVal gsA (inpVec n x) pot.1 = (drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1))).1 :=
          congrArg Prod.fst hpot_val
        have hpot2 : wVal gsA (inpVec n x) pot.2 = (drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1))).2 :=
          congrArg Prod.snd hpot_val
        have hpe_v : ∀ g : List Gate, wVal g (inpVec n x) wPe = decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) := fun g => by
          rw [evalWires_input g (inpVec n x) (by rw [inpVec_length]; dsimp only [wPe]; omega)]
          exact inpVec_getD_lt n x ⟨2 * q, by omega⟩
        have hpo_v : ∀ g : List Gate, wVal g (inpVec n x) wPo = decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) := fun g => by
          rw [evalWires_input g (inpVec n x) (by rw [inpVec_length]; dsimp only [wPo]; omega)]
          exact inpVec_getD_lt n x ⟨2 * q + 1, by omega⟩
        constructor
        · rw [hx48.wVal_eq (inpVec n x) (i := zP) (by omega), he4 (inpVec n x) hinp,
            evalWires_input g3 (inpVec n x) (by rw [inpVec_length]; omega),
            he3 (inpVec n x) hinp, hx2.wVal_eq (inpVec n x) (i := a1) (by omega),
            he1 (inpVec n x) hinp, he2 (inpVec n x) hinp,
            hx1.wVal_eq (inpVec n x) (i := pot.2) (by omega), hpot1, hpot2, hpe_v gsA, hpo_v g1]
        · rw [he8 (inpVec n x) hinp, evalWires_input g7 (inpVec n x) (by rw [inpVec_length]; omega),
            he7 (inpVec n x) hinp, hx6.wVal_eq (inpVec n x) (i := b1) (by omega),
            he5 (inpVec n x) hinp, he6 (inpVec n x) hinp,
            hxA4.wVal_eq (inpVec n x) (i := pot.1) (by omega), hxA5.wVal_eq (inpVec n x) (i := pot.2) (by omega),
            hpot1, hpot2, hpe_v g5, hpo_v g4])
      hgs6
  have hzHat_exact : ∀ (x : Finset (Fin n)) (z : Finset (Fin q)) (j : Fin n),
      insert j x = codeSet z →
      ∀ t : Fin q,
        wVal gs7 (inpVec n x) (zHat.getD t.val (0, 0)).1 = decide (t ∈ z) ∧
        wVal gs7 (inpVec n x) (zHat.getD t.val (0, 0)).2 = !(decide (t ∈ z)) := by
    intro x z j hjx t
    have hsub : x ⊆ codeSet z := by rw [← hjx]; exact Finset.subset_insert j x
    have hagree_ne : ∀ i : Fin n, i ≠ j → (i ∈ x ↔ i ∈ codeSet z) := by
      intro i hi
      have : i ∈ insert j x ↔ i ∈ codeSet z := by rw [hjx]
      simpa [Finset.mem_insert, hi] using this
    have hj_mem : j ∈ codeSet z := by rw [← hjx]; exact Finset.mem_insert_self j x
    have hj_not_last : j.val ≠ 2 * q + 3 := by
      intro h; exact not_mem_codeSet_last hn z (mem_of_fin_val_eq h hj_mem)
    have hspec := hzHat_ev t.val t.isLt x
    dsimp only at hspec
    rw [hspec.1, hspec.2, inpVec_getD_lt n x ⟨2 * t.val + 1, by omega⟩, inpVec_getD_lt n x ⟨2 * t.val, by omega⟩]
    by_cases hjt : j.val / 2 = t.val
    · have hpO : drFold ((xDataList hn x).take t.val ++ (xDataList hn x).drop (t.val + 1)) =
          (decide ((z.erase t).card % 2 = 1), decide ((z.erase t).card % 2 = 0)) := by
        apply drFold_xDataList_skip_of_agree hn t
        intro u hu
        have hne1 : (⟨2 * u.val + 1, by omega⟩ : Fin n) ≠ j := by
          intro h; have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by omega))
        have hne0 : (⟨2 * u.val, by omega⟩ : Fin n) ≠ j := by
          intro h; have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by omega))
        exact ⟨(hagree_ne _ hne1).trans (mem_codeSet_data_odd hn z u),
               (hagree_ne _ hne0).trans (mem_codeSet_data_even hn z u)⟩
      have hpe : (⟨2 * q, by omega⟩ : Fin n) ∈ x ↔ z.card % 2 = 0 :=
        (hagree_ne _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_par_even hn z)
      have hpo : (⟨2 * q + 1, by omega⟩ : Fin n) ∈ x ↔ z.card % 2 = 1 :=
        (hagree_ne _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_par_odd hn z)
      rw [hpO]; dsimp only
      have hpe_d : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 0) :=
        Bool.eq_iff_iff.2 (by simp [hpe])
      have hpo_d : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 1) :=
        Bool.eq_iff_iff.2 (by simp [hpo])
      rw [hpe_d, hpo_d]
      have hmod : z.card % 2 = 0 ∨ z.card % 2 = 1 := by omega
      by_cases htz : t ∈ z
      · have hnot0 : (⟨2 * t.val, by omega⟩ : Fin n) ∉ x := fun hm =>
          ((mem_codeSet_data_even hn z t).1 (hsub hm)) htz
        have herase : (z.erase t).card + 1 = z.card := Finset.card_erase_add_one htz
        rcases hmod with hm | hm
        · have he1 : (z.erase t).card % 2 = 1 := by omega
          rw [he1, hm]; simp [htz, hnot0]
        · have he0 : (z.erase t).card % 2 = 0 := by omega
          rw [he0, hm]; simp [htz, hnot0]
      · have hnot1 : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∉ x := fun hm =>
          htz ((mem_codeSet_data_odd hn z t).1 (hsub hm))
        have herase : (z.erase t).card = z.card := by rw [Finset.erase_eq_of_notMem htz]
        rcases hmod with hm | hm
        · rw [herase, hm]; simp [htz, hnot1]
        · rw [herase, hm]; simp [htz, hnot1]
    · have h1 : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z :=
        (hagree_ne _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_data_odd hn z t)
      have h0 : (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z :=
        (hagree_ne _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_data_even hn z t)
      have hd1 : decide ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x) = decide (t ∈ z) := Bool.eq_iff_iff.2 (by simp [h1])
      have hd0 : decide ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x) = !(decide (t ∈ z)) := Bool.eq_iff_iff.2 (by simp [h0])
      rw [hd1, hd0]
      by_cases hfull : j ∈ x ∨ j.val = 2 * q + 2
      · have hother_ag : ∀ i : Fin n, i.val < 2 * q + 2 → (i ∈ x ↔ i ∈ codeSet z) := by
          intro i hi
          rcases hfull with hjx' | hjp
          · rw [← hjx, Finset.insert_eq_of_mem hjx']
          · exact hagree_ne i (fun h => by have := congrArg Fin.val h; omega)
        have hpO : drFold ((xDataList hn x).take t.val ++ (xDataList hn x).drop (t.val + 1)) =
            (decide ((z.erase t).card % 2 = 1), decide ((z.erase t).card % 2 = 0)) := by
          apply drFold_xDataList_skip_of_agree hn t
          intro u _
          exact ⟨(hother_ag ⟨2 * u.val + 1, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_data_odd hn z u),
                 (hother_ag ⟨2 * u.val, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_data_even hn z u)⟩
        have hpe_d : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 0) :=
          Bool.eq_iff_iff.2 (by simp [(hother_ag ⟨2 * q, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_par_even hn z)])
        have hpo_d : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 1) :=
          Bool.eq_iff_iff.2 (by simp [(hother_ag ⟨2 * q + 1, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_par_odd hn z)])
        rw [hpO, hpe_d, hpo_d]; dsimp only
        have hmod : z.card % 2 = 0 ∨ z.card % 2 = 1 := by omega
        by_cases htz : t ∈ z
        · have herase : (z.erase t).card + 1 = z.card := Finset.card_erase_add_one htz
          rcases hmod with hm | hm
          · have he1 : (z.erase t).card % 2 = 1 := by omega
            rw [he1, hm]; simp [htz]
          · have he0 : (z.erase t).card % 2 = 0 := by omega
            rw [he0, hm]; simp [htz]
        · have herase : (z.erase t).card = z.card := by rw [Finset.erase_eq_of_notMem htz]
          rcases hmod with hm | hm
          · rw [herase, hm]; simp [htz]
          · rw [herase, hm]; simp [htz]
      · push Not at hfull
        rcases hfull with ⟨hjnx, hjp⟩
        by_cases hjq : j.val / 2 = q
        · have hpe_f : (⟨2 * q, by omega⟩ : Fin n) ∉ x := by
            intro hm
            by_cases hje : j.val = 2 * q
            · exact hjnx (mem_of_fin_val_eq hje.symm hm)
            · have hjo : j.val = 2 * q + 1 := by omega
              have h1' := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq hjo hj_mem)
              have h0' := (mem_codeSet_par_even hn z).1 (hsub hm)
              omega
          have hpo_f : (⟨2 * q + 1, by omega⟩ : Fin n) ∉ x := by
            intro hm
            by_cases hjo : j.val = 2 * q + 1
            · exact hjnx (mem_of_fin_val_eq hjo.symm hm)
            · have hje : j.val = 2 * q := by omega
              have h0' := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq hje hj_mem)
              have h1' := (mem_codeSet_par_odd hn z).1 (hsub hm)
              omega
          simp [hpe_f, hpo_f]
        · have ht1lt : j.val / 2 < q := by omega
          let t1 : Fin q := ⟨j.val / 2, ht1lt⟩
          have ht1ne : t1 ≠ t := fun h => hjt (congrArg Fin.val h)
          have hmiss1 : (⟨2 * t1.val + 1, by omega⟩ : Fin n) ∉ x := by
            intro hm
            by_cases hjo : j.val = 2 * t1.val + 1
            · exact hjnx (mem_of_fin_val_eq hjo.symm hm)
            · have hje : j.val = 2 * t1.val := by dsimp only [t1] at hjo ⊢; omega
              have h0' := (mem_codeSet_data_even hn z t1).1 (mem_of_fin_val_eq hje hj_mem)
              have h1' := (mem_codeSet_data_odd hn z t1).1 (hsub hm)
              exact h0' h1'
          have hmiss0 : (⟨2 * t1.val, by omega⟩ : Fin n) ∉ x := by
            intro hm
            by_cases hje : j.val = 2 * t1.val
            · exact hjnx (mem_of_fin_val_eq hje.symm hm)
            · have hjo : j.val = 2 * t1.val + 1 := by dsimp only [t1] at hje ⊢; omega
              have h1' := (mem_codeSet_data_odd hn z t1).1 (mem_of_fin_val_eq hjo hj_mem)
              have h0' := (mem_codeSet_data_even hn z t1).1 (hsub hm)
              exact h0' h1'
          have hpO : drFold ((xDataList hn x).take t.val ++ (xDataList hn x).drop (t.val + 1)) = (false, false) :=
            drFold_xDataList_skip_of_missing hn t t1 ht1ne hmiss1 hmiss0
          simp [hpO]
  let initDR : List (ℕ × ℕ) := zHat ++ [(wF, wT), (wT, wF)]
  have hinitDR_len : initDR.length = q + 2 := by simp [initDR, hzHatl]
  obtain ⟨gs8, drD, hext78, hgs8, hnc8, hlen8, hdrDl, hdrDW, hdrD_ev⟩ :=
    exists_sim_D_mono_aux wF wT hwF hwT D.gates gs7 initDR hgs7 hDok.1
      (fun j hj i hi => by rw [hinitDR_len]; exact hDok.2 j hj i hi)
      (fun p hp => by
        simp only [initDR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | rfl | rfl
        · exact hzHatW p hp
        · omega
        · omega)
  let fVal := (drD.getD D.output (0, 0)).1
  have hfVal_mem : drD.getD D.output (0, 0) ∈ drD := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hfValW : fVal < m + gs8.length := (hdrDW _ hfVal_mem).1
  refine ⟨gs8, fVal, hext67.trans hext78, hgs8, hnc8.trans hnc7, by omega, hfValW, ?_⟩
  intro x z j hjx
  have hag : ∀ i < initDR.length,
      wVal gs7 (inpVec n x) (initDR.getD i (0, 0)).1 = (inpVec q z).getD i false ∧
      wVal gs7 (inpVec n x) (initDR.getD i (0, 0)).2 = !((inpVec q z).getD i false) := by
    intro i hi
    by_cases hiq : i < q
    · have hget : initDR.getD i (0, 0) = zHat.getD i (0, 0) := by
        simp only [initDR, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < zHat.length)]
      rw [hget, inpVec_getD_lt q z ⟨i, hiq⟩]
      exact hzHat_exact x z j hjx ⟨i, hiq⟩
    · by_cases hiq0 : i = q
      · rw [hiq0]
        have hget : initDR.getD q (0, 0) = (wF, wT) := by
          rw [List.getD_eq_getElem?_getD]
          dsimp only [initDR]
          rw [List.getElem?_append_right (by omega : zHat.length ≤ q)]
          simp [hzHatl]
        rw [hget, inpVec_getD_m q z,
          evalWires_input gs7 (inpVec n x) (by rw [inpVec_length]; omega),
          evalWires_input gs7 (inpVec n x) (by rw [inpVec_length]; omega),
          inpVec_getD_m n x, inpVec_getD_m1 n x]
        exact ⟨rfl, rfl⟩
      · have hiq1 : i = q + 1 := by omega
        rw [hiq1]
        have hget : initDR.getD (q + 1) (0, 0) = (wT, wF) := by
          rw [List.getD_eq_getElem?_getD]
          dsimp only [initDR]
          rw [List.getElem?_append_right (by omega : zHat.length ≤ q + 1)]
          simp [hzHatl]
        rw [hget, inpVec_getD_m1 q z,
          evalWires_input gs7 (inpVec n x) (by rw [inpVec_length]; omega),
          evalWires_input gs7 (inpVec n x) (by rw [inpVec_length]; omega),
          inpVec_getD_m n x, inpVec_getD_m1 n x]
        exact ⟨rfl, rfl⟩
  have hev := (hdrD_ev (inpVec n x) (inpVec q z) (inpVec_length n x)
    (inpVec_getD_m n x) (inpVec_getD_m1 n x) (by rw [inpVec_length, hinitDR_len]) hag D.output (by omega)).1
  rw [hev, hDeval z]

lemma exists_goodX {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool)
    (gs8 : List Gate) (hgs8 : GateOK (n + 2) gs8)
    (parAll : ℕ × ℕ) (hparAllW : parAll.1 < n + 2 + gs8.length ∧ parAll.2 < n + 2 + gs8.length)
    (hparAll_ev : ∀ x : Finset (Fin n),
      (wVal gs8 (inpVec n x) parAll.1, wVal gs8 (inpVec n x) parAll.2) = drFold (xDataList hn x))
    (fVal : ℕ) (hfValW : fVal < n + 2 + gs8.length)
    (hfVal_exact : ∀ (x : Finset (Fin n)) (z : Finset (Fin q)) (j : Fin n),
      insert j x = codeSet z → wVal gs8 (inpVec n x) fVal = f z) :
    ∃ (gs9 : List Gate) (baseBad goodX : ℕ),
      Extends gs8 gs9 ∧ GateOK (n + 2) gs9 ∧ notCnt gs9 = notCnt gs8 ∧
      gs9.length ≤ gs8.length + 2 * (q + 1) + 6 ∧
      baseBad < n + 2 + gs9.length ∧ goodX < n + 2 + gs9.length ∧
      (∀ x : Finset (Fin n),
        wVal gs9 (inpVec n x) baseBad =
        (decide ((⟨2 * q + 3, by omega⟩ : Fin n) ∈ x) ||
         decide (∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x))) ∧
      (∀ x : Finset (Fin n),
        wVal gs9 (inpVec n x) goodX =
        (wVal gs9 (inpVec n x) baseBad ||
          (((drFold (xDataList hn x)).1 && decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x)) ||
           ((drFold (xDataList hn x)).2 && decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x))) ||
         wVal gs9 (inpVec n x) fVal)) ∧
      (∀ x : Finset (Fin n), x.card = r →
        wVal gs9 (inpVec n x) goodX = decide (∀ z : Finset (Fin q), x = codeSet z → f z = true)) := by
  let m := n + 2
  let wF := n
  let wPe := 2 * q
  let wPo := 2 * q + 1
  have hanyDbl_build : ∀ (k : ℕ) (hk : k ≤ q + 1),
      ∃ (gsA : List Gate) (wDbl : ℕ),
        Extends gs8 gsA ∧ GateOK m gsA ∧ notCnt gsA = notCnt gs8 ∧
        gsA.length ≤ gs8.length + 2 * k ∧ wDbl < m + gsA.length ∧
        ∀ x : Finset (Fin n),
          wVal gsA (inpVec n x) wDbl =
          decide (∃ t : Fin k, (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs8, wF, Extends.refl gs8, hgs8, rfl, by simp, by dsimp only [wF, m]; omega, ?_⟩
      intro x
      rw [evalWires_input gs8 (inpVec n x) (by rw [inpVec_length]; dsimp only [wF]; omega), inpVec_getD_m n x]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨gsA, wA, hext8A, hgsA, hncA, hlenA, hwA, hevA⟩ := ih (by omega)
      obtain ⟨g1, w1, hx1, hg1, hn1, hl1, hw1, he1⟩ := mkAnd_ex hgsA
        (a := 2 * k) (b := 2 * k + 1) (by dsimp only [m]; omega) (by dsimp only [m]; omega)
      obtain ⟨g2, w2, hx2, hg2, hn2, hl2, hw2, he2⟩ := mkOr_ex hg1 (by omega : wA < m + g1.length) hw1
      refine ⟨g2, w2, hext8A.trans (hx1.trans hx2), hg2, hn2.trans (hn1.trans hncA), by omega, hw2, ?_⟩
      intro x
      rw [he2 (inpVec n x) (inpVec_length n x), hx1.wVal_eq (inpVec n x) (i := wA) (by rw [inpVec_length]; omega),
        hevA x, he1 (inpVec n x) (inpVec_length n x),
        evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; omega),
        evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; omega),
        inpVec_getD_lt n x ⟨2 * k, by omega⟩, inpVec_getD_lt n x ⟨2 * k + 1, by omega⟩]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨t, h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨⟨t.val, by omega⟩, h1, h2⟩
        · exact ⟨⟨k, by omega⟩, h1, h2⟩
      · rintro ⟨t, h1, h2⟩
        by_cases htk : t.val < k
        · exact Or.inl ⟨⟨t.val, htk⟩, h1, h2⟩
        · have hteq : t.val = k := by omega
          exact Or.inr ⟨mem_of_fin_val_eq (by dsimp only; omega) h1, mem_of_fin_val_eq (by dsimp only; omega) h2⟩
  obtain ⟨gs8a, anyDbl, hext8_8a, hgs8a, hnc8a, hlen8a, hanyDblW, hanyDbl_ev⟩ := hanyDbl_build (q + 1) le_rfl
  have hle8a := hext8_8a.length_le
  have hparAll_8a : parAll.1 < m + gs8a.length ∧ parAll.2 < m + gs8a.length := by dsimp only [m]; omega
  obtain ⟨gb1, baseBad, hx1, hgb1, hnb1, hlb1, hwb1, heb1⟩ := mkOr_ex hgs8a (a := 2 * q + 3) (by dsimp only [m]; omega) hanyDblW
  obtain ⟨gb2, wp1, hx2, hgb2, hnb2, hlb2, hwb2, heb2⟩ := mkAnd_ex hgb1 (by omega : parAll.1 < m + gb1.length) (b := wPe) (by dsimp only [wPe, m]; omega)
  obtain ⟨gb3, wp2, hx3, hgb3, hnb3, hlb3, hwb3, heb3⟩ := mkAnd_ex hgb2 (by omega : parAll.2 < m + gb2.length) (b := wPo) (by dsimp only [wPo, m]; omega)
  obtain ⟨gb4, wrongParX, hx4, hgb4, hnb4, hlb4, hwb4, heb4⟩ := mkOr_ex hgb3 (by omega : wp1 < m + gb3.length) hwb3
  obtain ⟨gb5, notCodeX, hx5, hgb5, hnb5, hlb5, hwb5, heb5⟩ := mkOr_ex hgb4 (by omega : baseBad < m + gb4.length) hwb4
  obtain ⟨gs9, goodX, hx6, hgs9, hnb6, hlb6, hgoodXW, heb6⟩ := mkOr_ex hgb5 hwb5 (by dsimp only [m]; omega : fVal < m + gb5.length)
  have hx15 : Extends gb1 gb5 := hx2.trans (hx3.trans (hx4.trans hx5))
  have hx19 : Extends gb1 gs9 := hx15.trans hx6
  have hx8a_9 : Extends gs8a gs9 := hx1.trans hx19
  have hx8_9 : Extends gs8 gs9 := hext8_8a.trans hx8a_9
  have hnc9 : notCnt gs9 = notCnt gs8 :=
    (hnb6.trans (hnb5.trans (hnb4.trans (hnb3.trans (hnb2.trans hnb1))))).trans hnc8a
  have hbaseBad_ev : ∀ x : Finset (Fin n),
      wVal gs9 (inpVec n x) baseBad =
      (decide ((⟨2 * q + 3, by omega⟩ : Fin n) ∈ x) ||
       decide (∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x)) := by
    intro x
    rw [hx19.wVal_eq (inpVec n x) (i := baseBad) (by rw [inpVec_length]; omega),
      heb1 (inpVec n x) (inpVec_length n x),
      evalWires_input gs8a (inpVec n x) (by rw [inpVec_length]; omega),
      inpVec_getD_lt n x ⟨2 * q + 3, by omega⟩, hanyDbl_ev x]
  have hgoodX_ev : ∀ x : Finset (Fin n),
      wVal gs9 (inpVec n x) goodX =
      (wVal gs9 (inpVec n x) baseBad ||
        (((drFold (xDataList hn x)).1 && decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x)) ||
         ((drFold (xDataList hn x)).2 && decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x))) ||
       wVal gs9 (inpVec n x) fVal) := by
    intro x
    have hinp : (inpVec n x).length = m := inpVec_length n x
    have hx8_gb1 : Extends gs8 gb1 := hext8_8a.trans hx1
    have hx8_gb2 : Extends gs8 gb2 := hx8_gb1.trans hx2
    have hbb4 : wVal gb4 (inpVec n x) baseBad = wVal gs9 (inpVec n x) baseBad := by
      rw [(hx5.trans hx6).wVal_eq (inpVec n x) (i := baseBad) (by rw [inpVec_length]; omega)]
    have hfV5 : wVal gb5 (inpVec n x) fVal = wVal gs9 (inpVec n x) fVal := by
      rw [hx6.wVal_eq (inpVec n x) (i := fVal) (by rw [inpVec_length]; omega)]
    have hpa1 : wVal gs8 (inpVec n x) parAll.1 = (drFold (xDataList hn x)).1 := congrArg Prod.fst (hparAll_ev x)
    have hpa2 : wVal gs8 (inpVec n x) parAll.2 = (drFold (xDataList hn x)).2 := congrArg Prod.snd (hparAll_ev x)
    rw [heb6 (inpVec n x) hinp, heb5 (inpVec n x) hinp, hbb4, hfV5,
      heb4 (inpVec n x) hinp, hx3.wVal_eq (inpVec n x) (i := wp1) (by rw [inpVec_length]; omega),
      heb2 (inpVec n x) hinp, heb3 (inpVec n x) hinp,
      hx8_gb1.wVal_eq (inpVec n x) (i := parAll.1) (by rw [inpVec_length]; omega),
      hx8_gb2.wVal_eq (inpVec n x) (i := parAll.2) (by rw [inpVec_length]; omega),
      hpa1, hpa2,
      evalWires_input gb1 (inpVec n x) (by rw [inpVec_length]; dsimp only [wPe]; omega),
      evalWires_input gb2 (inpVec n x) (by rw [inpVec_length]; dsimp only [wPo]; omega),
      inpVec_getD_lt n x ⟨2 * q, by omega⟩, inpVec_getD_lt n x ⟨2 * q + 1, by omega⟩]
  refine ⟨gs9, baseBad, goodX, hx8_9, hgs9, hnc9, by omega, by dsimp only [m] at hwb1; omega, hgoodXW,
    hbaseBad_ev, hgoodX_ev, ?_⟩
  intro x hxc
  rw [hgoodX_ev x, hbaseBad_ev x]
  by_cases hcode : ∃ z : Finset (Fin q), x = codeSet z
  · rcases hcode with ⟨z, rfl⟩
    have hnl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ codeSet z := not_mem_codeSet_last hn z
    have hndbl : ¬ ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ codeSet z ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ codeSet z := by
      rintro ⟨t, h0, h1⟩
      by_cases htq : t.val < q
      · exact ((mem_codeSet_data_even hn z ⟨t.val, htq⟩).1 h0) ((mem_codeSet_data_odd hn z ⟨t.val, htq⟩).1 h1)
      · have htqe : t.val = q := by omega
        have := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h0)
        have := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h1)
        omega
    have hpar : drFold (xDataList hn (codeSet z)) = (decide (z.card % 2 = 1), decide (z.card % 2 = 0)) :=
      drFold_xDataList_of_agree hn (fun t => ⟨mem_codeSet_data_odd hn z t, mem_codeSet_data_even hn z t⟩)
    have hpe : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ codeSet z) = decide (z.card % 2 = 0) :=
      Bool.eq_iff_iff.2 (by simp [mem_codeSet_par_even hn z])
    have hpo : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ codeSet z) = decide (z.card % 2 = 1) :=
      Bool.eq_iff_iff.2 (by simp [mem_codeSet_par_odd hn z])
    have hfv : wVal gs9 (inpVec n (codeSet z)) fVal = f z := by
      rw [hx8_9.wVal_eq (inpVec n (codeSet z)) (i := fVal) (by rw [inpVec_length]; omega)]
      exact hfVal_exact (codeSet z) z ⟨2 * q + 2, by omega⟩ (Finset.insert_eq_of_mem (mem_codeSet_probe hn z))
    rw [hpar, hpe, hpo, hfv]; dsimp only
    have hmod : z.card % 2 = 0 ∨ z.card % 2 = 1 := by omega
    have hwpF : ((decide (z.card % 2 = 1) && decide (z.card % 2 = 0)) ||
                 (decide (z.card % 2 = 0) && decide (z.card % 2 = 1))) = false := by
      rcases hmod with hm | hm <;> simp [hm]
    simp only [hnl, hndbl, decide_false, hwpF, Bool.false_or]
    apply Bool.eq_iff_iff.2; rw [decide_eq_true_eq]
    constructor
    · intro hf z' hz'; rw [← codeSet_injective hn hz']; exact hf
    · intro hall; exact hall z rfl
  · push Not at hcode
    have hrhs : decide (∀ z : Finset (Fin q), x = codeSet z → f z = true) = true := by
      simp only [decide_eq_true_eq]; intro z hz; exact absurd hz (hcode z)
    rw [hrhs]
    by_cases hbad : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ x ∨
        ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x
    · rcases hbad with h1 | h2
      · simp [h1]
      · simp [h2]
    · push Not at hbad
      have hpig := pigeonhole_pairs hn (by omega : x.card = q + 2) hbad.1
        (fun t ⟨h0, h1⟩ => hbad.2 t h0 h1)
      have hpw := parity_wrong_of_ne_codeSet hn (by omega : x.card = q + 2) hbad.1
        (fun t ⟨h0, h1⟩ => hbad.2 t h0 h1) hcode
      let z : Finset (Fin q) := Finset.univ.filter fun t => (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x
      have hag : ∀ t : Fin q, ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
          ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z) := by
        intro t
        have ht1 : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z := by simp [z]
        exact ⟨ht1, (hpig.2 ⟨t.val, by omega⟩).trans (not_congr ht1)⟩
      rw [drFold_xDataList_of_agree hn hag]; dsimp only
      rcases hpw with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · change z.card % 2 = 1 at h1; simp [h0, h1]
      · change z.card % 2 = 0 at h1; simp [h0, h1]

lemma exists_goodPlus {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool)
    (gs9 : List Gate) (hgs9 : GateOK (n + 2) gs9)
    (parAll : ℕ × ℕ) (hparAllW : parAll.1 < n + 2 + gs9.length ∧ parAll.2 < n + 2 + gs9.length)
    (hparAll_ev : ∀ x : Finset (Fin n),
      (wVal gs9 (inpVec n x) parAll.1, wVal gs9 (inpVec n x) parAll.2) = drFold (xDataList hn x))
    (pOther : List (ℕ × ℕ)) (hpOl : pOther.length = q)
    (hpOW : ∀ p ∈ pOther, p.1 < n + 2 + gs9.length ∧ p.2 < n + 2 + gs9.length)
    (hpO_ev : ∀ t < q, ∀ x : Finset (Fin n),
      (wVal gs9 (inpVec n x) (pOther.getD t (0, 0)).1, wVal gs9 (inpVec n x) (pOther.getD t (0, 0)).2) =
      drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1)))
    (baseBad goodX fVal : ℕ)
    (hbbW : baseBad < n + 2 + gs9.length) (hgXW : goodX < n + 2 + gs9.length) (hfVW : fVal < n + 2 + gs9.length)
    (hbaseBad_ev : ∀ x : Finset (Fin n),
      wVal gs9 (inpVec n x) baseBad =
      (decide ((⟨2 * q + 3, by omega⟩ : Fin n) ∈ x) ||
       decide (∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x)))
    (hgoodX_ev : ∀ x : Finset (Fin n),
      wVal gs9 (inpVec n x) goodX =
      (wVal gs9 (inpVec n x) baseBad ||
        (((drFold (xDataList hn x)).1 && decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x)) ||
         ((drFold (xDataList hn x)).2 && decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x))) ||
       wVal gs9 (inpVec n x) fVal))
    (hfVal_exact : ∀ (x : Finset (Fin n)) (z : Finset (Fin q)) (j : Fin n),
      insert j x = codeSet z → wVal gs9 (inpVec n x) fVal = f z) :
    ∃ (gs10 : List Gate) (goodPlus : List ℕ),
      Extends gs9 gs10 ∧ GateOK (n + 2) gs10 ∧ notCnt gs10 = notCnt gs9 ∧
      gs10.length ≤ gs9.length + 6 * n ∧ goodPlus.length = n ∧
      (∀ w ∈ goodPlus, w < n + 2 + gs10.length) ∧
      ∀ (j : ℕ) (hj : j < n) (x : Finset (Fin n)),
        (insert (⟨j, hj⟩ : Fin n) x).card = r →
        wVal gs10 (inpVec n x) (goodPlus.getD j 0) =
          decide (∀ z : Finset (Fin q), insert (⟨j, hj⟩ : Fin n) x = codeSet z → f z = true) := by
  let m := n + 2
  let wT := n + 1
  let wPe := 2 * q
  let wPo := 2 * q + 1
  obtain ⟨gs10, goodPlus, hext9_10, hgs10, hnc10, hlen10, hgpL, hgpW, hgp_ev⟩ :=
    exists_map_build (m := m) 6 n gs9
      (fun j gsX w => ∀ (x : Finset (Fin n)) (hj : j < n),
        (insert (⟨j, hj⟩ : Fin n) x).card = r →
        wVal gsX (inpVec n x) w = decide (∀ z : Finset (Fin q), insert (⟨j, hj⟩ : Fin n) x = codeSet z → f z = true))
      (fun j _ gsA gsB w hw hext hP x hj hcard => by
        rw [hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hP x hj hcard)
      (fun j hj gsA hext9A hgsA => by
        have hle9A := hext9A.length_le
        have hbbA : baseBad < m + gsA.length := by dsimp only [m]; omega
        have hfVA : fVal < m + gsA.length := by dsimp only [m]; omega
        by_cases hj3 : j = 2 * q + 3
        · refine ⟨gsA, wT, Extends.refl gsA, hgsA, rfl, by omega, by dsimp only [wT, m]; omega, ?_⟩
          intro x _ _
          rw [evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; dsimp only [wT]; omega), inpVec_getD_m1 n x]
          symm; simp only [decide_eq_true_eq]
          intro z hz
          have hjm : (⟨j, hj⟩ : Fin n) ∈ codeSet z := by rw [← hz]; exact Finset.mem_insert_self _ x
          have hm : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ codeSet z :=
            mem_of_fin_val_eq (by dsimp only; exact hj3) hjm
          exact absurd hm (not_mem_codeSet_last hn z)
        · by_cases hj2 : j = 2 * q + 2
          · refine ⟨gsA, goodX, Extends.refl gsA, hgsA, rfl, by omega, by dsimp only [m]; omega, ?_⟩
            intro x _ hcard
            rw [hext9A.wVal_eq (inpVec n x) (i := goodX) (by rw [inpVec_length]; omega), hgoodX_ev x, hbaseBad_ev x]
            let y := insert (⟨j, hj⟩ : Fin n) x
            by_cases hcode : ∃ z : Finset (Fin q), y = codeSet z
            · rcases hcode with ⟨z, hyz⟩
              have hsub : x ⊆ codeSet z := by rw [← hyz]; exact Finset.subset_insert _ x
              have hag_ne : ∀ i : Fin n, i.val < 2 * q + 2 → (i ∈ x ↔ i ∈ codeSet z) := by
                intro i hi
                have hne : i ≠ ⟨j, hj⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                have : i ∈ y ↔ i ∈ codeSet z := by rw [hyz]
                simpa [y, Finset.mem_insert, hne] using this
              have hnl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ x := fun hm => not_mem_codeSet_last hn z (hsub hm)
              have hndbl : ¬ ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x := by
                rintro ⟨t, h0, h1⟩
                have h0' := hsub h0; have h1' := hsub h1
                by_cases htq : t.val < q
                · exact ((mem_codeSet_data_even hn z ⟨t.val, htq⟩).1 h0') ((mem_codeSet_data_odd hn z ⟨t.val, htq⟩).1 h1')
                · have htqe : t.val = q := by omega
                  have := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h0')
                  have := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h1')
                  omega
              have hpar : drFold (xDataList hn x) = (decide (z.card % 2 = 1), decide (z.card % 2 = 0)) :=
                drFold_xDataList_of_agree hn (fun t =>
                  ⟨(hag_ne ⟨2 * t.val + 1, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_data_odd hn z t),
                   (hag_ne ⟨2 * t.val, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_data_even hn z t)⟩)
              have hpe : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 0) :=
                Bool.eq_iff_iff.2 (by simp [(hag_ne ⟨2 * q, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_par_even hn z)])
              have hpo : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 1) :=
                Bool.eq_iff_iff.2 (by simp [(hag_ne ⟨2 * q + 1, by omega⟩ (by dsimp only; omega)).trans (mem_codeSet_par_odd hn z)])
              have hfv : wVal gs9 (inpVec n x) fVal = f z := hfVal_exact x z ⟨j, hj⟩ hyz
              rw [hpar, hpe, hpo, hfv]; dsimp only
              have hmod : z.card % 2 = 0 ∨ z.card % 2 = 1 := by omega
              have hwpF : ((decide (z.card % 2 = 1) && decide (z.card % 2 = 0)) ||
                           (decide (z.card % 2 = 0) && decide (z.card % 2 = 1))) = false := by
                rcases hmod with hm | hm <;> simp [hm]
              simp only [hnl, hndbl, decide_false, hwpF, Bool.false_or]
              apply Bool.eq_iff_iff.2; rw [decide_eq_true_eq]
              constructor
              · intro hf z' hz'; rw [← codeSet_injective hn (hyz.symm.trans hz')]; exact hf
              · intro hall; exact hall z hyz
            · push Not at hcode
              have hrhs : decide (∀ z : Finset (Fin q), y = codeSet z → f z = true) = true := by
                simp only [decide_eq_true_eq]; intro z hz; exact absurd hz (hcode z)
              rw [hrhs]
              by_cases hbad : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ x ∨
                  ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x
              · rcases hbad with h1 | h2
                · simp [h1]
                · simp [h2]
              · push Not at hbad
                have hy_nl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ y := by
                  simp only [y, Finset.mem_insert, not_or]
                  exact ⟨fun h => by have := congrArg Fin.val h; dsimp only at this; omega, hbad.1⟩
                have hy_ndbl : ∀ t : Fin (q + 1), ¬ ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y) := by
                  rintro t ⟨h0, h1⟩
                  simp only [y, Finset.mem_insert] at h0 h1
                  rcases h0 with h0 | h0
                  · have := congrArg Fin.val h0; dsimp only at this; omega
                  · rcases h1 with h1 | h1
                    · have := congrArg Fin.val h1; dsimp only at this; omega
                    · exact hbad.2 t h0 h1
                have hpig := pigeonhole_pairs hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl
                have hpw := parity_wrong_of_ne_codeSet hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl hcode
                have hag_xy : ∀ i : Fin n, i.val < 2 * q + 2 → (i ∈ x ↔ i ∈ y) := by
                  intro i hi; simp only [y, Finset.mem_insert]
                  have hne : i ≠ ⟨j, hj⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                  simp [hne]
                let z : Finset (Fin q) := Finset.univ.filter fun t => (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y
                have hag : ∀ t : Fin q, ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
                    ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z) := by
                  intro t
                  have h1y : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y ↔ t ∈ z := by simp [z]
                  have ht1 := (hag_xy ⟨2 * t.val + 1, by omega⟩ (by dsimp only; omega)).trans h1y
                  have ht0 := (hag_xy ⟨2 * t.val, by omega⟩ (by dsimp only; omega)).trans
                    ((hpig.2 ⟨t.val, by omega⟩).trans (not_congr h1y))
                  exact ⟨ht1, ht0⟩
                rw [drFold_xDataList_of_agree hn hag]; dsimp only
                have hpe_xy := hag_xy ⟨2 * q, by omega⟩ (by dsimp only; omega)
                have hpo_xy := hag_xy ⟨2 * q + 1, by omega⟩ (by dsimp only; omega)
                rcases hpw with ⟨h0, h1⟩ | ⟨h0, h1⟩
                · change z.card % 2 = 1 at h1; have h0x := hpe_xy.2 h0; simp [h0x, h1]
                · change z.card % 2 = 0 at h1; have h0x := hpo_xy.2 h0; simp [h0x, h1]
          · by_cases hjq : j / 2 = q
            · let partner := if j % 2 = 0 then 2 * q + 1 else 2 * q
              let parW := if j % 2 = 0 then parAll.1 else parAll.2
              have hpartA : partner < m + gsA.length := by dsimp only [partner, m]; split_ifs <;> omega
              have hparWA : parW < m + gsA.length := by dsimp only [parW, m]; split_ifs <;> omega
              obtain ⟨g1, w1, hx1, hg1, hn1, hl1, hw1, he1⟩ := mkOr_ex hgsA hbbA hpartA
              obtain ⟨g2, w2, hx2, hg2, hn2, hl2, hw2, he2⟩ := mkOr_ex hg1 hw1 (by omega : parW < m + g1.length)
              obtain ⟨g3, w3, hx3, hg3, hn3, hl3, hw3, he3⟩ := mkOr_ex hg2 hw2 (by omega : fVal < m + g2.length)
              have hx9_g1 : Extends gs9 g1 := hext9A.trans hx1
              have hx9_g2 : Extends gs9 g2 := hx9_g1.trans hx2
              refine ⟨g3, w3, hx1.trans (hx2.trans hx3), hg3, hn3.trans (hn2.trans hn1), by omega, hw3, ?_⟩
              intro x _ hcard
              have hinp : (inpVec n x).length = m := inpVec_length n x
              have hparW_val : wVal g1 (inpVec n x) parW =
                  if j % 2 = 0 then (drFold (xDataList hn x)).1 else (drFold (xDataList hn x)).2 := by
                dsimp only [parW]
                split_ifs
                · rw [hx9_g1.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
                  exact congrArg Prod.fst (hparAll_ev x)
                · rw [hx9_g1.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
                  exact congrArg Prod.snd (hparAll_ev x)
              have hval : wVal g3 (inpVec n x) w3 =
                  (wVal gs9 (inpVec n x) baseBad || decide ((⟨partner, by dsimp only [partner]; split_ifs <;> omega⟩ : Fin n) ∈ x) ||
                   (if j % 2 = 0 then (drFold (xDataList hn x)).1 else (drFold (xDataList hn x)).2) ||
                   wVal gs9 (inpVec n x) fVal) := by
                rw [he3 (inpVec n x) hinp, he2 (inpVec n x) hinp, he1 (inpVec n x) hinp,
                  hext9A.wVal_eq (inpVec n x) (i := baseBad) (by rw [inpVec_length]; omega),
                  evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; dsimp only [partner]; split_ifs <;> omega),
                  inpVec_getD_lt n x ⟨partner, by dsimp only [partner]; split_ifs <;> omega⟩,
                  hparW_val, hx9_g2.wVal_eq (inpVec n x) (i := fVal) (by rw [inpVec_length]; omega)]
              rw [hval, hbaseBad_ev x]
              let y := insert (⟨j, hj⟩ : Fin n) x
              by_cases hcode : ∃ z : Finset (Fin q), y = codeSet z
              · rcases hcode with ⟨z, hyz⟩
                have hsub : x ⊆ codeSet z := by rw [← hyz]; exact Finset.subset_insert _ x
                have hag_data : ∀ t : Fin q, ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
                    ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z) := by
                  intro t
                  have hne1 : (⟨2 * t.val + 1, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                    have := congrArg Fin.val h; dsimp only at this; omega
                  have hne0 : (⟨2 * t.val, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                    have := congrArg Fin.val h; dsimp only at this; omega
                  have h1 : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ codeSet z := by
                    have : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y ↔ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ codeSet z := by rw [hyz]
                    simpa [y, Finset.mem_insert, hne1] using this
                  have h0 : (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ (⟨2 * t.val, by omega⟩ : Fin n) ∈ codeSet z := by
                    have : (⟨2 * t.val, by omega⟩ : Fin n) ∈ y ↔ (⟨2 * t.val, by omega⟩ : Fin n) ∈ codeSet z := by rw [hyz]
                    simpa [y, Finset.mem_insert, hne0] using this
                  exact ⟨h1.trans (mem_codeSet_data_odd hn z t), h0.trans (mem_codeSet_data_even hn z t)⟩
                have hnl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ x := fun hm => not_mem_codeSet_last hn z (hsub hm)
                have hndbl : ¬ ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x := by
                  rintro ⟨t, h0, h1⟩
                  have h0' := hsub h0; have h1' := hsub h1
                  by_cases htq : t.val < q
                  · exact ((mem_codeSet_data_even hn z ⟨t.val, htq⟩).1 h0') ((mem_codeSet_data_odd hn z ⟨t.val, htq⟩).1 h1')
                  · have htqe : t.val = q := by omega
                    have := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h0')
                    have := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h1')
                    omega
                have hpar := drFold_xDataList_of_agree hn hag_data
                have hjmem : (⟨j, hj⟩ : Fin n) ∈ codeSet z := by rw [← hyz]; exact Finset.mem_insert_self _ x
                have hfv : wVal gs9 (inpVec n x) fVal = f z := hfVal_exact x z ⟨j, hj⟩ hyz
                have hpart_nm : (⟨partner, by dsimp only [partner]; split_ifs <;> omega⟩ : Fin n) ∉ x := by
                  intro hm; have hm' := hsub hm
                  by_cases hjev : j % 2 = 0
                  · have h0 := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) hjmem)
                    have h1 := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only [partner]; simp [hjev]) hm')
                    omega
                  · have h1 := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) hjmem)
                    have h0 := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only [partner]; simp [hjev]) hm')
                    omega
                have hpar_f : (if j % 2 = 0 then (drFold (xDataList hn x)).1 else (drFold (xDataList hn x)).2) = false := by
                  rw [hpar]; dsimp only
                  by_cases hjev : j % 2 = 0
                  · have h0 := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) hjmem)
                    simp [hjev, h0]
                  · have h1 := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) hjmem)
                    simp [hjev, h1]
                simp only [hnl, hndbl, hpart_nm, decide_false, hpar_f, Bool.false_or, hfv]
                apply Bool.eq_iff_iff.2; rw [decide_eq_true_eq]
                constructor
                · intro hf z' hz'; rw [← codeSet_injective hn (hyz.symm.trans hz')]; exact hf
                · intro hall; exact hall z hyz
              · push Not at hcode
                have hrhs : decide (∀ z : Finset (Fin q), y = codeSet z → f z = true) = true := by
                  simp only [decide_eq_true_eq]; intro z hz; exact absurd hz (hcode z)
                rw [hrhs]
                by_cases hbad : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ x ∨
                    (∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x) ∨
                    (⟨partner, by dsimp only [partner]; split_ifs <;> omega⟩ : Fin n) ∈ x
                · rcases hbad with h1 | h2 | h3
                  · simp [h1]
                  · simp [h2]
                  · simp [h3]
                · push Not at hbad
                  rcases hbad with ⟨hnl, hndbl, hpart_nm⟩
                  have hy_nl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ y := by
                    simp only [y, Finset.mem_insert, not_or]
                    exact ⟨fun h => by have := congrArg Fin.val h; dsimp only at this; omega, hnl⟩
                  have hy_ndbl : ∀ t : Fin (q + 1), ¬ ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y) := by
                    rintro t ⟨h0, h1⟩
                    simp only [y, Finset.mem_insert] at h0 h1
                    by_cases htq : t.val < q
                    · rcases h0 with h0 | h0
                      · have := congrArg Fin.val h0; dsimp only at this; omega
                      · rcases h1 with h1 | h1
                        · have := congrArg Fin.val h1; dsimp only at this; omega
                        · exact hndbl t h0 h1
                    · have htqe : t.val = q := by omega
                      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
                      · have := congrArg Fin.val h0; have := congrArg Fin.val h1; dsimp only at *; omega
                      · have hj0 : j = 2 * q := by have := congrArg Fin.val h0; dsimp only at this; omega
                        exact hpart_nm (mem_of_fin_val_eq (by dsimp only [partner]; simp [hj0, htqe]) h1)
                      · have hj1 : j = 2 * q + 1 := by have := congrArg Fin.val h1; dsimp only at this; omega
                        exact hpart_nm (mem_of_fin_val_eq (by dsimp only [partner]; simp [hj1, htqe]) h0)
                      · exact hndbl t h0 h1
                  have hpig := pigeonhole_pairs hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl
                  have hpw := parity_wrong_of_ne_codeSet hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl hcode
                  have hag_data_xy : ∀ i : Fin n, i.val < 2 * q → (i ∈ x ↔ i ∈ y) := by
                    intro i hi; simp only [y, Finset.mem_insert]
                    have hne : i ≠ ⟨j, hj⟩ := fun h => by have := congrArg Fin.val h; dsimp only at this; omega
                    simp [hne]
                  let z : Finset (Fin q) := Finset.univ.filter fun t => (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y
                  have hag : ∀ t : Fin q, ((⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x ↔ t ∈ z) ∧
                      ((⟨2 * t.val, by omega⟩ : Fin n) ∈ x ↔ t ∉ z) := by
                    intro t
                    have h1y : (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y ↔ t ∈ z := by simp [z]
                    have ht1 := (hag_data_xy ⟨2 * t.val + 1, by omega⟩ (by dsimp only; omega)).trans h1y
                    have ht0 := (hag_data_xy ⟨2 * t.val, by omega⟩ (by dsimp only; omega)).trans
                      ((hpig.2 ⟨t.val, by omega⟩).trans (not_congr h1y))
                    exact ⟨ht1, ht0⟩
                  rw [drFold_xDataList_of_agree hn hag]; dsimp only
                  have hpar_true : (if j % 2 = 0 then decide (z.card % 2 = 1) else decide (z.card % 2 = 0)) = true := by
                    by_cases hjev : j % 2 = 0
                    · have hm0 : (⟨2 * q, by omega⟩ : Fin n) ∈ y :=
                        mem_of_fin_val_eq (by dsimp only; omega) (Finset.mem_insert_self (⟨j, hj⟩ : Fin n) x)
                      have hnm1 : (⟨2 * q + 1, by omega⟩ : Fin n) ∉ y := (hpig.2 ⟨q, by omega⟩).1 hm0
                      rcases hpw with ⟨_, h1⟩ | ⟨h1, _⟩
                      · change z.card % 2 = 1 at h1; simp [hjev, h1]
                      · exact absurd h1 hnm1
                    · have hm1 : (⟨2 * q + 1, by omega⟩ : Fin n) ∈ y :=
                        mem_of_fin_val_eq (by dsimp only; omega) (Finset.mem_insert_self (⟨j, hj⟩ : Fin n) x)
                      have hnm0 : (⟨2 * q, by omega⟩ : Fin n) ∉ y := fun hm0 => (hpig.2 ⟨q, by omega⟩).1 hm0 hm1
                      rcases hpw with ⟨h0, _⟩ | ⟨_, h0⟩
                      · exact absurd h0 hnm0
                      · change z.card % 2 = 0 at h0; simp [hjev, h0]
                  simp [hpar_true]
            · have htlt : j / 2 < q := by omega
              let t0 : Fin q := ⟨j / 2, htlt⟩
              let partner := if j % 2 = 0 then 2 * t0.val + 1 else 2 * t0.val
              let pot := pOther.getD t0.val (0, 0)
              have hpot_m : pot ∈ pOther := by
                dsimp only [pot]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
              have hpotA : pot.1 < m + gsA.length ∧ pot.2 < m + gsA.length := by
                have := hpOW _ hpot_m; dsimp only [m]; omega
              let paW := if j % 2 = 0 then wPe else wPo
              let pbW := if j % 2 = 0 then wPo else wPe
              have hpaA : paW < m + gsA.length := by dsimp only [paW, wPe, wPo, m]; split_ifs <;> omega
              have hpbA : pbW < m + gsA.length := by dsimp only [pbW, wPe, wPo, m]; split_ifs <;> omega
              have hpartA : partner < m + gsA.length := by dsimp only [partner, t0, m]; split_ifs <;> omega
              obtain ⟨g1, w1, hx1, hg1, hn1, hl1, hw1, he1⟩ := mkAnd_ex hgsA hpotA.1 hpaA
              obtain ⟨g2, w2, hx2, hg2, hn2, hl2, hw2, he2⟩ := mkAnd_ex hg1 (by omega : pot.2 < m + g1.length) (by omega : pbW < m + g1.length)
              obtain ⟨g3, wp, hx3, hg3, hn3, hl3, hw3, he3⟩ := mkOr_ex hg2 (by omega : w1 < m + g2.length) hw2
              obtain ⟨g4, w4, hx4, hg4, hn4, hl4, hw4, he4⟩ := mkOr_ex hg3 (by omega : baseBad < m + g3.length) (by omega : partner < m + g3.length)
              obtain ⟨g5, nc, hx5, hg5, hn5, hl5, hw5, he5⟩ := mkOr_ex hg4 hw4 (by omega : wp < m + g4.length)
              obtain ⟨g6, gp, hx6, hg6, hn6, hl6, hw6, he6⟩ := mkOr_ex hg5 hw5 (by omega : fVal < m + g5.length)
              have hx9_g1 : Extends gs9 g1 := hext9A.trans hx1
              have hx9_g3 : Extends gs9 g3 := hx9_g1.trans (hx2.trans hx3)
              have hx9_g5 : Extends gs9 g5 := hx9_g3.trans (hx4.trans hx5)
              refine ⟨g6, gp, hx1.trans (hx2.trans (hx3.trans (hx4.trans (hx5.trans hx6)))), hg6,
                hn6.trans (hn5.trans (hn4.trans (hn3.trans (hn2.trans hn1)))), by omega, hw6, ?_⟩
              intro x _ hcard
              have hinp : (inpVec n x).length = m := inpVec_length n x
              have hpot1 : wVal gsA (inpVec n x) pot.1 =
                  (drFold ((xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1))).1 := by
                rw [hext9A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hpot_m; omega)]
                exact congrArg Prod.fst (hpO_ev t0.val t0.isLt x)
              have hpot2 : wVal g1 (inpVec n x) pot.2 =
                  (drFold ((xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1))).2 := by
                rw [hx9_g1.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hpot_m; omega)]
                exact congrArg Prod.snd (hpO_ev t0.val t0.isLt x)
              have hpa_v : wVal gsA (inpVec n x) paW =
                  if j % 2 = 0 then decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) else decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) := by
                dsimp only [paW]
                split_ifs
                · rw [evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; dsimp only [wPe]; omega)]
                  exact inpVec_getD_lt n x ⟨2 * q, by omega⟩
                · rw [evalWires_input gsA (inpVec n x) (by rw [inpVec_length]; dsimp only [wPo]; omega)]
                  exact inpVec_getD_lt n x ⟨2 * q + 1, by omega⟩
              have hpb_v : wVal g1 (inpVec n x) pbW =
                  if j % 2 = 0 then decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) else decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) := by
                dsimp only [pbW]
                split_ifs
                · rw [evalWires_input g1 (inpVec n x) (by rw [inpVec_length]; dsimp only [wPo]; omega)]
                  exact inpVec_getD_lt n x ⟨2 * q + 1, by omega⟩
                · rw [evalWires_input g1 (inpVec n x) (by rw [inpVec_length]; dsimp only [wPe]; omega)]
                  exact inpVec_getD_lt n x ⟨2 * q, by omega⟩
              let poVal := drFold ((xDataList hn x).take t0.val ++ (xDataList hn x).drop (t0.val + 1))
              let wpVal :=
                (poVal.1 && (if j % 2 = 0 then decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) else decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x))) ||
                (poVal.2 && (if j % 2 = 0 then decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) else decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x)))
              have hval : wVal g6 (inpVec n x) gp =
                  (wVal gs9 (inpVec n x) baseBad || decide ((⟨partner, by dsimp only [partner, t0]; split_ifs <;> omega⟩ : Fin n) ∈ x) ||
                   wpVal || wVal gs9 (inpVec n x) fVal) := by
                rw [he6 (inpVec n x) hinp, he5 (inpVec n x) hinp, he4 (inpVec n x) hinp,
                  hx4.wVal_eq (inpVec n x) (i := wp) (by rw [inpVec_length]; omega),
                  he3 (inpVec n x) hinp, hx2.wVal_eq (inpVec n x) (i := w1) (by rw [inpVec_length]; omega),
                  he1 (inpVec n x) hinp, he2 (inpVec n x) hinp,
                  hpot1, hpot2, hpa_v, hpb_v,
                  hx9_g3.wVal_eq (inpVec n x) (i := baseBad) (by rw [inpVec_length]; omega),
                  evalWires_input g3 (inpVec n x) (by rw [inpVec_length]; dsimp only [partner, t0]; split_ifs <;> omega),
                  inpVec_getD_lt n x ⟨partner, by dsimp only [partner, t0]; split_ifs <;> omega⟩,
                  hx9_g5.wVal_eq (inpVec n x) (i := fVal) (by rw [inpVec_length]; omega)]
              rw [hval, hbaseBad_ev x]
              let y := insert (⟨j, hj⟩ : Fin n) x
              by_cases hcode : ∃ z : Finset (Fin q), y = codeSet z
              · rcases hcode with ⟨z, hyz⟩
                have hsub : x ⊆ codeSet z := by rw [← hyz]; exact Finset.subset_insert _ x
                have hag_ne : ∀ i : Fin n, i ≠ ⟨j, hj⟩ → (i ∈ x ↔ i ∈ codeSet z) := by
                  intro i hi; have : i ∈ y ↔ i ∈ codeSet z := by rw [hyz]
                  simpa [y, Finset.mem_insert, hi] using this
                have hnl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ x := fun hm => not_mem_codeSet_last hn z (hsub hm)
                have hndbl : ¬ ∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x := by
                  rintro ⟨t, h0, h1⟩
                  have h0' := hsub h0; have h1' := hsub h1
                  by_cases htq : t.val < q
                  · exact ((mem_codeSet_data_even hn z ⟨t.val, htq⟩).1 h0') ((mem_codeSet_data_odd hn z ⟨t.val, htq⟩).1 h1')
                  · have htqe : t.val = q := by omega
                    have := (mem_codeSet_par_even hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h0')
                    have := (mem_codeSet_par_odd hn z).1 (mem_of_fin_val_eq (by dsimp only; omega) h1')
                    omega
                have hjmem : (⟨j, hj⟩ : Fin n) ∈ codeSet z := by rw [← hyz]; exact Finset.mem_insert_self _ x
                have hpart_nm : (⟨partner, by dsimp only [partner, t0]; split_ifs <;> omega⟩ : Fin n) ∉ x := by
                  intro hm; have hm' := hsub hm
                  by_cases hjev : j % 2 = 0
                  · have h0 := (mem_codeSet_data_even hn z t0).1 (mem_of_fin_val_eq (by dsimp only [t0]; omega) hjmem)
                    have h1 := (mem_codeSet_data_odd hn z t0).1 (mem_of_fin_val_eq (by dsimp only [partner]; simp [hjev]) hm')
                    exact h0 h1
                  · have h1 := (mem_codeSet_data_odd hn z t0).1 (mem_of_fin_val_eq (by dsimp only [t0]; omega) hjmem)
                    have h0 := (mem_codeSet_data_even hn z t0).1 (mem_of_fin_val_eq (by dsimp only [partner]; simp [hjev]) hm')
                    exact h0 h1
                have hpo_eq : poVal = (decide ((z.erase t0).card % 2 = 1), decide ((z.erase t0).card % 2 = 0)) := by
                  apply drFold_xDataList_skip_of_agree hn t0
                  intro u hu
                  have hne1 : (⟨2 * u.val + 1, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                    have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by dsimp only [t0]; omega))
                  have hne0 : (⟨2 * u.val, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                    have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by dsimp only [t0]; omega))
                  exact ⟨(hag_ne _ hne1).trans (mem_codeSet_data_odd hn z u),
                         (hag_ne _ hne0).trans (mem_codeSet_data_even hn z u)⟩
                have hpe_d : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 0) :=
                  Bool.eq_iff_iff.2 (by simp [(hag_ne ⟨2 * q, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_par_even hn z)])
                have hpo_d : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) = decide (z.card % 2 = 1) :=
                  Bool.eq_iff_iff.2 (by simp [(hag_ne ⟨2 * q + 1, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)).trans (mem_codeSet_par_odd hn z)])
                have hwp_f : wpVal = false := by
                  dsimp only [wpVal]
                  rw [hpo_eq, hpe_d, hpo_d]; dsimp only
                  have hmod : z.card % 2 = 0 ∨ z.card % 2 = 1 := by omega
                  by_cases hjev : j % 2 = 0
                  · have hnt : t0 ∉ z := (mem_codeSet_data_even hn z t0).1 (mem_of_fin_val_eq (by dsimp only [t0]; omega) hjmem)
                    have he : (z.erase t0).card = z.card := by rw [Finset.erase_eq_of_notMem hnt]
                    rcases hmod with hm | hm
                    · rw [he, hm]; simp [hjev]
                    · rw [he, hm]; simp [hjev]
                  · have ht : t0 ∈ z := (mem_codeSet_data_odd hn z t0).1 (mem_of_fin_val_eq (by dsimp only [t0]; omega) hjmem)
                    have he : (z.erase t0).card + 1 = z.card := Finset.card_erase_add_one ht
                    rcases hmod with hm | hm
                    · have he1 : (z.erase t0).card % 2 = 1 := by omega
                      rw [he1, hm]; simp [hjev]
                    · have he0 : (z.erase t0).card % 2 = 0 := by omega
                      rw [he0, hm]; simp [hjev]
                have hfv : wVal gs9 (inpVec n x) fVal = f z := hfVal_exact x z ⟨j, hj⟩ hyz
                simp only [hnl, hndbl, hpart_nm, decide_false, hwp_f, Bool.false_or, hfv]
                apply Bool.eq_iff_iff.2; rw [decide_eq_true_eq]
                constructor
                · intro hf z' hz'; rw [← codeSet_injective hn (hyz.symm.trans hz')]; exact hf
                · intro hall; exact hall z hyz
              · push Not at hcode
                have hrhs : decide (∀ z : Finset (Fin q), y = codeSet z → f z = true) = true := by
                  simp only [decide_eq_true_eq]; intro z hz; exact absurd hz (hcode z)
                rw [hrhs]
                by_cases hbad : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ x ∨
                    (∃ t : Fin (q + 1), (⟨2 * t.val, by omega⟩ : Fin n) ∈ x ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ x) ∨
                    (⟨partner, by dsimp only [partner, t0]; split_ifs <;> omega⟩ : Fin n) ∈ x
                · rcases hbad with h1 | h2 | h3
                  · simp [h1]
                  · simp [h2]
                  · simp [h3]
                · push Not at hbad
                  rcases hbad with ⟨hnl, hndbl, hpart_nm⟩
                  have hy_nl : (⟨2 * q + 3, by omega⟩ : Fin n) ∉ y := by
                    simp only [y, Finset.mem_insert, not_or]
                    exact ⟨fun h => by have := congrArg Fin.val h; dsimp only at this; omega, hnl⟩
                  have hy_ndbl : ∀ t : Fin (q + 1), ¬ ((⟨2 * t.val, by omega⟩ : Fin n) ∈ y ∧ (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y) := by
                    rintro t ⟨h0, h1⟩
                    simp only [y, Finset.mem_insert] at h0 h1
                    by_cases htt0 : t.val = t0.val
                    · rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
                      · have := congrArg Fin.val h0; have := congrArg Fin.val h1; dsimp only at *; omega
                      · have hj0 : j = 2 * t0.val := by have := congrArg Fin.val h0; dsimp only at this; omega
                        exact hpart_nm (mem_of_fin_val_eq (by dsimp only [partner]; simp [hj0, htt0]) h1)
                      · have hj1 : j = 2 * t0.val + 1 := by have := congrArg Fin.val h1; dsimp only at this; omega
                        exact hpart_nm (mem_of_fin_val_eq (by dsimp only [partner]; simp [hj1, htt0]) h0)
                      · exact hndbl t h0 h1
                    · rcases h0 with h0 | h0
                      · have := congrArg Fin.val h0; dsimp only [t0] at *; omega
                      · rcases h1 with h1 | h1
                        · have := congrArg Fin.val h1; dsimp only [t0] at *; omega
                        · exact hndbl t h0 h1
                  have hpig := pigeonhole_pairs hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl
                  have hpw := parity_wrong_of_ne_codeSet hn (by dsimp only [y]; omega : y.card = q + 2) hy_nl hy_ndbl hcode
                  let z : Finset (Fin q) := Finset.univ.filter fun t => (⟨2 * t.val + 1, by omega⟩ : Fin n) ∈ y
                  have hag_ne_xy : ∀ i : Fin n, i ≠ ⟨j, hj⟩ → (i ∈ x ↔ i ∈ y) := by
                    intro i hi; simp [y, Finset.mem_insert, hi]
                  have hpo_eq : poVal = (decide ((z.erase t0).card % 2 = 1), decide ((z.erase t0).card % 2 = 0)) := by
                    apply drFold_xDataList_skip_of_agree hn t0
                    intro u hu
                    have hne1 : (⟨2 * u.val + 1, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                      have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by dsimp only [t0]; omega))
                    have hne0 : (⟨2 * u.val, by omega⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => by
                      have := congrArg Fin.val h; dsimp only at this; exact hu (Fin.ext (by dsimp only [t0]; omega))
                    have h1 : (⟨2 * u.val + 1, by omega⟩ : Fin n) ∈ y ↔ u ∈ z := by simp [z]
                    have h0 : (⟨2 * u.val, by omega⟩ : Fin n) ∈ y ↔ u ∉ z :=
                      (hpig.2 ⟨u.val, by omega⟩).trans (not_congr h1)
                    exact ⟨(hag_ne_xy _ hne1).trans h1, (hag_ne_xy _ hne0).trans h0⟩
                  have hpe_xy : (⟨2 * q, by omega⟩ : Fin n) ∈ x ↔ (⟨2 * q, by omega⟩ : Fin n) ∈ y :=
                    hag_ne_xy ⟨2 * q, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
                  have hpo_xy : (⟨2 * q + 1, by omega⟩ : Fin n) ∈ x ↔ (⟨2 * q + 1, by omega⟩ : Fin n) ∈ y :=
                    hag_ne_xy ⟨2 * q + 1, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
                  have hwp_t : wpVal = true := by
                    dsimp only [wpVal]
                    rw [hpo_eq]; dsimp only
                    have hpe_d : decide ((⟨2 * q, by omega⟩ : Fin n) ∈ x) = decide ((⟨2 * q, by omega⟩ : Fin n) ∈ y) :=
                      Bool.eq_iff_iff.2 (by simp [hpe_xy])
                    have hpo_d : decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ x) = decide ((⟨2 * q + 1, by omega⟩ : Fin n) ∈ y) :=
                      Bool.eq_iff_iff.2 (by simp [hpo_xy])
                    rw [hpe_d, hpo_d]
                    by_cases hjev : j % 2 = 0
                    · have hm0 : (⟨2 * t0.val, by omega⟩ : Fin n) ∈ y :=
                        mem_of_fin_val_eq (by dsimp only [t0]; omega) (Finset.mem_insert_self (⟨j, hj⟩ : Fin n) x)
                      have hnt : t0 ∉ z := by
                        simp only [z, Finset.mem_filter, Finset.mem_univ, true_and]
                        exact (hpig.2 ⟨t0.val, by omega⟩).1 hm0
                      have he : (z.erase t0).card = z.card := by rw [Finset.erase_eq_of_notMem hnt]
                      rcases hpw with ⟨h0, h1⟩ | ⟨h0, h1⟩
                      · change z.card % 2 = 1 at h1; rw [he, h1]; simp [hjev, h0]
                      · change z.card % 2 = 0 at h1; rw [he, h1]; simp [hjev, h0]
                    · have hm1 : (⟨2 * t0.val + 1, by omega⟩ : Fin n) ∈ y :=
                        mem_of_fin_val_eq (by dsimp only [t0]; omega) (Finset.mem_insert_self (⟨j, hj⟩ : Fin n) x)
                      have ht : t0 ∈ z := by simp only [z, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm1
                      have he : (z.erase t0).card + 1 = z.card := Finset.card_erase_add_one ht
                      rcases hpw with ⟨h0, h1⟩ | ⟨h0, h1⟩
                      · change z.card % 2 = 1 at h1
                        have he0 : (z.erase t0).card % 2 = 0 := by omega
                        rw [he0]; simp [hjev, h0]
                      · change z.card % 2 = 0 at h1
                        have he1 : (z.erase t0).card % 2 = 1 := by omega
                        rw [he1]; simp [hjev, h0]
                  simp [hwp_t])
      hgs9
  exact ⟨gs10, goodPlus, hext9_10, hgs10, hnc10, hlen10, hgpL, hgpW, fun j hj x hcard => hgp_ev j hj x hj hcard⟩

lemma winRm1_decide_eq (r c : ℕ) (hr : 1 ≤ r) :
    decide (r - 1 ≤ 0 + c) = decide (r ≤ c + 1) := by
  apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega

lemma winR_decide_eq (r c : ℕ) :
    decide (r ≤ 0 + c) = decide (r + 1 ≤ c + 1) := by
  apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega

lemma part1_len_bound {b q r n dL l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 l12 l13 l14 l15 : ℕ}
    (hr : r = q + 2) (hn : n = 2 * q + 4) (h2b : 2 ^ b ≤ n + 2)
    (h1 : l1 ≤ 0 + (b + 1) * (b + 1 + 1) * (n + 2))
    (h2 : l2 ≤ l1 + 4 * (b + 1) * (b + 1 + 2) * (n + 2))
    (h3 : l3 ≤ l2 + 4 * (b + 1) * (b + 1 + 2) * (n + 2))
    (h4 : l4 ≤ l3 + 6 * q) (h5 : l5 ≤ l4 + 6 * q) (h6 : l6 ≤ l5 + 6 * q)
    (h8 : l8 ≤ l6 + 8 * q + 2 * dL) (h9 : l9 ≤ l8 + 2 * (q + 1) + 6)
    (h10 : l10 ≤ l9 + 6 * n) (h11 : l11 = l10 + 2)
    (h12 : l12 ≤ l11 + 5 * 2 ^ b) (h13 : l13 ≤ l12 + (r - 2))
    (h14 : l14 ≤ l13 + 2 * (b + 1) * (b + 1 + 1) * (n + 2))
    (h15 : l15 ≤ l14 + 5 * n) :
    l15 ≤ 2 * dL + 128 * (n + 2) * (b + 1 + 2) ^ 2 := by
  have hquad : (b + 1) * (b + 1 + 1) * (n + 2) + 4 * (b + 1) * (b + 1 + 2) * (n + 2) +
      4 * (b + 1) * (b + 1 + 2) * (n + 2) + 2 * (b + 1) * (b + 1 + 1) * (n + 2) + 50 * (n + 2) ≤
      128 * (n + 2) * (b + 1 + 2) ^ 2 := by nlinarith
  omega

lemma exists_taps {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool)
    (gs14 : List Gate) (hgs14 : GateOK (n + 2) gs14)
    (winRm1 winR goodPlus revOut : List ℕ)
    (hwinRm1_len : n ≤ winRm1.length) (hwinR_len : n ≤ winR.length)
    (hgp_len : goodPlus.length = n) (hrev_len : n ≤ revOut.length)
    (hwinRm1W : ∀ w ∈ winRm1, w < n + 2 + gs14.length)
    (hwinRW : ∀ w ∈ winR, w < n + 2 + gs14.length)
    (hgpW : ∀ w ∈ goodPlus, w < n + 2 + gs14.length)
    (hrevW : ∀ w ∈ revOut, w < n + 2 + gs14.length)
    (wLeRm2 wEqRm1 : ℕ)
    (hwLeW : wLeRm2 < n + 2 + gs14.length) (hwEqW : wEqRm1 < n + 2 + gs14.length)
    (hleR_ev : ∀ x : Finset (Fin n), wVal gs14 (inpVec n x) wLeRm2 = decide (RVal r f x ≤ r - 2))
    (heqR_ev : ∀ x : Finset (Fin n), wVal gs14 (inpVec n x) wEqRm1 = decide (RVal r f x = r - 1))
    (hrev_spec : ∀ x : Finset (Fin n), RVal r f x ≤ r - 2 → ∀ j : Fin n,
      wVal gs14 (inpVec n x) (revOut.getD j.val 0) = decide (j ∉ x))
    (hwinRm1_all : ∀ (x : Finset (Fin n)) (j : ℕ) (hj : j < n),
      wVal gs14 (inpVec n x) (winRm1.getD j 0) = decide (r ≤ (insert (⟨j, hj⟩ : Fin n) x).card))
    (hwinR_all : ∀ (x : Finset (Fin n)) (j : ℕ) (hj : j < n),
      wVal gs14 (inpVec n x) (winR.getD j 0) = decide (r + 1 ≤ (insert (⟨j, hj⟩ : Fin n) x).card))
    (hgp_ev : ∀ (j : ℕ) (hj : j < n) (x : Finset (Fin n)),
      (insert (⟨j, hj⟩ : Fin n) x).card = r →
      wVal gs14 (inpVec n x) (goodPlus.getD j 0) =
        decide (∀ z : Finset (Fin q), insert (⟨j, hj⟩ : Fin n) x = codeSet z → f z = true)) :
    ∃ (gs15 : List Gate) (taps : List ℕ),
      Extends gs14 gs15 ∧ GateOK (n + 2) gs15 ∧ notCnt gs15 = notCnt gs14 ∧
      gs15.length ≤ gs14.length + 5 * n ∧ taps.length = n ∧
      (∀ w ∈ taps, w < n + 2 + gs15.length) ∧
      ∀ (x : Finset (Fin n)) (j : Fin n),
        wVal gs15 (inpVec n x) (taps.getD j.val 0) = gainVal r f x j := by
  let m := n + 2
  obtain ⟨gs15, taps, hext14_15, hgs15, hnc15, hlen15, htapsL, htapsW, htaps_ev⟩ :=
    exists_map_build (m := m) 5 n gs14
      (fun j gsX w => ∀ (x : Finset (Fin n)) (hj : j < n), wVal gsX (inpVec n x) w = gainVal r f x ⟨j, hj⟩)
      (fun j _ gsA gsB w hw hext hP x hj => by
        rw [hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hP x hj)
      (fun j hj gsA hext14A hgsA => by
        let w1j := winRm1.getD j 0
        let wRj := winR.getD j 0
        let gpj := goodPlus.getD j 0
        let revj := revOut.getD j 0
        have hw1j_m : w1j ∈ winRm1 := by
          dsimp only [w1j]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hwRj_m : wRj ∈ winR := by
          dsimp only [wRj]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hgpj_m : gpj ∈ goodPlus := by
          dsimp only [gpj]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hrevj_m : revj ∈ revOut := by
          dsimp only [revj]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hle14A := hext14A.length_le
        have hw1jA : w1j < m + gsA.length := by have := hwinRm1W _ hw1j_m; dsimp only [m]; omega
        have hwRjA : wRj < m + gsA.length := by have := hwinRW _ hwRj_m; dsimp only [m]; omega
        have hgpjA : gpj < m + gsA.length := by have := hgpW _ hgpj_m; dsimp only [m]; omega
        have hrevjA : revj < m + gsA.length := by have := hrevW _ hrevj_m; dsimp only [m]; omega
        have hleA : wLeRm2 < m + gsA.length := by dsimp only [m]; omega
        have heqA : wEqRm1 < m + gsA.length := by dsimp only [m]; omega
        obtain ⟨g1, s1, hx1, hg1, hn1, hl1, hw1, he1⟩ := mkAnd_ex hgsA hw1jA hgpjA
        obtain ⟨g2, spanW, hx2, hg2, hn2, hl2, hw2, he2⟩ := mkOr_ex hg1 (by omega : wRj < m + g1.length) hw1
        obtain ⟨g3, p1, hx3, hg3, hn3, hl3, hw3, he3⟩ := mkAnd_ex hg2 (by omega : wLeRm2 < m + g2.length) (by omega : revj < m + g2.length)
        obtain ⟨g4, p2, hx4, hg4, hn4, hl4, hw4, he4⟩ := mkAnd_ex hg3 (by omega : wEqRm1 < m + g3.length) (by omega : spanW < m + g3.length)
        obtain ⟨g5, tapW, hx5, hg5, hn5, hl5, hw5, he5⟩ := mkOr_ex hg4 (by omega : p1 < m + g4.length) hw4
        have hxA2 : Extends gsA g2 := hx1.trans hx2
        have hxA3 : Extends gsA g3 := hxA2.trans hx3
        refine ⟨g5, tapW, hxA3.trans (hx4.trans hx5), hg5,
          hn5.trans (hn4.trans (hn3.trans (hn2.trans hn1))), by omega, hw5, ?_⟩
        intro x _
        have hinp : (inpVec n x).length = m := inpVec_length n x
        rw [he5 (inpVec n x) hinp, hx4.wVal_eq (inpVec n x) (i := p1) (by rw [inpVec_length]; omega),
          he3 (inpVec n x) hinp, he4 (inpVec n x) hinp,
          hxA3.wVal_eq (inpVec n x) (i := wEqRm1) (by rw [inpVec_length]; omega),
          hxA2.wVal_eq (inpVec n x) (i := wLeRm2) (by rw [inpVec_length]; omega),
          hxA2.wVal_eq (inpVec n x) (i := revj) (by rw [inpVec_length]; omega),
          hx3.wVal_eq (inpVec n x) (i := spanW) (by rw [inpVec_length]; omega),
          he2 (inpVec n x) hinp, hx1.wVal_eq (inpVec n x) (i := wRj) (by rw [inpVec_length]; omega),
          he1 (inpVec n x) hinp,
          hext14A.wVal_eq (inpVec n x) (i := wLeRm2) (by rw [inpVec_length]; omega),
          hext14A.wVal_eq (inpVec n x) (i := wEqRm1) (by rw [inpVec_length]; omega),
          hext14A.wVal_eq (inpVec n x) (i := revj) (by rw [inpVec_length]; have := hrevW _ hrevj_m; omega),
          hext14A.wVal_eq (inpVec n x) (i := wRj) (by rw [inpVec_length]; have := hwinRW _ hwRj_m; omega),
          hext14A.wVal_eq (inpVec n x) (i := w1j) (by rw [inpVec_length]; have := hwinRm1W _ hw1j_m; omega),
          hext14A.wVal_eq (inpVec n x) (i := gpj) (by rw [inpVec_length]; have := hgpW _ hgpj_m; omega),
          hleR_ev x, heqR_ev x]
        have hRle := RVal_le r f x
        by_cases hle2 : RVal r f x ≤ r - 2
        · have hne1 : RVal r f x ≠ r - 1 := by omega
          simp only [hle2, decide_true, Bool.true_and, hne1, decide_false, Bool.false_and, Bool.or_false]
          rw [hrev_spec x hle2 ⟨j, hj⟩, gainVal_of_le_rm2 hr hn f hle2 ⟨j, hj⟩]
        · by_cases heq1 : RVal r f x = r - 1
          · simp only [hle2, decide_false, Bool.false_and, Bool.false_or]
            simp only [heq1, decide_true, Bool.true_and]
            rw [hwinR_all x j hj, hwinRm1_all x j hj, gainVal_of_eq_rm1 hr f heq1 ⟨j, hj⟩]
            by_cases hgt' : r + 1 ≤ (insert (⟨j, hj⟩ : Fin n) x).card
            · simp only [hgt', decide_true, Bool.true_or]
              symm; rw [decide_eq_true_eq]
              exact RVal_eq_r_of_card_gt hr hn f (by omega)
            · by_cases hge' : r ≤ (insert (⟨j, hj⟩ : Fin n) x).card
              · have hcard : (insert (⟨j, hj⟩ : Fin n) x).card = r := by omega
                simp only [hgt', decide_false, Bool.false_or, hge', decide_true, Bool.true_and]
                rw [hgp_ev j hj x hcard]
                apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
                rw [RVal_eq_r_iff hr hn f]
                simp [hcard]
              · simp only [hgt', hge', decide_false, Bool.false_and, Bool.false_or]
                symm; simp only [decide_eq_false_iff_not]
                rw [RVal_eq_r_iff hr hn f]; omega
          · have heqr : RVal r f x = r := by omega
            simp only [hle2, heq1, decide_false, Bool.false_and, Bool.or_false]
            exact (gainVal_of_eq_r f heqr ⟨j, hj⟩).symm)
      hgs14
  exact ⟨gs15, taps, hext14_15, hgs15, hnc15, hlen15, htapsL, htapsW, fun x j => htaps_ev j.val j.isLt x j.isLt⟩

lemma L_lib_1275_part1 (b : ℕ) (hb : 2 ≤ b)
    (f : Finset (Fin (2 ^ b - 1 - 2)) → Bool)
    (D : Circuit)
    (hDok : GateOK (2 ^ b - 1 - 2 + 2) D.gates)
    (hDout : D.output < 2 ^ b - 1 - 2 + 2 + D.gates.length)
    (hDeval : ∀ z : Finset (Fin (2 ^ b - 1 - 2)),
      (evalWires D.gates (inpVec (2 ^ b - 1 - 2) z)).getD D.output false = f z) :
    let r := 2 ^ b - 1
    let n := 2 * r
    ∃ (gs : List Gate) (taps : List ℕ),
      GateOK (n + 2) gs ∧ notCnt gs = b ∧
      gs.length ≤ 2 * D.gates.length + 128 * (n + 2) * (Nat.log2 (n + 2) + 2) ^ 2 ∧
      taps.length = n ∧ (∀ w ∈ taps, w < n + 2 + gs.length) ∧
      ∀ (x : Finset (Fin n)) (j : Fin n),
        wVal gs (inpVec n x) (taps.getD j.val 0) = gainVal r f x j := by
  intro r n
  let q := r - 2
  have h2b4 : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
  have hr : r = q + 2 := by dsimp only [r, q]; omega
  have hn : n = 2 * q + 4 := by dsimp only [n, r, q]; omega
  have hNpow : n + 2 = 2 ^ (b + 1) := by
    dsimp only [n, r]
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    omega
  have hlog : Nat.log2 (n + 2) = b + 1 := by
    rw [hNpow, Nat.log2_eq_iff (by positivity)]
    have h2 : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by ring
    have hpos := Nat.two_pow_pos (b + 1)
    exact ⟨le_rfl, by omega⟩
  let m := n + 2
  let wF := n
  let wT := n + 1
  have hwF : wF < m := by dsimp only [wF, m]; omega
  have hwT : wT < m := by dsimp only [wT, m]; omega
  let padIn : List ℕ := List.ofFn (fun i : Fin n => i.val) ++ [wF, wF]
  have hpadIn_len : padIn.length = 2 ^ (b + 1) := by simp [padIn, ← hNpow]
  have hpadIn_W : ∀ w ∈ padIn, w < m + ([] : List Gate).length := by
    intro w hw
    simp only [padIn, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ⟨i, rfl⟩ | rfl | rfl <;> dsimp only [m, wF] <;> omega
  have hpadIn_cnt : ∀ x : Finset (Fin n),
      (padIn.map (wVal [] (inpVec n x))).count true = x.card := by
    intro x
    have hmap : padIn.map (wVal [] (inpVec n x)) =
        List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, false] := by
      simp only [padIn, List.map_append, List.map_ofFn, List.map_cons, List.map_nil]
      congr 1
      · apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hin : i < n := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn, Function.comp_apply]
        rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega)]
        exact inpVec_getD_lt n x ⟨i, hin⟩
      · rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; dsimp only [wF]; omega),
          inpVec_getD_m n x]
    rw [hmap, List.count_append, count_true_ofFn_mem]
    simp

  obtain ⟨gs1, ys, hext01, hgs1, hnc1, hlen1, hysl, hysW, hsort_ev, hsort_rev, hsort_win⟩ :=
    exists_sort_full (m := m) wF hwF (b + 1) [] padIn (GateOK_nil m) hpadIn_len hpadIn_W

  let rootRm1 : List ℕ := List.ofFn fun t : Fin (2 ^ (b + 1)) => if r - 1 + 1 + t.val ≤ 2 ^ (b + 1) then wT else wF
  obtain ⟨gs2, winRm1, hext12, hgs2, hnc2, hlen2, hwinRm1l, hwinRm1W, hwinRm1_ev⟩ :=
    hsort_win (r - 1) gs1 rootRm1 (Extends.refl gs1) hgs1 (by simp [rootRm1])
      (fun w hw => by
        simp only [rootRm1, List.mem_ofFn] at hw
        rcases hw with ⟨t, rfl⟩; split_ifs <;> omega)
  let rootR : List ℕ := List.ofFn fun t : Fin (2 ^ (b + 1)) => if r + 1 + t.val ≤ 2 ^ (b + 1) then wT else wF
  obtain ⟨gs3, winR, hext23, hgs3, hnc3, hlen3, hwinRl, hwinRW, hwinR_ev⟩ :=
    hsort_win r gs2 rootR hext12 hgs2 (by simp [rootR])
      (fun w hw => by
        simp only [rootR, List.mem_ofFn] at hw
        rcases hw with ⟨t, rfl⟩; split_ifs <;> omega)

  let dataPairs : List (ℕ × ℕ) := List.ofFn fun t : Fin q => (2 * t.val + 1, 2 * t.val)
  have hdp_len : dataPairs.length = q := by simp [dataPairs]
  have hdp_W : ∀ p ∈ dataPairs, p.1 < m + gs3.length ∧ p.2 < m + gs3.length := by
    intro p hp; simp only [dataPairs, List.mem_ofFn] at hp
    rcases hp with ⟨t, rfl⟩; dsimp only [m]; omega
  obtain ⟨gs4, pref, hext34, hgs4, hnc4, hlen4, hprefl, hprefW, hpref_ev⟩ :=
    exists_drPref wF wT hwF hwT dataPairs gs3 hgs3 hdp_W
  obtain ⟨gs5, suff, hext45, hgs5, hnc5, hlen5, hsuffl, hsuffW, hsuff_ev⟩ :=
    exists_drSuff wF wT hwF hwT dataPairs gs4 hgs4
      (fun p hp => by have := hext34.length_le; have := hdp_W p hp; omega)
  have hdp_map : ∀ (gsX : List Gate) (x : Finset (Fin n)),
      dataPairs.map (fun p => (wVal gsX (inpVec n x) p.1, wVal gsX (inpVec n x) p.2)) = xDataList hn x := by
    intro gsX x
    apply List.ext_getElem
    · simp [dataPairs, xDataList]
    · intro i hi1 hi2
      have hiq : i < q := by simp [dataPairs] at hi1; exact hi1
      simp only [dataPairs, xDataList, List.getElem_map, List.getElem_ofFn, Prod.mk.injEq]
      rw [evalWires_input gsX (inpVec n x) (by rw [inpVec_length]; omega),
        evalWires_input gsX (inpVec n x) (by rw [inpVec_length]; omega)]
      exact ⟨inpVec_getD_lt n x ⟨2 * i + 1, by omega⟩, inpVec_getD_lt n x ⟨2 * i, by omega⟩⟩
  obtain ⟨gs6, pOther, hext56, hgs6, hnc6, hlen6, hpOl, hpOW, hpO_ev⟩ :=
    exists_map_build_pair (m := m) 6 q gs5
      (fun t gsX p => ∀ x : Finset (Fin n),
        (wVal gsX (inpVec n x) p.1, wVal gsX (inpVec n x) p.2) =
        drFold ((xDataList hn x).take t ++ (xDataList hn x).drop (t + 1)))
      (fun t _ gsA gsB p hp1 hp2 hext hP x => by
        rw [hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega),
          hext.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hP x)
      (fun t ht gsA hext5A hgsA => by
        let pt := pref.getD t (0, 0)
        let st := suff.getD (t + 1) (0, 0)
        have hpt_m : pt ∈ pref := by
          dsimp only [pt]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hst_m : st ∈ suff := by
          dsimp only [st]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hext4A : Extends gs4 gsA := hext45.trans hext5A
        have hptA : pt.1 < m + gsA.length ∧ pt.2 < m + gsA.length := by
          have := hext4A.length_le; have := hprefW _ hpt_m; omega
        have hstA : st.1 < m + gsA.length ∧ st.2 < m + gsA.length := by
          have := hext5A.length_le; have := hsuffW _ hst_m; omega
        obtain ⟨gsB, outP, hextAB, hgsB, hncB, hlenB, ho1, ho2, hevB⟩ :=
          exists_drXor hgsA hptA.1 hptA.2 hstA.1 hstA.2
        refine ⟨gsB, outP, hextAB, hgsB, hncB, hlenB, ho1, ho2, ?_⟩
        intro x
        rw [hevB (inpVec n x) (inpVec_length n x),
          hext4A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hprefW _ hpt_m; omega),
          hext4A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hprefW _ hpt_m; omega),
          hext5A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hsuffW _ hst_m; omega),
          hext5A.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hsuffW _ hst_m; omega),
          hpref_ev (inpVec n x) (inpVec_length n x) (inpVec_getD_m n x) (inpVec_getD_m1 n x) t (by omega),
          hsuff_ev (inpVec n x) (inpVec_length n x) (inpVec_getD_m n x) (inpVec_getD_m1 n x) (t + 1) (by omega),
          List.map_take, List.map_drop, hdp_map gs3 x, hdp_map gs4 x, ← drFold_append])
      hgs5

  obtain ⟨gs8, fVal, hext68, hgs8, hnc8, hlen8, hfValW, hfVal_exact⟩ :=
    exists_zHat_and_fVal hn f D hDok hDout hDeval gs6 hgs6 pOther hpOl hpOW hpO_ev

  let parAll := pref.getD q (0, 0)
  have hparAll_m : parAll ∈ pref := by
    dsimp only [parAll]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hext48 : Extends gs4 gs8 := hext45.trans (hext56.trans hext68)
  have hparAll_8 : parAll.1 < n + 2 + gs8.length ∧ parAll.2 < n + 2 + gs8.length := by
    have := hext48.length_le; have := hprefW _ hparAll_m; dsimp only [m] at this; omega
  have hparAll_ev8 : ∀ x : Finset (Fin n),
      (wVal gs8 (inpVec n x) parAll.1, wVal gs8 (inpVec n x) parAll.2) = drFold (xDataList hn x) := by
    intro x
    rw [hext48.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hprefW _ hparAll_m; omega),
      hext48.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hprefW _ hparAll_m; omega)]
    have h := hpref_ev (inpVec n x) (inpVec_length n x) (inpVec_getD_m n x) (inpVec_getD_m1 n x) q (by omega)
    rw [List.take_of_length_le (by omega), hdp_map gs3 x] at h
    exact h
  obtain ⟨gs9, baseBad, goodX, hext89, hgs9, hnc9, hlen9, hbbW, hgoodXW, hbaseBad_ev, hgoodX_ev, hgoodX_spec⟩ :=
    exists_goodX hr hn f gs8 hgs8 parAll hparAll_8 hparAll_ev8 fVal hfValW hfVal_exact

  have hext69 : Extends gs6 gs9 := hext68.trans hext89
  obtain ⟨gs10, goodPlus, hext9_10, hgs10, hnc10, hlen10, hgpL, hgpW, hgp_ev⟩ :=
    exists_goodPlus hr hn f gs9 hgs9 parAll
      (by have := hext89.length_le; omega)
      (fun x => by
        rw [hext89.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega),
          hext89.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hparAll_ev8 x)
      pOther hpOl
      (fun p hp => by have := hext69.length_le; have := hpOW p hp; dsimp only [m] at this; omega)
      (fun t ht x => by
        have hm : pOther.getD t (0, 0) ∈ pOther := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext69.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hm; omega),
          hext69.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hpOW _ hm; omega)]
        exact hpO_ev t ht x)
      baseBad goodX fVal hbbW hgoodXW (by have := hext89.length_le; omega)
      hbaseBad_ev hgoodX_ev
      (fun x z j hjx => by
        rw [hext89.wVal_eq (inpVec n x) (by rw [inpVec_length]; omega)]
        exact hfVal_exact x z j hjx)

  have hext1_10 : Extends gs1 gs10 :=
    hext12.trans (hext23.trans (hext34.trans (hext45.trans (hext56.trans (hext68.trans (hext89.trans hext9_10))))))
  let yRm1 := ys.getD (r - 1) 0
  let yR := ys.getD r 0
  have hyRm1_m : yRm1 ∈ ys := by
    dsimp only [yRm1]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hyR_m : yR ∈ ys := by
    dsimp only [yR]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hyRm1_10 : yRm1 < m + gs10.length := by have := hext1_10.length_le; have := hysW _ hyRm1_m; omega
  have hyR_10 : yR < m + gs10.length := by have := hext1_10.length_le; have := hysW _ hyR_m; omega
  have hgoodX_10 : goodX < m + gs10.length := by have := hext9_10.length_le; dsimp only [m]; omega
  obtain ⟨gs11a, wTRa, hx11a, hgs11a, hn11a, hl11a, hw11a, he11a⟩ := mkAnd_ex hgs10 hyRm1_10 hgoodX_10
  obtain ⟨gs11, tR, hx11b, hgs11, hn11b, hl11b, htRW, he11b⟩ := mkOr_ex hgs11a (by omega : yR < m + gs11a.length) hw11a
  have hext10_11 : Extends gs10 gs11 := hx11a.trans hx11b
  have hext1_11 : Extends gs1 gs11 := hext1_10.trans hext10_11
  have hnc11 : notCnt gs11 = notCnt gs10 := hn11b.trans hn11a
  let Tlist : List ℕ := List.ofFn fun k : Fin (2 ^ b) =>
    if k.val = 0 then wF else if k.val < r then ys.getD (k.val - 1) 0 else tR
  have hTlist_len : Tlist.length = 2 ^ b := by simp [Tlist]
  have hTlist_W : ∀ w ∈ Tlist, w < m + gs11.length := by
    intro w hw
    simp only [Tlist, List.mem_ofFn] at hw
    rcases hw with ⟨k, rfl⟩
    split_ifs with h0 hlt
    · omega
    · have hm : ys.getD (k.val - 1) 0 ∈ ys := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have := hext1_11.length_le; have := hysW _ hm; omega
    · exact htRW
  have hys_val : ∀ (x : Finset (Fin n)) (i : ℕ), i < 2 ^ (b + 1) →
      wVal gs1 (inpVec n x) (ys.getD i 0) = decide (i < x.card) := by
    intro x i hi
    have hs := hsort_ev (inpVec n x) (inpVec_length n x)
    have hget := getElem_isSortedDesc hs.1 (i := i) (by simp [hysl]; omega)
    simp only [List.getElem_map] at hget
    rw [hs.2, hpadIn_cnt x] at hget
    have hgt : ys.getD i 0 = ys[i]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hgt, hget]
  have hTlist_ev : ∀ (x : Finset (Fin n)) (k : ℕ), 1 ≤ k → k < 2 ^ b →
      wVal gs11 (inpVec n x) (Tlist.getD k 0) = decide (k ≤ RVal r f x) := by
    intro x k hk1 hkb
    have hgt : Tlist.getD k 0 = if k < r then ys.getD (k - 1) 0 else tR := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < Tlist.length)]
      simp [Tlist, show k ≠ 0 by omega]
    rw [hgt]
    split_ifs with hkr
    · have hm : ys.getD (k - 1) 0 ∈ ys := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      rw [hext1_11.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hysW _ hm; omega),
        hys_val x (k - 1) (by omega)]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
      by_cases hcx : x.card ≤ r - 2
      · rw [RVal_eq_of_card_le_rm2 hr hn f hcx]; omega
      · have hrx : r - 1 ≤ RVal r f x := by unfold RVal; split_ifs <;> omega
        omega
    · have hkeq : k = r := by dsimp only [r]; omega
      subst hkeq
      rw [he11b (inpVec n x) (inpVec_length n x),
        hx11a.wVal_eq (inpVec n x) (i := yR) (by rw [inpVec_length]; omega),
        he11a (inpVec n x) (inpVec_length n x),
        hext1_10.wVal_eq (inpVec n x) (i := yR) (by rw [inpVec_length]; have := hysW _ hyR_m; omega),
        hext1_10.wVal_eq (inpVec n x) (i := yRm1) (by rw [inpVec_length]; have := hysW _ hyRm1_m; omega),
        hext9_10.wVal_eq (inpVec n x) (i := goodX) (by rw [inpVec_length]; omega),
        hys_val x r (by omega), hys_val x (r - 1) (by omega)]
      by_cases hgt' : r < x.card
      · rw [RVal_eq_r_of_card_gt hr hn f hgt']; simp [hgt']
      · by_cases heq' : x.card = r
        · rw [hgoodX_spec x heq']
          have h1 : decide (r < x.card) = false := by simp [hgt']
          have h2 : decide (r - 1 < x.card) = true := by simp [heq']; omega
          rw [h1, h2, Bool.false_or, Bool.true_and]
          apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
          have hle := RVal_le r f x
          rw [show (r ≤ RVal r f x ↔ RVal r f x = r) by omega, RVal_eq_r_iff hr hn f x]
          simp [heq']
        · have hlt' : x.card ≤ r - 1 := by omega
          have hrx : RVal r f x ≤ r - 1 := by unfold RVal; split_ifs <;> omega
          have h1 : decide (r < x.card) = false := by simp; omega
          have h2 : decide (r - 1 < x.card) = false := by simp; omega
          have h3 : decide (r ≤ RVal r f x) = false := by simp; omega
          rw [h1, h2, h3]; rfl
  obtain ⟨gs12, eqR, hext11_12, hgs12, hnc12, hlen12, heqRl, heqRW, heqR_ev⟩ :=
    exists_b_decoder_aux b wF wT hwF hwT Tlist hTlist_len b le_rfl gs11 hgs11 hTlist_W
  obtain ⟨gs13, leR, hext12_13, hgs13, hnc13, hlen13, hleRl, hleRW, hleR_ev⟩ :=
    exists_prefix_or eqR (r - 2) (by dsimp only [r]; omega) gs12 hgs12 heqRW
  have heqR_spec : ∀ (x : Finset (Fin n)) (u : ℕ), u < 2 ^ b →
      wVal gs12 (inpVec n x) (eqR.getD u 0) = decide (RVal r f x = u) := by
    intro x u hu
    have hRle' : RVal r f x ≤ r := RVal_le r f x
    have hRlt : RVal r f x < 2 ^ b := by dsimp only [r] at hRle' ⊢; omega
    have h := heqR_ev (inpVec n x) (RVal r f x) (inpVec_length n x)
      (inpVec_getD_m n x) (inpVec_getD_m1 n x) hRlt (hTlist_ev x) u hu
    simpa using h
  have hleR_spec : ∀ (x : Finset (Fin n)) (k : ℕ), k ≤ r - 2 →
      wVal gs13 (inpVec n x) (leR.getD k 0) = decide (RVal r f x ≤ k) := by
    intro x k hk
    rw [hleR_ev (inpVec n x) (inpVec_length n x) k hk]
    apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hiv⟩
      rw [heqR_spec x i (by dsimp only [r] at hk; omega), decide_eq_true_eq] at hiv
      omega
    · intro hle
      refine ⟨RVal r f x, hle, ?_⟩
      rw [heqR_spec x (RVal r f x) (by dsimp only [r] at hk; omega)]; simp

  let cOut : List ℕ := List.ofFn fun t : Fin (2 ^ (b + 1)) =>
    if t.val < r - 2 then leR.getD t.val 0 else wT
  have hext1_13 : Extends gs1 gs13 := hext1_11.trans (hext11_12.trans hext12_13)
  obtain ⟨gs14, revOut, hext13_14, hgs14, hnc14, hlen14, hrevl, hrevW, hrev_ev⟩ :=
    hsort_rev gs13 cOut hext1_13 hgs13 (by simp [cOut])
      (fun w hw => by
        simp only [cOut, List.mem_ofFn] at hw
        rcases hw with ⟨t, rfl⟩
        split_ifs with hlt
        · have hm : leR.getD t.val 0 ∈ leR := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
          exact hleRW _ hm
        · omega)
  have hrev_spec : ∀ (x : Finset (Fin n)), RVal r f x ≤ r - 2 →
      ∀ j : Fin n, wVal gs14 (inpVec n x) (revOut.getD j.val 0) = decide (j ∉ x) := by
    intro x hrx j
    have hcx : x.card ≤ r - 2 := (RVal_le_rm2_iff hr hn f x).1 hrx
    have hrx_eq : RVal r f x = x.card := RVal_eq_of_card_le_rm2 hr hn f hcx
    have hcEq : cOut.map (wVal gs13 (inpVec n x)) = (ys.map (wVal gs1 (inpVec n x))).map (!·) := by
      apply List.ext_getElem
      · simp [cOut, hysl]
      · intro t ht1 ht2
        have htl : t < 2 ^ (b + 1) := by simp [cOut] at ht1; exact ht1
        simp only [cOut, List.getElem_map, List.getElem_ofFn]
        have hyt : wVal gs1 (inpVec n x) (ys[t]'(by omega)) = decide (t < x.card) := by
          have := hys_val x t htl
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < ys.length)] at this
          simpa using this
        rw [hyt]
        split_ifs with htr
        · rw [hleR_spec x t (by omega), hrx_eq]
          apply Bool.eq_iff_iff.2; simp
        · rw [evalWires_input gs13 (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m1 n x]
          symm; simp; omega
    have hrEq := hrev_ev (inpVec n x) (inpVec_length n x) hcEq
    have hget := congrArg (fun L => L.getD j.val false) hrEq
    have hjN : j.val < 2 ^ (b + 1) := by omega
    have hL : (revOut.map (wVal gs14 (inpVec n x))).getD j.val false =
        wVal gs14 (inpVec n x) (revOut.getD j.val 0) := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hrevl]; omega),
          List.getElem?_eq_getElem (by omega : j.val < revOut.length)]
      simp
    have hR : ((padIn.map (wVal [] (inpVec n x))).map (!·)).getD j.val false = decide (j ∉ x) := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hpadIn_len]; omega)]
      simp only [Option.getD_some, List.getElem_map]
      have hpj : padIn[j.val]'(by omega) = j.val := by
        simp only [padIn]
        rw [List.getElem_append_left (by simp)]
        simp
      rw [hpj, evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_lt n x j]
      by_cases hm : j ∈ x <;> simp [hm]
    rw [← hL, hget, hR]

  have hext2_14 : Extends gs2 gs14 :=
    hext23.trans (hext34.trans (hext45.trans (hext56.trans (hext68.trans (hext89.trans
      (hext9_10.trans (hext10_11.trans (hext11_12.trans (hext12_13.trans hext13_14)))))))))
  have hext3_14 : Extends gs3 gs14 :=
    hext34.trans (hext45.trans (hext56.trans (hext68.trans (hext89.trans
      (hext9_10.trans (hext10_11.trans (hext11_12.trans (hext12_13.trans hext13_14))))))))
  have hext10_14 : Extends gs10 gs14 := hext10_11.trans (hext11_12.trans (hext12_13.trans hext13_14))
  have hext12_14 : Extends gs12 gs14 := hext12_13.trans hext13_14
  let wLeRm2 := leR.getD (r - 2) 0
  let wEqRm1 := eqR.getD (r - 1) 0
  have hwLeRm2_m : wLeRm2 ∈ leR := by
    dsimp only [wLeRm2]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hwEqRm1_m : wEqRm1 ∈ eqR := by
    dsimp only [wEqRm1]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by dsimp only [r]; omega)]; exact List.getElem_mem _
  have hwinRm1_all : ∀ (x : Finset (Fin n)) (j : ℕ) (hj : j < n),
      wVal gs2 (inpVec n x) (winRm1.getD j 0) = decide (r ≤ (insert (⟨j, hj⟩ : Fin n) x).card) := by
    intro x j hj
    have hpad_j : wVal [] (inpVec n x) (padIn.getD j 0) = decide ((⟨j, hj⟩ : Fin n) ∈ x) := by
      have hgt : padIn.getD j 0 = j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < padIn.length)]
        simp only [padIn, Option.getD_some]
        rw [List.getElem_append_left (by simp [hj])]; simp
      rw [hgt, evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega)]
      exact inpVec_getD_lt n x ⟨j, hj⟩
    have hsub_card : x.card - (if decide ((⟨j, hj⟩ : Fin n) ∈ x) = true then 1 else 0) =
        (x.erase ⟨j, hj⟩).card := by
      by_cases hm : (⟨j, hj⟩ : Fin n) ∈ x
      · simp only [hm, decide_true, ↓reduceIte]; exact (Finset.card_erase_of_mem hm).symm
      · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
        exact (congrArg Finset.card (Finset.erase_eq_of_notMem hm)).symm
    have h := hwinRm1_ev (inpVec n x) 0 (inpVec_length n x) (inpVec_getD_m n x)
      (fun t ht => by
        have hgt : rootRm1.getD t 0 = if r - 1 + 1 + t ≤ 2 ^ (b + 1) then wT else wF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [rootRm1]; exact ht)]
          simp [rootRm1]
        rw [hgt]
        split_ifs with hle
        · rw [evalWires_input gs1 (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m1 n x]
          symm; simp; omega
        · rw [evalWires_input gs1 (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m n x]
          symm; simp; omega)
      j (by omega)
    rw [h, hpadIn_cnt x, hpad_j, hsub_card, card_insert_eq_card_erase_add_one]
    exact winRm1_decide_eq r _ (by omega)
  have hwinR_all : ∀ (x : Finset (Fin n)) (j : ℕ) (hj : j < n),
      wVal gs3 (inpVec n x) (winR.getD j 0) = decide (r + 1 ≤ (insert (⟨j, hj⟩ : Fin n) x).card) := by
    intro x j hj
    have hpad_j : wVal [] (inpVec n x) (padIn.getD j 0) = decide ((⟨j, hj⟩ : Fin n) ∈ x) := by
      have hgt : padIn.getD j 0 = j := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < padIn.length)]
        simp only [padIn, Option.getD_some]
        rw [List.getElem_append_left (by simp [hj])]; simp
      rw [hgt, evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega)]
      exact inpVec_getD_lt n x ⟨j, hj⟩
    have hsub_card : x.card - (if decide ((⟨j, hj⟩ : Fin n) ∈ x) = true then 1 else 0) =
        (x.erase ⟨j, hj⟩).card := by
      by_cases hm : (⟨j, hj⟩ : Fin n) ∈ x
      · simp only [hm, decide_true, ↓reduceIte]; exact (Finset.card_erase_of_mem hm).symm
      · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
        exact (congrArg Finset.card (Finset.erase_eq_of_notMem hm)).symm
    have h := hwinR_ev (inpVec n x) 0 (inpVec_length n x) (inpVec_getD_m n x)
      (fun t ht => by
        have hgt : rootR.getD t 0 = if r + 1 + t ≤ 2 ^ (b + 1) then wT else wF := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [rootR]; exact ht)]
          simp [rootR]
        rw [hgt]
        split_ifs with hle
        · rw [evalWires_input gs2 (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m1 n x]
          symm; simp; omega
        · rw [evalWires_input gs2 (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m n x]
          symm; simp; omega)
      j (by omega)
    rw [h, hpadIn_cnt x, hpad_j, hsub_card, card_insert_eq_card_erase_add_one]
    exact winR_decide_eq r _
  obtain ⟨gs15, taps, hext14_15, hgs15, hnc15, hlen15, htapsL, htapsW, htaps_ev⟩ :=
    exists_taps hr hn f gs14 hgs14 winRm1 winR goodPlus revOut
      (by omega) (by omega) hgpL (by omega)
      (fun w hw => by have := hext2_14.length_le; have := hwinRm1W w hw; dsimp only [m] at this; omega)
      (fun w hw => by have := hext3_14.length_le; have := hwinRW w hw; dsimp only [m] at this; omega)
      (fun w hw => by have := hext10_14.length_le; have := hgpW w hw; omega)
      (fun w hw => by have := hrevW w hw; dsimp only [m] at this; omega)
      wLeRm2 wEqRm1
      (by have := hext13_14.length_le; have := hleRW _ hwLeRm2_m; dsimp only [m] at this; omega)
      (by have := hext12_14.length_le; have := heqRW _ hwEqRm1_m; dsimp only [m] at this; omega)
      (fun x => by
        rw [hext13_14.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hleRW _ hwLeRm2_m; omega)]
        exact hleR_spec x (r - 2) le_rfl)
      (fun x => by
        rw [hext12_14.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := heqRW _ hwEqRm1_m; omega)]
        exact heqR_spec x (r - 1) (by dsimp only [r]; omega))
      hrev_spec
      (fun x j hj => by
        have hm : winRm1.getD j 0 ∈ winRm1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext2_14.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hwinRm1W _ hm; omega)]
        exact hwinRm1_all x j hj)
      (fun x j hj => by
        have hm : winR.getD j 0 ∈ winR := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext3_14.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hwinRW _ hm; omega)]
        exact hwinR_all x j hj)
      (fun j hj x hcard => by
        have hm : goodPlus.getD j 0 ∈ goodPlus := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext10_14.wVal_eq (inpVec n x) (by rw [inpVec_length]; have := hgpW _ hm; omega)]
        exact hgp_ev j hj x hcard)
  have hnc_tot : notCnt gs15 = b := by
    have hnc0 : notCnt ([] : List Gate) = 0 := rfl
    rw [hnc15, hnc14, hnc13, hnc12, hnc11, hnc10, hnc9, hnc8, hnc6, hnc5, hnc4, hnc3, hnc2, hnc1, hnc0]
    omega
  have hlen_tot : gs15.length ≤ 2 * D.gates.length + 128 * (n + 2) * (Nat.log2 (n + 2) + 2) ^ 2 := by
    rw [hlog]
    have hpowN : 2 ^ (b + 1) = n + 2 := hNpow.symm
    rw [hpowN] at hlen1 hlen2 hlen3 hlen14
    rw [hdp_len] at hlen4 hlen5
    exact part1_len_bound hr hn (by omega) hlen1 hlen2 hlen3 hlen4 hlen5 hlen6 hlen8 hlen9 hlen10
      (by omega) hlen12 hlen13 hlen14 hlen15
  exact ⟨gs15, taps, hgs15, hnc_tot, hlen_tot, htapsL, htapsW, htaps_ev⟩

def notInBit (w : List Bool) (g : Gate) : ℕ :=
  if (g.inputs.map fun i => w.getD i false).headD false then 1 else 0

def notCodeFrom (w : List Bool) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let w' := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      if isNotOp g.op then
        notInBit w g * 2 ^ notCnt gs + notCodeFrom w' gs
      else
        notCodeFrom w' gs

lemma notCnt_cons (g : Gate) (gs : List Gate) :
    notCnt (g :: gs) = (if isNotOp g.op then 1 else 0) + notCnt gs := by
  unfold notCnt
  rw [List.filter_cons]
  cases isNotOp g.op <;> simp [Nat.add_comm]

lemma notCodeFrom_lt (gs : List Gate) (w : List Bool) :
    notCodeFrom w gs < 2 ^ notCnt gs := by
  induction gs generalizing w with
  | nil => simp [notCodeFrom, notCnt]
  | cons g gs ih =>
    simp only [notCodeFrom, notCnt_cons]
    split_ifs with hnot
    · have hih := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      have hbit : notInBit w g ≤ 1 := by unfold notInBit; split_ifs <;> omega
      have hpow : 2 ^ (1 + notCnt gs) = 2 ^ notCnt gs + 2 ^ notCnt gs := by
        rw [pow_add, pow_one]; ring
      rw [hpow]
      nlinarith
    · simp only [zero_add]
      exact ih _

lemma notCodeFrom_mono_and_fall (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
      notCodeFrom w1 gs ≤ notCodeFrom w2 gs ∧
      ((∃ i : ℕ, (evalWires gs w1).getD i false = true ∧ (evalWires gs w2).getD i false = false) →
       notCodeFrom w1 gs < notCodeFrom w2 gs) := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle
    refine ⟨le_rfl, ?_⟩
    rintro ⟨i, h1, h2⟩
    simp only [evalWires, List.foldl_nil] at h1 h2
    have := hle i h1
    rw [h2] at this; cases this
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hop g (by simp)
    have hrest : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not :=
      fun g' hg' => hop g' (by simp [hg'])
    let v1 := g.op.eval (g.inputs.map fun i => w1.getD i false)
    let v2 := g.op.eval (g.inputs.map fun i => w2.getD i false)
    let w1' := w1 ++ [v1]
    let w2' := w2 ++ [v2]
    have hstep_le : (v1 = true → v2 = true) →
        ∀ i : ℕ, w1'.getD i false = true → w2'.getD i false = true := by
      intro hv i hi
      by_cases hilt : i < w1.length
      · have h1 : w1'.getD i false = w1.getD i false := by
          simp only [w1', List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
        have h2 : w2'.getD i false = w2.getD i false := by
          simp only [w2', List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w2.length)]
        rw [h1] at hi; rw [h2]; exact hle i hi
      · by_cases hieq : i = w1.length
        · subst hieq
          have h1 : w1'.getD w1.length false = v1 := by simp [w1', List.getD_eq_getElem?_getD]
          have h2 : w2'.getD w1.length false = v2 := by simp [w2', hlen, List.getD_eq_getElem?_getD]
          rw [h1] at hi; rw [h2]; exact hv hi
        · have h1 : w1'.getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [w1']; omega)]; rfl
          rw [h1] at hi; cases hi
    rcases hg with hAnd | hOr | hNot
    · have hnotF : isNotOp g.op = false := by rw [hAnd]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hAnd]; simp only [GateOp.eval, List.all_eq_true, id_eq]
        intro hall b hb
        rcases List.mem_map.1 hb with ⟨i, hi, rfl⟩
        exact hle i (hall (w1.getD i false) (List.mem_map_of_mem hi))
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotF : isNotOp g.op = false := by rw [hOr]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hOr]; simp only [GateOp.eval, List.any_eq_true, id_eq]
        rintro ⟨b, hb, rfl⟩
        rcases List.mem_map.1 hb with ⟨i, hi, hwi⟩
        exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle i hwi⟩
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotT : isNotOp g.op = true := by rw [hNot]; rfl
      let b1 := (g.inputs.map fun i => w1.getD i false).headD false
      let b2 := (g.inputs.map fun i => w2.getD i false).headD false
      have hb_le : b1 = true → b2 = true := by
        dsimp only [b1, b2]
        cases hgin : g.inputs with
        | nil => intro h; simp at h
        | cons a _ => simp only [List.map_cons, List.headD_cons]; exact hle a
      have hv1 : v1 = !b1 := by dsimp only [v1, b1]; rw [hNot]; rfl
      have hv2 : v2 = !b2 := by dsimp only [v2, b2]; rw [hNot]; rfl
      by_cases hbeq : b1 = b2
      · have hbit : notInBit w1 g = notInBit w2 g := by
          unfold notInBit; change (if b1 then 1 else 0) = (if b2 then 1 else 0); rw [hbeq]
        have hv : v1 = true → v2 = true := by rw [hv1, hv2, hbeq]; exact id
        have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
        simp only [notCodeFrom, hnotT, ↓reduceIte, evalWires, List.foldl_cons] at hih ⊢
        rw [hbit]
        exact ⟨Nat.add_le_add_left hih.1 _, fun hex => Nat.add_lt_add_left (hih.2 hex) _⟩
      · have hb1F : b1 = false := by
          cases hb1 : b1 with
          | false => rfl
          | true => exact absurd (hb_le hb1).symm (by rw [hb1] at hbeq; exact hbeq)
        have hb2T : b2 = true := by
          cases hb2 : b2 with
          | true => rfl
          | false => exact absurd (hb1F.trans hb2.symm) hbeq
        have hbit1 : notInBit w1 g = 0 := by unfold notInBit; change (if b1 then 1 else 0) = 0; rw [hb1F]; rfl
        have hbit2 : notInBit w2 g = 1 := by unfold notInBit; change (if b2 then 1 else 0) = 1; rw [hb2T]; rfl
        have hlt1 := notCodeFrom_lt gs w1'
        have hstrict : notCodeFrom w1 (g :: gs) < notCodeFrom w2 (g :: gs) := by
          simp only [notCodeFrom, hnotT, ↓reduceIte, hbit1, hbit2, zero_mul, zero_add, one_mul]
          dsimp only [w1', v1] at hlt1
          omega
        exact ⟨le_of_lt hstrict, fun _ => hstrict⟩

lemma inpVec_le_of_subset {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) :
    (inpVec n u).length = (inpVec n v).length ∧
    ∀ i : ℕ, (inpVec n u).getD i false = true → (inpVec n v).getD i false = true := by
  refine ⟨by rw [inpVec_length, inpVec_length], ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [inpVec_getD_lt n u ⟨i, hin⟩, decide_eq_true_eq] at hi
    rw [inpVec_getD_lt n v ⟨i, hin⟩, decide_eq_true_eq]
    exact huv hi
  · by_cases him : i = n
    · rw [him, inpVec_getD_m n u] at hi; cases hi
    · by_cases him1 : i = n + 1
      · rw [him1]; exact inpVec_getD_m1 n v
      · have hnone : (inpVec n u).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [inpVec_length]; omega)]; rfl
        rw [hnone] at hi; cases hi

lemma markov_chain_bound {n : ℕ} (gs : List Gate) (hgs : GateOK (n + 2) gs)
    (M : ℕ) (S : ℕ → Finset (Fin n))
    (hsub : ∀ t < M, S t ⊆ S (t + 1))
    (hfall : ∀ t < M, ∃ w : ℕ, wVal gs (inpVec n (S t)) w = true ∧ wVal gs (inpVec n (S (t + 1))) w = false) :
    M < 2 ^ notCnt gs := by
  have hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hgs.1 g hg).1
  have hle : ∀ k ≤ M, k ≤ notCodeFrom (inpVec n (S k)) gs := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hih := ih (by omega)
      have hvec := inpVec_le_of_subset (hsub k (by omega))
      have hlt := (notCodeFrom_mono_and_fall gs hop _ _ hvec.1 hvec.2).2 (hfall k (by omega))
      omega
  have hM := hle M le_rfl
  have hlt := notCodeFrom_lt gs (inpVec n (S M))
  omega

lemma exists_subset_chain {α : Type*} [DecidableEq α] (B : Finset α) :
    ∃ (A : ℕ → Finset α),
      A 0 = ∅ ∧ A B.card = B ∧
      ∀ t < B.card, ∃ a : α, A (t + 1) = insert a (A t) ∧ a ∉ A t ∧ (A t).card = t := by
  induction B using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => ∅, rfl, rfl, fun t ht => by simp at ht⟩
  | insert x s hx ih =>
    rcases ih with ⟨A, h0, hcard, hstep⟩
    let A' : ℕ → Finset α := fun t => if t ≤ s.card then A t else insert x s
    refine ⟨A', by simp [A', h0], by simp [A', Finset.card_insert_of_notMem hx], ?_⟩
    intro t ht
    rw [Finset.card_insert_of_notMem hx] at ht
    by_cases hts : t < s.card
    · rcases hstep t hts with ⟨a, ha1, ha2, ha3⟩
      refine ⟨a, ?_, ?_, ?_⟩
      · simp only [A', show t + 1 ≤ s.card by omega, show t ≤ s.card by omega, ↓reduceIte]; exact ha1
      · simp only [A', show t ≤ s.card by omega, ↓reduceIte]; exact ha2
      · simp only [A', show t ≤ s.card by omega, ↓reduceIte]; exact ha3
    · have hteq : t = s.card := by omega
      subst hteq
      refine ⟨x, ?_, ?_, ?_⟩
      · simp [A', hcard]
      · simp [A', hcard, hx]
      · simp [A', hcard]

def remapIdx (mC : ℕ) (phi : ℕ → ℕ) (base : ℕ) (i : ℕ) : ℕ :=
  if i < mC then phi i else base + (i - mC)

def remapGates (mC : ℕ) (phi : ℕ → ℕ) (base : ℕ) (cg : List Gate) : List Gate :=
  cg.map fun g => ⟨g.op, g.inputs.map (remapIdx mC phi base)⟩

lemma GateOK_remap {mD mC : ℕ} {pre cg : List Gate} (hpre : GateOK mD pre) (hcg : GateOK mC cg)
    (phi : ℕ → ℕ) (hphi : ∀ i < mC, phi i < mD + pre.length) :
    GateOK mD (pre ++ remapGates mC phi (mD + pre.length) cg) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, remapGates, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hpre.1 g hg
    · have h := hcg.1 g0 hg0
      exact ⟨h.1, by simp [h.2]⟩
  · intro j hj i hi
    simp only [List.length_append, remapGates, List.length_map] at hj
    by_cases hjp : j < pre.length
    · have hget : (pre ++ remapGates mC phi (mD + pre.length) cg).getD j ⟨GateOp.or, []⟩ =
          pre.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [hget] at hi
      exact hpre.2 j hjp i hi
    · have hget : (pre ++ remapGates mC phi (mD + pre.length) cg).getD j ⟨GateOp.or, []⟩ =
          (remapGates mC phi (mD + pre.length) cg).getD (j - pre.length) ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : pre.length ≤ j)]
      rw [hget] at hi
      have hjk : j - pre.length < cg.length := by omega
      have hget2 : (remapGates mC phi (mD + pre.length) cg).getD (j - pre.length) ⟨GateOp.or, []⟩ =
          ⟨(cg.getD (j - pre.length) ⟨GateOp.or, []⟩).op,
           (cg.getD (j - pre.length) ⟨GateOp.or, []⟩).inputs.map (remapIdx mC phi (mD + pre.length))⟩ := by
        simp only [remapGates, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by simp [hjk]), List.getElem?_eq_getElem hjk]
        simp
      rw [hget2] at hi
      rcases List.mem_map.1 hi with ⟨i0, hi0, rfl⟩
      have hi0lt := hcg.2 (j - pre.length) hjk i0 hi0
      unfold remapIdx
      split_ifs with him
      · have := hphi i0 him; omega
      · omega

lemma wVal_remap {mD mC : ℕ} (pre : List Gate) (phi : ℕ → ℕ) (hphi : ∀ i < mC, phi i < mD + pre.length)
    (inpD inpC : List Bool) (hinpD : inpD.length = mD) (hinpC : inpC.length = mC)
    (hmatch : ∀ i < mC, wVal pre inpD (phi i) = inpC.getD i false) :
    ∀ (cg : List Gate), GateOK mC cg →
      ∀ i < mC + cg.length,
        wVal (pre ++ remapGates mC phi (mD + pre.length) cg) inpD (remapIdx mC phi (mD + pre.length) i) =
        wVal cg inpC i := by
  intro cg
  induction cg using List.reverseRecOn with
  | nil =>
    intro _ i hi
    simp only [List.length_nil, add_zero] at hi
    simp only [remapGates, List.map_nil, List.append_nil, remapIdx, hi, ↓reduceIte]
    rw [hmatch i hi, evalWires_input [] inpC (by omega)]
  | append_singleton cg1 g ih =>
    intro hcg i hi
    have hcg1 : GateOK mC cg1 := by
      refine ⟨fun g' hg' => hcg.1 g' (by simp [hg']), fun j hj k hk => ?_⟩
      have h := hcg.2 j (by simp; omega) k
      have hget : (cg1 ++ [g]).getD j ⟨GateOp.or, []⟩ = cg1.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      rw [hget] at h; exact h hk
    have hgin : ∀ k ∈ g.inputs, k < mC + cg1.length := by
      have h := hcg.2 cg1.length (by simp)
      have hget : (cg1 ++ [g]).getD cg1.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at h; exact h
    have hrm_app : pre ++ remapGates mC phi (mD + pre.length) (cg1 ++ [g]) =
        (pre ++ remapGates mC phi (mD + pre.length) cg1) ++
        [⟨g.op, g.inputs.map (remapIdx mC phi (mD + pre.length))⟩] := by
      simp [remapGates, List.append_assoc]
    rw [hrm_app]
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hilt : i < mC + cg1.length
    · have hidx_lt : remapIdx mC phi (mD + pre.length) i <
          inpD.length + (pre ++ remapGates mC phi (mD + pre.length) cg1).length := by
        simp only [List.length_append, remapGates, List.length_map, hinpD]
        unfold remapIdx
        split_ifs with him
        · have := hphi i him; omega
        · omega
      rw [evalWires_prefix_getD _ _ inpD hidx_lt, evalWires_prefix_getD cg1 [g] inpC (by omega)]
      exact ih hcg1 i hilt
    · have hieq : i = mC + cg1.length := by omega
      subst hieq
      have hidx_eq : remapIdx mC phi (mD + pre.length) (mC + cg1.length) =
          inpD.length + (pre ++ remapGates mC phi (mD + pre.length) cg1).length := by
        simp only [remapIdx, show ¬ (mC + cg1.length < mC) by omega, ↓reduceIte,
          List.length_append, remapGates, List.length_map, hinpD]
        omega
      have hrhs : wVal (cg1 ++ [g]) inpC (mC + cg1.length) = g.op.eval (g.inputs.map (wVal cg1 inpC)) := by
        rw [← hinpC]; exact wVal_append_gate cg1 g inpC
      rw [hidx_eq, wVal_append_gate, hrhs]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro k hk
      simp only [Function.comp_apply]
      exact ih hcg1 k (hgin k hk)

lemma exists_D_from_C {q r n : ℕ} (hr : r = q + 2) (hn : n = 2 * q + 4)
    (f : Finset (Fin q) → Bool)
    (C : Circuit) (hCok : GateOK (n + 2) C.gates)
    (tap : Fin n → Fin (n + 2 + C.gates.length))
    (hCgain : ∀ x j, wVal C.gates (inpVec n x) (tap j).val = gainVal r f x j) :
    ∃ D : Circuit,
      GateOK (q + 2) D.gates ∧ D.output < q + 2 + D.gates.length ∧
      (∀ z : Finset (Fin q), (evalWires D.gates (inpVec q z)).getD D.output false = f z) ∧
      D.gates.length ≤ C.gates.length + 6 * (q + 1) := by
  let mD := q + 2
  have hneg_build : ∀ k ≤ q,
      ∃ (gsA : List Gate) (negW : List ℕ),
        GateOK mD gsA ∧ gsA.length = k ∧ negW.length = k ∧
        (∀ w ∈ negW, w < mD + gsA.length) ∧
        ∀ (z : Finset (Fin q)) (t : Fin q), t.val < k →
          wVal gsA (inpVec q z) (negW.getD t.val 0) = decide (t ∉ z) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨[], [], GateOK_nil mD, rfl, rfl, by simp, fun _ _ ht => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨gsA, negW, hgsA, hlenA, hnlA, hnWA, hevA⟩ := ih (by omega)
      obtain ⟨gsB, wk, hextAB, hgsB, _, hlenB, hwB, hevB⟩ := mkNot_ex hgsA (a := k) (by dsimp only [mD]; omega)
      refine ⟨gsB, negW ++ [wk], hgsB, by omega, by simp [hnlA],
        fun w hw => by
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with hw | rfl
          · have := hextAB.length_le; have := hnWA w hw; omega
          · exact hwB,
        ?_⟩
      intro z t htk
      by_cases htlt : t.val < k
      · have hget : (negW ++ [wk]).getD t.val 0 = negW.getD t.val 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : t.val < negW.length)]
        rw [hget]
        have hm : negW.getD t.val 0 ∈ negW := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hextAB.wVal_eq (inpVec q z) (by rw [inpVec_length]; have := hnWA _ hm; omega)]
        exact hevA z t htlt
      · have hteq : t.val = k := by omega
        have hget : (negW ++ [wk]).getD t.val 0 = wk := by
          rw [hteq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : negW.length ≤ k)]
          simp [hnlA]
        rw [hget, hevB (inpVec q z) (inpVec_length q z),
          evalWires_input gsA (inpVec q z) (by rw [inpVec_length]; omega)]
        have hklt : (⟨k, by omega⟩ : Fin q) = t := Fin.ext hteq.symm
        rw [inpVec_getD_lt q z ⟨k, by omega⟩, hklt]
        by_cases htz : t ∈ z <;> simp [htz]
  obtain ⟨gsA, negW, hgsA, hlenA, hnlA, hnWA, hneg_ev⟩ := hneg_build q le_rfl
  have hpar_build : ∀ k ≤ q,
      ∃ (gsB : List Gate) (pW : ℕ),
        Extends gsA gsB ∧ GateOK mD gsB ∧ gsB.length = gsA.length + 4 * k ∧ pW < mD + gsB.length ∧
        ∀ z : Finset (Fin q),
          wVal gsB (inpVec q z) pW = decide ((z.filter fun t : Fin q => t.val < k).card % 2 = 1) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gsA, q, Extends.refl gsA, hgsA, by simp, by dsimp only [mD]; omega, ?_⟩
      intro z
      rw [evalWires_input gsA (inpVec q z) (by rw [inpVec_length]; omega), inpVec_getD_m q z]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨gsB, pW, hextAB, hgsB, hlenB, hpWB, hevB⟩ := ih (by omega)
      have hkB : k < mD + gsB.length := by dsimp only [mD]; omega
      obtain ⟨g1, u, hx1, hg1, _, hl1, hw1, he1⟩ := mkAnd_ex hgsB hpWB hkB
      obtain ⟨g2, v, hx2, hg2, _, hl2, hw2, he2⟩ := mkOr_ex hg1 (by omega : pW < mD + g1.length) (b := k) (by dsimp only [mD]; omega)
      obtain ⟨g3, nu, hx3, hg3, _, hl3, hw3, he3⟩ := mkNot_ex hg2 (by omega : u < mD + g2.length)
      obtain ⟨g4, pW', hx4, hg4, _, hl4, hw4, he4⟩ := mkAnd_ex hg3 (by omega : v < mD + g3.length) hw3
      refine ⟨g4, pW', hextAB.trans (hx1.trans (hx2.trans (hx3.trans hx4))), hg4, by omega, hw4, ?_⟩
      intro z
      have hinp : (inpVec q z).length = mD := inpVec_length q z
      rw [he4 (inpVec q z) hinp, hx3.wVal_eq (inpVec q z) (i := v) (by rw [inpVec_length]; omega),
        he2 (inpVec q z) hinp, hx1.wVal_eq (inpVec q z) (i := pW) (by rw [inpVec_length]; omega),
        he3 (inpVec q z) hinp, hx2.wVal_eq (inpVec q z) (i := u) (by rw [inpVec_length]; omega),
        he1 (inpVec q z) hinp, hevB z,
        evalWires_input gsB (inpVec q z) (by rw [inpVec_length]; omega),
        evalWires_input g1 (inpVec q z) (by rw [inpVec_length]; omega),
        inpVec_getD_lt q z ⟨k, by omega⟩]
      have hflt : (z.filter fun t : Fin q => t.val < k + 1) =
          if (⟨k, by omega⟩ : Fin q) ∈ z then insert ⟨k, by omega⟩ (z.filter fun t : Fin q => t.val < k)
          else z.filter fun t : Fin q => t.val < k := by
        split_ifs with hkz
        · ext t; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨htz, htk⟩
            by_cases hteq : t.val = k
            · left; exact Fin.ext hteq
            · right; exact ⟨htz, by omega⟩
          · rintro (rfl | ⟨htz, htk⟩)
            · exact ⟨hkz, by dsimp only; omega⟩
            · exact ⟨htz, by omega⟩
        · ext t; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨htz, htk⟩
            refine ⟨htz, ?_⟩
            by_contra hge
            have htv : t.val = k := by omega
            have hteq : t = ⟨k, by omega⟩ := Fin.ext htv
            rw [hteq] at htz; exact hkz htz
          · rintro ⟨htz, htk⟩; exact ⟨htz, by omega⟩
      rw [hflt]
      have hmod : (z.filter fun t : Fin q => t.val < k).card % 2 = 0 ∨
          (z.filter fun t : Fin q => t.val < k).card % 2 = 1 := by omega
      by_cases hkz : (⟨k, by omega⟩ : Fin q) ∈ z
      · have hnm : (⟨k, by omega⟩ : Fin q) ∉ z.filter (fun t : Fin q => t.val < k) := by simp
        simp only [hkz, decide_true, ↓reduceIte, Finset.card_insert_of_notMem hnm]
        rcases hmod with hm | hm
        · have h1 : ((z.filter fun t : Fin q => t.val < k).card + 1) % 2 = 1 := by omega
          rw [h1, hm]; rfl
        · have h0 : ((z.filter fun t : Fin q => t.val < k).card + 1) % 2 = 0 := by omega
          rw [h0, hm]; rfl
      · simp only [hkz, decide_false, ↓reduceIte]
        rcases hmod with hm | hm
        · rw [hm]; rfl
        · rw [hm]; rfl
  obtain ⟨gsB, parOdd, hextAB, hgsB, hlenB, hparOddW, hparOdd_ev⟩ := hpar_build q le_rfl
  obtain ⟨pre, parEven, hextBpre, hpreOK, _, hpreLen, hparEvenW, hparEven_ev⟩ := mkNot_ex hgsB hparOddW
  have hextApre : Extends gsA pre := hextAB.trans hextBpre
  have hpre_len_eq : pre.length = 5 * q + 1 := by omega
  let phi : ℕ → ℕ := fun i =>
    if i < 2 * q then
      if i % 2 = 0 then negW.getD (i / 2) 0 else i / 2
    else if i = 2 * q then parEven
    else if i = 2 * q + 1 then parOdd
    else if i = n + 1 then q + 1
    else q
  have hphiW : ∀ i < n + 2, phi i < mD + pre.length := by
    intro i hi
    dsimp only [phi]
    split_ifs with h1 h2 h3 h4 h5
    · have hm : negW.getD (i / 2) 0 ∈ negW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have := hextApre.length_le; have := hnWA _ hm; omega
    · dsimp only [mD]; omega
    · exact hparEvenW
    · have := hextBpre.length_le; omega
    · dsimp only [mD]; omega
    · dsimp only [mD]; omega
  let xOf : Finset (Fin q) → Finset (Fin n) := fun z => (codeSet z).erase ⟨2 * q + 2, by omega⟩
  have hmatch : ∀ (z : Finset (Fin q)) (i : ℕ), i < n + 2 →
      wVal pre (inpVec q z) (phi i) = (inpVec n (xOf z)).getD i false := by
    intro z i hi
    have hparOdd_z : wVal gsB (inpVec q z) parOdd = decide (z.card % 2 = 1) := by
      have h := hparOdd_ev z
      have hflt : (z.filter fun t : Fin q => t.val < q) = z := by
        ext t; simp
      rw [hflt] at h; exact h
    dsimp only [phi]
    split_ifs with h1 h2 h3 h4 h5
    · have hm : negW.getD (i / 2) 0 ∈ negW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      rw [hextApre.wVal_eq (inpVec q z) (by rw [inpVec_length]; have := hnWA _ hm; omega),
        hneg_ev z ⟨i / 2, by omega⟩ (by dsimp only; omega),
        inpVec_getD_lt n (xOf z) ⟨i, by omega⟩]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq, xOf, Finset.mem_erase]
      have hne : (⟨i, by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ := fun h => by
        have := congrArg Fin.val h; dsimp only at this; omega
      have hev : (⟨i, by omega⟩ : Fin n) = ⟨2 * (i / 2), by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hev, mem_codeSet_data_even hn z ⟨i / 2, by omega⟩]
      simp [show (⟨2 * (i / 2), by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ by rw [← hev]; exact hne]
    · rw [evalWires_input pre (inpVec q z) (by rw [inpVec_length]; omega),
        inpVec_getD_lt q z ⟨i / 2, by omega⟩, inpVec_getD_lt n (xOf z) ⟨i, by omega⟩]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq, xOf, Finset.mem_erase]
      have hne : (⟨i, by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ := fun h => by
        have := congrArg Fin.val h; dsimp only at this; omega
      have hodd : (⟨i, by omega⟩ : Fin n) = ⟨2 * (i / 2) + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hodd, mem_codeSet_data_odd hn z ⟨i / 2, by omega⟩]
      simp [show (⟨2 * (i / 2) + 1, by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ by rw [← hodd]; exact hne]
    · subst h3
      rw [hparEven_ev (inpVec q z) (inpVec_length q z), hparOdd_z,
        inpVec_getD_lt n (xOf z) ⟨2 * q, by omega⟩]
      apply Bool.eq_iff_iff.2; simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, xOf, Finset.mem_erase]
      rw [mem_codeSet_par_even hn z]
      have hne : (⟨2 * q, by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ := fun h => by
        have := congrArg Fin.val h; dsimp only at this; omega
      simp [hne]
    · subst h4
      rw [hextBpre.wVal_eq (inpVec q z) (by rw [inpVec_length]; omega), hparOdd_z,
        inpVec_getD_lt n (xOf z) ⟨2 * q + 1, by omega⟩]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq, xOf, Finset.mem_erase]
      rw [mem_codeSet_par_odd hn z]
      have hne : (⟨2 * q + 1, by omega⟩ : Fin n) ≠ ⟨2 * q + 2, by omega⟩ := fun h => by
        have := congrArg Fin.val h; dsimp only at this; omega
      simp [hne]
    · subst h5
      rw [evalWires_input pre (inpVec q z) (by rw [inpVec_length]; omega),
        inpVec_getD_m1 q z, inpVec_getD_m1 n (xOf z)]
    · rw [evalWires_input pre (inpVec q z) (by rw [inpVec_length]; omega), inpVec_getD_m q z]
      by_cases hin : i < n
      · rw [inpVec_getD_lt n (xOf z) ⟨i, hin⟩]
        symm; simp only [decide_eq_false_iff_not, xOf, Finset.mem_erase, not_and]
        by_cases h2 : i = 2 * q + 2
        · intro hne; exact absurd (Fin.ext h2) hne
        · have h3' : i = 2 * q + 3 := by omega
          intro _ hm; exact not_mem_codeSet_last hn z (mem_of_fin_val_eq h3' hm)
      · have heqn : i = n := by omega
        rw [heqn, inpVec_getD_m n (xOf z)]
  let Dgates := pre ++ remapGates (n + 2) phi (mD + pre.length) C.gates
  let probe : Fin n := ⟨2 * q + 2, by omega⟩
  let Dout := remapIdx (n + 2) phi (mD + pre.length) (tap probe).val
  have hDok : GateOK (q + 2) Dgates := GateOK_remap hpreOK hCok phi hphiW
  have hDlen : Dgates.length = pre.length + C.gates.length := by simp [Dgates, remapGates]
  have hDout_lt : Dout < q + 2 + Dgates.length := by
    rw [hDlen]; dsimp only [Dout, remapIdx]
    split_ifs with hlt
    · have := hphiW _ hlt; dsimp only [mD] at this; omega
    · have := (tap probe).isLt; dsimp only [mD]; omega
  refine ⟨⟨Dgates, Dout⟩, hDok, hDout_lt, ?_, by change Dgates.length ≤ _; omega⟩
  intro z
  change wVal Dgates (inpVec q z) Dout = f z
  rw [wVal_remap pre phi hphiW (inpVec q z) (inpVec n (xOf z)) (inpVec_length q z) (inpVec_length n (xOf z))
    (hmatch z) C.gates hCok (tap probe).val (tap probe).isLt]
  rw [hCgain (xOf z) probe]
  unfold gainVal
  have hprobe_mem : probe ∈ codeSet z := mem_codeSet_probe hn z
  have hins_eq : insert probe (xOf z) = codeSet z := Finset.insert_erase hprobe_mem
  have hxcard : (xOf z).card = r - 1 := by
    rw [Finset.card_erase_of_mem hprobe_mem, card_codeSet hn z]; omega
  rw [hins_eq, RVal_eq_rm1_of_card_rm1 hr f hxcard]
  unfold RVal
  cases hfz : f z with
  | false =>
    have hex : ∃ z' : Finset (Fin q), f z' = false ∧ codeSet (n := n) z = codeSet z' := ⟨z, hfz, rfl⟩
    simp only [hex, ↓reduceIte, lt_irrefl, decide_false]
  | true =>
    have hnex : ¬ ∃ z' : Finset (Fin q), f z' = false ∧ codeSet (n := n) z = codeSet z' := by
      rintro ⟨z', hfz', hz'⟩
      have heqz := codeSet_injective hn hz'
      rw [← heqz, hfz] at hfz'; cases hfz'
    simp only [hnex, ↓reduceIte, card_codeSet hn z]
    rw [decide_eq_true_eq]; omega

lemma L_lib_1275_part2 (b : ℕ) (hb : 2 ≤ b)
    (f : Finset (Fin (2 ^ b - 1 - 2)) → Bool)
    (C : Circuit) (g : Finset (Fin (2 * (2 ^ b - 1))) → Fin (2 * (2 ^ b - 1)) → Bool)
    (hCok : GateOK (2 * (2 ^ b - 1) + 2) C.gates)
    (tap : Fin (2 * (2 ^ b - 1)) → Fin (2 * (2 ^ b - 1) + 2 + C.gates.length))
    (hCcomp : ∀ x j, wVal C.gates (inpVec (2 * (2 ^ b - 1)) x) (tap j).val = g x j)
    (hfits1 : ∀ x j, gainVal (2 ^ b - 1) f x j = true → g x j = true)
    (hfits2 : ∀ x j, j ∈ x → g x j = false)
    (hnot_le : notCnt C.gates ≤ b) :
    let r := 2 ^ b - 1
    let q := r - 2
    notCnt C.gates = b ∧ g = gainVal r f ∧
    ∃ D : Circuit,
      GateOK (q + 2) D.gates ∧ D.output < q + 2 + D.gates.length ∧
      (∀ z : Finset (Fin q), (evalWires D.gates (inpVec q z)).getD D.output false = f z) ∧
      D.gates.length ≤ C.gates.length + 6 * (q + 1) := by
  intro r q
  let n := 2 * r
  have h2b4 : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb
  have hr : r = q + 2 := by dsimp only [r, q]; omega
  have hn : n = 2 * q + 4 := by dsimp only [n, r, q]; omega

  have hnot_eq : notCnt C.gates = b := by
    let e : ℕ → Fin n := fun t =>
      if ht : t = 0 then ⟨2 * q + 3, by omega⟩
      else if ht2 : t < r then ⟨t - 1, by omega⟩
      else ⟨0, by omega⟩
    let S : ℕ → Finset (Fin n) := fun t =>
      Nat.rec ∅ (fun k acc => insert (e k) acc) t
    have hS_sub : ∀ t < r, S t ⊆ S (t + 1) := fun t _ => Finset.subset_insert _ _
    have hS_mem : ∀ t (i : Fin n), t ≤ r →
        (i ∈ S t ↔ (0 < t ∧ i.val = 2 * q + 3) ∨ (1 < t ∧ i.val < t - 1)) := by
      intro t
      induction t with
      | zero => intro i _; simp [S]
      | succ k ih =>
        intro i hk
        simp only [S, Finset.mem_insert]
        rw [ih i (by omega)]
        by_cases hk0 : k = 0
        · subst hk0
          have he0 : e 0 = ⟨2 * q + 3, by omega⟩ := by simp [e]
          rw [he0]; constructor
          · rintro (rfl | (⟨h, _⟩ | ⟨h, _⟩)) <;> [exact Or.inl ⟨by omega, rfl⟩; omega; omega]
          · rintro (⟨_, h⟩ | ⟨h, _⟩)
            · left; exact Fin.ext h
            · omega
        · have hek : e k = ⟨k - 1, by omega⟩ := by simp [e, hk0, show k < r by omega]
          rw [hek]; constructor
          · rintro (rfl | (⟨_, h⟩ | ⟨_, h⟩))
            · right; refine ⟨by omega, ?_⟩; dsimp only; omega
            · left; exact ⟨by omega, h⟩
            · right; exact ⟨by omega, by omega⟩
          · rintro (⟨_, h⟩ | ⟨_, h⟩)
            · right; left; exact ⟨by omega, h⟩
            · by_cases hik : i.val = k - 1
              · left; exact Fin.ext hik
              · right; right; exact ⟨by omega, by omega⟩
    have hS_not_mem : ∀ t < r, e t ∉ S t := by
      intro t ht hm
      rw [hS_mem t (e t) (by omega)] at hm
      by_cases ht0 : t = 0
      · subst ht0; rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · have het : (e t).val = t - 1 := by simp [e, ht0, ht]
        rw [het] at hm
        rcases hm with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    have hS_card : ∀ t ≤ r, (S t).card = t := by
      intro t
      induction t with
      | zero => intro _; simp [S]
      | succ k ih =>
        intro hk
        change (insert (e k) (S k)).card = k + 1
        rw [Finset.card_insert_of_notMem (hS_not_mem k (by omega)), ih (by omega)]
    have hS_fall : ∀ t < r, ∃ w : ℕ, wVal C.gates (inpVec n (S t)) w = true ∧
        wVal C.gates (inpVec n (S (t + 1))) w = false := by
      intro t ht
      refine ⟨(tap (e t)).val, ?_, ?_⟩
      · rw [hCcomp]
        apply hfits1
        unfold gainVal; rw [decide_eq_true_eq]
        have hRt : RVal r f (S t) = t := by
          by_cases hle : t ≤ r - 2
          · rw [RVal_eq_of_card_le_rm2 hr hn f (by rw [hS_card t (by omega)]; omega), hS_card t (by omega)]
          · have hteq : t = r - 1 := by omega
            rw [RVal_eq_rm1_of_card_rm1 hr f (by rw [hS_card t (by omega)]; exact hteq), hteq]
        have hRt1 : RVal r f (insert (e t) (S t)) = t + 1 := by
          have hseq : insert (e t) (S t) = S (t + 1) := rfl
          rw [hseq]
          have hlast : (⟨2 * q + 3, by omega⟩ : Fin n) ∈ S (t + 1) := by
            rw [hS_mem (t + 1) _ (by omega)]; left; exact ⟨by omega, rfl⟩
          unfold RVal
          have hnex : ¬ ∃ z : Finset (Fin q), f z = false ∧ S (t + 1) = codeSet z := by
            rintro ⟨z, _, hz⟩; rw [hz] at hlast; exact not_mem_codeSet_last hn z hlast
          have hc1 : (S (t + 1)).card = t + 1 := hS_card (t + 1) (by omega)
          split_ifs with hex
          · exfalso; exact hnex hex
          · rw [hc1]; omega
        rw [hRt, hRt1]; omega
      · rw [hCcomp]
        exact hfits2 (S (t + 1)) (e t) (Finset.mem_insert_self _ _)
    have hlt := markov_chain_bound C.gates hCok r S hS_sub hS_fall
    have h2le : 2 ^ b ≤ 2 ^ notCnt C.gates := by dsimp only [r] at hlt; omega
    have hble : b ≤ notCnt C.gates := by
      by_contra hlt2
      have : 2 ^ notCnt C.gates < 2 ^ b := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    omega

  have hg_eq : g = gainVal r f := by
    funext x j
    by_contra hne
    have hgainF : gainVal r f x j = false := by
      cases hg1 : gainVal r f x j with
      | false => rfl
      | true => exact absurd (hfits1 x j hg1) (by rw [hg1] at hne; exact hne)
    have hgxT : g x j = true := by
      cases hg2 : g x j with
      | true => rfl
      | false => exact absurd (hg2.trans hgainF.symm) hne
    have hjnx : j ∉ x := fun h => by have := hfits2 x j h; rw [hgxT] at this; cases this
    have hRle := RVal_le r f x
    by_cases hRxr : RVal r f x = r
    · have hexB : ∃ B : Finset (Fin n), B ⊆ x ∧ B.card = r ∧ RVal r f B = r := by
        have hcx_ge : r ≤ x.card := by
          rw [RVal_eq_r_iff hr hn f x] at hRxr
          rcases hRxr with h1 | ⟨h1, _⟩ <;> omega
        by_cases hcx_eq : x.card = r
        · exact ⟨x, Finset.Subset.refl x, hcx_eq, hRxr⟩
        · obtain ⟨T, hTx, hTcard⟩ := Finset.exists_subset_card_eq (by omega : r + 1 ≤ x.card)
          by_contra hnone
          push Not at hnone
          have h1lt : 1 < T.card := by omega
          rcases Finset.one_lt_card.1 h1lt with ⟨u1, hu1, u2, hu2, hu12⟩
          have he1 : (T.erase u1).card = r := by rw [Finset.card_erase_of_mem hu1, hTcard]; omega
          have he2 : (T.erase u2).card = r := by rw [Finset.card_erase_of_mem hu2, hTcard]; omega
          have hR1 : RVal r f (T.erase u1) ≠ r :=
            hnone (T.erase u1) ((Finset.erase_subset u1 T).trans hTx) he1
          have hR2 : RVal r f (T.erase u2) ≠ r :=
            hnone (T.erase u2) ((Finset.erase_subset u2 T).trans hTx) he2
          have hz1 : ∃ z1 : Finset (Fin q), T.erase u1 = codeSet z1 := by
            rw [ne_eq, RVal_eq_r_iff hr hn f] at hR1
            push Not at hR1
            rcases hR1.2 he1 with ⟨z1, hz1, _⟩
            exact ⟨z1, hz1⟩
          have hz2 : ∃ z2 : Finset (Fin q), T.erase u2 = codeSet z2 := by
            rw [ne_eq, RVal_eq_r_iff hr hn f] at hR2
            push Not at hR2
            rcases hR2.2 he2 with ⟨z2, hz2, _⟩
            exact ⟨z2, hz2⟩
          rcases hz1 with ⟨z1, hz1⟩; rcases hz2 with ⟨z2, hz2⟩
          have hne_z : z1 ≠ z2 := by
            intro h; subst h
            have hEq : T.erase u1 = T.erase u2 := hz1.trans hz2.symm
            have : u2 ∈ T.erase u1 := Finset.mem_erase.2 ⟨hu12.symm, hu2⟩
            rw [hEq] at this
            exact (Finset.mem_erase.1 this).1 rfl
          have hinter_eq : T.erase u1 ∩ T.erase u2 = (T.erase u1).erase u2 := by
            ext v; simp [Finset.mem_inter, Finset.mem_erase]; tauto
          have hinter_card : (codeSet (n := n) z1 ∩ codeSet (n := n) z2).card = r - 1 := by
            rw [← hz1, ← hz2, hinter_eq, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hu12.symm, hu2⟩), he1]
          have hle_q := codeSet_inter_le hn hne_z
          omega
      rcases hexB with ⟨B, hBx, hBcard, hBR⟩
      rcases exists_subset_chain B with ⟨A, hA0, hAcard, hAstep⟩
      rw [hBcard] at hAcard hAstep
      let S : ℕ → Finset (Fin n) := fun t => if t < r then A t else if t = r then x else insert j x
      have hS_sub : ∀ t < r + 1, S t ⊆ S (t + 1) := by
        intro t ht
        by_cases h1 : t + 1 < r
        · simp only [S, show t < r by omega, h1, ↓reduceIte]
          rcases hAstep t (by omega) with ⟨a, ha1, _, _⟩
          rw [ha1]; exact Finset.subset_insert _ _
        · by_cases h2 : t + 1 = r
          · simp only [S, show t < r by omega, h2, lt_irrefl, ↓reduceIte]
            rcases hAstep t (by omega) with ⟨a, ha1, _, _⟩
            have hsubB : A t ⊆ B := by
              rw [← hAcard, ← h2, ha1]; exact Finset.subset_insert _ _
            exact hsubB.trans hBx
          · have hteq : t = r := by omega
            subst hteq
            simp only [S, lt_irrefl, show ¬ (r + 1 < r) by omega, show r + 1 ≠ r by omega, ↓reduceIte]
            exact Finset.subset_insert j x
      have hS_fall : ∀ t < r + 1, ∃ w : ℕ, wVal C.gates (inpVec n (S t)) w = true ∧
          wVal C.gates (inpVec n (S (t + 1))) w = false := by
        intro t ht
        by_cases htr : t < r
        · rcases hAstep t htr with ⟨a, ha1, _, hac⟩
          refine ⟨(tap a).val, ?_, ?_⟩
          · rw [hCcomp]; apply hfits1
            simp only [S, htr, ↓reduceIte]
            unfold gainVal; rw [decide_eq_true_eq, ← ha1]
            have hRt : RVal r f (A t) = t := by
              by_cases hle : t ≤ r - 2
              · rw [RVal_eq_of_card_le_rm2 hr hn f (by omega), hac]
              · have hteq : t = r - 1 := by omega
                rw [RVal_eq_rm1_of_card_rm1 hr f (by omega), hteq]
            have hRt1 : RVal r f (A (t + 1)) = t + 1 := by
              by_cases hlt1 : t + 1 < r
              · have hc1 : (A (t + 1)).card = t + 1 := by
                  rcases hAstep (t + 1) hlt1 with ⟨_, _, _, hc⟩; exact hc
                by_cases hle1 : t + 1 ≤ r - 2
                · rw [RVal_eq_of_card_le_rm2 hr hn f (by omega), hc1]
                · have hteq : t + 1 = r - 1 := by omega
                  rw [RVal_eq_rm1_of_card_rm1 hr f (by omega), hteq]
              · have hteq : t + 1 = r := by omega
                rw [hteq, hAcard, hBR]
            rw [hRt, hRt1]; omega
          · rw [hCcomp]
            apply hfits2
            have ha_mem : a ∈ A (t + 1) := by rw [ha1]; exact Finset.mem_insert_self _ _
            by_cases hlt1 : t + 1 < r
            · simp only [S, hlt1, ↓reduceIte]; exact ha_mem
            · have hteq : t + 1 = r := by omega
              simp only [S, hteq, lt_irrefl, ↓reduceIte]
              rw [hteq, hAcard] at ha_mem
              exact hBx ha_mem
        · have hteq : t = r := by omega
          subst hteq
          refine ⟨(tap j).val, ?_, ?_⟩
          · rw [hCcomp]; simp only [S, lt_irrefl, ↓reduceIte]; exact hgxT
          · rw [hCcomp]; simp only [S, show ¬ (r + 1 < r) by omega, show r + 1 ≠ r by omega, ↓reduceIte]
            exact hfits2 _ _ (Finset.mem_insert_self j x)
      have hlt := markov_chain_bound C.gates hCok (r + 1) S hS_sub hS_fall
      rw [hnot_eq] at hlt
      dsimp only [r] at hlt; omega
    · have hRx_rm1 : RVal r f x = r - 1 := by
        by_contra hne1
        have hle2 : RVal r f x ≤ r - 2 := by omega
        have hgt := gainVal_of_le_rm2 hr hn f hle2 j
        rw [hgainF] at hgt
        simp [hjnx] at hgt
      have hRins_rm1 : RVal r f (insert j x) = r - 1 := by
        have hmono := RVal_mono hr hn f (Finset.subset_insert j x)
        have hnotlt : ¬ (RVal r f x < RVal r f (insert j x)) := by
          unfold gainVal at hgainF; simpa [decide_eq_false_iff_not] using hgainF
        omega
      have hcx : x.card = r - 1 := by
        by_cases hgt : r ≤ x.card
        · have hcins : r < (insert j x).card := by rw [Finset.card_insert_of_notMem hjnx]; omega
          have := RVal_eq_r_of_card_gt hr hn f hcins
          omega
        · have hlt2 : x.card ≤ r - 1 := by omega
          by_cases hle2 : x.card ≤ r - 2
          · have := RVal_eq_of_card_le_rm2 hr hn f hle2; omega
          · omega
      have hcard_ins : (insert j x).card = r := by rw [Finset.card_insert_of_notMem hjnx, hcx]; omega
      have hex_er : ∃ eR : Fin n, eR ∉ insert j x := by
        by_contra hall
        push Not at hall
        have huniv : insert j x = Finset.univ := Finset.eq_univ_iff_forall.2 hall
        have : (insert j x).card = n := by rw [huniv, Finset.card_univ, Fintype.card_fin]
        dsimp only [n] at this; omega
      rcases hex_er with ⟨eR, heR⟩
      rcases exists_subset_chain x with ⟨A, hA0, hAcard, hAstep⟩
      rw [hcx] at hAcard hAstep
      let S : ℕ → Finset (Fin n) := fun t =>
        if t < r - 1 then A t else if t = r - 1 then x else if t = r then insert j x else insert eR (insert j x)
      have hr1 : r - 1 + 1 = r := by omega
      have hS_sub : ∀ t < r + 1, S t ⊆ S (t + 1) := by
        intro t ht
        by_cases h1 : t + 1 < r - 1
        · simp only [S, show t < r - 1 by omega, h1, ↓reduceIte]
          rcases hAstep t (by omega) with ⟨a, ha1, _, _⟩
          rw [ha1]; exact Finset.subset_insert _ _
        · by_cases h2 : t + 1 = r - 1
          · simp only [S, show t < r - 1 by omega, h2, lt_irrefl, ↓reduceIte]
            rcases hAstep t (by omega) with ⟨a, ha1, _, _⟩
            rw [← hAcard, ← h2, ha1]; exact Finset.subset_insert _ _
          · by_cases h3 : t = r - 1
            · subst h3
              rw [hr1]
              simp only [S, lt_irrefl, show ¬ (r < r - 1) by omega, show r ≠ r - 1 by omega, ↓reduceIte]
              exact Finset.subset_insert j x
            · have hteq : t = r := by omega
              subst hteq
              simp only [S, show ¬ (r < r - 1) by omega, show r ≠ r - 1 by omega,
                show ¬ (r + 1 < r - 1) by omega, show r + 1 ≠ r - 1 by omega, show r + 1 ≠ r by omega, ↓reduceIte]
              exact Finset.subset_insert eR _
      have hS_fall : ∀ t < r + 1, ∃ w : ℕ, wVal C.gates (inpVec n (S t)) w = true ∧
          wVal C.gates (inpVec n (S (t + 1))) w = false := by
        intro t ht
        by_cases h1 : t < r - 1
        · rcases hAstep t h1 with ⟨a, ha1, _, hac⟩
          refine ⟨(tap a).val, ?_, ?_⟩
          · rw [hCcomp]; apply hfits1
            simp only [S, h1, ↓reduceIte]
            unfold gainVal; rw [decide_eq_true_eq, ← ha1]
            have hRt : RVal r f (A t) = t := by
              rw [RVal_eq_of_card_le_rm2 hr hn f (by omega), hac]
            have hRt1 : RVal r f (A (t + 1)) = t + 1 := by
              by_cases hlt1 : t + 1 < r - 1
              · have hc1 : (A (t + 1)).card = t + 1 := by
                  rcases hAstep (t + 1) hlt1 with ⟨_, _, _, hc⟩; exact hc
                rw [RVal_eq_of_card_le_rm2 hr hn f (by omega), hc1]
              · have hteq : t + 1 = r - 1 := by omega
                rw [hteq, hAcard, hRx_rm1]
            rw [hRt, hRt1]; omega
          · rw [hCcomp]; apply hfits2
            have ha_mem : a ∈ A (t + 1) := by rw [ha1]; exact Finset.mem_insert_self _ _
            by_cases hlt1 : t + 1 < r - 1
            · simp only [S, hlt1, ↓reduceIte]; exact ha_mem
            · have hteq : t + 1 = r - 1 := by omega
              simp only [S, hteq, lt_irrefl, ↓reduceIte]
              rw [hteq, hAcard] at ha_mem; exact ha_mem
        · by_cases h2 : t = r - 1
          · subst h2
            refine ⟨(tap j).val, ?_, ?_⟩
            · rw [hCcomp]; simp only [S, lt_irrefl, ↓reduceIte]; exact hgxT
            · rw [hCcomp, hr1]
              simp only [S, show ¬ (r < r - 1) by omega, show r ≠ r - 1 by omega, ↓reduceIte]
              exact hfits2 _ _ (Finset.mem_insert_self j x)
          · have hteq : t = r := by omega
            subst hteq
            refine ⟨(tap eR).val, ?_, ?_⟩
            · rw [hCcomp]; apply hfits1
              simp only [S, show ¬ (r < r - 1) by omega, show r ≠ r - 1 by omega, ↓reduceIte]
              unfold gainVal; rw [decide_eq_true_eq, hRins_rm1]
              have hc2 : r < (insert eR (insert j x)).card := by
                rw [Finset.card_insert_of_notMem heR, hcard_ins]; omega
              rw [RVal_eq_r_of_card_gt hr hn f hc2]; omega
            · rw [hCcomp]
              simp only [S, show ¬ (r + 1 < r - 1) by omega, show r + 1 ≠ r - 1 by omega,
                show r + 1 ≠ r by omega, ↓reduceIte]
              exact hfits2 _ _ (Finset.mem_insert_self eR _)
      have hlt := markov_chain_bound C.gates hCok (r + 1) S hS_sub hS_fall
      rw [hnot_eq] at hlt
      dsimp only [r] at hlt; omega
  exact ⟨hnot_eq, hg_eq, exists_D_from_C hr hn f C hCok tap (fun x j => by rw [hCcomp x j, hg_eq])⟩

lemma notCnt_eq_notCount (C : Circuit) : notCnt C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCnt PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> rfl

lemma L_lib_1275_core :
    ∀ b : Nat, 2 ≤ b →
      let r := 2 ^ b - 1
      let q := r - 2
      let n := 2 * r
      ∀ f : Finset (Fin q) → Bool,
      let valid := fun (m : Nat) (C : Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size
      let realizes := fun (D : Circuit) =>
        valid q D ∧ ∀ z, D.eval (inpVec q z) = f z
      let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
        (∀ x j, gainVal r f x j = true → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
      let computes := fun (C : Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
        valid n C ∧ ∃ tap : Fin n → Fin (n + 2 + C.size), ∀ x j,
          (C.wires (inpVec n x)).getD (tap j).val false = g x j
      (∀ D, realizes D → ∃ C, computes C (gainVal r f) ∧ PEqualNP.NotBracket.notCount C = b ∧
        C.size ≤ 2 * D.size + 128 * (n + 2) * (Nat.log2 (n + 2) + 2) ^ 2) ∧
      ∀ C g, computes C g → fits g → PEqualNP.NotBracket.notCount C ≤ b →
        PEqualNP.NotBracket.notCount C = b ∧ g = gainVal r f ∧
        ∃ D, realizes D ∧ D.size ≤ C.size + 6 * (q + 1) := by
  intro b hb r q n f valid realizes fits computes
  constructor
  · intro D ⟨⟨hDf, hDr, hDout⟩, hDeval⟩
    obtain ⟨gs, taps, hgsOK, hnc, hlen, htapsL, htapsW, htaps_ev⟩ :=
      L_lib_1275_part1 b hb f D ⟨hDf, hDr⟩ hDout hDeval
    let C : Circuit := ⟨gs, n⟩
    refine ⟨C, ⟨⟨hgsOK.1, hgsOK.2, by dsimp only [C, Circuit.size]; omega⟩, ?_⟩, ?_, hlen⟩
    · refine ⟨fun j => ⟨taps.getD j.val 0, ?_⟩, fun x j => htaps_ev x j⟩
      have hm : taps.getD j.val 0 ∈ taps := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact htapsW _ hm
    · rw [← notCnt_eq_notCount C]; exact hnc
  · intro C g ⟨⟨hCf, hCr, _⟩, tap, hCcomp⟩ ⟨hf1, hf2⟩ hnot
    have hnot' : notCnt C.gates ≤ b := by rw [notCnt_eq_notCount C]; exact hnot
    obtain ⟨hnc, hgeq, D, hDok, hDout, hDeval, hDsize⟩ :=
      L_lib_1275_part2 b hb f C g ⟨hCf, hCr⟩ tap hCcomp hf1 hf2 hnot'
    exact ⟨by rw [← notCnt_eq_notCount C]; exact hnc, hgeq,
      D, ⟨⟨hDok.1, hDok.2, hDout⟩, hDeval⟩, hDsize⟩

end PEqualNP.Outside.L_lib_1275_aux

theorem PEqualNP.Outside.L_lib_1275 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ b : Nat, 2 ≤ b →
      let r := 2^b-1
      let q := r-2
      let n := 2*r
      ∀ f : Finset (Fin q) → Bool,
      let code := fun (z : Finset (Fin q)) => (Finset.univ : Finset (Fin n)).filter (fun i =>
        i.val = 2*q+2 ∨
        (i.val/2 < q ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val/2 then 1 else 0)) ∨
        (i.val/2 = q ∧ i.val % 2 = z.card % 2))
      let R := fun (x : Finset (Fin n)) => if ∃ z, f z = false ∧ x = code z then r-1 else min r x.card
      let input := fun (m : Nat) (x : Finset (Fin m)) => List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false,true]
      let valid := fun (m : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+2) C ∧ C.output < m+2+C.size
      let realizes := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
        valid q D ∧ ∀ z, D.eval (input q z) = f z
      let gain := fun (x : Finset (Fin n)) (j : Fin n) => decide (R x < R (insert j x))
      let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
        (∀ x j, gain x j = true → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
      let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
        valid n C ∧ ∃ tap : Fin n → Fin (n+2+C.size), ∀ x j,
          (C.wires (input n x)).getD (tap j).val false = g x j
      (∀ D, realizes D → ∃ C, computes C gain ∧ PEqualNP.NotBracket.notCount C = b ∧
        C.size ≤ 2*D.size + 128*(n+2)*(Nat.log2 (n+2)+2)^2) ∧
      ∀ C g, computes C g → fits g → PEqualNP.NotBracket.notCount C ≤ b →
        PEqualNP.NotBracket.notCount C = b ∧ g = gain ∧
        ∃ D, realizes D ∧ D.size ≤ C.size + 6*(q+1) := by
  dsimp only
  intro b hb f
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  have hcode : (fun (z : Finset (Fin (2 ^ b - 1 - 2))) =>
      (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
        i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
        (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
        (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))) =
      PEqualNP.Outside.L_lib_1275_aux.codeSet := by
    funext z; ext i
    simp only [PEqualNP.Outside.L_lib_1275_aux.codeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : ∃ t ∈ z, t.val = i.val / 2 <;> simp only [h, ↓reduceIte]
  have hR : (fun (x : Finset (Fin (2 * (2 ^ b - 1)))) =>
      if ∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ x =
        (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
          i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
          (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
          (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))
      then 2 ^ b - 1 - 1 else min (2 ^ b - 1) x.card) =
      PEqualNP.Outside.L_lib_1275_aux.RVal (2 ^ b - 1) f := by
    funext x
    unfold PEqualNP.Outside.L_lib_1275_aux.RVal
    have hiff : (∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ x =
        (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
          i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
          (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
          (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))) ↔
        (∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ x = PEqualNP.Outside.L_lib_1275_aux.codeSet z) := by
      simp only [congrFun hcode]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  have hgain_app : ∀ (x : Finset (Fin (2 * (2 ^ b - 1)))) (j : Fin (2 * (2 ^ b - 1))),
      decide ((if ∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ x =
          (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
            i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
            (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
            (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))
        then 2 ^ b - 1 - 1 else min (2 ^ b - 1) x.card) <
        (if ∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ insert j x =
          (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
            i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
            (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
            (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))
        then 2 ^ b - 1 - 1 else min (2 ^ b - 1) (insert j x).card)) =
      PEqualNP.Outside.L_lib_1275_aux.gainVal (2 ^ b - 1) f x j := by
    intro x j
    unfold PEqualNP.Outside.L_lib_1275_aux.gainVal
    rw [congrFun hR x, congrFun hR (insert j x)]
    apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
    have hins : (insert j x : Finset (Fin (2 * (2 ^ b - 1)))) =
        @Insert.insert _ _ (@Finset.instInsert _ (instDecidableEqFin _)) j x := by
      ext u; simp only [Finset.mem_insert]
    rw [hins]
  have hgain_fun : (fun (x : Finset (Fin (2 * (2 ^ b - 1)))) (j : Fin (2 * (2 ^ b - 1))) =>
      decide ((if ∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ x =
          (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
            i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
            (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
            (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))
        then 2 ^ b - 1 - 1 else min (2 ^ b - 1) x.card) <
        (if ∃ z : Finset (Fin (2 ^ b - 1 - 2)), f z = false ∧ insert j x =
          (Finset.univ : Finset (Fin (2 * (2 ^ b - 1)))).filter (fun i =>
            i.val = 2 * (2 ^ b - 1 - 2) + 2 ∨
            (i.val / 2 < 2 ^ b - 1 - 2 ∧ i.val % 2 = (if ∃ t ∈ z, t.val = i.val / 2 then 1 else 0)) ∨
            (i.val / 2 = 2 ^ b - 1 - 2 ∧ i.val % 2 = z.card % 2))
        then 2 ^ b - 1 - 1 else min (2 ^ b - 1) (insert j x).card))) =
      PEqualNP.Outside.L_lib_1275_aux.gainVal (2 ^ b - 1) f := by
    funext x j; exact hgain_app x j
  have hinput : ∀ (m : Nat) (x : Finset (Fin m)),
      (List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false, true]) =
      PEqualNP.Outside.L_lib_1275_aux.inpVec m x := by
    intro m x
    unfold PEqualNP.Outside.L_lib_1275_aux.inpVec
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi1 _
    simp only [List.getElem_ofFn]
    apply Bool.eq_iff_iff.2; simp
  have hcore := PEqualNP.Outside.L_lib_1275_aux.L_lib_1275_core b hb f
  dsimp only at hcore
  simpa only [hgain_app, hgain_fun, hinput] using hcore
