import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50025

open PEqualNP.CircuitLowerBounds

def targets : List Nat := [5, 22, 29]

def gateBudget : Nat := 5
def notBudget : Nat := 2

def W0 : List Nat := [30, 28, 24, 16, 0, 31]

def S0 : Nat := 2 ^ 30 + 2 ^ 28 + 2 ^ 24 + 2 ^ 16 + 2 ^ 0 + 2 ^ 31

def need (S : Nat) : Nat := (targets.filter (fun t => !S.testBit t)).length

def members (S : Nat) : List Nat := (List.range 32).filter (fun x => S.testBit x)

def andOr (S v : Nat) : Bool :=
  (members S).any (fun x => (members S).any (fun y => x &&& y == v || x ||| y == v))

def notOf (S v : Nat) : Bool := (members S).any (fun x => 31 ^^^ x == v)

def good (S : Nat) : Nat → Nat → Bool
  | 0, _ => need S == 0
  | g + 1, n => need S == 0 || (decide (need S ≤ g + 1) && (good S g n ||
      (List.range 32).any (fun v => !S.testBit v &&
        ((andOr S v && good (S ||| 2 ^ v) g n) ||
         (decide (0 < n) && notOf S v && good (S ||| 2 ^ v) g (n - 1))))))

def gval (W : List Nat) : GateOp → List Nat → Nat
  | .and, [] => 31
  | .and, [i] => W.getD i 0
  | .and, i :: j :: _ => W.getD i 0 &&& W.getD j 0
  | .or, [] => 0
  | .or, [i] => W.getD i 0
  | .or, i :: j :: _ => W.getD i 0 ||| W.getD j 0
  | .not, [] => 31
  | .not, i :: _ => 31 ^^^ W.getD i 0
  | _, _ => 0

def wiresP (gs : List Gate) (W : List Nat) : List Nat :=
  gs.foldl (fun W g => W ++ [gval W g.op g.inputs]) W

def cnt (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

def Fan (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem need_or (S v : Nat) : need S ≤ need (S ||| 2 ^ v) + 1 := by
  simp only [need, targets, List.filter, Nat.testBit_or, Nat.testBit_two_pow]
  repeat' split
  all_goals (simp_all; try omega)

theorem need_zero {S : Nat} (h : ∀ t ∈ targets, S.testBit t = true) : need S = 0 := by
  unfold need
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro t ht; simp [h t ht]

theorem good_of_need {S g n : Nat} (h : need S = 0) : good S g n = true := by
  cases g <;> simp [good, h]

theorem need_of_good {S g n : Nat} (h : good S g n = true) : need S ≤ g := by
  cases g with
  | zero => simp [good] at h; omega
  | succ g =>
    simp only [good, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩ <;> omega

theorem lt32_and {a b : Nat} (_ha : a < 32) (hb : b < 32) : a &&& b < 32 :=
  Nat.and_lt_two_pow (n := 5) a hb
theorem lt32_or {a b : Nat} (ha : a < 32) (hb : b < 32) : a ||| b < 32 :=
  Nat.or_lt_two_pow (n := 5) ha hb
theorem lt32_xor {b : Nat} (hb : b < 32) : 31 ^^^ b < 32 :=
  Nat.xor_lt_two_pow (n := 5) (by norm_num) hb

theorem mem_members {S x : Nat} (hx : x < 32) (h : S.testBit x = true) : x ∈ members S := by
  simp [members, hx, h]

theorem step (W : List Nat) (S : Nat) (g : Gate) (hg : Fan g)
    (hW : ∀ x ∈ W, x < 32 ∧ S.testBit x = true) (h0 : S.testBit 0 = true)
    (h31 : S.testBit 31 = true) :
    gval W g.op g.inputs < 32 ∧ (S.testBit (gval W g.op g.inputs) = true ∨
      (g.op ≠ GateOp.not ∧ andOr S (gval W g.op g.inputs) = true) ∨
      (g.op = GateOp.not ∧ notOf S (gval W g.op g.inputs) = true)) := by
  have hget : ∀ i, W.getD i 0 < 32 ∧ S.testBit (W.getD i 0) = true := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hc : W[i]? with
    | none => simp [h0]
    | some x => simpa using hW x (List.mem_of_getElem? hc)
  obtain ⟨hop, hlen⟩ := hg
  have m31 : (31 : Nat) ∈ members S := mem_members (by norm_num) h31
  have m0 : (0 : Nat) ∈ members S := mem_members (by norm_num) h0
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop hlen ⊢
  rcases hop with rfl | rfl | rfl <;>
    match ins, hlen with
    | [], _ =>
      simp only [gval]
      first
      | exact ⟨by norm_num, Or.inl h31⟩
      | exact ⟨by norm_num, Or.inl h0⟩
    | [i], _ =>
      simp only [gval]
      first
      | exact ⟨(hget i).1, Or.inl (hget i).2⟩
      | exact ⟨lt32_xor (hget i).1, Or.inr (Or.inr ⟨by simp, by
          simp only [notOf, List.any_eq_true, beq_iff_eq]
          exact ⟨_, mem_members (hget i).1 (hget i).2, rfl⟩⟩)⟩
    | [i, j], _ =>
      simp only [gval]
      first
      | exact ⟨lt32_and (hget i).1 (hget j).1, Or.inr (Or.inl ⟨by simp, by
          simp only [andOr, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
          exact ⟨_, mem_members (hget i).1 (hget i).2, _, mem_members (hget j).1 (hget j).2,
            Or.inl rfl⟩⟩)⟩
      | exact ⟨lt32_or (hget i).1 (hget j).1, Or.inr (Or.inl ⟨by simp, by
          simp only [andOr, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
          exact ⟨_, mem_members (hget i).1 (hget i).2, _, mem_members (hget j).1 (hget j).2,
            Or.inr rfl⟩⟩)⟩
      | exact ⟨lt32_xor (hget i).1, Or.inr (Or.inr ⟨by simp, by
          simp only [notOf, List.any_eq_true, beq_iff_eq]
          exact ⟨_, mem_members (hget i).1 (hget i).2, rfl⟩⟩)⟩
    | _ :: _ :: _ :: _, h => simp at h

theorem search (gs : List Gate) : ∀ (W : List Nat) (S g n : Nat), (∀ x ∈ gs, Fan x) →
    gs.length ≤ g → cnt gs ≤ n → (∀ x ∈ W, x < 32 ∧ S.testBit x = true) →
    S.testBit 0 = true → S.testBit 31 = true → (∀ t ∈ targets, t ∈ wiresP gs W) →
    good S g n = true := by
  induction gs with
  | nil =>
    intro W S g n _ _ _ hW _ _ hT
    exact good_of_need (need_zero fun t ht => (hW t (hT t ht)).2)
  | cons g0 rest ih =>
    intro W S g n hF hlen hcnt hW h0 h31 hT
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hlen; omega⟩
    have hlen' : rest.length ≤ g' := by simp at hlen; omega
    have hF' : ∀ x ∈ rest, Fan x := fun x hx => hF x (List.mem_cons_of_mem _ hx)
    have hT' : ∀ t ∈ targets, t ∈ wiresP rest (W ++ [gval W g0.op g0.inputs]) := hT
    set v := gval W g0.op g0.inputs with hvdef
    obtain ⟨hv32, hcase⟩ := step W S g0 (hF g0 (List.mem_cons_self ..)) hW h0 h31
    rw [← hvdef] at hv32 hcase
    have hcnt' : (g0.op = GateOp.not → cnt rest + 1 ≤ n) ∧ (g0.op ≠ GateOp.not → cnt rest ≤ n) := by
      simp only [cnt, PEqualNP.NotBracket.notCount, List.filter_cons] at hcnt ⊢
      constructor <;> intro h <;> simp [h] at hcnt <;> omega
    by_cases hin : S.testBit v = true
    · have hg := ih (W ++ [v]) S g' n hF' hlen' (by by_cases h : g0.op = GateOp.not; have := hcnt'.1 h; omega; exact hcnt'.2 h)
        (by intro x hx; simp at hx; rcases hx with hx | rfl; exact hW x hx; exact ⟨hv32, hin⟩)
        h0 h31 hT'
      have hn := need_of_good hg
      simp only [good, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨by omega, Or.inl hg⟩
    · have hW' : ∀ x ∈ W ++ [v], x < 32 ∧ (S ||| 2 ^ v).testBit x = true := by
        intro x hx; simp at hx
        rcases hx with hx | rfl
        · exact ⟨(hW x hx).1, by simp [Nat.testBit_or, (hW x hx).2]⟩
        · exact ⟨hv32, by simp [Nat.testBit_or, Nat.testBit_two_pow]⟩
      have h0' : (S ||| 2 ^ v).testBit 0 = true := by rw [Nat.testBit_or, h0, Bool.true_or]
      have h31' : (S ||| 2 ^ v).testBit 31 = true := by rw [Nat.testBit_or, h31, Bool.true_or]
      have hmono := need_or S v
      have hvr : v ∈ List.range 32 := List.mem_range.2 hv32
      rcases hcase with h | ⟨hop, hao⟩ | ⟨hop, hno⟩
      · exact absurd h hin
      · have hg := ih (W ++ [v]) (S ||| 2 ^ v) g' n hF' hlen' (hcnt'.2 hop)
          hW' h0' h31' hT'
        have hn := need_of_good hg
        simp only [good, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
          List.any_eq_true]
        refine Or.inr ⟨by omega, Or.inr ⟨v, hvr, ?_⟩⟩
        simp [hin, hao, hg]
      · have hg := ih (W ++ [v]) (S ||| 2 ^ v) g' (n - 1) hF' hlen'
          (by have := hcnt'.1 hop; omega) hW' h0' h31' hT'
        have hn := need_of_good hg
        have hnpos : 0 < n := by have := hcnt'.1 hop; omega
        simp only [good, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
          List.any_eq_true]
        refine Or.inr ⟨by omega, Or.inr ⟨v, hvr, ?_⟩⟩
        simp [hin, hno, hg, hnpos]

theorem sem (gs : List Gate) : ∀ (w : Fin 5 → List Bool) (W : List Nat), (∀ x ∈ gs, Fan x) →
    (∀ t, (w t).length = W.length) →
    (∀ t i, (w t).getD i false = (W.getD i 0).testBit t.val) →
    (∀ t i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w t)).getD i false = ((wiresP gs W).getD i 0).testBit t.val) := by
  induction gs with
  | nil => intro w W _ _ h; exact h
  | cons g0 rest ih =>
    intro w W hF hl h
    have key : ∀ t : Fin 5, g0.op.eval (g0.inputs.map fun i => (w t).getD i false) =
        (gval W g0.op g0.inputs).testBit t.val := by
      intro t
      have t5 : t.val < 5 := t.isLt
      have b31 : (31 : Nat).testBit t.val = true :=
        (by decide : ∀ t < 5, (31 : Nat).testBit t = true) t.val t5
      obtain ⟨hop, hlen⟩ := hF g0 (List.mem_cons_self ..)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop <;> rw [hop] <;>
        match g0.inputs, hlen with
        | [], _ => simp [GateOp.eval, gval, b31]
        | [i], _ =>
          simp only [GateOp.eval, gval, List.map_cons, List.map_nil, h t i]
          simp [Nat.testBit_xor, b31]
        | [i, j], _ =>
          simp only [GateOp.eval, gval, List.map_cons, List.map_nil, h t i, h t j]
          simp [Nat.testBit_xor, b31]
        | _ :: _ :: _ :: _, h => simp at h
    exact ih (fun t => w t ++ [g0.op.eval (g0.inputs.map fun i => (w t).getD i false)])
      (W ++ [gval W g0.op g0.inputs]) (fun x hx => hF x (List.mem_cons_of_mem _ hx))
      (by intro t; simp [hl t])
      (by
        intro t i
        rcases lt_trichotomy i W.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ (by rw [hl t]; exact hi), List.getD_append _ _ _ _ hi]
          exact h t i
        · subst hi
          rw [List.getD_append_right _ _ _ _ (by rw [hl t]), List.getD_append_right _ _ _ _ le_rfl]
          rw [hl t, Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero]
          exact key t
        · rw [List.getD_eq_default _ _ (by simp [hl t]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
          simp)

theorem wiresP_length (gs : List Gate) : ∀ W, (wiresP gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp [wiresP]
  | cons g rest ih =>
    intro W
    have e : wiresP (g :: rest) W = wiresP rest (W ++ [gval W g.op g.inputs]) := rfl
    rw [e, ih]; simp; omega

theorem bound (gs : List Gate) : ∀ W : List Nat, (∀ x ∈ gs, Fan x) → (∀ x ∈ W, x < 32) →
    ∀ x ∈ wiresP gs W, x < 32 := by
  induction gs with
  | nil => intro W _ h; exact h
  | cons g rest ih =>
    intro W hF hW
    have hb : ∀ x < 32, (2 ^ 32 - 1 : Nat).testBit x = true := by
      intro x hx; rw [Nat.testBit_two_pow_sub_one]; simpa using hx
    have hv := (step W (2 ^ 32 - 1) g (hF g (List.mem_cons_self ..))
      (fun x hx => ⟨hW x hx, hb x (hW x hx)⟩) (hb 0 (by norm_num)) (hb 31 (by norm_num))).1
    exact ih (W ++ [gval W g.op g.inputs]) (fun x hx => hF x (List.mem_cons_of_mem _ hx))
      (by intro x hx; simp at hx; rcases hx with hx | rfl; exact hW x hx; exact hv)

set_option maxRecDepth 100000 in
theorem good_false : good S0 gateBudget notBudget = false := by decide

theorem pat_eq {x a : Nat} (hx : x < 32) (ha : a < 32)
    (h : ∀ t : Fin 5, x.testBit t.val = a.testBit t.val) : x = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 5
  · exact h ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
        calc (32 : Nat) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (by
        calc (32 : Nat) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))]

end PEqualNP.Outside.L_meta_50025

theorem PEqualNP.Outside.L_meta_50025 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (29 : Nat).testBit t.val) := by
  open PEqualNP.Outside.L_meta_50025 in
  rintro ⟨D, p, q, r, hF, -, hN, hS, hw⟩
  have hFan : ∀ x ∈ D.gates, Fan x := fun x hx => hF x hx
  have hsem := sem D.gates (fun t => (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++
    [false,true]) W0 hFan (by intro t; simp [W0]) (by
      intro t i
      rcases t with ⟨t, ht⟩
      rcases i with _ | _ | _ | _ | _ | _ | i
      all_goals simp [W0, List.getD_eq_default, List.getD_append_right]
      all_goals (interval_cases t <;> rfl))
  have hlen : (wiresP D.gates W0).length = 6 + D.size := by
    rw [wiresP_length]; rfl

  have hall : ∀ x ∈ wiresP D.gates W0, x < 32 := by
    exact bound D.gates W0 hFan (by intro x hx; simp [W0] at hx; omega)
  have tgt : ∀ (k : Fin (6 + D.size)) (a : Nat), a < 32 →
      (∀ t : Fin 5, ((D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++
        [false,true])).getD k.val false) = a.testBit t.val) → a ∈ wiresP D.gates W0 := by
    intro k a ha hk
    have hk' : k.val < (wiresP D.gates W0).length := by rw [hlen]; exact k.isLt
    have hm := List.getElem_mem hk'
    rw [← List.getD_eq_getElem _ 0 hk'] at hm
    rwa [← pat_eq (hall _ hm) ha (fun t => by rw [← hsem t k.val]; exact hk t)]
  have h1 := tgt p 5 (by norm_num) (fun t => (hw t).1)
  have h2 := tgt q 22 (by norm_num) (fun t => (hw t).2.1)
  have h3 := tgt r 29 (by norm_num) (fun t => (hw t).2.2)
  have hg := search D.gates W0 S0 gateBudget notBudget hFan hS hN
    (by intro x hx; simp [W0] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide)
    (by intro t ht; simp [targets] at ht; rcases ht with rfl | rfl | rfl <;> assumption)
  rw [good_false] at hg
  exact absurd hg (by decide)
