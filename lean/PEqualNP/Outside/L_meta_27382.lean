import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27382_aux

namespace FormulaInvariant

inductive Formula where
  | var : Nat → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula

def leaves : Formula → List Nat
  | .var i => [i]
  | .conj l r | .disj l r => leaves l ++ leaves r

def eval (env : Nat → Bool) : Formula → Bool
  | .var i => env i
  | .conj l r => eval env l && eval env r
  | .disj l r => eval env l || eval env r

theorem eval_congr (f : Formula) {env₁ env₂ : Nat → Bool}
    (h : ∀ i ∈ leaves f, env₁ i = env₂ i) : eval env₁ f = eval env₂ f := by
  induction f with
  | var i => exact h i (by simp [leaves])
  | conj l r ihl ihr | disj l r ihl ihr =>
    have hl := ihl (fun i hi => h i (by simp [leaves, hi]))
    have hr := ihr (fun i hi => h i (by simp [leaves, hi]))
    simp only [eval, hl, hr]

/-- Only leaf `a` may depend on the first input, and only `b` on the second. -/
def IsContext (a b : Nat) (ctx : Bool → Bool → Nat → Bool) : Prop :=
  (∀ x x' y i, i ≠ a → ctx x y i = ctx x' y i) ∧
  (∀ x y y' i, i ≠ b → ctx x y i = ctx x y' i)

private theorem fixed_first (f : Formula) {a b : Nat} {ctx : Bool → Bool → Nat → Bool}
    (hc : IsContext a b ctx) (ha : a ∉ leaves f) (x x' y : Bool) :
    eval (ctx x y) f = eval (ctx x' y) f :=
  eval_congr f (fun i hi => hc.1 x x' y i (fun e => ha (e ▸ hi)))

private theorem fixed_second (f : Formula) {a b : Nat} {ctx : Bool → Bool → Nat → Bool}
    (hc : IsContext a b ctx) (hb : b ∉ leaves f) (x y y' : Bool) :
    eval (ctx x y) f = eval (ctx x y') f :=
  eval_congr f (fun i hi => hc.2 x y y' i (fun e => hb (e ▸ hi)))

private theorem fixed_both (f : Formula) {a b : Nat} {ctx : Bool → Bool → Nat → Bool}
    (hc : IsContext a b ctx) (ha : a ∉ leaves f) (hb : b ∉ leaves f) (x y : Bool) :
    eval (ctx x y) f = eval (ctx false false) f :=
  (fixed_first f hc ha x false y).trans (fixed_second f hc hb false y false)

private inductive Gate where
  | conj
  | disj

private def Gate.run : Gate → Bool → Bool → Bool
  | .conj => (· && ·)
  | .disj => (· || ·)

private theorem Gate.run_comm (g : Gate) (x y : Bool) : g.run x y = g.run y x := by
  cases g <;> simp [Gate.run, Bool.and_comm, Bool.or_comm]

private theorem remove_fixed (g : Gate) {s t goal : Bool → Bool → Bool} {c : Bool}
    (hs : ∀ x y, s x y = c) (hf : goal false false = false) (ht : goal true true = true)
    (h : ∀ x y, g.run (s x y) (t x y) = goal x y) :
    ∀ x y, t x y = goal x y := by
  cases g <;> cases c
  · have h₁ := h true true
    simp [Gate.run, hs, ht] at h₁
  · intro x y
    simpa [Gate.run, hs] using h x y
  · intro x y
    simpa [Gate.run, hs] using h x y
  · have h₀ := h false false
    simp [Gate.run, hs, hf] at h₀

private theorem split_impossible (g : Gate) (l r : Formula) {a b : Nat}
    {ctxAnd ctxOr : Bool → Bool → Nat → Bool} (hcAnd : IsContext a b ctxAnd)
    (hcOr : IsContext a b ctxOr) (hl : b ∉ leaves l) (hr : a ∉ leaves r)
    (hAnd : ∀ x y, g.run (eval (ctxAnd x y) l) (eval (ctxAnd x y) r) = (x && y))
    (hOr : ∀ x y, g.run (eval (ctxOr x y) l) (eval (ctxOr x y) r) = (x || y)) : False := by
  cases g with
  | conj =>
    have h₁ := hOr false true
    have h₂ := hOr true false
    have h₀ := hOr false false
    rw [fixed_second l hcOr hl false true false] at h₁
    rw [fixed_first r hcOr hr true false false] at h₂
    simp only [Gate.run, Bool.false_or, Bool.true_or, Bool.and_eq_true] at h₁ h₂ h₀
    simp [h₁.1, h₂.2] at h₀
  | disj =>
    have h₁ := hAnd true false
    have h₂ := hAnd false true
    have h₀ := hAnd true true
    rw [fixed_second l hcAnd hl true false true] at h₁
    rw [fixed_first r hcAnd hr false true true] at h₂
    simp only [Gate.run, Bool.true_and, Bool.false_and, Bool.or_eq_false_iff] at h₁ h₂ h₀
    simp [h₁.1, h₂.2] at h₀

private theorem not_mem_other {a : Nat} {l r : List Nat} (h : l.count a + r.count a ≤ 1)
    (hl : a ∈ l) : a ∉ r := by
  intro hr
  have h₁ := List.count_pos_iff.mpr hl
  have h₂ := List.count_pos_iff.mpr hr
  omega

private theorem no_and_or_node (g : Gate) (l r : Formula) {a b : Nat}
    {ctxAnd ctxOr : Bool → Bool → Nat → Bool} (hcAnd : IsContext a b ctxAnd)
    (hcOr : IsContext a b ctxOr)
    (ihl : (leaves l).count a ≤ 1 → (leaves l).count b ≤ 1 →
      (∀ x y, eval (ctxAnd x y) l = (x && y)) → (∀ x y, eval (ctxOr x y) l = (x || y)) → False)
    (ihr : (leaves r).count a ≤ 1 → (leaves r).count b ≤ 1 →
      (∀ x y, eval (ctxAnd x y) r = (x && y)) → (∀ x y, eval (ctxOr x y) r = (x || y)) → False)
    (ha : (leaves l).count a + (leaves r).count a ≤ 1)
    (hb : (leaves l).count b + (leaves r).count b ≤ 1)
    (hAnd : ∀ x y, g.run (eval (ctxAnd x y) l) (eval (ctxAnd x y) r) = (x && y))
    (hOr : ∀ x y, g.run (eval (ctxOr x y) l) (eval (ctxOr x y) r) = (x || y)) : False := by
  have hAnd' x y := (g.run_comm _ _).trans (hAnd x y)
  have hOr' x y := (g.run_comm _ _).trans (hOr x y)
  by_cases hla : a ∈ leaves l <;> by_cases hlb : b ∈ leaves l
  · have hra := not_mem_other ha hla
    have hrb := not_mem_other hb hlb
    exact ihl (by omega) (by omega)
      (remove_fixed g (fixed_both r hcAnd hra hrb) rfl rfl hAnd')
      (remove_fixed g (fixed_both r hcOr hra hrb) rfl rfl hOr')
  · exact split_impossible g l r hcAnd hcOr hlb (not_mem_other ha hla) hAnd hOr
  · exact split_impossible g r l hcAnd hcOr (not_mem_other hb hlb) hla hAnd' hOr'
  · exact ihr (by omega) (by omega)
      (remove_fixed g (fixed_both l hcAnd hla hlb) rfl rfl hAnd)
      (remove_fixed g (fixed_both l hcOr hla hlb) rfl rfl hOr)

/-- A formula reading each of two distinguished variables at most once cannot realize
AND in one context and OR in another. Other variables can change between contexts. -/
theorem no_and_or_of_contexts (f : Formula) {a b : Nat} (hab : a ≠ b)
    {ctxAnd ctxOr : Bool → Bool → Nat → Bool} (hcAnd : IsContext a b ctxAnd)
    (hcOr : IsContext a b ctxOr) (ha : (leaves f).count a ≤ 1) (hb : (leaves f).count b ≤ 1)
    (hAnd : ∀ x y, eval (ctxAnd x y) f = (x && y))
    (hOr : ∀ x y, eval (ctxOr x y) f = (x || y)) : False := by
  induction f with
  | var i =>
    by_cases hai : a = i
    · have hbi : b ∉ leaves (.var i) := by simpa [leaves, ← hai] using Ne.symm hab
      have h := fixed_second (.var i) hcAnd hbi true false true
      simp only [hAnd, Bool.true_and] at h
      contradiction
    · have hai' : a ∉ leaves (.var i) := by simpa [leaves] using hai
      have h := fixed_first (.var i) hcAnd hai' false true true
      simp only [hAnd, Bool.false_and, Bool.true_and] at h
      contradiction
  | conj l r ihl ihr =>
    simp only [leaves, List.count_append] at ha hb
    exact no_and_or_node .conj l r hcAnd hcOr ihl ihr ha hb hAnd hOr
  | disj l r ihl ihr =>
    simp only [leaves, List.count_append] at ha hb
    exact no_and_or_node .disj l r hcAnd hcOr ihl ihr ha hb hAnd hOr

/-- Use a fixed environment except for labels `a` and `b`. -/
def context (a b : Nat) (env : Nat → Bool) (x y : Bool) (i : Nat) : Bool :=
  if i = a then x else if i = b then y else env i

private theorem context_isContext (a b : Nat) (env : Nat → Bool) :
    IsContext a b (context a b env) := by
  constructor
  · intro x x' y i hi
    simp [context, hi]
  · intro x y y' i hi
    simp [context, hi]

theorem no_and_or (f : Formula) (envAnd envOr : Nat → Bool)
    (h₂ : (leaves f).count 2 ≤ 1) (h₄ : (leaves f).count 4 ≤ 1)
    (hAnd : ∀ x y, eval (context 2 4 envAnd x y) f = (x && y))
    (hOr : ∀ x y, eval (context 2 4 envOr x y) f = (x || y)) : False :=
  no_and_or_of_contexts f (by decide) (context_isContext 2 4 envAnd) (context_isContext 2 4 envOr)
    h₂ h₄ hAnd hOr

end FormulaInvariant

open PEqualNP.CircuitLowerBounds

private def reads (gs : List Gate) : List Nat := gs.flatMap Gate.inputs
private def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem agree (gs : List Gate) (a b : List Bool) (o : Nat)
    (hl : a.length = b.length)
    (h : ∀ i ∈ reads gs, a.getD i false = b.getD i false)
    (ho : a.getD o false = b.getD o false) :
    (gs.foldl push a).getD o false = (gs.foldl push b).getD o false := by
  induction gs generalizing a b with
  | nil => exact ho
  | cons g gs ih =>
    have he : g.inputs.map (a.getD · false) = g.inputs.map (b.getD · false) :=
      List.map_congr_left fun i hi => h i (by simp [reads, hi])
    have keep (i : Nat) (e : a.getD i false = b.getD i false) :
        (push a g).getD i false = (push b g).getD i false := by
      by_cases hi : i < a.length
      · simpa only [push, List.getD_append _ _ _ _ hi,
          List.getD_append _ _ _ _ (show i < b.length by omega)] using e
      · simp only [push, List.getD_append_right _ _ _ _ (show a.length ≤ i by omega),
          List.getD_append_right _ _ _ _ (show b.length ≤ i by omega), he, hl]
    exact ih _ _ (by simp [push, hl])
      (fun i hi => keep i (h i (List.mem_append_right _ hi))) (keep o ho)

private def first : Gate := ⟨.and, [0,1]⟩
private def second : Gate := ⟨.or, [3,7]⟩
private def pre (x : Fin 9 → Bool) : List Bool := push (push (List.ofFn x) first) second
private def goal (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
private def input (m : Fin 512) (i : Fin 9) : Bool := m.val.testBit i.val

private theorem witnesses : ∀ v : Fin 9,
    ∃ a b : Fin 512, goal (input a) ≠ goal (input b) ∧
      ∀ i : Fin 11, i.val ≠ v.val → (pre (input a)).getD i.val false = (pre (input b)).getD i.val false := by
  intro v
  let masks : Fin 9 → Fin 512 := ![272,96,80,386,257,66,34,41,17]
  refine ⟨masks v, ⟨(masks v).val + 2^v.val, by fin_cases v <;> decide⟩, ?_⟩
  fin_cases v <;> decide +kernel

private theorem pre_length (x : Fin 9 → Bool) : (pre x).length = 11 := by
  simp [pre, push]

private theorem needed (gs : List Gate) (o : Nat) (ho : 11 ≤ o)
    (hev : ∀ x, (gs.foldl push (pre x)).getD o false = goal x) (v : Fin 9) :
    v.val ∈ reads gs := by
  by_contra hn
  obtain ⟨a,b,hab,h⟩ := witnesses v
  have e (i : Nat) (hi : i ≠ v.val) :
      (pre (input a)).getD i false = (pre (input b)).getD i false := by
    by_cases hlt : i < 11
    · exact h ⟨i,hlt⟩ hi
    · simp only [List.getD_eq_default _ _ (show (pre (input a)).length ≤ i by simpa [pre_length] using hlt),
        List.getD_eq_default _ _ (show (pre (input b)).length ≤ i by simpa [pre_length] using hlt)]
  apply hab
  rw [← hev, ← hev]
  exact agree gs _ _ o (by simp [pre_length]) (fun i hi => e i (by rintro rfl; exact hn hi))
    (e o (by omega))

private def Binary (k : Nat) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < k ∧ g.inputs = [a,b]

private def Local (k : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, a < k ∧ g.inputs = [a]) ∨ Binary k g

private inductive Ordered : Nat → List Gate → Prop
  | nil (k) : Ordered k []
  | cons {k g gs} : Local k g → Ordered (k+1) gs → Ordered k (g :: gs)

private theorem ordered_of (k : Nat) (gs : List Gate)
    (h : ∀ j : Fin gs.length, Local (k + j.val) (gs.get j)) : Ordered k gs := by
  induction gs generalizing k with
  | nil => exact .nil k
  | cons g gs ih =>
    refine .cons (by simpa using h ⟨0, by simp⟩) (ih (k+1) ?_)
    intro j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h j.succ

private theorem local_bounds {k g} (hg : Local k g) :
    g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < k) ∧ (g.inputs.length = 2 → Binary k g) := by
  rcases hg with ⟨_, a, ha, he⟩ | hb
  · simp [he, ha]
  · rcases hb with ⟨hop,a,b,hab,hb,he⟩
    exact ⟨by simp [he], by simp [he]; omega, fun _ => ⟨hop,a,b,hab,hb,he⟩⟩

private theorem ordered_bounds {k gs} (h : Ordered k gs) :
    (reads gs).length ≤ 2 * gs.length ∧ (∀ i ∈ reads gs, i + 1 < k + gs.length) := by
  induction h with
  | nil => simp [reads]
  | @cons k g gs hg _ ih =>
    obtain ⟨hl, hb⟩ := ih
    obtain ⟨gl, gb, _⟩ := local_bounds hg
    constructor
    · simp only [reads, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega
    · intro i hi
      simp only [reads, List.flatMap_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · have := gb i hi
        simp only [List.length_cons]
        omega
      · have := hb i hi
        simp only [List.length_cons]
        omega

private inductive LinearOrder : Nat → List Gate → Prop
  | nil (k) : LinearOrder k []
  | cons {k g gs} : Binary k g → LinearOrder (k+1) gs → LinearOrder k (g :: gs)

private theorem linear_of {k gs} (h : Ordered k gs)
    (hlen : (reads gs).length = 2 * gs.length) : LinearOrder k gs := by
  induction h with
  | nil => exact .nil _
  | @cons k g gs hg ht ih =>
    have ht' := (ordered_bounds ht).1
    have hg' := (local_bounds hg).1
    change (g.inputs ++ reads gs).length = 2 * (g :: gs).length at hlen
    simp only [List.length_append, List.length_cons] at hlen
    exact .cons ((local_bounds hg).2.2 (by omega)) (ih (by omega))

private theorem sum_indicator (rs : List Nat) (k c : Nat) :
    (rs.map fun i => if i = k then c else 0).sum = rs.count k * c := by
  induction rs with
  | nil => simp
  | cons i rs ih =>
    by_cases h : i = k
    · subst i
      simp [ih, Nat.add_mul, Nat.add_comm]
    · simp [h, ih]

private theorem sum_add (rs : List Nat) (f g : Nat → Nat) :
    (rs.map fun i => f i + g i).sum = (rs.map f).sum + (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons i rs ih => simp [ih]; omega

private def env (mask : Nat) (a b : Bool) (i : Nat) : Bool :=
  if i = 2 then a else if i = 4 then b else mask.testBit i

private theorem and_context (a b : Bool) :
    goal (fun i => env 64 a b i.val) = (a && b) := by
  cases a <;> cases b <;> decide

private theorem or_context (a b : Bool) :
    goal (fun i => env 393 a b i.val) = (a || b) := by
  cases a <;> cases b <;> decide

private theorem uses_all (gs : List Gate) (o : Nat) (ho : o + 1 = 11 + gs.length)
    (hev : ∀ x, (gs.foldl push (pre x)).getD o false = goal x)
    (hu : ∀ j : Fin (first :: second :: gs).length,
      j.val + 1 < (first :: second :: gs).length →
      ∃ k : Fin (first :: second :: gs).length, j.val < k.val ∧
        9 + j.val ∈ ((first :: second :: gs).get k).inputs) :
    ∀ w, w < o → w ∈ reads gs := by
  intro w hw
  have ho' : 11 ≤ o := by
    by_contra! hn
    have hg : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    have h10 : o = 10 := by omega
    subst o
    have e := hev (input 8)
    have hf : (pre (input 8)).getD 10 false ≠ goal (input 8) := by decide
    exact hf e
  by_cases h9 : w < 9
  · exact needed gs o ho' hev ⟨w,h9⟩
  · let j : Fin (first :: second :: gs).length := ⟨w-9, by simp; omega⟩
    obtain ⟨k, _, hk⟩ := hu j (by simp [j]; omega)
    have he : 9 + j.val = w := by dsimp [j]; omega
    rw [he] at hk
    have hm := List.get_mem (l := first :: second :: gs) k
    have hall : w ∈ reads (first :: second :: gs) :=
      List.mem_flatMap.mpr ⟨_, hm, hk⟩
    change w ∈ [0,1] ++ ([3,7] ++ reads gs) at hall
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hall
    rcases hall with (h | h) | (h | h) | h <;> omega

-- Counting just the tail makes the four extra reads by the fixed gates implicit.
private theorem tail_ledger (L : List Nat) (n o : Nat) (hn : n ≤ 10)
    (ho : o = 10 + n) (hcap : L.length ≤ 2*n)
    (hb : ∀ i ∈ L, i < o) (hc : ∀ i < o, i ∈ L) :
    L.length = 2*n ∧ ∀ i < o, L.count i = 1 := by
  have sum_counts (xs : List Nat) (hxs : ∀ i ∈ xs, i < o) :
      (∑ i ∈ Finset.range o, xs.count i) = xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx : x ∈ Finset.range o := Finset.mem_range.mpr (hxs x (by simp))
      rw [List.length_cons, ← ih (fun i hi => hxs i (List.mem_cons_of_mem x hi))]
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib]
      simp [hx]
  have hsum := sum_counts L hb
  have hp : ∀ i ∈ Finset.range o, (1 : Nat) ≤ L.count i :=
    fun i hi => List.count_pos_iff.mpr (hc i (Finset.mem_range.mp hi))
  have hmin := Finset.sum_le_sum hp
  have hconst : (∑ _i ∈ Finset.range o, (1 : Nat)) = o := by simp
  rw [hconst, hsum] at hmin
  refine ⟨by omega, fun i hi => ?_⟩
  have hmem := Finset.mem_range.mpr hi
  have hlow := hp i hmem
  by_contra! hne
  have hlt := Finset.sum_lt_sum hp ⟨i, hmem, show 1 < L.count i by omega⟩
  rw [hconst, hsum] at hlt
  omega

open FormulaInvariant (Formula leaves eval no_and_or)

private def dummy : Formula := .var 30
private def isAnd : GateOp → Bool
  | .and => true
  | _ => false
private def fp (w : List Formula) (g : Gate) : List Formula :=
  w ++ [if isAnd g.op then .conj (w.getD (g.inputs.getD 0 0) dummy)
      (w.getD (g.inputs.getD 1 0) dummy)
    else .disj (w.getD (g.inputs.getD 0 0) dummy) (w.getD (g.inputs.getD 1 0) dummy)]

private def score (p : Nat) (w : List Formula) (rs : List Nat) : Nat :=
  (rs.map fun i => (leaves (w.getD i dummy)).count p).sum

private theorem append_score (p : Nat) (hp : p ≠ 30)
    (w : List Formula) (f : Formula) (rs : List Nat) :
    score p (w ++ [f]) rs = score p w rs + rs.count w.length * (leaves f).count p := by
  let v (i : Nat) := (leaves (w.getD i dummy)).count p
  let extra (i : Nat) := if i = w.length then (leaves f).count p else 0
  have hm : (rs.map fun i => (leaves ((w ++ [f]).getD i dummy)).count p) =
      rs.map (fun i => v i + extra i) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < w.length
    · simp only [List.getD_append _ _ _ _ hi, v, extra, ite_eq_right (ne_of_lt hi), Nat.add_zero]
    · by_cases he : i = w.length
      · subst i
        rw [List.getD_append_right _ _ _ _ (by omega)]
        have hd := List.getD_eq_default w dummy (n := w.length) (by omega)
        simp only [v, extra, ite_eq_left rfl, Nat.sub_self]
        rw [hd]
        simp [List.getD, dummy, leaves, Ne.symm hp]
      · have h1 : w.length ≤ i := by omega
        have h2 : (w ++ [f]).length ≤ i := by simp; omega
        simp only [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2,
          v, extra, ite_eq_right he, Nat.add_zero]
  unfold score
  rw [hm, sum_add, sum_indicator]

private theorem formula_score {k gs} (hl : LinearOrder k gs) (w : List Formula)
    (hw : w.length = k) (o p : Nat) (hp : p ≠ 30)
    (hc : ∀ i, k ≤ i → i < k + gs.length → (reads gs ++ [o]).count i = 1) :
    (leaves ((gs.foldl fp w).getD o dummy)).count p = score p w (reads gs ++ [o]) := by
  induction hl generalizing w with
  | nil => simp [reads, score]
  | @cons k g gs hg ht ih =>
    obtain ⟨hop,a,b,hab,hb,hins⟩ := hg
    let A := w.getD a dummy
    let B := w.getD b dummy
    let F := if isAnd g.op then Formula.conj A B else Formula.disj A B
    have hf : fp w g = w ++ [F] := by simp [fp, hins, F, A, B, List.getD]
    have H (i : Nat) (hi : k ≤ i) (hi' : i < k + (g :: gs).length) :
        (reads gs ++ [o]).count i = 1 := by
      have hh := hc i hi hi'
      have ha' : i ≠ a := by omega
      have hb' : i ≠ b := by omega
      change ((g.inputs ++ reads gs) ++ [o]).count i = 1 at hh
      simpa [hins, List.count_cons, ha', hb', Ne.symm ha', Ne.symm hb'] using hh
    have hlen : (fp w g).length = k+1 := by simp [hf, hw]
    change (leaves ((gs.foldl fp (fp w g)).getD o dummy)).count p = _
    rw [ih _ hlen (fun i hi hi' => H i (by omega) (by simp; omega)),
      hf, append_score p hp, hw, H k (by omega) (by simp)]
    have hF : (leaves F).count p = (leaves A).count p + (leaves B).count p := by
      unfold F
      split <;> simp [leaves, List.count_append]
    change _ = score p w ((g.inputs ++ reads gs) ++ [o])
    simp [hF, score, hins, A, B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem eval_formula {k gs} (hl : LinearOrder k gs) (w : List Formula)
    (hw : w.length = k) (e : Nat → Bool) :
    (gs.foldl fp w).map (eval e) = gs.foldl push (w.map (eval e)) := by
  induction hl generalizing w with
  | nil => rfl
  | @cons k g gs hg ht ih =>
    obtain ⟨hop,a,b,hab,hb,hins⟩ := hg
    have ha' : a < w.length := by omega
    have hb' : b < w.length := by omega
    have hread (i : Nat) (hi : i < w.length) :
        (w.map (eval e)).getD i false = eval e (w.getD i dummy) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
      simp
    have hlen : (fp w g).length = k+1 := by simp [fp, hw]
    have hpush : (fp w g).map (eval e) = push (w.map (eval e)) g := by
      simp only [fp, push, hins, List.map_append, List.map_cons, List.map_nil]
      change _ ++ [eval e (if isAnd g.op then Formula.conj (w.getD a dummy) (w.getD b dummy)
        else Formula.disj (w.getD a dummy) (w.getD b dummy))] =
        _ ++ [g.op.eval [(w.map (eval e)).getD a false, (w.map (eval e)).getD b false]]
      rw [hread _ ha', hread _ hb']
      rcases hop with hop | hop <;> simp [hop, isAnd, eval, GateOp.eval]
    change (gs.foldl fp (fp w g)).map (eval e) = gs.foldl push (push (w.map (eval e)) g)
    rw [ih _ hlen, hpush]

private def initial : List Formula := List.ofFn fun i : Fin 11 => .var i.val

private theorem initial_score (rs : List Nat) (p : Nat) (hp : p < 11) :
    score p initial rs = rs.count p := by
  have hm : (rs.map fun i => (leaves (initial.getD i dummy)).count p) =
      rs.map (fun i => if i = p then 1 else 0) := by
    apply List.map_congr_left
    intro i _
    by_cases h : i < 11
    · have hi : i < initial.length := by simpa [initial] using h
      rw [List.getD_eq_getElem _ _ hi]
      simp only [initial, List.getElem_ofFn, leaves]
      by_cases he : i = p <;> simp [he]
    · have hd : initial.length ≤ i := by simp [initial]; omega
      rw [List.getD_eq_default _ _ hd, ite_eq_right (show i ≠ p by omega)]
      simp [dummy, leaves, show 30 ≠ p by omega]
  unfold score
  rw [hm, sum_indicator, Nat.mul_one]

private theorem fp_length (gs : List Gate) (w : List Formula) :
    (gs.foldl fp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    change (gs.foldl fp (fp w g)).length = _
    rw [ih]
    simp [fp, Nat.add_comm, Nat.add_left_comm]

private theorem finish_formula (gs : List Gate) (o : Nat) (ho : o + 1 = 11 + gs.length)
    (hl : LinearOrder 11 gs) (hc : ∀ i < o, (reads gs).count i = 1)
    (hb : ∀ i ∈ reads gs, i < o)
    (hev : ∀ x, (gs.foldl push (pre x)).getD o false = goal x) : False := by
  let w := gs.foldl fp initial
  let f := w.getD o dummy
  have hinit : initial.length = 11 := by simp [initial]
  have hcount (i : Nat) (_ : 11 ≤ i) (hi : i < 11 + gs.length) :
      (reads gs ++ [o]).count i = 1 := by
    by_cases he : i = o
    · subst i
      have hn : o ∉ reads gs := fun h => (lt_irrefl o) (hb o h)
      simp [List.count_eq_zero_of_not_mem hn]
    · have hlt : i < o := by omega
      simp [List.count_append, hc i hlt, Ne.symm he]
  have hleaves (p : Nat) (hp : p < 11) (hpo : p < o) : (leaves f).count p ≤ 1 := by
    change (leaves ((gs.foldl fp initial).getD o dummy)).count p ≤ 1
    rw [formula_score hl initial hinit o p (by omega) hcount, initial_score _ _ hp]
    simp [List.count_append, hc p hpo, (ne_of_lt hpo).symm]
  have hevaluate (e : Nat → Bool) (x : Fin 9 → Bool)
      (he : initial.map (eval e) = pre x) : eval e f = goal x := by
    let h := eval_formula hl initial hinit e
    have hw : o < w.length := by dsimp [w]; rw [fp_length, hinit]; omega
    have hm : o < (w.map (eval e)).length := by simpa using hw
    have hf : eval e f = (w.map (eval e)).getD o false := by
      dsimp [f]
      rw [List.getD_eq_getElem _ _ hw, List.getD_eq_getElem _ _ hm]
      simp
    rw [hf]
    change ((gs.foldl fp initial).map (eval e)).getD o false = _
    rw [h, he, hev]
  have hpreAnd (a b : Bool) :
      initial.map (eval (env 64 a b)) = pre (fun i => env 64 a b i.val) := by
    cases a <;> cases b <;> decide +kernel
  have hpreOr (a b : Bool) :
      initial.map (eval (env 1417 a b)) = pre (fun i => env 393 a b i.val) := by
    cases a <;> cases b <;> decide +kernel
  apply no_and_or f (fun i => Nat.testBit 64 i) (fun i => Nat.testBit 1417 i)
    (hleaves 2 (by decide) (by omega)) (hleaves 4 (by decide) (by omega))
  · intro a b
    exact (hevaluate _ _ (hpreAnd a b)).trans (and_context a b)
  · intro a b
    exact (hevaluate _ _ (hpreOr a b)).trans (or_context a b)

end PEqualNP.Outside.L_meta_27382_aux

open PEqualNP.Outside.L_meta_27382_aux in
theorem PEqualNP.Outside.L_meta_27382 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
        C.output + 1 = 9 + C.size ∧
        (∀ j : Fin C.gates.length,
          ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
              ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
          (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
              ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
        (∀ j : Fin C.gates.length,
          (∃ x y : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
          ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
        (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
          ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
        C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
        C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩) := by
  rintro ⟨⟨gs,o⟩, _, hsize, hev, ho, hloc, _, hu, hfirst, hsecond⟩
  cases gs with
  | nil => simp at hfirst
  | cons g gs =>
    have hg : g = first := Option.some.inj hfirst
    subst g
    cases gs with
    | nil => simp at hsecond
    | cons g gs =>
      have hg : g = second := Option.some.inj hsecond
      subst g
      change o + 1 = 9 + (first :: second :: gs).length at ho
      change (first :: second :: gs).length ≤ 12 at hsize
      simp only [List.length_cons] at ho hsize
      have heval : ∀ x, (gs.foldl push (pre x)).getD o false = goal x := hev
      have hl : Ordered 11 gs := ordered_of _ _ (fun j => by
        let j' : Fin (first :: second :: gs).length := ⟨j.val+2, by simp⟩
        have he : (first :: second :: gs).get j' = gs.get j := rfl
        have hi : 9 + j'.val = 11 + j.val := by dsimp [j']; omega
        have h : Local (9 + j'.val) ((first :: second :: gs).get j') := hloc j'
        simpa only [he, hi] using h)
      have hb : ∀ i ∈ reads gs, i < o := fun i hi => by
        have hh := (ordered_bounds hl).2 i hi
        omega
      obtain ⟨hlen, hc⟩ := tail_ledger (reads gs) gs.length o (by omega) (by omega)
        (ordered_bounds hl).1 hb (uses_all gs o (by omega) heval hu)
      exact finish_formula gs o (by omega) (linear_of hl hlen) hc hb heval
