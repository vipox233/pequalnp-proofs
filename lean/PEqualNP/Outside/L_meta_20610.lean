import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20610

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

inductive Tree where
  | leaf (wire : ℕ)
  | const (value : Bool)
  | join (and : Bool) (left right : Tree)

def applyOp (and a b : Bool) : Bool := if and then a && b else a || b

def evaluate : Tree → (ℕ → Bool) → Bool
  | .leaf i, x => x i
  | .const b, _ => b
  | .join op l r, x => applyOp op (evaluate l x) (evaluate r x)

def support : Tree → Finset ℕ
  | .leaf i => {i}
  | .const _ => ∅
  | .join _ l r => support l ∪ support r

theorem eval_mono (t : Tree) (x y : ℕ → Bool)
    (h : ∀ i ∈ support t, x i = true → y i = true) :
    evaluate t x = true → evaluate t y = true := by
  induction t with
  | leaf i => exact h i (by simp [support])
  | const b => simp [evaluate]
  | join op l r hl hr =>
    have upL := hl (fun i hi => h i (by simp [support, hi]))
    have upR := hr (fun i hi => h i (by simp [support, hi]))
    cases op <;> simp only [evaluate, applyOp, Bool.false_eq_true, if_false, if_true,
      Bool.and_eq_true, Bool.or_eq_true]
    · exact Or.imp upL upR
    · exact And.imp upL upR

def replace (k : ℕ) (p : Tree) : Tree → Tree
  | .leaf i => if i = k then p else .leaf i
  | .const b => .const b
  | .join op l r => .join op (replace k p l) (replace k p r)

theorem eval_replace (k : ℕ) (p t : Tree) (v : ℕ → Bool) :
    evaluate (replace k p t) v = evaluate t (fun i => if i = k then evaluate p v else v i) := by
  induction t with
  | leaf i => by_cases h : i = k <;> simp [replace, evaluate, h]
  | const b => rfl
  | join op l r hl hr => simp [replace, evaluate, hl, hr]

theorem vars_replace (k : ℕ) (p t : Tree) :
    support (replace k p t) = if k ∈ support t then (support t).erase k ∪ support p else support t := by
  induction t with
  | leaf i =>
    by_cases h : i = k
    · subst i; simp [replace, support]
    · simp [replace, support, h, Ne.symm h]
  | const b => simp [replace, support]
  | join op l r hl hr =>
    simp only [replace, support, hl, hr]
    ext i
    by_cases hL : k ∈ support l <;> by_cases hR : k ∈ support r <;>
      by_cases hI : i = k <;> simp_all [Finset.mem_union, Finset.mem_erase]
    all_goals tauto

def rawAt (k a : ℕ) : Tree := if a < k then .leaf a else .const false

def gateTree (k : ℕ) (g : Gate) : Tree :=
  match g with
  | ⟨op, []⟩ => .const (match op with | .and => true | _ => false)
  | ⟨_, [a]⟩ => rawAt k a
  | ⟨op, a :: b :: _⟩ => .join (match op with | .and => true | _ => false) (rawAt k a) (rawAt k b)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

theorem runLen (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (run gs x ++ [_]).length = x.length + (gs ++ [g]).length
    simp [ih, Nat.add_assoc]

theorem getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i = l.length then b else l.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | rfl | h
  · simp [List.getElem?_append_left h, ne_of_lt h]
  · simp
  · have h2 : l.length + 1 ≤ i := by omega
    simp [List.getElem?_eq_none h.le, List.getElem?_eq_none (by simpa using h2 : (l ++ [b]).length ≤ i), ne_of_gt h]

theorem rawAt_eval (w : List Bool) (a : ℕ) :
    evaluate (rawAt w.length a) (fun i => w.getD i false) = w.getD a false := by
  unfold rawAt
  split_ifs with h
  · rfl
  · simp [evaluate, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem gateTree_eval (w : List Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    evaluate (gateTree w.length g) (fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl <;> rfl
  · rcases hop with rfl | rfl <;> simp only [gateTree, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true, Bool.or_false, rawAt_eval]
  · rcases hop with rfl | rfl <;> simp only [gateTree, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true, Bool.or_false, evaluate, applyOp, Bool.false_eq_true, if_false, if_true, rawAt_eval]
  · simp at hlen

theorem rawAt_small (k a : ℕ) : (support (rawAt k a)).card ≤ 1 := by
  unfold rawAt
  split <;> simp [support]

theorem gateTree_small (k : ℕ) (g : Gate) : (support (gateTree k g)).card ≤ 2 := by
  rcases g with ⟨op, _ | ⟨a, _ | ⟨b, rest⟩⟩⟩
  · simp [gateTree, support]
  · exact (rawAt_small k a).trans (by decide)
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add (rawAt_small k a) (rawAt_small k b))

def expandRev (n : ℕ) : List Gate → Tree → Tree
  | [], t => t
  | g :: rest, t => expandRev n rest (replace (n + rest.length) (gateTree (n + rest.length) g) t)

def expand (n : ℕ) (gs : List Gate) (t : Tree) : Tree := expandRev n gs.reverse t

theorem expand_snoc (n : ℕ) (gs : List Gate) (g : Gate) (t : Tree) :
    expand n (gs ++ [g]) t = expand n gs (replace (n + gs.length) (gateTree (n + gs.length) g) t) := by
  simp [expand, expandRev]

theorem expand_eval (n : ℕ) (gs : List Gate) (t : Tree) (x : List Bool) (hx : x.length = n)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    evaluate (expand n gs t) (fun i => x.getD i false) =
      evaluate t (fun i => (run gs x).getD i false) := by
  induction gs using List.reverseRecOn generalizing t with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [expand_snoc, ih _ (fun v hv => hg v (by simp [hv])), eval_replace]
    have ww := runLen gs x
    rw [hx] at ww
    rw [← ww, gateTree_eval _ _ (hg g (by simp)).1 (hg g (by simp)).2]
    congr 1
    funext i
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, step, getD_snoc]
    rfl

theorem replace_small (k : ℕ) (t p : Tree) (h : (support p).card ≤ 2) :
    (support (replace k p t)).card ≤ (support t).card + 1 := by
  rw [vars_replace]
  split_ifs with hk
  · have z := Finset.card_erase_of_mem hk
    have c := Finset.card_union_le ((support t).erase k) (support p)
    have nz : 0 < (support t).card := Finset.card_pos.mpr ⟨k, hk⟩
    omega
  · omega

theorem expand_small (n : ℕ) (gs : List Gate) (t : Tree) :
    (support (expand n gs t)).card ≤ (support t).card + gs.length := by
  induction gs using List.reverseRecOn generalizing t with
  | nil => simp [expand, expandRev]
  | append_singleton gs g ih =>
    rw [expand_snoc]
    have h1 := ih (replace (n+gs.length) (gateTree (n+gs.length) g) t)
    have h2 := replace_small (n+gs.length) t (gateTree (n+gs.length) g) (gateTree_small _ _)
    simp only [List.length_append, List.length_singleton]
    omega

private def relation (u v : Fin 5) : Bool :=
  (8521760 : ℕ).testBit (5*u.val+v.val)

private def posPair (i : Fin 8) : Fin 5 × Fin 5 :=
  (⟨i.val % 4 + 1, by omega⟩,⟨i.val % 4,by omega⟩)

private def negPair (i : Fin 8) : Fin 5 × Fin 5 :=
  if i.val < 4 then (0,(posPair i).2) else ((posPair i).1,4)

private theorem pairTests :
    ∀ i : Fin 8,
      relation (posPair i).1 (posPair i).2 = true ∧
      relation (negPair i).1 (negPair i).2 = false ∧
      ∀ k : Fin 10, k.val ≠ i.val+1 →
        (oneEach (posPair i).1 (posPair i).2).getD k.val false = true →
        (oneEach (negPair i).1 (negPair i).2).getD k.val false = true := by
  decide +kernel

private theorem requireWire (C : Circuit) (rep : Represents relation C) (mono : Monotone2 C)
    (i : Fin 8) : i.val+1 ∈ support (expand 10 C.gates (.leaf C.output)) := by
  by_contra absent
  let t := expand 10 C.gates (.leaf C.output)
  obtain ⟨yes,no,order⟩ := pairTests i
  let p := oneEach (posPair i).1 (posPair i).2
  let q := oneEach (negPair i).1 (negPair i).2
  have r (u v : Fin 5) :
      evaluate t (fun k => (oneEach u v).getD k false) = relation u v := by
    have proof := expand_eval 10 C.gates (.leaf C.output) (oneEach u v)
      (by simp [oneEach]) (fun g hm => by simpa [Monotone2] using mono g hm)
    exact proof.trans (rep u v)
  have tTrue : evaluate t (fun k => p.getD k false) = true :=
    (r _ _).trans yes
  have tFalse : evaluate t (fun k => q.getD k false) = false :=
    (r _ _).trans no
  have tAgain : evaluate t (fun k => q.getD k false) = true := by
    apply eval_mono t (fun k => p.getD k false) _ ?_ tTrue
    intro k mem full
    have ne : k ≠ i.val+1 := fun e => absent (e ▸ mem)
    by_cases small : k<10
    · exact order ⟨k,small⟩ ne full
    · have far : p.length ≤ k := by simpa [p,oneEach] using Nat.le_of_not_gt small
      rw [List.getD_eq_default _ _ far] at full
      exact Bool.noConfusion full
  exact Bool.noConfusion (tFalse.symm.trans tAgain)

private theorem lower (C : Circuit) (rep : Represents relation C) (mono : Monotone2 C) :
    7 ≤ C.size := by
  let W : Finset ℕ := Finset.univ.image (fun i : Fin 8 => i.val+1)
  have cardW : W.card = 8 := by
    rw [show W = Finset.univ.image (fun i : Fin 8 => i.val+1) from rfl,
      Finset.card_image_of_injective _ (fun a b eq => Fin.ext (Nat.add_right_cancel eq))]
    simp
  have covered : W ⊆ support (expand 10 C.gates (.leaf C.output)) := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact requireWire C rep mono i
  have c := Finset.card_le_card covered
  have up := expand_small 10 C.gates (.leaf C.output)
  simp only [support,Finset.card_singleton] at up
  change 7 ≤ C.gates.length
  omega

private def witness : Circuit :=
  ⟨[⟨.and,[1,5]⟩,⟨.and,[2,6]⟩,⟨.and,[3,7]⟩,⟨.and,[4,8]⟩,
    ⟨.or,[10,11]⟩,⟨.or,[14,12]⟩,⟨.or,[15,13]⟩],16⟩

private theorem witnessMono : Monotone2 witness := by simp [Monotone2,witness]

end PEqualNP.Outside.L_meta_20610

open PEqualNP.Outside.L_meta_20610 in
theorem PEqualNP.Outside.L_meta_20610 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (8521760 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (8521760 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  constructor
  · exact ⟨witness,witnessMono,by decide,by decide +kernel⟩
  · rintro ⟨C,mono,small,rep⟩
    have impossible := lower C rep mono
    omega
