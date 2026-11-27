import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

inductive PExpr where
  | var (w : Nat)
  | lit (b : Bool)
  | both (a b : PExpr)
  | either (a b : PExpr)
  | neg (a : PExpr)
  deriving DecidableEq

def support : PExpr → Finset Nat
  | .var w => {w}
  | .lit _ => ∅
  | .both a b | .either a b => support a ∪ support b
  | .neg a => support a

def ev : PExpr → Finset Nat → Bool
  | .var w, x => decide (w ∈ x)
  | .lit b, _ => b
  | .both a b, x => ev a x && ev b x
  | .either a b, x => ev a x || ev b x
  | .neg a, x => !ev a x

def replace : PExpr → Nat → PExpr → PExpr
  | .var w, k, r => if w = k then r else .var w
  | .lit b, _, _ => .lit b
  | .both a b, k, r => .both (replace a k r) (replace b k r)
  | .either a b, k, r => .either (replace a k r) (replace b k r)
  | .neg a, k, r => .neg (replace a k r)

def pos : PExpr → Prop
  | .var _ | .lit _ => True
  | .both a b | .either a b => pos a ∧ pos b
  | .neg _ => False

def linear : PExpr → Prop
  | .var _ | .lit _ => True
  | .both a b | .either a b => linear a ∧ linear b ∧ Disjoint (support a) (support b)
  | .neg a => linear a

def nots : PExpr → Nat
  | .var _ | .lit _ => 0
  | .both a b | .either a b => nots a + nots b
  | .neg a => nots a + 1

def wireExpr (n w : Nat) : PExpr := if w < n then .var w else .lit false

def gateExpr (n : Nat) (g : Gate) : PExpr :=
  match g.op, g.inputs with
  | .and, [] => .lit true
  | .or, [] => .lit false
  | .and, [a] | .or, [a] => wireExpr n a
  | .and, a :: b :: _ => .both (wireExpr n a) (wireExpr n b)
  | .or, a :: b :: _ => .either (wireExpr n a) (wireExpr n b)
  | .not, [] => .lit true
  | .not, a :: _ => .neg (wireExpr n a)
  | _, _ => .lit false

def unroll (n : Nat) : List Gate → PExpr → PExpr
  | [], e => e
  | g :: gs, e => replace (unroll (n+1) gs e) n (gateExpr n g)

def outputExpr (n : Nat) (C : Circuit) : PExpr :=
  unroll n C.gates (wireExpr (n + C.size) C.output)

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def evalWith : PExpr → (Nat → Bool) → Bool
  | .var w, f => f w
  | .lit b, _ => b
  | .both a b, f => evalWith a f && evalWith b f
  | .either a b, f => evalWith a f || evalWith b f
  | .neg a, f => !evalWith a f

theorem ev_eq_evalWith (e : PExpr) (x : Finset Nat) :
    ev e x = evalWith e (fun w => decide (w ∈ x)) := by
  induction e <;> simp_all [ev, evalWith]

theorem evalWith_replace (e : PExpr) (k : Nat) (r : PExpr) (f : Nat → Bool) :
    evalWith (replace e k r) f =
      evalWith e (fun w => if w = k then evalWith r f else f w) := by
  induction e with
  | var w => by_cases h : w = k <;> simp [replace, evalWith, h]
  | _ => simp_all [replace, evalWith]

theorem bridge_getD_ge (xs : List Bool) (w : Nat) (h : xs.length ≤ w) :
    xs.getD w false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem evalWith_wireExpr (xs : List Bool) (w : Nat) :
    evalWith (wireExpr xs.length w) (fun t => xs.getD t false) = xs.getD w false := by
  by_cases h : w < xs.length
  · simp [wireExpr, evalWith, h]
  · simp [wireExpr, evalWith, h]

def bridgeStep (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map (fun t => xs.getD t false))]

theorem evalWith_gateExpr (xs : List Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hsize : g.inputs.length ≤ 2) :
    evalWith (gateExpr xs.length g) (fun t => xs.getD t false) =
      g.op.eval (g.inputs.map (fun t => xs.getD t false)) := by
  rcases g with ⟨o, ins⟩
  change o = .and ∨ o = .or ∨ o = .not at hop
  change ins.length ≤ 2 at hsize
  rcases ins with _ | ⟨a, ins⟩
  · rcases hop with rfl | rfl | rfl <;> rfl
  rcases ins with _ | ⟨b, tail⟩
  · rcases hop with rfl | rfl | rfl <;>
      simp only [gateExpr, evalWith, evalWith_wireExpr, GateOp.eval, List.map_cons, List.map_nil] <;> simp
  have ht : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hsize; omega)
  subst tail
  rcases hop with rfl | rfl | rfl <;>
    simp only [gateExpr, evalWith, evalWith_wireExpr, GateOp.eval, List.map_cons, List.map_nil] <;> simp

theorem bridge_snoc (xs : List Bool) (b : Bool) (w : Nat) :
    (xs ++ [b]).getD w false = if w = xs.length then b else xs.getD w false := by
  by_cases he : w = xs.length
  · subst w
    simp [List.getD_eq_getElem?_getD]
  · simp only [he, ↓reduceIte]
    by_cases h : w < xs.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · rw [bridge_getD_ge (xs ++ [b]) w (by simp; omega), bridge_getD_ge xs w (by omega)]

theorem evalWith_unroll (gs : List Gate) (xs : List Bool) (e : PExpr)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    evalWith (unroll xs.length gs e) (fun t => xs.getD t false) =
      evalWith e (fun t => (gs.foldl bridgeStep xs).getD t false) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have hg0 := hg g (by simp)
    have hrest : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or ∨ a.op = .not) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hg a (by simp [ha])
    have hlen : (bridgeStep xs g).length = xs.length + 1 := by simp [bridgeStep]
    have hfun : (fun w => if w = xs.length then evalWith (gateExpr xs.length g)
                    (fun t => xs.getD t false) else xs.getD w false) =
                (fun w => (bridgeStep xs g).getD w false) := by
      funext w
      rw [evalWith_gateExpr xs g hg0.1 hg0.2, bridgeStep, bridge_snoc]
    simp only [unroll, evalWith_replace, hfun, List.foldl_cons]
    rw [← hlen]
    exact ih (bridgeStep xs g) hrest

theorem bridge_fold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl bridgeStep xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [ih, bridgeStep, Nat.add_comm, Nat.add_left_comm]

theorem bridge_oneEach_lookup {n m : Nat} (i : Fin n) (j : Fin m) (w : Nat) :
    (oneEach i j).getD w false = true ↔ w = i.val ∨ w = n + j.val := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem outputExpr_oneEach {n m : Nat} (C : Circuit) (hC : FanInTwo C) (i : Fin n) (j : Fin m) :
    ev (outputExpr (n+m) C) {i.val, n+j.val} = C.eval (oneEach i j) := by
  let xs := oneEach i j
  have hlen : xs.length = n+m := by simp [xs, oneEach]
  have hfun : (fun w : Nat => decide (w ∈ ({i.val,n+j.val} : Finset Nat))) =
              (fun w : Nat => xs.getD w false) := by
    funext w
    apply Bool.eq_iff_iff.mpr
    change _ ↔ (oneEach i j).getD w false = true
    rw [bridge_oneEach_lookup i j w]
    simp
  have hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hm
    obtain ⟨ho, hs⟩ := hC g hm
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hs⟩
  rw [ev_eq_evalWith, hfun, outputExpr, ← hlen, evalWith_unroll C.gates xs _ hg]
  change evalWith (wireExpr (xs.length + C.gates.length) C.output) _ = _
  rw [← bridge_fold_len C.gates xs, evalWith_wireExpr]
  rfl

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

def atPair {n m : Nat} (i : Fin n) (j : Fin m) : Finset Nat := {i.val, n+j.val}

def supported (S : Finset Nat) (f : Finset Nat → Bool) : Prop :=
  ∀ x y, x ∩ S = y ∩ S → f x = f y

theorem omitted_eq {w t : Nat} (s : Finset Nat) (hw : w ∉ s) :
    ({w,t} : Finset Nat) ∩ s = {t} ∩ s := by
  ext i
  by_cases he : i = w <;> simp_all

theorem row_agreement {n m : Nat} {A : Fin n → Fin m → Bool} {S : Finset Nat}
    {f : Finset Nat → Bool} (hs : supported S f) (hf : ∀ i j, f (atPair i j) = A i j)
    (i k : Fin n) (h : i.val ∉ S) (hk : k.val ∉ S) (j : Fin m) :
    A i j = A k j := by
  rw [← hf, ← hf]
  apply hs
  exact (omitted_eq S h).trans (omitted_eq S hk).symm

theorem col_agreement {n m : Nat} {A : Fin n → Fin m → Bool} {S : Finset Nat}
    {f : Finset Nat → Bool} (hs : supported S f) (hf : ∀ i j, f (atPair i j) = A i j)
    (j k : Fin m) (h : n+j.val ∉ S) (hk : n+k.val ∉ S) (i : Fin n) :
    A i j = A i k := by
  rw [← hf, ← hf]
  apply hs
  simpa only [atPair, Finset.pair_comm i.val] using
    (omitted_eq (t := i.val) S h).trans (omitted_eq S hk).symm

theorem image_le_one_more {α β : Type} [DecidableEq α] [DecidableEq β] (I U : Finset α)
    (p : α → β) (h : ∀ i ∈ I, i ∉ U → ∀ k ∈ I, k ∉ U → p i = p k) :
    (I.image p).card ≤ U.card+1 := by
  classical
  by_cases hall : I ⊆ U
  · exact le_trans Finset.card_image_le (by have := Finset.card_le_card hall; omega)
  · obtain ⟨k,hk,hku⟩ := Finset.not_subset.mp hall
    have sub : I.image p ⊆ insert (p k) (U.image p) := by
      intro t ht
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      by_cases hu : i ∈ U
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hu)
      · exact Finset.mem_insert.mpr (Or.inl (h i hi hu k hk hku))
    have a := Finset.card_le_card sub
    have b := Finset.card_insert_le (p k) (U.image p)
    have c : (U.image p).card ≤ U.card := Finset.card_image_le
    omega

theorem profile_count {n m : Nat} (A : Fin n → Fin m → Bool) (I : Finset (Fin n))
    (J : Finset (Fin m)) (S : Finset Nat) (f : Finset Nat → Bool) (hs : supported S f)
    (hf : ∀ i j, f (atPair i j) = A i j) :
    let R := I.filter fun i => i.val ∈ S
    let T := J.filter fun j => n+j.val ∈ S
    let rp := fun i => J.filter (fun j => A i j = true)
    let cp := fun j => I.filter (fun i => A i j = true)
    R.card + T.card ≤ S.card ∧
      (I.image rp).card ≤ R.card+1 ∧ (J.image cp).card ≤ T.card+1 := by
  classical
  dsimp only
  let R := I.filter fun i => i.val ∈ S
  let T := J.filter fun j => n+j.val ∈ S
  let R' := R.image fun i => i.val
  let T' := T.image fun j => n+j.val
  have hr : R'.card = R.card := Finset.card_image_of_injective _ Fin.val_injective
  have ht : T'.card = T.card := Finset.card_image_of_injective _ (by
    intro a b hab
    apply Fin.ext
    exact Nat.add_left_cancel hab)
  have hd : Disjoint R' T' := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,ei⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,ej⟩ := Finset.mem_image.mp hy
    have := i.isLt
    omega
  have hu : R' ∪ T' ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hi).2
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hj).2
  refine ⟨?_,?_,?_⟩
  · have h := Finset.card_le_card hu
    rwa [Finset.card_union_of_disjoint hd, hr, ht] at h
  · apply image_le_one_more
    intro i hi hui k hk huk
    have ni : i.val ∉ S := fun h => hui (Finset.mem_filter.mpr ⟨hi,h⟩)
    have nk : k.val ∉ S := fun h => huk (Finset.mem_filter.mpr ⟨hk,h⟩)
    ext j
    simp only [Finset.mem_filter, row_agreement hs hf i k ni nk j]
  · apply image_le_one_more
    intro j hj huj k hk huk
    have nj : n+j.val ∉ S := fun h => huj (Finset.mem_filter.mpr ⟨hj,h⟩)
    have nk : n+k.val ∉ S := fun h => huk (Finset.mem_filter.mpr ⟨hk,h⟩)
    ext i
    simp only [Finset.mem_filter, col_agreement hs hf j k nj nk i]

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

def increasing (f : Finset Nat → Bool) : Prop :=
  ∀ x y, x ⊆ y → f x = true → f y = true

theorem mono_all_present {n m : Nat} (A : Fin n → Fin m → Bool) (I : Finset (Fin n))
    (J : Finset (Fin m)) (S : Finset Nat) (f : Finset Nat → Bool) (hs : supported S f)
    (hf : ∀ i j, f (atPair i j) = A i j) (hm : increasing f)
    (row : ∀ i ∈ I, (∃ j ∈ J, A i j = false) ∧ ∃ j ∈ J, A i j = true)
    (col : ∀ j ∈ J, (∃ i ∈ I, A i j = false) ∧ ∃ i ∈ I, A i j = true) :
    (∀ i ∈ I, i.val ∈ S) ∧ (∀ j ∈ J, n+j.val ∈ S) := by
  constructor
  · intro i hi
    by_contra h
    obtain ⟨j,hj,hij⟩ := (row i hi).2
    obtain ⟨k,_,hkj⟩ := (col j hj).1
    have he : f (atPair i j) = f {n+j.val} := hs _ _ (omitted_eq S h)
    have hyes : f {n+j.val} = true := he.symm.trans ((hf i j).trans hij)
    have hno : f (atPair k j) = true :=
      hm _ _ (by simp [atPair]) hyes
    rw [hf,hkj] at hno
    contradiction
  · intro j hj
    by_contra h
    obtain ⟨i,hi,hij⟩ := (col j hj).2
    obtain ⟨k,_,hik⟩ := (row i hi).1
    have he : f (atPair i j) = f {i.val} := by
      apply hs
      simpa only [atPair, Finset.pair_comm i.val] using omitted_eq (t := i.val) S h
    have hyes : f {i.val} = true := he.symm.trans ((hf i j).trans hij)
    have hno : f (atPair i k) = true := hm _ _ (by simp [atPair]) hyes
    rw [hf,hik] at hno
    contradiction

theorem floor_of_cases {n m : Nat} (A : Fin n → Fin m → Bool) (I : Finset (Fin n))
    (J : Finset (Fin m)) (S : Finset Nat) (f : Finset Nat → Bool) (s : Nat)
    (hs : supported S f) (hf : ∀ i j, f (atPair i j) = A i j)
    (row : ∀ i ∈ I, (∃ j ∈ J, A i j = false) ∧ ∃ j ∈ J, A i j = true)
    (col : ∀ j ∈ J, (∃ i ∈ I, A i j = false) ∧ ∃ i ∈ I, A i j = true)
    (cap : S.card ≤ s+1)
    (cases : increasing f ∨
      (S.card ≤ s ∧ ∀ i ∈ I, i.val ∉ S → ∀ j ∈ J, n+j.val ∈ S) ∨ S.card+1 ≤ s) :
    (I.image fun i => J.filter (fun j => A i j = true)).card +
      (J.image fun j => I.filter (fun i => A i j = true)).card ≤ s+1 := by
  classical
  let R := I.filter fun i => i.val ∈ S
  let T := J.filter fun j => n+j.val ∈ S
  let rp := fun i => J.filter (fun j => A i j = true)
  let cp := fun j => I.filter (fun i => A i j = true)
  change (I.image rp).card + (J.image cp).card ≤ s+1
  obtain ⟨hc,hr,hj⟩ := profile_count A I J S f hs hf
  change R.card + T.card ≤ S.card at hc
  change (I.image rp).card ≤ R.card+1 at hr
  change (J.image cp).card ≤ T.card+1 at hj
  have left (h : ∀ i ∈ I, i.val ∈ S) : (I.image rp).card ≤ R.card := by
    apply le_trans Finset.card_image_le
    exact Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨hi, h i hi⟩)
  have right (h : ∀ j ∈ J, n+j.val ∈ S) : (J.image cp).card ≤ T.card := by
    apply le_trans Finset.card_image_le
    exact Finset.card_le_card (fun j hj' => Finset.mem_filter.mpr ⟨hj', h j hj'⟩)
  rcases cases with hm | ⟨small,missing⟩ | slack
  · obtain ⟨presentL,presentR⟩ := mono_all_present A I J S f hs hf hm row col
    have l := left presentL
    have r := right presentR
    omega
  · by_cases hall : ∀ i ∈ I, i.val ∈ S
    · have l := left hall
      omega
    · push Not at hall
      obtain ⟨i,hi,notIn⟩ := hall
      have r := right (missing i hi notIn)
      omega
  · omega

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

theorem expr_agree (e : PExpr) (x y : Finset Nat)
    (h : ∀ w ∈ support e, w ∈ x ↔ w ∈ y) : ev e x = ev e y := by
  induction e with
  | var w => simpa [ev] using (propext (h w (by simp [support])))
  | lit => rfl
  | both a b ia ib =>
    simp only [ev, ia (fun w hw => h w (Finset.mem_union_left _ hw)),
      ib (fun w hw => h w (Finset.mem_union_right _ hw))]
  | either a b ia ib =>
    simp only [ev, ia (fun w hw => h w (Finset.mem_union_left _ hw)),
      ib (fun w hw => h w (Finset.mem_union_right _ hw))]
  | neg a ia => simp only [ev, ia h]

theorem expr_supported (e : PExpr) : supported (support e) (ev e) := by
  intro x y hx
  apply expr_agree
  intro w hw
  have hiff : w ∈ x ∩ support e ↔ w ∈ y ∩ support e := by rw [hx]
  simpa [hw] using hiff

theorem expr_pos_mono (e : PExpr) (h : pos e) : increasing (ev e) := by
  induction e with
  | var w =>
    intro x y hsub hx
    simp only [ev, decide_eq_true_eq] at hx ⊢
    exact hsub hx
  | lit =>
    intro x y _ hx
    exact hx
  | both a b ia ib =>
    intro x y hsub hx
    simp only [ev, Bool.and_eq_true] at hx ⊢
    exact ⟨ia h.1 x y hsub hx.1, ib h.2 x y hsub hx.2⟩
  | either a b ia ib =>
    intro x y hsub hx
    simp only [ev, Bool.or_eq_true] at hx ⊢
    exact hx.imp (ia h.1 x y hsub) (ib h.2 x y hsub)
  | neg => exact h.elim

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

open PEqualNP.CircuitLowerBounds

private theorem cone_distribute {p a b c d z : Prop} :
    (((p ∧ a) ∨ (c ∧ z)) ∨ ((p ∧ b) ∨ (d ∧ z))) ↔
    ((p ∧ (a ∨ b)) ∨ ((c ∨ d) ∧ z)) := by tauto

theorem cone_mem_replace (e r : PExpr) (k i : Nat) :
    i ∈ support (replace e k r) ↔
      (i ≠ k ∧ i ∈ support e) ∨ (k ∈ support e ∧ i ∈ support r) := by
  induction e with
  | var w =>
    by_cases h : w = k
    · subst w; simp [replace, support]
    · simp [replace, support, h, Ne.symm h]; rintro rfl; exact h
  | lit b => simp [replace, support]
  | neg e he => simpa [replace, support] using he
  | both a b ha hb =>
    simp only [replace, support, Finset.mem_union, ha, hb]; exact cone_distribute
  | either a b ha hb =>
    simp only [replace, support, Finset.mem_union, ha, hb]; exact cone_distribute

theorem cone_replace_miss (e r : PExpr) (k : Nat) (h : k ∉ support e) :
    replace e k r = e := by
  induction e with
  | var w => have hn : w ≠ k := by simpa [support, eq_comm] using h
             simp [replace, hn]
  | lit b => rfl
  | neg e ih => simp [replace, ih h]
  | both a b ha hb =>
    have hh := Finset.notMem_union.mp h
    simp [replace, ha hh.1, hb hh.2]
  | either a b ha hb =>
    have hh := Finset.notMem_union.mp h
    simp [replace, ha hh.1, hb hh.2]

theorem cone_support_hit {e r : PExpr} {k : Nat} (h : k ∈ support e) :
    support (replace e k r) = (support e).erase k ∪ support r := by
  ext i
  simp [cone_mem_replace, Finset.mem_erase, h]

theorem cone_pos_replace {e r : PExpr} {k : Nat} (he : pos e) (hr : pos r) :
    pos (replace e k r) := by
  induction e with
  | var w => by_cases h : w = k <;> simp [replace, h, pos, hr]
  | lit b => simp [replace, pos]
  | neg _ _ => exact False.elim he
  | both a b ha hb => exact ⟨ha he.1, hb he.2⟩
  | either a b ha hb => exact ⟨ha he.1, hb he.2⟩

theorem cone_zero_nots {e : PExpr} (he : pos e) : nots e = 0 := by
  induction e with
  | var w => rfl
  | lit b => rfl
  | neg e _ => exact False.elim he
  | both a b ha hb => simp [nots, ha he.1, hb he.2]
  | either a b ha hb => simp [nots, ha he.1, hb he.2]

private theorem cone_pair_disjoint {a b r : PExpr} {k : Nat}
    (hab : Disjoint (support a) (support b))
    (hd : Disjoint ((support a ∪ support b).erase k) (support r)) :
    Disjoint (support (replace a k r)) (support (replace b k r)) := by
  apply Finset.disjoint_left.mpr
  intro i ha hb
  rw [cone_mem_replace] at ha hb
  have H := Finset.disjoint_left.mp hab
  have D := Finset.disjoint_left.mp hd
  rcases ha with ⟨iak, ia⟩ | ⟨ka, ir⟩ <;> rcases hb with ⟨ibk, ib⟩ | ⟨kb, ir'⟩
  · exact H ia ib
  · exact D (Finset.mem_erase.mpr ⟨iak, Finset.mem_union_left _ ia⟩) ir'
  · exact D (Finset.mem_erase.mpr ⟨ibk, Finset.mem_union_right _ ib⟩) ir
  · exact H ka kb

theorem cone_linear_replace {e r : PExpr} {k : Nat} (he : linear e) (hr : linear r)
    (hd : Disjoint ((support e).erase k) (support r)) : linear (replace e k r) := by
  induction e with
  | var w => by_cases h : w = k <;> simp [replace, h, linear, hr]
  | lit b => trivial
  | neg a ha => exact ha he hd
  | both a b ha hb | either a b ha hb =>
    obtain ⟨la,lb,d⟩ := he
    exact ⟨ha la (hd.mono_left (Finset.erase_subset_erase _ Finset.subset_union_left)),
      hb lb (hd.mono_left (Finset.erase_subset_erase _ Finset.subset_union_right)),
      cone_pair_disjoint d hd⟩

theorem cone_nots_replace {e r : PExpr} {k : Nat} (he : linear e) :
    nots (replace e k r) = nots e + (if k ∈ support e then nots r else 0) := by
  induction e with
  | var w => by_cases h : w = k <;> simp [replace, h, Ne.symm, support, nots]
  | lit b => simp [replace, support, nots]
  | neg a ha =>
    by_cases h : k ∈ support a <;> simp [replace, nots, support, ha he, h, Nat.add_right_comm]
  | both a b ha hb | either a b ha hb =>
    obtain ⟨la,lb,d⟩ := he
    have hh := Finset.disjoint_left.mp d
    simp only [replace, nots, support, Finset.mem_union, ha la, hb lb]
    by_cases h1 : k ∈ support a <;> by_cases h2 : k ∈ support b <;> simp_all <;> omega

structure ConeBudget (e : PExpr) (s : Nat) : Prop where
  cap : (support e).card ≤ s+1
  full : (support e).card = s+1 → pos e ∧ linear e
  tight : (support e).card = s → pos e ∨ (linear e ∧ nots e = 1)

structure ConeGateShape (r : PExpr) : Prop where
  cap : (support r).card ≤ 2
  full : (support r).card = 2 → pos r ∧ linear r
  neg : ¬ pos r → (support r).card ≤ 1 ∧ linear r ∧ nots r = 1

theorem cone_budget_step {e r : PExpr} {k s : Nat}
    (he : ConeBudget e s) (hr : ConeGateShape r) : ConeBudget (replace e k r) (s+1) := by
  by_cases hk : k ∈ support e
  · have hs := cone_support_hit (r := r) hk
    have hcard : ((support e).erase k).card + 1 = (support e).card :=
      Finset.card_erase_add_one hk
    have hu := Finset.card_union_le ((support e).erase k) (support r)
    have hCap := he.cap
    have rCap := hr.cap
    have dis : (support (replace e k r)).card = ((support e).erase k).card + (support r).card →
        Disjoint ((support e).erase k) (support r) := by
      rw [hs]; exact Finset.card_union_eq_card_add_card.mp
    refine ⟨?_, ?_, ?_⟩
    · rw [hs]; omega
    · intro h
      have h' := h; rw [hs] at h'
      have eqe : (support e).card=s+1 := by omega
      have eqr : (support r).card=2 := by omega
      obtain ⟨pe,le⟩ := he.full eqe
      obtain ⟨pr,lr⟩ := hr.full eqr
      exact ⟨cone_pos_replace pe pr, cone_linear_replace le lr (dis (by omega))⟩
    · intro h
      have h' := h; rw [hs] at h'
      by_cases eqe : (support e).card = s+1
      · obtain ⟨pe,le⟩ := he.full eqe
        by_cases pr : pos r
        · exact Or.inl (cone_pos_replace pe pr)
        · obtain ⟨cr,lr,nr⟩ := hr.neg pr
          exact Or.inr ⟨cone_linear_replace le lr (dis (by omega)), by
            rw [cone_nots_replace le, ite_eq_left hk, cone_zero_nots pe, nr]⟩
      · have es : (support e).card=s := by omega
        obtain ⟨pr,lr⟩ := hr.full (by omega)
        rcases he.tight es with pe | ⟨le,ne⟩
        · exact Or.inl (cone_pos_replace pe pr)
        · exact Or.inr ⟨cone_linear_replace le lr (dis (by omega)), by
            rw [cone_nots_replace le, ite_eq_left hk, ne, cone_zero_nots pr]⟩
  · rw [cone_replace_miss e r k hk]
    have hc := he.cap
    exact ⟨by omega, by omega, fun h => Or.inl (he.full h).1⟩

private def ConeAtom (e : PExpr) : Prop := (support e).card ≤ 1 ∧ pos e ∧ linear e

private theorem cone_lit_atom (b : Bool) : ConeAtom (.lit b) := by
  simp [ConeAtom, support, pos, linear]

private theorem cone_wire_atom (n i : Nat) : ConeAtom (wireExpr n i) := by
  by_cases h : i < n <;> simp [ConeAtom, wireExpr, h, support, pos, linear]

private theorem cone_atom_shape {e : PExpr} (h : ConeAtom e) : ConeGateShape e :=
  ⟨by have := h.1; omega, fun _ => h.2, fun bad => False.elim (bad h.2.1)⟩

private theorem cone_neg_shape {e : PExpr} (h : ConeAtom e) : ConeGateShape (.neg e) := by
  have hc := h.1
  refine ⟨by change (support e).card ≤ 2; omega, ?_, ?_⟩
  · intro hbad; change (support e).card = 2 at hbad; omega
  · intro _; exact ⟨hc, h.2.2, by simp [nots, cone_zero_nots h.2.1]⟩

private theorem cone_atoms_union {a b : PExpr} (ha : ConeAtom a) (hb : ConeAtom b) :
    (support a ∪ support b).card ≤ 2 ∧
    ((support a ∪ support b).card = 2 → Disjoint (support a) (support b)) := by
  have h := Finset.card_union_le (support a) (support b)
  have a' := ha.1
  have b' := hb.1
  exact ⟨by omega, fun eq => Finset.card_union_eq_card_add_card.mp (by omega)⟩

private theorem cone_both_shape {a b : PExpr} (ha : ConeAtom a) (hb : ConeAtom b) :
    ConeGateShape (.both a b) :=
  ⟨(cone_atoms_union ha hb).1,
    fun eq => ⟨⟨ha.2.1,hb.2.1⟩, ha.2.2, hb.2.2, (cone_atoms_union ha hb).2 eq⟩,
    fun bad => False.elim (bad ⟨ha.2.1,hb.2.1⟩)⟩

private theorem cone_either_shape {a b : PExpr} (ha : ConeAtom a) (hb : ConeAtom b) :
    ConeGateShape (.either a b) :=
  ⟨(cone_atoms_union ha hb).1,
    fun eq => ⟨⟨ha.2.1,hb.2.1⟩, ha.2.2, hb.2.2, (cone_atoms_union ha hb).2 eq⟩,
    fun bad => False.elim (bad ⟨ha.2.1,hb.2.1⟩)⟩

private theorem cone_gate_shape (n : Nat) (g : Gate) : ConeGateShape (gateExpr n g) := by
  rcases g with ⟨op, xs⟩
  cases op <;> rcases xs with _ | ⟨a, _ | ⟨b,t⟩⟩ <;>
    first
    | exact cone_atom_shape (cone_lit_atom _)
    | exact cone_atom_shape (cone_wire_atom _ _)
    | exact cone_neg_shape (cone_wire_atom _ _)
    | exact cone_both_shape (cone_wire_atom _ _) (cone_wire_atom _ _)
    | exact cone_either_shape (cone_wire_atom _ _) (cone_wire_atom _ _)

private theorem cone_unroll_budget (n : Nat) (gs : List Gate) (e : PExpr) (t : Nat)
    (he : ConeBudget e t) : ConeBudget (unroll n gs e) (t + gs.length) := by
  induction gs generalizing n with
  | nil => simpa [unroll] using he
  | cons g gs ih =>
    have hh := cone_budget_step (k := n) (ih (n+1)) (cone_gate_shape n g)
    simpa [unroll, Nat.add_assoc] using hh

theorem cone_output_budget (n : Nat) (C : Circuit) : ConeBudget (outputExpr n C) C.size := by
  let e := wireExpr (n+C.size) C.output
  have h : ConeAtom e := cone_wire_atom _ _
  have he : ConeBudget e 0 := ⟨h.1, fun _ => h.2, fun _ => Or.inl h.2.1⟩
  simpa [outputExpr, e, Circuit.size] using cone_unroll_budget n C.gates e 0 he

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

theorem separated_impossible {n m : Nat} (A : Fin n → Fin m → Bool)
    (I : Finset (Fin n)) (J : Finset (Fin m))
    (mixedRow : ∀ i ∈ I, (∃ j ∈ J, A i j = false) ∧ ∃ j ∈ J, A i j = true)
    (mixedCol : ∀ j ∈ J, (∃ i ∈ I, A i j = false) ∧ ∃ i ∈ I, A i j = true)
    (er ir : Fin n → Finset Nat) (ec ic : Fin m → Finset Nat)
    (splitRow : ∀ i ∈ I, er i = ∅ ∨ ir i = ∅)
    (splitCol : ∀ j ∈ J, ec j = ∅ ∨ ic j = ∅)
    (i₀ : Fin n) (hi₀ : i₀ ∈ I) (he₀ : er i₀ = ∅) (hr₀ : ir i₀ = ∅)
    (j₀ : Fin m) (hj₀ : j₀ ∈ J) (hf₀ : ec j₀ = ∅) (hc₀ : ic j₀ = ∅)
    (P : Finset Nat → Bool → Bool) (H : Finset Nat → Bool)
    (hP : ∀ {s t : Finset Nat} {b d : Bool}, s ⊆ t → (b = true → d = true) →
      P s b = true → P t d = true)
    (hH : ∀ {s t : Finset Nat}, s ⊆ t → H s = true → H t = true)
    (eval : ∀ i ∈ I, ∀ j ∈ J, A i j = P (er i ∪ ec j) (!(H (ir i ∪ ic j)))) : False := by
  have colLow (j : Fin m) (hj : j ∈ J) : P (ec j) false = false := by
    cases h : P (ec j) false with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hzero⟩ := (mixedCol j hj).1
      have hyes : A i j = true := (eval i hi j hj).trans (hP Finset.subset_union_right (by simp) h)
      simp [hzero] at hyes
  have innerLow (i : Fin n) (hi : i ∈ I) (he : er i = ∅) : H (ir i) = false := by
    cases h : H (ir i) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hyes⟩ := (mixedRow i hi).2
      have hhigh : H (ir i ∪ ic j) = true := hH Finset.subset_union_left h
      rw [eval i hi j hj] at hyes
      simp [he, hhigh, colLow j hj] at hyes
  have hbase : H ∅ = false := by simpa [hr₀] using innerLow i₀ hi₀ he₀
  have innerRow (i : Fin n) (hi : i ∈ I) : H (ir i) = false := by
    rcases splitRow i hi with he | hr
    · exact innerLow i hi he
    · simpa [hr] using hbase
  have outerBase : P ∅ true = false := by
    cases h : P ∅ true with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hzero⟩ := (mixedCol j₀ hj₀).1
      have hyes : P (er i) true = true := hP (Finset.empty_subset _) id h
      rw [eval i hi j₀ hj₀] at hzero
      simp [hf₀, hc₀, innerRow i hi, hyes] at hzero
  obtain ⟨j, hj, hyes⟩ := (mixedRow i₀ hi₀).2
  rw [eval i₀ hi₀ j hj] at hyes
  simp [he₀, hr₀] at hyes
  have hOuter : ec j ≠ ∅ := by
    intro he
    rw [he] at hyes
    have h := hP (Finset.Subset.refl _) (by simp : _ → true = true) hyes
    simp [outerBase] at h
  have hInner : ic j = ∅ := (splitCol j hj).resolve_left hOuter
  simp [hInner, hbase] at hyes
  obtain ⟨i, hi, hzero⟩ := (mixedCol j hj).1
  have hfull : P (er i ∪ ec j) true = true := hP Finset.subset_union_right id hyes
  rw [eval i hi j hj] at hzero
  simp [hInner, innerRow i hi, hfull] at hzero

end PEqualNP.Outside.L_meta_29777

namespace PEqualNP.Outside.L_meta_29777

structure NegFactor (e : PExpr) where
  outer : Finset Nat
  inner : Finset Nat
  cover : outer ∪ inner = support e
  separate : Disjoint outer inner
  P : Finset Nat → Bool → Bool
  H : Finset Nat → Bool
  upP : ∀ {x y : Finset Nat} {b d : Bool}, x ⊆ y → (b = true → d = true) → P x b = true → P y d = true
  upH : increasing H
  depP : ∀ b, supported outer (fun x => P x b)
  depH : supported inner H
  eqn : ∀ x, ev e x = P x (!(H x))

private theorem pos_of_no_neg (e : PExpr) (h : nots e = 0) : pos e := by
  induction e with
  | var | lit => trivial
  | both a b ia ib | either a b ia ib =>
    change nots a + nots b = 0 at h
    exact ⟨ia (by omega), ib (by omega)⟩
  | neg a ia => simp [nots] at h

private theorem restrict_sub {x y s t : Finset Nat} (h : s ⊆ t) (he : x ∩ t = y ∩ t) : x ∩ s = y ∩ s := by
  ext w
  by_cases hw : w ∈ s
  · have hh : w ∈ x ∩ t ↔ w ∈ y ∩ t := by rw [he]
    simpa [hw, h hw] using hh
  · simp [hw]

private def OpUp (op : Bool → Bool → Bool) := ∀ {a b c d : Bool}, (a = true → c = true) →
  (b = true → d = true) → op a b = true → op c d = true

private theorem and_up : OpUp (· && ·) := by
  intro a b c d ha hb h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨ha h.1, hb h.2⟩

private theorem or_up : OpUp (· || ·) := by
  intro a b c d ha hb h
  simp only [Bool.or_eq_true] at h ⊢
  exact h.imp ha hb

private theorem attach_factor {a b c : PExpr} (op : Bool → Bool → Bool) (hop : OpUp op)
    (hc : support c = support a ∪ support b) (hc' : ∀ x, ev c x = op (ev a x) (ev b x))
    (hd : Disjoint (support a) (support b)) (hb : pos b) (F : NegFactor a) : Nonempty (NegFactor c) := by
  have hin : F.inner ⊆ support a := by rw [← F.cover]; exact Finset.subset_union_right
  refine ⟨{ outer := F.outer ∪ support b, inner := F.inner, P := fun x d => op (F.P x d) (ev b x),
            H := F.H, cover := ?_, separate := ?_, upP := ?_, upH := F.upH,
            depP := ?_, depH := F.depH, eqn := ?_ }⟩
  · rw [hc, ← F.cover]; ac_rfl
  · exact Finset.disjoint_union_left.mpr ⟨F.separate, hd.symm.mono_right hin⟩
  · intro x y v w hxy hvw he
    exact hop (F.upP hxy hvw) (expr_pos_mono b hb x y hxy) he
  · intro d x y hxy
    exact congrArg₂ op (F.depP d x y (restrict_sub Finset.subset_union_left hxy))
      (expr_supported b x y (restrict_sub Finset.subset_union_right hxy))
  · intro x; rw [hc', F.eqn]

theorem expr_neg_factor (e : PExpr) (hl : linear e) (hn : nots e = 1) : Nonempty (NegFactor e) := by
  induction e with
  | var | lit => simp [nots] at hn
  | neg a ia =>
    have hpos : pos a := pos_of_no_neg a (by change nots a + 1 = 1 at hn; omega)
    exact ⟨{ outer := ∅, inner := support a, cover := by simp [support], separate := by simp,
             P := fun _ b => b, H := ev a, upP := fun _ h => h, upH := expr_pos_mono a hpos,
             depP := fun _ _ _ _ => rfl, depH := expr_supported a, eqn := fun _ => rfl }⟩
  | both a b ia ib =>
    change nots a + nots b = 1 at hn
    rcases hl with ⟨hla, hlb, hd⟩
    by_cases ha : nots a = 1
    · obtain ⟨F⟩ := ia hla ha
      exact attach_factor _ and_up rfl (fun _ => rfl) hd (pos_of_no_neg b (by omega)) F
    · obtain ⟨F⟩ := ib hlb (by omega)
      exact attach_factor _ and_up (by simp [support, Finset.union_comm])
        (fun _ => Bool.and_comm ..) hd.symm (pos_of_no_neg a (by omega)) F
  | either a b ia ib =>
    change nots a + nots b = 1 at hn
    rcases hl with ⟨hla, hlb, hd⟩
    by_cases ha : nots a = 1
    · obtain ⟨F⟩ := ia hla ha
      exact attach_factor _ or_up rfl (fun _ => rfl) hd (pos_of_no_neg b (by omega)) F
    · obtain ⟨F⟩ := ib hlb (by omega)
      exact attach_factor _ or_up (by simp [support, Finset.union_comm])
        (fun _ => Bool.or_comm ..) hd.symm (pos_of_no_neg a (by omega)) F

theorem missing_pair_one_neg {n m : Nat} (A : Fin n → Fin m → Bool)
    (I : Finset (Fin n)) (J : Finset (Fin m))
    (mixedRow : ∀ i ∈ I, (∃ j ∈ J, A i j = false) ∧ ∃ j ∈ J, A i j = true)
    (mixedCol : ∀ j ∈ J, (∃ i ∈ I, A i j = false) ∧ ∃ i ∈ I, A i j = true)
    (e : PExpr) (hl : linear e) (hn : nots e = 1) (he : ∀ i j, ev e (atPair i j) = A i j)
    (i₀ : Fin n) (hi₀ : i₀ ∈ I) (hr : i₀.val ∉ support e)
    (j₀ : Fin m) (hj₀ : j₀ ∈ J) (hc : n + j₀.val ∉ support e) : False := by
  obtain ⟨F⟩ := expr_neg_factor e hl hn
  let part (s : Finset Nat) (w : Nat) := {w} ∩ s
  have empty {s : Finset Nat} {w : Nat} (hw : w ∉ s) : part s w = ∅ :=
    Finset.singleton_inter_of_notMem hw
  have split (w : Nat) : part F.outer w = ∅ ∨ part F.inner w = ∅ := by
    by_cases h : w ∈ F.outer
    · exact Or.inr (empty (Finset.disjoint_left.mp F.separate h))
    · exact Or.inl (empty h)
  have omissions (w : Nat) (hw : w ∉ support e) : part F.outer w = ∅ ∧ part F.inner w = ∅ := by
    rw [← F.cover, Finset.mem_union] at hw
    exact ⟨empty (fun h => hw (Or.inl h)), empty (fun h => hw (Or.inr h))⟩
  obtain ⟨ero, iro⟩ := omissions _ hr
  obtain ⟨eco, ico⟩ := omissions _ hc
  refine separated_impossible A I J mixedRow mixedCol (fun i => part F.outer i.val) (fun i => part F.inner i.val)
    (fun j => part F.outer (n+j.val)) (fun j => part F.inner (n+j.val)) (fun i _ => split _) (fun j _ => split _)
    i₀ hi₀ ero iro j₀ hj₀ eco ico F.P F.H F.upP (fun {s t} => F.upH s t) ?_
  intro i _ j _
  have pieces (s : Finset Nat) : atPair i j ∩ s = part s i.val ∪ part s (n+j.val) := by
    ext w
    simp only [atPair, part, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, or_and_right]
  have projectH : F.H (atPair i j) = F.H (part F.inner i.val ∪ part F.inner (n+j.val)) := by
    apply F.depH
    rw [← pieces]; simp
  rw [← he, F.eqn, projectH]
  apply F.depP
  rw [← pieces]; simp

end PEqualNP.Outside.L_meta_29777

open PEqualNP.Outside.L_meta_29777

theorem PEqualNP.Outside.L_meta_29777 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool) (I : Finset (Fin n)) (J : Finset (Fin m)),
  I.Nonempty → J.Nonempty →
  (∀ i ∈ I, (∃ j ∈ J, A i j = false) ∧ ∃ j ∈ J, A i j = true) →
  (∀ j ∈ J, (∃ i ∈ I, A i j = false) ∧ ∃ i ∈ I, A i j = true) →
  let rows := I.image (fun i => J.filter (fun j => A i j = true))
  let cols := J.image (fun j => I.filter (fun i => A i j = true))
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → rows.card + cols.card ≤ C.size + 1) := by
  intro n m A I J _ _ mixRows mixCols
  dsimp only
  intro C hb rep
  let e := outputExpr (n+m) C
  have eqs (i : Fin n) (j : Fin m) : ev e (atPair i j) = A i j :=
    (outputExpr_oneEach C hb i j).trans (rep i j)
  have b : ConeBudget e C.size := cone_output_budget (n+m) C
  apply floor_of_cases A I J (support e) (ev e) C.size (expr_supported e) eqs mixRows mixCols b.cap
  by_cases hp : pos e
  · exact Or.inl (expr_pos_mono e hp)
  have cap := b.cap
  have hfull : (support e).card ≠ C.size+1 := fun he => hp (b.full he).1
  have small : (support e).card ≤ C.size := by omega
  by_cases heq : (support e).card = C.size
  · obtain ⟨hl,hn⟩ := (b.tight heq).resolve_left hp
    refine Or.inr (Or.inl ⟨small, ?_⟩)
    intro i hi hmi j hj
    by_contra hmj
    exact missing_pair_one_neg A I J mixRows mixCols e hl hn eqs i hi hmi j hj hmj
  · exact Or.inr (Or.inr (by omega))
