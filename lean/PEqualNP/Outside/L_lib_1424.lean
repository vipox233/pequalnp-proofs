import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1424_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket (notCount)

noncomputable def conj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d && g d
noncomputable def disj {α : Type*} (f g : α → Bool) : α → Bool := fun d => f d || g d
noncomputable def inv {α : Type*} (f : α → Bool) : α → Bool := fun d => !(f d)

def WVal {α : Type*} (x : α → List Bool) (gs : List Gate) (p : Nat) : α → Bool :=
  fun d => ((Circuit.mk gs 0).wires (x d)).getD p false

noncomputable def Built {α : Type*} (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool)) : Prop :=
  (∀ d, (x d).length = N) ∧ ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack N ⟨gs,0⟩ ∧
    gs.length - notCount ⟨gs,0⟩ ≤ p ∧ notCount ⟨gs,0⟩ ≤ b ∧
    ∀ f ∈ S, ∃ i < N+gs.length, WVal x gs i = f

-- Wire extension arguments adapted from b81440944eeb15a06b92ee0d64d15d33c12dfab6, lean/PEqualNP/Outside/L_lib_1341.lean.
private theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

private theorem old {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) {i} (hi : i < N+gs.length) :
    WVal x (gs++[g]) i = WVal x gs i := by
  funext d
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD i false = _
  exact List.getD_append _ _ _ _ (by omega)

private theorem fresh {α : Type*} (x : α → List Bool) {N : Nat} (hlen : ∀ d, (x d).length=N)
    (gs : List Gate) (g : Gate) (d : α) :
    WVal x (gs++[g]) (N+gs.length) d = g.op.eval (g.inputs.map fun i => WVal x gs i d) := by
  have len := wirelen gs (x d)
  rw [hlen] at len
  simp only [WVal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (x d)) ++ [_]).getD (N+gs.length) false = _
  rw [← len, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private theorem extendBack {N : Nat} (gs : List Gate) (g : Gate) (h : ReadsBack N ⟨gs,0⟩)
    (ok : ∀ i ∈ g.inputs, i < N+gs.length) : ReadsBack N ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

section Compiler
variable {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}

theorem Built.start (hlen : ∀ d, (x d).length = N) :
    Built x N 0 0 {f | ∃ i < N, f = fun d => (x d).getD i false} := by
  refine ⟨hlen, [], by simp [FanInTwo], by simp [ReadsBack], by simp, by simp [notCount], ?_⟩
  rintro f ⟨i, hi, rfl⟩
  exact ⟨i, by simpa using hi, rfl⟩

theorem Built.relax {P B : Nat} {T : Set (α → Bool)} (H : Built x N p b S)
    (hp : p ≤ P) (hb : b ≤ B) (hst : T ⊆ S) : Built x N P B T := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  exact ⟨hlen, gs, fan, back, pc.trans hp, nc.trans hb, fun u hu => sig u (hst hu)⟩

private theorem Built.push (H : Built x N p b S) (op : GateOp) (arity : Nat)
    (allowed : op = .and ∨ op = .or ∨ op = .not) (ha : arity ≤ 2)
    (fs : List (α → Bool)) (hfs : fs.length = arity) (hf : ∀ f ∈ fs, f ∈ S) :
    Built x N (p + if op = .not then 0 else 1) (b + if op = .not then 1 else 0)
      (insert (fun d => op.eval (fs.map fun f => f d)) S) := by
  obtain ⟨hlen, gs, fan, back, pc, nc, sig⟩ := H
  have choose (f : α → Bool) (h : f ∈ fs) := sig f (hf f h)
  let is := fs.attach.map (fun f => (choose f.val f.property).choose)
  let g : Gate := ⟨op, is⟩
  have hcount : notCount ⟨gs++[g],0⟩ = notCount ⟨gs,0⟩ + (if op = .not then 1 else 0) := by
    by_cases h : op = .not <;> simp [notCount, List.filter_append, g, h]
  have hnc : notCount ⟨gs,0⟩ ≤ gs.length := List.length_filter_le _ _
  refine ⟨hlen, gs++[g], ?_, ?_, ?_, by rw [hcount]; exact Nat.add_le_add_right nc _, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact fan j hj
    · obtain rfl := List.mem_singleton.mp hj
      exact ⟨allowed, by simpa [g, is, hfs] using ha⟩
  · apply extendBack _ _ back
    intro i hi
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hi
    exact (choose f.val f.property).choose_spec.1
  · rw [hcount]
    simp only [List.length_append, List.length_singleton]
    split <;> omega
  · intro f hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · refine ⟨N+gs.length, by simp, ?_⟩
      funext d
      rw [fresh _ hlen]
      congr 1
      change is.map (fun i => WVal x gs i d) = _
      simp only [is, List.map_map]
      calc
        _ = fs.attach.map (fun f => f.val d) := by
          apply List.map_congr_left
          intro f _
          exact congrFun (choose f.val f.property).choose_spec.2 d
        _ = _ := List.attach_map_val (f := fun f : α → Bool => f d)
    · obtain ⟨i, hi, he⟩ := sig f hm
      exact ⟨i, by simp; omega, (old x hlen gs g hi).trans he⟩

theorem Built.andGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (conj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d && g d) S)
  simpa [GateOp.eval] using H.push .and 2 (Or.inl rfl) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.orGate {f g : α → Bool} (H : Built x N p b S) (hf : f ∈ S) (hg : g ∈ S) :
    Built x N (p+1) b (insert (disj f g) S) := by
  change Built x N (p+1) b (insert (fun d => f d || g d) S)
  simpa [GateOp.eval] using H.push .or 2 (Or.inr (Or.inl rfl)) (by decide) [f,g] rfl (by simp [hf,hg])

theorem Built.notGate {f : α → Bool} (H : Built x N p b S) (hf : f ∈ S) :
    Built x N p (b+1) (insert (inv f) S) := by
  change Built x N p (b+1) (insert (fun d => !f d) S)
  simpa [GateOp.eval] using H.push .not 1 (Or.inr (Or.inr rfl)) (by decide) [f] rfl (by simpa)

theorem boolOfIff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  cases hP : decide P <;> cases hQ : decide Q <;> simp_all

-- Finite batches and folds adapted from b81440944eeb15a06b92ee0d64d15d33c12dfab6, lean/PEqualNP/Outside/L_lib_1341.lean.
noncomputable def Grow (x : α → List Bool) (N p b : Nat) (S : Set (α → Bool))
    (c : Nat) (f : α → Bool) := ∃ T, Built x N (p+c) b T ∧ S ⊆ T ∧ f ∈ T

theorem batch {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (c : Nat) (H : Built x N p b S)
    (make : ∀ {P T}, Built x N P b T → S ⊆ T → ∀ a ∈ s, Grow x N P b T c (F a)) :
    ∃ T, Built x N (p+s.card*c) b T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fr ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fr,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type*} (s : Finset ι) (F : ι → α → Bool) (H : Built x N p b S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x N p b S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

end Compiler


-- Markov grade adapted from b81440944eeb15a06b92ee0d64d15d33c12dfab6, lean/PEqualNP/Outside/L_lib_1356.lean.
private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not
private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1], ?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD, ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none noneX, List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases g.inputs with
  | nil => simp
  | cons i _ => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i, here, rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.any_eq_true] at on ⊢
  obtain ⟨v, hm, active⟩ := on
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact ⟨_, List.mem_map.mpr ⟨i, here, rfl⟩, (bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1], if inverting g then 2 * s.2 + (firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance, neg, ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance, neg] using strict
    exact ⟨increase.le, fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega, ?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit, op, GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gs : List Gate) : ℕ := (gs.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting, h]

private theorem run_consistent (gs : List Gate) (allowed : ∀ g ∈ gs, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gs.foldl advance s) (gs.foldl advance t) := by
  induction gs generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gs : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2 ^ d) :
    (gs.foldl advance s).2 < 2 ^ (d + negCount gs) := by
  induction gs generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2 ^ (d + 1) := by
        simp only [advance, neg, ite_true, Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d + 1) raises
      simpa [negCount, neg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2 ^ d := by simpa [advance, neg] using bound
      simpa [negCount, neg] using ih (advance s g) d same

private theorem run_wires (gs : List Gate) (s : List Bool × ℕ) :
    (gs.foldl advance s).1 = gs.foldl gateStep s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private def grade (C : Circuit) (x : List Bool) : ℕ := (C.gates.foldl advance (x, 0)).2

private theorem grade_bound (C : Circuit) (x : List Bool) : grade C x < 2 ^ (notCount C) := by
  simpa [grade, negCount_spec] using run_bounded C.gates (x, 0) 0 (by change 0 < (1 : ℕ); decide)
private theorem grade_order {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i, (C.wires x).getD i false ≤ (C.wires y).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (x, 0) (y, 0) := ⟨le_rfl, fun _ => xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1, ?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires, run_wires] at order
  exact order


noncomputable def bits {r : Nat} (X : Finset (Fin r)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun j : Fin r => decide (j ∈ X))

noncomputable def labelBit {m : Nat} (i j : Fin m) : Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  decide (i=j)

def Near {r : Nat} (a f : Nat) (C Y : Finset (Fin r)) : Prop :=
  (C \ Y).card ≤ a ∧ (Y \ C).card ≤ f

def Label {r m : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (Y : Finset (Fin r)) (i : Fin m) : Prop :=
  ∃ C : Finset (Fin r), (Finset.univ \ C) ⊆ Z i ∧ C ⊆ O i ∧ Near (a i) (f i) C Y

def Valid (n : Nat) (D : Circuit) : Prop :=
  FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size

noncomputable def Possible {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) : Prop :=
  ∃ (D : Circuit) (out : Fin m → Nat), Valid r D ∧
    (∀ j, out j < r+2+D.size) ∧ notCount D ≤ b ∧
    ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = labelBit i j

def Adj {m l : Nat} (w : Fin l → Fin m) : Prop :=
  ∀ i j : Fin l, i.val + 1 = j.val → w i ≠ w j

def WordTrace {r m l : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r))
    (w : Fin l → Fin m) : Prop :=
  ∃ Y : Fin l → Finset (Fin r), Monotone Y ∧ (∀ i, Y i ⊆ T) ∧ ∀ i, lab (Y i) (w i)

def Trace {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (l : Nat) : Prop :=
  ∃ w : Fin l → Fin m, Adj w ∧ WordTrace lab T w

def Bucket {r m : Nat} (lab : Finset (Fin r) → Fin m → Prop) (T : Finset (Fin r)) (k : Nat)
    (j : Fin m) : Prop :=
  ∃ w : Fin (k+1) → Fin m, Adj w ∧ WordTrace lab T w ∧ w (Fin.last k) = j

private theorem bits_getD {r : Nat} (Y : Finset (Fin r)) (j : Fin r) :
    (bits Y).getD j.val false = decide (j ∈ Y) := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  first | rfl | exact Bool.eq_iff_iff.mpr (by simp)

private theorem bits_order {r : Nat} {Y T : Finset (Fin r)} (h : Y ⊆ T) :
    bitOrder (bits Y ++ [false,true]) (bits T ++ [false,true]) := by
  refine ⟨by simp [bits], fun q => ?_⟩
  by_cases hq : q < r
  · rw [List.getD_append _ _ _ _ (by simpa [bits] using hq),
      List.getD_append _ _ _ _ (by simpa [bits] using hq)]
    change (bits Y).getD (⟨q,hq⟩ : Fin r).val false ≤ (bits T).getD (⟨q,hq⟩ : Fin r).val false
    rw [bits_getD, bits_getD, bool_order]
    simpa using (fun hm : (⟨q,hq⟩ : Fin r) ∈ Y => h hm)
  · rw [List.getD_append_right _ _ _ _ (by simpa [bits] using Nat.le_of_not_gt hq),
      List.getD_append_right _ _ _ _ (by simpa [bits] using Nat.le_of_not_gt hq)]
    simp [bits]

private theorem index_le_of_steps {l : Nat} (v : Fin l → Nat)
    (step : ∀ i j : Fin l, i.val + 1 = j.val → v i < v j) (i : Fin l) : i.val ≤ v i := by
  have aux (j : Nat) : ∀ h : j < l, j ≤ v ⟨j,h⟩ := by
    induction j with
    | zero => simp
    | succ j ih =>
      intro h
      have hj : j < l := by omega
      have sv := step ⟨j,hj⟩ ⟨j+1,h⟩ rfl
      have iv := ih hj
      change v ⟨j,hj⟩ < v ⟨j+1,h⟩ at sv
      omega
  exact aux i.val i.isLt

private theorem possible_no_trace {r m b : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    (h : Possible b lab) : ¬ Trace lab Finset.univ (min (2^b) (r+1)+1) := by
  obtain ⟨D,out,valid,_,budget,fit⟩ := h
  rintro ⟨w,adj,Y,mono,_,ok⟩
  let l := min (2^b) (r+1)+1
  have last : l-1 < l := by dsimp [l]; omega
  let lastI : Fin l := ⟨l-1,last⟩
  have step (i j : Fin l) (hj : i.val+1=j.val) :
      grade D (bits (Y i) ++ [false,true]) < grade D (bits (Y j) ++ [false,true]) := by
    have sub := mono (show i ≤ j by exact Fin.le_iff_val_le_val.mpr (by omega))
    have ord := grade_order valid.1 (bits_order sub)
    apply lt_of_le_of_ne ord.1
    intro eq
    have hn := adj i j hj
    have bad := ord.2 eq (out (w i))
    rw [fit _ _ (ok i) _, fit _ _ (ok j) _] at bad
    simp [labelBit, Ne.symm hn] at bad
    exact (by decide : ¬((true : Bool) ≤ false)) bad
  have hpow := index_le_of_steps (fun i => grade D (bits (Y i) ++ [false,true])) step lastI
  have hb := (grade_bound D (bits (Y lastI) ++ [false,true])).trans_le (Nat.pow_le_pow_right (by decide) budget)
  have szstep (i j : Fin l) (hj : i.val+1=j.val) : (Y i).card < (Y j).card := by
    apply Finset.card_lt_card
    have sub := mono (show i ≤ j by exact Fin.le_iff_val_le_val.mpr (by omega))
    apply lt_of_le_of_ne sub
    intro eq
    have hs := step i j hj
    rw [eq] at hs
    exact (Nat.lt_irrefl _ hs)
  have hsz := index_le_of_steps (fun i => (Y i).card) szstep lastI
  have hcard : (Y lastI).card ≤ r := by
    simpa using (Y lastI).card_le_univ
  change min (2^b) (r+1) ≤ _ at hpow hsz
  omega

private theorem trace_mono {r m l : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T U : Finset (Fin r)} (sub : T ⊆ U) : Trace lab T l → Trace lab U l := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  exact ⟨w,adj,Y,mono,fun i => (top i).trans sub,ok⟩

private theorem trace_prefix {r m i j : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {T : Finset (Fin r)} (le : i ≤ j) : Trace lab T j → Trace lab T i := by
  rintro ⟨w,adj,Y,mono,top,ok⟩
  refine ⟨w ∘ Fin.castLE le, fun a b h => adj _ _ h,
    Y ∘ Fin.castLE le, fun a b h => mono h, fun a => top _, fun a => ok _⟩

private theorem trace_one {r m : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i : Fin m} (h : lab X i) : Trace lab X 1 := by
  refine ⟨fun _ => i, fun j k adj => ?_, fun _ => X, fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ => h⟩
  have hj := j.isLt
  have hk := k.isLt
  omega

private theorem trace_extend {r m k : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (diff : j ≠ i) (hi : lab X i) (h : Bucket lab X k j) :
    Trace lab X (k+2) := by
  obtain ⟨w,adj,⟨Y,mono,top,ok⟩,last⟩ := h
  let w' : Fin (k+2) → Fin m := Fin.lastCases i w
  let Y' : Fin (k+2) → Finset (Fin r) := Fin.lastCases X Y
  refine ⟨w', ?_, Y', ?_, ?_, ?_⟩
  · intro a b step
    revert step
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro step
      have hb := b.isLt
      change k+1+1 = b.val at step
      omega
    · refine Fin.lastCases ?_ (fun b step => ?_) b
      · intro step
        have ha : a = Fin.last k := Fin.ext (by change a.val+1 = k+1 at step; exact Nat.add_right_cancel step)
        simpa [w', ha, last] using diff
      · simpa [w'] using adj a b step
  · intro a b le
    revert le
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro le
      have hb : b = Fin.last (k+1) := le_antisymm (Fin.le_last b) le
      simp [hb]
    · refine Fin.lastCases ?_ (fun b le => ?_) b
      · intro _; simpa [Y'] using top a
      · simpa [Y'] using mono (show a ≤ b from le)
  · intro a; exact Fin.lastCases (by simp [Y']) (fun a => by simpa [Y'] using top a) a
  · intro a; exact Fin.lastCases (by simpa [Y',w'] using hi) (fun a => by simpa [Y',w'] using ok a) a

noncomputable def rank {r m : Nat} (K : Nat) (lab : Finset (Fin r) → Fin m → Prop)
    (X : Finset (Fin r)) : Nat := ((Finset.range K).filter (fun k => Trace lab X (k+1))).sup id

private theorem rank_lt {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hk : 0 < K) : rank K lab X < K := by
  have h : rank K lab X ≤ K-1 := Finset.sup_le (fun i hi => by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    dsimp; omega)
  omega

private theorem le_rank_iff {r m K i : Nat} {lab : Finset (Fin r) → Fin m → Prop} {X : Finset (Fin r)}
    (hi : i < K) : i ≤ rank K lab X ↔ i = 0 ∨ Trace lab X (i+1) := by
  by_cases iz : i = 0
  · simp [iz]
  constructor
  · intro h
    right
    by_contra no
    have small : rank K lab X ≤ i-1 := Finset.sup_le (fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).2
      change j ≤ i-1
      by_contra hn
      exact no (trace_prefix (by omega) hj'))
    omega
  · rintro (h | h)
    · exact (iz h).elim
    · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,h⟩)

private theorem correct_bucket {r m K : Nat} {lab : Finset (Fin r) → Fin m → Prop}
    {X : Finset (Fin r)} {i j : Fin m} (hK : 0 < K) (hi : lab X i)
    (good : ¬ Trace lab Finset.univ (K+1)) : Bucket lab X (rank K lab X) j ↔ i = j := by
  let u := rank K lab X
  have ltK : u < K := rank_lt hK
  constructor
  · intro buck
    by_contra diff
    have ext := trace_extend (Ne.symm diff) hi buck
    change Trace lab X (u+2) at ext
    by_cases top : u+1 = K
    · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
    · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
      change u+1 ≤ u at lev
      omega
  · rintro rfl
    have existsTrace : Trace lab X (u+1) := by
      rcases (le_rank_iff (lab := lab) (X := X) ltK).mp (le_refl u) with z | yes
      · simpa [z] using trace_one hi
      · exact yes
    obtain ⟨w,adj,tr⟩ := existsTrace
    let j := w (Fin.last u)
    have buck : Bucket lab X u j := ⟨w,adj,tr,rfl⟩
    have eq : i = j := by
      by_contra diff
      have ext := trace_extend (Ne.symm diff) hi buck
      change Trace lab X (u+2) at ext
      by_cases top : u+1 = K
      · exact good (trace_mono (Finset.subset_univ _) (by simpa [show u+2=K+1 by omega] using ext))
      · have lev := (le_rank_iff (lab := lab) (X := X) (i := u+1) (K := K) (by omega)).mpr (Or.inr ext)
        change u+1 ≤ u at lev
        omega
    exact eq ▸ buck

namespace RankDecoder

private theorem one {α : Type*} {x : α → List Bool} {N p nb b : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hR : ∀ d, R d < 1) :
    ∃ T, Built x N (p + 16 * (1 + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < 1 → (fun d => decide (R d = i)) ∈ T := by
  refine ⟨S, H.relax (by omega) (by omega) (fun _ h => h), fun _ h => h, ?_⟩
  intro i hi
  have eq : (fun d => decide (R d = i)) = (fun _ => true) := by
    funext d
    have : R d = i := by have := hR d; omega
    simp [this]
  rw [eq]
  exact ht

/-- Decode all exact ranks with one shared midpoint inversion per recursion level. -/
theorem decode {α : Type*} {x : α → List Bool} {N p nb b K : Nat}
    {S : Set (α → Bool)} {R : α → Nat} (H : Built x N p nb S)
    (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (hR : ∀ d, R d < K) (hK : 0 < K) (hpow : K ≤ 2^b)
    (threshold : ∀ i : Nat, i < K → (fun d => decide (i ≤ R d)) ∈ S) :
    ∃ T, Built x N (p + 16 * (K + 1)^2) (nb + b) T ∧ S ⊆ T ∧
      ∀ i : Nat, i < K → (fun d => decide (R d = i)) ∈ T := by
  classical
  induction b generalizing p nb K S R with
  | zero =>
    have : K = 1 := by simp at hpow; omega
    subst K
    exact one H ht hR
  | succ b ih =>
    by_cases small : K = 1
    · subst K
      exact one H ht hR
    let h := (K + 1) / 2
    have hh : 0 < h := by dsimp [h]; omega
    have hlt : h < K := by dsimp [h]; omega
    have hsplit : K ≤ 2 * h := by dsimp [h]; omega
    have hhpow : h ≤ 2^b := by rw [pow_succ] at hpow; dsimp [h]; omega
    let U : Nat → α → Bool := fun i d => decide (i ≤ R d)
    let Q : α → Nat := fun d => if R d < h then R d else R d - h
    have qbound (d : α) : Q d < h := by
      have hd := hR d
      dsimp [Q]
      split <;> omega
    have uget (i : Nat) : U i ∈ S := by
      by_cases hi : i < K
      · exact threshold i hi
      · have eq : U i = (fun _ => false) := by
          funext d
          have hn : ¬ i ≤ R d := by have := hR d; omega
          simp [U, hn]
        rw [eq]
        exact hf
    let S₀ := insert (inv (U h)) S
    have H₀ : Built x N p (nb + 1) S₀ := H.notGate (uget h)
    have s₀ : S ⊆ S₀ := Set.subset_insert _ _
    have lower₀ : inv (U h) ∈ S₀ := Set.mem_insert _ _
    have foldStep {P : Nat} {V : Set (α → Bool)} (HV : Built x N P (nb + 1) V)
        (sV : S₀ ⊆ V) (i : Nat) (_ : i ∈ Finset.range h) :
        Grow x N P (nb + 1) V 2 (fun d => decide (i ≤ Q d)) := by
      let g := disj (inv (U h)) (U (h + i))
      have Hg : Built x N (P + 1) (nb + 1) (insert g V) :=
        HV.orGate (sV lower₀) (sV (s₀ (uget (h + i))))
      have vsub : V ⊆ insert g V := Set.subset_insert _ _
      have Hf := Hg.andGate (vsub (sV (s₀ (uget i)))) (Set.mem_insert g V)
      have f_eq : conj (U i) g = (fun d => decide (i ≤ Q d)) := by
        funext d
        by_cases hd : R d < h
        · have hn : ¬ h ≤ R d := by omega
          simp [conj, g, disj, inv, U, Q, hd, hn]
        · have hu : h ≤ R d := by omega
          have ieq : (h + i ≤ R d) ↔ (i ≤ R d - h) := by omega
          by_cases hi : i ≤ R d
          · simp [conj, g, disj, inv, U, Q, hd, hu, hi, ieq]
          · have hnot : ¬ i ≤ R d - h := by omega
            simp [conj, U, Q, hd, hi, hnot]
      refine ⟨_, Hf, vsub.trans (Set.subset_insert _ _), ?_⟩
      rw [← f_eq]
      exact Set.mem_insert _ _
    obtain ⟨A, HA, sA, getA⟩ := batch (Finset.range h)
      (fun i d => decide (i ≤ Q d)) 2 H₀ foldStep
    obtain ⟨C, HC, sC, getC⟩ := ih HA (sA (s₀ ht)) (sA (s₀ hf)) qbound hh hhpow
      (fun i hi => getA i (Finset.mem_range.mpr hi))
    have exactStep {P : Nat} {V : Set (α → Bool)}
        (HV : Built x N P (nb + 1 + b) V) (sV : C ⊆ V)
        (i : Nat) (hi : i ∈ Finset.range K) :
        Grow x N P (nb + 1 + b) V 1 (fun d => decide (R d = i)) := by
      have hiK := Finset.mem_range.mp hi
      let j := if i < h then i else i - h
      let flag := if i < h then inv (U h) else U h
      have hj : j < h := by dsimp [j]; split <;> omega
      have hflag : flag ∈ V := by
        by_cases il : i < h
        · simpa only [flag, if_pos il] using sV (sC (sA lower₀))
        · simpa only [flag, if_neg il] using sV (sC (sA (s₀ (uget h))))
      have HM := HV.andGate (sV (getC j hj)) hflag
      have eq : conj (fun d => decide (Q d = j)) flag = (fun d => decide (R d = i)) := by
        funext d
        by_cases il : i < h <;> by_cases dl : R d < h
        · have dn : ¬ h ≤ R d := by omega
          simp [conj, flag, inv, U, Q, j, il, dl, dn]
        · have du : h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, inv, U, il, du, ne]
        · have dn : ¬ h ≤ R d := by omega
          have ne : R d ≠ i := by omega
          simp [conj, flag, U, il, dn, ne]
        · have du : h ≤ R d := by omega
          have eq' : (R d - h = i - h) ↔ R d = i := by omega
          simp [conj, flag, U, Q, j, il, dl, du, eq']
      refine ⟨_, HM, Set.subset_insert _ _, ?_⟩
      rw [← eq]
      exact Set.mem_insert _ _
    obtain ⟨T, HT, sT, getT⟩ := batch (Finset.range K)
      (fun i d => decide (R d = i)) 1 HC exactStep
    refine ⟨T, HT.relax ?_ (by omega) (fun _ m => m),
      s₀.trans (sA.trans (sC.trans sT)), fun i hi => getT i (Finset.mem_range.mpr hi)⟩
    simp only [Finset.card_range, Nat.mul_one]
    have hs : (h + 1)^2 ≤ K^2 := by
      have le : h + 1 ≤ K := by omega
      simpa only [pow_two] using Nat.mul_le_mul le le
    nlinarith

end RankDecoder

namespace Tables

open scoped Classical

private abbrev State (l A F : Nat) := (Fin l → Fin (A+1)) × (Fin l → Fin (F+1))
private abbrev Keys (l A F : Nat) := Fin (l+1) × State l A F
private abbrev Rows (α : Type*) (l r : Nat) := α → Fin l → Finset (Fin r)

private def bit {r : Nat} (U : Finset (Fin r)) (j : Fin r) : Bool := decide (j ∈ U)
private def yBit {l : Nat} (t : Fin (l+1)) (i : Fin l) : Bool := decide (t.val ≤ i.val)
private def charge (u v : Bool) : Nat := if u && !v then 1 else 0

private def lower {U : Nat} (q : Fin (U+1)) (c : Nat) : Fin (U+1) :=
  ⟨q.val - c, (Nat.sub_le _ _).trans_lt q.isLt⟩

private def debit {l A F : Nat} (q : State l A F) (i : Fin l) (y c : Bool) : State l A F :=
  (Function.update q.1 i (lower (q.1 i) (charge c y)),
   Function.update q.2 i (lower (q.2 i) (charge y c)))

private def Pay {l A F : Nat} (q : State l A F) (i : Fin l) (y c : Bool) : Prop :=
  charge c y ≤ (q.1 i).val ∧ charge y c ≤ (q.2 i).val

private def Allowed {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (j : Fin r) (i : Fin l) (y c : Bool) (d : α) : Prop :=
  (if c then j ∈ O d i else j ∈ Z d i) ∧ (y = true → j ∈ T d)

private noncomputable def edge {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y : Bool)
    (V : State l A F → α → Bool) (q : State l A F) (c : Bool) : α → Bool :=
  if Pay q i y c then
    conj (if c then fun d => bit (O d i) j else fun d => bit (Z d i) j)
      (if y then conj (fun d => bit (T d) j) (V (debit q i y c)) else V (debit q i y c))
  else fun _ => false

private theorem edge_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y : Bool)
    (V : State l A F → α → Bool) (q : State l A F) (c : Bool) (d : α) :
    edge Z O T j i y V q c d = true ↔
      Pay q i y c ∧ Allowed Z O T j i y c d ∧ V (debit q i y c) d = true := by
  unfold edge
  split <;> rename_i h <;> cases y <;> cases c <;>
    simp [h, Allowed, conj, bit, and_assoc]

/-- A fixed threshold is processed one row at a time; every row only branches on one C bit. -/
private noncomputable def steps {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (t : Fin (l+1)) (V : State l A F → α → Bool) :
    (n : Nat) → n ≤ l → State l A F → α → Bool
  | 0, _, q => V q
  | n+1, h, q =>
      let i : Fin l := ⟨n, by omega⟩
      let W := fun v => steps Z O T j t V n (by omega) v
      disj (edge Z O T j i (yBit t i) W q false) (edge Z O T j i (yBit t i) W q true)

private def Balance {l A F : Nat} (n : Nat) (q v : State l A F) (t : Fin (l+1))
    (C : Fin l → Bool) : Prop :=
  ∀ i, (q.1 i).val = (v.1 i).val + (if i.val < n then charge (C i) (yBit t i) else 0) ∧
       (q.2 i).val = (v.2 i).val + (if i.val < n then charge (yBit t i) (C i) else 0)

private theorem steps_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (t : Fin (l+1)) (V : State l A F → α → Bool)
    (d : α) (n : Nat) (hn : n ≤ l) (q : State l A F) :
    steps Z O T j t V n hn q d = true ↔
      ∃ (C : Fin l → Bool) (v : State l A F),
        (∀ i, i.val < n → Allowed Z O T j i (yBit t i) (C i) d) ∧
        Balance n q v t C ∧ V v d = true := by
  induction n generalizing q with
  | zero =>
      rw [steps]
      constructor
      · intro h
        exact ⟨fun _ => false, q, by simp, by simp [Balance], h⟩
      · rintro ⟨C, v, _, hb, hv⟩
        have e : q = v := Prod.ext
          (funext fun i => Fin.ext (by simpa using (hb i).1))
          (funext fun i => Fin.ext (by simpa using (hb i).2))
        rwa [e]
  | succ n ih =>
      let i : Fin l := ⟨n, by omega⟩
      let W := fun v => steps Z O T j t V n (by omega) v
      have hi : ¬ i.val < n := by simp [i]
      have hi' : i.val < n+1 := by simp [i]
      have sep (s : Fin l) (hs : s ≠ i) : s.val < n+1 ↔ s.val < n := by
        have hne : s.val ≠ n := fun h => hs (Fin.ext h)
        omega
      change (edge Z O T j i (yBit t i) W q false d ||
        edge Z O T j i (yBit t i) W q true d) = true ↔ _
      rw [Bool.or_eq_true_iff]
      constructor
      · intro h
        have extend (c : Bool) (he : edge Z O T j i (yBit t i) W q c d = true) :
            ∃ (C : Fin l → Bool) (v : State l A F),
              (∀ s, s.val < n+1 → Allowed Z O T j s (yBit t s) (C s) d) ∧
              Balance (n+1) q v t C ∧ V v d = true := by
          obtain ⟨hp, hc, hw⟩ := (edge_true Z O T j i _ W q c d).1 he
          obtain ⟨C, v, hg, hb, hv⟩ := (ih (by omega) (debit q i (yBit t i) c)).1 hw
          refine ⟨Function.update C i c, v, ?_, ?_, hv⟩
          · intro s hs
            by_cases heq : s = i
            · subst s
              simpa using hc
            · simpa [Function.update_of_ne heq] using hg s ((sep s heq).1 hs)
          · intro s
            by_cases heq : s = i
            · subst s
              have hbi := hb i
              have ha := hp.1
              have hf := hp.2
              simp only [debit, Function.update_self, lower, hi, if_false, Nat.add_zero] at hbi
              simp only [Function.update_self, hi', if_true]
              constructor <;> omega
            · simpa [sep s heq, debit, Function.update_of_ne heq] using hb s
        exact h.elim (extend false) (extend true)
      · rintro ⟨C, v, hc, hb, hv⟩
        have hbi := hb i
        simp only [hi', if_true] at hbi
        have hp : Pay q i (yBit t i) (C i) := by
          constructor <;> omega
        have hrest : W (debit q i (yBit t i) (C i)) d = true := by
          apply (ih (by omega) _).2
          refine ⟨C, v, (fun s hs => hc s (by omega)), ?_, hv⟩
          intro s
          by_cases heq : s = i
          · subst s
            simp only [debit, Function.update_self, lower, hi, if_false, Nat.add_zero]
            constructor <;> omega
          · simpa [sep s heq, debit, Function.update_of_ne heq] using hb s
        have he := (edge_true Z O T j i _ W q (C i) d).2 ⟨hp, hc i hi', hrest⟩
        cases hC : C i with
        | false => exact Or.inl (by simpa only [hC] using he)
        | true => exact Or.inr (by simpa only [hC] using he)

private noncomputable def table {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) : (k : Nat) → k ≤ r → State l A F → α → Bool
  | 0, _, _ => fun _ => true
  | k+1, hk, q => fun d =>
      decide (∃ t ∈ (Finset.univ : Finset (Fin (l+1))),
        steps Z O T ⟨k, by omega⟩ t (fun v => table Z O T k (by omega) v) l le_rfl q d = true)

private def put {r : Nat} (j : Fin r) (v : Bool) (U : Finset (Fin r)) : Finset (Fin r) :=
  if v then insert j U else U

private theorem mem_put {r : Nat} {j z : Fin r} {v : Bool} {U : Finset (Fin r)} :
    z ∈ put j v U ↔ z ∈ U ∨ (z = j ∧ v = true) := by
  cases v <;> simp [put, or_comm]

private theorem put_erase {r : Nat} (j : Fin r) (U : Finset (Fin r)) :
    put j (bit U j) (U.erase j) = U := by
  ext z
  by_cases h : z = j
  · subst z
    simp [mem_put, bit]
  · simp [mem_put, Finset.mem_erase, h]

private theorem card_put_sdiff {r : Nat} {j : Fin r} {U V : Finset (Fin r)}
    (hU : j ∉ U) (hV : j ∉ V) (u v : Bool) :
    (put j u U \ put j v V).card = (U \ V).card + charge u v := by
  have he : put j u U \ put j v V = put j (u && !v) (U \ V) := by
    ext z
    by_cases h : z = j
    · subst z
      cases u <;> cases v <;> simp [mem_put, Finset.mem_sdiff, hU, hV]
    · simp [mem_put, Finset.mem_sdiff, h]
  rw [he]
  cases u <;> cases v <;> simp [put, charge, Finset.card_insert_of_notMem, Finset.mem_sdiff, hU]

private def Row {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (k : Nat) (d : α) (i : Fin l) (Y C : Finset (Fin r)) : Prop :=
  ∀ z : Fin r, if z.val < k then Allowed Z O T z i (bit Y z) (bit C z) d
    else z ∉ Y ∧ z ∉ C

private theorem row_step {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    {k : Nat} {j : Fin r} (hj : j.val = k) (d : α) (i : Fin l) {Y C : Finset (Fin r)}
    (hy : j ∉ Y) (hc : j ∉ C) (y c : Bool) :
    Row Z O T (k+1) d i (put j y Y) (put j c C) ↔
      Row Z O T k d i Y C ∧ Allowed Z O T j i y c d := by
  have hj₀ : ¬ j.val < k := by omega
  have hj₁ : j.val < k+1 := by omega
  have sep (z : Fin r) (h : z ≠ j) : z.val < k+1 ↔ z.val < k := by
    have hn : z.val ≠ j.val := fun e => h (Fin.ext e)
    omega
  have self (Ws : Finset (Fin r)) (hWs : j ∉ Ws) (v : Bool) : bit (put j v Ws) j = v := by
    cases v <;> simp [bit, mem_put, hWs]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro z
      by_cases he : z = j
      · subst z
        simp [hj₀, hy, hc]
      · simpa [sep z he, bit, mem_put, he] using h z
    · simpa [hj₁, self Y hy, self C hc] using h j
  · rintro ⟨h, ha⟩ z
    by_cases he : z = j
    · subst z
      simpa [hj₁, self Y hy, self C hc] using ha
    · simpa [sep z he, bit, mem_put, he] using h z

private theorem row_top {α : Type*} {l r : Nat} (Z O : Rows α l r) (T : α → Finset (Fin r))
    (d : α) (i : Fin l) (Y C : Finset (Fin r)) :
    Row Z O T r d i Y C ↔ Y ⊆ T d ∧ (Finset.univ \ C) ⊆ Z d i ∧ C ⊆ O d i := by
  unfold Row
  simp only [Fin.isLt, if_true]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (h z).2 (by simp [bit, hz])
    · intro z hz
      have hn := (Finset.mem_sdiff.mp hz).2
      simpa [bit, hn] using (h z).1
    · intro z hz
      simpa [bit, hz] using (h z).1
  · rintro ⟨hY, hZ, hO⟩ z
    constructor
    · by_cases hz : z ∈ C
      · simpa [bit, hz] using hO hz
      · simpa [bit, hz] using hZ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩)
    · intro h
      exact hY (by simpa [bit] using h)

private theorem threshold {l r : Nat} {Y : Fin l → Finset (Fin r)} (hY : Monotone Y) (j : Fin r) :
    ∃ t : Fin (l+1), ∀ i, yBit t i = bit (Y i) j := by
  by_cases h : ∃ n : Nat, ∃ i : Fin l, i.val = n ∧ j ∈ Y i
  · obtain ⟨i₀, hi₀, hm⟩ := Nat.find_spec h
    refine ⟨⟨Nat.find h, by have := i₀.isLt; omega⟩, fun i => ?_⟩
    change decide (Nat.find h ≤ i.val) = decide (j ∈ Y i)
    apply decide_eq_decide.mpr
    constructor
    · intro hi
      exact hY (show i₀ ≤ i from by change i₀.val ≤ i.val; omega) hm
    · intro hi
      exact Nat.find_min' h ⟨i, rfl, hi⟩
  · refine ⟨⟨l, by omega⟩, fun i => ?_⟩
    have hm : j ∉ Y i := fun hi => h ⟨i.val, i, rfl, hi⟩
    have hn : ¬ l ≤ i.val := Nat.not_le_of_lt i.isLt
    simp [yBit, bit, hm, hn]

private def Feasible {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (k : Nat) (q : State l A F) (d : α) : Prop :=
  ∃ Y C : Fin l → Finset (Fin r), Monotone Y ∧
    ∀ i, Row Z O T k d i (Y i) (C i) ∧
      (C i \ Y i).card ≤ (q.1 i).val ∧ (Y i \ C i).card ≤ (q.2 i).val

private theorem table_true {α : Type*} {l r A F : Nat} (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (d : α) (k : Nat) (hk : k ≤ r) (q : State l A F) :
    table Z O T k hk q d = true ↔ Feasible Z O T k q d := by
  induction k generalizing q with
  | zero =>
      rw [table]
      refine ⟨fun _ => ⟨fun _ => ∅, fun _ => ∅, fun _ _ _ => le_rfl, fun i => ?_⟩,
        fun _ => rfl⟩
      simp [Row]
  | succ k ih =>
      let j : Fin r := ⟨k, by omega⟩
      let V := fun v : State l A F => table Z O T k (by omega) v
      change decide (∃ t ∈ (Finset.univ : Finset (Fin (l+1))),
        steps Z O T j t V l le_rfl q d = true) = true ↔ _
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨t, _, ht⟩
        obtain ⟨c, v, hc, hb, hv⟩ := (steps_true Z O T j t V d l le_rfl q).1 ht
        obtain ⟨Y, C, hY, h⟩ := (ih (by omega) v).1 hv
        refine ⟨fun i => put j (yBit t i) (Y i), fun i => put j (c i) (C i), ?_, ?_⟩
        · intro i s his z hz
          rw [mem_put] at hz ⊢
          refine hz.elim (fun hmem => Or.inl (hY his hmem)) ?_
          rintro ⟨hmem, hbit⟩
          have ht' : t.val ≤ i.val := by simpa [yBit] using hbit
          exact Or.inr ⟨hmem, by simpa [yBit] using ht'.trans his⟩
        · intro i
          obtain ⟨hr, ha, hf⟩ := h i
          have fresh : j ∉ Y i ∧ j ∉ C i := by simpa [j] using hr j
          have hbi := hb i
          simp only [i.isLt, if_true] at hbi
          refine ⟨(row_step Z O T rfl d i fresh.1 fresh.2 _ _).2 ⟨hr, hc i i.isLt⟩, ?_, ?_⟩
          · rw [card_put_sdiff fresh.2 fresh.1, hbi.1]
            exact Nat.add_le_add_right ha _
          · rw [card_put_sdiff fresh.1 fresh.2, hbi.2]
            exact Nat.add_le_add_right hf _
      · rintro ⟨Y, C, hY, h⟩
        obtain ⟨t, ht⟩ := threshold hY j
        let c := fun i => bit (C i) j
        let U := fun i => (Y i).erase j
        let W := fun i => (C i).erase j
        let v : State l A F := (fun i => lower (q.1 i) (charge (c i) (yBit t i)),
                                 fun i => lower (q.2 i) (charge (yBit t i) (c i)))
        have split (i : Fin l) :
            (Row Z O T k d i (U i) (W i) ∧ Allowed Z O T j i (yBit t i) (c i) d) ∧
            (W i \ U i).card + charge (c i) (yBit t i) ≤ (q.1 i).val ∧
            (U i \ W i).card + charge (yBit t i) (c i) ≤ (q.2 i).val := by
          have h1 : put j (yBit t i) (U i) = Y i := by rw [ht i]; exact put_erase j (Y i)
          have h2 : put j (c i) (W i) = C i := put_erase j (C i)
          have hu : j ∉ U i := by simp [U]
          have hw : j ∉ W i := by simp [W]
          refine ⟨(row_step Z O T rfl d i hu hw _ _).1 ?_, ?_, ?_⟩
          · rw [h1, h2]
            exact (h i).1
          · rw [← card_put_sdiff hw hu, h1, h2]
            exact (h i).2.1
          · rw [← card_put_sdiff hu hw, h1, h2]
            exact (h i).2.2
        refine ⟨t, Finset.mem_univ _, (steps_true Z O T j t V d l le_rfl q).2
          ⟨c, v, (fun i _ => (split i).1.2), ?_, ?_⟩⟩
        · intro i
          have ha := (split i).2.1
          have hf := (split i).2.2
          simp only [i.isLt, if_true, v, lower]
          constructor <;> omega
        · apply (ih (by omega) v).2
          refine ⟨U, W, ?_, fun i => ⟨(split i).1.1, ?_, ?_⟩⟩
          · intro i s his z hz
            obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hz
            exact Finset.mem_erase.mpr ⟨hn, hY his hm⟩
          · have ha := (split i).2.1
            change (W i \ U i).card ≤ (q.1 i).val - charge (c i) (yBit t i)
            omega
          · have hf := (split i).2.2
            change (U i \ W i).card ≤ (q.2 i).val - charge (yBit t i) (c i)
            omega

private theorem already {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f : α → Bool} (hf : f ∈ S) (cost : Nat) : Grow x N p b S cost f :=
  ⟨S, H.relax (by omega) le_rfl (by intro g hg; exact hg), (by intro g hg; exact hg), hf⟩

private theorem appendAnd {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f g : α → Bool} (hf : f ∈ S) (hg : g ∈ S) :
    Grow x N p b S 1 (conj f g) :=
  ⟨_, H.andGate hf hg, Set.subset_insert _ _, Set.mem_insert _ _⟩

private theorem appendOr {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) {f g : α → Bool} (hf : f ∈ S) (hg : g ∈ S) :
    Grow x N p b S 1 (disj f g) :=
  ⟨_, H.orGate hf hg, Set.subset_insert _ _, Set.mem_insert _ _⟩

private theorem edge_grow {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (i : Fin l) (y c : Bool)
    (V : State l A F → α → Bool) (q : State l A F)
    (hz : (fun d => bit (Z d i) j) ∈ S) (ho : (fun d => bit (O d i) j) ∈ S)
    (ht : (fun d => bit (T d) j) ∈ S) (hfalse : (fun _ => false) ∈ S)
    (hv : V (debit q i y c) ∈ S) : Grow x N p b S 2 (edge Z O T j i y V q c) := by
  by_cases hp : Pay q i y c
  · let B := if c then fun d => bit (O d i) j else fun d => bit (Z d i) j
    have hB : B ∈ S := by cases c <;> assumption
    let w := V (debit q i y c)
    have hw : w ∈ S := hv
    have hinner : Grow x N p b S 1 (if y then conj (fun d => bit (T d) j) w else w) := by
      cases y
      · exact already H hw 1
      · exact appendAnd H ht hw
    obtain ⟨U, hU, hSU, hinner⟩ := hinner
    obtain ⟨W, hW, hUW, hout⟩ := appendAnd hU (hSU hB) hinner
    exact ⟨W, hW, hSU.trans hUW, by simpa only [edge, hp, if_true, B, w] using hout⟩
  · simpa only [edge, hp, if_false] using already H hfalse 2

private noncomputable def layerCost (l A F : Nat) : Nat := Fintype.card (Keys l A F) * 5
private noncomputable def columnCost (l A F : Nat) : Nat :=
  l * layerCost l A F + Fintype.card (State l A F) * (l+1)

private theorem steps_built {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r)) (j : Fin r) (V : State l A F → α → Bool)
    (hz : ∀ i, (fun d => bit (Z d i) j) ∈ S) (ho : ∀ i, (fun d => bit (O d i) j) ∈ S)
    (ht : (fun d => bit (T d) j) ∈ S) (hfalse : (fun _ => false) ∈ S) (hv : ∀ q, V q ∈ S)
    (n : Nat) (hn : n ≤ l) :
    ∃ U, Built x N (p+n*layerCost l A F) b U ∧ S ⊆ U ∧
      ∀ t q, steps Z O T j t V n hn q ∈ U := by
  induction n with
  | zero => exact ⟨S, by simpa using H, fun _ h => h, fun _ q => hv q⟩
  | succ n ih =>
      obtain ⟨R, hR, hSR, hprev⟩ := ih (by omega)
      let i : Fin l := ⟨n, by omega⟩
      obtain ⟨U, hU, hRU, hvalues⟩ := batch (Finset.univ : Finset (Keys l A F))
        (fun z => steps Z O T j z.1 V (n+1) hn z.2) 5 hR (by
          intro P M hM hRM z _
          let W := fun q => steps Z O T j z.1 V n (by omega) q
          have hSM := hSR.trans hRM
          let y := yBit z.1 i
          have make (c : Bool) := edge_grow hM Z O T j i y c W z.2
            (hSM (hz i)) (hSM (ho i)) (hSM ht) (hSM hfalse) (hRM (hprev _ _))
          obtain ⟨M₀, hM₀, hMM₀, he₀⟩ := make false
          obtain ⟨M₁, hM₁, hM₀M₁, he₁⟩ := edge_grow hM₀ Z O T j i y true W z.2
            (hMM₀ (hSM (hz i))) (hMM₀ (hSM (ho i))) (hMM₀ (hSM ht))
            (hMM₀ (hSM hfalse)) (hMM₀ (hRM (hprev _ _)))
          obtain ⟨M₂, hM₂, hM₁M₂, hdone⟩ := appendOr hM₁ (hM₀M₁ he₀) he₁
          exact ⟨M₂, hM₂, hMM₀.trans (hM₀M₁.trans hM₁M₂), hdone⟩)
      refine ⟨U, ?_, hSR.trans hRU, fun t q => hvalues (t,q) (Finset.mem_univ _)⟩
      simpa [layerCost, Nat.succ_mul, Nat.add_assoc] using hU

private theorem table_built {α : Type*} {x : α → List Bool} {N p b l r A F : Nat}
    {S : Set (α → Bool)} (H : Built x N p b S) (Z O : Rows α l r)
    (T : α → Finset (Fin r))
    (hz : ∀ i j, (fun d => bit (Z d i) j) ∈ S) (ho : ∀ i j, (fun d => bit (O d i) j) ∈ S)
    (ht : ∀ j, (fun d => bit (T d) j) ∈ S)
    (hfalse : (fun _ => false) ∈ S) (htrue : (fun _ => true) ∈ S) (k : Nat) (hk : k ≤ r) :
    ∃ U, Built x N (p+k*columnCost l A F) b U ∧ S ⊆ U ∧
      ∀ q : State l A F, table Z O T k hk q ∈ U := by
  induction k with
  | zero => exact ⟨S, by simpa using H, fun _ h => h, fun _ => htrue⟩
  | succ k ih =>
      obtain ⟨R, hR, hSR, hprev⟩ := ih (by omega)
      let j : Fin r := ⟨k, by omega⟩
      let V := fun v : State l A F => table Z O T k (by omega) v
      obtain ⟨U, hU, hRU, hstep⟩ := steps_built hR Z O T j V (fun i => hSR (hz i j))
        (fun i => hSR (ho i j)) (hSR (ht j)) (hSR hfalse) hprev l le_rfl
      obtain ⟨W, hW, hUW, hout⟩ := batch (Finset.univ : Finset (State l A F))
        (fun q => table Z O T (k+1) hk q) (l+1) hU (by
          intro P M hM hUM q _
          obtain ⟨Q, hQ, hMQ, hfQ⟩ := anyFold (Finset.univ : Finset (Fin (l+1)))
            (fun t => steps Z O T j t V l le_rfl q) hM (hUM (hRU (hSR hfalse)))
            (fun t _ => hUM (hstep t q))
          refine ⟨Q, by simpa only [Finset.card_univ, Fintype.card_fin] using hQ, hMQ, ?_⟩
          refine Eq.mpr (congrArg (fun g : α → Bool => g ∈ Q) ?_) hfQ
          funext d
          apply Bool.eq_iff_iff.mpr
          simp only [table, decide_eq_true_eq, j, V])
      refine ⟨W, ?_, hSR.trans (hRU.trans hUW), fun q => hout q (Finset.mem_univ _)⟩
      simpa [columnCost, Nat.succ_mul, Nat.add_assoc] using hW

private theorem columnCost_bound (l A F : Nat) :
    columnCost l A F ≤ 8 * (l+1)^2 * ((A+1)*(F+1))^l := by
  have hs : Fintype.card (State l A F) = ((A+1)*(F+1))^l := by
    simp [Fintype.card_prod, Fintype.card_fun, mul_pow]
  have hk : Fintype.card (Keys l A F) = (l+1) * ((A+1)*(F+1))^l := by
    rw [Fintype.card_prod, Fintype.card_fin, hs]
  rw [columnCost, layerCost, hs, hk]
  let c := ((A+1)*(F+1))^l
  change l * ((l+1) * c * 5) + c * (l+1) ≤ 8 * (l+1)^2 * c
  have h : l*5+1 ≤ 8*(l+1) := by omega
  calc
    l * ((l+1) * c * 5) + c * (l+1) = (l*5+1) * (l+1) * c := by ring
    _ ≤ (8*(l+1)) * (l+1) * c := Nat.mul_le_mul_right c (Nat.mul_le_mul_right (l+1) h)
    _ = 8 * (l+1)^2 * c := by ring

/-- Share all residual-budget entries after each row and coordinate. No NOT gates are added. -/
theorem grow {α : Type*} {x : α → List Bool} {N p b l r A F : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) (Z O : α → Fin l → Finset (Fin r)) (T : α → Finset (Fin r))
    (a f : Fin l → Nat) (ha : ∀ i, a i ≤ A) (hf : ∀ i, f i ≤ F)
    (hz : ∀ i j, (fun d => decide (j ∈ Z d i)) ∈ S)
    (ho : ∀ i j, (fun d => decide (j ∈ O d i)) ∈ S)
    (ht : ∀ j, (fun d => decide (j ∈ T d)) ∈ S)
    (hfalse : (fun _ => false) ∈ S) (htrue : (fun _ => true) ∈ S) :
    Grow x N p b S (8 * (r+2) * (l+1)^2 * ((A+1)*(F+1))^l)
      (fun d => decide (∃ Y C : Fin l → Finset (Fin r), Monotone Y ∧
        (∀ i, Y i ⊆ T d) ∧
        (∀ i, (Finset.univ \ C i) ⊆ Z d i ∧ C i ⊆ O d i ∧
          (C i \ Y i).card ≤ a i ∧ (Y i \ C i).card ≤ f i))) := by
  let q : State l A F := (fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩,
                          fun i => ⟨f i, Nat.lt_succ_of_le (hf i)⟩)
  obtain ⟨U, hU, hSU, hout⟩ := table_built H Z O T hz ho ht hfalse htrue r le_rfl
    (A := A) (F := F)
  have hcost : r * columnCost l A F ≤ 8 * (r+2) * (l+1)^2 * ((A+1)*(F+1))^l := by
    calc
      _ ≤ (r+2) * (8 * (l+1)^2 * ((A+1)*(F+1))^l) :=
        Nat.mul_le_mul (by omega) (columnCost_bound l A F)
      _ = _ := by ring
  refine ⟨U, hU.relax (Nat.add_le_add_left hcost p) le_rfl (fun _ h => h), hSU, ?_⟩
  refine Eq.mpr (congrArg (fun g : α → Bool => g ∈ U) ?_) (hout q)
  funext d
  apply Bool.eq_iff_iff.mpr
  rw [table_true, decide_eq_true_eq]
  constructor
  · rintro ⟨Y, C, hm, hy, h⟩
    refine ⟨Y, C, hm, fun i => ⟨(row_top Z O T d i (Y i) (C i)).2
      ⟨hy i, (h i).1, (h i).2.1⟩, (h i).2.2.1, (h i).2.2.2⟩⟩
  · rintro ⟨Y, C, hm, h⟩
    have hr := fun i => (row_top Z O T d i (Y i) (C i)).1 (h i).1
    exact ⟨Y, C, hm, fun i => (hr i).1, fun i => ⟨(hr i).2.1, (hr i).2.2, (h i).2⟩⟩

end Tables


-- Row indexing adapted from b81440944eeb15a06b92ee0d64d15d33c12dfab6, lean/PEqualNP/Outside/L_lib_1330.lean.
private theorem flatten_ofFn_length {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) :
    (List.ofFn f).flatten.length = k * m := by
  rw [List.length_flatten, List.map_ofFn]
  have hconst : (List.length ∘ f) = fun _ => m := funext hlen
  rw [hconst, List.ofFn_const, List.sum_replicate, smul_eq_mul]

private theorem flatten_ofFn_getElem {α : Type} {k m : ℕ} (f : Fin k → List α)
    (hlen : ∀ i : Fin k, (f i).length = m) (i : Fin k) (r : ℕ) (hr : r < m) :
    ((List.ofFn f).flatten)[i.val * m + r]'(by
      rw [flatten_ofFn_length f hlen]
      have : (i.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.isLt)
      rw [Nat.add_mul, Nat.one_mul] at this; omega) =
    (f i)[r]'(by rw [hlen i]; exact hr) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      rw [List.getElem_append_left (by rw [hlen 0]; exact hr)]
    | succ i' =>
      simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, Nat.add_mul, Nat.one_mul]
      have h1 : m ≤ i'.val * m + m + r := by omega
      rw [List.getElem_append_right (by rw [hlen 0]; exact h1)]
      have heq : i'.val * m + m + r - (f 0).length = i'.val * m + r := by rw [hlen 0]; omega
      simp only [heq]
      exact ih (fun j => f j.succ) (fun j => hlen j.succ) i'


private def wordCost (r l A F : Nat) : Nat := 8*(r+2)*(l+1)^2*((A+1)*(F+1))^l

private def familyCost (r m l A F : Nat) : Nat := (m+1)^l * (wordCost r l A F + 1)

private def sizeBound (r m K A F : Nat) : Nat :=
  128*(r+2)*(K+3)^3*((m+1)*(A+1)*(F+1))^(K+1)

private theorem grow_family {α : Type*} {x : α → List Bool} {N p b : Nat} {S : Set (α → Bool)}
    {r m l A F : Nat} {lab : α → Finset (Fin r) → Fin m → Prop} {U : α → Finset (Fin r)}
    (H : Built x N p b S) (hf : (fun _ => false) ∈ S) (P : (Fin l → Fin m) → Prop)
    (word : ∀ {P' T}, Built x N P' b T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x N P' b T (wordCost r l A F) (fun d => decide (WordTrace (lab d) (U d) w))) :
    Grow x N p b S (familyCost r m l A F)
      (fun d => decide (∃ w : Fin l → Fin m, P w ∧ WordTrace (lab d) (U d) w)) := by
  let ws : Finset (Fin l → Fin m) := Finset.univ.filter P
  let sig (w : Fin l → Fin m) (d : α) := decide (WordTrace (lab d) (U d) w)
  obtain ⟨T,hT,st,hw⟩ := batch ws sig (wordCost r l A F) H (fun h sub w _ => word h sub w)
  obtain ⟨Q,hQ,tq,hq⟩ := anyFold ws sig hT (st hf) hw
  have cw : ws.card ≤ (m+1)^l := by
    calc
      ws.card ≤ (Finset.univ : Finset (Fin l → Fin m)).card := Finset.card_filter_le _ _
      _ = m^l := by simp [Fintype.card_fun]
      _ ≤ (m+1)^l := Nat.pow_le_pow_left (by omega) _
  have cap : p + ws.card * wordCost r l A F + ws.card ≤ p + familyCost r m l A F := by
    rw [Nat.add_assoc, ← Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ cw) _
  refine ⟨Q,hQ.relax cap le_rfl (Set.Subset.rfl),st.trans tq,?_⟩
  have eq : (fun d => decide (∃ w ∈ ws, sig w d = true)) =
      (fun d => decide (∃ w : Fin l → Fin m, P w ∧ WordTrace (lab d) (U d) w)) := by
    funext d; simp [ws,sig]
  exact eq ▸ hq

private noncomputable def signal {r m : Nat} (K : Nat) (lab : Finset (Fin r) → Fin m → Prop)
    (X : Finset (Fin r)) (j : Fin m) : Bool := decide (Bucket lab X (rank K lab X) j)

private theorem aggregate {α : Type*} {x : α → List Bool} {N : Nat} {S : Set (α → Bool)}
    {r m b K A F : Nat} {lab : α → Finset (Fin r) → Fin m → Prop} {X : α → Finset (Fin r)}
    (H : Built x N 0 0 S) (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (hK : 0 < K) (pow : K ≤ 2^b)
    (word : ∀ {P T l} (U : α → Finset (Fin r)), (U = X ∨ U = fun _ => Finset.univ) →
      Built x N P 0 T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x N P 0 T (wordCost r l A F) (fun d => decide (WordTrace (lab d) (U d) w))) :
    ∃ T, Built x N (sizeBound r m K A F) b T ∧
      (fun d => decide (Trace (lab d) Finset.univ (K+1))) ∈ T ∧
      ∀ j, (fun d => signal K (lab d) (X d) j) ∈ T := by
  let M := (m+1)*(A+1)*(F+1)
  let H₀ := 9*(r+2)*(K+2)^2
  let p₀ := H₀*M^(K+1)
  let p₁ := H₀*M^K
  have hM : 1 ≤ M := by change 0 < M; dsimp [M]; positivity
  have cost (l : Nat) (hl : l ≤ K+1) : familyCost r m l A F ≤ H₀*M^l := by
    have hcoeff : 1 ≤ (r+2)*(l+1)^2*((A+1)*(F+1))^l := by
      change 0 < (r+2)*(l+1)^2*((A+1)*(F+1))^l
      positivity
    calc
      familyCost r m l A F = (m+1)^l * (8*((r+2)*(l+1)^2*((A+1)*(F+1))^l) + 1) := by
        unfold familyCost wordCost; ring
      _ ≤ (m+1)^l * (9*((r+2)*(l+1)^2*((A+1)*(F+1))^l)) := by gcongr; omega
      _ = 9*(r+2)*(l+1)^2*M^l := by dsimp [M]; rw [mul_pow,mul_pow,mul_pow]; ring
      _ ≤ H₀*M^l := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (show l+1 ≤ K+2 by omega) 2))
  obtain ⟨U,hU,su,bad⟩ := grow_family H hf (Adj (m := m) (l := K+1))
    (fun h st w => word (fun _ => Finset.univ) (Or.inr rfl) h st w)
  have hU' : Built x N p₀ 0 U := hU.relax (by simpa [p₀] using cost (K+1) le_rfl) le_rfl (Set.Subset.rfl)
  let L (v : Fin K × Option (Fin m)) (d : α) := decide
    (∃ w : Fin (v.1.val+1) → Fin m, (Adj w ∧ ∀ j, v.2 = some j → w (Fin.last v.1.val) = j) ∧
      WordTrace (lab d) (X d) w)
  obtain ⟨V,hV,uv,lh⟩ := batch (Finset.univ : Finset (Fin K × Option (Fin m))) L p₁ hU' (by
    intro P T h ut v _
    obtain ⟨Q,hQ,tq,out⟩ := grow_family h (ut (su hf))
      (fun w : Fin (v.1.val+1) → Fin m => Adj w ∧ ∀ j, v.2 = some j → w (Fin.last v.1.val) = j)
      (fun hh st w => word X (Or.inl rfl) hh (su.trans (ut.trans st)) w)
    have cv : familyCost r m (v.1.val+1) A F ≤ p₁ :=
      (cost _ (by have := v.1.isLt; omega)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM (by have := v.1.isLt; omega)))
    refine ⟨Q,hQ.relax (Nat.add_le_add_left cv _) le_rfl (Set.Subset.rfl),tq,?_⟩
    convert out using 1
    funext d; apply Bool.eq_iff_iff.mpr; simp [L])
  have tr (k : Fin K) : (fun d => decide (Trace (lab d) (X d) (k.val+1))) ∈ V := by
    convert lh (k,none) (Finset.mem_univ _) using 1
    funext d; apply boolOfIff; simp [L,Trace]
  have buck (k : Fin K) (j : Fin m) : (fun d => decide (Bucket (lab d) (X d) k.val j)) ∈ V := by
    convert lh (k,some j) (Finset.mem_univ _) using 1
    funext d; apply boolOfIff
    simp [L,Bucket,and_left_comm,and_assoc,and_comm]
  let R (d : α) := rank K (lab d) (X d)
  have threshold (i : Nat) (hi : i < K) : (fun d => decide (i ≤ R d)) ∈ V := by
    rcases eq_or_ne i 0 with rfl | nz
    · simpa using uv (su ht)
    · have he : (fun d => decide (i ≤ R d)) = (fun d => decide (Trace (lab d) (X d) (i+1))) := by
        funext d
        simp [R, le_rank_iff hi,nz]
      rw [he]; exact tr ⟨i,hi⟩
  obtain ⟨W,hW,vw,exactRank⟩ := RankDecoder.decode hV (uv (su ht)) (uv (su hf))
    (R := R) (fun _ => rank_lt hK) hK pow threshold
  obtain ⟨T,hT,wt,taps⟩ := batch (Finset.univ : Finset (Fin m))
    (fun j d => signal K (lab d) (X d) j) (2*K) hW (by
      intro P Q h wq j _
      let c (k : Fin K) := conj (fun d => decide (R d=k.val))
        (fun d => decide (Bucket (lab d) (X d) k.val j))
      obtain ⟨Q',hQ',qq,terms⟩ := batch (Finset.univ : Finset (Fin K)) c 1 h (by
        intro p' A hh qa k _
        have hh' := hh.andGate (qa (wq (exactRank k.val k.isLt))) (qa (wq (vw (buck k j))))
        exact ⟨_,hh',Set.subset_insert _ _,Set.mem_insert _ _⟩)
      obtain ⟨Q'',hQ'',q'q'',sum⟩ := anyFold (Finset.univ : Finset (Fin K)) c hQ'
        (qq (wq (vw (uv (su hf))))) terms
      refine ⟨Q'',hQ''.relax (by simp; omega) le_rfl (Set.Subset.rfl),qq.trans q'q'',?_⟩
      convert sum using 1
      funext d
      symm
      apply Bool.eq_iff_iff.mpr
      simp only [Finset.mem_univ,true_and,c,conj,Bool.and_eq_true,decide_eq_true_eq,signal]
      constructor
      · rintro ⟨k,hk,ok⟩; simpa only [← hk] using ok
      · intro yes; exact ⟨⟨R d,rank_lt hK⟩,rfl,yes⟩)
  have leM : m+1 ≤ M := by
    dsimp [M]
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hp01 : (m+1)*p₁ ≤ p₀ := by
    dsimp [p₀,p₁]
    rw [pow_succ]
    calc
      (m+1)*(H₀*M^K) ≤ M*(H₀*M^K) := Nat.mul_le_mul_right _ leM
      _ = H₀*(M^K*M) := by ring
  have hp : K*(m+1)*p₁ ≤ K*p₀ := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hp01
  have hdr : 16*(K+1)^2 ≤ p₀ := by
    have hz : 1 ≤ M^(K+1) := by change 0 < M^(K+1); positivity
    calc
      16*(K+1)^2 ≤ H₀ := by dsimp [H₀]; nlinarith
      _ ≤ p₀ := by dsimp [p₀]; exact Nat.le_mul_of_pos_right _ hz
  have hlast : m*(2*K) ≤ p₀ := by
    have leP : m ≤ M^(K+1) := by
      nlinarith [Nat.pow_le_pow_right hM (show 1 ≤ K+1 by omega), pow_one M]
    have coef : 2*K ≤ H₀ := by dsimp [H₀]; nlinarith
    simpa [p₀,Nat.mul_comm] using Nat.mul_le_mul coef leP
  have tot : p₀ + K*(m+1)*p₁ + 16*(K+1)^2 + m*(2*K) ≤ sizeBound r m K A F := by
    calc
      _ ≤ (K+3)*p₀ := by nlinarith
      _ = 9*(r+2)*(K+2)^2*(K+3)*M^(K+1) := by dsimp [p₀,H₀]; ring
      _ ≤ sizeBound r m K A F := by
        change _ ≤ 128*(r+2)*(K+3)^3*M^(K+1)
        have hs : (K+2)^2 ≤ (K+3)^2 := by gcongr; omega
        rw [show (K+3)^3 = (K+3)^2*(K+3) by ring]
        rw [← Nat.mul_assoc (128*(r+2)) ((K+3)^2) (K+3)]
        gcongr <;> omega
  have hfinal : Built x N (sizeBound r m K A F) b T := by
    apply hT.relax _ (by simp) (Set.Subset.rfl)
    simpa [Fintype.card_prod,Nat.add_comm] using tot
  refine ⟨T,hfinal,wt (vw (uv ?_)),fun j => taps j (Finset.mem_univ _)⟩
  convert bad using 1
  funext d; apply boolOfIff; rfl


noncomputable def rows {m r : Nat} (D : Fin m → Finset (Fin r)) : List Bool :=
  (List.ofFn (fun i => bits (D i))).flatten

private theorem rows_length {m r : Nat} (D : Fin m → Finset (Fin r)) : (rows D).length = m*r :=
  flatten_ofFn_length _ (fun _ => by simp [bits])

private theorem rows_getD {m r : Nat} (D : Fin m → Finset (Fin r)) (i : Fin m) (j : Fin r) :
    (rows D).getD (i.val*r+j.val) false = decide (j ∈ D i) := by
  have lb : i.val*r+j.val < (rows D).length := by
    rw [rows_length]
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  have rb : j.val < (bits (D i)).length := by simp [bits]
  calc
    _ = (rows D)[i.val*r+j.val] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lb]
    _ = (bits (D i))[j.val] := flatten_ofFn_getElem _ (fun _ => by simp [bits]) i j.val j.isLt
    _ = _ := by
      rw [← bits_getD (D i) j]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem rb]

private def InputSet {α : Type*} (x : α → List Bool) (N : Nat) : Set (α → Bool) :=
  {f | ∃ i < N, f = fun d => (x d).getD i false}

private theorem input_mem {α : Type*} {x : α → List Bool} {N i : Nat} {f : α → Bool}
    (hi : i < N) (eq : ∀ d, (x d).getD i false = f d) : f ∈ InputSet x N :=
  ⟨i,hi,(funext eq).symm⟩

private theorem suffix_const {α : Type*} {w : α → List Bool} {n : Nat} (L : ∀ d, (w d).length = n) :
    (fun _ => false) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) ∧
    (fun _ => true) ∈ InputSet (fun d => w d ++ [false,true]) (n+2) := by
  constructor
  · apply input_mem (i := n) (by omega)
    intro d; simp [List.getD_append_right _ _ _ _ (show (w d).length ≤ n by rw [L]),L]
  · apply input_mem (i := n+1) (by omega)
    intro d; simp [List.getD_append_right _ _ _ _ (show (w d).length ≤ n+1 by rw [L]; omega),L]

private theorem some_taps {α : Type*} {x : α → List Bool} {n m p b : Nat} {S : Set (α → Bool)}
    {bad : α → Bool} {tap : Fin m → α → Bool} (H : Built x (n+2) p b S)
    (hb : bad ∈ S) (ht : ∀ j, tap j ∈ S) :
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧ (∀ j, out j < n+2+D.size) ∧
      notCount D ≤ b ∧ D.size - notCount D ≤ p ∧
      (∀ d, D.eval (x d) = bad d) ∧ ∀ d j, (D.wires (x d)).getD (out j) false = tap j d := by
  obtain ⟨_,gs,fan,back,pc,nc,sigs⟩ := H
  obtain ⟨o,ho,eo⟩ := sigs _ hb
  choose out hout eout using (fun j => sigs (tap j) (ht j))
  exact ⟨⟨gs,o⟩,out,⟨fan,back,ho⟩,hout,nc,pc,congrFun eo,fun d j => congrFun (eout j) d⟩

private theorem word_table_equiv {r m l : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (U : Finset (Fin r)) (w : Fin l → Fin m) :
    WordTrace (Label a f Z O) U w ↔
      ∃ (Y C : Fin l → Finset (Fin r)), Monotone Y ∧ (∀ i, Y i ⊆ U) ∧
        ∀ i, (Finset.univ \ C i) ⊆ Z (w i) ∧ C i ⊆ O (w i) ∧
          ((C i) \ (Y i)).card ≤ min r (a (w i)) ∧ ((Y i) \ (C i)).card ≤ min r (f (w i)) := by
  constructor
  · rintro ⟨Y,mono,sub,lab⟩
    choose C hC using lab
    refine ⟨Y,C,mono,sub,fun i => ?_⟩
    obtain ⟨hZ,hO,ha,hf⟩ := hC i
    exact ⟨hZ,hO,le_min (by simpa using ((C i) \ (Y i)).card_le_univ) ha,
      le_min (by simpa using ((Y i) \ (C i)).card_le_univ) hf⟩
  · rintro ⟨Y,C,mono,sub,all⟩
    exact ⟨Y,mono,sub,fun i => ⟨C i,(all i).1,(all i).2.1,
      (all i).2.2.1.trans (min_le_right ..),(all i).2.2.2.trans (min_le_right ..)⟩⟩

private theorem realize {α : Type*} {x : α → List Bool} {n r m b : Nat} {S : Set (α → Bool)}
    (a f : Fin m → Nat) (Z O : α → Fin m → Finset (Fin r)) (X : α → Finset (Fin r))
    (H : Built x (n+2) 0 0 S) (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S)
    (word : ∀ {P T l} (U : α → Finset (Fin r)), (U = X ∨ U = fun _ => Finset.univ) →
      Built x (n+2) P 0 T → S⊆T → ∀ w : Fin l → Fin m,
      Grow x (n+2) P 0 T (wordCost r l (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i)))
        (fun d => decide (WordTrace (Label a f (Z d) (O d)) (U d) w))) :
    let K := min (2^b) (r+1)
    let B := sizeBound r m K (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i))
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧ (∀ j, out j < n+2+D.size) ∧
      notCount D ≤ b ∧ D.size - notCount D ≤ B ∧
      (∀ d, D.eval (x d) = false ↔ ¬ Trace (Label a f (Z d) (O d)) Finset.univ (K+1)) ∧
      ∀ d, (¬ Trace (Label a f (Z d) (O d)) Finset.univ (K+1)) →
        ∀ i, Label a f (Z d) (O d) (X d) i → ∀ j,
        (D.wires (x d)).getD (out j) false = labelBit i j := by
  dsimp only
  let K := min (2^b) (r+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T,hT,bad,tap⟩ := aggregate (K := K) (b := b) H ht hf hK (min_le_left ..) word
  obtain ⟨D,out,v,lt,neg,pos,fail,hit⟩ := some_taps hT bad tap
  refine ⟨D,out,v,lt,neg,pos,fun d => by rw [fail]; simp [K],?_⟩
  intro d good i hi j
  rw [hit]
  exact Bool.eq_iff_iff.mpr (by simp [signal,labelBit,correct_bucket hK hi good])

private theorem val_or_const {α : Type*} {S : Set (α → Bool)}
    (ht : (fun _ => true) ∈ S) (hf : (fun _ => false) ∈ S) (v : Bool) : (fun _ => v) ∈ S := by
  cases v <;> assumption

private abbrev Data (r m : Nat) := (Fin m → Finset (Fin r)) × (Fin m → Finset (Fin r)) × Finset (Fin r)
private noncomputable def raw {r m : Nat} (d : Data r m) : List Bool :=
  rows d.1 ++ rows d.2.1 ++ bits d.2.2 ++ [false,true]

private theorem raw_len {r m : Nat} (d : Data r m) : (raw d).length = 2*m*r+r+2 := by
  simp [raw,rows_length,bits, Nat.add_mul, Nat.add_assoc, two_mul]

private theorem raw_Z {r m : Nat} (i : Fin m) (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.1 i)) ∈ InputSet raw (2*m*r+r+2) := by
  have base : i.val*r+j.val < m*r := by
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  apply input_mem (i := i.val*r+j.val) (by rw [two_mul, Nat.add_mul]; omega)
  intro d
  have h₁ : i.val*r+j.val < (rows d.1).length := by rw [rows_length]; exact base
  rw [raw,List.append_assoc,List.append_assoc,List.getD_append _ _ _ _ h₁]
  exact rows_getD d.1 i j

private theorem raw_O {r m : Nat} (i : Fin m) (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.2.1 i)) ∈ InputSet raw (2*m*r+r+2) := by
  have base : i.val*r+j.val < m*r := by
    have := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    omega
  apply input_mem (i := m*r+(i.val*r+j.val)) (by rw [two_mul, Nat.add_mul]; omega)
  intro d
  have h₁ : (rows d.1).length ≤ m*r+(i.val*r+j.val) := by rw [rows_length]; omega
  have h₂ : i.val*r+j.val < (rows d.2.1).length := by rw [rows_length]; exact base
  rw [raw,List.append_assoc,List.append_assoc,List.getD_append_right _ _ _ _ h₁,rows_length]
  rw [Nat.add_sub_cancel_left, List.getD_append _ _ _ _ h₂]
  exact rows_getD d.2.1 i j

private theorem raw_X {r m : Nat} (j : Fin r) :
    (fun d : Data r m => decide (j ∈ d.2.2)) ∈ InputSet raw (2*m*r+r+2) := by
  have hj := j.isLt
  apply input_mem (i := 2*m*r+j.val) (by omega)
  intro d
  have hL : (rows d.1 ++ rows d.2.1).length = 2*m*r := by simp [rows_length, two_mul, Nat.add_mul]
  have hR : j.val < (bits d.2.2).length := by simp [bits]
  unfold raw
  rw [List.append_assoc (rows d.1 ++ rows d.2.1), List.getD_append_right _ _ _ _ (by omega),hL,
    Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hR]
  exact bits_getD _ _

private theorem raw_const {r m : Nat} :
    (fun _ : Data r m => false) ∈ InputSet raw (2*m*r+r+2) ∧
    (fun _ : Data r m => true) ∈ InputSet raw (2*m*r+r+2) :=
  suffix_const (w := fun d : Data r m => rows d.1 ++ rows d.2.1 ++ bits d.2.2)
    (fun d => by simp [rows_length,bits, two_mul,Nat.add_mul,Nat.add_assoc])

private theorem fixed_X {r : Nat} (j : Fin r) :
    (fun d : Finset (Fin r) => decide (j ∈ d)) ∈ InputSet (fun d => bits d ++ [false,true]) (r+2) := by
  apply input_mem (i := j.val) (by have := j.isLt; omega)
  intro d
  rw [List.getD_append _ _ _ _ (by simp [bits])]
  exact bits_getD _ _


private theorem grow_word {α : Type*} {x : α → List Bool} {N p b r m l : Nat} {S : Set (α → Bool)}
    (H : Built x N p b S) (a f : Fin m → Nat) (Z O : α → Fin m → Finset (Fin r))
    (U : α → Finset (Fin r)) (w : Fin l → Fin m)
    (hz : ∀ i j, (fun d => decide (j ∈ Z d i)) ∈ S)
    (ho : ∀ i j, (fun d => decide (j ∈ O d i)) ∈ S)
    (hu : ∀ j, (fun d => decide (j ∈ U d)) ∈ S)
    (hf : (fun _ => false) ∈ S) (ht : (fun _ => true) ∈ S) :
    Grow x N p b S (wordCost r l (Finset.univ.sup fun i => min r (a i)) (Finset.univ.sup fun i => min r (f i)))
      (fun d => decide (WordTrace (Label a f (Z d) (O d)) (U d) w)) := by
  have ha (i : Fin l) : min r (a (w i)) ≤ Finset.univ.sup (fun j => min r (a j)) :=
    Finset.le_sup (f := fun j => min r (a j)) (Finset.mem_univ (w i))
  have hff (i : Fin l) : min r (f (w i)) ≤ Finset.univ.sup (fun j => min r (f j)) :=
    Finset.le_sup (f := fun j => min r (f j)) (Finset.mem_univ (w i))
  obtain ⟨T,build,st,word⟩ := Tables.grow H (fun d i => Z d (w i)) (fun d i => O d (w i)) U
    (fun i => min r (a (w i))) (fun i => min r (f (w i))) ha hff
    (fun i => hz (w i)) (fun i => ho (w i)) hu hf ht
  refine ⟨T,build,st,?_⟩
  convert word using 1
  funext d
  apply boolOfIff
  exact word_table_equiv a f (Z d) (O d) (U d) w

private theorem no_trace_possible {r m b : Nat} (a f : Fin m → Nat) (Z O : Fin m → Finset (Fin r))
    (h : ¬ Trace (Label a f Z O) Finset.univ (min (2^b) (r+1)+1)) : Possible b (Label a f Z O) := by
  let x : Finset (Fin r) → List Bool := fun d => bits d ++ [false,true]
  let S := InputSet x (r+2)
  have H : Built x (r+2) 0 0 S := Built.start (fun d => by simp [x,bits])
  obtain ⟨hf,ht⟩ := suffix_const (n := r) (w := bits (r := r)) (fun d => by simp [bits])
  obtain ⟨D,out,v,lt,neg,_,_,ok⟩ := realize (b := b) a f (fun _ => Z) (fun _ => O) id H ht hf (by
    intro p T l U eq hh st w
    apply grow_word hh a f (fun _ => Z) (fun _ => O) U w
    · intro i j; exact st (val_or_const ht hf _)
    · intro i j; exact st (val_or_const ht hf _)
    · intro j
      rcases eq with rfl | rfl
      · exact st (fixed_X j)
      · exact st (val_or_const ht hf _)
    · exact st hf
    · exact st ht)
  exact ⟨D,out,v,lt,neg,fun X => ok X h⟩

private theorem solve (r m b : Nat) (a f : Fin m → Nat) :
    let K := min (2^b) (r+1)
    let A := Finset.univ.sup (fun i => min r (a i))
    let F := Finset.univ.sup (fun i => min r (f i))
    let n := 2*m*r+r
    ∃ (D : Circuit) (out : Fin m → Nat), Valid n D ∧
      (∀ j, out j < n+2+D.size) ∧ notCount D ≤ b ∧ D.size-notCount D ≤ sizeBound r m K A F ∧
      ∀ (Z O : Fin m → Finset (Fin r)) (X : Finset (Fin r)),
        (D.eval (raw (Z,O,X)) = false ↔ Possible b (Label a f Z O)) ∧
        (Possible b (Label a f Z O) → ∀ i, Label a f Z O X i → ∀ j,
          (D.wires (raw (Z,O,X))).getD (out j) false = labelBit i j) := by
  dsimp only
  obtain ⟨hf,ht⟩ := raw_const (r := r) (m := m)
  obtain ⟨D,out,v,lt,neg,pos,test,ok⟩ := realize (b := b) a f Prod.fst (fun d : Data r m => d.2.1)
    (fun d => d.2.2) (Built.start raw_len) ht hf (by
    intro p T l U eq hh st w
    apply grow_word hh a f Prod.fst (fun d : Data r m => d.2.1) U w
    · intro i j; exact st (raw_Z i j)
    · intro i j; exact st (raw_O i j)
    · intro j
      rcases eq with rfl | rfl
      · exact st (raw_X j)
      · exact st (val_or_const ht hf _)
    · exact st hf
    · exact st ht)
  refine ⟨D,out,v,lt,neg,pos,fun Z O X => ⟨?_,?_⟩⟩
  · exact (test (Z,O,X)).trans ⟨no_trace_possible a f Z O, possible_no_trace⟩
  · exact fun p => ok (Z,O,X) (possible_no_trace p)

end PEqualNP.Outside.L_lib_1424_aux


theorem PEqualNP.Outside.L_lib_1424 : (
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
let bits := fun {n : Nat} (X : Finset (Fin n)) => List.ofFn (fun j : Fin n => decide (j ∈ X))
let near := fun {r : Nat} (a f : Nat) (C Y : Finset (Fin r)) => (C \ Y).card ≤ a ∧ (Y \ C).card ≤ f
let rows := fun {k r : Nat} (W : Fin k → Finset (Fin r)) => (List.ofFn (fun j => bits (W j))).flatten
let possible := fun {r m : Nat} (b : Nat) (lab : Finset (Fin r) → Fin m → Prop) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid r D ∧
    (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧
    ∀ X i, lab X i → ∀ j, (D.wires (bits X ++ [false,true])).getD (out j) false = decide (i=j)
∀ (r m b : Nat) (a f : Fin m → Nat),
  let K := min (2^b) (r+1)
  let A := Finset.univ.sup (fun i => min r (a i))
  let F := Finset.univ.sup (fun i => min r (f i))
  let n := 2*m*r+r
  let B := 128*(r+2)*(K+3)^3*((m+1)*(A+1)*(F+1))^(K+1)
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin m → Nat), valid n D ∧
    (∀ j, out j < n+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ B ∧
    ∀ (Z O : Fin m → Finset (Fin r)) (X : Finset (Fin r)),
      let lab := fun (Y : Finset (Fin r)) (i : Fin m) => ∃ C : Finset (Fin r),
        (Finset.univ \ C) ⊆ Z i ∧ C ⊆ O i ∧ near (a i) (f i) C Y
      let I := rows Z ++ rows O ++ bits X ++ [false,true]
      (D.eval I = false ↔ possible b lab) ∧
      (possible b lab → ∀ i, lab X i → ∀ j, (D.wires I).getD (out j) false = decide (i=j))
) := by
  dsimp only
  intro r m b a f
  obtain ⟨D,out,hv,hr,hn,hp,correct⟩ := PEqualNP.Outside.L_lib_1424_aux.solve r m b a f
  refine ⟨D,out,hv,hr,hn,hp,?_⟩
  intro Z O X
  have H := correct Z O X
  unfold PEqualNP.Outside.L_lib_1424_aux.raw PEqualNP.Outside.L_lib_1424_aux.rows
    PEqualNP.Outside.L_lib_1424_aux.Possible PEqualNP.Outside.L_lib_1424_aux.Valid
    PEqualNP.Outside.L_lib_1424_aux.Label PEqualNP.Outside.L_lib_1424_aux.Near
    PEqualNP.Outside.L_lib_1424_aux.bits PEqualNP.Outside.L_lib_1424_aux.labelBit at H
  dsimp only at H
  have hsd (C Y : Finset (Fin r)) :
      @SDiff.sdiff (Finset (Fin r))
        (@Finset.instSDiff (Fin r) (fun u v => Classical.propDecidable (u=v))) C Y = C \ Y := by
    ext i
    simp only [Finset.mem_sdiff]
  simp only [hsd]
  exact H
