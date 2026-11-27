import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_063_aux.Main

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev Sig (m : ℕ) := (Fin m → Bool) → Bool

def Scheduled (m : ℕ) (k q : ℕ) (S : Set (Sig m)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ q ∧ ReadsBack m ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < m + k ∧
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem startSched (m : ℕ) :
    Scheduled m 0 0 (Set.range (fun i : Fin m => fun x : Fin m → Bool => x i)) := by
  refine ⟨[], rfl, by decide, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem realizeDeps {m k : ℕ} {S : Set (Sig m)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < m + k ∧
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig m)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < m + k) ∧
      ∀ x : Fin m → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

def ncost (op : GateOp) : Nat := match op with | .not => 1 | _ => 0

theorem pushSched {m k q : ℕ} {S : Set (Sig m)}
    (h : Scheduled m k q S) (op : GateOp) (deps : List (Sig m)) (out : Sig m)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled m (k + 1) (q + ncost op) (insert out S) := by
  obtain ⟨gs, hgs, hq, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin m → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = m + k := by
    rw [wireLength]; simpa using congrArg (m + ·) hgs
  have hsnoc (x : Fin m → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_, ?_⟩
  · unfold PEqualNP.NotBracket.notCount at hq ⊢
    cases op <;> simp [g, ncost] at * <;> omega
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by change is.length ≤ 2; simpa only [his] using hlen⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨m + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

theorem finishMulti {m k n q : ℕ} {S : Set (Sig m)}
    (h : Scheduled m k q S) (out : Sig m) (hout : out ∈ S)
    (bits : Fin n → Sig m) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (outBit : Fin n → Fin (m + C.size)),
      C.size = k ∧ PEqualNP.NotBracket.notCount C ≤ q ∧ ReadsBack m C ∧ FanInTwo C ∧ C.output < m + C.size ∧
      (∀ x : Fin m → Bool, C.eval (List.ofFn x) = out x) ∧
      (∀ (p : Fin n) (x : Fin m → Bool),
        (C.wires (List.ofFn x)).getD (outBit p).val false = bits p x) := by
  obtain ⟨gs, hgs, hq, hr, hf, hw⟩ := h
  obtain ⟨i0, hi0, hval0⟩ := hw out hout
  have hcho : ∀ p : Fin n, ∃ i : Fin (m + gs.length),
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨⟨i, by omega⟩, hv⟩
  choose outBit houtBit using hcho
  exact ⟨⟨gs, i0⟩, outBit, hgs, hq, hr, hf, by change i0 < m + gs.length; omega, hval0, houtBit⟩

structure Build {m : ℕ} (A B : Set (Sig m)) (b r : ℕ) : Prop where
  run : ∀ {k q : ℕ} {S : Set (Sig m)}, Scheduled m k q S → A ⊆ S →
    ∃ c ≤ b, Scheduled m (k + c) (q + r) (S ∪ B)

theorem idleB {m : ℕ} {A B : Set (Sig m)} (h : B ⊆ A) : Build A B 0 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

theorem relaxB {m : ℕ} {A A' B B' : Set (Sig m)} {b b' r r' : ℕ}
    (H : Build A B b r) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') (hr' : r ≤ r') : Build A' B' b' r' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hq, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hq.trans (Nat.add_le_add_left hr' _), hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)⟩

theorem seqB {m : ℕ} {A B C : Set (Sig m)} {b c p q : ℕ}
    (H1 : Build A B b p) (H2 : Build (A ∪ B) C c q) : Build A (B ∪ C) (b + c) (p + q) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1 (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

theorem gateB {m : ℕ} {A : Set (Sig m)} (op : GateOp) (deps : List (Sig m)) (out : Sig m)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 (ncost op) :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩⟩

theorem constB {m : ℕ} {A : Set (Sig m)} (b : Bool) : Build A {fun _ => b} 1 0 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

theorem notB {m : ℕ} {A : Set (Sig m)} {f : Sig m} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

theorem andB {m : ℕ} {A : Set (Sig m)} {f g : Sig m} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 0 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem orB {m : ℕ} {A : Set (Sig m)} {f g : Sig m} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 0 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem listB {m : ℕ} {α : Type*} {A : Set (Sig m)} (F : α → Set (Sig m)) (c p : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c p) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) (xs.length * p) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) (xs.length * p) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb))) Set.subset_union_left Set.subset_union_right le_rfl le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm]) (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

theorem orListB {m : ℕ} {A : Set (Sig m)} (xs : List (Sig m))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length 0 := by
  induction xs with
  | nil =>
    exact idleB (by simpa using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.any (fun g => g x)})
        {fun x => (f :: xs).any (fun g => g x)} 1 0 := by
      have heq : (fun x => (f :: xs).any (fun g => g x)) =
          (fun x => f x || xs.any (fun g => g x)) := by
        funext x; simp [List.any_cons]
      rw [heq]
      exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp) (by simp)


end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux.Main
theorem andListB {m : ℕ} {A : Set (Sig m)} (xs : List (Sig m))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length 0 := by
  induction xs with
  | nil =>
    exact idleB (by simpa using htrue)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.all (fun g => g x)})
        {fun x => (f :: xs).all (fun g => g x)} 1 0 := by
      have heq : (fun x => (f :: xs).all (fun g => g x)) =
          (fun x => f x && xs.all (fun g => g x)) := by
        funext x; simp [List.all_cons]
      rw [heq]
      exact andB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp) (by simp)


noncomputable def anyS {m : ℕ} {α : Type*} (s : Finset α) (f : α → Sig m) : Sig m :=
  fun x => s.toList.any (fun a => f a x)

noncomputable def allS {m : ℕ} {α : Type*} (s : Finset α) (f : α → Sig m) : Sig m :=
  fun x => s.toList.all (fun a => f a x)

theorem anyS_true {m : ℕ} {α : Type*} (s : Finset α) (f : α → Sig m) (x) :
    anyS s f x = true ↔ ∃ a ∈ s, f a x = true := by simp [anyS]

theorem allS_true {m : ℕ} {α : Type*} (s : Finset α) (f : α → Sig m) (x) :
    allS s f x = true ↔ ∀ a ∈ s, f a x = true := by simp [allS]

theorem anySB {m : ℕ} {α : Type*} {A : Set (Sig m)} (s : Finset α) (f : α → Sig m)
    (h : ∀ a ∈ s, f a ∈ A) : Build A {anyS s f} (s.card + 1) 0 := by
  classical
  have c := constB (A:=A) false
  have r := orListB (A:=A ∪ {fun _ => false}) (s.toList.map f)
    (by simp only [List.mem_map, Finset.mem_toList]; rintro _ ⟨a,ha,rfl⟩; exact Or.inl (h a ha))
    (Or.inr rfl)
  apply relaxB (seqB c r) le_rfl _ (by simp [Nat.add_comm]) (by simp)
  intro v hv
  obtain rfl : v = anyS s f := hv
  exact Or.inr (Or.inr (by simp [List.any_map, Function.comp_def]; rfl))

theorem allSB {m : ℕ} {α : Type*} {A : Set (Sig m)} (s : Finset α) (f : α → Sig m)
    (h : ∀ a ∈ s, f a ∈ A) : Build A {allS s f} (s.card + 1) 0 := by
  classical
  have c := constB (A:=A) true
  have r := andListB (A:=A ∪ {fun _ => true}) (s.toList.map f)
    (by simp only [List.mem_map, Finset.mem_toList]; rintro _ ⟨a,ha,rfl⟩; exact Or.inl (h a ha))
    (Or.inr rfl)
  apply relaxB (seqB c r) le_rfl _ (by simp [Nat.add_comm]) (by simp)
  intro v hv
  obtain rfl : v = allS s f := hv
  exact Or.inr (Or.inr (by simp [List.all_map, Function.comp_def]; rfl))

theorem batchSet {m : ℕ} {α : Type*} {A : Set (Sig m)} (s : Finset α) (F : α → Set (Sig m)) (cost : α → ℕ)
    (hs : ∀ i ∈ s, Build A (F i) (cost i) 0) :
    Build A (⋃ i ∈ s, F i) (∑ i ∈ s, cost i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact idleB (by simp)
  | @insert i s hi ih =>
    have pre := hs i (by simp)
    have rest := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    have tail := relaxB rest (A':=A ∪ F i) (B':=⋃ j ∈ s, F j)
      Set.subset_union_left Set.subset_union_right le_rfl le_rfl
    apply relaxB (seqB pre tail) le_rfl _ (by simp [hi]) (by simp)
    intro z hz
    simp only [Set.mem_iUnion, Finset.mem_insert] at hz
    rcases hz with ⟨j, rfl | hj, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,h⟩⟩))

theorem batch {m : ℕ} {α : Type*} [Fintype α] {A : Set (Sig m)} (f : α → Sig m) (cost : α → ℕ)
    (hs : ∀ i, Build A {f i} (cost i) 0) :
    Build A (Set.range f) (∑ i, cost i) 0 := by
  apply relaxB (batchSet Finset.univ (fun i => {f i}) cost (fun i _ => hs i)) le_rfl _ le_rfl le_rfl
  rintro _ ⟨i,rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_univ _,rfl⟩⟩)

end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux
abbrev Word (n : Nat) := Fin n → Bool

def weight {n : Nat} (x : Word n) : Nat :=
  ∑ i, if x i then 1 else 0

theorem weightCons {n : Nat} (b : Bool) (x : Word n) :
    weight (Fin.cons b x) = (if b then 1 else 0) + weight x := by
  simp only [weight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

def newHead (b : Bool) (r l n : Nat) : Bool := b && decide (r + l < n)

def chainTag : (n : Nat) → Word n → Word n
  | 0, x => x
  | n+1, x =>
    let z := Fin.tail x
    let t := chainTag n z
    Fin.cons (newHead (x 0) (weight z) (weight t) n) t

theorem tagCons {n : Nat} (b : Bool) (x : Word n) :
    chainTag (n+1) (Fin.cons b x) =
      Fin.cons (newHead b (weight x) (weight (chainTag n x)) n) (chainTag n x) := by
  simp [chainTag]

theorem tagBounds (n : Nat) (x : Word n) :
    weight (chainTag n x) ≤ weight x ∧ weight x + weight (chainTag n x) ≤ n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    obtain ⟨b, x, rfl⟩ := Fin.exists_cons x
    obtain ⟨h1,h2⟩ := ih x
    cases b <;> simp only [tagCons, weightCons, newHead, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ite_false, ite_true, Bool.decide_iff]
    all_goals (try split_ifs) <;> omega

theorem tagLayer (n : Nat) (x : Word n) (k : Nat)
    (hl : weight (chainTag n x) ≤ k) (hu : k + weight (chainTag n x) ≤ n) :
    ∃ y, chainTag n y = chainTag n x ∧ weight y = k := by
  induction n generalizing k with
  | zero =>
    have h : k = 0 := by omega
    exact ⟨x, rfl, by simp [weight, h]⟩
  | succ n ih =>
    obtain ⟨b, x, rfl⟩ := Fin.exists_cons x
    simp only [tagCons, weightCons] at hl hu
    rw [tagCons]
    obtain ⟨h1,h2⟩ := tagBounds n x
    generalize hc : newHead b (weight x) (weight (chainTag n x)) n = c at *
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ite_false, zero_add] at hl hu
      by_cases h : k + weight (chainTag n x) ≤ n
      · obtain ⟨y,hy,hw⟩ := ih x k hl h
        exact ⟨Fin.cons false y, by simp [tagCons, hy, newHead], by simp [weightCons, hw]⟩
      · have htop : k = (n - weight (chainTag n x)) + 1 := by omega
        obtain ⟨y,hy,hw⟩ := ih x (n-weight (chainTag n x)) (by omega) (by omega)
        have he : ¬ (weight y + weight (chainTag n x) < n) := by omega
        exact ⟨Fin.cons true y, by simp [tagCons, hy, newHead, he], by simp [weightCons, hw, htop, Nat.add_comm]⟩
    | true =>
      simp only [ite_true] at hl hu
      obtain ⟨y,hy,hw⟩ := ih x (k-1) (by omega) (by omega)
      have he : weight y + weight (chainTag n x) < n := by omega
      exact ⟨Fin.cons true y, by simp [tagCons, hy, newHead, he], by simp only [weightCons, ite_true]; omega⟩

theorem tagOrder (n : Nat) (x y : Word n) (ht : chainTag n x = chainTag n y)
    (hle : weight x ≤ weight y) : x ≤ y := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a, x, rfl⟩ := Fin.exists_cons x
    obtain ⟨b, y, rfl⟩ := Fin.exists_cons y
    simp only [tagCons, Fin.cons_inj] at ht
    obtain ⟨hc,ht⟩ := ht
    obtain ⟨h1,h2⟩ := tagBounds n x
    obtain ⟨h3,h4⟩ := tagBounds n y
    rw [ht] at h1 h2 hc
    apply Fin.cons_le_cons.mpr
    cases a <;> cases b <;> simp [weightCons] at hle <;> simp [newHead] at hc
    all_goals first | exact ⟨by decide, ih x y ht (by omega)⟩ | omega

def support {n : Nat} (x : Word n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

theorem supportWeight {n : Nat} (x : Word n) : (support x).card = weight x := by
  simp only [weight, support, Finset.sum_boole, Nat.cast_id]

theorem supportInj {n : Nat} : Function.Injective (@support n) := by
  intro x y h
  funext i
  have hi : (i ∈ support x) = (i ∈ support y) := congrArg (fun s : Finset (Fin n) => i ∈ s) h
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  cases hx : x i <;> cases hy : y i <;> simp_all

theorem chainColor (n : Nat) :
    ∃ color : Word n → Fin (Nat.choose n (n / 2)),
      ∀ x y, color x = color y → x ≤ y ∨ y ≤ x := by
  classical
  let T := {t : Word n // ∃ x, chainTag n x = t}
  let tOf (x : Word n) : T := ⟨chainTag n x, x, rfl⟩
  have hc (t : T) : ∃ y : Word n, chainTag n y = t.val ∧ weight y = n/2 := by
    obtain ⟨x,h⟩ := t.property
    obtain ⟨h1,h2⟩ := tagBounds n x
    obtain ⟨y,hy,hw⟩ := tagLayer n x (n/2) (by omega) (by omega)
    exact ⟨y,hy.trans h,hw⟩
  let mid (t : T) := Classical.choose (hc t)
  have hm (t : T) : chainTag n (mid t) = t.val ∧ weight (mid t) = n/2 :=
    Classical.choose_spec (hc t)
  let rep (t : T) : {s : Finset (Fin n) // s.card = n/2} :=
    ⟨support (mid t), (supportWeight _).trans (hm t).2⟩
  let e := Fintype.equivFinOfCardEq (α := {s : Finset (Fin n) // s.card = n/2})
    (by simp :
      Fintype.card {s : Finset (Fin n) // s.card = n/2} = Nat.choose n (n/2))
  refine ⟨fun x => e (rep (tOf x)), ?_⟩
  intro x y he
  have hr := congrArg Subtype.val (e.injective he)
  have hmid := supportInj (show support (mid (tOf x)) = support (mid (tOf y)) from hr)
  have htag : chainTag n x = chainTag n y :=
    (hm (tOf x)).1.symm.trans ((congrArg (chainTag n) hmid).trans (hm (tOf y)).1)
  rcases le_total (weight x) (weight y) with h | h
  · exact Or.inl (tagOrder n x y htag h)
  · exact Or.inr (tagOrder n y x htag.symm h)

theorem chainHasGreatest {n : Nat} (s : Finset (Word n)) (hne : s.Nonempty)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  obtain ⟨x,hx⟩ := s.exists_maximal hne
  refine ⟨x, hx.1, ?_⟩
  intro y hy
  exact (hc y hy x hx.1).elim id (hx.2 hy)

theorem chainOR {n : Nat} (s : Finset (Word n)) (hne : s.Nonempty)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x) :
    ∃ x ∈ s, ∀ i, (∃ y ∈ s, y i = true) ↔ x i = true := by
  obtain ⟨x,hx,hm⟩ := chainHasGreatest s hne hc
  refine ⟨x,hx,fun i => ⟨?_,fun hi => ⟨x,hx,hi⟩⟩⟩
  rintro ⟨y,hy,hi⟩
  have hl := hm y hy i
  cases he : x i
  · rw [hi, he] at hl
    exact False.elim ((by decide : ¬ (true ≤ false)) hl)
  · rfl

end PEqualNP.Outside.L_clb_063_aux

namespace PEqualNP.Outside.L_clb_063_aux.Main

private theorem selectKeep {m b h} {A B A' : Set (Sig m)} (H : Build A B b h)
    (inc : A ⊆ A') : Build A' (A' ∪ B) b h :=
  relaxB H inc le_rfl le_rfl le_rfl

private theorem selectTrans {m b c h t} {A B C : Set (Sig m)}
    (H : Build A B b h) (K : Build B C c t) : Build A C (b+c) (h+t) :=
  relaxB (seqB H (relaxB K Set.subset_union_right Set.subset_union_right le_rfl le_rfl))
    le_rfl (fun _ hc => Or.inr (Or.inr hc)) le_rfl le_rfl

private theorem selectRange {m n} {A : Set (Sig m)} (f : Fin n → Sig m)
    (H : ∀ i, Build A {f i} 1 0) : Build A (Set.range f) n 0 := by
  have h := listB (fun i => ({f i} : Set (Sig m))) 1 0 (List.finRange n) (fun i _ => H i)
  refine relaxB h le_rfl ?_ (by simp) (by simp)
  rintro _ ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simp, rfl⟩⟩)

theorem selectTree {m : ℕ} (d : ℕ) (a : Fin (2^d) → Sig m) :
    ∃ (enable : Fin (2^d) → Sig m) (root : Sig m),
      Build (Set.range a) (insert root (Set.range enable)) (6 * (2^d - 1)) d ∧
      ∀ x, (root x = true ↔ ∃ j, a j x = true) ∧
        (root x = true → ∃ j, a j x = true ∧ ∀ k, enable k x = decide (k = j)) := by
  induction d with
  | zero =>
    letI : Subsingleton (Fin (2^0)) := inferInstanceAs (Subsingleton (Fin 1))
    let z : Fin (2^0) := 0
    refine ⟨a, a z, idleB ?_, ?_⟩
    · exact Set.insert_subset (Set.mem_range_self z) le_rfl
    · intro x
      constructor
      · constructor
        · exact fun h => ⟨z, h⟩
        · rintro ⟨j, hj⟩
          simpa [Subsingleton.elim j z] using hj
      · intro h
        refine ⟨z, h, fun k => ?_⟩
        simpa [Subsingleton.elim k z] using h
  | succ d ih =>
    let N := 2^d
    let e : Fin N ⊕ Fin N ≃ Fin (2^(d+1)) :=
      finSumFinEquiv.trans (finCongr (by dsimp [N]; rw [Nat.pow_succ]; omega))
    let pair : Fin N → Sig m := fun i x => a (e (.inl i)) x || a (e (.inr i)) x
    obtain ⟨p, root, hp, hspec⟩ := ih pair
    let left : Fin N → Sig m := fun i x => p i x && a (e (.inl i)) x
    let lAny : Sig m := fun x => (List.ofFn left).any (fun f => f x)
    let inv : Sig m := fun x => !(lAny x)
    let right : Fin N → Sig m := fun i x => p i x && inv x
    let enable : Fin (2^(d+1)) → Sig m := fun j => Sum.elim left right (e.symm j)
    refine ⟨enable, root, ?_, ?_⟩
    · let A := Set.range a
      let P := Set.range pair
      let O := insert root (Set.range p)
      let S1 := A ∪ P
      let S2 := S1 ∪ O
      let S3 := S2 ∪ Set.range left
      let S4 := S3 ∪ {((fun _ => false) : Sig m)}
      let S5 := S4 ∪ {lAny}
      let S6 := S5 ∪ {inv}
      have h1 : Build A S1 N 0 := selectKeep (selectRange pair (fun i =>
        orB (Set.mem_range_self (e (.inl i))) (Set.mem_range_self (e (.inr i))))) le_rfl
      have h2 : Build S1 S2 (6*(2^d-1)) d := selectKeep hp Set.subset_union_right
      have h3 : Build S2 S3 N 0 := selectKeep (selectRange left (fun i =>
        andB (Or.inr (Set.mem_insert_of_mem _ (Set.mem_range_self i)) : p i ∈ S2)
          (Or.inl (Or.inl (Set.mem_range_self (e (.inl i)))) : a (e (.inl i)) ∈ S2))) le_rfl
      have h4 : Build S3 S4 1 0 := selectKeep (constB false) le_rfl
      have h5 : Build S4 S5 N 0 := by
        have h := orListB (List.ofFn left)
          (A:=S4) (fun f hf => Or.inl (Or.inr (List.mem_ofFn.mp hf)))
          (Or.inr rfl)
        simpa only [List.length_ofFn] using selectKeep h le_rfl
      have h6 : Build S5 S6 1 1 := selectKeep (notB (Or.inr rfl : lAny ∈ S5)) le_rfl
      have h7 : Build S6 (S6 ∪ Set.range right) N 0 :=
        selectKeep (selectRange right (fun i => andB
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_insert_of_mem _ (Set.mem_range_self i)))))) : p i ∈ S6)
          (Or.inr rfl : inv ∈ S6))) le_rfl
      have hc := selectTrans (selectTrans (selectTrans (selectTrans (selectTrans (selectTrans h1 h2) h3) h4) h5) h6) h7
      refine relaxB hc le_rfl ?_ ?_ (by omega)
      · intro f hf
        rcases Set.mem_insert_iff.mp hf with rfl | ⟨j, rfl⟩
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_insert _ _)))))))
        · obtain ⟨s, rfl⟩ := e.surjective j
          cases s with
          | inl i =>
            exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simpa [enable] using Set.mem_range_self (f:=left) i))))))
          | inr i =>
            exact Or.inr (Or.inr (by simpa [enable] using Set.mem_range_self (f:=right) i))
      · have hn : 0 < 2^d := Nat.two_pow_pos _
        dsimp [N]
        rw [Nat.pow_succ]
        omega
    · intro x
      obtain ⟨ex, unique⟩ := hspec x
      constructor
      · rw [ex]
        constructor
        · rintro ⟨i, hi⟩
          rcases Bool.or_eq_true_iff.mp hi with hl | hr
          · exact ⟨e (.inl i), hl⟩
          · exact ⟨e (.inr i), hr⟩
        · rintro ⟨j, hj⟩
          obtain ⟨s, rfl⟩ := e.surjective j
          cases s with
          | inl i => exact ⟨i, Bool.or_eq_true_iff.mpr (Or.inl hj)⟩
          | inr i => exact ⟨i, Bool.or_eq_true_iff.mpr (Or.inr hj)⟩
      · intro hr
        obtain ⟨i, ha, alone⟩ := unique hr
        have hva : lAny x = true ↔ a (e (.inl i)) x = true := by
          change (List.ofFn left).any (fun f => f x) = true ↔ _
          simp only [List.any_eq_true, List.mem_ofFn]
          constructor
          · rintro ⟨f, ⟨j,rfl⟩, hj⟩
            obtain ⟨hpj, hval⟩ := Bool.and_eq_true_iff.mp hj
            have eq : j = i := of_decide_eq_true (by simpa only [← alone j] using hpj)
            simpa [eq] using hval
          · intro hi
            exact ⟨left i, ⟨i, rfl⟩, by simp [left, alone, hi]⟩
        cases hl : a (e (.inl i)) x with
        | true =>
          have lon := hva.mpr hl
          refine ⟨e (.inl i), hl, ?_⟩
          intro k
          obtain ⟨s, rfl⟩ := e.surjective k
          cases s with
          | inl j =>
            by_cases h : j = i
            · subst j; simp [enable, left, alone, hl]
            · simp [enable, left, alone, h]
          | inr j => simp [enable, right, inv, lon]
        | false =>
          have loff : lAny x = false := by cases h : lAny x <;> simp_all
          have har : a (e (.inr i)) x = true := by simpa [pair, hl] using ha
          refine ⟨e (.inr i), har, ?_⟩
          intro k
          obtain ⟨s, rfl⟩ := e.surjective k
          cases s with
          | inl j =>
            by_cases h : j = i
            · subst j; simp [enable, left, alone, hl]
            · simp [enable, left, alone, h]
          | inr j => simp [enable, right, inv, loff, alone]
end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux.Main

abbrev Word (n : Nat) := Fin n → Bool

noncomputable def fiber {n P : Nat} (color : Word n → Fin P) (i : Fin P) : Finset (Word n) :=
  Finset.univ.filter (fun u => color u = i)

noncomputable def avail {m n P : Nat} (color : Word n → Fin P) (f : Word n → Sig m) (i : Fin P) : Sig m :=
  anyS (fiber color i) f

noncomputable def leafBit {m n P : Nat} (color : Word n → Fin P) (f : Word n → Sig m)
    (i : Fin P) (j : Fin n) : Sig m :=
  anyS ((fiber color i).filter (fun u => u j = true)) f

theorem fiber_sum {n P : Nat} (color : Word n → Fin P) :
    ∑ i, (fiber color i).card = 2 ^ n := by
  classical
  simpa [fiber, Word] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Word n)) (Finset.univ : Finset (Fin P)) color

theorem stage {m n P : Nat} (color : Word n → Fin P) (f : Word n → Sig m) :
    Build (Set.range f)
      (Set.range (avail color f) ∪ Set.range (fun p : Fin P × Fin n => leafBit color f p.1 p.2))
      ((n+1)*(2^n + P)) 0 := by
  classical
  let cost (i : Fin P) := (fiber color i).card + 1
  have sumCost : (∑ i, cost i) = 2 ^ n + P := by simp [cost, Finset.sum_add_distrib, fiber_sum]
  have ba : Build (Set.range f) (Set.range (avail color f)) (∑ i, cost i) 0 :=
    batch _ cost (fun i => anySB _ f (fun x _ => ⟨x,rfl⟩))
  have single (p : Fin P × Fin n) :
      Build (Set.range f ∪ Set.range (avail color f)) {leafBit color f p.1 p.2} (cost p.1) 0 := by
    apply relaxB (anySB (A:=Set.range f) ((fiber color p.1).filter (fun u => u p.2 = true))
      f (fun x _ => ⟨x,rfl⟩)) Set.subset_union_left Set.subset_union_right _ le_rfl
    exact Nat.add_le_add_right (Finset.card_filter_le _ _) _
  have bb := batch (fun p : Fin P × Fin n => leafBit color f p.1 p.2) (fun p => cost p.1) single
  have sumSecond : (∑ p : Fin P × Fin n, cost p.1) = n * (2^n + P) := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, sumCost]
  apply relaxB (seqB ba bb) le_rfl Set.subset_union_right _ (by simp)
  rw [sumCost, sumSecond, Nat.add_mul, Nat.one_mul]; omega

theorem avail_true {m n P : Nat} (color : Word n → Fin P) (f : Word n → Sig m) (x) :
    (∃ i, avail color f i x = true) ↔ ∃ u, f u x = true := by
  constructor
  · rintro ⟨i,h⟩
    obtain ⟨u,_,hu⟩ := (anyS_true _ _ _).mp h
    exact ⟨u,hu⟩
  · rintro ⟨u,hu⟩
    exact ⟨color u,(anyS_true _ _ _).mpr ⟨u,by simp [fiber],hu⟩⟩

theorem leaf_feasible {m n P : Nat} (color : Word n → Fin P) (f : Word n → Sig m)
    (chain : ∀ a b, color a = color b → a ≤ b ∨ b ≤ a)
    (i : Fin P) (x) (hi : avail color f i x = true) :
    f (fun j => leafBit color f i j x) x = true := by
  classical
  let s := (fiber color i).filter (fun u => f u x = true)
  have hn : s.Nonempty := by
    obtain ⟨u,hu,hv⟩ := (anyS_true _ _ _).mp hi
    exact ⟨u,Finset.mem_filter.mpr ⟨hu,hv⟩⟩
  have hc : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a := by
    intro a ha b hb
    have h1 := (Finset.mem_filter.mp ha).1
    have h2 := (Finset.mem_filter.mp hb).1
    exact chain a b ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
  obtain ⟨u,hu,hh⟩ := PEqualNP.Outside.L_clb_063_aux.chainOR s hn hc
  have heq : (fun j => leafBit color f i j x) = u := by
    funext j
    apply Bool.eq_iff_iff.mpr
    rw [leafBit, anyS_true, ← hh j]
    simp [s, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact (Finset.mem_filter.mp hu).2

end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux.Main

noncomputable def pickedBit {m P n : ℕ} (en : Fin P → Sig m)
    (v : Fin P → Fin n → Sig m) (j : Fin n) : Sig m :=
  anyS Finset.univ (fun i x => en i x && v i j x)

theorem buildPicked {m P n : ℕ} {A : Set (Sig m)} (en : Fin P → Sig m)
    (v : Fin P → Fin n → Sig m) (hen : ∀ i, en i ∈ A) (hv : ∀ i j, v i j ∈ A) :
    Build A (Set.range (pickedBit en v)) (n * (2 * P + 1)) 0 := by
  classical
  have hbit (j : Fin n) : Build A {pickedBit en v j} (2 * P + 1) 0 := by
    let masked : Fin P → Sig m := fun i x => en i x && v i j x
    have masks : Build A (Set.range masked) P 0 := by
      simpa using batch masked (fun _ => 1) (fun i => andB (hen i) (hv i j))
    have pool := anySB (A:=A ∪ Set.range masked) Finset.univ masked
      (fun i _ => Or.inr (Set.mem_range_self i))
    refine relaxB (seqB masks pool) le_rfl ?_ (by simp; omega) (by simp)
    exact fun _ h => Or.inr (Or.inr h)
  simpa using batch (pickedBit en v) (fun _ => 2 * P + 1) hbit

theorem pickedBit_eq {m P n : ℕ} (en : Fin P → Sig m) (v : Fin P → Fin n → Sig m)
    (x : Fin m → Bool) (i : Fin P) (h : ∀ k, en k x = decide (k = i)) (j : Fin n) :
    pickedBit en v j x = v i j x := by
  have iffTrue : pickedBit en v j x = true ↔ v i j x = true := by
    unfold pickedBit
    rw [anyS_true]
    constructor
    · rintro ⟨k, _, hk⟩
      obtain ⟨enabled, hits⟩ := Bool.and_eq_true_iff.mp hk
      have equal : k = i := of_decide_eq_true (by simpa only [← h k] using enabled)
      simpa only [equal] using hits
    · intro hv
      exact ⟨i, Finset.mem_univ i, by simp [h, hv]⟩
  cases ha : pickedBit en v j x <;> cases hb : v i j x <;> simp_all

end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux.Main

def rawSig (m : ℕ) : Set (Sig m) := Set.range (fun i : Fin m => fun x : Fin m → Bool => x i)

def tableInputs {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w+1) → Bool) → Bool)
    (a : Fin (n * 2^(w+1))) : Bool :=
  table ⟨(a.val / 2^(w+1)) % n, Nat.mod_lt _ hn⟩ (fun j => a.val.testBit j.val)

def window {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (i : Fin n) (j : Fin (w+1)) : Bool :=
  word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def windowCode {w : ℕ} (v : Fin (w+1) → Bool) : Fin (2^(w+1)) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn v)).toNat, by
    simpa using (BitVec.ofBoolListLE (List.ofFn v)).isLt⟩

theorem windowCodeBit {w : ℕ} (v : Fin (w+1) → Bool) (j : Fin (w+1)) :
    (windowCode v).val.testBit j.val = v j := by
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD j.val = v j
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]

def windowAddress {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (i : Fin n) :
    Fin (n * 2^(w+1)) :=
  let c := windowCode (w:=w) (window hn word i)
  ⟨i.val * 2^(w+1) + c.val, by
    have h := Nat.mul_le_mul_right (2^(w+1)) (show i.val+1 ≤ n from i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at h
    have h' := c.isLt
    omega⟩

theorem windowRead {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w+1) → Bool) → Bool) (word : Fin n → Bool) (i : Fin n) :
    tableInputs hn table (windowAddress hn word i) = table i (window hn word i) := by
  let c := windowCode (w:=w) (window hn word i)
  have hdiv : (i.val * 2^(w+1) + c.val) / 2^(w+1) = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt c.isLt, Nat.zero_add]
  have hbit (j : Fin (w+1)) : (i.val * 2^(w+1) + c.val).testBit j.val = (window hn word i) j := by
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ c.isLt, ite_eq_left j.isLt]
    exact windowCodeBit _ _
  change table ⟨((i.val * 2^(w+1) + c.val) / 2^(w+1)) % n, _⟩
    (fun j => (i.val * 2^(w+1) + c.val).testBit j.val) = _
  simp [hdiv, Nat.mod_eq_of_lt i.isLt, hbit]

noncomputable def feas {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) : Sig (n * 2^(w+1)) :=
  allS Finset.univ (fun i x => x (windowAddress hn word i))

theorem feas_correct {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w+1) → Bool) → Bool) (word : Fin n → Bool) :
    feas hn word (tableInputs hn table) = true ↔
    ∀ i : Fin n, table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
  change _ ↔ ∀ i, table i (window hn word i) = true
  simp [feas, allS_true, windowRead]

theorem feasBuild {n w : ℕ} (hn : 0 < n) :
    Build (rawSig _) (Set.range (feas (w:=w) hn)) ((n+1)*2^n) 0 := by
  classical
  have h (word : Fin n → Bool) : Build (rawSig _) {feas (w:=w) hn word} (n+1) 0 := by
    simpa [feas] using (allSB (A:=rawSig (n*2^(w+1))) Finset.univ
      (fun i x => x (windowAddress hn word i))
      (fun i _ => Set.mem_range_self (windowAddress hn word i)))
  simpa [Nat.mul_comm] using (batch (feas (w:=w) hn) (fun _ => n+1) h)

end PEqualNP.Outside.L_clb_063_aux.Main

namespace PEqualNP.Outside.L_clb_063_aux.Main

theorem sizeEstimate {n P : Nat} (hp : P ≤ 2^n) :
    (n+1)*2^n + (n+1)*(2^n+P) + 6*(P-1) + n*(2*P+1) ≤ 16*(n+1)*2^n := by
  have hd : 1 ≤ 2^n := Nat.one_le_two_pow
  calc
    _ ≤ (n+1)*2^n + (n+1)*(2^n+2^n) + 6*2^n + n*(2*2^n+2^n) := by
      gcongr <;> omega
    _ ≤ _ := by nlinarith [Nat.zero_le (n * 2^n), Nat.zero_le (2^n)]

theorem generic {n m : Nat} (f : Word n → Sig m)
    (hb : Build (Set.range fun (i : Fin m) (x : Fin m → Bool) => x i)
          (Set.range f) ((n+1)*2^n) 0) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (m+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack m C ∧
      C.output < m+C.size ∧ C.size ≤ 16*(n+1)*2^n ∧
      PEqualNP.NotBracket.notCount C ≤ Nat.clog 2 (Nat.choose n (n/2)) ∧
      ∀ x : Fin m → Bool,
        (C.eval (List.ofFn x) = true ↔ ∃ u, f u x = true) ∧
        (C.eval (List.ofFn x) = true →
          f (fun j => (C.wires (List.ofFn x)).getD (outBit j).val false) x = true) := by
  classical
  let M := Nat.choose n (n/2)
  let d := Nat.clog 2 M
  let P := 2^d
  have hpad : M ≤ P := Nat.le_pow_clog (by decide) _
  have hp : P ≤ 2^n := Nat.pow_le_pow_right (by decide)
    ((Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.choose_le_two_pow n (n/2)))
  obtain ⟨first,hfirst⟩ := PEqualNP.Outside.L_clb_063_aux.chainColor n
  let col (u : Word n) : Fin P := Fin.castLE hpad (first u)
  have chain : ∀ u v, col u = col v → u ≤ v ∨ v ≤ u := by
    intro u v h
    exact hfirst u v (Fin.ext (congrArg (fun z : Fin P => z.val) h))
  obtain ⟨en,top,hselect,sem⟩ := selectTree d (avail col f)
  obtain ⟨a,ha,S1⟩ := hb.run (startSched m) le_rfl
  obtain ⟨b,hdB,S2⟩ := (stage col f).run S1 Set.subset_union_right
  obtain ⟨c,hc,S3⟩ := hselect.run S2 (fun _ h => Or.inr (Or.inl h))
  let U := Set.range en ∪ Set.range (fun p : Fin P × Fin n => leafBit col f p.1 p.2)
  have hen (i : Fin P) : en i ∈ U := Or.inl (Set.mem_range_self i)
  have hv (i : Fin P) (j : Fin n) : leafBit col f i j ∈ U :=
    Or.inr (Set.mem_range.mpr ⟨(i,j),rfl⟩)
  have hdBuild := buildPicked en (leafBit col f) hen hv
  obtain ⟨e,heCost,S4⟩ := hdBuild.run S3 (by
    rintro z (hz | hz)
    · exact Or.inr (Or.inr hz)
    · exact Or.inl (Or.inr (Or.inr hz)))
  obtain ⟨C,outBit,hsize,hnots,hr,hfan,hout,evalC,evalBit⟩ :=
    finishMulti S4 top (Or.inl (Or.inr (Or.inl rfl))) (pickedBit en (leafBit col f))
      (fun j => Or.inr (Set.mem_range_self j))
  refine ⟨C,outBit,hfan,hr,hout,?_,?_,?_⟩
  · have H := sizeEstimate hp
    have heSize : e ≤ n * (2 * P + 1) := heCost
    have hcSize : c ≤ 6 * (P - 1) := hc
    rw [hsize]
    omega
  · simpa [d,M] using hnots
  · intro x
    have ht := sem x
    refine ⟨(by rw [evalC x, ht.1]; exact avail_true col f x),?_⟩
    intro hy
    obtain ⟨i,hi,honly⟩ := ht.2 ((evalC x).symm.trans hy)
    have eq : (fun j => (C.wires (List.ofFn x)).getD (outBit j).val false) =
        (fun j => leafBit col f i j x) := by
      funext j
      exact (evalBit j x).trans (pickedBit_eq en (leafBit col f) x i honly j)
    rw [eq]
    exact leaf_feasible col f chain i x hi

end PEqualNP.Outside.L_clb_063_aux.Main

theorem PEqualNP.Outside.L_clb_063 : (∀ (n w : ℕ) (hn : 0 < n),
  let stride := 2 ^ (w + 1)
  let I := n * stride
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.output < I + C.size ∧
    C.size ≤ 16 * (n + 1) * 2 ^ n ∧
    PEqualNP.NotBracket.notCount C ≤ Nat.clog 2 (Nat.choose n (n / 2)) ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun addr : Fin I =>
        table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
      let valid := fun (word : Fin n → Bool) => ∀ i : Fin n,
        table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true
      let picked := fun pos : Fin n => (C.wires inputs).getD (outBit pos).val false
      (C.eval inputs = true ↔ ∃ word, valid word) ∧ (C.eval inputs = true → valid picked)) := by
  intro n w hn
  dsimp only
  let f := PEqualNP.Outside.L_clb_063_aux.Main.feas (w:=w) hn
  obtain ⟨C,outBit,fan,reads,output,size,nots,correct⟩ :=
    PEqualNP.Outside.L_clb_063_aux.Main.generic f (PEqualNP.Outside.L_clb_063_aux.Main.feasBuild (w:=w) hn)
  refine ⟨C,outBit,fan,reads,output,size,nots,?_⟩
  intro table
  let x := PEqualNP.Outside.L_clb_063_aux.Main.tableInputs hn table
  obtain ⟨top,pick⟩ := correct x
  constructor
  · change (C.eval (List.ofFn x) = true ↔ _)
    rw [top]
    exact exists_congr (fun u => PEqualNP.Outside.L_clb_063_aux.Main.feas_correct hn table u)
  · intro h
    exact (PEqualNP.Outside.L_clb_063_aux.Main.feas_correct hn table _).mp (pick h)
