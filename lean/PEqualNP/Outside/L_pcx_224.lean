import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_224_aux

-- Circuit scheduling helpers adapted from L_clb_063.lean at 1e55a702f965ad93b7313e6e1df0a45e8a6d7ca9.

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

private def Build {m : ℕ} (A B : Set (Sig m)) (b r : ℕ) : Prop :=
  ∀ (k q : ℕ) (S : Set (Sig m)), Scheduled m k q S → A ⊆ S →
    ∃ c ≤ b, Scheduled m (k + c) (q + r) (S ∪ B)

private theorem Build.run {m b r : ℕ} {A B : Set (Sig m)} (h : Build A B b r)
    {k q : ℕ} {S : Set (Sig m)} (hs : Scheduled m k q S) (ha : A ⊆ S) :
    ∃ c ≤ b, Scheduled m (k+c) (q+r) (S∪B) := h k q S hs ha

theorem idleB {m : ℕ} {A B : Set (Sig m)} (h : B ⊆ A) : Build A B 0 0 :=
  fun _ _ _ hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩

theorem relaxB {m : ℕ} {A A' B B' : Set (Sig m)} {b b' r r' : ℕ}
    (H : Build A B b r) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') (hr' : r ≤ r') : Build A' B' b' r' :=
  fun _ _ _ hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hq, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hq.trans (Nat.add_le_add_left hr' _), hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)

theorem seqB {m : ℕ} {A B C : Set (Sig m)} {b c p q : ℕ}
    (H1 : Build A B b p) (H2 : Build (A ∪ B) C c q) : Build A (B ∪ C) (b + c) (p + q) :=
  fun _ _ _ hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1 (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2

theorem gateB {m : ℕ} {A : Set (Sig m)} (op : GateOp) (deps : List (Sig m)) (out : Sig m)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 (ncost op) :=
  fun _ _ _ hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩

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


private abbrev SigSet (m : ℕ) := Set (Sig m)

private theorem produceB {m b c p q : ℕ} {A B C : SigSet m}
    (h : Build A B b p) (g : Build (A ∪ B) C c q) : Build A C (b+c) (p+q) :=
  relaxB (seqB h g) le_rfl (fun _ z => Or.inr (Or.inr z)) le_rfl le_rfl

private theorem batchRSet {m : ℕ} {α : Type*} {A : SigSet m} (s : Finset α)
    (F : α → SigSet m) (cost neg : α → ℕ)
    (hs : ∀ i ∈ s, Build A (F i) (cost i) (neg i)) :
    Build A (⋃ i ∈ s, F i) (∑ i ∈ s, cost i) (∑ i ∈ s, neg i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact idleB (by simp)
  | @insert i s hi ih =>
    have pre := hs i (by simp)
    have rest := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    have tail := relaxB rest (A':=A ∪ F i) (B':=⋃ j ∈ s, F j)
      Set.subset_union_left Set.subset_union_right le_rfl le_rfl
    apply relaxB (seqB pre tail) le_rfl _ (by simp [hi]) (by simp [hi])
    intro z hz
    simp only [Set.mem_iUnion, Finset.mem_insert] at hz
    rcases hz with ⟨j, rfl | hj, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, h⟩⟩))

private theorem batchR {m : ℕ} {α : Type*} [Fintype α] {A : SigSet m}
    (f : α → Sig m) (b r : ℕ) (h : ∀ i, Build A {f i} b r) :
    Build A (Set.range f) (Fintype.card α * b) (Fintype.card α * r) := by
  classical
  have h' := batchRSet Finset.univ (fun i => {f i}) (fun _ => b) (fun _ => r) (fun i _ => h i)
  apply relaxB h' le_rfl _ (by simp) (by simp)
  rintro _ ⟨i,rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,rfl⟩⟩)

private abbrev andS {m : ℕ} (f g : Sig m) : Sig m := fun x => f x && g x
private abbrev orS {m : ℕ} (f g : Sig m) : Sig m := fun x => f x || g x
private abbrev notS {m : ℕ} (f : Sig m) : Sig m := fun x => !(f x)

private theorem twoAndOrB {m : ℕ} {A : SigSet m} {f g p q : Sig m}
    (hf : f ∈ A) (hg : g ∈ A) (hp : p ∈ A) (hq : q ∈ A) :
    Build A {orS (andS f g) (andS p q)} 3 0 := by
  have h1 := andB hf hg
  have h2 := andB (A := A ∪ {andS f g}) (Or.inl hp) (Or.inl hq)
  have h3 := orB (A := A ∪ ({andS f g} ∪ {andS p q}))
    (Or.inr (Or.inl (rfl : andS f g = andS f g))) (Or.inr (Or.inr (rfl : andS p q = andS p q)))
  exact produceB (seqB h1 h2) h3

private def Through {m : ℕ} (L : ℕ → SigSet m) (l : ℕ) : SigSet m :=
  { f | ∃ k ≤ l, f ∈ L k }

private theorem mem_through {m : ℕ} {L : ℕ → SigSet m} {i l : ℕ} {f : Sig m}
    (hi : i ≤ l) (hf : f ∈ L i) : f ∈ Through L l := ⟨i, hi, hf⟩

private theorem iterateB {m n c r : ℕ} {A : SigSet m} {L : ℕ → SigSet m}
    (h0 : L 0 ⊆ A) (hs : ∀ k < n, Build (A ∪ L k) (L (k+1)) c r) :
    Build A (Through L n) (n*c) (n*r) := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul]
    apply idleB
    rintro f ⟨i, hi, hf⟩
    exact h0 (by simpa [Nat.eq_zero_of_le_zero hi] using hf)
  | succ n ih =>
    have h := ih (fun k hk => hs k (by omega))
    have j : Build (A ∪ Through L n) (L (n+1)) c r :=
      relaxB (hs n (by omega)) (fun _ z => z.elim Or.inl (fun hz => Or.inr (mem_through le_rfl hz)))
        Set.subset_union_right le_rfl le_rfl
    refine relaxB (seqB h j) le_rfl ?_ (by rw [Nat.add_mul, Nat.one_mul]) (by rw [Nat.add_mul, Nat.one_mul])
    rintro f ⟨k, hk, hf⟩
    exact Or.inr (if hkn : k ≤ n then Or.inl (mem_through hkn hf)
      else Or.inr (by simpa [show k = n+1 by omega] using hf))

private theorem sq_pow (w : ℕ) : 2^w * 2^w = 4^w := by
  rw [← mul_pow]
  rfl

private theorem width_le (w : ℕ) : w+1 ≤ 2^w := by
  induction w with
  | zero => simp
  | succ w ih => rw [pow_succ]; omega

private theorem state_le_sq (w : ℕ) : 2^w ≤ 4^w := by
  rw [← sq_pow]
  have h : 1 ≤ 2^w := Nat.two_pow_pos _
  simpa using Nat.mul_le_mul_left (2^w) h



abbrev S (w : ℕ) := Fin (2 ^ w)
abbrev E (w : ℕ) := Fin (2 ^ (w + 1))

def src {w : ℕ} (e : E w) : S w :=
  ⟨e.val % 2 ^ w, Nat.mod_lt _ (by positivity)⟩

def dst {w : ℕ} (e : E w) : S w :=
  ⟨e.val / 2, (Nat.div_lt_iff_lt_mul (by decide)).2 (by
    simpa only [pow_succ] using e.isLt)⟩

def inEdge {w : ℕ} (t : S w) (b : Bool) : E w :=
  ⟨2 * t.val + b.toNat, by
    rw [pow_succ]
    have ht := t.isLt
    have hb := Bool.toNat_lt b
    omega⟩

def outEdge {w : ℕ} (s : S w) (b : Bool) : E w :=
  ⟨s.val + b.toNat * 2 ^ w, by
    rw [pow_succ]
    have hs := s.isLt
    cases b <;> norm_num [Bool.toNat] <;> omega⟩

@[local simp] theorem src_outEdge {w : ℕ} (s : S w) (b : Bool) : src (outEdge s b) = s := by
  apply Fin.ext
  change (s.val + b.toNat * 2 ^ w) % 2 ^ w = s.val
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt s.isLt]

@[local simp] theorem dst_inEdge {w : ℕ} (t : S w) (b : Bool) : dst (inEdge t b) = t := by
  apply Fin.ext
  change (2 * t.val + b.toNat) / 2 = t.val
  have hb := Bool.toNat_lt b
  omega

theorem exists_outEdge {w : ℕ} {s : S w} {e : E w} (h : src e = s) :
    ∃ b : Bool, outEdge s b = e := by
  have hs : e.val % 2 ^ w = s.val := congrArg Fin.val h
  have he : e.val < 2 ^ w * 2 := by simpa only [pow_succ] using e.isLt
  by_cases hsmall : e.val < 2 ^ w
  · refine ⟨false, Fin.ext ?_⟩
    change s.val + 0 * 2 ^ w = e.val
    rw [← hs, Nat.mod_eq_of_lt hsmall, zero_mul, Nat.add_zero]
  · have hlarge : 2 ^ w ≤ e.val := by omega
    have hsub : e.val - 2 ^ w < 2 ^ w := by omega
    rw [Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hsub] at hs
    refine ⟨true, Fin.ext ?_⟩
    change s.val + 1 * 2 ^ w = e.val
    rw [one_mul, ← hs]
    omega

theorem exists_inEdge {w : ℕ} {t : S w} {e : E w} (h : dst e = t) :
    ∃ b : Bool, inEdge t b = e := by
  have ht : e.val / 2 = t.val := congrArg Fin.val h
  have he := Nat.mod_add_div e.val 2
  by_cases hzero : e.val % 2 = 0
  · refine ⟨false, Fin.ext ?_⟩
    change 2 * t.val + 0 = e.val
    omega
  · refine ⟨true, Fin.ext ?_⟩
    change 2 * t.val + 1 = e.val
    have hm := Nat.mod_lt e.val (by decide : 0 < 2)
    omega

def decode {w : ℕ} (e : E w) : Fin (w + 1) → Bool := fun i => e.val.testBit i.val

-- Encoding and its bit lemma adapted from windowCode / windowCodeBit in
-- lean/PEqualNP/Outside/L_clb_063.lean at 1e55a702f965ad93b7313e6e1df0a45e8a6d7ca9.
def encode {w : ℕ} (p : Fin (w + 1) → Bool) : E w :=
  ⟨(BitVec.ofBoolListLE (List.ofFn p)).toNat, by
    simpa using (BitVec.ofBoolListLE (List.ofFn p)).isLt⟩

@[local simp] theorem decode_encode {w : ℕ} (p : Fin (w + 1) → Bool) : decode (encode p) = p := by
  funext j
  change (BitVec.ofBoolListLE (List.ofFn p)).getLsbD j.val = p j
  rw [BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]

-- Bounded bit extensionality and truncation adapted from bits_eq / bits_mod in
-- lean/PEqualNP/Outside/L_clb_042.lean at 1e55a702f965ad93b7313e6e1df0a45e8a6d7ca9.
private theorem geom_bits_eq (x y w : ℕ) (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (h : ∀ i < w, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i w with hi | hi
  · exact h i hi
  · have hp : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hp)]

private theorem geom_src_bit {w : ℕ} (e : E w) (k : ℕ) (hk : k < w) :
    (src e).val.testBit k = e.val.testBit k := by
  change (e.val % 2 ^ w).testBit k = e.val.testBit k
  rw [Nat.testBit_mod_two_pow]; simp [hk]

private theorem geom_dst_bit {w : ℕ} (e : E w) (k : ℕ) :
    (dst e).val.testBit k = e.val.testBit (k + 1) :=
  (Nat.testBit_succ e.val k).symm

@[local simp] theorem encode_decode {w : ℕ} (e : E w) : encode (decode e) = e := by
  apply Fin.ext
  refine geom_bits_eq _ _ (w + 1) (encode (decode e)).isLt e.isLt ?_
  intro k hk
  exact congrFun (decode_encode (decode e)) ⟨k, hk⟩

def pos {n w : ℕ} (hn : 0 < n) (i : Fin n) (k : Fin (w + 1)) : Fin n :=
  ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩

def win {n w : ℕ} (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) (k : Fin (w + 1)) : Bool :=
  x (pos hn i k)

def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def IsCycle {n w : ℕ} (hn : 0 < n) (e : Fin n → E w) : Prop :=
  ∀ i, dst (e i) = src (e (next hn i))

private theorem geom_pos_succ {n w : ℕ} (hn : 0 < n) (i : Fin n) (k : ℕ)
    (hk : k + 1 < w + 1) :
    pos (w := w) hn i ⟨k + 1, hk⟩ = pos (w := w) hn (next hn i) ⟨k, by omega⟩ := by
  apply Fin.ext
  change (i.val + (k + 1)) % n = ((i.val + 1) % n + k) % n
  rw [Nat.mod_add_mod]
  exact congrArg (fun j : ℕ => j % n) (by omega)

theorem win_cycle {n w : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    IsCycle (w := w) hn (fun i => encode (win hn x i)) := by
  intro i
  let a := encode (w := w) (win hn x i)
  let b := encode (w := w) (win hn x (next hn i))
  change dst a = src b
  apply Fin.ext
  refine geom_bits_eq _ _ w (dst a).isLt (src b).isLt ?_
  intro k hk
  rw [geom_dst_bit, geom_src_bit _ _ hk]
  have hks : k + 1 < w + 1 := by omega
  calc
    a.val.testBit (k + 1) = x (pos (w := w) hn i ⟨k + 1, hks⟩) :=
      congrFun (decode_encode (win (w := w) hn x i)) ⟨k + 1, hks⟩
    _ = x (pos (w := w) hn (next hn i) ⟨k, by omega⟩) :=
      congrArg x (geom_pos_succ hn i k hks)
    _ = b.val.testBit k :=
      (congrFun (decode_encode (win (w := w) hn x (next hn i))) ⟨k, by omega⟩).symm

theorem cycle_win {n w : ℕ} {hn : 0 < n} {e : Fin n → E w} (h : IsCycle hn e) :
    ∀ i, win hn (fun j => (e j).val.testBit 0) i = decode (e i) := by
  have hbit (i : Fin n) (k : ℕ) (hk : k < w) :
      (e (next hn i)).val.testBit k = (e i).val.testBit (k + 1) := by
    rw [← geom_src_bit _ _ hk, ← h i, geom_dst_bit]
  have hall : ∀ (k : ℕ) (hk : k < w + 1) (i : Fin n),
      (e (pos (w := w) hn i ⟨k, hk⟩)).val.testBit 0 = (e i).val.testBit k := by
    intro k
    induction k with
    | zero =>
      intro hk i
      have hpos : pos (w := w) hn i ⟨0, hk⟩ = i := by
        apply Fin.ext
        change (i.val + 0) % n = i.val
        rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
      rw [hpos]
    | succ k ih =>
      intro hk i
      rw [geom_pos_succ hn i k hk, ih (by omega) (next hn i), hbit i k (by omega)]
  intro i
  funext k
  exact hall k.val k.isLt i




section AbstractWalk

variable {S E : Type} (src dst : E → S)

def Reach (A : ℕ → E → Bool) (i : ℕ) : ℕ → S → S → Prop
  | 0, s, t => s = t
  | l + 1, s, t => ∃ e, src e = s ∧ A i e = true ∧
      Reach A (i + 1) l (dst e) t

theorem reach_mono {A C : ℕ → E → Bool} {i l : ℕ} {s t : S}
    (h : Reach src dst A i l s t)
    (hAC : ∀ j, j < l → ∀ e, A (i+j) e = true → C (i+j) e = true) :
    Reach src dst C i l s t := by
  induction l generalizing i s with
  | zero => exact h
  | succ l ih =>
    obtain ⟨e, he, ha, hr⟩ := h
    refine ⟨e, he, hAC 0 (by omega) e (by simpa using ha),
      ih (i := i+1) (s := dst e) hr ?_⟩
    intro j hj f hf
    have hh : i + 1 + j = i + (j + 1) := by omega
    rw [hh] at hf ⊢
    exact hAC (j+1) (by omega) f hf

theorem reach_split {A : ℕ → E → Bool} {i k l : ℕ} {s t : S} :
    Reach src dst A i (k+l) s t ↔
      ∃ u, Reach src dst A i k s u ∧ Reach src dst A (i+k) l u t := by
  induction k generalizing i s with
  | zero =>
    change Reach src dst A i (0+l) s t ↔
      ∃ u, s = u ∧ Reach src dst A (i+0) l u t
    simp
  | succ k ih =>
    have h₁ : k + 1 + l = k + l + 1 := by omega
    have h₂ : i + (k + 1) = i + 1 + k := by omega
    rw [h₁, h₂]
    constructor
    · rintro ⟨e, he, ha, hr⟩
      obtain ⟨u, hp, hs⟩ := (ih (i := i+1) (s := dst e)).mp hr
      exact ⟨u, ⟨e, he, ha, hp⟩, hs⟩
    · rintro ⟨u, ⟨e, he, ha, hp⟩, hs⟩
      exact ⟨e, he, ha, (ih (i := i+1) (s := dst e)).mpr ⟨u, hp, hs⟩⟩

theorem reach_snoc {A : ℕ → E → Bool} {i l : ℕ} {s t : S} :
    Reach src dst A i (l+1) s t ↔
      ∃ e, Reach src dst A i l s (src e) ∧ A (i+l) e = true ∧ dst e = t := by
  rw [reach_split src dst]
  constructor
  · rintro ⟨u, hp, e, rfl, ha, ht⟩
    exact ⟨e, hp, ha, ht⟩
  · rintro ⟨e, hp, ha, ht⟩
    exact ⟨src e, hp, e, rfl, ha, ht⟩

/-- A realized path. Values of its vertex and edge functions beyond the path are irrelevant. -/
def Walk (A : ℕ → E → Bool) (i l : ℕ) (p : ℕ → E) (x : ℕ → S) (s t : S) : Prop :=
  x 0 = s ∧ x l = t ∧ ∀ j, j < l →
    src (p j) = x j ∧ dst (p j) = x (j+1) ∧ A (i+j) (p j) = true

theorem Walk.reach {A : ℕ → E → Bool} {i l : ℕ} {p : ℕ → E} {x : ℕ → S} {s t : S}
    (h : Walk src dst A i l p x s t) : Reach src dst A i l s t := by
  induction l generalizing i p x s with
  | zero => exact h.1.symm.trans h.2.1
  | succ l ih =>
    obtain ⟨hs, ht, h⟩ := h
    obtain ⟨he, hd, ha⟩ := h 0 (by omega)
    refine ⟨p 0, he.trans hs, by simpa using ha, ?_⟩
    apply ih (p := fun j => p (j+1)) (x := fun j => x (j+1))
    refine ⟨hd.symm, ht, ?_⟩
    intro j hj
    have hh : i + 1 + j = i + (j + 1) := by omega
    simpa only [hh] using h (j+1) (by omega)

theorem reach_walk [Nonempty E] {A : ℕ → E → Bool} {i l : ℕ} {s t : S}
    (h : Reach src dst A i l s t) : ∃ p x, Walk src dst A i l p x s t := by
  induction l generalizing i s with
  | zero =>
    obtain ⟨e⟩ := ‹Nonempty E›
    exact ⟨fun _ => e, fun _ => s, rfl, h, fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | succ l ih =>
    obtain ⟨e, he, ha, h⟩ := h
    obtain ⟨p, x, hd, ht, hw⟩ := ih (i := i+1) (s := dst e) h
    refine ⟨(fun | 0 => e | j+1 => p j), (fun | 0 => s | j+1 => x j), rfl, ht, ?_⟩
    intro j hj
    cases j with
    | zero => exact ⟨he, hd.symm, by simpa using ha⟩
    | succ j =>
      have hh : i + (j + 1) = i + 1 + j := by omega
      simpa only [hh] using hw j (by omega)

theorem reach_iff_walk_of_pos {A : ℕ → E → Bool} {i l : ℕ} {s t : S} (hl : 0 < l) :
    Reach src dst A i l s t ↔ ∃ p x, Walk src dst A i l p x s t := by
  constructor
  · intro h
    cases l with
    | zero => omega
    | succ l =>
      obtain ⟨e, _⟩ := (show ∃ e, src e = s ∧ A i e = true ∧
        Reach src dst A (i+1) l (dst e) t from h)
      letI : Nonempty E := ⟨e⟩
      exact reach_walk src dst h
  · rintro ⟨p, x, h⟩
    exact Walk.reach src dst h

section Reduction

variable {A cut : ℕ → E → Bool} {F B : ℕ → S → S → Bool} {n : ℕ}

/-- Set row `i` to accept exactly the queried edge, leaving all other rows alone. -/
noncomputable def forceEdge (cut : ℕ → E → Bool) (i : ℕ) (e : E) : ℕ → E → Bool := by
  classical
  exact fun j f => if j = i then decide (f = e) else cut j f

theorem cut_false_forced_walk
    (hF : ∀ k ≤ n, ∀ s u, F k s u = true ↔ Reach src dst cut 0 k s u)
    (hB : ∀ k ≤ n, ∀ v s, B k v s = true ↔ Reach src dst A k (n-k) v s)
    (hc : ∀ i < n, ∀ e, cut i e = true ↔ A i e = true ∨
      ¬ ∃ s, F i s (src e) = true ∧ B (i+1) (dst e) s = true)
    {i : ℕ} {e : E} (hi : i < n) (he : cut i e = false) :
    ∃ (p : ℕ → E) (x : ℕ → S) (s : S),
      Walk src dst (forceEdge cut i e) 0 n p x s s ∧
      p i = e ∧ ∀ j < n, j ≠ i → cut j (p j) = true := by
  classical
  have hex : ∃ s, F i s (src e) = true ∧ B (i+1) (dst e) s = true := by
    by_contra h
    have h' := (hc i hi e).mpr (Or.inr h)
    simp [he] at h'
  obtain ⟨s, hf, hb⟩ := hex
  have hp := (hF i (by omega) s _).mp hf
  have hs := (hB (i+1) (by omega) _ s).mp hb
  have hp' : Reach src dst (forceEdge cut i e) 0 i s (src e) := by
    apply reach_mono src dst hp
    intro j hj f h
    simpa [forceEdge, show j ≠ i by omega] using h
  have hs' : Reach src dst (forceEdge cut i e) (i+1) (n-(i+1)) (dst e) s := by
    apply reach_mono src dst hs
    intro j hj f h
    rw [forceEdge, ite_eq_right (show i+1+j ≠ i by omega)]
    exact (hc _ (by omega) f).mpr (Or.inl h)
  have hn : n = i + (n-(i+1)+1) := by omega
  have hr : Reach src dst (forceEdge cut i e) 0 n s s := by
    rw [hn]
    apply (reach_split src dst).mpr
    refine ⟨src e, hp', ?_⟩
    exact ⟨e, rfl, by simp [forceEdge], by simpa only [Nat.zero_add] using hs'⟩
  obtain ⟨p, x, hw⟩ := (reach_iff_walk_of_pos src dst (by omega)).mp hr
  refine ⟨p, x, s, hw, ?_, ?_⟩
  · simpa [forceEdge] using (hw.2.2 i hi).2.2
  · intro j hj hji
    simpa [forceEdge, hji] using (hw.2.2 j hj).2.2

end Reduction
end AbstractWalk


private abbrev Matrix (m w : ℕ) := S w → S w → Sig m
private abbrev Mask (m w : ℕ) := E w → Sig m

private def MatSet {m w : ℕ} (a : Matrix m w) : SigSet m :=
  Set.range (fun p : S w × S w => a p.1 p.2)

private theorem mat_mem {m w : ℕ} (a : Matrix m w) (s t : S w) : a s t ∈ MatSet a :=
  ⟨(s,t), rfl⟩

private def diag {m w : ℕ} : Matrix m w := fun u v _ => decide (u = v)

private theorem diag_mem {m w : ℕ} {A : SigSet m}
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) :
    MatSet (diag (m:=m) (w:=w)) ⊆ A := by
  rintro _ ⟨⟨s,t⟩,rfl⟩
  change (fun _ => decide (s=t)) ∈ A
  by_cases h : s = t
  · simpa [h] using ht
  · simpa [h] using hf

private def binaryStep {m w : ℕ} (a : Mask m w) (r : Matrix m w)
    (pick : S w → Bool → E w) (neighbor : E w → S w) : Matrix m w :=
  fun u v => orS (andS (a (pick u false)) (r (neighbor (pick u false)) v))
    (andS (a (pick u true)) (r (neighbor (pick u true)) v))

private theorem binaryStepB {m w : ℕ} {A : SigSet m} (a : Mask m w) (r : Matrix m w)
    (pick : S w → Bool → E w) (neighbor : E w → S w)
    (ha : ∀ e, a e ∈ A) (hr : ∀ u v, r u v ∈ A) :
    Build A (MatSet (binaryStep a r pick neighbor)) (3*4^w) 0 := by
  have h := batchR (A:=A) (fun p : S w × S w => binaryStep a r pick neighbor p.1 p.2) 3 0
    (fun p => twoAndOrB (ha _) (hr _ _) (ha _) (hr _ _))
  simpa [MatSet, Fintype.card_prod, sq_pow, Nat.mul_comm] using h

private def rear {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) : ℕ → Matrix m w
  | 0 => diag
  | l+1 => binaryStep (A (n-(l+1))) (rear n A l) outEdge dst

private def suffix {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (k : ℕ) : Matrix m w :=
  rear n A (n-k)

private theorem suffix_zero {m w n : ℕ} {A : ℕ → Mask m w} (u v : S w) (x) :
    suffix n A n u v x = decide (u=v) := by simp [suffix, rear, diag]

private theorem suffix_step {m w n k : ℕ} {A : ℕ → Mask m w} (hk : k<n) :
    suffix n A k = binaryStep (A k) (suffix n A (k+1)) outEdge dst := by
  unfold suffix
  rw [show n-k = (n-(k+1))+1 by omega, rear]
  congr 2
  omega

private def RearSet {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) : SigSet m :=
  Through (fun k => MatSet (rear n A k)) n

private theorem suffix_mem {m w n k : ℕ} {A : ℕ → Mask m w} (u v : S w) :
    suffix n A k u v ∈ RearSet n A :=
  mem_through (Nat.sub_le _ _) (mat_mem _ _ _)

private theorem rearBuild {m w n : ℕ} {A : ℕ → Mask m w} {Z : SigSet m}
    (ha : ∀ k < n, ∀ e, A k e ∈ Z)
    (hf : (fun _ => false) ∈ Z) (ht : (fun _ => true) ∈ Z) :
    Build Z (RearSet n A) (n*(3*4^w)) 0 := by
  have h := iterateB (n:=n) (c:=3*4^w) (r:=0) (L:=fun k => MatSet (rear n A k))
    (diag_mem hf ht) (fun k hk => by
      change Build _ (MatSet (binaryStep (A (n-(k+1))) (rear n A k) outEdge dst)) _ _
      exact binaryStepB _ _ _ _ (fun e => Or.inl (ha _ (by omega) e))
        (fun u v => Or.inr (mat_mem _ u v)))
  rw [Nat.mul_zero] at h
  exact h

private noncomputable def context {m w : ℕ} (f b : Matrix m w) (e : E w) : Sig m :=
  anyS Finset.univ (fun s => andS (f (src e) s) (b (dst e) s))

private noncomputable def weaken {m w : ℕ} (a : Mask m w) (f b : Matrix m w) (e : E w) : Sig m :=
  orS (a e) (notS (context f b e))

private theorem weakenB {m w : ℕ} {Z : SigSet m} (a : Mask m w) (f b : Matrix m w)
    (ha : ∀ e, a e ∈ Z) (hf : ∀ u v, f u v ∈ Z) (hb : ∀ u v, b u v ∈ Z) :
    Build Z (Set.range (weaken a f b)) (10*4^w) (2*4^w) := by
  have each (e : E w) : Build Z {weaken a f b e} (2 * 2^w + 3) 1 := by
    let r := fun s : S w => andS (f (src e) s) (b (dst e) s)
    have h1 := batchR (A:=Z) r 1 0 (fun s => andB (hf _ _) (hb _ _))
    have h2 : Build (Z ∪ Set.range r) {context f b e} (2^w + 1) 0 := by
      simpa [context, r] using anySB (A:=Z ∪ Set.range r) Finset.univ r
        (fun s _ => Or.inr ⟨s,rfl⟩)
    have h12 : Build Z {context f b e} (2^w + (2^w + 1)) 0 := by
      simpa using produceB h1 h2
    have h3 : Build (Z ∪ {context f b e}) {notS (context f b e)} 1 1 :=
      notB (Or.inr rfl)
    have h123 := produceB h12 h3
    have h4 : Build (Z ∪ {notS (context f b e)}) {weaken a f b e} 1 0 :=
      orB (Or.inl (ha _)) (Or.inr rfl)
    exact relaxB (produceB h123 h4) le_rfl Set.subset_union_right (by omega) (by omega)
  have r := batchR (weaken a f b) _ _ each
  have hcard : Fintype.card (E w) = 2*2^w := by simp [E, pow_succ, Nat.mul_comm]
  have hsq := sq_pow w
  have hle := state_le_sq w
  rw [hcard] at r
  exact relaxB r le_rfl Set.subset_union_right (by nlinarith) (by omega)

private noncomputable def sweep {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) : ℕ → Matrix m w × Mask m w
  | 0 => (diag, fun _ _ => false)
  | k+1 =>
    let f := (sweep n A k).1
    let a := weaken (A k) f (suffix n A (k+1))
    (binaryStep a f inEdge src, a)

private noncomputable def cut {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (k : ℕ) : Mask m w :=
  (sweep n A (k+1)).2

private noncomputable def SweepLayer {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (k : ℕ) : SigSet m :=
  MatSet (sweep n A k).1 ∪ Set.range (sweep n A k).2

private noncomputable def SweepSet {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) : SigSet m :=
  Through (SweepLayer n A) n

private theorem cut_mem {m w n k : ℕ} {A : ℕ → Mask m w} (hk : k < n) (e : E w) :
    cut n A k e ∈ SweepSet n A :=
  mem_through (i:=k+1) (by omega) (Or.inr ⟨e,rfl⟩)

private theorem sweepBuild {m w n : ℕ} {A : ℕ → Mask m w} {Z : SigSet m}
    (ha : ∀ k < n, ∀ e, A k e ∈ Z) (hb : RearSet n A ⊆ Z)
    (hf : (fun _ => false) ∈ Z) (ht : (fun _ => true) ∈ Z) :
    Build Z (SweepSet n A) (n*(13*4^w)) (n*(2*4^w)) := by
  apply iterateB
  · apply Set.union_subset (diag_mem hf ht)
    rintro _ ⟨e,rfl⟩
    exact hf
  · intro k hk
    let L := Z ∪ SweepLayer n A k
    let f := (sweep n A k).1
    let a := cut n A k
    have h1 : Build L (Set.range a) (10*4^w) (2*4^w) :=
      weakenB _ _ _ (fun e => Or.inl (ha k hk e))
        (fun u v => Or.inr (Or.inl (mat_mem f u v))) (fun u v => Or.inl (hb (suffix_mem u v)))
    have h2 : Build (L ∪ Set.range a) (MatSet (binaryStep a f inEdge src)) (3*4^w) 0 :=
      binaryStepB _ _ _ _ (fun e => Or.inr ⟨e,rfl⟩)
        (fun u v => Or.inl (Or.inr (Or.inl (mat_mem f u v))))
    apply relaxB (seqB h1 h2) le_rfl _ (by omega) (by omega)
    intro g hg
    exact Or.inr (hg.elim Or.inr Or.inl)


private theorem rear_correct {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (x : Fin m → Bool)
    (l : ℕ) (hl : l ≤ n) (u v : S w) :
    rear n A l u v x = true ↔ Reach src dst (fun k e => A k e x) (n-l) l u v := by
  induction l generalizing u with
  | zero => simp [rear, diag, Reach]
  | succ l ih =>
    have hEq : n-(l+1)+1 = n-l := by omega
    simp only [rear, binaryStep, orS, andS, Bool.or_eq_true, Bool.and_eq_true, Reach, hEq]
    constructor
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · exact ⟨outEdge u false, src_outEdge .., h1, (ih (by omega) _).mp h2⟩
      · exact ⟨outEdge u true, src_outEdge .., h1, (ih (by omega) _).mp h2⟩
    · rintro ⟨e, hu, ha, hr⟩
      obtain ⟨b, rfl⟩ := exists_outEdge hu
      cases b
      · exact Or.inl ⟨ha, (ih (by omega) _).mpr hr⟩
      · exact Or.inr ⟨ha, (ih (by omega) _).mpr hr⟩

private theorem suffix_correct {m w n : ℕ} (A : ℕ → Mask m w) (x : Fin m → Bool) :
    ∀ k ≤ n, ∀ u v : S w,
    suffix n A k u v x = true ↔ Reach src dst (fun j e => A j e x) k (n-k) u v := by
  intro k hk u v
  simpa only [suffix, show n-(n-k) = k by omega] using
    rear_correct n A x (n-k) (Nat.sub_le _ _) u v

private theorem sweep_correct {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (x : Fin m → Bool)
    (k : ℕ) (u s : S w) :
    (sweep n A k).1 u s x = true ↔ Reach src dst (fun j e => cut n A j e x) 0 k s u := by
  induction k generalizing u with
  | zero => simp [sweep, diag, Reach, eq_comm]
  | succ k ih =>
    have h : (sweep n A (k+1)).1 = binaryStep (cut n A k) (sweep n A k).1 inEdge src := rfl
    rw [h, reach_snoc src dst]
    simp only [binaryStep, orS, andS, Bool.or_eq_true, Bool.and_eq_true, Nat.zero_add]
    constructor
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · exact ⟨inEdge u false, (ih _).mp h2, h1, dst_inEdge ..⟩
      · exact ⟨inEdge u true, (ih _).mp h2, h1, dst_inEdge ..⟩
    · rintro ⟨e, hp, he, hu⟩
      obtain ⟨b,rfl⟩ := exists_inEdge hu
      cases b
      · exact Or.inl ⟨he, (ih _).mpr hp⟩
      · exact Or.inr ⟨he, (ih _).mpr hp⟩

private theorem cut_correct {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (x : Fin m → Bool)
    (k : ℕ) (e : E w) : cut n A k e x = true ↔ A k e x = true ∨
      ¬ ∃ s, (sweep n A k).1 (src e) s x = true ∧ suffix n A (k+1) (dst e) s x = true := by
  change (A k e x || !(context (sweep n A k).1 (suffix n A (k+1)) e x)) = true ↔ _
  have hc : context (sweep n A k).1 (suffix n A (k+1)) e x = true ↔
      ∃ s, (sweep n A k).1 (src e) s x = true ∧ suffix n A (k+1) (dst e) s x = true := by
    simp [context, anyS_true]
  rw [← hc]
  cases context (sweep n A k).1 (suffix n A (k+1)) e x <;> simp

private def rowAt {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

private theorem rowAt_fin {n : ℕ} (hn : 0 < n) (i : Fin n) : rowAt hn i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem walk_of_cycle {n w : ℕ} {hn : 0 < n} {A : ℕ → E w → Bool}
    {e : Fin n → E w} (h : IsCycle hn e) (ha : ∀ i : Fin n, A i.val (e i) = true) :
    ∃ v s, Walk src dst A 0 n (fun j => e (rowAt hn j)) v s s := by
  let p (j : ℕ) := e (rowAt hn j)
  let v (j : ℕ) := src (p j)
  refine ⟨v, v 0, ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · simp [v, p, rowAt]
  · intro j hj
    let i : Fin n := ⟨j, hj⟩
    have hi : rowAt hn j = i := rowAt_fin hn i
    have hnext : rowAt hn (j+1) = next hn i := rfl
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [v, p, hi, hnext] using h i
    · simpa only [Nat.zero_add, p, hi] using ha i

private theorem reach_of_cycle {n w : ℕ} {hn : 0 < n} {A : ℕ → E w → Bool}
    {e : Fin n → E w} (h : IsCycle hn e) (ha : ∀ i : Fin n, A i.val (e i) = true) :
    ∃ s, Reach src dst A 0 n s s := by
  obtain ⟨v,s,hv⟩ := walk_of_cycle h ha
  exact ⟨s, Walk.reach src dst hv⟩

private theorem cycle_of_walk {n w : ℕ} (hn : 0 < n) {A : ℕ → E w → Bool}
    {p : ℕ → E w} {v : ℕ → S w} {s : S w} (h : Walk src dst A 0 n p v s s) :
    IsCycle hn (fun i => p i.val) ∧ ∀ i : Fin n, A i.val (p i.val) = true := by
  refine ⟨?_, fun i => by simpa using (h.2.2 i.val i.isLt).2.2⟩
  intro i
  have hii := (h.2.2 i.val i.isLt).2.1
  change dst (p i.val) = src (p ((i.val+1)%n))
  by_cases hi : i.val+1<n
  · rw [Nat.mod_eq_of_lt hi, hii, (h.2.2 _ hi).1]
  · have hN : i.val+1=n := by omega
    rw [hN, Nat.mod_self, hii, hN, h.2.1, (h.2.2 0 hn).1, h.1]

private theorem cycle_iff_reach {n w : ℕ} (hn : 0 < n) (A : ℕ → E w → Bool) :
    (∃ e : Fin n → E w, IsCycle hn e ∧ ∀ i : Fin n, A i.val (e i) = true) ↔
    ∃ s, Reach src dst A 0 n s s := by
  constructor
  · rintro ⟨e, he, ha⟩
    exact reach_of_cycle he ha
  · rintro ⟨s, hs⟩
    obtain ⟨p,v,h⟩ := (reach_iff_walk_of_pos src dst hn).mp hs
    exact ⟨fun i => p i.val, cycle_of_walk hn h⟩

private theorem cut_monotone {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (x : Fin m → Bool)
    (k : ℕ) (e : E w) : A k e x = true → cut n A k e x = true :=
  fun h => (cut_correct n A x k e).mpr (Or.inl h)

private theorem cut_witness {m w n : ℕ} (A : ℕ → Mask m w) (x : Fin m → Bool)
    {k : ℕ} (hk : k < n) {e : E w} (he : cut n A k e x = false) :
    ∃ s : S w, Reach src dst (forceEdge (fun j e => cut n A j e x) k e) 0 n s s := by
  obtain ⟨p,v,s,h,_,_⟩ := cut_false_forced_walk src dst
    (fun j _ u v => sweep_correct n A x j v u) (suffix_correct A x)
    (fun j _ f => cut_correct n A x j f) hk he
  exact ⟨s, Walk.reach src dst h⟩

private theorem cut_walk_same {m w n : ℕ} (A : ℕ → Mask m w) (x : Fin m → Bool)
    {p : ℕ → E w} {v : ℕ → S w} {s : S w}
    (h : Walk src dst (fun j e => cut n A j e x) 0 n p v s s) :
    ∀ j < n, A j (p j) x = true := by
  have hh : ∀ l ≤ n, ∀ j < n, n-l ≤ j → A j (p j) x = true := by
    intro l
    induction l with
    | zero => intro _ j hj hb; omega
    | succ l ih =>
      intro hl j hj hbound
      by_cases hk : n-l ≤ j
      · exact ih (by omega) j hj hk
      have hEq : j+1 = n-l := by omega
      obtain ⟨hsrc,hdst,hcut⟩ := h.2.2 j hj
      have hP : Walk src dst (fun k e => cut n A k e x) 0 j p v s (v j) :=
        ⟨h.1,rfl,fun k hk => h.2.2 k (by omega)⟩
      have hB : Walk src dst (fun k e => A k e x) (j+1) (n-(j+1))
          (fun k => p (j+1+k)) (fun k => v (j+1+k)) (v (j+1)) s := by
        refine ⟨by simp, ?_, ?_⟩
        · change v (j+1+(n-(j+1))) = s
          rw [show j+1+(n-(j+1)) = n by omega]
          exact h.2.1
        · intro k hk
          obtain ⟨he1,he2,_⟩ := h.2.2 (j+1+k) (by omega)
          exact ⟨he1,he2,ih (by omega) _ (by omega) (by omega)⟩
      have hcut' : cut n A j (p j) x = true := by simpa using hcut
      rcases (cut_correct n A x j (p j)).mp hcut' with ha | hno
      · exact ha
      · exfalso
        apply hno
        refine ⟨s, (sweep_correct n A x j _ _).mpr ?_, (suffix_correct A x (j+1) (by omega) _ _).mpr ?_⟩
        · rw [hsrc]
          exact Walk.reach src dst hP
        · rw [hdst]
          exact Walk.reach src dst hB
  exact fun j hj => hh n le_rfl j hj (by simp)


private abbrev Table (n w : ℕ) := Fin n → (Fin (w+1) → Bool) → Bool
private abbrev InCount (n w : ℕ) := n * 2^(w+1) + n + (w+1)

private def inputs {n w : ℕ} (hn : 0 < n) (table : Table n w)
    (i : Fin n) (p : Fin (w+1) → Bool) : List Bool :=
  List.ofFn (fun a : Fin (n*2^(w+1)) =>
    table ⟨(a.val / 2^(w+1)) % n, Nat.mod_lt _ hn⟩ (fun k => a.val.testBit k.val)) ++
  List.ofFn (fun j : Fin n => decide (j = i)) ++ List.ofFn p

private theorem inputs_length {n w : ℕ} (hn : 0 < n) (table : Table n w) (i p) :
    (inputs hn table i p).length = InCount n w := by simp [inputs, InCount, Nat.add_assoc]

private def inputVec {n w : ℕ} (hn : 0 < n) (table : Table n w) (i : Fin n) (p : Fin (w+1) → Bool) :
    Fin (InCount n w) → Bool := fun a => (inputs hn table i p).getD a.val false

private theorem ofFn_inputVec {n w : ℕ} (hn : 0 < n) (table : Table n w) (i p) :
    List.ofFn (inputVec hn table i p) = inputs hn table i p := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, inputs_length]
  · intro a ha hb
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hb

private def addr {n w : ℕ} (i : Fin n) (e : E w) : Fin (n * 2^(w+1)) :=
  ⟨i.val * 2^(w+1) + e.val, by
    have h := Nat.mul_le_mul_right (2^(w+1)) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    have he := e.isLt
    omega⟩

private def tableSig {n w : ℕ} (hn : 0 < n) (k : ℕ) (e : E w) : Sig (InCount n w) :=
  fun x => x ⟨(addr (rowAt hn k) e).val, by unfold InCount; have := (addr (rowAt hn k) e).isLt; omega⟩

private def rowSig {n w : ℕ} (j : Fin n) : Sig (InCount n w) :=
  fun x => x ⟨n * 2^(w+1) + j.val, by unfold InCount; have := j.isLt; omega⟩

private def patSig {n w : ℕ} (k : Fin (w+1)) : Sig (InCount n w) :=
  fun x => x ⟨n * 2^(w+1) + n + k.val, by unfold InCount; have := k.isLt; omega⟩

private def Raw (m : ℕ) : SigSet m := Set.range (fun j : Fin m => fun x => x j)

private theorem tableSig_mem {n w : ℕ} (hn : 0 < n) (k : ℕ) (e : E w) :
    tableSig hn k e ∈ Raw (InCount n w) := ⟨_,rfl⟩

private theorem rowSig_mem {n w : ℕ} (j : Fin n) : rowSig (w:=w) j ∈ Raw (InCount n w) := ⟨_,rfl⟩

private theorem patSig_mem {n w : ℕ} (k : Fin (w+1)) : patSig (n:=n) k ∈ Raw (InCount n w) := ⟨_,rfl⟩

private theorem addr_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p)
    (i : Fin n) (e : E w) :
    (inputs hn table q p).getD (addr i e).val false = table i (decode e) := by
  unfold inputs
  rw [List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simpa using (addr i e).isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using (addr i e).isLt), List.getElem_ofFn]
  have hd : (i.val * 2^(w+1) + e.val) / 2^(w+1) = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt e.isLt, Nat.zero_add]
  have hb (j : Fin (w+1)) : (i.val * 2^(w+1) + e.val).testBit j.val = decode e j := by
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ e.isLt, ite_eq_left j.isLt]
    rfl
  change table ⟨((i.val * 2^(w+1) + e.val) / 2^(w+1)) % n, _⟩
    (fun j => (i.val * 2^(w+1) + e.val).testBit j.val) = _
  simp [hd, Nat.mod_eq_of_lt i.isLt, hb]

private theorem tableSig_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p)
    (i : Fin n) (e : E w) : tableSig hn i.val e (inputVec hn table q p) = table i (decode e) := by
  simpa only [tableSig, inputVec, rowAt_fin] using addr_read hn table q p i e

private theorem rowSig_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p) (i : Fin n) :
    rowSig i (inputVec hn table q p) = decide (i=q) := by
  unfold rowSig inputVec inputs
  rw [List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt), List.getD_eq_getElem _ _ (by simpa using i.isLt),
    List.getElem_ofFn]

private theorem patSig_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p) (k : Fin (w+1)) :
    patSig k (inputVec hn table q p) = p k := by
  unfold patSig inputVec inputs
  rw [List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using k.isLt), List.getElem_ofFn]

private def negInput {n w : ℕ} (j : Fin n ⊕ Fin (w+1)) : Sig (InCount n w) :=
  j.elim (fun i => notS (rowSig i)) (fun k => notS (patSig k))

private noncomputable def queryEq {n w : ℕ} (e : E w) : Sig (InCount n w) :=
  allS Finset.univ (fun k => if decode e k then patSig k else notS (patSig k))

private noncomputable def Prep (n w : ℕ) : SigSet (InCount n w) :=
  Set.range (negInput (n:=n) (w:=w)) ∪ Set.range (queryEq (n:=n) (w:=w))

private theorem prepBuild {n w : ℕ} {Z : SigSet (InCount n w)} (hz : Raw _ ⊆ Z) :
    Build Z (Prep n w) ((n+(w+1)) + 2^(w+1)*(w+2)) (n+(w+1)) := by
  have h1 : Build Z (Set.range (negInput (n:=n) (w:=w))) (n+(w+1)) (n+(w+1)) := by
    simpa only [Fintype.card_sum, Fintype.card_fin, mul_one] using
      (batchR (A:=Z) negInput 1 1 (fun j => by
        cases j with
        | inl i => exact notB (hz (rowSig_mem i))
        | inr k => exact notB (hz (patSig_mem k))))
  have h2 : Build (Z ∪ Set.range (negInput (n:=n) (w:=w))) (Set.range (queryEq (n:=n) (w:=w)))
      (2^(w+1)*(w+2)) 0 := by
    simpa only [Fintype.card_fin, Nat.mul_zero] using
      (batchR (A:=Z ∪ Set.range (negInput (n:=n) (w:=w))) (queryEq (n:=n) (w:=w)) (w+2) 0
        (fun e => by
          unfold queryEq
          simpa only [Finset.card_univ, Fintype.card_fin] using
            allSB (A:=Z ∪ Set.range (negInput (n:=n) (w:=w))) Finset.univ
              (fun k => if decode e k then patSig k else notS (patSig k))
              (fun k _ => by
                cases hk : decode e k
                · simpa [hk] using (show notS (patSig k) ∈ Z ∪ Set.range (negInput (n:=n) (w:=w)) from
                    Or.inr ⟨Sum.inr k,rfl⟩)
                · simpa [hk] using (show patSig k ∈ Z ∪ Set.range (negInput (n:=n) (w:=w)) from
                    Or.inl (hz (patSig_mem k))))))
  simpa only [Prep, Nat.add_zero] using seqB h1 h2

private noncomputable def forced {n w : ℕ} (hn : 0 < n) (A : ℕ → Mask (InCount n w) w) (k : ℕ) (e : E w) :
    Sig (InCount n w) :=
  orS (andS (rowSig (rowAt hn k)) (queryEq e))
    (andS (notS (rowSig (rowAt hn k))) (cut n A k e))

private noncomputable def ForcedSet {n w : ℕ} (hn : 0 < n) (A : ℕ → Mask (InCount n w) w) : SigSet (InCount n w) :=
  Set.range (fun p : Fin n × E w => forced hn A p.1.val p.2)

private theorem forced_mem {n w : ℕ} {hn : 0 < n} {A : ℕ → Mask (InCount n w) w}
    {k : ℕ} (hk : k<n) (e : E w) : forced hn A k e ∈ ForcedSet hn A := ⟨(⟨k,hk⟩,e),rfl⟩

private theorem forcedBuild {n w : ℕ} (hn : 0 < n) (A : ℕ → Mask (InCount n w) w)
    {Z : SigSet (InCount n w)} (hz : Raw _ ⊆ Z) (hp : Prep n w ⊆ Z) (hc : SweepSet n A ⊆ Z) :
    Build Z (ForcedSet hn A) (n * 2^(w+1) * 3) 0 := by
  simpa only [ForcedSet, Fintype.card_prod, Fintype.card_fin, Nat.mul_zero] using
    (batchR (A:=Z) (fun p : Fin n × E w => forced hn A p.1.val p.2) 3 0
      (fun p => twoAndOrB (hz (rowSig_mem _)) (hp (Or.inr ⟨_,rfl⟩))
        (hp (Or.inl ⟨Sum.inl _,rfl⟩)) (hc (cut_mem p.1.isLt p.2))))

private theorem queryEq_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p) (e : E w) :
    queryEq e (inputVec hn table q p) = decide (e = encode p) := by
  have ht : queryEq e (inputVec hn table q p) = true ↔ decode e = p := by
    rw [queryEq, allS_true]
    simp only [Finset.mem_univ, true_implies]
    rw [funext_iff]
    apply forall_congr'
    intro k
    cases hk : decode e k <;> cases hp : p k <;> simp [hk, hp, patSig_read]
  have he : decode e = p ↔ e = encode p := by
    constructor
    · intro h
      rw [← h, encode_decode]
    · rintro rfl
      exact decode_encode p
  exact Bool.eq_iff_iff.mpr (ht.trans (he.trans (by simp)))

private theorem forced_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p)
    (A : ℕ → Mask (InCount n w) w) (i : Fin n) (e : E w) :
    let x := inputVec hn table q p
    forced hn A i.val e x = forceEdge (fun j f => cut n A j f x) q.val (encode p) i.val e := by
  dsimp only
  unfold forced orS andS notS
  rw [rowAt_fin, rowSig_read, queryEq_read]
  by_cases h : i=q
  · subst i
    simp [forceEdge]
  · have h' : i.val ≠ q.val := fun hval => h (Fin.ext hval)
    simp [forceEdge, h, h']


private theorem cut_congr {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) (x y : Fin m → Bool)
    (h : ∀ j e, A j e x = A j e y) (k : ℕ) (e : E w) : cut n A k e x = cut n A k e y := by
  have hb : ∀ l u v, rear n A l u v x = rear n A l u v y := by
    intro l
    induction l with
    | zero => simp [rear, diag]
    | succ l ih => simp [rear, binaryStep, orS, andS, h, ih]
  have hf : ∀ l,
      (∀ u v, (sweep n A l).1 u v x = (sweep n A l).1 u v y) ∧
      (∀ e, (sweep n A l).2 e x = (sweep n A l).2 e y) := by
    intro l
    induction l with
    | zero => simp [sweep, diag]
    | succ l ih =>
      have hstep : ∀ e, weaken (A l) (sweep n A l).1 (suffix n A (l+1)) e x =
          weaken (A l) (sweep n A l).1 (suffix n A (l+1)) e y := by
        intro e
        simp [weaken, orS, notS, andS, context, anyS, suffix, h, hb, ih.1]
      constructor
      · intro u v
        simp [sweep, binaryStep, orS, andS, ih.1, hstep]
      · exact hstep
  exact (hf (k+1)).2 e

private noncomputable def reducedTable {n w : ℕ} (hn : 0 < n) (table : Table n w) : Table n w :=
  fun i p => cut n (tableSig hn) i.val (encode p) (inputVec hn table ⟨0,hn⟩ (fun _ => false))

private theorem reduced_read {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p) (i : Fin n) (a) :
    cut n (tableSig hn) i.val (encode a) (inputVec hn table q p) = reducedTable hn table i a := by
  apply cut_congr
  intro j e
  exact (addr_read hn table q p (rowAt hn j) e).trans (addr_read hn table ⟨0,hn⟩ _ _ e).symm

private theorem closed_windows {m w n : ℕ} (hn : 0 < n) (A : ℕ → Mask m w) (x : Fin m → Bool)
    (table : Table n w) (ht : ∀ i : Fin n, ∀ e, A i.val e x = table i (decode e)) :
    (∃ a : Fin n → Bool, ∀ i, table i (win hn a i) = true) ↔
      ∃ s : S w, Reach src dst (fun j e => A j e x) 0 n s s := by
  rw [← cycle_iff_reach hn]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun i => encode (win hn a i), win_cycle hn a, fun i => by simpa [ht] using ha i⟩
  · rintro ⟨e, he, ha⟩
    refine ⟨fun i => (e i).val.testBit 0, fun i => ?_⟩
    rw [cycle_win he i, ← ht]
    exact ha i

private def clauseOf {n w : ℕ} (hn : 0 < n) (i : Fin n) (p : Fin (w+1) → Bool) :
    PEqualNP.ProofComplexity.Clause (Fin n) :=
  Finset.univ.image (fun k : Fin (w+1) => (pos hn i k, !(p k)))

private def clausesOf {n w : ℕ} (hn : 0 < n) (table : Table n w) :
    Set (PEqualNP.ProofComplexity.Clause (Fin n)) :=
  {D | ∃ i p, table i p = false ∧ D = clauseOf hn i p}

private theorem clause_unsat_iff {n w : ℕ} (hn : 0 < n) (a : Fin n → Bool)
    (i : Fin n) (p : Fin (w+1) → Bool) :
    ¬ PEqualNP.ProofComplexity.ClauseSat a (clauseOf hn i p) ↔ win hn a i = p := by
  unfold PEqualNP.ProofComplexity.ClauseSat clauseOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hs
    funext k
    have hh : a (pos hn i k) ≠ !(p k) := fun hk => hs ⟨_, ⟨k,rfl⟩,hk⟩
    cases hp : p k <;> cases ha : a (pos hn i k) <;> simp_all [win]
  · intro h
    rintro ⟨_, ⟨k,rfl⟩,hk⟩
    have hh := congrFun h k
    change a (pos hn i k) = p k at hh
    rw [hh] at hk
    change p k = !(p k) at hk
    cases hv : p k <;> simp [hv] at hk

private theorem clauses_sat_iff {n w : ℕ} (hn : 0 < n) (table : Table n w) (a : Fin n → Bool) :
    PEqualNP.ProofComplexity.Satisfies a (clausesOf hn table) ↔ ∀ i, table i (win hn a i) = true := by
  constructor
  · intro h i
    cases hh : table i (win hn a i)
    · exact False.elim ((clause_unsat_iff hn a i _).mpr rfl (h _ ⟨i,_,hh,rfl⟩))
    · rfl
  · intro h D hD
    obtain ⟨i,p,hbad,rfl⟩ := hD
    by_contra hcl
    have he := (clause_unsat_iff hn a i p).mp hcl
    have hh := h i
    rw [he, hbad] at hh
    contradiction

private theorem irredundant {n w : ℕ} (hn : 0 < n) (table : Table n w)
    (hw : ∀ i p, table i p = false → ∃ a : Fin n → Bool,
      win hn a i = p ∧ ∀ j, j ≠ i → table j (win hn a j) = true) :
    ∀ D ∈ clausesOf hn table, ∃ a, ¬ PEqualNP.ProofComplexity.ClauseSat a D ∧
      PEqualNP.ProofComplexity.Satisfies a (clausesOf hn table \ {D}) := by
  intro D hD
  obtain ⟨i,p,hi,rfl⟩ := hD
  obtain ⟨a,ha,hothers⟩ := hw i p hi
  refine ⟨a,(clause_unsat_iff hn a i p).mpr ha, ?_⟩
  intro D hD
  obtain ⟨⟨j,q,hj,rfl⟩, hne⟩ := hD
  by_contra hs
  have he := (clause_unsat_iff hn a j q).mp hs
  by_cases hji : j=i
  · subst j
    have heq := he.symm.trans ha
    apply hne
    rw [heq]
    exact Set.mem_singleton _
  · have ht := hothers j hji
    rw [he, hj] at ht
    contradiction


private abbrev WPair (w : ℕ) := S w × S w

private def wHigh {w : ℕ} (e : E w) : Bool := decide (2^w ≤ e.val)

private theorem wHighOut {w : ℕ} (u : S w) (b : Bool) : wHigh (outEdge u b) = b := by
  have hu := u.isLt
  change decide (2^w ≤ u.val + b.toNat * 2^w) = b
  cases b
  · simp [Nat.not_le_of_lt hu]
  · have h : 2^w ≤ u.val + 2^w := by omega
    simp [h]

private theorem wOutInverts {w : ℕ} (e : E w) : outEdge (src e) (wHigh e) = e := by
  have he : e.val < 2^w * 2 := by simpa only [pow_succ] using e.isLt
  apply Fin.ext
  change e.val % 2^w + (decide (2^w ≤ e.val)).toNat * 2^w = e.val
  by_cases h : 2^w ≤ e.val
  · have hs : e.val - 2^w < 2^w := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hs]
    simp [h, Nat.sub_add_cancel h]
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_not_ge h)]
    simp [h]

private theorem wInInverts {w : ℕ} (e : E w) : inEdge (dst e) (e.val.testBit 0) = e := by
  apply Fin.ext
  change 2 * (e.val / 2) + (e.val.testBit 0).toNat = e.val
  rw [Nat.testBit_zero]
  have hmod := Nat.mod_lt e.val (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div e.val 2
  by_cases h : e.val % 2 = 1 <;> simp [h] <;> omega

private def wNo {m w : ℕ} (B : ℕ → S w → S w → Sig m) (s : S w) : Sig m :=
  fun x => !(B 0 s s x)

private noncomputable def wEarlier {m w : ℕ} (B : ℕ → S w → S w → Sig m) (s : S w) : Sig m :=
  allS (Finset.univ.filter fun t : S w => t < s) (wNo B)

private noncomputable def wFirst {m w : ℕ} (B : ℕ → S w → S w → Sig m) (s : S w) : Sig m :=
  fun x => B 0 s s x && wEarlier B s x

private noncomputable def wInit {m w : ℕ} (B : ℕ → S w → S w → Sig m) (p : WPair w) : Sig m :=
  if p.1 = p.2 then wFirst B p.1 else fun _ => false

private theorem wFirst_true {m w : ℕ} (B : ℕ → S w → S w → Sig m) (s : S w) (x : Fin m → Bool) :
    wFirst B s x = true ↔ B 0 s s x = true ∧ ∀ t < s, B 0 t t x = false := by
  have hno (t : S w) : wNo B t x = true ↔ B 0 t t x = false := by
    unfold wNo
    cases B 0 t t x <;> decide
  simp only [wFirst, Bool.and_eq_true_iff, wEarlier, allS_true, Finset.mem_filter,
    Finset.mem_univ, true_and, hno]

private theorem wInit_unique {m w : ℕ} {B : ℕ → S w → S w → Sig m} {x : Fin m → Bool}
    (h : ∃ s, B 0 s s x = true) :
    ∃ s, B 0 s s x = true ∧ ∀ p, wInit B p x = true ↔ p = (s, s) := by
  classical
  have hval : ∃ j : ℕ, ∃ s : S w, s.val = j ∧ B 0 s s x = true := by
    obtain ⟨s, hs⟩ := h
    exact ⟨s.val, s, rfl, hs⟩
  obtain ⟨s, hsval, hs⟩ := Nat.find_spec hval
  have hlt (t : S w) (ht : t < s) : B 0 t t x = false := by
    cases hbt : B 0 t t x
    · rfl
    · have hm := Nat.find_min' hval (show ∃ u : S w, u.val = t.val ∧ B 0 u u x = true from ⟨t, rfl, hbt⟩)
      change t.val < s.val at ht
      omega
  refine ⟨s, hs, ?_⟩
  rintro ⟨t,u⟩
  constructor
  · intro htu
    have htu' : t = u := by
      by_contra hne
      simp [wInit, hne] at htu
    subst u
    have ht := (wFirst_true B t x).mp (by simpa [wInit] using htu)
    have hts : t = s := by
      rcases lt_trichotomy t s with hts | hts | hst
      · exact (Bool.false_ne_true (by simpa only [hlt t hts] using ht.1)).elim
      · exact hts
      · exact (Bool.false_ne_true (by simpa only [ht.2 s hst] using hs)).elim
    simp [hts]
  · intro heq
    have hts : t = s := congrArg Prod.fst heq
    have hus : u = s := congrArg Prod.snd heq
    subst t
    subst u
    simpa [wInit] using (wFirst_true B s x).mpr ⟨hs, hlt⟩

section Layer

variable {m n w : ℕ}
variable (Q : Fin n → E w → Sig m) (B : ℕ → S w → S w → Sig m)

private def wViable (i : Fin n) (p : WPair w) (b : Bool) : Sig m :=
  fun x => Q i (outEdge p.2 b) x && B (i.val + 1) (dst (outEdge p.2 b)) p.1 x

-- Prefer false. An active pair is suffix-viable, so when false fails,
-- the recurrence already guarantees the true branch.
private def wPick (i : Fin n) (T : WPair w → Sig m) (a : WPair w × Bool) : Sig m :=
  fun x => T a.1 x && (if a.2 then !(wViable Q B i a.1 false x) else wViable Q B i a.1 false x)

-- Index the two incoming edges by their low bit, then recover each edge's
-- outgoing branch at its source.
private def wPred (p : WPair w) (b : Bool) : WPair w × Bool :=
  let e := inEdge p.2 b
  ((p.1, src e), wHigh e)

private def wMove (i : Fin n) (T : WPair w → Sig m) (p : WPair w) : Sig m :=
  fun x => wPick Q B i T (wPred p false) x || wPick Q B i T (wPred p true) x

private def wHead (a : WPair w × Bool) : Bool := (outEdge a.1.2 a.2).val.testBit 0

private noncomputable def wReport (i : Fin n) (T : WPair w → Sig m) : Sig m :=
  anyS (Finset.univ.filter fun a : WPair w × Bool => wHead a = true) (wPick Q B i T)

private noncomputable def wLayer : ℕ → WPair w → Sig m
  | 0 => wInit B
  | k+1 => if hi : k < n then wMove Q B ⟨k, hi⟩ (wLayer k) else wLayer k

private def wState (s : S w) (x : Fin m → Bool) : ℕ → S w
  | 0 => s
  | k+1 => if hi : k < n then
      let u := wState s x k
      dst (outEdge u (!(wViable Q B ⟨k, hi⟩ (s,u) false x)))
    else wState s x k

private theorem wPick_true (i : Fin n) (T : WPair w → Sig m) (a : WPair w × Bool) (x : Fin m → Bool) :
    wPick Q B i T a x = true ↔ T a.1 x = true ∧ a.2 = !(wViable Q B i a.1 false x) := by
  obtain ⟨p,b⟩ := a
  cases b <;> cases h : wViable Q B i p false x <;> simp [wPick, h]

private theorem wMove_true (i : Fin n) (T : WPair w → Sig m) (p : WPair w) (x : Fin m → Bool) :
    wMove Q B i T p x = true ↔ ∃ u b, wPick Q B i T ((p.1, u),b) x = true ∧ dst (outEdge u b) = p.2 := by
  simp only [wMove, Bool.or_eq_true_iff]
  constructor
  · intro hp
    have aux (c : Bool) (hc : wPick Q B i T (wPred p c) x = true) :
        ∃ u b, wPick Q B i T ((p.1, u),b) x = true ∧ dst (outEdge u b) = p.2 := by
      exact ⟨src (inEdge p.2 c), wHigh (inEdge p.2 c), hc, by rw [wOutInverts, dst_inEdge]⟩
    exact hp.elim (aux false) (aux true)
  · rintro ⟨u,b,h,hd⟩
    let e := outEdge u b
    have hp : wPred p (e.val.testBit 0) = ((p.1,u),b) := by
      change ((p.1, src (inEdge p.2 (e.val.testBit 0))), wHigh (inEdge p.2 (e.val.testBit 0))) = _
      have hd' : dst e = p.2 := hd
      rw [← hd', wInInverts]
      simp [e, wHighOut]
    have hc : wPick Q B i T (wPred p (e.val.testBit 0)) x = true := by
      rw [hp]
      exact h
    cases hc' : e.val.testBit 0
    · exact Or.inl (by simpa only [hc'] using hc)
    · exact Or.inr (by simpa only [hc'] using hc)

private theorem wReport_true (i : Fin n) (T : WPair w → Sig m) (x : Fin m → Bool) :
    wReport Q B i T x = true ↔ ∃ a, wHead a = true ∧ wPick Q B i T a x = true := by
  simp [wReport, anyS_true]

private theorem wViable_chosen (x : Fin m → Bool) (i : Fin n) (p : WPair w)
    (hrec : B i.val p.2 p.1 x = (wViable Q B i p false x || wViable Q B i p true x))
    (h : B i.val p.2 p.1 x = true) :
    wViable Q B i p (!(wViable Q B i p false x)) x = true := by
  have hv := hrec.symm.trans h
  cases hf : wViable Q B i p false x
  · simpa [hf] using hv
  · exact hf

private theorem wCorrect (hn : 0 < n) (x : Fin m → Bool)
    (hbase : ∀ u s, B n u s x = decide (u = s))
    (hrec : ∀ (i : Fin n) u s, B i.val u s x =
      (wViable Q B i (s,u) false x || wViable Q B i (s,u) true x))
    (hstart : ∃ s, B 0 s s x = true) :
    ∃ e : Fin n → E w, IsCycle hn e ∧ (∀ i, Q i (e i) x = true) ∧
      ∀ i, wReport Q B i (wLayer Q B i.val) x = (e i).val.testBit 0 := by
  obtain ⟨s, hs, hinit⟩ := wInit_unique hstart
  let u := wState Q B s x
  let b (i : Fin n) := !(wViable Q B i (s, u i.val) false x)
  let e (i : Fin n) := outEdge (u i.val) (b i)
  have hu (i : Fin n) : u (i.val + 1) = dst (e i) := by
    simp only [u, b, e, wState, dif_pos i.isLt]
  -- Every layer has exactly one active pair, and its suffix still closes.
  have hgood (k : ℕ) (hk : k ≤ n) : B k (u k) s x = true ∧
      ∀ p, wLayer Q B k p x = true ↔ p = (s, u k) := by
    induction k with
    | zero => exact ⟨hs, hinit⟩
    | succ k ih =>
      have hlt : k < n := by omega
      let i : Fin n := ⟨k, hlt⟩
      obtain ⟨hval, hhot⟩ := ih (Nat.le_of_lt hlt)
      have hv := (Bool.and_eq_true_iff.mp (wViable_chosen Q B x i (s,u k) (hrec i (u k) s) hval)).2
      refine ⟨?_, ?_⟩
      · rw [show u (k+1) = dst (e i) from hu i]
        exact hv
      · intro p
        rw [wLayer, dif_pos hlt, wMove_true]
        constructor
        · rintro ⟨v,c,hp,hd⟩
          obtain ⟨hp, hc⟩ := (wPick_true Q B i _ _ x).mp hp
          have he := (hhot (p.1,v)).mp hp
          have h1 : p.1 = s := congrArg Prod.fst he
          have h2 : v = u k := congrArg Prod.snd he
          have hc' : c = b i := by simpa only [h1, h2] using hc
          have hd' : dst (e i) = p.2 := by simpa only [h2, hc'] using hd
          exact Prod.ext h1 (hd'.symm.trans (hu i).symm)
        · intro hp
          refine ⟨u k, b i, (wPick_true Q B i _ _ x).mpr ⟨?_, ?_⟩, ?_⟩
          · apply (hhot (p.1,u k)).mpr
            exact Prod.ext (show p.1 = s from congrArg Prod.fst hp) rfl
          · have hps : p.1 = s := congrArg Prod.fst hp
            change b i = !(wViable Q B i (p.1,u k) false x)
            rw [hps]
          · exact (hu i).symm.trans (congrArg Prod.snd hp).symm
  have hclose : u n = s := by
    have h := (hgood n le_rfl).1
    rw [hbase] at h
    exact of_decide_eq_true h
  have hsel (i : Fin n) (a : WPair w × Bool) :
      wPick Q B i (wLayer Q B i.val) a x = true ↔ a = ((s,u i.val),b i) := by
    rw [wPick_true, (hgood i.val i.isLt.le).2]
    rcases a with ⟨p,c⟩
    constructor
    · rintro ⟨hp,hc⟩
      rw [hp] at hc
      exact Prod.ext hp hc
    · intro he
      have hp : p = (s,u i.val) := congrArg Prod.fst he
      have hc : c = b i := congrArg Prod.snd he
      exact ⟨hp, by simpa only [hp] using hc⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    rw [← hu i, show src (e (next hn i)) = u (next hn i).val from src_outEdge _ _]
    change u (i.val + 1) = u ((i.val + 1) % n)
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
    · have heq : i.val + 1 = n := by omega
      rw [heq, Nat.mod_self, hclose] <;> rfl
  · intro i
    exact (Bool.and_eq_true_iff.mp (wViable_chosen Q B x i (s,u i.val) (hrec i (u i.val) s)
      (hgood i.val i.isLt.le).1)).1
  · intro i
    have hbit : wReport Q B i (wLayer Q B i.val) x = true ↔ (e i).val.testBit 0 = true := by
      rw [wReport_true]
      simp only [hsel]
      constructor
      · rintro ⟨_,ha,rfl⟩
        exact ha
      · intro he
        exact ⟨((s,u i.val),b i), he, rfl⟩
    exact Bool.eq_iff_iff.mpr hbit

private theorem wBatch {α : Type*} [Fintype α] {A : Set (Sig m)} (f : α → Sig m) (c : ℕ)
    (hf : ∀ a, Build A {f a} c c) : Build A (Set.range f) (Fintype.card α * c) (Fintype.card α * c) := by
  classical
  have H := listB (A:=A) (fun a => {f a}) c c (Finset.univ : Finset α).toList (fun a _ => hf a)
  apply relaxB H le_rfl _ (by simp) (by simp)
  rintro _ ⟨a,rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨by simp, rfl⟩⟩)

private theorem wInitBuild {A : Set (Sig m)} (hB : ∀ s, B 0 s s ∈ A) :
    Build A (Set.range (wInit B)) (5 * (2^w)^2) (5 * (2^w)^2) := by
  classical
  let d : ℕ := 2^w
  have hd : 1 ≤ d := Nat.two_pow_pos _
  have Hno : Build A (Set.range (wNo B)) d d := by
    simpa [d] using wBatch (wNo B) 1 (fun s => notB (hB s))
  let A₁ := A ∪ Set.range (wNo B)
  have hFirst (s : S w) : Build A₁ {wFirst B s} (d+2) (d+2) := by
    let ss := Finset.univ.filter fun t : S w => t < s
    have H₁ : Build A₁ {wEarlier B s} (ss.card + 1) 0 :=
      allSB ss (wNo B) (fun t _ => Or.inr (Set.mem_range_self t))
    have H₂ : Build (A₁ ∪ {wEarlier B s}) {wFirst B s} 1 0 :=
      andB (Or.inl (Or.inl (hB s))) (Or.inr rfl)
    refine relaxB (seqB H₁ H₂) le_rfl (fun _ h => Or.inr (Or.inr h)) ?_ (by omega)
    have hc : ss.card ≤ d := by
      simpa [ss, d] using Finset.card_filter_le (Finset.univ : Finset (S w)) (fun t => t < s)
    omega
  have Hfirst : Build A₁ (Set.range (wFirst B)) (d * (d+2)) (d * (d+2)) := by
    simpa [d] using wBatch (wFirst B) (d+2) hFirst
  have Hfalse := constB (A:= A₁ ∪ Set.range (wFirst B)) false
  have Htail := seqB Hfirst Hfalse
  refine relaxB (seqB Hno Htail) le_rfl ?_ ?_ ?_
  · rintro _ ⟨p,rfl⟩
    by_cases hp : p.1 = p.2
    · exact Or.inr (Or.inr (Or.inl ⟨p.1, by simp [wInit, hp]⟩))
    · exact Or.inr (Or.inr (Or.inr (by simp [wInit, hp])))
  · change d + (d * (d+2) + 1) ≤ 5*d^2
    nlinarith [Nat.mul_le_mul_right d hd]
  · change d + (d * (d+2) + 0) ≤ 5*d^2
    nlinarith [Nat.mul_le_mul_right d hd]

private theorem wPickBuild {A : Set (Sig m)} (i : Fin n) (T : WPair w → Sig m)
    (hT : ∀ p, T p ∈ A) (hQ : ∀ i e, Q i e ∈ A) (hB : ∀ u s, B (i.val+1) u s ∈ A) :
    Build A (Set.range (wPick Q B i T)) (2 * (2^w)^2 * 3) (2 * (2^w)^2 * 3) := by
  classical
  have hp (a : WPair w × Bool) : Build A {wPick Q B i T a} 3 3 := by
    obtain ⟨p,b⟩ := a
    let V := wViable Q B i p false
    have HV : Build A {V} 1 0 := andB (hQ i (outEdge p.2 false)) (hB _ _)
    cases b
    · have H : Build (A ∪ {V}) {wPick Q B i T (p,false)} 1 0 := by
        exact andB (Or.inl (hT p)) (Or.inr (show V = V from rfl))
      exact relaxB (seqB HV H) le_rfl (fun _ h => Or.inr (Or.inr h)) (by decide) (by decide)
    · let N : Sig m := fun x => !(V x)
      have HN : Build (A ∪ {V}) {N} 1 1 := notB (Or.inr (show V = V from rfl))
      have H : Build ((A ∪ {V}) ∪ {N}) {wPick Q B i T (p,true)} 1 0 := by
        exact andB (Or.inl (Or.inl (hT p))) (Or.inr (show N = N from rfl))
      exact relaxB (seqB HV (seqB HN H)) le_rfl
        (fun _ h => Or.inr (Or.inr (Or.inr h))) (by decide) (by decide)
  simpa [Fintype.card_prod, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    wBatch (wPick Q B i T) 3 hp

private theorem wStepBuild {A : Set (Sig m)} (i : Fin n) (T : WPair w → Sig m)
    (hT : ∀ p, T p ∈ A) (hQ : ∀ i e, Q i e ∈ A) (hB : ∀ u s, B (i.val+1) u s ∈ A) :
    Build A (Set.range (wMove Q B i T) ∪ {wReport Q B i T}) (12 * (2^w)^2) (12 * (2^w)^2) := by
  classical
  let d : ℕ := 2^w
  have hd : 1 ≤ d := Nat.two_pow_pos _
  have HP := wPickBuild Q B i T hT hQ hB
  let A₁ := A ∪ Set.range (wPick Q B i T)
  have hP (a : WPair w × Bool) : wPick Q B i T a ∈ A₁ := Or.inr (Set.mem_range_self a)
  have HM : Build A₁ (Set.range (wMove Q B i T)) (d^2) (d^2) := by
    have HM' (p : WPair w) : Build A₁ {wMove Q B i T p} 1 1 :=
      relaxB (orB (hP (wPred p false)) (hP (wPred p true))) le_rfl
        (fun _ h => Or.inr h) le_rfl (by decide)
    simpa [d, Fintype.card_prod, pow_two] using wBatch (wMove Q B i T) 1 HM'
  let ss := Finset.univ.filter fun a : WPair w × Bool => wHead a = true
  have HR : Build (A₁ ∪ Set.range (wMove Q B i T)) {wReport Q B i T} (ss.card+1) 0 :=
    anySB ss (wPick Q B i T) (fun a _ => Or.inl (hP a))
  have hc : ss.card ≤ 2*d^2 := by
    simpa [ss, d, Fintype.card_prod, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Finset.card_filter_le (Finset.univ : Finset (WPair w × Bool)) (fun a => wHead a = true)
  refine relaxB (seqB HP (seqB HM HR)) le_rfl (fun _ h => Or.inr (Or.inr h)) ?_ ?_
  · change 2*d^2*3 + (d^2 + (ss.card+1)) ≤ 12*d^2
    nlinarith [Nat.mul_le_mul_right d hd]
  · change 2*d^2*3 + (d^2 + 0) ≤ 12*d^2
    nlinarith

private noncomputable def wPast (k : ℕ) : Set (Sig m) :=
  {a | ∃ i : Fin n, i.val < k ∧ a = wReport Q B i (wLayer Q B i.val)}

private theorem wLoopBuild {A : Set (Sig m)} (hQ : ∀ i e, Q i e ∈ A)
    (hB : ∀ k ≤ n, ∀ u s, B k u s ∈ A)
    (k : ℕ) (hk : k ≤ n) :
    Build A (Set.range (wLayer Q B k) ∪ wPast Q B k)
      (5*(2^w)^2 + k*(12*(2^w)^2)) (5*(2^w)^2 + k*(12*(2^w)^2)) := by
  induction k with
  | zero =>
    refine relaxB (wInitBuild B (fun s => hB 0 (Nat.zero_le _) s s)) le_rfl ?_ (by simp) (by simp)
    rintro a (ha | ⟨i,hi,_⟩)
    · exact Or.inr ha
    · omega
  | succ k ih =>
    have hl : k < n := by omega
    let i : Fin n := ⟨k, hl⟩
    let A₁ := A ∪ (Set.range (wLayer Q B k) ∪ wPast Q B k)
    have H₁ := ih (Nat.le_of_lt hl)
    have H₂ := wStepBuild Q B (A:=A₁) i (wLayer Q B k)
      (fun p => Or.inr (Or.inl (Set.mem_range_self p))) (fun j e => Or.inl (hQ j e))
      (fun u s => Or.inl (hB (k+1) hk u s))
    refine relaxB (seqB H₁ H₂) le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_assoc])
      (by simp [Nat.succ_mul, Nat.add_assoc])
    rintro a (ha | ⟨j,hj,rfl⟩)
    · rw [wLayer, dif_pos hl] at ha
      exact Or.inr (Or.inr (Or.inl ha))
    · by_cases hj' : j.val < k
      · exact Or.inr (Or.inl (Or.inr ⟨j,hj',rfl⟩))
      · have heq : j = i := Fin.ext (by change j.val = k; omega)
        subst j
        exact Or.inr (Or.inr (Or.inr rfl))

/-- Extract a cycle from the suffix table and schedule its head bits.  The table
    recurrence and the accepting diagonal need only hold pointwise on the input. -/
theorem buildWitness (hn : 0 < n) {A : Set (Sig m)}
    (hQ : ∀ i e, Q i e ∈ A) (hB : ∀ k ≤ n, ∀ u s, B k u s ∈ A)
    (hbase : ∀ u s x, B n u s x = decide (u = s))
    (hrec : ∀ (i : Fin n) u s x, B i.val u s x =
      ((Q i (outEdge u false) x && B (i.val+1) (dst (outEdge u false)) s x) ||
       (Q i (outEdge u true) x && B (i.val+1) (dst (outEdge u true)) s x))) :
    ∃ answer : Fin n → Sig m,
      Build A (Set.range answer) (24*(n+1)*4^w) (24*(n+1)*4^w) ∧
      ∀ x, (∃ s, B 0 s s x = true) →
        ∃ e : Fin n → E w, IsCycle hn e ∧ (∀ i, Q i (e i) x = true) ∧
          ∀ i, answer i x = (e i).val.testBit 0 := by
  refine ⟨fun i => wReport Q B i (wLayer Q B i.val), ?_, ?_⟩
  · have hc : (2^w : ℕ)^2 = 4^w := by rw [pow_two, ← mul_pow] <;> norm_num
    have hcost : 5*(2^w)^2 + n*(12*(2^w)^2) ≤ 24*(n+1)*4^w := by
      rw [hc]
      calc
        5*4^w + n*(12*4^w) = (5 + n*12)*4^w := by ring
        _ ≤ (24*(n+1))*4^w := Nat.mul_le_mul_right _ (by omega)
    refine relaxB (wLoopBuild Q B hQ hB n le_rfl) le_rfl ?_ hcost hcost
    rintro _ ⟨i,rfl⟩
    exact Or.inr (Or.inr ⟨i,i.isLt,rfl⟩)
  · intro x hx
    exact wCorrect Q B hn x (fun u s => hbase u s x) (fun i u s => hrec i u s x) hx

end Layer



private theorem reduced_monotone {n w : ℕ} (hn : 0 < n) (table : Table n w)
    (i : Fin n) (p : Fin (w+1) → Bool) : table i p = true → reducedTable hn table i p = true := by
  intro h
  apply cut_monotone
  simpa only [tableSig_read, decode_encode] using h

private theorem same_words {n w : ℕ} (hn : 0 < n) (table : Table n w) (a : Fin n → Bool) :
    (∀ i, table i (win hn a i) = true) ↔ ∀ i, reducedTable hn table i (win hn a i) = true := by
  refine ⟨fun h i => reduced_monotone hn table _ _ (h i), ?_⟩
  intro h i
  let x := inputVec hn table ⟨0,hn⟩ (fun _ => false)
  let A := tableSig hn (w:=w)
  let e (j : Fin n) : E w := encode (win hn a j)
  obtain ⟨v,s,hv⟩ := walk_of_cycle (A:=fun j f => cut n A j f x) (show IsCycle hn e from win_cycle hn a) h
  have ht := cut_walk_same A x hv i.val i.isLt
  rw [rowAt_fin] at ht
  simpa only [A, x, e, tableSig_read, decode_encode] using ht

private theorem forced_diagonal {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p)
    (h : reducedTable hn table q p = false) :
    ∃ s, suffix n (forced hn (tableSig hn)) 0 s s (inputVec hn table q p) = true := by
  let A := tableSig hn (w:=w)
  let x := inputVec hn table q p
  obtain ⟨s,hs⟩ := cut_witness A x q.isLt ((reduced_read hn table q p q p).trans h)
  refine ⟨s, (suffix_correct (forced hn A) x 0 (Nat.zero_le _) s s).mpr ?_⟩
  simp only [Nat.sub_zero]
  apply reach_mono src dst hs
  intro j hj f hf
  simpa only [Nat.zero_add] using (forced_read hn table q p A ⟨j,hj⟩ f).trans
    (show forceEdge (fun j e => cut n A j e x) q.val (encode p) j f = true from by simpa only [Nat.zero_add] using hf)

private theorem query_windows {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p)
    (answer : Fin n → Bool) (e : Fin n → E w) (he : IsCycle hn e)
    (ha : ∀ j, forced hn (tableSig hn) j.val (e j) (inputVec hn table q p) = true)
    (hb : ∀ j, answer j = (e j).val.testBit 0) :
    win hn answer q = p ∧ ∀ j, j ≠ q → reducedTable hn table j (win hn answer j) = true := by
  have hv (j : Fin n) : win hn answer j = decode (e j) := by
    rw [funext hb, cycle_win he j]
  have hf (j : Fin n) := (forced_read hn table q p (tableSig hn) j (e j)).symm.trans (ha j)
  constructor
  · have hq : e q = encode p := by simpa [forceEdge] using hf q
    rw [hv, hq, decode_encode]
  · intro j hj
    have hval : cut n (tableSig hn) j.val (e j) (inputVec hn table q p) = true := by
      simpa [forceEdge, show j.val ≠ q.val from fun h => hj (Fin.ext h)] using hf j
    rw [hv, ← reduced_read hn table q p, encode_decode]
    exact hval

private def Constants (m : ℕ) : SigSet m := {fun _ => false} ∪ {fun _ => true}

private theorem constantsBuild (m : ℕ) : Build (Raw m) (Constants m) 2 0 :=
  seqB (constB false) (constB true)

private noncomputable def satSignal {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) : Sig m :=
  anyS Finset.univ (fun s => suffix n A 0 s s)

private theorem satSignalBuild {m w : ℕ} (n : ℕ) (A : ℕ → Mask m w) {Z : SigSet m}
    (h : RearSet n A ⊆ Z) : Build Z {satSignal n A} (2^w+1) 0 := by
  simpa [satSignal] using anySB (A:=Z) (Finset.univ : Finset (S w))
    (fun s => suffix n A 0 s s) (fun s _ => h (suffix_mem s s))

private theorem satSignal_spec {n w : ℕ} (hn : 0 < n) (table : Table n w) (q p) :
    satSignal n (tableSig hn) (inputVec hn table q p) = true ↔
      PEqualNP.ProofComplexity.Satisfiable (clausesOf hn table) := by
  let x := inputVec hn table q p
  let A := tableSig hn (w:=w)
  have h₁ : satSignal n A x = true ↔ ∃ s : S w, Reach src dst (fun j e => A j e x) 0 n s s := by
    rw [satSignal, anyS_true]
    simp only [Finset.mem_univ, true_and]
    apply exists_congr
    intro s
    simpa only [Nat.sub_zero] using suffix_correct A x 0 (Nat.zero_le _) s s
  have h₂ := closed_windows hn A x table (tableSig_read hn table q p)
  rw [h₁, ← h₂]
  exact exists_congr (fun a => (clauses_sat_iff hn table a).symm)

private theorem finishAll {m k q : ℕ} {α : Type*} {Z : SigSet m}
    (h : Scheduled m k q Z) (out : Sig m) (ho : out ∈ Z) (bits : α → Sig m)
    (hb : ∀ a, bits a ∈ Z) :
    ∃ (C : Circuit) (wire : α → Fin (m+C.size)),
      C.size = k ∧ FanInTwo C ∧ ReadsBack m C ∧ C.output < m+C.size ∧
      (∀ x, C.eval (List.ofFn x) = out x) ∧
      (∀ j x, (C.wires (List.ofFn x)).getD (wire j).val false = bits j x) := by
  obtain ⟨gs,hgs,_,hr,hf,hw⟩ := h
  obtain ⟨i,hi,he⟩ := hw out ho
  have hbits (a : α) : ∃ j : Fin (m+gs.length), ∀ x,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD j.val false = bits a x := by
    obtain ⟨j,hj,hv⟩ := hw (bits a) (hb a)
    exact ⟨⟨j, by omega⟩,hv⟩
  choose wire hwire using hbits
  exact ⟨⟨gs,i⟩,wire,hgs,hf,hr,by change i < m+gs.length; omega,he,hwire⟩

private theorem cost_bound (n w : ℕ) :
    2 + n*(3*4^w) + n*(13*4^w) + ((n+(w+1)) + 2^(w+1)*(w+2)) +
      n*2^(w+1)*3 + n*(3*4^w) + 24*(n+1)*4^w + (2^w+1) ≤ 64*(n+1)*4^w := by
  have hz : 1 ≤ 4^w := pow_pos (show 0 < (4 : ℕ) by decide) w
  have hd := width_le w
  have hle := state_le_sq w
  have hw2 : w+2 ≤ 2*2^w := by omega
  have hm := Nat.mul_le_mul_left (2^(w+1)) hw2
  have hp : 2^(w+1)*(w+2) ≤ 4*4^w := by
    calc
      _ ≤ 2^(w+1)*(2*2^w) := hm
      _ = 4*4^w := by rw [pow_succ, ← sq_pow]; ring
  have hforce : n * 2^(w+1) * 3 ≤ 6 * n * 4^w := by
    rw [pow_succ]
    calc
      _ = (6*n) * 2^w := by ring
      _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (6*n) hle
  have hn : n ≤ n*4^w := by simpa using Nat.mul_le_mul_left n hz
  nlinarith only [hz, hd, hle, hp, hforce, hn]

set_option maxHeartbeats 1200000 in
private theorem design {n w : ℕ} (hn : 0 < n) :
    ∃ (answer : Fin n → Sig (InCount n w)) (C : Circuit)
      (allow : Fin n → (Fin (w+1) → Bool) → Fin (InCount n w+C.size))
      (word : Fin n → Fin (InCount n w+C.size)),
      FanInTwo C ∧ ReadsBack (InCount n w) C ∧ C.size ≤ 64*(n+1)*4^w ∧ C.output < InCount n w+C.size ∧
      (∀ x i p, (C.wires (List.ofFn x)).getD (allow i p).val false = cut n (tableSig hn) i.val (encode p) x) ∧
      (∀ x j, (C.wires (List.ofFn x)).getD (word j).val false = answer j x) ∧
      (∀ x : Fin (InCount n w) → Bool, C.eval (List.ofFn x) = satSignal n (tableSig hn (w:=w)) x) ∧
      (∀ x, (∃ s, suffix n (forced hn (tableSig hn)) 0 s s x = true) →
        ∃ e : Fin n → E w, IsCycle hn e ∧ (∀ i, forced hn (tableSig hn) i.val (e i) x = true) ∧
          ∀ i, answer i x = (e i).val.testBit 0) := by
  let I := InCount n w
  let A := tableSig hn (w:=w)
  let Q := forced hn A
  let Z0 := Raw I ∪ Constants I
  let Z1 := Z0 ∪ RearSet n A
  let Z2 := Z1 ∪ SweepSet n A
  let Z3 := Z2 ∪ Prep n w
  let Z4 := Z3 ∪ ForcedSet hn A
  let Z5 := Z4 ∪ RearSet n Q
  have raw0 : Raw I ⊆ Z0 := Set.subset_union_left
  have raw1 : Raw I ⊆ Z1 := raw0.trans Set.subset_union_left
  have raw2 : Raw I ⊆ Z2 := raw1.trans Set.subset_union_left
  have raw3 : Raw I ⊆ Z3 := raw2.trans Set.subset_union_left
  have f0 : (fun _ => false) ∈ Z0 := Or.inr (Or.inl rfl)
  have t0 : (fun _ => true) ∈ Z0 := Or.inr (Or.inr rfl)
  have b0 := constantsBuild I
  have b1 : Build Z0 (RearSet n A) (n*(3*4^w)) 0 :=
    rearBuild (fun k _ e => raw0 (tableSig_mem hn k e)) f0 t0
  have b2 : Build Z1 (SweepSet n A) (n*(13*4^w)) (n*(2*4^w)) :=
    sweepBuild (fun k _ e => raw1 (tableSig_mem hn k e)) Set.subset_union_right (Or.inl f0) (Or.inl t0)
  have b3 := prepBuild raw2
  have b4 := forcedBuild hn A raw3 Set.subset_union_right (fun _ h => Or.inl (Or.inr h))
  have b5 : Build Z4 (RearSet n Q) (n*(3*4^w)) 0 :=
    rearBuild (fun _ hk e => Or.inr (forced_mem hk e))
      (Or.inl (Or.inl (Or.inl (Or.inl f0)))) (Or.inl (Or.inl (Or.inl (Or.inl t0))))
  obtain ⟨answer,b6,hanswer⟩ := buildWitness (fun i e => Q i.val e) (suffix n Q) hn (A:=Z5)
    (fun i e => Or.inl (Or.inr (forced_mem i.isLt e))) (fun _ _ u s => Or.inr (suffix_mem u s))
    suffix_zero (fun i u s x => congrFun (congrFun (congrFun (suffix_step (A:=Q) i.isLt) u) s) x)
  let Z6 := Z5 ∪ Set.range answer
  have old6 : RearSet n A ⊆ Z6 :=
    fun _ h => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  have b7 := satSignalBuild n A old6
  obtain ⟨c0,h0,s0⟩ := b0.run (startSched I) le_rfl
  obtain ⟨c1,h1,s1⟩ := b1.run s0 le_rfl
  obtain ⟨c2,h2,s2⟩ := b2.run s1 le_rfl
  obtain ⟨c3,h3,s3⟩ := b3.run s2 le_rfl
  obtain ⟨c4,h4,s4⟩ := b4.run s3 le_rfl
  obtain ⟨c5,h5,s5⟩ := b5.run s4 le_rfl
  obtain ⟨c6,h6,s6⟩ := b6.run s5 le_rfl
  obtain ⟨c7,h7,s7⟩ := b7.run s6 le_rfl
  let bits : (Fin n × (Fin (w+1) → Bool)) ⊕ Fin n → Sig I :=
    Sum.elim (fun p => cut n A p.1.val (encode p.2)) answer
  have hbits (t) : bits t ∈ Z6 ∪ {satSignal n A} := by
    cases t with
    | inl p => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (cut_mem p.1.isLt (encode p.2)))))))
    | inr j => exact Or.inl (Or.inr ⟨j,rfl⟩)
  obtain ⟨C,wire,hsz,hfan,hback,hout,heval,hwire⟩ := finishAll s7 (satSignal n A) (Or.inr rfl) bits hbits
  refine ⟨answer,C,fun i p => wire (Sum.inl (i,p)), fun j => wire (Sum.inr j),
    hfan,hback,?_,hout,fun x i p => hwire (Sum.inl (i,p)) x,fun x j => hwire (Sum.inr j) x,heval,hanswer⟩
  exact hsz.le.trans ((Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (by simpa using h0) h1) h2) h3) h4) h5) h6) h7).trans
      (cost_bound n w))

private theorem finalStatement (n w : ℕ) (hn : 0 < n) :
    ∃ (C : Circuit) (allowWire : Fin n → (Fin (w+1) → Bool) → ℕ) (wordWire : Fin n → ℕ),
      FanInTwo C ∧ ReadsBack (InCount n w) C ∧ C.size ≤ 64*(n+1)*4^w ∧
      C.output < InCount n w+C.size ∧ (∀ i p, allowWire i p < InCount n w+C.size) ∧
      (∀ j, wordWire j < InCount n w+C.size) ∧ ∀ table : Table n w,
      ∃ reduced : Table n w,
        (∀ i p, table i p = true → reduced i p = true) ∧
        (∀ x : Fin n → Bool, (∀ i, table i (win hn x i) = true) ↔ ∀ i, reduced i (win hn x i) = true) ∧
        (∀ D ∈ clausesOf hn reduced, ∃ a : Fin n → Bool,
          ¬ PEqualNP.ProofComplexity.ClauseSat a D ∧
          PEqualNP.ProofComplexity.Satisfies a (clausesOf hn reduced \ {D})) ∧
        ∀ q p,
          let x := inputs hn table q p
          let a := fun j => (C.wires x).getD (wordWire j) false
          (∀ i r, (C.wires x).getD (allowWire i r) false = reduced i r) ∧
          (C.eval x = true ↔ PEqualNP.ProofComplexity.Satisfiable (clausesOf hn table)) ∧
          (reduced q p = false → win hn a q = p ∧ ∀ j, j ≠ q → reduced j (win hn a j) = true) := by
  obtain ⟨answer,C,allow,word,hfan,hback,hsz,hout,hallow,hword,heval,hanswer⟩ := design (w:=w) hn
  refine ⟨C,fun i p => (allow i p).val,fun j => (word j).val,hfan,hback,hsz,hout,
    fun i p => (allow i p).isLt,fun j => (word j).isLt,?_⟩
  intro table
  have witness (q : Fin n) (p : Fin (w+1) → Bool) (h : reducedTable hn table q p = false) :
      let a := fun j => answer j (inputVec hn table q p)
      win hn a q = p ∧ ∀ j, j ≠ q → reducedTable hn table j (win hn a j) = true := by
    let x := inputVec hn table q p
    obtain ⟨e,he,ha,hb⟩ := hanswer x (forced_diagonal hn table q p h)
    exact query_windows hn table q p (fun i => answer i x) e he ha hb
  refine ⟨reducedTable hn table,reduced_monotone hn table,same_words hn table,
    irredundant hn _ (fun q p h => ⟨fun j => answer j (inputVec hn table q p),witness q p h⟩),?_⟩
  intro q p
  dsimp only
  rw [← ofFn_inputVec hn table q p]
  refine ⟨fun i r => (hallow _ i r).trans (reduced_read hn table q p i r), ?_, ?_⟩
  · rw [heval]
    exact satSignal_spec hn table q p
  · intro h
    simp only [hword]
    exact witness q p h

end PEqualNP.Outside.L_pcx_224_aux

theorem PEqualNP.Outside.L_pcx_224 :
  ∀ (n w : ℕ) (hn : 0 < n),
    let T := n * 2 ^ (w + 1)
    let I := T + n + (w + 1)
    let pos := fun (start : Fin n) (offset : Fin (w + 1)) =>
      (⟨(start.val + offset.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let window := fun (word : Fin n → Bool) (row : Fin n) (k : Fin (w + 1)) =>
      word (pos row k)
    let clauses := fun (mask : Fin n → (Fin (w + 1) → Bool) → Bool) =>
      ({D | ∃ (r : Fin n) (p : Fin (w + 1) → Bool), mask r p = false ∧
        D = Finset.univ.image (fun b : Fin (w + 1) => (pos r b, !(p b)))} :
        Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (allowWire : Fin n → (Fin (w + 1) → Bool) → ℕ) (wordWire : Fin n → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
      C.size ≤ 64 * (n + 1) * 4 ^ w ∧ C.output < I + C.size ∧
      (∀ i q, allowWire i q < I + C.size) ∧ (∀ j, wordWire j < I + C.size) ∧
      ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        ∃ reduced : Fin n → (Fin (w + 1) → Bool) → Bool,
          (∀ i q, table i q = true → reduced i q = true) ∧
          (∀ x : Fin n → Bool, (∀ i, table i (window x i) = true) ↔
            ∀ i, reduced i (window x i) = true) ∧
          (∀ D ∈ clauses reduced, ∃ a : Fin n → Bool,
            ¬ PEqualNP.ProofComplexity.ClauseSat a D ∧
            PEqualNP.ProofComplexity.Satisfies a (clauses reduced \ {D})) ∧
          ∀ (queryRow : Fin n) (queryPat : Fin (w + 1) → Bool),
            let inputs := List.ofFn (fun addr : Fin T =>
              table ⟨(addr.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
                (fun digit => addr.val.testBit digit.val)) ++
              List.ofFn (fun rowBit : Fin n => decide (rowBit = queryRow)) ++
              List.ofFn queryPat
            let bit := fun wire : ℕ => (C.wires inputs).getD wire false
            let answer := fun index : Fin n => bit (wordWire index)
            (∀ i q, bit (allowWire i q) = reduced i q) ∧
            (C.eval inputs = true ↔ PEqualNP.ProofComplexity.Satisfiable (clauses table)) ∧
            (reduced queryRow queryPat = false → window answer queryRow = queryPat ∧
              ∀ j : Fin n, j ≠ queryRow → reduced j (window answer j) = true) := by
  intro n w hn
  exact PEqualNP.Outside.L_pcx_224_aux.finalStatement n w hn
