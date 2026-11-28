import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25894_aux

-- Circuit and arithmetic helpers adapted from f4abcb19ee3d72833a38618b9a4159c742387f5e,
-- lean/PEqualNP/Outside/L_meta_25940.lean. The scheduler contract is a definition.
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Sig (N : ℕ) := (Fin N → Bool) → Bool

def Scheduled (N : ℕ) (k : ℕ) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack N ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

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

theorem startSched (N : ℕ) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem realizeDeps {N k : ℕ} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < N + k) ∧
      ∀ x : Fin N → Bool,
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

theorem pushSched {N k : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + k := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
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
    · refine ⟨N + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

theorem finishFinBits {N k L : ℕ} {S : Set (Sig N)}
    (h : Scheduled N k S) (bits : Fin L → Sig N) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (out : Fin L → Fin (N + C.size)),
      FanInTwo C ∧ ReadsBack N C ∧ C.size = k ∧
      ∀ (p : Fin L) (x : Fin N → Bool),
        (C.wires (List.ofFn x)).getD (out p).val false = bits p x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  have hcho : ∀ p : Fin L, ∃ i : Fin (N + gs.length),
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨⟨i, by omega⟩, hv⟩
  choose out hout using hcho
  refine ⟨⟨gs, 0⟩, out, hf, hr, hgs, ?_⟩
  intro p x
  exact hout p x

def Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop :=
  (∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B)) ∧ True

theorem Build.run {N b k : ℕ} {A B S : Set (Sig N)} (H : Build A B b)
    (hs : Scheduled N k S) (ha : A ⊆ S) :
    ∃ c ≤ b, Scheduled N (k+c) (S ∪ B) := H.1 hs ha

theorem idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩, trivial⟩

theorem relaxB {N : ℕ} {A A' B B' : Set (Sig N)} {b b' : ℕ}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)
  , trivial⟩

theorem seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2
  , trivial⟩

theorem seq2B {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

theorem extB {N : ℕ} {A B : Set (Sig N)} {b : ℕ} (H : Build A B b) : Build A (A ∪ B) b :=
  relaxB H le_rfl le_rfl le_rfl

theorem transB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build B C c) : Build A C (b + c) :=
  relaxB (seqB H1 (relaxB H2 Set.subset_union_right Set.subset_union_right le_rfl))
    le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

theorem gateB {N : ℕ} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩, trivial⟩

theorem constB {N : ℕ} {A : Set (Sig N)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

theorem notB {N : ℕ} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

theorem andB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem orB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

theorem xorB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let s1 : Sig N := fun x => f x || g x
  let s2 : Sig N := fun x => f x && g x
  let s3 : Sig N := fun x => !(s2 x)
  let s4 : Sig N := fun x => s1 x && s3 x
  have h1 : Build A {s1} 1 := orB hf hg
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hf) (Or.inl hg)
  have h3 : Build (A ∪ ({s1} ∪ {s2})) {s3} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({s1} ∪ {s2}) ∪ {s3})) {s4} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have heq : s4 = fun x => xor (f x) (g x) := by
    funext x
    simp only [s4, s3, s2, s1]
    exact (xor_eq_or_and_not_and (f x) (g x)).symm
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

theorem iteB {N : ℕ} {A : Set (Sig N)} {c a b : Sig N}
    (hc : c ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Build A {fun x => if c x then a x else b x} 4 := by
  let nc : Sig N := fun x => !(c x)
  let t1 : Sig N := fun x => c x && a x
  let t2 : Sig N := fun x => nc x && b x
  let out : Sig N := fun x => t1 x || t2 x
  have h1 : Build A {nc} 1 := notB hc
  have h2 : Build (A ∪ {nc}) {t1} 1 := andB (Or.inl hc) (Or.inl ha)
  have h3 : Build (A ∪ ({nc} ∪ {t1})) {t2} 1 :=
    andB (Or.inr (Or.inl rfl)) (Or.inl hb)
  have h4 : Build (A ∪ (({nc} ∪ {t1}) ∪ {t2})) {out} 1 :=
    orB (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inr rfl))
  have heq : out = fun x => if c x then a x else b x := by
    funext x
    simp only [out, t1, t2, nc]
    cases c x <;> cases a x <;> cases b x <;> rfl
  refine relaxB (seqB (seqB (seqB h1 h2) h3) h4) le_rfl ?_ (by omega)
  intro h hm
  rw [Set.mem_singleton_iff.mp hm, ← heq]
  exact Or.inr (Or.inr rfl)

theorem listB {N : ℕ} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))
        Set.subset_union_left Set.subset_union_right le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

theorem finB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : ℕ)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  refine relaxB hl le_rfl ?_ (by simp)
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨List.mem_finRange i, hfi⟩⟩)

theorem finSigB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Sig N) (c : ℕ)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_range.mp hf with ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

theorem fin2SigB {N n1 n2 : ℕ} {A : Set (Sig N)} (F : Fin n1 → Fin n2 → Sig N) (c : ℕ)
    (h : ∀ i j, Build A {F i j} c) :
    Build A {f | ∃ i j, F i j = f} (n1 * (n2 * c)) := by
  have h1 : Build A (⋃ i : Fin n1, Set.range (F i)) (n1 * (n2 * c)) :=
    finB (fun i => Set.range (F i)) (n2 * c) (fun i => finSigB (F i) c (fun j => h i j))
  refine relaxB h1 le_rfl ?_ le_rfl
  rintro f ⟨i, j, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩)

theorem unionB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

theorem andListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using htrue)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.all (fun g => g x)})
        {fun x => (f :: xs).all (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).all (fun g => g x)) =
          (fun x => f x && xs.all (fun g => g x)) := by
        funext x; simp [List.all_cons]
      rw [heq]
      exact andB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

theorem orListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.any (fun g => g x)})
        {fun x => (f :: xs).any (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).any (fun g => g x)) =
          (fun x => f x || xs.any (fun g => g x)) := by
        funext x; simp [List.any_cons]
      rw [heq]
      exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

def xorList (bs : List Bool) : Bool :=
  bs.foldr xor false

theorem xorListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xorList (xs.map fun f => f x)} (4 * xs.length) := by
  induction xs with
  | nil =>
    exact idleB (by simpa [xorList] using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xorList (xs.map fun g => g x)})
        {fun x => xorList ((f :: xs).map fun g => g x)} 4 := by
      have heq : (fun x => xorList ((f :: xs).map fun g => g x)) =
          (fun x => xor (f x) (xorList (xs.map fun g => g x))) := by
        funext x; rfl
      rw [heq]
      exact xorB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp; omega)

theorem iterB {N : ℕ} {α : Type*} (Sigs : ((Fin N → Bool) → α) → Set (Sig N))
    (step : ℕ → α → α) (c : ℕ) (Base : Set (Sig N))
    (hstep : ∀ t (st : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st) (Sigs (fun x => step t (st x))) c) :
    ∀ T (st0 : (Fin N → Bool) → α),
      Build (Base ∪ Sigs st0)
        (Sigs (fun x => (List.range T).foldl (fun s t => step t s) (st0 x)))
        (T * c) := by
  intro T
  induction T with
  | zero =>
    intro st0
    simpa using idleB (A := Base ∪ Sigs st0) (B := Sigs st0) Set.subset_union_right
  | succ T ih =>
    intro st0
    let stT : (Fin N → Bool) → α :=
      fun x => (List.range T).foldl (fun s t => step t s) (st0 x)
    have h1 : Build (Base ∪ Sigs st0) (Sigs stT) (T * c) := ih st0
    have h2 : Build ((Base ∪ Sigs st0) ∪ Sigs stT) (Sigs (fun x => step T (stT x))) c :=
      relaxB (hstep T stT)
        (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
        Set.subset_union_right le_rfl
    have heq : (fun x => (List.range (T + 1)).foldl (fun s t => step t s) (st0 x)) =
        (fun x => step T (stT x)) := by
      funext x
      simp [List.range_succ, List.foldl_append, stT]
    rw [heq]
    exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])

def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orB ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl

def sumListVal {N : ℕ} : List ((Fin N → Bool) → ℕ) → (Fin N → Bool) → ℕ
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

theorem sumListB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (Fs : List ((Fin N → Bool) → ℕ))
    (hFs : ∀ F ∈ Fs, ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal Fs))) (Fs.length * (9 * L)) := by
  induction Fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have : bitsOf L (sumListVal ([] : List ((Fin N → Bool) → ℕ))) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons F Fs ih =>
    have h1 := ih (fun G hG => hFs G (List.mem_cons_of_mem F hG))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal Fs)))
        (Set.range (bitsOf L (fun x => F x + sumListVal Fs x))) (9 * L) :=
      sumTwoB L F (sumListVal Fs) (Or.inl hfalse)
        (fun j => Or.inl (hFs F List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    refine relaxB (seq2B h1 h2) le_rfl Set.subset_union_right ?_
    simp only [List.length_cons]
    ring_nf
    omega

theorem testBit_two_pow_sub_one_sub {L b j : ℕ} (hb : b < 2 ^ L) (hj : j < L) :
    (2 ^ L - 1 - b).testBit j = !(b.testBit j) := by
  have h1 : (2 ^ L - 1 - b) + b = 2 ^ L - 1 := by omega
  have hpow : ∀ n k, (2 ^ n - 1).testBit k = decide (k < n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [testBit_eq_decide_div_mod]
      cases k with
      | zero =>
        simp only [Nat.pow_zero, Nat.div_one, Nat.zero_lt_succ, decide_true]
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hm : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
        simp [hm]
      | succ k =>
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hdiv : (2 ^ (n + 1) - 1) / 2 ^ (k + 1) = (2 ^ n - 1) / 2 ^ k := by
          rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
          congr 1
          omega
        rw [hdiv, ← testBit_eq_decide_div_mod, ih k]
        simp
  have hcarry : ∀ k ≤ L, rippleCarry (2 ^ L - 1 - b) b k = false := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hkL : k < L := by omega
      have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b k).2
      rw [h1, hpow L k, decide_eq_true hkL, ih (by omega)] at hspec
      unfold rippleCarry
      rw [ih (by omega)]
      simp only [faSum, Bool.xor_false] at hspec
      cases hA : (2 ^ L - 1 - b).testBit k <;> cases hB : b.testBit k <;>
        simp [hA, hB, faCarry] at hspec ⊢
  have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b j).2
  rw [h1, hpow L j, decide_eq_true hj, hcarry j (by omega)] at hspec
  simp only [faSum, Bool.xor_false] at hspec
  cases hA : (2 ^ L - 1 - b).testBit j <;> cases hB : b.testBit j <;>
    simp [hA, hB] at hspec ⊢

theorem testBit_add_two_pow_of_lt {L d j : ℕ} (hj : j < L) :
    (2 ^ L + d).testBit j = d.testBit j := by
  rw [testBit_eq_decide_div_mod, testBit_eq_decide_div_mod]
  have hsplit : 2 ^ L = 2 ^ j * 2 ^ (L - j) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  have hdiv : (2 ^ L + d) / 2 ^ j = 2 ^ (L - j) + d / 2 ^ j := by
    rw [hsplit, Nat.mul_add_div (Nat.two_pow_pos j)]
  rw [hdiv]
  have heven : 2 ^ (L - j) % 2 = 0 := by
    have hpos : 1 ≤ L - j := by omega
    rw [show L - j = (L - j - 1) + 1 by omega, Nat.pow_succ]
    omega
  have hmod : (2 ^ (L - j) + d / 2 ^ j) % 2 = (d / 2 ^ j) % 2 := by omega
  rw [hmod]

theorem subTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hvalid : ∀ x, G x ≤ F x ∧ G x < 2 ^ L) :
    Build A (Set.range (bitsOf L (fun x => F x - G x))) (19 * L) := by
  let compG : (Fin N → Bool) → ℕ := fun x => 2 ^ L - 1 - G x
  let oneF : (Fin N → Bool) → ℕ := fun _ => 1
  have hcomp : Build A (Set.range (bitsOf L compG)) L := by
    have h1 := finSigB (A := A) (fun j : Fin L => fun x => !(bitsOf L G j x)) 1
      (fun j => notB (hG j))
    refine relaxB h1 le_rfl ?_ (by omega)
    rintro _ ⟨j, rfl⟩
    have heq : bitsOf L compG j = fun x => !(bitsOf L G j x) := by
      funext x
      exact testBit_two_pow_sub_one_sub (hvalid x).2 j.isLt
    rw [heq]
    exact Or.inr ⟨j, rfl⟩
  have hone : ∀ j : Fin L, bitsOf L oneF j ∈ A := by
    intro j
    by_cases hj : j.val = 0
    · have heq : bitsOf L oneF j = fun _ => true := by
        funext x; simp [bitsOf, oneF, hj]
      rw [heq]; exact htrue
    · have heq : bitsOf L oneF j = fun _ => false := by
        funext x
        simp only [bitsOf, oneF]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [heq]; exact hfalse
  have hadd1 : Build (A ∪ Set.range (bitsOf L compG))
      (Set.range (bitsOf L (fun x => compG x + oneF x))) (9 * L) :=
    sumTwoB L compG oneF (Or.inl hfalse) (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (hone j))
  have hadd2 : Build (A ∪ (Set.range (bitsOf L compG) ∪
      Set.range (bitsOf L (fun x => compG x + oneF x))))
      (Set.range (bitsOf L (fun x => F x + (compG x + oneF x)))) (9 * L) :=
    sumTwoB L F (fun x => compG x + oneF x) (Or.inl hfalse)
      (fun j => Or.inl (hF j)) (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
  have hseq := seq2B (seqB hcomp hadd1) hadd2
  refine relaxB hseq le_rfl ?_ (by omega)
  rintro _ ⟨j, rfl⟩
  have heq : bitsOf L (fun x => F x - G x) j = bitsOf L (fun x => F x + (compG x + oneF x)) j := by
    funext x
    unfold bitsOf compG oneF
    dsimp only
    have hle := (hvalid x).1
    have hlt := (hvalid x).2
    have hsum : F x + (2 ^ L - 1 - G x + 1) = 2 ^ L + (F x - G x) := by omega
    rw [hsum, testBit_add_two_pow_of_lt j.isLt]
  rw [heq]
  exact Or.inr ⟨j, rfl⟩

def firstTrue {n : ℕ} (cond : Fin n → Bool) (i : Fin n) : Bool :=
  cond i && !(List.finRange n |>.filter (fun j => decide (j.val < i.val)) |>.any cond)

theorem firstTrue_spec {n : ℕ} (cond : Fin n → Bool) (i : Fin n) :
    firstTrue cond i = true ↔ cond i = true ∧ ∀ j : Fin n, j.val < i.val → cond j = false := by
  unfold firstTrue
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by
      have := h2 j hj
      cases h : cond j <;> simp_all⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by simp [h2 j hj]⟩

theorem firstTrue_unique {n : ℕ} (cond : Fin n → Bool) {i j : Fin n}
    (hi : firstTrue cond i = true) (hj : firstTrue cond j = true) : i = j := by
  have hi' := (firstTrue_spec cond i).mp hi
  have hj' := (firstTrue_spec cond j).mp hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have := hj'.2 i hlt
    rw [hi'.1] at this
    exact Bool.noConfusion this
  · have := hi'.2 j hgt
    rw [hj'.1] at this
    exact Bool.noConfusion this

theorem exists_firstTrue_iff {n : ℕ} (cond : Fin n → Bool) :
    (∃ i : Fin n, firstTrue cond i = true) ↔ (∃ i : Fin n, cond i = true) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, ((firstTrue_spec cond i).mp hi).1⟩
  · rintro ⟨i0, hi0⟩
    classical
    have hex : ∃ k : ℕ, ∃ h : k < n, cond ⟨k, h⟩ = true := ⟨i0.val, i0.isLt, hi0⟩
    let k := Nat.find hex
    rcases Nat.find_spec hex with ⟨hk, hcond⟩
    refine ⟨⟨k, hk⟩, (firstTrue_spec cond ⟨k, hk⟩).mpr ⟨hcond, ?_⟩⟩
    intro j hj
    by_contra hne
    have hjtrue : cond j = true := by cases h : cond j <;> simp_all
    exact Nat.find_min hex hj ⟨j.isLt, hjtrue⟩

theorem firstTrueB {N n : ℕ} {A : Set (Sig N)} (cond : Fin n → Sig N)
    (hfalse : (fun _ => false) ∈ A)
    (hcond : ∀ i : Fin n, cond i ∈ A) :
    Build A (Set.range (fun i : Fin n => fun x => firstTrue (fun j => cond j x) i)) (n * (n + 2)) := by
  refine finSigB (fun i : Fin n => fun x => firstTrue (fun j => cond j x) i) (n + 2) ?_
  intro i
  let xs : List (Sig N) := (List.finRange n |>.filter (fun j => decide (j.val < i.val))).map cond
  have hxs : ∀ f ∈ xs, f ∈ A := by
    intro f hf
    rcases List.mem_map.mp hf with ⟨j, _, rfl⟩
    exact hcond j
  have h1 : Build A {fun x => xs.any (fun f => f x)} xs.length := orListB xs hxs hfalse
  have h2 : Build (A ∪ {fun x => xs.any (fun f => f x)})
      {fun x => !(xs.any (fun f => f x))} 1 := notB (Or.inr rfl)
  have h3 : Build ((A ∪ {fun x => xs.any (fun f => f x)}) ∪ {fun x => !(xs.any (fun f => f x))})
      {fun x => cond i x && !(xs.any (fun f => f x))} 1 :=
    andB (Or.inl (Or.inl (hcond i))) (Or.inr rfl)
  have hlen : xs.length ≤ n := by
    calc
      xs.length = (List.finRange n |>.filter (fun j => decide (j.val < i.val))).length :=
        List.length_map _
      _ ≤ (List.finRange n).length := List.length_filter_le _ _
      _ = n := List.length_finRange
  have heq : (fun x => cond i x && !(xs.any (fun f => f x))) =
      (fun x => firstTrue (fun j => cond j x) i) := by
    funext x
    simp [firstTrue, xs, List.any_map]
  rw [← heq]
  exact relaxB (transB (transB (extB h1) (extB h2)) h3) le_rfl Set.subset_union_right (by omega)

def z2b (x : ZMod 2) : Bool := decide (x ≠ 0)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

theorem b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by
  rcases z2_cases x with rfl | rfl <;> rfl

theorem z2b_zero : z2b 0 = false := by decide

theorem z2b_one : z2b 1 = true := by decide

theorem z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> rfl

theorem z2b_mul (x y : ZMod 2) : z2b (x * y) = (z2b x && z2b y) := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> rfl

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> rfl

theorem z2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases z2_cases x with rfl | rfl <;> rfl

theorem z2_mul_self (x : ZMod 2) : x * x = x := by
  rcases z2_cases x with rfl | rfl <;> rfl

theorem z2b_sum {α : Type*} (l : List α) (f : α → ZMod 2) :
    z2b (l.map f).sum = xorList (l.map (fun a => z2b (f a))) := by
  induction l with
  | nil => simp [xorList, z2b_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, z2b_add, ih, xorList, List.foldr_cons]

theorem z2b_fin_sum {n : ℕ} (f : Fin n → ZMod 2) :
    z2b (∑ i : Fin n, f i) = xorList ((List.finRange n).map (fun i => z2b (f i))) := by
  rw [Fin.sum_univ_def, z2b_sum]

def signInt (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem signInt_add (x y : ZMod 2) : signInt (x + y) = signInt x * signInt y := by
  fin_cases x <;> fin_cases y <;> decide

theorem quadPair_sum (A B : ZMod 2) :
    ∑ x : ZMod 2, ∑ y : ZMod 2, signInt (x * y + x * A + y * B) = 2 * signInt (A * B) := by
  fin_cases A <;> fin_cases B <;> decide

theorem isoVar_sum (l : ZMod 2) :
    ∑ x : ZMod 2, signInt (l * x) = if l = 0 then 2 else 0 := by
  fin_cases l <;> decide

theorem char_ortho_sum : ∀ (h : ℕ) (v : Fin h → ZMod 2),
    ∑ σ : Fin h → ZMod 2, signInt (∑ s : Fin h, σ s * v s) =
      if (∀ s : Fin h, v s = 0) then (2 : ℤ) ^ h else 0 := by
  intro h
  induction h with
  | zero =>
    intro v
    simp [signInt]
  | succ h ih =>
    intro v
    let e : (ZMod 2 × (Fin h → ZMod 2)) ≃ (Fin (h + 1) → ZMod 2) := Fin.consEquiv (fun _ => ZMod 2)
    rw [← Fintype.sum_equiv e (fun p => signInt (∑ s : Fin (h + 1), e p s * v s))
      (fun σ => signInt (∑ s : Fin (h + 1), σ s * v s)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (a : ZMod 2) (τ : Fin h → ZMod 2),
        signInt (∑ s : Fin (h + 1), e (a, τ) s * v s) =
          signInt (v 0 * a) * signInt (∑ s : Fin h, τ s * v s.succ) := by
      intro a τ
      rw [Fin.sum_univ_succ, ← signInt_add]
      congr 1
      simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      ring
    simp_rw [hsplit, ← Finset.mul_sum, ← Finset.sum_mul, isoVar_sum, ih (fun s => v s.succ)]
    by_cases hall : ∀ s : Fin (h + 1), v s = 0
    · have h0 : v 0 = 0 := hall 0
      have hsucc : ∀ s : Fin h, v s.succ = 0 := fun s => hall s.succ
      rw [ite_eq_left_of_eq_true _ _ (eq_true hall), ite_eq_left_of_eq_true _ _ (eq_true h0),
        ite_eq_left_of_eq_true _ _ (eq_true hsucc), pow_succ]
      ring
    · simp only [hall, ↓reduceIte]
      by_cases h0 : v 0 = 0
      · have hns : ¬ ∀ s : Fin h, v s.succ = 0 := fun hs => hall (Fin.cases h0 hs)
        simp [h0, hns]
      · simp [h0]
def maskOfNat (h n : ℕ) : Fin h → ZMod 2 :=
  fun s => b2z (n.testBit s.val)

theorem maskOfNat_bijective (h : ℕ) :
    Function.Bijective (fun s : Fin (2 ^ h) => maskOfNat h s.val) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < h
    · have h1 := congrFun hab ⟨j, hj⟩
      have h2 := congrArg z2b h1
      simpa [maskOfNat, z2b_b2z] using h2
    · have ha : a.val < 2 ^ j := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have hb : b.val < 2 ^ j := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
  · simp [Fintype.card_fin, Fintype.card_pi, ZMod.card]
theorem finishFlagBits {N k L b : ℕ} {A : Set (Sig N)} {flag : Sig N}
    {ans : Fin L → Sig N} (hs : Scheduled N k A)
    (hb : Build A ({flag} ∪ Set.range ans) b) :
    ∃ (C : Circuit) (f : Fin (N+C.size)) (out : Fin L → Fin (N+C.size)),
      FanInTwo C ∧ ReadsBack N C ∧ C.output = f.val ∧ C.size ≤ k+b ∧
      (∀ x, (C.wires (List.ofFn x)).getD f.val false = flag x) ∧
      ∀ j x, (C.wires (List.ofFn x)).getD (out j).val false = ans j x := by
  obtain ⟨c, hc, gs, hlen, hr, hf, hw⟩ := hb.run hs le_rfl
  obtain ⟨i, hi, hflag⟩ := hw flag (Or.inr (Or.inl rfl))
  have hcho : ∀ j, ∃ p : Fin (N+gs.length), ∀ x,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD p.val false = ans j x := by
    intro j
    obtain ⟨p, hp, h⟩ := hw (ans j) (Or.inr (Or.inr ⟨j,rfl⟩))
    exact ⟨⟨p, by omega⟩, h⟩
  choose out hout using hcho
  exact ⟨⟨gs,i⟩, ⟨i, by change i < N+gs.length; omega⟩, out, hf, hr, rfl,
    by change gs.length ≤ k+b; omega, hflag, hout⟩
-- Fourier factorization from f4abcb19ee3d72833a38618b9a4159c742387f5e, lean/PEqualNP/Outside/L_meta_25899.lean.
def sg (f : ZMod 2) : ℤ := if f = 0 then 1 else -1

theorem sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

theorem sg_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

theorem char_sum (k : ℕ) (a target : Fin k → ZMod 2) (test : Finset (Fin k)) :
    ∑ x : Fin k → ZMod 2, (if ∀ j ∈ test, x j = target j then sg (a ⬝ᵥ x) else 0) =
      if ∀ j, j ∉ test → a j = 0 then (2 : ℤ) ^ (k - test.card) * sg (a ⬝ᵥ target) else 0 := by
  classical
  have h1 : ∀ x : Fin k → ZMod 2, (if ∀ j ∈ test, x j = target j then sg (a ⬝ᵥ x) else 0) =
      ∏ j, (if (j ∈ test → x j = target j) then sg (a j * x j) else 0) := by
    intro x
    rw [Fintype.prod_ite_zero, dotProduct, sg_sum]
    congr
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j (y : ZMod 2) => if (j ∈ test → y = target j) then sg (a j * y) else 0)]
  by_cases h : ∀ j, j ∉ test → a j = 0
  · rw [if_pos h]
    have h2 : ∀ j, (∑ y : ZMod 2, if (j ∈ test → y = target j) then sg (a j * y) else 0) =
        (if j ∈ test then 1 else 2) * sg (a j * target j) := by
      intro j
      by_cases hj : j ∈ test
      · simp [hj]
      · simp [hj, h j hj, sg]
    simp_rw [h2]
    rw [Finset.prod_mul_distrib, dotProduct, sg_sum, Finset.prod_ite, Finset.prod_const_one,
      Finset.prod_const, one_mul]
    congr 2
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (by simp)]
    simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj, haj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have : a j = 1 := by
      revert haj; generalize a j = z; revert z; decide
    simp only [hj, this, one_mul, false_imp_iff, if_true]
    decide

theorem foldl_take_succ {α : Type*} (r : ℕ) (f : α → Fin r → α) (a : α) (t : Fin r) :
    ((List.finRange r).take (t.val + 1)).foldl f a =
      f (((List.finRange r).take t.val).foldl f a) t := by
  rw [List.take_succ]
  simp

theorem core (k r s : ℕ) (L ρ0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (ρ : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (hρ0 : ∀ a b, ρ0 (a + b) = ρ0 a + ρ0 b) (hρ : ∀ n a b, ρ n (a + b) = ρ n a + ρ n b)
    (raw : Fin k → ZMod 2) (delta : Fin s → Fin k → ZMod 2)
    (path : Fin (r + 1) → Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (target : Fin k → ZMod 2)
    (st : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2) → (Fin k → ZMod 2) → Fin (r + 1) →
      (Fin k → ZMod 2))
    (h0 : ∀ d key, st d key 0 = ρ0 key + d.1)
    (hs : ∀ d key (t : Fin r),
      st d key t.succ = L (st d key t.castSucc) + ρ t.val key + d.2 t)
    (b : Fin r → Fin k → ZMod 2) :
    ∑ c : Fin r → Fin k → ZMod 2,
      (((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun name =>
        (∀ t p, st (name, c) (raw + delta p) t - st (name, c) raw t = path t p) ∧
        (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j))).card : ℤ) *
        sg (∑ t : Fin r, b t ⬝ᵥ c t) =
    if (∀ p, path 0 p = ρ0 (delta p)) ∧
        (∀ j : Fin k, j ∉ test → (∑ t : Fin r, (if t.val + 1 = r then b t else 0)) j = 0) then
      (2 : ℤ) ^ (k - test.card) *
        sg ((∑ t : Fin r, (if t.val + 1 = r then b t else 0)) ⬝ᵥ target) *
        (∏ t : Fin r, (∑ v ∈ (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v => ∀ p : Fin s,
          L (v + path t.castSucc p) - L v + ρ t.val (delta p) = path t.succ p),
          sg ((∑ t' : Fin r, (if t'.val + 1 = t.val then b t' else 0)) ⬝ᵥ v +
            b t ⬝ᵥ (L v + ρ t.val raw))))
    else 0 := by
  classical
  have sub_add : ∀ x y : Fin k → ZMod 2, x - y = x + y := by
    intro x y; funext j; exact CharTwo.sub_eq_add _ _
  have hD : ∀ d, (∀ t p, st d (raw + delta p) t - st d raw t = path t p) ↔
      (∀ p, path 0 p = ρ0 (delta p)) ∧ ∀ t : Fin r, ∀ p,
        L (st d raw t.castSucc + path t.castSucc p) - L (st d raw t.castSucc) +
          ρ t.val (delta p) = path t.succ p := by
    intro d
    constructor
    · intro h
      refine ⟨fun p => ?_, fun t p => ?_⟩
      · have := h 0 p
        rw [h0, h0, hρ0] at this
        rw [← this]; abel
      · have h1 := h t.succ p
        have h2 := h t.castSucc p
        rw [hs, hs, hρ] at h1
        have h3 : st d (raw + delta p) t.castSucc = st d raw t.castSucc + path t.castSucc p := by
          rw [← h2]; abel
        rw [h3] at h1
        rw [← h1]; abel
    · rintro ⟨hv, hl⟩ t p
      induction t using Fin.induction with
      | zero => rw [h0, h0, hρ0, hv p]; abel
      | succ t ih =>
        have h3 : st d (raw + delta p) t.castSucc = st d raw t.castSucc + path t.castSucc p := by
          rw [← ih]; abel
        rw [hs, hs, hρ, h3, ← hl t p]; abel
  have hc : ∀ (d : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2)) (t : Fin r),
      d.2 t = st d raw t.succ - L (st d raw t.castSucc) - ρ t.val raw := by
    intro d t; rw [hs]; abel
  let e : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2) ≃ (Fin (r + 1) → Fin k → ZMod 2) :=
    { toFun := fun d t => st d raw t
      invFun := fun v => (v 0 - ρ0 raw, fun t => v t.succ - L (v t.castSucc) - ρ t.val raw)
      left_inv := by
        rintro ⟨name, c⟩
        refine Prod.ext ?_ ?_
        · show st (name, c) raw 0 - ρ0 raw = name
          rw [h0]; abel
        · funext t
          show st (name, c) raw t.succ - L (st (name, c) raw t.castSucc) - ρ t.val raw = c t
          rw [hs]; abel
      right_inv := by
        intro v
        funext t
        induction t using Fin.induction with
        | zero => show st _ raw 0 = v 0; rw [h0]; dsimp only; abel
        | succ t ih =>
          show st _ raw t.succ = v t.succ
          rw [hs]
          have ih' : st (v 0 - ρ0 raw, fun t => v t.succ - L (v t.castSucc) - ρ t.val raw) raw
              t.castSucc = v t.castSucc := ih
          rw [ih']; dsimp only; abel }
  let pv : ℕ → Fin k → ZMod 2 := fun j => ∑ t' : Fin r, if t'.val + 1 = j then b t' else 0
  have pv0 : pv 0 = 0 := by simp [pv]
  have pvs : ∀ t : Fin r, pv (t.val + 1) = b t := by
    intro t; simp [pv, Fin.val_inj]
  let Gf : (Fin (r + 1) → Fin k → ZMod 2) → ℤ := fun v =>
    if (∀ p, path 0 p = ρ0 (delta p)) ∧ (∀ t : Fin r, ∀ p,
        L (v t.castSucc + path t.castSucc p) - L (v t.castSucc) + ρ t.val (delta p) =
          path t.succ p) ∧ (∀ j ∈ test, v (Fin.last r) j = target j) then
      sg (∑ t : Fin r, b t ⬝ᵥ (v t.succ - L (v t.castSucc) - ρ t.val raw)) else 0
  have step1 : ∑ c : Fin r → Fin k → ZMod 2,
      (((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun name =>
        (∀ t p, st (name, c) (raw + delta p) t - st (name, c) raw t = path t p) ∧
        (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j))).card : ℤ) *
        sg (∑ t : Fin r, b t ⬝ᵥ c t) = ∑ v, Gf v := by
    rw [← Equiv.sum_comp e Gf]
    simp only [Finset.natCast_card_filter, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun name _ => Finset.sum_congr rfl fun c _ => ?_
    show _ = if _ ∧ (∀ t : Fin r, ∀ p,
        L (st (name, c) raw t.castSucc + path t.castSucc p) - L (st (name, c) raw t.castSucc) +
          ρ t.val (delta p) = path t.succ p) ∧ (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j) then
      sg (∑ t : Fin r, b t ⬝ᵥ (st (name, c) raw t.succ - L (st (name, c) raw t.castSucc) - ρ t.val raw)) else 0
    simp only [hD (name, c), and_assoc]
    refine if_congr Iff.rfl (congrArg sg (Finset.sum_congr rfl fun t _ => ?_)) rfl
    rw [← hc (name, c) t]
  rw [step1]
  by_cases hV : ∀ p, path 0 p = ρ0 (delta p)
  swap
  · simp [Gf, hV]
  let G : Fin (r + 1) → (Fin k → ZMod 2) → ℤ := fun u =>
    Fin.lastCases (motive := fun _ => (Fin k → ZMod 2) → ℤ)
      (fun x => if ∀ j ∈ test, x j = target j then sg (pv r ⬝ᵥ x) else 0)
      (fun t x => if (∀ p, L (x + path t.castSucc p) - L x + ρ t.val (delta p) = path t.succ p)
        then sg (pv t.val ⬝ᵥ x + b t ⬝ᵥ (L x + ρ t.val raw)) else 0) u
  have hG : ∀ v, Gf v = ∏ u, G u (v u) := by
    intro v
    rw [Fin.prod_univ_castSucc]
    simp only [G, Gf, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [Fintype.prod_ite_zero]
    by_cases hQ : ∀ t : Fin r, ∀ p, L (v t.castSucc + path t.castSucc p) - L (v t.castSucc) +
        ρ t.val (delta p) = path t.succ p
    swap
    · simp [hQ]
    by_cases hT : ∀ j ∈ test, v (Fin.last r) j = target j
    swap
    · simp [hT]
    rw [if_pos ⟨hV, hQ, hT⟩, if_pos hQ, if_pos hT]
    have hH : ∏ u : Fin (r + 1), sg (pv u.val ⬝ᵥ v u) = ∏ t : Fin r, sg (b t ⬝ᵥ v t.succ) := by
      rw [Fin.prod_univ_succ]
      simp [pv0, pvs, sg]
    have hH2 := Fin.prod_univ_castSucc (fun u : Fin (r + 1) => sg (pv u.val ⬝ᵥ v u))
    simp only [Fin.val_castSucc, Fin.val_last] at hH2
    rw [sg_sum]
    simp only [sub_add, dotProduct_add, sg_add, Finset.prod_mul_distrib]
    rw [← hH, hH2]
    ring
  simp_rw [hG]
  rw [← Fintype.prod_sum G, Fin.prod_univ_castSucc]
  simp only [G, Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [char_sum]
  simp only [Finset.sum_filter, pv]
  by_cases hC : ∀ j, j ∉ test → (∑ t : Fin r, if t.val + 1 = r then b t else 0) j = 0
  · rw [if_pos hC, if_pos ⟨hV, hC⟩]; ring
  · rw [if_neg hC, if_neg (fun h => hC h.2)]; ring

-- Polar identities from f4abcb19ee3d72833a38618b9a4159c742387f5e, lean/PEqualNP/Outside/L_meta_25888.lean.
def rotF {k : ℕ} (hk : 0 < k) (amount : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x ⟨(j.val + k - amount % k) % k, Nat.mod_lt _ hk⟩

def mixF {k : ℕ} (hk : 0 < k) (gap : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x j + x ⟨(j.val + gap) % k, Nat.mod_lt _ hk⟩ + x ⟨(j.val + k - gap % k) % k, Nat.mod_lt _ hk⟩

def layerF {k : ℕ} (hk : 0 < k) (gap : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  let m := mixF hk gap x
  m j + (1 + m ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) * m ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩

def polarF {k : ℕ} (hk : 0 < k) (gap : ℕ) (u v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  layerF hk gap (u + v) - layerF hk gap u - layerF hk gap v

lemma rotF_add {k : ℕ} (hk : 0 < k) (a : ℕ) (x y : Fin k → ZMod 2) :
    rotF hk a (x + y) = rotF hk a x + rotF hk a y := rfl

lemma rotF_zero {k : ℕ} (hk : 0 < k) (a : ℕ) :
    rotF hk a (0 : Fin k → ZMod 2) = 0 := rfl

lemma mixF_add {k : ℕ} (hk : 0 < k) (g : ℕ) (x y : Fin k → ZMod 2) :
    mixF hk g (x + y) = mixF hk g x + mixF hk g y := by
  funext j; simp only [mixF, Pi.add_apply]; ring

lemma mixF_zero {k : ℕ} (hk : 0 < k) (g : ℕ) :
    mixF hk g (0 : Fin k → ZMod 2) = 0 := by
  funext j; simp [mixF]

lemma layerF_zero {k : ℕ} (hk : 0 < k) (g : ℕ) :
    layerF hk g (0 : Fin k → ZMod 2) = 0 := by
  funext j; simp [layerF, mixF]

lemma polarF_apply {k : ℕ} (hk : 0 < k) (g : ℕ) (u v : Fin k → ZMod 2) (j : Fin k) :
    polarF hk g u v j =
      mixF hk g u ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ * mixF hk g v ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ +
      mixF hk g v ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ * mixF hk g u ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ := by
  simp only [polarF, layerF, Pi.sub_apply, mixF_add, Pi.add_apply]
  have : ∀ a1 a2 b1 b2 c1 c2 : ZMod 2,
      a1 + a2 + (1 + (b1 + b2)) * (c1 + c2) - (a1 + (1 + b1) * c1) - (a2 + (1 + b2) * c2) =
        b1 * c2 + b2 * c1 := by decide
  exact this _ _ _ _ _ _

lemma polarF_zero_left {k : ℕ} (hk : 0 < k) (g : ℕ) (v : Fin k → ZMod 2) :
    polarF hk g 0 v = 0 := by
  funext j; simp [polarF_apply, mixF_zero]

lemma polarF_add_left {k : ℕ} (hk : 0 < k) (g : ℕ) (u1 u2 v : Fin k → ZMod 2) :
    polarF hk g (u1 + u2) v = polarF hk g u1 v + polarF hk g u2 v := by
  funext j; simp only [polarF_apply, mixF_add, Pi.add_apply]; ring

lemma polarF_smul_left {k : ℕ} (hk : 0 < k) (g : ℕ) (c : ZMod 2) (u v : Fin k → ZMod 2) :
    polarF hk g (c • u) v = c • polarF hk g u v := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp [polarF_zero_left]
  · simp

def polarLin {k : ℕ} (hk : 0 < k) (g : ℕ) (d : Fin k → ZMod 2) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun := fun v => polarF hk g v d
  map_add' := fun u1 u2 => polarF_add_left hk g u1 u2 d
  map_smul' := fun c u => polarF_smul_left hk g c u d

lemma layerF_diff_eq {k : ℕ} (hk : 0 < k) (g : ℕ) (v d : Fin k → ZMod 2) :
    layerF hk g (v + d) - layerF hk g v = polarF hk g v d + layerF hk g d := by
  funext j
  simp only [polarF, Pi.sub_apply, Pi.add_apply]
  have : ∀ a b c : ZMod 2, a - b = (a - b - c) + c := by decide
  exact this _ _ _

abbrev V (k : ℕ) := Fin k → ZMod 2

lemma intMonomial_of_sq {a : ℤ} {h k : ℕ}
    (hsq : a * a = 2 ^ h) (hbound : a.natAbs ≤ 2 ^ k) :
    ∃ e ≤ k, a = (2 : ℤ)^e ∨ a = -(2 : ℤ)^e := by
  have hn : a.natAbs * a.natAbs = 2 ^ h := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hsq
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨a.natAbs, hn.symm⟩
  have hek : e ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (he ▸ hbound)
  refine ⟨e, hek, ?_⟩
  have hc : (a.natAbs : ℤ) = (2 : ℤ)^e := by exact_mod_cast he
  rw [Int.natCast_natAbs] at hc
  by_cases h : 0 ≤ a
  · exact Or.inl ((abs_of_nonneg h).symm.trans hc)
  · rw [abs_of_neg (by omega)] at hc
    exact Or.inr (by omega)

def toFLinear {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module (ZMod 2) A]
    [Module (ZMod 2) B] (f : A → B) (h : ∀ a b, f (a+b) = f a+f b) : A →ₗ[ZMod 2] B where
  toFun := f
  map_add' := h
  map_smul' c a := by
    have h0 : f 0 = 0 := by
      have he : f 0 + 0 = f 0 + f 0 := by simpa using h 0 0
      exact (add_left_cancel he).symm
    rcases z2_cases c with rfl | rfl <;> simp [h0]

lemma linearChar {G : Type*} [Fintype G] [AddCommGroup G] [Module (ZMod 2) G]
    (f : G →ₗ[ZMod 2] ZMod 2) :
    ∑ x : G, sg (f x) = if f = 0 then (Fintype.card G : ℤ) else 0 := by
  classical
  split_ifs with hf
  · simp [hf, sg]
  · have hw : ∃ w : G, f w ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (LinearMap.ext (fun w => by simpa using h w))
    obtain ⟨w, hw⟩ := hw
    have hadd := Equiv.sum_comp (Equiv.addRight w) (fun x => sg (f x))
    change ∑ x : G, sg (f (x+w)) = ∑ x : G, sg (f x) at hadd
    have hs : sg (f w) = -1 := by simp [sg, hw]
    simp_rw [map_add, sg_add, hs, mul_neg_one] at hadd
    rw [Finset.sum_neg_distrib] at hadd
    omega

lemma finiteCardF2 (G : Type*) [Fintype G] [AddCommGroup G] [Module (ZMod 2) G] :
    Fintype.card G = 2 ^ Module.finrank (ZMod 2) G := by
  let b := Module.finBasis (ZMod 2) G
  rw [Fintype.card_congr b.equivFun.toEquiv]
  simp [Fintype.card_pi, ZMod.card]

lemma quadCharSq {G : Type*} [Fintype G] [AddCommGroup G] [Module (ZMod 2) G]
    (Q : G → ZMod 2) (B : G →ₗ[ZMod 2] G →ₗ[ZMod 2] ZMod 2)
    (hQ : ∀ x y, Q (x+y) + Q x + Q y + Q 0 = B x y) :
    let a := ∑ x : G, sg (Q x)
    a = 0 ∨ ∃ e : ℕ, a*a = (2 : ℤ)^e := by
  classical
  intro a
  let R := B.ker
  letI : Fintype R := Fintype.ofFinite _
  let f : R →ₗ[ZMod 2] ZMod 2 := toFLinear (fun x => Q (x : G) + Q 0) (by
    intro x y
    have hx : B (x : G) = 0 := x.2
    have h := hQ (x : G) (y : G)
    rw [hx, LinearMap.zero_apply] at h
    change Q ((x : G)+(y : G)) + Q 0 = (Q (x : G) + Q 0) + (Q (y : G) + Q 0)
    have hc := z2_add_self (Q (x : G) + Q (y : G) + Q 0)
    linear_combination h - hc)
  have hexpand : a*a = (Fintype.card G : ℤ) * ∑ x : R, sg (f x) := by
    dsimp only [a]
    have he : (∑ x : G, sg (Q x)) * (∑ y : G, sg (Q y)) =
        ∑ x : G, ∑ y : G, sg (Q x) * sg (Q y) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => Finset.mul_sum ..)
    rw [he]
    have hh (y : G) : (∑ x : G, sg (Q (y+x)) * sg (Q x)) =
        (Fintype.card G : ℤ) * (if B y = 0 then sg (Q y + Q 0) else 0) := by
      have he (x : G) : Q (y+x) + Q x = B y x + (Q y + Q 0) := by
        have h := hQ y x
        have h₂ := z2_add_self (Q y + Q 0)
        linear_combination h - h₂
      simp_rw [← sg_add, he, sg_add, ← Finset.sum_mul, linearChar]
      split_ifs <;> simp
    calc
      _ = ∑ x : G, ∑ y : G, sg (Q (y+x)) * sg (Q x) := by
        apply Finset.sum_congr rfl
        intro x _
        have H := (Equiv.sum_comp (Equiv.addRight x) (fun y => sg (Q y) * sg (Q x))).symm
        change (∑ y, sg (Q y) * sg (Q x)) = ∑ y, sg (Q (y+x)) * sg (Q x) at H
        simpa only [mul_comm (sg (Q x))] using H
      _ = ∑ y : G, ∑ x : G, sg (Q (y+x)) * sg (Q x) := Finset.sum_comm
      _ = (Fintype.card G : ℤ) * ∑ x : R, sg (f x) := by
        simp_rw [hh]
        rw [← Finset.mul_sum, ← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
        have hu : (Finset.univ : Finset G).subtype (fun x => B x = 0) =
            (Finset.univ : Finset R) := by
          ext x
          simp only [Finset.mem_subtype, Finset.mem_univ, true_iff]
          exact @Finset.mem_univ R _ x
        rw [hu]
        rfl
  rw [linearChar] at hexpand
  split_ifs at hexpand with hh
  · right
    refine ⟨Module.finrank (ZMod 2) G + Module.finrank (ZMod 2) R, ?_⟩
    rw [hexpand, finiteCardF2 G, finiteCardF2 R, pow_add]
    norm_cast
  · left
    rw [mul_zero, mul_eq_zero, or_self] at hexpand
    exact hexpand

lemma affineQuadChar {T : Type*} [AddCommGroup T] [Module (ZMod 2) T] [DecidableEq T] (k : ℕ)
    (L : V k →ₗ[ZMod 2] T) (rhs : T) (Q : V k → ZMod 2)
    (B : V k →ₗ[ZMod 2] V k →ₗ[ZMod 2] ZMod 2)
    (hQ : ∀ a x y, Q (a+x+y) + Q (a+x) + Q (a+y) + Q a = B x y) :
    let s := ∑ x : V k, if L x = rhs then sg (Q x) else 0
    s = 0 ∨ ∃ e ≤ k, s = (2 : ℤ)^e ∨ s = -(2 : ℤ)^e := by
  classical
  intro S
  by_cases h : ∃ y, L y = rhs
  · obtain ⟨y, hy⟩ := h
    let e : L.ker ≃ {x : V k // L x = rhs} :=
      { toFun := fun x => ⟨y + x, by rw [map_add, hy, LinearMap.mem_ker.mp x.2, add_zero]⟩
        invFun := fun x => ⟨x - y, by rw [LinearMap.mem_ker, map_sub, x.2, hy, sub_self]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    letI : Fintype L.ker := Fintype.ofFinite _
    letI : Fintype {x : V k // L x = rhs} := Fintype.ofFinite _
    let q : L.ker → ZMod 2 := fun x => Q (y+x)
    let b : L.ker →ₗ[ZMod 2] L.ker →ₗ[ZMod 2] ZMod 2 :=
      toFLinear (fun u => (B (u : V k)).comp L.ker.subtype) (by
        intro u v
        ext w
        change B ((u : V k)+(v : V k)) (w : V k) = B (u : V k) (w : V k) + B (v : V k) (w : V k)
        simp)
    have hs : S = ∑ x : L.ker, sg (q x) := by
      dsimp only [S]
      rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
      have hu : (Finset.univ : Finset (V k)).subtype (fun a => L a = rhs) =
          (Finset.univ : Finset {a : V k // L a = rhs}) := by
        ext a
        simp only [Finset.mem_subtype, Finset.mem_univ, true_iff]
      rw [hu]
      exact (Equiv.sum_comp e (fun x => sg (Q x))).symm
    have hq (u v : L.ker) : q (u+v) + q u + q v + q 0 = b u v := by
      simpa [q, b, toFLinear, add_assoc] using hQ y (u : V k) (v : V k)
    have habs : S.natAbs ≤ 2 ^ k := by
      have hb : (S.natAbs : ℤ) ≤ (2 : ℤ)^k := by
        rw [Int.natCast_natAbs]
        calc
          |S| ≤ ∑ x : V k, |if L x = rhs then sg (Q x) else 0| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _x : V k, (1 : ℤ) := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hx : L x = rhs <;> by_cases hqx : Q x = 0 <;> simp [hx, sg, hqx]
          _ = (2 : ℤ)^k := by simp [V, Fintype.card_pi, ZMod.card]
      exact_mod_cast hb
    rcases quadCharSq q b hq with hzero | ⟨j, hj⟩
    · exact Or.inl (hs.trans hzero)
    · exact Or.inr (intMonomial_of_sq (by simpa only [← hs] using hj) habs)
  · left
    push_neg at h
    simp [S, h]

def roundPhase {k : ℕ} (hk : 0 < k) (g : ℕ) (prev now u v : V k) : ZMod 2 :=
  dotProduct prev v + dotProduct now (layerF hk g v + u)

def roundAgree {k s : ℕ} (hk : 0 < k) (g : ℕ) (off p₀ p₁ : Fin s → V k) (v : V k) : Prop :=
  ∀ p, layerF hk g (v + p₀ p) - layerF hk g v + off p = p₁ p

lemma polarF_comm {k : ℕ} (hk : 0 < k) (g : ℕ) (x y : V k) :
    polarF hk g x y = polarF hk g y x := by
  funext j
  simp only [polarF_apply]
  ring

def phaseB {k : ℕ} (hk : 0 < k) (g : ℕ) (now : V k) : V k →ₗ[ZMod 2] V k →ₗ[ZMod 2] ZMod 2 :=
  toFLinear (fun x => toFLinear (fun y => dotProduct now (polarF hk g x y)) (by
    intro y₁ y₂
    rw [polarF_comm hk g x, polarF_add_left, dotProduct_add, polarF_comm hk g y₁, polarF_comm hk g y₂])) (by
    intro x₁ x₂
    apply LinearMap.ext
    intro y
    change dotProduct now (polarF hk g (x₁+x₂) y) =
      dotProduct now (polarF hk g x₁ y) + dotProduct now (polarF hk g x₂ y)
    rw [polarF_add_left, dotProduct_add])

lemma layerF_second {k : ℕ} (hk : 0 < k) (g : ℕ) (a x y : V k) :
    layerF hk g (a+x+y) + layerF hk g (a+x) + layerF hk g (a+y) + layerF hk g a =
      polarF hk g x y := by
  funext j
  have ha := congrFun (layerF_diff_eq hk g (a+x) y) j
  have hb := congrFun (layerF_diff_eq hk g a y) j
  simp only [polarF_add_left, Pi.add_apply, Pi.sub_apply] at ha hb ⊢
  have hc := z2_add_self (layerF hk g (a+x) j + layerF hk g (a+y) j)
  linear_combination ha - hb + hc

lemma phase_second {k : ℕ} (hk : 0 < k) (g : ℕ) (prev now u a x y : V k) :
    roundPhase hk g prev now u (a+x+y) + roundPhase hk g prev now u (a+x) +
        roundPhase hk g prev now u (a+y) + roundPhase hk g prev now u a = phaseB hk g now x y := by
  have hh := congrArg (dotProduct now) (layerF_second hk g a x y)
  change _ = dotProduct now (polarF hk g x y)
  simp only [roundPhase, dotProduct_add] at hh ⊢
  have hc := z2_add_self (dotProduct prev a + dotProduct prev a + dotProduct prev x +
    dotProduct prev y + dotProduct now u + dotProduct now u)
  linear_combination hh + hc

noncomputable def roundSum {k s : ℕ} (hk : 0 < k) (g : ℕ) (off p₀ p₁ : Fin s → V k)
    (prev now u : V k) : ℤ := by
  classical
  exact ∑ v : V k, if roundAgree hk g off p₀ p₁ v then sg (roundPhase hk g prev now u v) else 0

lemma roundSum_monomial {k s : ℕ} (hk : 0 < k) (g : ℕ) (off p₀ p₁ : Fin s → V k)
    (prev now u : V k) :
    roundSum hk g off p₀ p₁ prev now u = 0 ∨
    ∃ e ≤ k, roundSum hk g off p₀ p₁ prev now u = (2 : ℤ)^e ∨
      roundSum hk g off p₀ p₁ prev now u = -(2 : ℤ)^e := by
  classical
  let L : V k →ₗ[ZMod 2] (Fin s → V k) := LinearMap.pi (fun p => polarLin hk g (p₀ p))
  let rhs : Fin s → V k := fun p => p₁ p - off p - layerF hk g (p₀ p)
  have he (v : V k) : roundAgree hk g off p₀ p₁ v ↔ L v = rhs := by
    simp only [roundAgree, layerF_diff_eq, funext_iff, L, rhs,
      LinearMap.pi_apply, polarLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply]
    constructor <;> intro h p j <;> specialize h p j
    · rw [← h]; abel
    · rw [h]; abel
  unfold roundSum
  simp_rw [he]
  exact affineQuadChar k L rhs _ _ (phase_second hk g prev now u)

abbrev Inp (N : ℕ) := Fin N → Bool
abbrev FieldSig (N : ℕ) := Inp N → ZMod 2
abbrev bSig {N : ℕ} (f : FieldSig N) : Sig N := fun x => z2b (f x)
abbrev OneMade {N : ℕ} (A : Set (Sig N)) (f : FieldSig N) (b : ℕ) := Build A {bSig f} b

lemma oneMem {N : ℕ} {A : Set (Sig N)} {f : FieldSig N} (hf : bSig f ∈ A) : OneMade A f 0 :=
  idleB (by simpa using hf)

lemma oneConst {N : ℕ} {A : Set (Sig N)} (hfalse : (fun _ => false) ∈ A)
    (htrue : (fun _ => true) ∈ A) (c : ZMod 2) : OneMade A (fun _ => c) 0 := by
  rcases z2_cases c with rfl | rfl
  · refine oneMem (f := fun _ => 0) ?_
    change (fun _ => z2b 0) ∈ A
    simpa only [z2b_zero] using hfalse
  · refine oneMem (f := fun _ => 1) ?_
    change (fun _ => z2b 1) ∈ A
    simpa only [z2b_one] using htrue

lemma oneAdd {N : ℕ} {A : Set (Sig N)} {f g : FieldSig N} {a b : ℕ}
    (hf : OneMade A f a) (hg : OneMade A g b) : OneMade A (fun x => f x + g x) (a+b+4) := by
  refine seq2B (unionB hf hg) ?_
  have he : bSig (fun x => f x + g x) = fun x => xor (bSig f x) (bSig g x) :=
    funext (fun x => z2b_add (f x) (g x))
  rw [he]
  exact xorB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))

lemma oneMul {N : ℕ} {A : Set (Sig N)} {f g : FieldSig N} {a b : ℕ}
    (hf : OneMade A f a) (hg : OneMade A g b) : OneMade A (fun x => f x * g x) (a+b+1) := by
  refine seq2B (unionB hf hg) ?_
  have he : bSig (fun x => f x * g x) = fun x => bSig f x && bSig g x :=
    funext (fun x => z2b_mul (f x) (g x))
  rw [he]
  exact andB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))

lemma oneZero {N : ℕ} {A : Set (Sig N)} {f : FieldSig N} {a : ℕ}
    (hf : OneMade A f a) : Build A {fun x => !z2b (f x)} (a+1) :=
  seq2B hf (notB (Or.inr rfl))

lemma allFinB {N n : ℕ} {A : Set (Sig N)} (v : Fin n → Sig N)
    (ht : (fun _ => true) ∈ A) (hv : ∀ i, v i ∈ A) :
    Build A {fun x => (List.finRange n).all (fun i => v i x)} n := by
  simpa only [List.length_map, List.length_finRange, List.all_map, Function.comp_def] using
    andListB ((List.finRange n).map v) (by
      intro f hf
      rcases List.mem_map.mp hf with ⟨i, -, rfl⟩
      exact hv i) ht

lemma listSumFieldB {N n : ℕ} {A : Set (Sig N)} (v : Fin n → FieldSig N)
    (hf : (fun _ => false) ∈ A) (hv : ∀ i, bSig (v i) ∈ A) :
    OneMade A (fun x => ∑ i : Fin n, v i x) (4*n) := by
  have he : bSig (fun x => ∑ i : Fin n, v i x) =
      fun x => xorList ((List.finRange n).map (fun i => bSig (v i) x)) :=
    funext (fun x => z2b_fin_sum (fun i => v i x))
  change Build A {bSig (fun x => ∑ i : Fin n, v i x)} (4*n)
  rw [he]
  simpa only [List.length_map, List.length_finRange, List.map_map, Function.comp_def] using
    xorListB ((List.finRange n).map (fun i => bSig (v i))) (by
      intro f hf
      rcases List.mem_map.mp hf with ⟨i, -, rfl⟩
      exact hv i) hf

lemma finTypeBuild {T : Type*} [Fintype T] {N : ℕ} {A : Set (Sig N)}
    (S : T → Set (Sig N)) (c : ℕ) (h : ∀ i, Build A (S i) c) :
    Build A (⋃ i, S i) (Fintype.card T * c) := by
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine relaxB (finB (fun i => S (e i)) c (fun i => h (e i))) le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hi⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩)

def ixW {k : ℕ} (hk : 0 < k) (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

def winF {k : ℕ} (hk : 0 < k) (v : V k) (j : Fin k) : V 7 :=
  fun i => v (ixW hk (j.val+i.val))

lemma ixW_plus {k : ℕ} (hk : 0 < k) (x a : ℕ) :
    ixW hk ((ixW hk x).val+a) = ixW hk (x+a) := by
  apply Fin.ext
  exact ((Nat.mod_modEq x k).add Nat.ModEq.rfl)

lemma ixW_minus {k : ℕ} (hk : 0 < k) (x a b : ℕ) (hab : b ≤ a) :
    ixW hk ((ixW hk (x+a)).val+k-b%k) = ixW hk (x+(a-b)) := by
  apply Fin.ext
  change ((x+a)%k+k-b%k) ≡ x+(a-b) [MOD k]
  apply Nat.ModEq.add_right_cancel' (b%k)
  rw [Nat.sub_add_cancel (by have := Nat.mod_lt b hk; omega)]
  have h₁ : (x+a)%k+k ≡ x+a [MOD k] := by
    change (((x+a)%k)+k)%k = (x+a)%k
    simp
  have h₂ : (x+(a-b))+b%k ≡ (x+(a-b))+b [MOD k] :=
    Nat.ModEq.rfl.add (Nat.mod_modEq b k)
  rw [show (x+(a-b))+b = x+a by omega] at h₂
  exact h₁.trans h₂.symm

noncomputable def winShift {k : ℕ} (hk : 0 < k) (d : ℕ) : Fin k ≃ Fin k :=
  Equiv.ofBijective (fun j => ixW hk (j.val+d)) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro x y h
    have h' : x.val+d ≡ y.val+d [MOD k] := congrArg Fin.val h
    have hxy := Nat.ModEq.add_right_cancel' d h'
    apply Fin.ext
    simpa [Nat.ModEq, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hxy)

def winMid (j : Fin 3) : Fin 7 := ⟨j.val+2, by omega⟩

def winPlus (g : ℕ) (hg : g ≤ 2) (j : Fin 3) : Fin 7 := ⟨j.val+2+g, by omega⟩

def winMinus (g : ℕ) (hg : g ≤ 2) (j : Fin 3) : Fin 7 := ⟨j.val+2-g, by omega⟩

def winMix (g : ℕ) (hg : g ≤ 2) (v : V 7) (j : Fin 3) : ZMod 2 :=
  v (winMid j) + v (winPlus g hg j) + v (winMinus g hg j)

def winLayer (g : ℕ) (hg : g ≤ 2) (v : V 7) : ZMod 2 :=
  winMix g hg v 0 + (1 + winMix g hg v 1) * winMix g hg v 2

lemma winMix_apply {k : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2) (v : V k)
    (j : Fin k) (a : Fin 3) :
    winMix g hg (winF hk v j) a = mixF hk g v (ixW hk (j.val+(a.val+2))) := by
  unfold winMix winF mixF winMid winPlus winMinus
  change v (ixW hk (j.val+(a.val+2))) + v (ixW hk (j.val+(a.val+2+g))) +
      v (ixW hk (j.val+(a.val+2-g))) =
    v (ixW hk (j.val+(a.val+2))) + v (ixW hk ((ixW hk (j.val+(a.val+2))).val+g)) +
      v (ixW hk ((ixW hk (j.val+(a.val+2))).val+k-g%k))
  rw [ixW_plus, ixW_minus hk _ _ _ (by omega)]
  simp only [Nat.add_assoc]

lemma winLayer_apply {k : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2) (v : V k) (j : Fin k) :
    winLayer g hg (winF hk v j) = layerF hk g v (winShift hk 2 j) := by
  unfold winLayer
  simp only [winMix_apply]
  change mixF hk g v (ixW hk (j.val+2)) + (1+mixF hk g v (ixW hk (j.val+3))) *
    mixF hk g v (ixW hk (j.val+4)) = layerF hk g v (ixW hk (j.val+2))
  unfold layerF
  change _ = mixF hk g v (ixW hk (j.val+2)) +
    (1+mixF hk g v (ixW hk ((ixW hk (j.val+2)).val+1))) *
      mixF hk g v (ixW hk ((ixW hk (j.val+2)).val+2))
  rw [ixW_plus, ixW_plus]

lemma winLayerB {N : ℕ} {A : Set (Sig N)} (g : ℕ) (hg : g ≤ 2) (v : Inp N → V 7)
    (ht : (fun _ => true) ∈ A) (hf : (fun _ => false) ∈ A)
    (b : ℕ) (hv : ∀ j, OneMade A (fun x => v x j) b) :
    OneMade A (fun x => winLayer g hg (v x)) (9*b+33) := by
  have hm (j : Fin 3) : OneMade A (fun x => winMix g hg (v x) j) (b+b+4+b+4) :=
    oneAdd (oneAdd (hv (winMid j)) (hv (winPlus g hg j))) (hv (winMinus g hg j))
  have hh := oneAdd (hm 0) (oneMul (oneAdd (oneConst hf ht 1) (hm 1)) (hm 2))
  apply relaxB hh le_rfl
  · exact Set.subset_union_right
  · omega

-- This segment follows Base in namespace PEqualNP.Outside.L_meta_25894_aux.

open scoped BigOperators

abbrev CycleState := Fin 6 → Bool
-- Terminal six-bit state, current six-bit state, and accumulated sign.
abbrev CycleTable := CycleState → CycleState → Bool → ℕ

private theorem cycleSumBool (f : Bool → ℕ) : (∑ b, f b) = f false + f true := by
  have h : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  simp [h]

private def cycleLine {t : ℕ} (s : CycleState) (u : Fin t → Bool) (n : ℕ) : Bool :=
  if hn : n < t then u ⟨n, hn⟩ else if hm : n - t < 6 then s ⟨n - t, hm⟩ else false

private theorem cycleLine_cons_zero {t : ℕ} (s : CycleState) (u : Fin t → Bool) (b : Bool) :
    cycleLine s (Fin.cons b u) 0 = b := by
  simp [cycleLine]

private theorem cycleLine_cons_succ {t : ℕ} (s : CycleState) (u : Fin t → Bool) (b : Bool)
    (n : ℕ) : cycleLine s (Fin.cons b u) (n + 1) = cycleLine s u n := by
  unfold cycleLine
  by_cases hn : n < t
  · rw [dite_eq_left hn, dite_eq_left (by omega : n + 1 < t + 1)]
    exact Fin.cons_succ (α := fun _ => Bool) b u ⟨n, hn⟩
  · rw [dite_eq_right hn, dite_eq_right (by omega : ¬ n + 1 < t + 1)]
    simp only [Nat.add_sub_add_right]

private def cycleHead {t : ℕ} (s : CycleState) (u : Fin t → Bool) : CycleState :=
  fun i => cycleLine s u i.val

private def cycleLinearWindow {t : ℕ} (s : CycleState) (u : Fin t → Bool) (j : ℕ) : Fin 7 → Bool :=
  fun i => cycleLine s u (j + i.val)

private def cycleNext (a : CycleState) (b : Bool) : CycleState :=
  Fin.snoc (Fin.tail a) b

private theorem cycleHead_cons {t : ℕ} (s a : CycleState) (u : Fin t → Bool) (d : Bool) :
    cycleHead s (Fin.cons d u) = a ↔
      d = a 0 ∧ cycleHead s u = cycleNext a (cycleLine s u 5) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [cycleHead, Fin.val_zero, cycleLine_cons_zero] using congrFun h 0
    · funext i
      refine Fin.lastCases ?_ (fun m => ?_) i
      · change cycleLine s u 5 =
          Fin.snoc (α := fun _ => Bool) (Fin.tail a) (cycleLine s u 5) (Fin.last 5)
        rw [Fin.snoc_last]
      · have hm := congrFun h m.succ
        simpa only [cycleHead, cycleNext, Fin.snoc_castSucc, Fin.tail, Fin.val_castSucc,
          Fin.val_succ, cycleLine_cons_succ] using hm
  · rintro ⟨hd, he⟩
    funext i
    refine Fin.cases ?_ (fun m => ?_) i
    · simpa only [cycleHead, Fin.val_zero, cycleLine_cons_zero] using hd
    · have hm := congrFun he m.castSucc
      simpa only [cycleHead, cycleNext, Fin.snoc_castSucc, Fin.tail, Fin.val_castSucc,
        Fin.val_succ, cycleLine_cons_succ] using hm

private theorem cycleLinearWindow_cons_zero {t : ℕ} (s a : CycleState) (u : Fin t → Bool)
    (d : Bool) (h : cycleHead s (Fin.cons d u) = a) :
    cycleLinearWindow s (Fin.cons d u) 0 = Fin.snoc a (cycleLine s u 5) := by
  funext i
  refine Fin.lastCases ?_ (fun m => ?_) i
  · rw [Fin.snoc_last]
    exact cycleLine_cons_succ s u d 5
  · simpa only [cycleLinearWindow, Nat.zero_add, Fin.snoc_castSucc, Fin.val_castSucc,
      cycleHead] using congrFun h m

private theorem cycleLinearWindow_cons_succ {t : ℕ} (s : CycleState) (u : Fin t → Bool)
    (d : Bool) (j : ℕ) :
    cycleLinearWindow s (Fin.cons d u) (j + 1) = cycleLinearWindow s u j := by
  funext i
  have h : j + 1 + i.val = j + i.val + 1 := by omega
  simp only [cycleLinearWindow, h, cycleLine_cons_succ]

private def cyclePathGood {t : ℕ} (ok : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s : CycleState) (u : Fin t → Bool) : Prop :=
  ∀ i : Fin t, ok (j + i.val) (cycleLinearWindow s u i.val) = true

private def cyclePathNeg {t : ℕ} (neg : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s : CycleState) (u : Fin t → Bool) : Bool :=
  xorList (List.ofFn fun i : Fin t => neg (j + i.val) (cycleLinearWindow s u i.val))

private theorem cyclePathGood_cons {t : ℕ} (ok : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s : CycleState) (u : Fin t → Bool) (d : Bool) :
    cyclePathGood ok j s (Fin.cons d u) ↔
      ok j (cycleLinearWindow s (Fin.cons d u) 0) = true ∧ cyclePathGood ok (j + 1) s u := by
  unfold cyclePathGood
  rw [Fin.forall_fin_succ]
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, cycleLinearWindow_cons_succ]
  have h (i : Fin t) : j + (i.val + 1) = j + 1 + i.val := by omega
  simp only [h]

private theorem cyclePathNeg_cons {t : ℕ} (neg : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s : CycleState) (u : Fin t → Bool) (d : Bool) :
    cyclePathNeg neg j s (Fin.cons d u) =
      xor (neg j (cycleLinearWindow s (Fin.cons d u) 0)) (cyclePathNeg neg (j + 1) s u) := by
  unfold cyclePathNeg
  rw [List.ofFn_succ]
  have h (i : Fin t) : j + (i.val + 1) = j + 1 + i.val := by omega
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, cycleLinearWindow_cons_succ, h]
  rfl

private theorem cycleXor_match (c q p : Bool) : xor c q = p ↔ q = (if c then !p else p) := by
  cases c <;> cases q <;> cases p <;> decide

private noncomputable def cyclePathTerm {t : ℕ} (ok neg : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s a : CycleState) (p : Bool) (u : Fin t → Bool) : ℕ := by
  classical
  exact if cycleHead s u = a ∧ cyclePathGood ok j s u ∧ cyclePathNeg neg j s u = p
    then 1 else 0

-- A path of t steps is its first t bits followed by the fixed terminal state s.
private noncomputable def cyclePaths (ok neg : ℕ → (Fin 7 → Bool) → Bool)
    (j t : ℕ) : CycleTable := fun s a p => ∑ u : Fin t → Bool, cyclePathTerm ok neg j s a p u

private noncomputable def cycleInit : CycleTable := by
  classical
  exact fun s a p => if s = a ∧ p = false then 1 else 0

private def cycleLane (ok neg : (Fin 7 → Bool) → Bool) (st : CycleTable)
    (s a : CycleState) (p b : Bool) : ℕ :=
  if ok (Fin.snoc a b) then st s (cycleNext a b) (if neg (Fin.snoc a b) then !p else p) else 0

private def cycleStep (ok neg : (Fin 7 → Bool) → Bool) (st : CycleTable) : CycleTable :=
  fun s a p => cycleLane ok neg st s a p false + cycleLane ok neg st s a p true

private theorem cyclePaths_zero (ok neg : ℕ → (Fin 7 → Bool) → Bool) (j : ℕ) :
    cyclePaths ok neg j 0 = cycleInit := by
  classical
  funext s a p
  unfold cyclePaths
  have hu : (Finset.univ : Finset (Fin 0 → Bool)) = {fun _ => false} := by
    ext u
    have hu : u = fun _ => false := by funext i; exact Fin.elim0 i
    exact ⟨fun _ => Finset.mem_singleton.mpr hu, fun _ => Finset.mem_univ _⟩
  rw [hu, Finset.sum_singleton]
  have hh : cycleHead s (fun (_ : Fin 0) => false) = s := by
    funext i; simp [cycleHead, cycleLine, i.isLt]
  cases p <;> simp [cyclePathTerm, hh, cyclePathGood, cyclePathNeg, xorList, cycleInit]

private theorem cyclePathTerm_cons {t : ℕ} (ok neg : ℕ → (Fin 7 → Bool) → Bool)
    (j : ℕ) (s a : CycleState) (p d : Bool) (u : Fin t → Bool) :
    cyclePathTerm ok neg j s a p (Fin.cons d u) =
      if d = a 0 then
        let b := cycleLine s u 5
        if ok j (Fin.snoc a b) then
          cyclePathTerm ok neg (j + 1) s (cycleNext a b)
            (if neg j (Fin.snoc a b) then !p else p) u
        else 0
      else 0 := by
  classical
  by_cases hd : d = a 0
  · subst d
    by_cases ht : cycleHead s u = cycleNext a (cycleLine s u 5)
    · have hc := (cycleHead_cons s a u (a 0)).2 ⟨rfl, ht⟩
      rw [ite_eq_left rfl]
      simp only [cyclePathTerm, ht, hc, true_and, cyclePathGood_cons,
        cyclePathNeg_cons, cycleLinearWindow_cons_zero s a u (a 0) hc, cycleXor_match]
      by_cases h : ok j (Fin.snoc a (cycleLine s u 5)) = true <;> simp [h]
    · have hc : cycleHead s (Fin.cons (a 0) u) ≠ a :=
        fun h => ht ((cycleHead_cons s a u (a 0)).1 h).2
      rw [ite_eq_left rfl]
      simp [cyclePathTerm, ht, hc]
  · have hc : cycleHead s (Fin.cons d u) ≠ a := fun h => hd ((cycleHead_cons s a u d).1 h).1
    simp [cyclePathTerm, hd, hc]

private theorem cyclePaths_succ (ok neg : ℕ → (Fin 7 → Bool) → Bool) (j t : ℕ) :
    cyclePaths ok neg j (t + 1) = cycleStep (ok j) (neg j) (cyclePaths ok neg (j + 1) t) := by
  classical
  funext s a p
  let G (u : Fin t → Bool) (b : Bool) : ℕ :=
    if ok j (Fin.snoc a b) then
      cyclePathTerm ok neg (j + 1) s (cycleNext a b) (if neg j (Fin.snoc a b) then !p else p) u
    else 0
  have hzero (u : Fin t → Bool) (b : Bool) (h : b ≠ cycleLine s u 5) : G u b = 0 := by
    have hh : cycleHead s u ≠ cycleNext a b := by
      intro he
      have hh := congrFun he (Fin.last 5)
      change cycleLine s u 5 = Fin.snoc (α := fun _ => Bool) (Fin.tail a) b (Fin.last 5) at hh
      rw [Fin.snoc_last] at hh
      exact h hh.symm
    simp [G, cyclePathTerm, hh]
  calc
    cyclePaths ok neg j (t + 1) s a p =
        ∑ q : Bool × (Fin t → Bool), cyclePathTerm ok neg j s a p (Fin.cons q.1 q.2) := by
      exact (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (t + 1) => Bool) _ _ (fun _ => rfl)).symm
    _ = ∑ u : Fin t → Bool, ∑ d : Bool, cyclePathTerm ok neg j s a p (Fin.cons d u) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ u : Fin t → Bool, ∑ b : Bool, G u b := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [cycleSumBool, cyclePathTerm_cons]
      change ((if false = a 0 then G u (cycleLine s u 5) else 0) +
        (if true = a 0 then G u (cycleLine s u 5) else 0)) = G u false + G u true
      have hleft : (if false = a 0 then G u (cycleLine s u 5) else 0) +
          (if true = a 0 then G u (cycleLine s u 5) else 0) = G u (cycleLine s u 5) := by
        cases a 0 <;> simp
      rw [hleft]
      cases h : cycleLine s u 5 with
      | false => rw [hzero u true (by simp [h]), Nat.add_zero]
      | true => rw [hzero u false (by simp [h]), Nat.zero_add]
    _ = ∑ b : Bool, ∑ u : Fin t → Bool, G u b := Finset.sum_comm
    _ = cycleStep (ok j) (neg j) (cyclePaths ok neg (j + 1) t) s a p := by
      have hc (b : Bool) : (∑ u : Fin t → Bool, G u b) =
          cycleLane (ok j) (neg j) (cyclePaths ok neg (j + 1) t) s a p b := by
        by_cases h : ok j (Fin.snoc a b) = true <;> simp [G, cycleLane, cyclePaths, h]
      rw [cycleSumBool, hc, hc, cycleStep]

-- Work backwards from the final position. Every current state has two successors.
private noncomputable def cycleRun (k : ℕ) (ok neg : ℕ → (Fin 7 → Bool) → Bool) :
    ℕ → CycleTable
  | 0 => cycleInit
  | t + 1 => cycleStep (ok (k - (t + 1))) (neg (k - (t + 1))) (cycleRun k ok neg t)

private theorem cycleRun_spec (k : ℕ) (ok neg : ℕ → (Fin 7 → Bool) → Bool) :
    ∀ t ≤ k, cycleRun k ok neg t = cyclePaths ok neg (k - t) t := by
  intro t
  induction t with
  | zero => intro _; exact (cyclePaths_zero ok neg _).symm
  | succ t ih =>
    intro ht
    rw [cycleRun, ih (by omega), cyclePaths_succ]
    rw [show k - (t + 1) + 1 = k - t by omega]

def cycleWindow {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) (j : Fin k) : Fin 7 → Bool :=
  fun i => u ⟨(j.val + i.val) % k, Nat.mod_lt _ hk⟩

noncomputable def cycleCount {k : ℕ} (hk : 0 < k)
    (ok neg : Fin k → (Fin 7 → Bool) → Bool) (p : Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun u : Fin k → Bool =>
    (∀ j, ok j (cycleWindow hk u j) = true) ∧
      xorList ((List.finRange k).map fun j => neg j (cycleWindow hk u j)) = p).card

private def cycleEnd {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) : CycleState :=
  fun i => u ⟨i.val % k, Nat.mod_lt _ hk⟩

private theorem cycleLine_closed {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) (s : CycleState)
    (hs : cycleHead s u = s) (n : ℕ) (hn : n < k + 6) :
    cycleLine s u n = u ⟨n % k, Nat.mod_lt _ hk⟩ := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hnk : n < k
    · simp [cycleLine, hnk, Nat.mod_eq_of_lt hnk]
    · have hi : n - k < 6 := by omega
      have he := congrFun hs (⟨n - k, hi⟩ : Fin 6)
      change cycleLine s u (n - k) = s ⟨n - k, hi⟩ at he
      rw [cycleLine, dite_eq_right hnk, dite_eq_left hi, ← he, ih (n - k) (by omega) (by omega)]
      congr 1
      exact Fin.ext (Nat.mod_eq_sub_mod (by omega : k ≤ n)).symm

private theorem cycleLine_end {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) (n : ℕ)
    (hn : n < k + 6) : cycleLine (cycleEnd hk u) u n = u ⟨n % k, Nat.mod_lt _ hk⟩ := by
  by_cases hnk : n < k
  · simp [cycleLine, hnk, Nat.mod_eq_of_lt hnk]
  · have hi : n - k < 6 := by omega
    rw [cycleLine, dite_eq_right hnk, dite_eq_left hi]
    exact congrArg u (Fin.ext (Nat.mod_eq_sub_mod (by omega : k ≤ n)).symm)

private theorem cycleHead_closed_iff {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) (s : CycleState) :
    cycleHead s u = s ↔ s = cycleEnd hk u := by
  constructor
  · intro hs
    funext i
    rw [← congrFun hs i]
    exact cycleLine_closed hk u s hs i.val (by have := i.isLt; omega)
  · rintro rfl
    funext i
    exact cycleLine_end hk u i.val (by have := i.isLt; omega)

private def cycleExtend {k : ℕ} (hk : 0 < k) {α : Type*} (f : Fin k → α) (j : ℕ) : α :=
  f ⟨j % k, Nat.mod_lt _ hk⟩

private theorem cycleLinearWindow_closed {k : ℕ} (hk : 0 < k) (u : Fin k → Bool) (s : CycleState)
    (hs : cycleHead s u = s) (j : Fin k) :
    cycleLinearWindow s u j.val = cycleWindow hk u j := by
  funext i
  exact cycleLine_closed hk u s hs (j.val + i.val) (by have := j.isLt; have := i.isLt; omega)

private theorem cyclePathTerm_closed {k : ℕ} (hk : 0 < k)
    (ok neg : Fin k → (Fin 7 → Bool) → Bool) (u : Fin k → Bool) (s : CycleState) (p : Bool) :
    cyclePathTerm (cycleExtend hk ok) (cycleExtend hk neg) 0 s s p u =
      if s = cycleEnd hk u then
        if (∀ j, ok j (cycleWindow hk u j) = true) ∧
            xorList ((List.finRange k).map fun j => neg j (cycleWindow hk u j)) = p
        then 1 else 0
      else 0 := by
  classical
  by_cases h : s = cycleEnd hk u
  · have hs := (cycleHead_closed_iff hk u s).2 h
    have he (j : Fin k) : (⟨j.val % k, Nat.mod_lt _ hk⟩ : Fin k) = j :=
      Fin.ext (Nat.mod_eq_of_lt j.isLt)
    rw [ite_eq_left h]
    simp only [cyclePathTerm, hs, true_and, cyclePathGood, cyclePathNeg,
      Nat.zero_add, cycleExtend, he, cycleLinearWindow_closed hk u s hs, List.ofFn_eq_map]
  · have hs : cycleHead s u ≠ s := fun he => h ((cycleHead_closed_iff hk u s).1 he)
    simp [cyclePathTerm, hs, h]

-- Closing a path fixes its terminal state uniquely, even if a window wraps repeatedly.
private theorem cycleTrace_spec {k : ℕ} (hk : 0 < k)
    (ok neg : Fin k → (Fin 7 → Bool) → Bool) (p : Bool) :
    (∑ s : CycleState, cycleRun k (cycleExtend hk ok) (cycleExtend hk neg) k s s p) =
      cycleCount hk ok neg p := by
  classical
  rw [cycleRun_spec k _ _ k le_rfl, Nat.sub_self]
  unfold cyclePaths
  rw [Finset.sum_comm]
  let P (u : Fin k → Bool) : Prop :=
    (∀ j, ok j (cycleWindow hk u j) = true) ∧
      xorList ((List.finRange k).map fun j => neg j (cycleWindow hk u j)) = p
  change _ = (Finset.univ.filter P).card
  have hcard : (∑ u, if P u then 1 else 0 : ℕ) = (Finset.univ.filter P).card := by
    simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) P Finset.univ)
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro u _
  simp only [cyclePathTerm_closed]
  rw [Finset.sum_eq_single (cycleEnd hk u)]
  · simp [P]
  · intro s _ hs
    simp [hs]
  · simp

private noncomputable def cycleEnum : Fin 64 ≃ CycleState :=
  (Fintype.equivFinOfCardEq (α := CycleState) (n := 64) (by
    simp [CycleState])).symm

private def cycleSigs {N : ℕ} (L : ℕ) (st : (Fin N → Bool) → CycleTable) : Set (Sig N) :=
  {f | ∃ (s a : CycleState) (p : Bool) (i : Fin L), bitsOf L (fun x => st x s a p) i = f}

private theorem cycleInitB {N : ℕ} (L : ℕ) {A : Set (Sig N)}
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A (cycleSigs L (fun _ => cycleInit)) 0 := by
  classical
  apply idleB
  rintro _ ⟨s, a, p, i, rfl⟩
  have he : bitsOf L (fun _ : Fin N → Bool => cycleInit s a p) i =
      (fun _ => (cycleInit s a p).testBit i.val) := rfl
  rw [he]
  cases (cycleInit s a p).testBit i.val
  · exact hfalse
  · exact htrue

private theorem cycleMuxB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (c : Sig N) (F G : (Fin N → Bool) → ℕ) (hc : c ∈ A)
    (hF : ∀ i, bitsOf L F i ∈ A) (hG : ∀ i, bitsOf L G i ∈ A) :
    Build A (Set.range (bitsOf L (fun x => if c x then F x else G x))) (L * 4) := by
  apply finSigB
  intro i
  have he : bitsOf L (fun x => if c x then F x else G x) i =
      (fun x => if c x then bitsOf L F i x else bitsOf L G i x) := by
    funext x
    by_cases h : c x = true <;> simp [bitsOf, h]
  rw [he]
  exact iteB hc (hF i) (hG i)

private theorem cycleMaskB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (c : Sig N) (F : (Fin N → Bool) → ℕ) (hc : c ∈ A)
    (hF : ∀ i, bitsOf L F i ∈ A) :
    Build A (Set.range (bitsOf L (fun x => if c x then F x else 0))) (L * 1) := by
  apply finSigB
  intro i
  have he : bitsOf L (fun x => if c x then F x else 0) i =
      (fun x => c x && bitsOf L F i x) := by
    funext x
    cases h : c x <;> simp [bitsOf, h]
  rw [he]
  exact andB hc (hF i)

private theorem cycleLaneB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (ok neg : (Fin 7 → Bool) → Sig N) (st : (Fin N → Bool) → CycleTable)
    (hok : ∀ w, ok w ∈ A) (hneg : ∀ w, neg w ∈ A)
    (s a : CycleState) (p b : Bool) :
    Build (A ∪ cycleSigs L st)
      (Set.range (bitsOf L (fun x => cycleLane (fun w => ok w x) (fun w => neg w x) (st x) s a p b)))
      (5 * L) := by
  let F : (Fin N → Bool) → ℕ := fun x =>
    if neg (Fin.snoc a b) x then st x s (cycleNext a b) (!p) else st x s (cycleNext a b) p
  have hF : Build (A ∪ cycleSigs L st) (Set.range (bitsOf L F)) (L * 4) :=
    cycleMuxB L _ _ _ (Or.inl (hneg _))
      (fun i => Or.inr ⟨s, cycleNext a b, !p, i, rfl⟩)
      (fun i => Or.inr ⟨s, cycleNext a b, p, i, rfl⟩)
  have hmask := cycleMaskB (A := (A ∪ cycleSigs L st) ∪ Set.range (bitsOf L F))
    L (ok (Fin.snoc a b)) F (Or.inl (Or.inl (hok _))) (fun i => Or.inr ⟨i, rfl⟩)
  have he : (fun x => cycleLane (fun w => ok w x) (fun w => neg w x) (st x) s a p b) =
      (fun x => if ok (Fin.snoc a b) x then F x else 0) := by
    funext x
    by_cases h : ok (Fin.snoc a b) x = true <;>
      by_cases hn : neg (Fin.snoc a b) x = true <;> simp [cycleLane, F, h, hn]
  rw [he]
  exact relaxB (seq2B hF hmask) le_rfl Set.subset_union_right (by omega)

private theorem cycleEntryB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (ok neg : (Fin 7 → Bool) → Sig N) (st : (Fin N → Bool) → CycleTable)
    (hfalse : (fun _ => false) ∈ A) (hok : ∀ w, ok w ∈ A) (hneg : ∀ w, neg w ∈ A)
    (s a : CycleState) (p : Bool) :
    Build (A ∪ cycleSigs L st)
      (Set.range (bitsOf L (fun x => cycleStep (fun w => ok w x) (fun w => neg w x) (st x) s a p)))
      (19 * L) := by
  let F (b : Bool) (x : Fin N → Bool) : ℕ :=
    cycleLane (fun w => ok w x) (fun w => neg w x) (st x) s a p b
  have hl : Build (A ∪ cycleSigs L st)
      (Set.range (bitsOf L (F false)) ∪ Set.range (bitsOf L (F true))) (5 * L + 5 * L) :=
    unionB (cycleLaneB L ok neg st hok hneg s a p false) (cycleLaneB L ok neg st hok hneg s a p true)
  have hs := sumTwoB
    (A := (A ∪ cycleSigs L st) ∪ (Set.range (bitsOf L (F false)) ∪ Set.range (bitsOf L (F true))))
    L (F false) (F true) (Or.inl (Or.inl hfalse))
    (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
  exact relaxB (seq2B hl hs) le_rfl Set.subset_union_right (by omega)

private theorem cycleStepB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (ok neg : (Fin 7 → Bool) → Sig N) (st : (Fin N → Bool) → CycleTable)
    (hfalse : (fun _ => false) ∈ A) (hok : ∀ w, ok w ∈ A) (hneg : ∀ w, neg w ∈ A) :
    Build (A ∪ cycleSigs L st)
      (cycleSigs L (fun x => cycleStep (fun w => ok w x) (fun w => neg w x) (st x)))
      (155648 * L) := by
  let O (s a : CycleState) (p : Bool) :=
    Set.range (bitsOf L (fun x => cycleStep (fun w => ok w x) (fun w => neg w x) (st x) s a p))
  let P (i j : Fin 64) := O (cycleEnum i) (cycleEnum j) false ∪ O (cycleEnum i) (cycleEnum j) true
  have hp (i j : Fin 64) : Build (A ∪ cycleSigs L st) (P i j) (38 * L) := by
    exact relaxB (unionB (cycleEntryB L ok neg st hfalse hok hneg (cycleEnum i) (cycleEnum j) false)
      (cycleEntryB L ok neg st hfalse hok hneg (cycleEnum i) (cycleEnum j) true))
      le_rfl Set.subset_union_right (by omega)
  have hall := finB (fun i : Fin 64 => ⋃ j : Fin 64, P i j) (64 * (38 * L))
    (fun i => finB (P i) (38 * L) (hp i))
  refine relaxB hall le_rfl ?_ (by omega)
  rintro _ ⟨s, a, p, b, rfl⟩
  refine Or.inr (Set.mem_iUnion.mpr ⟨cycleEnum.symm s, Set.mem_iUnion.mpr ⟨cycleEnum.symm a, ?_⟩⟩)
  change _ ∈ O (cycleEnum (cycleEnum.symm s)) (cycleEnum (cycleEnum.symm a)) false ∪
    O (cycleEnum (cycleEnum.symm s)) (cycleEnum (cycleEnum.symm a)) true
  simp only [Equiv.apply_symm_apply]
  cases p
  · exact Or.inl ⟨b, rfl⟩
  · exact Or.inr ⟨b, rfl⟩

private theorem cycleRunB {N k : ℕ} {A : Set (Sig N)} (L : ℕ)
    (ok neg : ℕ → (Fin 7 → Bool) → Sig N)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hok : ∀ j w, ok j w ∈ A) (hneg : ∀ j w, neg j w ∈ A) :
    ∀ t, Build A (cycleSigs L
      (fun x => cycleRun k (fun j w => ok j w x) (fun j w => neg j w x) t)) (t * (155648 * L)) := by
  intro t
  induction t with
  | zero => simpa only [Nat.zero_mul, cycleRun] using cycleInitB L hfalse htrue
  | succ t ih =>
    let st (x : Fin N → Bool) := cycleRun k (fun j w => ok j w x) (fun j w => neg j w x) t
    have hstep := cycleStepB L (ok (k - (t + 1))) (neg (k - (t + 1))) st hfalse
      (hok _) (hneg _)
    simp only [cycleRun]
    exact relaxB (seq2B ih hstep) le_rfl Set.subset_union_right (by rw [Nat.succ_mul t])

private theorem cycleSumList_ofFn {N : ℕ} :
    ∀ {n : ℕ} (F : Fin n → (Fin N → Bool) → ℕ) (x : Fin N → Bool),
      sumListVal (List.ofFn F) x = ∑ i : Fin n, F i x := by
  intro n
  induction n with
  | zero => intro F x; simp [sumListVal]
  | succ n ih =>
    intro F x
    rw [List.ofFn_succ, sumListVal, Fin.sum_univ_succ]
    exact congrArg (F 0 x + ·) (ih (fun i => F i.succ) x)

set_option maxHeartbeats 1500000 in
private theorem cycleTraceB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (st : (Fin N → Bool) → CycleTable) (hfalse : (fun _ => false) ∈ A) (p : Bool) :
    Build (A ∪ cycleSigs L st) (Set.range (bitsOf L (fun x => ∑ s : CycleState, st x s s p)))
      (64 * (9 * L)) := by
  let F (i : Fin 64) (x : Fin N → Bool) := st x (cycleEnum i) (cycleEnum i) p
  have hF (G : (Fin N → Bool) → ℕ) (hG : G ∈ List.ofFn F) (i : Fin L) :
      bitsOf L G i ∈ A ∪ cycleSigs L st := by
    rcases List.mem_ofFn.mp hG with ⟨j, rfl⟩
    exact Or.inr ⟨cycleEnum j, cycleEnum j, p, i, rfl⟩
  have h := sumListB L (Or.inl hfalse : (fun _ => false) ∈ A ∪ cycleSigs L st) (List.ofFn F) hF
  have he : sumListVal (List.ofFn F) = (fun x => ∑ s : CycleState, st x s s p) := by
    funext x
    exact (cycleSumList_ofFn (n := 64) F x).trans
      (Fintype.sum_equiv cycleEnum (fun i => F i x) (fun s => st x s s p) (fun _ => rfl))
  simpa only [he, List.length_ofFn] using h

/-- Both parity classes of valid cyclic words, including lengths below the window width. -/
theorem cycleCountB {N k : ℕ} {A : Set (Sig N)} (hk : 0 < k)
    (ok neg : Fin k → (Fin 7 → Bool) → Sig N)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hok : ∀ z w, ok z w ∈ A) (hneg : ∀ z w, neg z w ∈ A) :
    Build A {f | ∃ (p : Bool) (i : Fin (k + 1)),
      bitsOf (k + 1) (fun x => cycleCount hk (fun z w => ok z w x) (fun z w => neg z w x) p) i = f}
      (160000 * (k + 1)^2) := by
  classical
  let L := k + 1
  let st (x : Fin N → Bool) :=
    cycleRun k (cycleExtend hk (fun z w => ok z w x)) (cycleExtend hk (fun z w => neg z w x)) k
  have hr : Build A (cycleSigs L st) (k * (155648 * L)) :=
    cycleRunB (k := k) L (cycleExtend hk ok) (cycleExtend hk neg) hfalse htrue
      (fun j w => hok _ w) (fun j w => hneg _ w) k
  let ans (p : Bool) (x : Fin N → Bool) :=
    cycleCount hk (fun z w => ok z w x) (fun z w => neg z w x) p
  have hs (p : Bool) : Build (A ∪ cycleSigs L st) (Set.range (bitsOf L (ans p))) (64 * (9 * L)) := by
    have he : (fun x => ∑ s : CycleState, st x s s p) = ans p := by
      funext x
      exact cycleTrace_spec hk (fun z w => ok z w x) (fun z w => neg z w x) p
    simpa only [he] using cycleTraceB L st hfalse p
  refine relaxB (seq2B hr (unionB (hs false) (hs true))) le_rfl ?_ ?_
  · rintro _ ⟨p, i, rfl⟩
    cases p
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · dsimp only [L]
    calc
      k * (155648 * (k + 1)) + (64 * (9 * (k + 1)) + 64 * (9 * (k + 1))) =
          (155648 * k + 1152) * (k + 1) := by ring
      _ ≤ (160000 * (k + 1)) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring

lemma negZ2_true (f : ZMod 2) : (!z2b f) = true ↔ f = 0 := by simp [z2b]

noncomputable def gateOff {N k s : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (off p₀ p₁ : Inp N → Fin s → V k) (j : Fin k) (wire : Fin 7 → Bool) (p : Fin s) : FieldSig N :=
  fun x => winLayer g hg (fun i => b2z (wire i) + winF hk (p₀ x p) j i) +
    winLayer g hg (fun i => b2z (wire i)) + off x p (winShift hk 2 j) + p₁ x p (winShift hk 2 j)

noncomputable def gateOkay {N k s : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (off p₀ p₁ : Inp N → Fin s → V k) (j : Fin k) (wire : Fin 7 → Bool) : Sig N :=
  fun x => (List.finRange s).all (fun p => !z2b (gateOff hk g hg off p₀ p₁ j wire p x))

noncomputable def gatePhase {N k : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (prev now u : Inp N → V k) (j : Fin k) (wire : Fin 7 → Bool) : FieldSig N :=
  fun x => prev x (winShift hk 2 j) * b2z (wire 2) + now x (winShift hk 2 j) *
    (winLayer g hg (fun i => b2z (wire i)) + u x (winShift hk 2 j))

def gateTerminalOK {N k : ℕ} (test target : Inp N → V k) (j : Fin k) (wire : Fin 7 → Bool) : Sig N :=
  fun x => !z2b (test x j) || !z2b (b2z (wire 0) + target x j)

def gateTerminalPhase {N k : ℕ} (last : Inp N → V k) (j : Fin k) (wire : Fin 7 → Bool) : FieldSig N :=
  fun x => last x j * b2z (wire 0)

def factorSigs {N k : ℕ} (ok : Fin k → (Fin 7 → Bool) → Sig N)
    (phase : Fin k → (Fin 7 → Bool) → FieldSig N) : Set (Sig N) :=
  {f | ∃ j w, f ∈ ({ok j w, bSig (phase j w)} : Set (Sig N))}

lemma factorSigsB {N k : ℕ} {A : Set (Sig N)} (ok : Fin k → (Fin 7 → Bool) → Sig N)
    (phase : Fin k → (Fin 7 → Bool) → FieldSig N) (a b : ℕ)
    (hok : ∀ j w, Build A {ok j w} a) (hphase : ∀ j w, OneMade A (phase j w) b) :
    Build A (factorSigs ok phase) (128*k*(a+b)) := by
  have H := finB (fun j => ⋃ w : Fin 7 → Bool, ({ok j w, bSig (phase j w)} : Set (Sig N)))
    (128*(a+b)) (fun j => by
      have HJ := finTypeBuild (fun w : Fin 7 → Bool => ({ok j w, bSig (phase j w)} : Set (Sig N)))
        (a+b) (fun w => by simpa only [Set.singleton_union] using unionB (hok j w) (hphase j w))
      simpa [Fintype.card_pi] using HJ)
  refine relaxB H le_rfl ?_ (by ring_nf; omega)
  rintro _ ⟨j,w,hw⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨w,hw⟩⟩)

lemma gateRoundB {N k s : ℕ} {A : Set (Sig N)} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (off p₀ p₁ : Inp N → Fin s → V k) (prev now u : Inp N → V k)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (ho : ∀ p j, bSig (fun x => off x p j) ∈ A) (h₀ : ∀ p j, bSig (fun x => p₀ x p j) ∈ A)
    (h₁ : ∀ p j, bSig (fun x => p₁ x p j) ∈ A)
    (hp : ∀ j, bSig (fun x => prev x j) ∈ A) (hn : ∀ j, bSig (fun x => now x j) ∈ A)
    (hu : ∀ j, bSig (fun x => u x j) ∈ A) :
    Build A (factorSigs (gateOkay hk g hg off p₀ p₁) (gatePhase hk g hg prev now u))
      (16384*k*(s+1)) := by
  have hok (j : Fin k) (w : Fin 7 → Bool) :
      Build A {gateOkay hk g hg off p₀ p₁ j w} (83*s) := by
    let cf : Fin s → Sig N := fun p x => !z2b (gateOff hk g hg off p₀ p₁ j w p x)
    have hc (p : Fin s) : Build A {cf p} 82 := by
      have ha : OneMade A (fun x => winLayer g hg (fun i => b2z (w i) + winF hk (p₀ x p) j i)) (9*4+33) :=
        winLayerB g hg _ htrue hfalse 4 (fun i => oneAdd (oneConst hfalse htrue _) (oneMem (h₀ p _)))
      have hb := oneConst hfalse htrue (winLayer g hg (fun i => b2z (w i)))
      change Build A {fun x => !z2b (gateOff hk g hg off p₀ p₁ j w p x)} 82
      exact oneZero (oneAdd (oneAdd (oneAdd ha hb) (oneMem (ho p _))) (oneMem (h₁ p _)))
    have hd := finSigB cf 82 hc
    have he : Build (A ∪ Set.range cf) {gateOkay hk g hg off p₀ p₁ j w} s :=
      allFinB cf (Or.inl htrue) (fun p => Or.inr ⟨p,rfl⟩)
    exact relaxB (seq2B hd he) le_rfl Set.subset_union_right (by omega)
  have hphase (j : Fin k) (w : Fin 7 → Bool) :
      OneMade A (gatePhase hk g hg prev now u j w) 10 :=
    oneAdd (oneMul (oneMem (hp _)) (oneConst hfalse htrue _))
      (oneMul (oneMem (hn _)) (oneAdd (oneConst hfalse htrue _) (oneMem (hu _))))
  refine relaxB (factorSigsB _ _ _ _ hok hphase) le_rfl Set.subset_union_right ?_
  have hk₀ := Nat.zero_le k
  nlinarith

lemma gateTerminalB {N k : ℕ} {A : Set (Sig N)} (test target last : Inp N → V k)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (htest : ∀ j, bSig (fun x => test x j) ∈ A) (htar : ∀ j, bSig (fun x => target x j) ∈ A)
    (hlast : ∀ j, bSig (fun x => last x j) ∈ A) :
    Build A (factorSigs (gateTerminalOK test target) (gateTerminalPhase last)) (16384*k) := by
  have hok (j : Fin k) (w : Fin 7 → Bool) : Build A {gateTerminalOK test target j w} 7 := by
    have h₁ := notB (htest j)
    have h₂ := oneZero (oneAdd (oneConst hfalse htrue (b2z (w 0))) (oneMem (htar j)))
    have h₃ := orB (A := A ∪ ({fun x => !z2b (test x j)} ∪ {fun x => !z2b (b2z (w 0)+target x j)}))
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    exact seq2B (unionB h₁ h₂) h₃
  have hphase (j : Fin k) (w : Fin 7 → Bool) : OneMade A (gateTerminalPhase last j w) 1 :=
    oneMul (oneMem (hlast j)) (oneConst hfalse htrue _)
  refine relaxB (factorSigsB _ _ _ _ hok hphase) le_rfl Set.subset_union_right ?_
  omega

lemma cycleCount_le {k : ℕ} (hk : 0 < k) (ok neg : Fin k → (Fin 7 → Bool) → Bool) (p : Bool) :
    cycleCount hk ok neg p ≤ 2^k := by
  classical
  unfold cycleCount
  simpa [Fintype.card_pi] using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k → Bool)))
    (p := fun u => (∀ j, ok j (cycleWindow hk u j) = true) ∧
      xorList ((List.finRange k).map fun j => neg j (cycleWindow hk u j)) = p))

noncomputable def factorCounts {N k : ℕ} (hk : 0 < k) (ok : Fin k → (Fin 7 → Bool) → Sig N)
    (phase : Fin k → (Fin 7 → Bool) → FieldSig N) : Bool → Inp N → ℕ :=
  fun p x => cycleCount hk (fun j w => ok j w x) (fun j w => z2b (phase j w x)) p

lemma factorCountsB {N k : ℕ} {A : Set (Sig N)} (hk : 0 < k)
    (ok : Fin k → (Fin 7 → Bool) → Sig N) (phase : Fin k → (Fin 7 → Bool) → FieldSig N)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build (A ∪ factorSigs ok phase)
      {f | ∃ (p : Bool) (i : Fin (k+1)), bitsOf (k+1) (factorCounts hk ok phase p) i = f}
      (160000*(k+1)^2) :=
  cycleCountB hk ok (fun j w => bSig (phase j w)) (Or.inl hfalse) (Or.inl htrue)
    (fun j w => Or.inr ⟨j,w,Or.inl rfl⟩) (fun j w => Or.inr ⟨j,w,Or.inr rfl⟩)

lemma factorCounts_spec {N k : ℕ} (hk : 0 < k) (ok : Fin k → (Fin 7 → Bool) → Sig N)
    (phase : Fin k → (Fin 7 → Bool) → FieldSig N) (x : Inp N) (P : V k → Prop) [DecidablePred P] (Q : V k → ZMod 2)
    (hP : ∀ v : Fin k → Bool, P (fun i => b2z (v i)) ↔ ∀ j, ok j (cycleWindow hk v j) x = true)
    (hQ : ∀ v : Fin k → Bool, Q (fun i => b2z (v i)) = ∑ j, phase j (cycleWindow hk v j) x) :
    (factorCounts hk ok phase false x : ℤ) - factorCounts hk ok phase true x =
      ∑ v : V k, (if P v then sg (Q v) else 0) := by
  classical
  let e : (Fin k → Bool) ≃ V k :=
    { toFun := fun v i => b2z (v i)
      invFun := fun v i => z2b (v i)
      left_inv := fun v => funext fun i => z2b_b2z (v i)
      right_inv := fun v => funext fun i => b2z_z2b (v i) }
  rw [← Equiv.sum_comp e]
  simp only [factorCounts, cycleCount, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  change _ = if P (fun i => b2z (v i)) then sg (Q (fun i => b2z (v i))) else 0
  rw [hQ, ← z2b_fin_sum]
  by_cases hp : ∀ j, ok j (cycleWindow hk v j) x = true
  · have hp' := (hP v).mpr hp
    rcases z2_cases (∑ j, phase j (cycleWindow hk v j) x) with h | h
    <;> simp [hp, hp', h, sg, z2b_zero, z2b_one]
  · have hp' : ¬ P (fun i => b2z (v i)) := fun h => hp ((hP v).mp h)
    simp [hp, hp']

lemma winF_b2z {k : ℕ} (hk : 0 < k) (v : Fin k → Bool) (j : Fin k) :
    winF hk (fun i => b2z (v i)) j = fun i => b2z (cycleWindow hk v j i) := rfl

lemma gateOff_spec {N k s : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (off p₀ p₁ : Inp N → Fin s → V k) (x : Inp N) (v : Fin k → Bool) (j : Fin k) (p : Fin s) :
    let F : V k := fun i => b2z (v i)
    gateOff hk g hg off p₀ p₁ j (cycleWindow hk v j) p x =
      layerF hk g (F+p₀ x p) (winShift hk 2 j) + layerF hk g F (winShift hk 2 j) +
      off x p (winShift hk 2 j) + p₁ x p (winShift hk 2 j) := by
  intro F
  change winLayer g hg (winF hk (F+p₀ x p) j) + winLayer g hg (winF hk F j) + _ + _ = _
  rw [winLayer_apply, winLayer_apply]

lemma roundCounts_spec {N k s : ℕ} (hk : 0 < k) (g : ℕ) (hg : g ≤ 2)
    (off p₀ p₁ : Inp N → Fin s → V k) (prev now u : Inp N → V k) (x : Inp N) :
    let F := factorCounts hk (gateOkay hk g hg off p₀ p₁) (gatePhase hk g hg prev now u)
    (F false x : ℤ) - F true x = roundSum hk g (off x) (p₀ x) (p₁ x) (prev x) (now x) (u x) := by
  classical
  intro F
  unfold roundSum
  apply factorCounts_spec
  · intro v
    have h (j : Fin k) (p : Fin s) :
        gateOff hk g hg off p₀ p₁ j (cycleWindow hk v j) p x = 0 ↔
        (layerF hk g ((fun i => b2z (v i))+p₀ x p) - layerF hk g (fun i => b2z (v i)) + off x p)
          (winShift hk 2 j) = p₁ x p (winShift hk 2 j) := by
      rw [gateOff_spec]
      simp only [Pi.add_apply, Pi.sub_apply, CharTwo.sub_eq_add, CharTwo.add_eq_zero]
    simp only [gateOkay, List.all_eq_true, List.mem_finRange, true_implies, negZ2_true, h, roundAgree]
    constructor
    · intro H j p
      exact congrFun (H p) _
    · intro H p
      funext j
      obtain ⟨j', rfl⟩ := (winShift hk 2).surjective j
      exact H j' p
  · intro v
    unfold roundPhase dotProduct
    rw [← Finset.sum_add_distrib]
    refine (Equiv.sum_comp (winShift hk 2) _).symm.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    unfold gatePhase
    rw [← winF_b2z hk v j, winLayer_apply]
    rfl

noncomputable def termSigned {k : ℕ} (test target last : V k) : ℤ := by
  classical
  exact ∑ v : V k, if ∀ j, test j ≠ 0 → v j = target j then sg (dotProduct last v) else 0

lemma terminalCounts_spec {N k : ℕ} (hk : 0 < k) (test target last : Inp N → V k) (x : Inp N) :
    let F := factorCounts hk (gateTerminalOK test target) (gateTerminalPhase last)
    (F false x : ℤ) - F true x = termSigned (test x) (target x) (last x) := by
  classical
  intro F
  unfold termSigned
  apply factorCounts_spec
  · intro v
    have hw (j : Fin k) : cycleWindow hk v j 0 = v j := by
      unfold cycleWindow
      congr 1
      exact Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt])
    simp only [gateTerminalOK, hw, Bool.or_eq_true, negZ2_true, CharTwo.add_eq_zero]
    constructor
    · intro h j
      by_cases hj : test x j = 0
      · exact Or.inl hj
      · exact Or.inr (h j hj)
    · intro h j hj
      exact (h j).resolve_left hj
  · intro v
    unfold dotProduct gateTerminalPhase
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2
    exact Fin.ext (by simp [cycleWindow, Nat.mod_eq_of_lt j.isLt])

lemma terminal_monomial {k : ℕ} (test target last : V k) :
    termSigned test target last = 0 ∨
      ∃ e ≤ k, termSigned test target last = (2 : ℤ)^e ∨ termSigned test target last = -(2 : ℤ)^e := by
  classical
  let T := Finset.univ.filter (fun j => test j ≠ 0)
  have h := char_sum k last target T
  have h' : termSigned test target last =
      if ∀ j, j ∉ T → last j = 0 then (2 : ℤ)^(k-T.card) * sg (dotProduct last target) else 0 := by
    simpa [termSigned, T] using h
  rw [h']
  split_ifs with hp
  · right
    refine ⟨k-T.card, Nat.sub_le .., ?_⟩
    unfold sg
    split_ifs <;> simp
  · exact Or.inl rfl

abbrev SeqV (r k : ℕ) := Fin r → V k

def flattenV (r k : ℕ) : SeqV r k ≃ₗ[ZMod 2] V (r*k) where
  toFun := fun f i => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun := fun f i j => f (finProdFinEquiv (i,j))
  left_inv := by intro f; funext i j; simp
  right_inv := by
    intro f
    funext i
    change f (finProdFinEquiv (finProdFinEquiv.symm i)) = f i
    rw [Equiv.apply_symm_apply]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma flatten_dot {r k : ℕ} (a b : SeqV r k) :
    dotProduct (flattenV r k a) (flattenV r k b) = ∑ t, dotProduct (a t) (b t) := by
  unfold dotProduct
  let q (ij : Fin r × Fin k) := a ij.1 ij.2 * b ij.1 ij.2
  exact (Fintype.sum_equiv finProdFinEquiv.symm _ q (fun _ => rfl)).trans (Fintype.sum_prod_type q)

lemma flatten_rank {r k q : ℕ} (o : Fin q → SeqV r k) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun i => flattenV r k (o i)))) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range o)) := by
  let e := flattenV r k
  have he : Set.range (fun i => e (o i)) = e '' Set.range o := by
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨o i,⟨i,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
  change Module.finrank _ (Submodule.span _ (Set.range (fun i => e (o i)))) = _
  rw [he]
  change Module.finrank _ (Submodule.span _ (e.toLinearMap '' Set.range o)) = _
  calc
    _ = Module.finrank (ZMod 2) ((Submodule.span (ZMod 2) (Set.range o)).map e.toLinearMap) :=
      congrArg (fun T : Submodule (ZMod 2) (V (r*k)) => Module.finrank (ZMod 2) T)
        (Submodule.map_span e.toLinearMap (Set.range o)).symm
    _ = _ := (e.submoduleMap (Submodule.span (ZMod 2) (Set.range o))).finrank_eq.symm

def freq {p n : ℕ} (a : Fin p → V n × ZMod 2) (m : V p) : V n :=
  fun j => ∑ i, m i * (a i).1 j

def rhsFreq {p n : ℕ} (a : Fin p → V n × ZMod 2) (m : V p) : ZMod 2 :=
  ∑ i, m i * (a i).2

lemma freq_dot {p n : ℕ} (a : Fin p → V n × ZMod 2) (m : V p) (v : V n) :
    dotProduct (freq a m) v = ∑ i, m i * dotProduct (a i).1 v := by
  simp only [dotProduct, freq, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma walshHit {T : Type*} [Fintype T] {p n : ℕ} (a : Fin p → V n × ZMod 2)
    (flat : T → V n) (hit : T → ℕ) :
    (∑ m : V p, sg (rhsFreq a m) * ∑ c : T,
      (hit c : ℤ) * sg (dotProduct (freq a m) (flat c))) =
      (2 : ℤ)^p * ∑ c : T, if ∀ i, dotProduct (a i).1 (flat c) = (a i).2 then (hit c : ℤ) else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  let v : V p := fun i => dotProduct (a i).1 (flat c) - (a i).2
  have he (m : V p) : sg (rhsFreq a m) * ((hit c : ℤ) * sg (dotProduct (freq a m) (flat c))) =
      (hit c : ℤ) * sg (∑ i, m i * v i) := by
    rw [mul_left_comm, ← sg_add, freq_dot, rhsFreq, ← Finset.sum_add_distrib]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    simp [v, CharTwo.sub_eq_add, mul_add, add_comm]
  simp_rw [he]
  rw [← Finset.mul_sum, show (∑ m : V p, sg (∑ i, m i * v i)) = if (∀ i, v i = 0) then (2 : ℤ)^p else 0 by
    simpa only [sg, signInt] using char_ortho_sum p v]
  simp only [v, sub_eq_zero]
  split_ifs <;> ring

lemma prevFreq_zero {r k : ℕ} (b : SeqV r k) : (∑ i : Fin r, if i.val+1=0 then b i else 0) = 0 := by
  simp

def prevFreq {r k : ℕ} (b : SeqV r k) (j : ℕ) : V k :=
  if h : 0 < j ∧ j ≤ r then b ⟨j-1,by omega⟩ else 0

lemma prevFreq_eq {r k : ℕ} (b : SeqV r k) (j : ℕ) :
    prevFreq b j = ∑ i : Fin r, if i.val+1=j then b i else 0 := by
  classical
  unfold prevFreq
  split_ifs with hj
  · let i : Fin r := ⟨j-1,by omega⟩
    rw [Finset.sum_eq_single i]
    · simp [i, show j-1+1=j by omega]
    · intro l _ hl
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hl (Fin.ext (by dsimp [i]; omega)))
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

abbrev InCount (k r s q : ℕ) := (3+s+(r+1)*s)*k+q*r*k+q
abbrev IC (k r s q : ℕ) := Fin (InCount k r s q) → Bool
abbrev ISlot (k r s q : ℕ) :=
  Fin k ⊕ ((Fin s × Fin k) ⊕ ((Fin (r+1) × Fin s × Fin k) ⊕
    (Fin k ⊕ (Fin k ⊕ ((Fin q × Fin r × Fin k) ⊕ Fin q)))))

def slotRaw {k r s q : ℕ} (j : Fin k) : ISlot k r s q := .inl j

def slotDelta {k r s q : ℕ} (i : Fin s) (j : Fin k) : ISlot k r s q := .inr (.inl (i,j))

def slotPath {k r s q : ℕ} (t : Fin (r+1)) (i : Fin s) (j : Fin k) : ISlot k r s q :=
  .inr (.inr (.inl (t,i,j)))

def slotTest {k r s q : ℕ} (j : Fin k) : ISlot k r s q := .inr (.inr (.inr (.inl j)))

def slotTarget {k r s q : ℕ} (j : Fin k) : ISlot k r s q := .inr (.inr (.inr (.inr (.inl j))))

def slotObs {k r s q : ℕ} (i : Fin q) (t : Fin r) (j : Fin k) : ISlot k r s q :=
  .inr (.inr (.inr (.inr (.inr (.inl (i,t,j))))))

def slotWant {k r s q : ℕ} (i : Fin q) : ISlot k r s q :=
  .inr (.inr (.inr (.inr (.inr (.inr i)))))

def inputSlots (k r s q : ℕ) : List (ISlot k r s q) :=
  List.ofFn slotRaw ++ (List.ofFn fun i => List.ofFn (slotDelta i)).flatten ++
    (List.ofFn fun t => (List.ofFn fun i => List.ofFn (slotPath t i)).flatten).flatten ++
    List.ofFn slotTest ++ List.ofFn slotTarget ++
    (List.ofFn fun i => (List.ofFn fun t => List.ofFn (slotObs i t)).flatten).flatten ++
    List.ofFn slotWant

lemma inputSlots_length (k r s q : ℕ) : (inputSlots k r s q).length = InCount k r s q := by
  simp [inputSlots, List.length_flatten, InCount, Function.comp_def, List.ofFn_const]
  ring

lemma inputSlots_mem {k r s q : ℕ} (z : ISlot k r s q) : z ∈ inputSlots k r s q := by
  rcases z with j | (⟨i,j⟩ | (⟨t,i,j⟩ | (j | (j | (⟨i,t,j⟩ | i)))))
  · simp [inputSlots, slotRaw]
  · simp [inputSlots, slotDelta, List.mem_flatten, List.mem_ofFn]
  · simp [inputSlots, slotPath, List.mem_flatten, List.mem_ofFn] <;> tauto
  · simp [inputSlots, slotTest]
  · simp [inputSlots, slotTarget]
  · simp [inputSlots, slotObs, List.mem_flatten, List.mem_ofFn]
  · simp [inputSlots, slotWant]

def inputIndex {k r s q : ℕ} (z : ISlot k r s q) : Fin (InCount k r s q) :=
  ⟨(inputSlots k r s q).idxOf z, inputSlots_length k r s q ▸ List.idxOf_lt_length_of_mem (inputSlots_mem z)⟩

def slotVal {k r s q : ℕ} (x : IC k r s q) (z : ISlot k r s q) := b2z (x (inputIndex z))

def packVector {k r s q : ℕ} (v : ISlot k r s q → ZMod 2) : IC k r s q :=
  fun i => z2b (v ((inputSlots k r s q).get ⟨i.val, by rw [inputSlots_length]; exact i.isLt⟩))

lemma decodeSlot {k r s q : ℕ} (v : ISlot k r s q → ZMod 2) (z : ISlot k r s q) :
    slotVal (packVector v) z = v z := by
  simp [slotVal, packVector, inputIndex, b2z_z2b, List.get_eq_getElem, List.getElem_idxOf]

def inputData {k r s q : ℕ} (raw : V k) (δ : Fin s → V k) (path : Fin (r+1) → Fin s → V k)
    (test target : V k) (obs : Fin q → SeqV r k) (wanted : V q) : ISlot k r s q → ZMod 2
  | .inl j => raw j
  | .inr (.inl (i,j)) => δ i j
  | .inr (.inr (.inl (t,i,j))) => path t i j
  | .inr (.inr (.inr (.inl j))) => test j
  | .inr (.inr (.inr (.inr (.inl j)))) => target j
  | .inr (.inr (.inr (.inr (.inr (.inl (i,t,j)))))) => obs i t j
  | .inr (.inr (.inr (.inr (.inr (.inr i))))) => wanted i

def packedBits {k} (x : V k) := (List.finRange k).map (fun j => z2b (x j))

def packedSeq {k r} (x : SeqV r k) := (List.finRange r).flatMap (fun t => packedBits (x t))

def packedAll {k r s q : ℕ} (raw : V k) (δ : Fin s → V k) (path : Fin (r+1) → Fin s → V k)
    (test target : V k) (obs : Fin q → SeqV r k) (wanted : V q) : List Bool :=
  (packedBits raw ++ (List.finRange s).flatMap (fun p => packedBits (δ p)) ++
    (List.finRange (r+1)).flatMap (fun t => (List.finRange s).flatMap (fun p => packedBits (path t p))) ++
    packedBits test ++ packedBits target) ++ (List.finRange q).flatMap (fun i => packedSeq (obs i)) ++ packedBits wanted

lemma listMapRange {a : Type*} {n : ℕ} (f : Fin n → a) : (List.finRange n).map f = List.ofFn f := by
  exact List.map_ofFn (f := id) (g := f)

lemma packVector_spec {k r s q : ℕ} (raw : V k) (δ : Fin s → V k) (path : Fin (r+1) → Fin s → V k)
    (test target : V k) (obs : Fin q → SeqV r k) (wanted : V q) :
    List.ofFn (packVector (inputData raw δ path test target obs wanted)) =
      packedAll raw δ path test target obs wanted := by
  let v := inputData raw δ path test target obs wanted
  have h : List.ofFn (packVector v) = (inputSlots k r s q).map (fun i => z2b (v i)) := by
    apply List.ext_getElem
    · simp [inputSlots_length]
    · intro i hi hj
      simp [packVector]
  rw [h]
  simp only [inputSlots, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def,
    v, inputData, slotRaw, slotDelta, slotPath, slotObs, slotTest, slotTarget, slotWant, packedAll,
    packedBits, packedSeq, List.append_assoc, List.flatMap_def, listMapRange]

abbrev initProj (N : ℕ) : Set (Sig N) := Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)

lemma slotSignal {k r s q : ℕ} (z : ISlot k r s q) :
    (fun x => z2b (slotVal x z)) ∈ initProj (InCount k r s q) := by
  exact ⟨inputIndex z, by funext x; exact (z2b_b2z _).symm⟩

abbrev inRaw {k r s q : ℕ} (x : IC k r s q) : V k := fun j => slotVal x (slotRaw j)
abbrev inDelta {k r s q : ℕ} (x : IC k r s q) (p : Fin s) : V k := fun j => slotVal x (slotDelta p j)
abbrev inPath {k r s q : ℕ} (x : IC k r s q) (t : Fin (r+1)) (p : Fin s) : V k := fun j => slotVal x (slotPath t p j)
abbrev inTest {k r s q : ℕ} (x : IC k r s q) : V k := fun j => slotVal x (slotTest j)
abbrev inTarget {k r s q : ℕ} (x : IC k r s q) : V k := fun j => slotVal x (slotTarget j)
abbrev inObs {k r s q : ℕ} (x : IC k r s q) (i : Fin q) : SeqV r k := fun t j => slotVal x (slotObs i t j)
abbrev inWant {k r s q : ℕ} (x : IC k r s q) : V q := fun i => slotVal x (slotWant i)

open scoped BigOperators

abbrev RowsVec (n : ℕ) := Fin (n + 1) → ZMod 2
abbrev RowsState (n : ℕ) := (Fin n → RowsVec n) × Bool

def rowsCoeff {n : ℕ} : RowsVec n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun a i := a i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rowsAug {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2) : RowsVec n := Fin.snoc a b

def rowsBadVec (n : ℕ) : RowsVec n := rowsAug 0 1

def rowsAny {n : ℕ} (f : Fin n → Bool) : Bool := (List.finRange n).any f

theorem rowsAny_true {n : ℕ} (f : Fin n → Bool) : rowsAny f = true ↔ ∃ i, f i = true := by
  simp [rowsAny, List.any_eq_true]

theorem rows_btrue {a : ZMod 2} : z2b a = true ↔ a = 1 := by
  rcases z2_cases a with h | h <;> simp [h, z2b_zero, z2b_one, zero_ne_one]

theorem rows_bfalse {a : ZMod 2} : z2b a = false ↔ a = 0 := by
  rcases z2_cases a with h | h <;> simp [h, z2b_zero, z2b_one, one_ne_zero]

def rowsChoose {n : ℕ} (sel : Fin n → Bool) (a : Fin n → ZMod 2) : ZMod 2 :=
  b2z (rowsAny (fun i => sel i && z2b (a i)))

theorem rowsChoose_none {n : ℕ} (sel : Fin n → Bool) (a : Fin n → ZMod 2)
    (hs : ∀ i, sel i = false) : rowsChoose sel a = 0 := by
  have h : rowsAny (fun i => sel i && z2b (a i)) = false := by
    cases hh : rowsAny (fun i => sel i && z2b (a i))
    · rfl
    · obtain ⟨i, hi⟩ := (rowsAny_true _).mp hh
      simp [hs i] at hi
  simp [rowsChoose, h, b2z]

theorem rowsChoose_one {n : ℕ} (sel : Fin n → Bool) (a : Fin n → ZMod 2)
    (p : Fin n) (hs : ∀ i, sel i = true ↔ i = p) : rowsChoose sel a = a p := by
  have h : rowsAny (fun i => sel i && z2b (a i)) = z2b (a p) := by
    apply Bool.eq_iff_iff.mpr
    rw [rowsAny_true]
    simp [Bool.and_eq_true, hs]
  rw [rowsChoose, h, b2z_z2b]

def rowsResidual {n : ℕ} (st : RowsState n) (a : RowsVec n) : RowsVec n :=
  a + ∑ i : Fin n, (a i.castSucc) • st.1 i

def rowsStep {n : ℕ} (st : RowsState n) (a : RowsVec n) : RowsState n :=
  let b := rowsResidual st a
  let nz : Fin n → Bool := fun i => z2b (b i.castSucc)
  let sel := firstTrue nz
  (fun i => if sel i then b else st.1 i + (rowsChoose sel (fun p => st.1 i p.castSucc)) • b,
    st.2 || (!(rowsAny nz) && z2b (b (Fin.last n))))

def rowsValid {n : ℕ} (st : RowsState n) : Prop :=
  (∀ i : Fin n, st.1 i i.castSucc = 0 → st.1 i = 0) ∧
  (∀ i j : Fin n, j ≠ i → st.1 i i.castSucc ≠ 0 → st.1 j i.castSucc = 0)

theorem rowsResidual_old_pivot {n : ℕ} {st : RowsState n} (hv : rowsValid st)
    (a : RowsVec n) (i : Fin n) (hi : st.1 i i.castSucc ≠ 0) :
    rowsResidual st a i.castSucc = 0 := by
  have h1 : st.1 i i.castSucc = 1 := (z2_cases _).resolve_left hi
  simp only [rowsResidual, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [h1, mul_one, z2_add_self]
  · intro j _ hj
    rw [hv.2 i j hj hi, mul_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

theorem rowsStep_inv {n : ℕ} (st : RowsState n) (a : RowsVec n) (hv : rowsValid st) :
    rowsValid (rowsStep st a) ∧
      ∀ S : Submodule (ZMod 2) (RowsVec n),
        ((∀ i, (rowsStep st a).1 i ∈ S) ∧
          ((rowsStep st a).2 = true → rowsBadVec n ∈ S)) ↔
        ((∀ i, st.1 i ∈ S) ∧ (st.2 = true → rowsBadVec n ∈ S)) ∧ a ∈ S := by
  let b := rowsResidual st a
  let nz : Fin n → Bool := fun i => z2b (b i.castSucc)
  let sel := firstTrue nz
  have hsum (S : Submodule (ZMod 2) (RowsVec n)) (h : ∀ i, st.1 i ∈ S) :
      (∑ i : Fin n, (a i.castSucc) • st.1 i) ∈ S :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (h i))
  have hb_mem (S : Submodule (ZMod 2) (RowsVec n)) (hs : ∀ i, st.1 i ∈ S) :
      b ∈ S ↔ a ∈ S := by
    constructor
    · intro hb
      have hm := S.sub_mem hb (hsum S hs)
      simpa [b, rowsResidual] using hm
    · intro ha
      exact S.add_mem ha (hsum S hs)
  cases hany : rowsAny nz with
  | false =>
    have hz (i : Fin n) : b i.castSucc = 0 := by
      apply rows_bfalse.mp
      change nz i = false
      cases hi : nz i
      · rfl
      · have ht := (rowsAny_true nz).mpr ⟨i, hi⟩
        simp [hany] at ht
    have hn (i : Fin n) : sel i = false := by
      cases hi : sel i
      · rfl
      · have ht := ((firstTrue_spec nz i).mp hi).1
        simp [nz, hz i, z2b_zero] at ht
    have heq : rowsStep st a = (st.1, st.2 || z2b (b (Fin.last n))) := by
      unfold rowsStep
      change (fun i => if sel i then b else st.1 i + rowsChoose sel _ • b,
        st.2 || (!(rowsAny nz) && z2b (b (Fin.last n)))) = _
      simp [hn, rowsChoose_none sel _ hn, hany]
    have hb : b = b (Fin.last n) • rowsBadVec n := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [rowsBadVec, rowsAug, Pi.smul_apply, smul_eq_mul]
      · simp [rowsBadVec, rowsAug, Pi.smul_apply, smul_eq_mul, hz]
    rw [heq]
    refine ⟨hv, fun S => ?_⟩
    change ((∀ i, st.1 i ∈ S) ∧ ((st.2 || z2b (b (Fin.last n))) = true → rowsBadVec n ∈ S)) ↔ _
    simp only [Bool.or_eq_true]
    constructor
    · rintro ⟨hs, hc⟩
      refine ⟨⟨hs, fun ht => hc (Or.inl ht)⟩, (hb_mem S hs).mp ?_⟩
      rcases z2_cases (b (Fin.last n)) with h0 | h1
      · rw [hb, h0, zero_smul]
        exact S.zero_mem
      · rw [hb, h1, one_smul]
        exact hc (Or.inr (rows_btrue.mpr h1))
    · rintro ⟨⟨hs, hc⟩, ha⟩
      refine ⟨hs, ?_⟩
      rintro (hold | hnew)
      · exact hc hold
      · have hm := (hb_mem S hs).mpr ha
        have he : b = rowsBadVec n := by rw [hb, rows_btrue.mp hnew, one_smul]
        exact he ▸ hm
  | true =>
    obtain ⟨p, hp⟩ := (exists_firstTrue_iff nz).mpr ((rowsAny_true nz).mp hany)
    have hsp (i : Fin n) : sel i = true ↔ i = p :=
      ⟨fun hi => firstTrue_unique nz hi hp, fun h => h ▸ hp⟩
    have hp1 : b p.castSucc = 1 := rows_btrue.mp ((firstTrue_spec nz p).mp hp).1
    have hp0 : st.1 p = 0 := by
      apply hv.1 p
      by_contra h
      have hh := rowsResidual_old_pivot hv a p h
      change b p.castSucc = 0 at hh
      rw [hp1] at hh
      exact one_ne_zero hh
    have hrow (i : Fin n) : (rowsStep st a).1 i =
        if i = p then b else st.1 i + st.1 i p.castSucc • b := by
      change (if sel i then b else st.1 i + rowsChoose sel _ • b) = _
      rw [rowsChoose_one sel _ p hsp]
      by_cases h : i = p
      · subst i
        have hs : sel p = true := hp
        simp [hs]
      · have hfalse : sel i = false := by
          cases hh : sel i
          · rfl
          · exact (h ((hsp i).mp hh)).elim
        simp [h, hfalse]
    have hflag : (rowsStep st a).2 = st.2 := by
      change (st.2 || (!(rowsAny nz) && _)) = _
      simp [hany]
    have hnewp : (rowsStep st a).1 p = b := by rw [hrow, ite_eq_left rfl]
    have hnewpi (i : Fin n) (hi : i ≠ p) : (rowsStep st a).1 i p.castSucc = 0 := by
      rw [hrow, ite_eq_right hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp1, mul_one, z2_add_self]
    refine ⟨⟨?_, ?_⟩, fun S => ?_⟩
    · intro i hi
      by_cases hip : i = p
      · subst i
        rw [hnewp, hp1] at hi
        exact (one_ne_zero hi).elim
      · by_cases hi0 : st.1 i i.castSucc = 0
        · rw [hrow, ite_eq_right hip, hv.1 i hi0]
          simp
        · have hbi := rowsResidual_old_pivot hv a i hi0
          change b i.castSucc = 0 at hbi
          rw [hrow, ite_eq_right hip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbi, mul_zero, add_zero] at hi
          exact (hi0 hi).elim
    · intro i j hji hi
      by_cases hip : i = p
      · subst i
        exact hnewpi j hji
      · have hi0 : st.1 i i.castSucc ≠ 0 := by
          intro h
          apply hi
          rw [hrow, ite_eq_right hip, hv.1 i h]
          simp
        have hbi := rowsResidual_old_pivot hv a i hi0
        change b i.castSucc = 0 at hbi
        by_cases hjp : j = p
        · simp [hjp, hnewp, hbi]
        · rw [hrow, ite_eq_right hjp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbi, mul_zero, add_zero]
          exact hv.2 i j hji hi0
    · rw [hflag]
      constructor
      · rintro ⟨hs, hc⟩
        have hbS : b ∈ S := hnewp ▸ hs p
        have hprev (i : Fin n) : st.1 i ∈ S := by
          by_cases hi : i = p
          · subst i
            rw [hp0]
            exact S.zero_mem
          · have hm := S.sub_mem (hs i) (S.smul_mem (st.1 i p.castSucc) hbS)
            rwa [hrow, ite_eq_right hi, add_sub_cancel_right] at hm
        exact ⟨⟨hprev, hc⟩, (hb_mem S hprev).mp hbS⟩
      · rintro ⟨⟨hs, hc⟩, ha⟩
        have hbS := (hb_mem S hs).mpr ha
        refine ⟨fun i => ?_, hc⟩
        rw [hrow]
        split
        · exact hbS
        · exact S.add_mem (hs i) (S.smul_mem _ hbS)

def rowsStart (n : ℕ) : RowsState n := (fun _ => 0, false)

def rowsFeed {q n : ℕ} (obs : Fin q → Fin n → ZMod 2) (wanted : Fin q → ZMod 2)
    (t : ℕ) (st : RowsState n) : RowsState n :=
  if h : t < q then rowsStep st (rowsAug (obs ⟨t, h⟩) (wanted ⟨t, h⟩)) else st

def rowsReduce {q n : ℕ} (obs : Fin q → Fin n → ZMod 2) (wanted : Fin q → ZMod 2) : RowsState n :=
  (List.range q).foldl (fun st t => rowsFeed obs wanted t st) (rowsStart n)

theorem rowsReduce_inv {q n : ℕ} (obs : Fin q → Fin n → ZMod 2) (wanted : Fin q → ZMod 2) :
    let st := rowsReduce obs wanted
    rowsValid st ∧ ∀ S : Submodule (ZMod 2) (RowsVec n),
      ((∀ i, st.1 i ∈ S) ∧ (st.2 = true → rowsBadVec n ∈ S)) ↔
        ∀ j, rowsAug (obs j) (wanted j) ∈ S := by
  have hrun (t : ℕ) (ht : t ≤ q) :
      let st := (List.range t).foldl (fun st k => rowsFeed obs wanted k st) (rowsStart n)
      rowsValid st ∧ ∀ S : Submodule (ZMod 2) (RowsVec n),
        ((∀ i, st.1 i ∈ S) ∧ (st.2 = true → rowsBadVec n ∈ S)) ↔
          ∀ j : Fin q, j.val < t → rowsAug (obs j) (wanted j) ∈ S := by
    induction t with
    | zero =>
      refine ⟨⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, fun S => ?_⟩
      simp [rowsStart, S.zero_mem]
    | succ t ih =>
      have htq : t < q := by omega
      let st := (List.range t).foldl (fun st k => rowsFeed obs wanted k st) (rowsStart n)
      have heq : (List.range (t + 1)).foldl (fun st k => rowsFeed obs wanted k st) (rowsStart n) =
          rowsStep st (rowsAug (obs ⟨t, htq⟩) (wanted ⟨t, htq⟩)) := by
        simp [List.range_succ, List.foldl_append, st, rowsFeed, htq]
      rw [heq]
      obtain ⟨hv, hm⟩ := ih (by omega)
      obtain ⟨hv', hm'⟩ := rowsStep_inv st _ hv
      refine ⟨hv', fun S => ?_⟩
      rw [hm', hm]
      constructor
      · rintro ⟨hprev, hnew⟩ j hj
        by_cases h : j.val < t
        · exact hprev j h
        · have h' : j = ⟨t, htq⟩ := Fin.ext (by change j.val = t; omega)
          subst j
          exact hnew
      · intro h
        exact ⟨fun j hj => h j (by omega), h ⟨t, htq⟩ (by simp)⟩
  obtain ⟨hv, hm⟩ := hrun q le_rfl
  exact ⟨hv, fun S => (hm S).trans ⟨fun h j => h j j.isLt, fun h j _ => h j⟩⟩

@[local simp] theorem rowsCoeff_aug {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2) :
    rowsCoeff (rowsAug a b) = a := by
  funext i
  change Fin.snoc (α := fun _ => ZMod 2) a b i.castSucc = a i
  exact Fin.snoc_castSucc (α := fun _ => ZMod 2) b a i

theorem rowsReduce_span {q n : ℕ} (obs : Fin q → Fin n → ZMod 2) (wanted : Fin q → ZMod 2) :
    Submodule.span (ZMod 2) (Set.range (fun i => rowsCoeff ((rowsReduce obs wanted).1 i))) =
      Submodule.span (ZMod 2) (Set.range obs) := by
  let st := rowsReduce obs wanted
  obtain ⟨_, h⟩ := rowsReduce_inv obs wanted
  have hh (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
      (∀ i, rowsCoeff (st.1 i) ∈ S) ↔ (∀ j, obs j ∈ S) := by
    have hb : rowsCoeff (rowsBadVec n) ∈ S := by
      change rowsCoeff (rowsAug 0 1) ∈ S
      simp
    simpa only [Submodule.mem_comap, rowsCoeff_aug, hb, implies_true, and_true] using
      h (S.comap rowsCoeff)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hh (Submodule.span (ZMod 2) (Set.range obs))).mpr
      (fun j => Submodule.subset_span ⟨j, rfl⟩) i
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hh (Submodule.span (ZMod 2) (Set.range (fun i => rowsCoeff (st.1 i))))).mp
      (fun i => Submodule.subset_span ⟨i, rfl⟩) j

def rowsUsed {n : ℕ} (st : RowsState n) (i : Fin n) : Bool := z2b (st.1 i i.castSucc)

def rowsPrefix {n : ℕ} (st : RowsState n) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i.val < t ∧ rowsUsed st i = true)).card

theorem rowsPrefix_rank {q n : ℕ} (obs : Fin q → Fin n → ZMod 2) (wanted : Fin q → ZMod 2) :
    rowsPrefix (rowsReduce obs wanted) n =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range obs)) := by
  classical
  let st := rowsReduce obs wanted
  let M := fun i => rowsCoeff (st.1 i)
  have hspan : Submodule.span (ZMod 2) (Set.range M) =
      Submodule.span (ZMod 2) (Set.range obs) := rowsReduce_span obs wanted
  obtain ⟨hv, _⟩ := rowsReduce_inv obs wanted
  let U : Finset (Fin n) := Finset.univ.filter (fun i => rowsUsed st i = true)
  let S : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range obs)
  have hmemS (i : U) : M i.val ∈ S := by
    change M i.val ∈ Submodule.span (ZMod 2) (Set.range obs)
    rw [← hspan]
    exact Submodule.subset_span ⟨i.val, rfl⟩
  let v : U → S := fun i => ⟨M i.val, hmemS i⟩
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hval := congrArg Subtype.val ha
    simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, v] at hval
    have hi : st.1 i.val i.val.castSucc = 1 :=
      rows_btrue.mp (Finset.mem_filter.mp i.2).2
    have hc := congrFun hval i.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
    rw [Finset.sum_eq_single i] at hc
    · change a i * st.1 i.val i.val.castSucc = 0 at hc
      simpa [hi] using hc
    · intro j _ hj
      have hne : j.val ≠ i.val := fun h => hj (Subtype.ext h)
      change a j * st.1 j.val i.val.castSucc = 0
      have hnonzero : st.1 i.val i.val.castSucc ≠ 0 := by
        rw [hi]
        exact one_ne_zero
      rw [hv.2 i.val j.val hne hnonzero, mul_zero]
    · exact fun h => (h (Finset.mem_univ i)).elim
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rintro ⟨y, hy⟩ _
    have hy' : y ∈ Submodule.span (ZMod 2) (Set.range M) := by rwa [hspan]
    have hm : Submodule.span (ZMod 2) (Set.range M) ≤
        Submodule.map S.subtype (Submodule.span (ZMod 2) (Set.range v)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases hi : rowsUsed st i with
      | false =>
        have hz : st.1 i = 0 := hv.1 i (rows_bfalse.mp hi)
        have hh : M i = 0 := by change rowsCoeff (st.1 i) = 0; rw [hz, map_zero]
        rw [hh]
        exact Submodule.zero_mem _
      | true =>
        have hiU : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        exact ⟨v ⟨i, hiU⟩, Submodule.subset_span ⟨⟨i, hiU⟩, rfl⟩, rfl⟩
    rcases hm hy' with ⟨w, hw, hwy⟩
    have : w = ⟨y, hy⟩ := Subtype.ext hwy
    rwa [← this]
  let b : Module.Basis U (ZMod 2) S := Module.Basis.mk hli htop
  have hcard : Fintype.card U = Module.finrank (ZMod 2) S := (Module.finrank_eq_card_basis b).symm
  rw [Fintype.card_coe] at hcard
  simpa [rowsPrefix, U, st, S, Fin.isLt] using hcard

theorem rowsPrefix_mono {n : ℕ} (st : RowsState n) {t u : ℕ} (h : t ≤ u) :
    rowsPrefix st t ≤ rowsPrefix st u := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hm, ht, hu⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hm, lt_of_lt_of_le ht h, hu⟩

theorem rowsPrefix_succ {n : ℕ} (st : RowsState n) (t : ℕ) (ht : t < n) :
    rowsPrefix st (t + 1) = rowsPrefix st t + if rowsUsed st ⟨t, ht⟩ then 1 else 0 := by
  let k : Fin n := ⟨t, ht⟩
  let s := Finset.univ.filter (fun i : Fin n => i.val < t ∧ rowsUsed st i = true)
  let u := Finset.univ.filter (fun i : Fin n => i.val < t + 1 ∧ rowsUsed st i = true)
  change u.card = s.card + if rowsUsed st k then 1 else 0
  have hk : k ∉ s := by simp [s, k]
  have he (i : Fin n) : i = k ↔ i.val = t := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  cases hu : rowsUsed st k with
  | false =>
    have h : u = s := by
      ext i
      simp only [u, s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi, hused⟩
        refine ⟨?_, hused⟩
        by_contra hh
        have hik := (he i).mpr (by omega)
        rw [hik, hu] at hused
        exact Bool.noConfusion hused
      · exact fun h => ⟨by omega, h.2⟩
    simp [h]
  | true =>
    have h : u = insert k s := by
      ext i
      simp only [u, s, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hused⟩
        by_cases hh : i.val < t
        · exact Or.inr ⟨hh, hused⟩
        · exact Or.inl ((he i).mpr (by omega))
      · rintro (rfl | ⟨hi, hused⟩)
        · exact ⟨by simp [k], hu⟩
        · exact ⟨by omega, hused⟩
    simp [h, Finset.card_insert_of_notMem hk]

theorem rowsPrefix_lt {n : ℕ} (st : RowsState n) {i : Fin n} {t : ℕ}
    (h : rowsUsed st i = true) (hi : i.val < t) : rowsPrefix st i.val < rowsPrefix st t := by
  have hs := rowsPrefix_succ st i.val i.isLt
  simp [h] at hs
  have hm := rowsPrefix_mono st (show i.val + 1 ≤ t by omega)
  omega

def rowsPick {n : ℕ} (st : RowsState n) (j : ℕ) (i : Fin n) : Bool :=
  rowsUsed st i && decide (rowsPrefix st i.val = j)

theorem rowsPick_unique {n : ℕ} (st : RowsState n) (j : ℕ) {i k : Fin n}
    (hi : rowsPick st j i = true) (hk : rowsPick st j k = true) : i = k := by
  simp only [rowsPick, Bool.and_eq_true, decide_eq_true_eq] at hi hk
  rcases lt_trichotomy i.val k.val with h | h | h
  · have hh := rowsPrefix_lt st hi.1 h
    omega
  · exact Fin.ext h
  · have hh := rowsPrefix_lt st hk.1 h
    omega

def rowsPackedVec {n : ℕ} (st : RowsState n) (j : ℕ) : RowsVec n :=
  fun c => rowsChoose (rowsPick st j) (fun i => st.1 i c)

def rowsPadded {n : ℕ} (cap : ℕ) (st : RowsState n) (j : Fin (min cap n)) :
    (Fin n → ZMod 2) × ZMod 2 :=
  (rowsCoeff (rowsPackedVec st j.val), rowsPackedVec st j.val (Fin.last n))

theorem rowsPackedVec_eq {n : ℕ} {st : RowsState n} {i : Fin n} {j : ℕ}
    (h : rowsPick st j i = true) : rowsPackedVec st j = st.1 i := by
  funext c
  exact rowsChoose_one _ _ i (fun k => ⟨fun hk => rowsPick_unique st j hk h, fun e => e ▸ h⟩)

theorem rowsPackedVec_zero {n : ℕ} (st : RowsState n) (j : ℕ)
    (h : ¬ ∃ i, rowsPick st j i = true) : rowsPackedVec st j = 0 := by
  funext c
  apply rowsChoose_none
  intro i
  cases hi : rowsPick st j i
  · rfl
  · exact (h ⟨i, hi⟩).elim

theorem rowsPadded_mem {n : ℕ} (cap : ℕ) (st : RowsState n) (hv : rowsValid st)
    (hr : rowsPrefix st n ≤ cap) (S : Submodule (ZMod 2) (RowsVec n)) :
    (∀ j : Fin (min cap n), rowsPackedVec st j.val ∈ S) ↔ ∀ i, st.1 i ∈ S := by
  constructor
  · intro h i
    cases hi : rowsUsed st i with
    | false =>
      rw [hv.1 i (rows_bfalse.mp hi)]
      exact S.zero_mem
    | true =>
      have hl := rowsPrefix_lt st hi i.isLt
      have hn : rowsPrefix st n ≤ n := by
        simpa [rowsPrefix] using
          (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
            (p := fun i : Fin n => i.val < n ∧ rowsUsed st i = true))
      let j : Fin (min cap n) := ⟨rowsPrefix st i.val, lt_min (by omega) (by omega)⟩
      have hj : rowsPick st j.val i = true := by simp [rowsPick, j, hi]
      simpa only [rowsPackedVec_eq hj] using h j
  · intro h j
    by_cases he : ∃ i, rowsPick st j.val i = true
    · obtain ⟨i, hi⟩ := he
      simpa only [rowsPackedVec_eq hi] using h i
    · rw [rowsPackedVec_zero st j.val he]
      exact S.zero_mem

def rowsConsistent {n : ℕ} (st : RowsState n) : Bool := !st.2

def rowsEval {n : ℕ} (v : Fin n → ZMod 2) : RowsVec n →ₗ[ZMod 2] ZMod 2 where
  toFun a := dotProduct (rowsCoeff a) v - a (Fin.last n)
  map_add' a b := by
    change dotProduct (rowsCoeff (a+b)) v - (a+b) (Fin.last n) = _
    rw [map_add, add_dotProduct, Pi.add_apply]
    abel
  map_smul' c a := by
    change dotProduct (rowsCoeff (c • a)) v - (c • a) (Fin.last n) = _
    rw [map_smul, smul_dotProduct, Pi.smul_apply, smul_sub]
    rfl

theorem rowsEval_mem {n : ℕ} (v : Fin n → ZMod 2) (a : RowsVec n) :
    a ∈ (rowsEval v).ker ↔ dotProduct (rowsCoeff a) v = a (Fin.last n) := by
  rw [LinearMap.mem_ker]
  change (dotProduct (rowsCoeff a) v - a (Fin.last n) = 0) ↔ _
  exact sub_eq_zero

theorem rows_spec {q n : ℕ} (cap : ℕ) (obs : Fin q → Fin n → ZMod 2)
    (wanted : Fin q → ZMod 2) (v : Fin n → ZMod 2) :
    let st := rowsReduce obs wanted
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range obs)) ≤ cap →
      rowsConsistent st = true →
      ((∀ j, dotProduct (obs j) v = wanted j) ↔
        ∀ j, dotProduct (rowsPadded cap st j).1 v = (rowsPadded cap st j).2)) ∧
    (rowsConsistent st = false → ¬ (∀ j, dotProduct (obs j) v = wanted j)) := by
  let st := rowsReduce obs wanted
  let S := (rowsEval v).ker
  obtain ⟨hv, hm⟩ := rowsReduce_inv obs wanted
  have hbad : rowsBadVec n ∉ S := by
    change rowsBadVec n ∉ (rowsEval v).ker
    rw [rowsEval_mem, rowsBadVec, rowsCoeff_aug]
    simp [rowsAug]
  have horig : (∀ j, rowsAug (obs j) (wanted j) ∈ S) ↔
      ∀ j, dotProduct (obs j) v = wanted j := by
    change (∀ j, rowsAug (obs j) (wanted j) ∈ (rowsEval v).ker) ↔ _
    simp only [rowsEval_mem, rowsCoeff_aug]
    simp [rowsAug]
  have hpad : (∀ j : Fin (min cap n), rowsPackedVec st j.val ∈ S) ↔
      ∀ j, dotProduct (rowsPadded cap st j).1 v = (rowsPadded cap st j).2 := by
    change (∀ j : Fin (min cap n), rowsPackedVec st j.val ∈ (rowsEval v).ker) ↔ _
    simp only [rowsEval_mem, rowsPadded]
  change (_ → rowsConsistent st = true → _) ∧ (rowsConsistent st = false → _)
  constructor
  · intro hr hc
    have hc' : st.2 = false := by simpa [rowsConsistent] using hc
    have hr' : rowsPrefix st n ≤ cap := by simpa [st, rowsPrefix_rank] using hr
    rw [← horig, ← hpad, rowsPadded_mem cap st hv hr' S]
    exact ⟨fun h => ((hm S).mpr h).1, fun h => (hm S).mp ⟨h, fun ht => by
      change st.2 = true at ht
      simp [hc'] at ht⟩⟩
  · intro hc ha
    have hc' : st.2 = true := by simpa [rowsConsistent] using hc
    exact hbad (((hm S).mpr (horig.mpr ha)).2 hc')

def rowsBit {N n : ℕ} (a : (Fin N → Bool) → RowsVec n) (c : Fin (n + 1)) : Sig N :=
  fun x => z2b (a x c)

def rowsStateSigs {N n : ℕ} (st : (Fin N → Bool) → RowsState n) : Set (Sig N) :=
  (⋃ i : Fin n, Set.range (rowsBit (fun x => (st x).1 i))) ∪ {fun x => (st x).2}

theorem rowsState_bit {N n : ℕ} (st : (Fin N → Bool) → RowsState n)
    (i : Fin n) (c : Fin (n + 1)) :
    rowsBit (fun x => (st x).1 i) c ∈ rowsStateSigs st :=
  Or.inl (Set.mem_iUnion.mpr ⟨i, ⟨c, rfl⟩⟩)

theorem rowsAnyB {N n : ℕ} {A : Set (Sig N)} (f : Fin n → Sig N)
    (hfalse : (fun _ => false) ∈ A) (hf : ∀ i, f i ∈ A) :
    Build A {fun x => rowsAny (fun i => f i x)} n := by
  let fs := (List.finRange n).map f
  have hs : ∀ g ∈ fs, g ∈ A := by
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact hf i
  simpa only [fs, List.length_map, List.length_finRange, rowsAny, List.any_map, Function.comp_def]
    using orListB fs hs hfalse

theorem rowsChooseB {N n : ℕ} {A : Set (Sig N)} (sel : Fin n → Sig N)
    (a : (Fin N → Bool) → Fin n → ZMod 2)
    (hfalse : (fun _ => false) ∈ A) (hs : ∀ i, sel i ∈ A)
    (ha : ∀ i, (fun x => z2b (a x i)) ∈ A) :
    Build A {fun x => z2b (rowsChoose (fun i => sel i x) (a x))} (2 * n) := by
  let f : Fin n → Sig N := fun i x => sel i x && z2b (a x i)
  have h1 := finSigB f 1 (fun i => andB (hs i) (ha i))
  have h2 := rowsAnyB (A := A ∪ Set.range f) f (Or.inl hfalse) (fun i => Or.inr ⟨i, rfl⟩)
  have hb := seq2B h1 h2
  simpa [rowsChoose, f, z2b_b2z, Nat.two_mul] using hb

theorem rowsSumB {N n : ℕ} {A : Set (Sig N)} (a : (Fin N → Bool) → Fin n → ZMod 2)
    (hfalse : (fun _ => false) ∈ A) (ha : ∀ i, (fun x => z2b (a x i)) ∈ A) :
    Build A {fun x => z2b (∑ i, a x i)} (4 * n) := by
  let fs := (List.finRange n).map (fun i x => z2b (a x i))
  have hs : ∀ g ∈ fs, g ∈ A := by
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact ha i
  have he : (fun x => z2b (∑ i, a x i)) = fun x => xorList (fs.map (fun g => g x)) := by
    funext x
    rw [z2b_fin_sum]
    simp [fs, List.map_map, Function.comp_def]
  rw [he]
  simpa [fs] using xorListB fs hs hfalse

theorem rowsAddMulB {N : ℕ} {A : Set (Sig N)} (a s b : (Fin N → Bool) → ZMod 2)
    (ha : (fun x => z2b (a x)) ∈ A) (hs : (fun x => z2b (s x)) ∈ A)
    (hb : (fun x => z2b (b x)) ∈ A) :
    Build A {fun x => z2b (a x + s x * b x)} 5 := by
  have h1 : Build A {fun x => z2b (s x * b x)} 1 := by
    simpa only [z2b_mul] using andB hs hb
  have h2 : Build (A ∪ {fun x => z2b (s x * b x)}) {fun x => z2b (a x + s x * b x)} 4 := by
    rw [show (fun x => z2b (a x + s x * b x)) =
      (fun x => xor (z2b (a x)) (z2b (s x * b x))) from funext (fun x => z2b_add _ _)]
    exact xorB (Or.inl ha) (Or.inr rfl)
  exact seq2B h1 h2

theorem rowsFlagB {N n : ℕ} {A : Set (Sig N)} (f : Fin n → Sig N) (old rhs : Sig N)
    (hfalse : (fun _ => false) ∈ A) (hf : ∀ i, f i ∈ A) (ho : old ∈ A) (hr : rhs ∈ A) :
    Build A {fun x => old x || (!(rowsAny (fun i => f i x)) && rhs x)} (n + 3) := by
  let t₁ : Sig N := fun x => rowsAny (fun i => f i x)
  let t₂ : Sig N := fun x => !t₁ x
  let t₃ : Sig N := fun x => t₂ x && rhs x
  have h1 : Build A {t₁} n := rowsAnyB f hfalse hf
  have h2 : Build (A ∪ {t₁}) {t₂} 1 := notB (Or.inr rfl)
  have h3 : Build (A ∪ ({t₁} ∪ {t₂})) {t₃} 1 := andB (Or.inr (Or.inr rfl)) (Or.inl hr)
  have h4 : Build (A ∪ (({t₁} ∪ {t₂}) ∪ {t₃})) {fun x => old x || t₃ x} 1 :=
    orB (Or.inl ho) (Or.inr (Or.inr rfl))
  have hb := seq2B (seqB (seqB h1 h2) h3) h4
  exact hb

theorem rowsResidualB {N n : ℕ} {A : Set (Sig N)}
    (st : (Fin N → Bool) → RowsState n) (a : (Fin N → Bool) → RowsVec n)
    (hfalse : (fun _ => false) ∈ A) (hst : rowsStateSigs st ⊆ A) (ha : ∀ c, rowsBit a c ∈ A) :
    Build A (Set.range (rowsBit (fun x => rowsResidual (st x) (a x)))) ((n + 1) * (5*n + 4)) := by
  refine finSigB _ (5*n + 4) (fun c => ?_)
  let term : (Fin N → Bool) → Fin n → ZMod 2 := fun x i => a x i.castSucc * (st x).1 i c
  let tb : Fin n → Sig N := fun i x => z2b (term x i)
  let sum : Sig N := fun x => z2b (∑ i, term x i)
  have h1 : Build A (Set.range tb) (n * 1) := by
    refine finSigB tb 1 (fun i => ?_)
    simpa only [rowsBit, tb, term, z2b_mul] using andB (ha i.castSucc) (hst (rowsState_bit st i c))
  have h2 : Build (A ∪ Set.range tb) {sum} (4*n) :=
    rowsSumB term (Or.inl hfalse) (fun i => Or.inr ⟨i, rfl⟩)
  have h3 : Build (A ∪ {sum}) {fun x => xor (rowsBit a c x) (sum x)} 4 :=
    xorB (Or.inl (ha c)) (Or.inr rfl)
  have he : rowsBit (fun x => rowsResidual (st x) (a x)) c = fun x => xor (rowsBit a c x) (sum x) := by
    funext x
    simp only [rowsBit, rowsResidual, sum, term, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, z2b_add]
  rw [he]
  exact relaxB (seq2B (seq2B h1 h2) h3) le_rfl Set.subset_union_right (by omega)

theorem rowsStepB {N n : ℕ} {A : Set (Sig N)}
    (st : (Fin N → Bool) → RowsState n) (a : (Fin N → Bool) → RowsVec n)
    (hfalse : (fun _ => false) ∈ A) (hst : rowsStateSigs st ⊆ A) (ha : ∀ c, rowsBit a c ∈ A) :
    Build A (rowsStateSigs (fun x => rowsStep (st x) (a x))) (64 * (n + 2)^2) := by
  let b : (Fin N → Bool) → RowsVec n := fun x => rowsResidual (st x) (a x)
  let nz : Fin n → Sig N := fun i => rowsBit b i.castSucc
  let sel : Fin n → Sig N := fun i x => firstTrue (fun j => nz j x) i
  let factor : (Fin N → Bool) → Fin n → ZMod 2 :=
    fun x i => rowsChoose (fun j => sel j x) (fun j => (st x).1 i j.castSucc)
  let fb : Fin n → Sig N := fun i x => z2b (factor x i)
  let R := Set.range (rowsBit b)
  let P := Set.range sel
  let T := Set.range fb
  let B := (A ∪ (R ∪ P)) ∪ T
  have h1 : Build A R ((n + 1) * (5*n + 4)) := rowsResidualB st a hfalse hst ha
  have h2 : Build (A ∪ R) P (n*(n+2)) :=
    firstTrueB nz (Or.inl hfalse) (fun i => Or.inr ⟨i.castSucc, rfl⟩)
  have h3 : Build (A ∪ (R ∪ P)) T (n * (2*n)) := by
    refine finSigB fb (2*n) (fun i => ?_)
    exact rowsChooseB sel (fun x j => (st x).1 i j.castSucc) (Or.inl hfalse)
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
      (fun j => Or.inl (hst (rowsState_bit st i j.castSucc)))
  have hA : A ⊆ B := fun _ h => Or.inl (Or.inl h)
  have hR : R ⊆ B := fun _ h => Or.inl (Or.inr (Or.inl h))
  have hP : P ⊆ B := fun _ h => Or.inl (Or.inr (Or.inr h))
  let o : (Fin N → Bool) → RowsState n := fun x => rowsStep (st x) (a x)
  have h4 : Build B (⋃ i : Fin n, Set.range (rowsBit (fun x => (o x).1 i))) (n*((n+1)*9)) := by
    refine finB _ ((n+1)*9) (fun i => finSigB _ 9 (fun c => ?_))
    let v : Sig N := fun x => z2b ((st x).1 i c + factor x i * b x c)
    have h5 : Build B {v} 5 :=
      rowsAddMulB (fun x => (st x).1 i c) (fun x => factor x i) (fun x => b x c)
        (hA (hst (rowsState_bit st i c))) (Or.inr ⟨i, rfl⟩) (hR ⟨c, rfl⟩)
    have h6 : Build (B ∪ {v}) {fun x => if sel i x then rowsBit b c x else v x} 4 :=
      iteB (Or.inl (hP ⟨i, rfl⟩)) (Or.inl (hR ⟨c, rfl⟩)) (Or.inr rfl)
    have he : rowsBit (fun x => (o x).1 i) c = fun x => if sel i x then rowsBit b c x else v x := by
      funext x
      change z2b ((if sel i x then b x else (st x).1 i + factor x i • b x) c) = _
      split <;> simp [rowsBit, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    exact seq2B h5 h6
  have h5 : Build B {fun x => (o x).2} (n+3) :=
    rowsFlagB nz (fun x => (st x).2) (rowsBit b (Fin.last n)) (hA hfalse)
      (fun i => hR ⟨i.castSucc, rfl⟩) (hA (hst (Or.inr rfl))) (hR ⟨Fin.last n, rfl⟩)
  have h6 : Build (A ∪ ((R ∪ P) ∪ T)) (rowsStateSigs o) (n*((n+1)*9)+(n+3)) := by
    apply relaxB (unionB h4 h5)
    · simpa only [B, Set.union_assoc] using (Set.Subset.rfl : B ⊆ B)
    · exact Set.subset_union_right
    · exact le_rfl
  refine relaxB (seq2B (seqB (seqB h1 h2) h3) h6) le_rfl Set.subset_union_right ?_
  have he : (n+1)*(5*n+4) + n*(n+2) + n*(2*n) + (n*((n+1)*9)+(n+3)) +
      (47*n^2+235*n+249) = 64*(n+2)^2 := by ring
  rw [← he]
  omega

theorem rowsReduceB {N q n : ℕ} {A : Set (Sig N)}
    (obs : (Fin N → Bool) → Fin q → Fin n → ZMod 2)
    (wanted : (Fin N → Bool) → Fin q → ZMod 2)
    (hfalse : (fun _ => false) ∈ A)
    (ho : ∀ i j, (fun x => z2b (obs x i j)) ∈ A)
    (hw : ∀ i, (fun x => z2b (wanted x i)) ∈ A) :
    Build A (rowsStateSigs (fun x => rowsReduce (obs x) (wanted x))) (q * (64 * (n+2)^2)) := by
  let Sigs : ((Fin N → Bool) → RowsState n) → Set (Sig N) := rowsStateSigs
  let step (t : ℕ) (st : (Fin N → Bool) → RowsState n) : (Fin N → Bool) → RowsState n :=
    fun x => rowsFeed (obs x) (wanted x) t (st x)
  have h (t : ℕ) (st : (Fin N → Bool) → RowsState n) :
      Build (A ∪ Sigs st) (Sigs (step t st)) (64*(n+2)^2) := by
    by_cases ht : t < q
    · let a : (Fin N → Bool) → RowsVec n := fun x => rowsAug (obs x ⟨t, ht⟩) (wanted x ⟨t, ht⟩)
      have ha (c : Fin (n+1)) : rowsBit a c ∈ A ∪ Sigs st := by
        refine Or.inl (Fin.lastCases (motive := fun j => rowsBit a j ∈ A) ?_ (fun i => ?_) c)
        · change (fun x => z2b (Fin.snoc (α := fun _ => ZMod 2)
            (obs x ⟨t, ht⟩) (wanted x ⟨t, ht⟩) (Fin.last n))) ∈ A
          simpa only [Fin.snoc_last] using hw ⟨t, ht⟩
        · change (fun x => z2b (Fin.snoc (α := fun _ => ZMod 2)
            (obs x ⟨t, ht⟩) (wanted x ⟨t, ht⟩) i.castSucc)) ∈ A
          simpa only [Fin.snoc_castSucc] using ho ⟨t, ht⟩ i
      simpa only [step, rowsFeed, ht, dite_eq_left, Sigs, a] using
        rowsStepB st a (Or.inl hfalse) Set.subset_union_right ha
    · have he : step t st = st := by funext x; simp [step, rowsFeed, ht]
      rw [he]
      exact relaxB (idleB Set.subset_union_right) le_rfl Set.subset_union_right (Nat.zero_le _)
  have hinit : Sigs (fun _ => rowsStart n) ⊆ A := by
    intro f hf
    rcases hf with h | h
    · obtain ⟨i, ⟨c, rfl⟩⟩ := Set.mem_iUnion.mp h
      change (fun _ => z2b 0) ∈ A
      simpa only [z2b_zero] using hfalse
    · obtain rfl := Set.mem_singleton_iff.mp h
      exact hfalse
  let start : (Fin N → Bool) → RowsState n := fun _ => rowsStart n
  have hb (t : ℕ) : Build (A ∪ Sigs start)
      (Sigs (fun x => (List.range t).foldl
        (fun st k => rowsFeed (obs x) (wanted x) k st) (rowsStart n))) (t*(64*(n+2)^2)) := by
    induction t with
    | zero =>
      simpa only [List.range_zero, List.foldl_nil, Nat.zero_mul, start] using
        (idleB (A := A ∪ Sigs start) (B := Sigs start) Set.subset_union_right)
    | succ t ih =>
      let prev : (Fin N → Bool) → RowsState n := fun x =>
        (List.range t).foldl (fun st k => rowsFeed (obs x) (wanted x) k st) (rowsStart n)
      have hstep : Build ((A ∪ Sigs start) ∪ Sigs prev) (Sigs (step t prev)) (64*(n+2)^2) :=
        relaxB (h t prev)
          (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
          Set.subset_union_right le_rfl
      simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        prev, step, Nat.succ_mul] using seq2B ih hstep
  exact relaxB (hb q) (Set.union_subset le_rfl hinit) Set.subset_union_right le_rfl

def rowsThresh {N n : ℕ} (st : (Fin N → Bool) → RowsState n) (t : ℕ)
    (j : Fin (n+2)) : Sig N := fun x => decide (j.val ≤ rowsPrefix (st x) t)

theorem rowsThreshB {N n : ℕ} {A : Set (Sig N)}
    (st : (Fin N → Bool) → RowsState n)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hst : rowsStateSigs st ⊆ A) (t : ℕ) (ht : t ≤ n) :
    Build A (Set.range (rowsThresh st t)) (t*((n+2)*4)) := by
  induction t with
  | zero =>
    rw [Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have he : rowsThresh st 0 j = fun _ => decide (j.val ≤ 0) := by
      funext x
      simp [rowsThresh, rowsPrefix]
    rw [he]
    cases h : decide (j.val ≤ 0)
    · simpa only [h] using hfalse
    · simpa only [h] using htrue
  | succ t ih =>
    have htn : t < n := by omega
    let i : Fin n := ⟨t, htn⟩
    let u : Sig N := fun x => rowsUsed (st x) i
    let prev := Set.range (rowsThresh st t)
    have hu : u ∈ A := hst (rowsState_bit st i i.castSucc)
    have h1 : Build A prev (t*((n+2)*4)) := ih (by omega)
    have h2 : Build (A ∪ prev) (Set.range (rowsThresh st (t+1))) ((n+2)*4) := by
      refine finSigB _ 4 (fun j => ?_)
      by_cases hj : j.val = 0
      · have he : rowsThresh st (t+1) j = fun _ => true := by
          funext x
          simp [rowsThresh, hj]
        rw [he]
        exact relaxB (idleB (by simpa using (Or.inl htrue : (fun _ => true) ∈ A ∪ prev)))
          le_rfl Set.subset_union_right (by omega)
      · let k : Fin (n+2) := ⟨j.val - 1, by omega⟩
        have he : rowsThresh st (t+1) j = fun x =>
            if u x then rowsThresh st t k x else rowsThresh st t j x := by
          funext x
          change decide (j.val ≤ rowsPrefix (st x) (t+1)) = _
          rw [rowsPrefix_succ (st x) t htn]
          change decide (j.val ≤ rowsPrefix (st x) t + if u x then 1 else 0) = _
          cases h : u x with
          | false => simp [rowsThresh]
          | true =>
            apply Bool.eq_iff_iff.mpr
            simp [rowsThresh, k]
        rw [he]
        exact iteB (Or.inl hu) (Or.inr ⟨k, rfl⟩) (Or.inr ⟨j, rfl⟩)
    simpa only [Nat.succ_mul] using seq2B h1 h2

theorem rowsPickB {N n : ℕ} {A : Set (Sig N)}
    (st : (Fin N → Bool) → RowsState n) (i : Fin n) (j : Fin n)
    (hst : rowsStateSigs st ⊆ A)
    (hprev : Set.range (rowsThresh st i.val) ⊆ A) :
    Build A {fun x => rowsPick (st x) j.val i} 3 := by
  let u : Sig N := fun x => rowsUsed (st x) i
  let j₀ : Fin (n+2) := ⟨j.val, by omega⟩
  let j₁ : Fin (n+2) := ⟨j.val + 1, by omega⟩
  let a := rowsThresh st i.val j₀
  let b := rowsThresh st i.val j₁
  let nb : Sig N := fun x => !b x
  let eq : Sig N := fun x => a x && nb x
  have he : (fun x => rowsPick (st x) j.val i) = fun x => u x && eq x := by
    funext x
    have hh : decide (rowsPrefix (st x) i.val = j.val) = eq x := by
      apply Bool.eq_iff_iff.mpr
      simp [eq, nb, a, b, rowsThresh, j₀, j₁]
      omega
    exact congrArg (fun y => u x && y) hh
  rw [he]
  have h1 : Build A {nb} 1 := notB (hprev ⟨j₁, rfl⟩)
  have h2 : Build (A ∪ {nb}) {eq} 1 := andB (Or.inl (hprev ⟨j₀, rfl⟩)) (Or.inr rfl)
  have h3 : Build (A ∪ ({nb} ∪ {eq})) {fun x => u x && eq x} 1 :=
    andB (Or.inl (hst (rowsState_bit st i i.castSucc))) (Or.inr (Or.inr rfl))
  exact seq2B (seqB h1 h2) h3

def rowsPackedSigs {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n) : Set (Sig N) :=
  ⋃ j : Fin (min cap n), Set.range (rowsBit (fun x => rowsPackedVec (st x) j.val))

def rowsOutputs {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n)
    (overflow : Sig N) : Set (Sig N) :=
  {overflow} ∪ ({fun x => rowsConsistent (st x)} ∪ rowsPackedSigs cap st)

theorem rows_out_overflow {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n)
    (overflow : Sig N) : overflow ∈ rowsOutputs cap st overflow := Or.inl rfl

theorem rows_out_consistent {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n)
    (overflow : Sig N) : (fun x => rowsConsistent (st x)) ∈ rowsOutputs cap st overflow :=
  Or.inr (Or.inl rfl)

theorem rows_out_coeff {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n)
    (overflow : Sig N) (j : Fin (min cap n)) (i : Fin n) :
    (fun x => z2b ((rowsPadded cap (st x) j).1 i)) ∈ rowsOutputs cap st overflow :=
  Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨i.castSucc, rfl⟩⟩))

theorem rows_out_rhs {N n : ℕ} (cap : ℕ) (st : (Fin N → Bool) → RowsState n)
    (overflow : Sig N) (j : Fin (min cap n)) :
    (fun x => z2b ((rowsPadded cap (st x) j).2)) ∈ rowsOutputs cap st overflow :=
  Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨Fin.last n, rfl⟩⟩))

theorem rowsPackB {N n : ℕ} {A : Set (Sig N)} (cap : ℕ)
    (st : (Fin N → Bool) → RowsState n)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hst : rowsStateSigs st ⊆ A) :
    Build A (rowsOutputs cap st (fun x => decide (cap < rowsPrefix (st x) n)))
      (32*(n+2)^3) := by
  let threshold := ⋃ t : Fin (n+1), Set.range (rowsThresh st t.val)
  let ov : Sig N := fun x => decide (cap < rowsPrefix (st x) n)
  let jFin (j : Fin (min cap n)) : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
  let sels (j : Fin (min cap n)) : Fin n → Sig N := fun i x => rowsPick (st x) j.val i
  let flags := ⋃ j : Fin (min cap n), Set.range (sels j)
  let B := A ∪ (threshold ∪ flags)
  have hT (t : Fin (n+1)) : Set.range (rowsThresh st t.val) ⊆ threshold :=
    fun _ h => Set.mem_iUnion.mpr ⟨t, h⟩
  have h1 : Build A threshold ((n+1)*(n*((n+2)*4))) := by
    refine finB _ _ (fun t => ?_)
    exact relaxB (rowsThreshB st hfalse htrue hst t.val (by omega))
      le_rfl Set.subset_union_right (Nat.mul_le_mul_right _ (by omega))
  have h2 : Build (A ∪ threshold) flags (min cap n * (n*3)) := by
    refine finB _ _ (fun j => finSigB (sels j) 3 (fun i => ?_))
    exact rowsPickB st i (jFin j) (fun _ h => Or.inl (hst h))
      (fun _ h => Or.inr (hT i.castSucc h))
  have h3 : Build B (rowsPackedSigs cap st) (min cap n * ((n+1)*(2*n))) := by
    refine finB _ _ (fun j => finSigB _ (2*n) (fun c => ?_))
    exact rowsChooseB (sels j) (fun x i => (st x).1 i c) (Or.inl hfalse)
      (fun i => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨i, rfl⟩⟩)))
      (fun i => Or.inl (hst (rowsState_bit st i c)))
  have h4 : Build B {fun x => rowsConsistent (st x)} 1 := notB (Or.inl (hst (Or.inr rfl)))
  have hov : ov ∈ B := by
    by_cases hcap : cap < n
    · let k : Fin (n+2) := ⟨cap+1, by omega⟩
      have he : ov = rowsThresh st n k := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp [ov, rowsThresh, k]
      rw [he]
      exact Or.inr (Or.inl (hT (Fin.last n) ⟨k, rfl⟩))
    · have he : ov = fun _ => false := by
        funext x
        have hn : rowsPrefix (st x) n ≤ n := by
          simpa [rowsPrefix] using
            (Finset.card_filter_le (Finset.univ : Finset (Fin n))
              (fun i => i.val < n ∧ rowsUsed (st x) i = true))
        exact decide_eq_false (by omega)
      rw [he]
      exact Or.inl hfalse
  have h5 : Build B (rowsOutputs cap st ov) (1+min cap n * ((n+1)*(2*n))) := by
    refine relaxB (unionB h4 h3) le_rfl ?_ le_rfl
    intro f hf
    rcases hf with h | h
    · exact Or.inl ((Set.mem_singleton_iff.mp h).symm ▸ hov)
    · exact Or.inr h
  have hb := seq2B (seqB h1 h2) h5
  have hm := min_le_right cap n
  have ha := Nat.mul_le_mul_right (n*3) hm
  have hc := Nat.mul_le_mul_right ((n+1)*(2*n)) hm
  refine relaxB hb le_rfl Set.subset_union_right ?_
  calc
    _ ≤ (n+1)*(n*((n+2)*4)) + n*(n*3) + (1+n*((n+1)*(2*n))) := by omega
    _ ≤ _ := by
      have he : (n+1)*(n*((n+2)*4)) + n*(n*3) + (1+n*((n+1)*(2*n))) +
          (26*n^3+175*n^2+376*n+255) = 32*(n+2)^3 := by ring
      rw [← he]
      omega

theorem rowsB {N q n : ℕ} {A : Set (Sig N)} (cap : ℕ)
    (obs : (Fin N → Bool) → Fin q → Fin n → ZMod 2)
    (wanted : (Fin N → Bool) → Fin q → ZMod 2)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (ho : ∀ i j, (fun x => z2b (obs x i j)) ∈ A)
    (hw : ∀ i, (fun x => z2b (wanted x i)) ∈ A) :
    Build A (rowsOutputs cap (fun x => rowsReduce (obs x) (wanted x))
      (fun x => decide (cap < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (obs x))))))
      (65500*(q+1)*(n+2)^3) := by
  let st : (Fin N → Bool) → RowsState n := fun x => rowsReduce (obs x) (wanted x)
  have h1 := rowsReduceB obs wanted hfalse ho hw
  have h2 := rowsPackB (A := A ∪ rowsStateSigs st) cap st (Or.inl hfalse) (Or.inl htrue)
    Set.subset_union_right
  have hcost : q * (64*(n+2)^2) + 32*(n+2)^3 ≤ 65500*(q+1)*(n+2)^3 := by
    have hn : (n+2)^2 ≤ (n+2)^3 := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      _ ≤ q * (64*(n+2)^3) + 32*(n+2)^3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left q (Nat.mul_le_mul_left 64 hn)) _
      _ = (64*q+32)*(n+2)^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  simpa only [st, rowsPrefix_rank] using
    relaxB (seq2B h1 h2) le_rfl Set.subset_union_right hcost

/-- The allowed signed integer coefficients of a `k`-bit factor. -/
def SignedMonomial (k : ℕ) (z : ℤ) : Prop :=
  z = 0 ∨ ∃ e ≤ k, z = (2 : ℤ)^e ∨ z = -(2 : ℤ)^e

/-- A nonzero flag, a negative flag, and the unsigned exponent. -/
abbrev Mono (N : ℕ) := Sig N × Sig N × ((Fin N → Bool) → ℕ)

def monoSigs {N : ℕ} (w : ℕ) (a : Mono N) : Set (Sig N) :=
  ({a.1} ∪ {a.2.1}) ∪ Set.range (bitsOf w a.2.2)

def monoTerms {N : ℕ} (a : Mono N) : ((Fin N → Bool) → ℕ) × ((Fin N → Bool) → ℕ) :=
  (fun x => if a.1 x && !(a.2.1 x) then 2 ^ a.2.2 x else 0,
   fun x => if a.1 x && a.2.1 x then 2 ^ a.2.2 x else 0)

def monoValue {N : ℕ} (a : Mono N) (x : Fin N → Bool) : ℤ :=
  ((monoTerms a).1 x : ℤ) - (monoTerms a).2 x

theorem monoValue_eq {N : ℕ} (a : Mono N) (x : Fin N → Bool) :
    monoValue a x =
      if a.1 x then (if a.2.1 x then -(2 : ℤ)^a.2.2 x else (2 : ℤ)^a.2.2 x) else 0 := by
  cases ha : a.1 x <;> cases hn : a.2.1 x <;> simp [monoValue, monoTerms, ha, hn]

def monoMagnitude (f g : ℕ) : ℕ := ((f : ℤ) - g).natAbs

private theorem monoMagnitude_eq (f g : ℕ) :
    monoMagnitude f g = if f < g then g - f else f - g := by
  unfold monoMagnitude
  split
  next h =>
    have he : (f : ℤ) - g = -((g - f : ℕ) : ℤ) := by omega
    simp [he]
  next h =>
    have he : (f : ℤ) - g = ((f - g : ℕ) : ℤ) := by omega
    simp [he]

private theorem monoMagnitude_cases {k f g : ℕ} (h : SignedMonomial k ((f : ℤ) - g)) :
    monoMagnitude f g = 0 ∨ ∃ e ≤ k, monoMagnitude f g = 2 ^ e := by
  have htwo : (2 : ℤ).natAbs = (2 : ℕ) := by decide
  rcases h with h | ⟨e, he, h | h⟩
  · exact Or.inl (by simp [monoMagnitude, h])
  · refine Or.inr ⟨e, he, ?_⟩
    simpa only [monoMagnitude, h, htwo] using Int.natAbs_pow 2 e
  · refine Or.inr ⟨e, he, ?_⟩
    simpa only [monoMagnitude, h, Int.natAbs_neg, htwo] using Int.natAbs_pow 2 e

def monoCompress {N : ℕ} (F G : (Fin N → Bool) → ℕ) : Mono N :=
  (fun x => decide (monoMagnitude (F x) (G x) ≠ 0),
   fun x => decide (F x < G x),
   fun x => Nat.log2 (monoMagnitude (F x) (G x)))

theorem monoCompress_exp_le {N k : ℕ} (F G : (Fin N → Bool) → ℕ)
    (h : ∀ x, SignedMonomial k ((F x : ℤ) - G x)) (x : Fin N → Bool) :
    (monoCompress F G).2.2 x ≤ k := by
  rcases monoMagnitude_cases (h x) with hz | ⟨e, he, hm⟩
  · simp [monoCompress, hz, Nat.log2_zero]
  · simpa [monoCompress, hm, Nat.log2_two_pow] using he

theorem monoCompress_spec {N k : ℕ} (F G : (Fin N → Bool) → ℕ)
    (h : ∀ x, SignedMonomial k ((F x : ℤ) - G x)) (x : Fin N → Bool) :
    monoValue (monoCompress F G) x = (F x : ℤ) - G x := by
  have hs : (if F x < G x then -(monoMagnitude (F x) (G x) : ℤ)
      else (monoMagnitude (F x) (G x) : ℤ)) = (F x : ℤ) - G x := by
    rw [monoMagnitude_eq]
    by_cases hlt : F x < G x <;> simp only [hlt, ite_true, ite_false] <;> omega
  rw [← hs, monoValue_eq]
  rcases monoMagnitude_cases (h x) with hz | ⟨e, _, hm⟩
  · simp [monoCompress, hz]
  · by_cases hlt : F x < G x <;>
      simp [monoCompress, hm, hlt, Nat.log2_two_pow]

-- Add at modulus `2^L`, retaining the extra carry bit. The low bits are the
-- modular difference and the extra bit is set exactly for a nonnegative difference.
private def monoResid {N : ℕ} (L : ℕ) (F G : (Fin N → Bool) → ℕ) :=
  fun x => 2 ^ L + F x - G x

private theorem monoResidB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
    (F G : (Fin N → Bool) → ℕ) (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A) (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hFb : ∀ x, F x < 2 ^ L) (hGb : ∀ x, G x < 2 ^ L) :
    Build A (Set.range (bitsOf (L + 1) (monoResid L F G))) (19 * (L + 1)) := by
  let C : (Fin N → Bool) → ℕ := fun x => 2 ^ L - 1 - G x
  let U : (Fin N → Bool) → ℕ := fun _ => 1
  let V : (Fin N → Bool) → ℕ := fun x => C x + U x
  have hC : Build A (Set.range (bitsOf (L + 1) C)) ((L + 1) * 1) := by
    apply finSigB (c := 1)
    intro j
    by_cases hj : j.val < L
    · have he : bitsOf (L + 1) C j = fun x => !(bitsOf L G ⟨j.val, hj⟩ x) := by
        funext x
        exact testBit_two_pow_sub_one_sub (hGb x) hj
      rw [he]
      exact notB (hG ⟨j.val, hj⟩)
    · have hj' : j.val = L := by have := j.isLt; omega
      have he : bitsOf (L + 1) C j = fun _ => false := by
        funext x
        apply Nat.testBit_lt_two_pow
        rw [hj']
        have hp := Nat.two_pow_pos L
        dsimp [C]
        omega
      rw [he]
      exact relaxB (idleB (Set.singleton_subset_iff.mpr hfalse)) le_rfl
        Set.subset_union_right (by omega)
  have hU : ∀ j : Fin (L + 1), bitsOf (L + 1) U j ∈ A := by
    intro j
    have he : bitsOf (L + 1) U j = fun _ => decide (0 = j.val) := by
      funext x
      simpa only [bitsOf, U, pow_zero] using (Nat.testBit_two_pow (n := 0) (m := j.val))
    rw [he]
    by_cases hz : 0 = j.val <;> simp [hz, hfalse, htrue]
  have hF' : ∀ j : Fin (L + 1), bitsOf (L + 1) F j ∈ A := by
    intro j
    by_cases hj : j.val < L
    · exact hF ⟨j.val, hj⟩
    · have hj' : j.val = L := by have := j.isLt; omega
      have he : bitsOf (L + 1) F j = fun _ => false := by
        funext x
        change (F x).testBit j.val = false
        rw [hj']
        exact Nat.testBit_lt_two_pow (hFb x)
      rw [he]
      exact hfalse
  have hV : Build (A ∪ Set.range (bitsOf (L + 1) C))
      (Set.range (bitsOf (L + 1) V)) (9 * (L + 1)) :=
    sumTwoB (L + 1) C U (Or.inl hfalse) (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (hU j))
  have hr : Build ((A ∪ Set.range (bitsOf (L + 1) C)) ∪ Set.range (bitsOf (L + 1) V))
      (Set.range (bitsOf (L + 1) (fun x => F x + V x))) (9 * (L + 1)) :=
    sumTwoB (L + 1) F V (Or.inl (Or.inl hfalse))
      (fun j => Or.inl (Or.inl (hF' j))) (fun j => Or.inr ⟨j, rfl⟩)
  have he : (fun x => F x + V x) = monoResid L F G := by
    funext x
    have hg := hGb x
    dsimp [V, C, U, monoResid]
    omega
  rw [he] at hr
  exact relaxB (transB (extB hC) (transB (extB hV) hr)) le_rfl
    Set.subset_union_right (by omega)

private theorem monoResid_neg {N : ℕ} {L : ℕ} (F G : (Fin N → Bool) → ℕ)
    (hFb : ∀ x, F x < 2 ^ L) (x : Fin N → Bool) :
    (!((monoResid L F G x).testBit L)) = decide (F x < G x) := by
  by_cases h : F x < G x
  · have hd : monoResid L F G x < 2 ^ L := by
      have hp := Nat.two_pow_pos L
      unfold monoResid
      omega
    simp [Nat.testBit_lt_two_pow hd, h]
  · have hd : monoResid L F G x = 2 ^ L + (F x - G x) := Nat.add_sub_assoc (Nat.le_of_not_gt h) _
    have hb : F x - G x < 2 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) (hFb x)
    simp [hd, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb, h]

private theorem monoMagnitude_bit {N : ℕ} {L : ℕ} (F G : (Fin N → Bool) → ℕ)
    (x : Fin N → Bool) (j : Fin L) :
    (monoMagnitude (F x) (G x)).testBit j.val =
      if (monoCompress F G).2.1 x then (monoResid L G F x).testBit j.val
      else (monoResid L F G x).testBit j.val := by
  rw [monoMagnitude_eq]
  by_cases h : F x < G x
  · have hd : monoResid L G F x = 2 ^ L + (G x - F x) := Nat.add_sub_assoc h.le _
    simp [monoCompress, h, hd, testBit_add_two_pow_of_lt j.isLt]
  · have hd : monoResid L F G x = 2 ^ L + (F x - G x) := Nat.add_sub_assoc (Nat.le_of_not_gt h) _
    simp [monoCompress, h, hd, testBit_add_two_pow_of_lt j.isLt]

private def monoSelect {N k : ℕ} (M : (Fin N → Bool) → ℕ) (P : Fin (k + 1) → Bool) : Sig N :=
  fun x => (((List.finRange (k + 1)).filter P).map (bitsOf (k + 1) M)).any (fun f => f x)

private theorem monoSelectB {N k : ℕ} {A : Set (Sig N)} (M : (Fin N → Bool) → ℕ)
    (P : Fin (k + 1) → Bool) (hf : (fun _ => false) ∈ A)
    (hM : ∀ j : Fin (k + 1), bitsOf (k + 1) M j ∈ A) :
    Build A {monoSelect M P} (k + 1) := by
  have hb := orListB (((List.finRange (k + 1)).filter P).map (bitsOf (k + 1) M))
    (by intro f hf; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf; exact hM j) hf
  refine relaxB hb le_rfl Set.subset_union_right ?_
  simpa using List.length_filter_le P (List.finRange (k + 1))

private theorem monoSelect_pow {N k e : ℕ} (M : (Fin N → Bool) → ℕ)
    (P : Fin (k + 1) → Bool) (x : Fin N → Bool) (he : e ≤ k) (hm : M x = 2 ^ e) :
    monoSelect M P x = P ⟨e, by omega⟩ := by
  apply Bool.eq_iff_iff.mpr
  simp only [monoSelect, List.any_map, Function.comp_def, List.any_eq_true, List.mem_filter,
    List.mem_finRange, true_and, bitsOf, hm, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hie⟩
    have hh : i = ⟨e, by omega⟩ := Fin.ext hie.symm
    simpa [hh] using hi
  · intro hp
    exact ⟨⟨e, by omega⟩, hp, rfl⟩

private theorem monoSelect_zero {N k : ℕ} (M : (Fin N → Bool) → ℕ)
    (P : Fin (k + 1) → Bool) (x : Fin N → Bool) (hm : M x = 0) :
    monoSelect M P x = false := by
  apply Bool.eq_iff_iff.mpr
  simp [monoSelect, List.any_map, Function.comp_def, bitsOf, hm]

theorem monoCompressB {N k : ℕ} {A : Set (Sig N)} (w : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hF : ∀ j : Fin (k + 1), bitsOf (k + 1) F j ∈ A)
    (hG : ∀ j : Fin (k + 1), bitsOf (k + 1) G j ∈ A)
    (hFb : ∀ x, F x < 2 ^ (k + 1)) (hGb : ∀ x, G x < 2 ^ (k + 1))
    (hm : ∀ x, SignedMonomial k ((F x : ℤ) - G x)) :
    Build A (monoSigs w (monoCompress F G)) (100 * (k + 1)^2) := by
  let L := k + 1
  let D := monoResid L F G
  let E := monoResid L G F
  let a := monoCompress F G
  let M := fun x => monoMagnitude (F x) (G x)
  let B := Set.range (bitsOf (L + 1) D) ∪ Set.range (bitsOf (L + 1) E)
  let A₁ := (A ∪ B) ∪ {a.2.1}
  let A₂ := A₁ ∪ Set.range (bitsOf L M)
  have hB : Build A B (19 * (L + 1) + 19 * (L + 1)) :=
    unionB (monoResidB L F G hf ht hF hG hFb hGb) (monoResidB L G F hf ht hG hF hGb hFb)
  have hn : Build (A ∪ B) {a.2.1} 1 := by
    have he : a.2.1 = fun x => !(bitsOf (L + 1) D (Fin.last L) x) := by
      funext x
      exact (monoResid_neg F G hFb x).symm
    rw [he]
    exact notB (Or.inr (Or.inl ⟨Fin.last L, rfl⟩))
  have hM : Build A₁ (Set.range (bitsOf L M)) (L * 4) := by
    apply finSigB
    intro j
    have he : bitsOf L M j = fun x => if a.2.1 x then
        bitsOf (L + 1) E j.castSucc x else bitsOf (L + 1) D j.castSucc x := by
      funext x
      exact monoMagnitude_bit F G x j
    rw [he]
    exact iteB (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨j.castSucc, rfl⟩)))
      (Or.inl (Or.inr (Or.inl ⟨j.castSucc, rfl⟩)))
  have hz : (fun _ => false) ∈ A₂ := Or.inl (Or.inl (Or.inl hf))
  have hMb (j : Fin L) : bitsOf L M j ∈ A₂ := Or.inr ⟨j, rfl⟩
  have ho : Build A₂ {a.1} L := by
    have he : a.1 = monoSelect M (fun _ : Fin (k + 1) => true) := by
      funext x
      rcases monoMagnitude_cases (hm x) with h0 | ⟨e, he, hp⟩
      · rw [monoSelect_zero M _ x h0]
        simp [a, monoCompress, h0]
      · rw [monoSelect_pow M _ x he hp]
        simp [a, monoCompress, hp]
    rw [he]
    exact monoSelectB M _ hz hMb
  have he : Build A₂ (Set.range (bitsOf L a.2.2)) (L * L) := by
    apply finSigB
    intro j
    have hbit : bitsOf L a.2.2 j = monoSelect M (fun i : Fin (k + 1) => i.val.testBit j.val) := by
      funext x
      rcases monoMagnitude_cases (hm x) with h0 | ⟨e, he, hp⟩
      · rw [monoSelect_zero M _ x h0]
        simp [bitsOf, a, monoCompress, h0, Nat.log2_zero]
      · rw [monoSelect_pow M _ x he hp]
        simp [bitsOf, a, monoCompress, hp, Nat.log2_two_pow]
    rw [hbit]
    exact monoSelectB M _ hz hMb
  have hpre : Build A A₂ ((19 * (L + 1) + 19 * (L + 1)) + (1 + L * 4)) :=
    transB (extB hB) (transB (extB hn) (extB hM))
  refine relaxB (seqB hpre (relaxB (unionB ho he) Set.subset_union_right
    Set.subset_union_right le_rfl)) le_rfl ?_ ?_
  · rintro f ((hf' | hf') | ⟨j, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl hf'))
    · exact Or.inr (Or.inl (Or.inl (Or.inr hf')))
    · by_cases hj : j.val < L
      · exact Or.inr (Or.inr (Or.inr ⟨(⟨j.val, hj⟩ : Fin L), rfl⟩))
      · have hzz : bitsOf w a.2.2 j = fun _ => false := by
          funext x
          apply Nat.testBit_lt_two_pow
          exact lt_of_le_of_lt ((monoCompress_exp_le F G hm x).trans (show k ≤ j.val by omega))
            (Nat.lt_two_pow_self (n := j.val))
        rw [hzz]
        exact Or.inl hf
  · dsimp [L]
    nlinarith [Nat.zero_le k, Nat.zero_le (k*k)]

/-- Multiply exponents additively, negative flags by parity, and nonzero flags by conjunction.
The extra flags represent a multiplier in `{-1, 0, 1}`. -/
def monoCombine {N : ℕ} (ok neg : Sig N) (fs : List (Mono N)) : Mono N :=
  (fun x => (fs.map Prod.fst ++ [ok]).all (fun f => f x),
   fun x => xorList ((fs.map (fun a => a.2.1) ++ [neg]).map (fun f => f x)),
   sumListVal (fs.map (fun a => a.2.2)))

private theorem monoValue_mul {N : ℕ} (a b : Mono N) (x : Fin N → Bool) :
    monoValue (fun y => a.1 y && b.1 y, fun y => xor (a.2.1 y) (b.2.1 y),
      fun y => a.2.2 y + b.2.2 y) x = monoValue a x * monoValue b x := by
  simp only [monoValue_eq]
  cases ha : a.1 x <;> cases hb : b.1 x <;> cases hsa : a.2.1 x <;> cases hsb : b.2.1 x <;>
    simp [*, pow_add]

theorem monoProduct_spec {N : ℕ} (ok neg : Sig N) (fs : List (Mono N)) (x : Fin N → Bool) :
    (((monoTerms (monoCombine ok neg fs)).1 x : ℕ) : ℤ) - (monoTerms (monoCombine ok neg fs)).2 x =
      (if ok x then (if neg x then -1 else 1) else 0) * (fs.map (fun a => monoValue a x)).prod := by
  change monoValue (monoCombine ok neg fs) x = _
  induction fs with
  | nil =>
    cases ho : ok x <;> cases hn : neg x <;>
      simp [monoValue_eq, monoCombine, xorList, sumListVal, ho, hn]
  | cons a fs ih =>
    have hs : monoValue (monoCombine ok neg (a :: fs)) x =
        monoValue a x * monoValue (monoCombine ok neg fs) x :=
      monoValue_mul a (monoCombine ok neg fs) x
    rw [hs, ih, List.map_cons, List.prod_cons]
    ring

theorem monoCombine_exp_le {N k : ℕ} (ok neg : Sig N) (fs : List (Mono N))
    (h : ∀ a ∈ fs, ∀ x, a.2.2 x ≤ k) (x : Fin N → Bool) :
    (monoCombine ok neg fs).2.2 x ≤ fs.length * k := by
  induction fs with
  | nil => simp [monoCombine, sumListVal]
  | cons a fs ih =>
    have ha := h a List.mem_cons_self x
    have hs := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    change a.2.2 x + (monoCombine ok neg fs).2.2 x ≤ (fs.length + 1) * k
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem monoCombineB {N : ℕ} {A : Set (Sig N)} (w : ℕ) (ok neg : Sig N) (fs : List (Mono N))
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hok : ok ∈ A) (hneg : neg ∈ A) (hfs : ∀ a ∈ fs, monoSigs w a ⊆ A) :
    Build A (monoSigs w (monoCombine ok neg fs)) (fs.length * (9 * w + 5) + 5) := by
  have ho := andListB (fs.map Prod.fst ++ [ok]) (A := A) (fun f h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact hfs a ha (Or.inl (Or.inl rfl))
    · rw [List.mem_singleton.mp h]; exact hok) ht
  have hn := xorListB (fs.map (fun a => a.2.1) ++ [neg]) (A := A) (fun f h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact hfs a ha (Or.inl (Or.inr rfl))
    · rw [List.mem_singleton.mp h]; exact hneg) hf
  have he := sumListB w hf (fs.map (fun a => a.2.2)) (fun F h j => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact hfs a ha (Or.inr ⟨j, rfl⟩))
  refine relaxB (unionB (unionB ho hn) he) le_rfl Set.subset_union_right ?_
  simp [Nat.mul_add]
  omega

private theorem monoEqB {N : ℕ} {A : Set (Sig N)} (w c : ℕ) (F : (Fin N → Bool) → ℕ)
    (ht : (fun _ => true) ∈ A) (hbits : ∀ j : Fin w, bitsOf w F j ∈ A)
    (hF : ∀ x, F x < 2 ^ w) (hc : c < 2 ^ w) :
    Build A {fun x => decide (F x = c)} (2 * w) := by
  let lit : Fin w → Sig N := fun j => if c.testBit j.val then bitsOf w F j
    else fun x => !(bitsOf w F j x)
  have hb : Build A (Set.range lit) (w * 1) := by
    apply finSigB
    intro j
    by_cases hj : c.testBit j.val = true
    · simp only [lit, hj, ite_true]
      exact relaxB (idleB (Set.singleton_subset_iff.mpr (hbits j))) le_rfl
        Set.subset_union_right (by omega)
    · cases he : c.testBit j.val
      · simpa [lit, he] using notB (hbits j)
      · exact (hj he).elim
  let U := (List.finRange w).map lit
  have hall : Build (A ∪ Set.range lit) {fun x => U.all (fun f => f x)} U.length :=
    andListB U (by intro f hf; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨j, rfl⟩)
      (Or.inl ht)
  have hval : (fun x => U.all (fun f => f x)) = fun x => decide (F x = c) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [U, List.all_map, Function.comp_def, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq]
    have hlit (j : Fin w) : lit j x = true ↔ (F x).testBit j.val = c.testBit j.val := by
      cases hj : c.testBit j.val <;> cases hFj : (F x).testBit j.val <;>
        simp [lit, bitsOf, hj, hFj]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < w
      · exact (hlit ⟨j, hj⟩).mp (h ⟨j, hj⟩)
      · have hpow : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow ((hF x).trans_le hpow), Nat.testBit_lt_two_pow (hc.trans_le hpow)]
    · intro h j
      exact (hlit j).mpr (by rw [h])
  rw [hval] at hall
  exact relaxB (seq2B hb hall) le_rfl Set.subset_union_right (by simp [U]; omega)

private theorem monoDecode_bit {N : ℕ} (a : Mono N) (b : Bool) (j : ℕ) (x : Fin N → Bool) :
    ((if b then (monoTerms a).2 else (monoTerms a).1) x).testBit j =
      ((a.1 x && (if b then a.2.1 x else !(a.2.1 x))) && decide (a.2.2 x = j)) := by
  cases b <;> cases ho : a.1 x <;> cases hn : a.2.1 x <;>
    simp [monoTerms, ho, hn, Nat.testBit_two_pow]

private theorem monoDecodeB {N : ℕ} {A : Set (Sig N)} (w countBits length : ℕ) (a : Mono N)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hs : monoSigs w a ⊆ A) (ha : ∀ x, a.2.2 x ≤ countBits) (hc : countBits < 2 ^ w)
    (b : Bool) :
    Build A (Set.range (bitsOf length (if b then (monoTerms a).2 else (monoTerms a).1)))
      (2 + length * (2 * w + 1)) := by
  let tag : Sig N := fun x => a.1 x && (if b then a.2.1 x else !(a.2.1 x))
  have ho : a.1 ∈ A := hs (Or.inl (Or.inl rfl))
  have hn : a.2.1 ∈ A := hs (Or.inl (Or.inr rfl))
  have htag : Build A {tag} 2 := by
    cases b
    · let n : Sig N := fun x => !(a.2.1 x)
      have h₁ : Build A {n} 1 := notB hn
      have h₂ : Build (A ∪ {n}) {tag} 1 := andB (Or.inl ho) (Or.inr rfl)
      exact seq2B h₁ h₂
    · exact relaxB (andB ho hn) le_rfl Set.subset_union_right (by omega)
  have hbits : Build (A ∪ {tag})
      (Set.range (bitsOf length (if b then (monoTerms a).2 else (monoTerms a).1)))
      (length * (2 * w + 1)) := by
    apply finSigB
    intro j
    have hbit : bitsOf length (if b then (monoTerms a).2 else (monoTerms a).1) j =
        fun x => tag x && decide (a.2.2 x = j.val) := by
      funext x
      exact monoDecode_bit a b j.val x
    rw [hbit]
    by_cases hj : j.val ≤ countBits
    · let eq : Sig N := fun x => decide (a.2.2 x = j.val)
      have h₁ : Build (A ∪ {tag}) {eq} (2 * w) :=
        monoEqB w j.val a.2.2 (Or.inl ht) (fun i => Or.inl (hs (Or.inr ⟨i, rfl⟩)))
          (fun x => (ha x).trans_lt hc) (hj.trans_lt hc)
      have h₂ : Build ((A ∪ {tag}) ∪ {eq}) {fun x => tag x && eq x} 1 :=
        andB (Or.inl (Or.inr rfl)) (Or.inr rfl)
      exact seq2B h₁ h₂
    · have hz : (fun x => tag x && decide (a.2.2 x = j.val)) = fun _ => false := by
        funext x
        have hh := ha x
        have hne : a.2.2 x ≠ j.val := by omega
        simp [hne]
      rw [hz]
      exact relaxB (idleB (Set.singleton_subset_iff.mpr (Or.inl hf))) le_rfl
        Set.subset_union_right (Nat.zero_le _)
  exact seq2B htag hbits

/-- Decode the product exponent only at indices at most `countBits`; higher output bits are zero. -/
theorem monoProductB {N : ℕ} {A : Set (Sig N)} (countBits length : ℕ)
    (ok neg : Sig N) (fs : List (Mono N))
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hok : ok ∈ A) (hneg : neg ∈ A)
    (hfs : ∀ a ∈ fs, monoSigs (Nat.log2 countBits + 1) a ⊆ A)
    (he : ∀ x, (monoCombine ok neg fs).2.2 x ≤ countBits)
    (hL : countBits < length) :
    Build A (Set.range (bitsOf length (monoTerms (monoCombine ok neg fs)).1) ∪
      Set.range (bitsOf length (monoTerms (monoCombine ok neg fs)).2))
      (fs.length * (9 * (Nat.log2 countBits + 1) + 5) + 100 * length^2) := by
  let w := Nat.log2 countBits + 1
  let a := monoCombine ok neg fs
  have hc : countBits < 2 ^ w := Nat.lt_log2_self
  have hw : w ≤ length := by
    dsimp [w]
    have h := Nat.log2_le_self countBits
    omega
  have h₁ : Build A (monoSigs w a) (fs.length * (9*w + 5) + 5) :=
    monoCombineB w ok neg fs hf ht hok hneg hfs
  have h₂ := monoDecodeB w countBits length a (Or.inl hf : (fun _ => false) ∈ A ∪ monoSigs w a)
    (Or.inl ht) Set.subset_union_right he hc false
  have h₃ := monoDecodeB w countBits length a (Or.inl hf : (fun _ => false) ∈ A ∪ monoSigs w a)
    (Or.inl ht) Set.subset_union_right he hc true
  refine relaxB (seq2B h₁ (unionB h₂ h₃)) le_rfl Set.subset_union_right ?_
  change fs.length * (9*w + 5) + 5 + ((2 + length * (2*w + 1)) + (2 + length * (2*w + 1))) ≤
    fs.length * (9*w + 5) + 100 * length^2
  have hz := Nat.mul_le_mul_left length hw
  have hpos : 1 ≤ length := by omega
  have hsq := Nat.mul_le_mul_right length hpos
  nlinarith

/-- Compress and multiply a list of bounded positive/negative count pairs. -/
theorem monoCountProductB {N k : ℕ} {A : Set (Sig N)} (countBits length : ℕ)
    (ok neg : Sig N) (fs : List (((Fin N → Bool) → ℕ) × ((Fin N → Bool) → ℕ)))
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hok : ok ∈ A) (hneg : neg ∈ A)
    (hbits : ∀ a ∈ fs, ∀ j : Fin (k+1), bitsOf (k+1) a.1 j ∈ A ∧ bitsOf (k+1) a.2 j ∈ A)
    (hb : ∀ a ∈ fs, ∀ x, a.1 x < 2^(k+1) ∧ a.2 x < 2^(k+1))
    (hm : ∀ a ∈ fs, ∀ x, SignedMonomial k ((a.1 x : ℤ) - a.2 x))
    (he : fs.length * k ≤ countBits) (hL : countBits < length) :
    let a := monoCombine ok neg (fs.map (fun f => monoCompress f.1 f.2))
    Build A (Set.range (bitsOf length (monoTerms a).1) ∪ Set.range (bitsOf length (monoTerms a).2))
      (fs.length * (100*(k+1)^2 + (9*(Nat.log2 countBits+1)+5)) + 100*length^2) := by
  let w := Nat.log2 countBits + 1
  let f := fun a : ((Fin N → Bool) → ℕ) × ((Fin N → Bool) → ℕ) => monoCompress a.1 a.2
  let B := ⋃ a ∈ fs, monoSigs w (f a)
  have h₁ : Build A B (fs.length * (100*(k+1)^2)) :=
    listB (fun a => monoSigs w (f a)) (100*(k+1)^2) fs (fun a ha =>
      monoCompressB w a.1 a.2 hf ht (fun j => (hbits a ha j).1) (fun j => (hbits a ha j).2)
        (fun x => (hb a ha x).1) (fun x => (hb a ha x).2) (hm a ha))
  have hmem : ∀ a ∈ fs.map f, monoSigs w a ⊆ A ∪ B := by
    intro a ha g hg
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb', hg⟩⟩)
  have hE : ∀ a ∈ fs.map f, ∀ x, a.2.2 x ≤ k := by
    intro a ha x
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha
    exact monoCompress_exp_le b.1 b.2 (hm b hb') x
  have hex (x : Fin N → Bool) : (monoCombine ok neg (fs.map f)).2.2 x ≤ countBits :=
    (monoCombine_exp_le ok neg (fs.map f) hE x).trans (by simpa using he)
  have h₂ := monoProductB countBits length ok neg (fs.map f)
    (Or.inl hf : (fun _ => false) ∈ A ∪ B) (Or.inl ht) (Or.inl hok) (Or.inl hneg) hmem hex hL
  refine relaxB (seq2B h₁ h₂) le_rfl Set.subset_union_right ?_
  simp only [List.length_map, Nat.mul_add, Nat.add_assoc]
  exact le_rfl

theorem monoCountProduct_spec {N k : ℕ} (ok neg : Sig N)
    (fs : List (((Fin N → Bool) → ℕ) × ((Fin N → Bool) → ℕ)))
    (hm : ∀ a ∈ fs, ∀ x, SignedMonomial k ((a.1 x : ℤ) - a.2 x)) (x : Fin N → Bool) :
    let a := monoCombine ok neg (fs.map (fun f => monoCompress f.1 f.2))
    ((monoTerms a).1 x : ℤ) - (monoTerms a).2 x =
      (if ok x then (if neg x then -1 else 1) else 0) *
        (fs.map (fun f => (f.1 x : ℤ) - f.2 x)).prod := by
  dsimp only
  have hmap : ((fs.map (fun f => monoCompress f.1 f.2)).map (fun a => monoValue a x)) =
      fs.map (fun f => (f.1 x : ℤ) - f.2 x) := by
    rw [List.map_map]
    exact List.map_congr_left (fun a ha => monoCompress_spec a.1 a.2 (hm a ha) x)
  rw [monoProduct_spec, hmap]

def initAmount (col : Bool) : ℕ := if col then 3 else 1
def gapAmount (col : Bool) : ℕ := if col then 2 else 1
def stepAmount (col : Bool) (t : ℕ) : ℕ := if col then 3*(t+1)+1 else 2*t

lemma gapAmount_le (col : Bool) : gapAmount col ≤ 2 := by cases col <;> decide

def stF {k r : ℕ} (hk : 0 < k) (col : Bool) (data : V k × SeqV r k) (key : V k)
    (time : Fin (r+1)) : V k :=
  ((List.finRange r).take time.val).foldl (fun v tick =>
    layerF hk (gapAmount col) v + rotF hk (stepAmount col tick.val) key + data.2 tick)
    (rotF hk (initAmount col) key + data.1)

def hitF {k r s : ℕ} (hk : 0 < k) (col : Bool) (raw : V k) (δ : Fin s → V k)
    (path : Fin (r+1) → Fin s → V k) (test target : V k) (c : SeqV r k) : ℕ :=
  ((Finset.univ : Finset (V k)).filter (fun name =>
    (∀ t p, stF hk col (name,c) (raw+δ p) t - stF hk col (name,c) raw t = path t p) ∧
    (∀ j, test j ≠ 0 → stF hk col (name,c) raw (Fin.last r) j = target j))).card

def goodFirst {k r s : ℕ} (hk : 0 < k) (col : Bool) (δ : Fin s → V k)
    (path : Fin (r+1) → Fin s → V k) : Bool :=
  (List.finRange s).all (fun p => (List.finRange k).all (fun j =>
    !z2b (path 0 p j + rotF hk (initAmount col) (δ p) j)))

lemma goodFirst_iff {k r s : ℕ} (hk : 0 < k) (col : Bool) (δ : Fin s → V k)
    (path : Fin (r+1) → Fin s → V k) :
    goodFirst hk col δ path = true ↔ ∀ p, path 0 p = rotF hk (initAmount col) (δ p) := by
  simp only [goodFirst, List.all_eq_true, List.mem_finRange, true_implies, negZ2_true,
    CharTwo.add_eq_zero, funext_iff]

lemma goodFirstB {N k r s : ℕ} {A : Set (Sig N)} (hk : 0 < k) (col : Bool)
    (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (ht : (fun _ => true) ∈ A) (hd : ∀ p j, bSig (fun x => δ x p j) ∈ A)
    (hp : ∀ t p j, bSig (fun x => path x t p j) ∈ A) :
    Build A {fun x => goodFirst hk col (δ x) (path x)} (s*(6*k+1)) := by
  let f : Fin s → Fin k → Sig N := fun p j x => !z2b (path x 0 p j + rotF hk (initAmount col) (δ x p) j)
  let g : Fin s → Sig N := fun p x => (List.finRange k).all (fun j => f p j x)
  have hout (p : Fin s) : Build A {g p} (6*k) := by
    have h := finSigB (f p) 5 (fun j => oneZero (oneAdd (oneMem (hp 0 p j)) (oneMem (hd p _))))
    have h' := allFinB (A := A ∪ Set.range (f p)) (f p) (Or.inl ht)
      (fun j => Or.inr (Set.mem_range.mpr ⟨j,rfl⟩))
    exact relaxB (seq2B h h') le_rfl Set.subset_union_right (by omega)
  have h := finSigB g (6*k) hout
  have h' := allFinB (A := A ∪ Set.range g) g (Or.inl ht)
    (fun p => Or.inr (Set.mem_range.mpr ⟨p,rfl⟩))
  exact relaxB (seq2B h h') le_rfl Set.subset_union_right (by rw [Nat.mul_add, Nat.mul_one])

abbrev CountPair (N : ℕ) := (Inp N → ℕ) × (Inp N → ℕ)

def pairBits {N : ℕ} (L : ℕ) (P : CountPair N) : Set (Sig N) :=
  Set.range (bitsOf L P.1) ∪ Set.range (bitsOf L P.2)

noncomputable def roundPair {N k r s : ℕ} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (freq : Inp N → SeqV r k) (t : Fin r) : CountPair N :=
  let C := factorCounts hk
    (gateOkay hk (gapAmount col) (gapAmount_le col)
      (fun x p => rotF hk (stepAmount col t.val) (δ x p)) (fun x => path x t.castSucc) (fun x => path x t.succ))
    (gatePhase hk (gapAmount col) (gapAmount_le col) (fun x => prevFreq (freq x) t.val)
      (fun x => freq x t) (fun x => rotF hk (stepAmount col t.val) (raw x)))
  (C false, C true)

noncomputable def terminalPair {N k r : ℕ} (hk : 0 < k) (test target : Inp N → V k)
    (freq : Inp N → SeqV r k) : CountPair N :=
  let C := factorCounts hk (gateTerminalOK test target) (gateTerminalPhase (fun x => prevFreq (freq x) r))
  (C false, C true)

noncomputable def countPairs {N k r s : ℕ} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (test target : Inp N → V k) (freq : Inp N → SeqV r k) : Fin (r+1) → CountPair N :=
  Fin.lastCases (terminalPair hk test target freq) (roundPair hk col raw δ path freq)

lemma prevFreqSignal {N k r : ℕ} {A : Set (Sig N)} (F : Inp N → SeqV r k)
    (hfalse : (fun _ => false) ∈ A) (hf : ∀ t j, bSig (fun x => F x t j) ∈ A) (t : ℕ) (j : Fin k) :
    bSig (fun x => prevFreq (F x) t j) ∈ A := by
  by_cases ht : 0 < t ∧ t ≤ r
  · simpa only [prevFreq, dif_pos ht] using hf ⟨t-1,by omega⟩ j
  · change (fun x => z2b (prevFreq (F x) t j)) ∈ A
    simpa only [prevFreq, dif_neg ht, Pi.zero_apply, z2b_zero] using hfalse

lemma roundPairB {N k r s : ℕ} {A : Set (Sig N)} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (freq : Inp N → SeqV r k) (t : Fin r)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hr : ∀ j, bSig (fun x => raw x j) ∈ A) (hd : ∀ p j, bSig (fun x => δ x p j) ∈ A)
    (hp : ∀ t p j, bSig (fun x => path x t p j) ∈ A) (hf : ∀ t j, bSig (fun x => freq x t j) ∈ A) :
    Build A (pairBits (k+1) (roundPair hk col raw δ path freq t))
      (16384*k*(s+1)+160000*(k+1)^2) := by
  let off (x : Inp N) (p : Fin s) := rotF hk (stepAmount col t.val) (δ x p)
  let prev (x : Inp N) := prevFreq (freq x) t.val
  let now (x : Inp N) := freq x t
  let u (x : Inp N) := rotF hk (stepAmount col t.val) (raw x)
  let d₀ (x : Inp N) := path x t.castSucc
  let d₁ (x : Inp N) := path x t.succ
  have H := gateRoundB (A := A) hk (gapAmount col) (gapAmount_le col) off d₀ d₁ prev now u
    hfalse htrue (fun p j => hd p _) (hp t.castSucc) (hp t.succ) (prevFreqSignal freq hfalse hf t.val)
    (hf t) (fun j => hr _)
  have G := factorCountsB hk (gateOkay hk (gapAmount col) (gapAmount_le col) off d₀ d₁)
    (gatePhase hk (gapAmount col) (gapAmount_le col) prev now u) hfalse htrue
  refine relaxB (seq2B H G) le_rfl ?_ le_rfl
  rintro _ (⟨j,rfl⟩ | ⟨j,rfl⟩)
  · exact Or.inr ⟨false,j,rfl⟩
  · exact Or.inr ⟨true,j,rfl⟩

lemma terminalPairB {N k r : ℕ} {A : Set (Sig N)} (hk : 0 < k) (test target : Inp N → V k)
    (freq : Inp N → SeqV r k) (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (htest : ∀ j, bSig (fun x => test x j) ∈ A) (htar : ∀ j, bSig (fun x => target x j) ∈ A)
    (hf : ∀ t j, bSig (fun x => freq x t j) ∈ A) :
    Build A (pairBits (k+1) (terminalPair hk test target freq)) (16384*k+160000*(k+1)^2) := by
  let last (x : Inp N) := prevFreq (freq x) r
  have H := gateTerminalB (A := A) test target last hfalse htrue htest htar (prevFreqSignal freq hfalse hf r)
  have G := factorCountsB hk (gateTerminalOK test target) (gateTerminalPhase last) hfalse htrue
  refine relaxB (seq2B H G) le_rfl ?_ le_rfl
  rintro _ (⟨j,rfl⟩ | ⟨j,rfl⟩)
  · exact Or.inr ⟨false,j,rfl⟩
  · exact Or.inr ⟨true,j,rfl⟩

lemma countPairsB {N k r s : ℕ} {A : Set (Sig N)} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (test target : Inp N → V k) (freq : Inp N → SeqV r k)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hr : ∀ j, bSig (fun x => raw x j) ∈ A) (hd : ∀ p j, bSig (fun x => δ x p j) ∈ A)
    (hp : ∀ t p j, bSig (fun x => path x t p j) ∈ A) (htest : ∀ j, bSig (fun x => test x j) ∈ A)
    (htar : ∀ j, bSig (fun x => target x j) ∈ A) (hf : ∀ t j, bSig (fun x => freq x t j) ∈ A) :
    Build A (⋃ t, pairBits (k+1) (countPairs hk col raw δ path test target freq t))
      ((r+1)*(16384*k*(s+1)+160000*(k+1)^2)) := by
  apply finB
  intro t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · simp only [countPairs, Fin.lastCases_last]
    refine relaxB (terminalPairB hk test target freq hfalse htrue htest htar hf) le_rfl Set.subset_union_right ?_
    have hk' := Nat.zero_le (16384*k*s)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · simpa only [countPairs, Fin.lastCases_castSucc] using
      roundPairB hk col raw δ path freq i hfalse htrue hr hd hp hf

noncomputable def coeff {k r s : ℕ} (hk : 0 < k) (col : Bool) (raw : V k) (δ : Fin s → V k)
    (path : Fin (r+1) → Fin s → V k) (test target : V k) (b : SeqV r k) : ℤ :=
  ∑ c : SeqV r k, (hitF hk col raw δ path test target c : ℤ) * sg (∑ t, dotProduct (b t) (c t))

lemma coeff_factor {k r s : ℕ} (hk : 0 < k) (col : Bool) (raw : V k) (δ : Fin s → V k)
    (path : Fin (r+1) → Fin s → V k) (test target : V k) (b : SeqV r k) :
    coeff hk col raw δ path test target b =
      if goodFirst hk col δ path then termSigned test target (prevFreq b r) *
        ∏ t : Fin r, roundSum hk (gapAmount col) (fun p => rotF hk (stepAmount col t.val) (δ p))
          (path t.castSucc) (path t.succ) (prevFreq b t.val) (b t) (rotF hk (stepAmount col t.val) raw)
      else 0 := by
  classical
  let T := (Finset.univ : Finset (Fin k)).filter (fun j => test j ≠ 0)
  have h0 (d : V k × SeqV r k) (key : V k) : stF hk col d key 0 = rotF hk (initAmount col) key + d.1 := rfl
  have hs (d : V k × SeqV r k) (key : V k) (t : Fin r) :
      stF hk col d key t.succ = layerF hk (gapAmount col) (stF hk col d key t.castSucc) +
        rotF hk (stepAmount col t.val) key + d.2 t :=
    foldl_take_succ r _ _ t
  have h := core k r s (layerF hk (gapAmount col)) (rotF hk (initAmount col))
    (fun t => rotF hk (stepAmount col t)) (rotF_add hk _) (fun _ => rotF_add hk _) raw δ path T target
    (stF hk col) h0 hs b
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h
  unfold coeff hitF
  rw [h]
  simp_rw [← prevFreq_eq]
  have hchar : termSigned test target (prevFreq b r) =
      if ∀ j, ¬ test j ≠ 0 → prevFreq b r j = 0 then
        (2 : ℤ) ^ (k-T.card) * sg (dotProduct (prevFreq b r) target) else 0 := by
    simpa only [termSigned, T, Finset.mem_filter, Finset.mem_univ, true_and] using
      char_sum k (prevFreq b r) target T
  rw [hchar]
  simp only [roundSum, Finset.sum_filter, roundAgree, roundPhase]
  by_cases h₀ : goodFirst hk col δ path = true
  · have h₀' := (goodFirst_iff hk col δ path).mp h₀
    simp [h₀, h₀', T, ite_mul]
  · have h₀' : ¬ ∀ p, path 0 p = rotF hk (initAmount col) (δ p) :=
      fun hp => h₀ ((goodFirst_iff hk col δ path).mpr hp)
    simp [h₀, h₀']

lemma listOfFn_prod {T : Type*} [CommMonoid T] : ∀ {n : ℕ} (f : Fin n → T),
    (List.ofFn f).prod = ∏ i : Fin n, f i := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih => intro f; rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, ih]

lemma countPairs_monomial {N k r s : ℕ} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (test target : Inp N → V k) (f : Inp N → SeqV r k) (t : Fin (r+1)) (x : Inp N) :
    let a := countPairs hk col raw δ path test target f t
    a.1 x < 2^(k+1) ∧ a.2 x < 2^(k+1) ∧ SignedMonomial k ((a.1 x : ℤ) - a.2 x) := by
  refine Fin.lastCases ?_ (fun i => ?_) t
  · simp only [countPairs, Fin.lastCases_last]
    have h (p : Bool) : factorCounts hk (gateTerminalOK test target)
        (gateTerminalPhase (fun y => prevFreq (f y) r)) p x ≤ 2^k := cycleCount_le hk _ _ p
    have hp : (2 : ℕ)^k < 2^(k+1) := by simp [pow_succ, Nat.two_pow_pos]
    refine ⟨(h false).trans_lt hp, (h true).trans_lt hp, ?_⟩
    change SignedMonomial k ((factorCounts hk _ _ false x : ℤ) - factorCounts hk _ _ true x)
    rw [terminalCounts_spec]
    exact terminal_monomial _ _ _
  · simp only [countPairs, Fin.lastCases_castSucc]
    let off (x : Inp N) (p : Fin s) := rotF hk (stepAmount col i.val) (δ x p)
    let ok := gateOkay hk (gapAmount col) (gapAmount_le col) off (fun x => path x i.castSucc) (fun x => path x i.succ)
    let ph := gatePhase hk (gapAmount col) (gapAmount_le col) (fun x => prevFreq (f x) i.val)
      (fun x => f x i) (fun x => rotF hk (stepAmount col i.val) (raw x))
    have h (p : Bool) : factorCounts hk ok ph p x ≤ 2^k := cycleCount_le hk _ _ p
    have hp : (2 : ℕ)^k < 2^(k+1) := by simp [pow_succ, Nat.two_pow_pos]
    refine ⟨(h false).trans_lt hp, (h true).trans_lt hp, ?_⟩
    change SignedMonomial k ((factorCounts hk ok ph false x : ℤ) - factorCounts hk ok ph true x)
    have e := roundCounts_spec hk (gapAmount col) (gapAmount_le col) off (fun x => path x i.castSucc)
      (fun x => path x i.succ) (fun x => prevFreq (f x) i.val) (fun x => f x i)
      (fun x => rotF hk (stepAmount col i.val) (raw x)) x
    dsimp only at e
    rw [e]
    exact roundSum_monomial ..

lemma countPairs_factor {N k r s : ℕ} (hk : 0 < k) (col : Bool)
    (raw : Inp N → V k) (δ : Inp N → Fin s → V k) (path : Inp N → Fin (r+1) → Fin s → V k)
    (test target : Inp N → V k) (f : Inp N → SeqV r k) (x : Inp N) :
    let F := countPairs hk col raw δ path test target f
    (Finset.univ.prod (fun t : Fin (r+1) => Int.ofNat ((F t).1 x) - Int.ofNat ((F t).2 x))) =
      termSigned (test x) (target x) (prevFreq (f x) r) *
      ∏ t : Fin r, roundSum hk (gapAmount col) (fun p => rotF hk (stepAmount col t.val) (δ x p))
        (path x t.castSucc) (path x t.succ) (prevFreq (f x) t.val) (f x t) (rotF hk (stepAmount col t.val) (raw x)) := by
  intro F
  rw [Fin.prod_univ_castSucc, mul_comm]
  congr 1
  · simp only [F, countPairs, Fin.lastCases_last, terminalPair]
    exact terminalCounts_spec hk test target (fun x => prevFreq (f x) r) x
  · apply Finset.prod_congr rfl
    intro t _
    simp only [F, countPairs, Fin.lastCases_castSucc, roundPair]
    exact roundCounts_spec hk (gapAmount col) (gapAmount_le col) _ _ _ _ _ _ x

abbrev signals0 (N : ℕ) : Set (Sig N) := initProj N ∪ ({fun _ => false} ∪ {fun _ => true})

lemma signal0false (N : ℕ) : (fun _ => false) ∈ signals0 N := Or.inr (Or.inl rfl)
lemma signal0true (N : ℕ) : (fun _ => true) ∈ signals0 N := Or.inr (Or.inr rfl)

lemma signals0B (N : ℕ) : Build (initProj N) (signals0 N) 2 :=
  extB (unionB (constB false) (constB true))

abbrev flatObs {k r s q : ℕ} (x : IC k r s q) (j : Fin q) : V (r*k) := flattenV r k (inObs x j)

abbrev redRows {k r s q : ℕ} (x : IC k r s q) : RowsState (r*k) := rowsReduce (flatObs x) (inWant x)

noncomputable def ovFlag {k r s q : ℕ} (cap : ℕ) : Sig (InCount k r s q) :=
  fun x => decide (cap < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (flatObs x))))

noncomputable abbrev readyWires (k r s q cap : ℕ) : Set (Sig (InCount k r s q)) :=
  signals0 (InCount k r s q) ∪ rowsOutputs cap (fun x => redRows x) (ovFlag cap)

lemma readyInput {k r s q cap : ℕ} (z : ISlot k r s q) :
    bSig (fun x => slotVal x z) ∈ readyWires k r s q cap :=
  Or.inl (Or.inl (slotSignal z))

lemma readyB (k r s q cap : ℕ) :
    Build (initProj (InCount k r s q)) (readyWires k r s q cap) (65536*(q+1)*(r*k+2)^3) := by
  let N := InCount k r s q
  have H : Build (signals0 N) (rowsOutputs cap (fun x => redRows x) (ovFlag cap))
      (65500*(q+1)*(r*k+2)^3) :=
    rowsB cap flatObs inWant (signal0false N) (signal0true N)
      (fun j i => Or.inl (slotSignal (slotObs j (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)))
      (fun j => Or.inl (slotSignal (slotWant j)))
  have h := seqB (signals0B N) (relaxB H Set.subset_union_right Set.subset_union_right le_rfl)
  refine relaxB h le_rfl Set.subset_union_right ?_
  have h₁ : 1 ≤ q+1 := by omega
  have h₂ : 1 ≤ (r*k+2)^3 := Nat.pow_pos (by omega)
  have h₃ := Nat.mul_le_mul h₁ h₂
  nlinarith

abbrev Padded {k r s q : ℕ} (cap : ℕ) (x : IC k r s q) := rowsPadded cap (redRows x)

noncomputable def maskOkay {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) : Sig (InCount k r s q) :=
  fun x => (!ovFlag cap x && rowsConsistent (redRows x)) && goodFirst hk col (inDelta x) (inPath x)

abbrev measureN (r k : ℕ) := (r+1)*k
abbrev answerLength (r k p : ℕ) := measureN r k+p+3
abbrev termW (r k : ℕ) := Nat.log2 (measureN r k)+1

abbrev maskFreq {k r s q : ℕ} (cap : ℕ) (m : V (min cap (r*k))) (x : IC k r s q) : SeqV r k :=
  (flattenV r k).symm (freq (Padded cap x) m)

abbrev maskNegative {k r s q : ℕ} (cap : ℕ) (m : V (min cap (r*k))) : Sig (InCount k r s q) :=
  bSig (fun x => rhsFreq (Padded cap x) m)

lemma comboB {N p : ℕ} {A : Set (Sig N)} (m : V p) (d : Fin p → FieldSig N)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hd : ∀ i, bSig (d i) ∈ A) : OneMade A (fun x => ∑ i, m i * d i x) (5*p) := by
  let g : Fin p → FieldSig N := fun i x => m i * d i x
  have h := finSigB (fun i => bSig (g i)) 1 (fun i => oneMul (oneConst hfalse htrue (m i)) (oneMem (hd i)))
  have h' := listSumFieldB (A := A ∪ Set.range (fun i => bSig (g i))) g (Or.inl hfalse)
    (fun i => Or.inr (Set.mem_range.mpr ⟨i,rfl⟩))
  exact relaxB (seq2B h h') le_rfl Set.subset_union_right (by omega)

def maskWires {k r s q : ℕ} (cap : ℕ) (m : V (min cap (r*k))) : Set (Sig (InCount k r s q)) :=
  {maskNegative cap m} ∪ {f | ∃ t j, bSig (fun x => maskFreq cap m x t j) = f}

lemma maskWiresB {k r s q : ℕ} (cap : ℕ) (m : V (min cap (r*k))) :
    Build (readyWires k r s q cap) (maskWires cap m) ((r*k+1)*(5*min cap (r*k))) := by
  let N := InCount k r s q
  let A := readyWires k r s q cap
  let st : Inp N → RowsState (r*k) := redRows
  let ov : Sig N := ovFlag cap
  let p := min cap (r*k)
  have hf : (fun _ => false) ∈ A := Or.inl (signal0false N)
  have ht : (fun _ => true) ∈ A := Or.inl (signal0true N)
  have hsg : Build A {maskNegative cap m} (5*p) :=
    comboB m (fun i x => (Padded cap x i).2) hf ht (fun i => Or.inr (rows_out_rhs cap st ov i))
  have hmat (t : Fin r) (j : Fin k) : OneMade A (fun x => maskFreq cap m x t j) (5*p) :=
    comboB m (fun i x => (Padded cap x i).1 (finProdFinEquiv (t,j))) hf ht
      (fun i => Or.inr (rows_out_coeff cap st ov i _))
  refine relaxB (unionB hsg (fin2SigB (fun t j => bSig (fun x => maskFreq cap m x t j)) (5*p) hmat))
    le_rfl Set.subset_union_right ?_
  simp only [p, Nat.mul_add, Nat.one_mul]
  ring_nf
  omega

lemma maskOkayB {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) :
    Build (readyWires k r s q cap) {maskOkay hk col cap} (s*(6*k+1)+3) := by
  let N := InCount k r s q
  let A := readyWires k r s q cap
  let st : Inp N → RowsState (r*k) := redRows
  let f : Sig N := fun x => goodFirst hk col (inDelta x) (inPath x)
  let c : Sig N := fun x => rowsConsistent (redRows x)
  let ov : Sig N := ovFlag cap
  have hf : Build A {f} (s*(6*k+1)) := goodFirstB hk col inDelta inPath
    (Or.inl (signal0true N)) (fun p j => readyInput (slotDelta p j)) (fun t p j => readyInput (slotPath t p j))
  have hc : c ∈ A := Or.inr (rows_out_consistent cap st ov)
  have ho : ov ∈ A := Or.inr (rows_out_overflow cap st ov)
  have hn := notB (A := A ∪ {f}) (Or.inl ho)
  have hh := andB (A := (A ∪ {f}) ∪ {fun x => !ov x}) (Or.inr rfl) (Or.inl (Or.inl hc))
  have hlast : Build (((A ∪ {f}) ∪ {fun x => !ov x}) ∪ {fun x => !ov x && c x}) {maskOkay hk col cap} 1 :=
    andB (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))
  have b := seq2B hf (seq2B hn (seq2B hh hlast))
  exact b

noncomputable def maskPairs {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) : Fin (r+1) → CountPair (InCount k r s q) :=
  countPairs hk col inRaw inDelta inPath inTest inTarget (maskFreq cap m)

noncomputable def maskMono {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) : Mono (InCount k r s q) :=
  monoCombine (maskOkay hk col cap) (maskNegative cap m)
    ((List.ofFn (maskPairs hk col cap m)).map (fun a => monoCompress a.1 a.2))

noncomputable def maskTerms {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) : CountPair (InCount k r s q) := monoTerms (maskMono hk col cap m)

lemma maskM_le {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) (x : IC k r s q) : (maskMono hk col cap m).2.2 x ≤ measureN r k := by
  refine (monoCombine_exp_le (k := k) _ _ _ ?_ x).trans_eq (by simp [measureN])
  intro a ha y
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
  rw [← hi]
  exact monoCompress_exp_le _ _ (fun y => (countPairs_monomial hk col inRaw inDelta inPath
    inTest inTarget (maskFreq cap m) i y).2.2) y

lemma maskTerm_bound {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) (x : IC k r s q) :
    (maskTerms hk col cap m).1 x ≤ 2^(measureN r k) ∧ (maskTerms hk col cap m).2 x ≤ 2^(measureN r k) := by
  have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (maskM_le hk col cap m x)
  constructor <;> simp only [maskTerms, monoTerms] <;> split_ifs <;> first | exact h | exact Nat.zero_le _

lemma maskTerms_spec {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) (x : IC k r s q) :
    ((maskTerms hk col cap m).1 x : ℤ) - (maskTerms hk col cap m).2 x =
      if !ovFlag cap x && rowsConsistent (redRows x) then
        sg (rhsFreq (Padded cap x) m) * coeff hk col (inRaw x) (inDelta x) (inPath x)
          (inTest x) (inTarget x) (maskFreq cap m x) else 0 := by
  let f := maskFreq (k:=k) (r:=r) (s:=s) (q:=q) cap m
  let fs := List.ofFn (maskPairs (s:=s) (q:=q) hk col cap m)
  have hm : ∀ a ∈ fs, ∀ x, SignedMonomial k ((a.1 x : ℤ) - a.2 x) := by
    intro a ha y
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    rw [← hi]
    exact (countPairs_monomial hk col inRaw inDelta inPath inTest inTarget f i y).2.2
  have h := monoCountProduct_spec (maskOkay hk col cap) (maskNegative cap m) fs hm x
  change (_ : ℤ) - _ = _ at h
  rw [show ((maskTerms hk col cap m).1 x : ℤ) - (maskTerms hk col cap m).2 x = _ from h,
    coeff_factor, List.map_ofFn, listOfFn_prod]
  have hprod := countPairs_factor hk col inRaw inDelta inPath inTest inTarget f x
  have hprod' : (∏ i : Fin (r+1), ((fun a : CountPair (InCount k r s q) => (a.1 x : ℤ) - a.2 x) ∘
      maskPairs hk col cap m) i) = _ := hprod
  rw [hprod']
  simp only [maskOkay, maskNegative, bSig]
  by_cases h₀ : (!ovFlag cap x && rowsConsistent (redRows x)) = true <;>
    by_cases h₁ : goodFirst hk col (inDelta x) (inPath x) = true <;>
    simp [h₀, h₁, sg, z2b, f]

lemma oracleCost_le (k r s p : ℕ) :
    ((r*k+1)*(5*p)+(s*(6*k+1)+3)) +
      (r+1)*(16384*k*(s+1)+160000*(k+1)^2) +
      ((r+1)*(100*(k+1)^2 + (9*termW r k+5)) + 100*(answerLength r k p)^2) ≤
    524288*(r+1)*((k+1)*(k+s+p+1)+(termW r k+1)^2) + 100*(answerLength r k p)^2 := by
  let X := (k+1)*(k+s+p+1)
  let w := termW r k
  have hks : k*(s+1) ≤ X := Nat.mul_le_mul (by omega) (by omega)
  have hkk : (k+1)^2 ≤ X := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _ (by omega)
  have hkp : (k+1)*p ≤ X := Nat.mul_le_mul_left _ (by omega)
  have hps : (k+1)*s ≤ X := Nat.mul_le_mul_left _ (by omega)
  have hX : 1 ≤ X := Nat.mul_pos (by omega) (by omega)
  have hr : 1 ≤ r+1 := by omega
  have hxf : X ≤ (r+1)*X := by simpa using Nat.mul_le_mul_right X hr
  have hrr : r*k+1 ≤ (r+1)*(k+1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have hF : (r*k+1)*(5*p) ≤ 5*((r+1)*X) := calc
    _ ≤ ((r+1)*(k+1))*(5*p) := Nat.mul_le_mul_right _ hrr
    _ = 5*((r+1)*((k+1)*p)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hkp)
  have hG : s*(6*k+1)+3 ≤ 10*((r+1)*X) := by
    calc
      _ ≤ s*(7*(k+1))+3 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      _ = 7*((k+1)*s)+3 := by ring
      _ ≤ 7*X+3 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hps) _
      _ ≤ 10*X := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hxf
  have h1 : (r+1)*(16384*k*(s+1)+160000*(k+1)^2) ≤ 176384*((r+1)*X) := calc
    _ = (r+1)*(16384*(k*(s+1))+160000*(k+1)^2) := by ring
    _ ≤ (r+1)*(16384*X+160000*X) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hks) (Nat.mul_le_mul_left _ hkk))
    _ = _ := by ring
  have h2 : (r+1)*(100*(k+1)^2 + (9*w+5)) ≤ 100*((r+1)*X) + 14*((r+1)*(w+1)^2) := by
    have hw : w+1 ≤ (w+1)^2 := by nlinarith
    have hw' : 9*w+5 ≤ 14*(w+1)^2 := by omega
    calc
      _ ≤ (r+1)*(100*X+14*(w+1)^2) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hkk) hw')
      _ = _ := by ring
  change _ ≤ 524288*(r+1)*(X+(w+1)^2)+_
  have he : 524288*(r+1)*(X+(w+1)^2) =
      524288*((r+1)*X)+524288*((r+1)*(w+1)^2) := by ring
  rw [he]
  change (r+1)*(100*(k+1)^2 + (9*termW r k+5)) ≤ _ at h2
  omega

lemma maskTermsB {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ)
    (m : V (min cap (r*k))) :
    let p := min cap (r*k)
    let L := answerLength r k p
    Build (readyWires k r s q cap) (pairBits L (maskTerms hk col cap m))
      (524288*(r+1)*((k+1)*(k+s+p+1)+(termW r k+1)^2)+100*L^2) := by
  intro p L
  let N := InCount k r s q
  let A := readyWires k r s q cap
  let W := maskWires (r:=r) (s:=s) (q:=q) cap m
  let ok : Sig N := maskOkay hk col cap
  let ng : Sig N := maskNegative cap m
  let B := W ∪ {ok}
  let f := maskFreq (s:=s) (q:=q) cap m
  let pairs := maskPairs (s:=s) (q:=q) hk col cap m
  let C := ⋃ t, pairBits (k+1) (pairs t)
  have hb : Build A B ((r*k+1)*(5*p)+(s*(6*k+1)+3)) :=
    unionB (maskWiresB cap m) (maskOkayB hk col cap)
  have hf (t : Fin r) (j : Fin k) : bSig (fun x => f x t j) ∈ A ∪ B :=
    Or.inr (Or.inl (Or.inr ⟨t,j,rfl⟩))
  have hfalse : (fun _ => false) ∈ A := Or.inl (signal0false N)
  have htrue : (fun _ => true) ∈ A := Or.inl (signal0true N)
  have hc : Build (A ∪ B) C ((r+1)*(16384*k*(s+1)+160000*(k+1)^2)) :=
    countPairsB hk col inRaw inDelta inPath inTest inTarget f (Or.inl hfalse) (Or.inl htrue)
      (fun j => Or.inl (readyInput (slotRaw j))) (fun p j => Or.inl (readyInput (slotDelta p j)))
      (fun t p j => Or.inl (readyInput (slotPath t p j))) (fun j => Or.inl (readyInput (slotTest j)))
      (fun j => Or.inl (readyInput (slotTarget j))) hf
  let D := A ∪ (B ∪ C)
  let fs := List.ofFn pairs
  have hbits : ∀ a ∈ fs, ∀ i : Fin (k+1), bitsOf (k+1) a.1 i ∈ D ∧ bitsOf (k+1) a.2 i ∈ D := by
    intro a ha j
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨t, Or.inl ⟨j,rfl⟩⟩)),
      Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨t, Or.inr ⟨j,rfl⟩⟩))⟩
  have hmono : ∀ a ∈ fs, ∀ x, a.1 x < 2^(k+1) ∧ a.2 x < 2^(k+1) ∧
      SignedMonomial k ((a.1 x : ℤ) - a.2 x) := by
    intro a ha x
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp ha
    exact countPairs_monomial hk col inRaw inDelta inPath inTest inTarget f t x
  have hd := monoCountProductB (A := D) (measureN r k) L ok ng fs (Or.inl hfalse) (Or.inl htrue)
    (Or.inr (Or.inl (Or.inr rfl))) (Or.inr (Or.inl (Or.inl (Or.inl rfl)))) hbits
    (fun a ha x => ⟨(hmono a ha x).1, (hmono a ha x).2.1⟩) (fun a ha x => (hmono a ha x).2.2)
    (by simp [fs, measureN]) (by dsimp [L,answerLength]; omega)
  have hd' : Build D (pairBits L (maskTerms hk col cap m))
      ((r+1)*(100*(k+1)^2 + (9*termW r k+5)) + 100*L^2) := by
    simpa only [fs, List.length_ofFn, pairBits, maskTerms, maskMono, pairs, ok, ng, termW] using hd
  exact relaxB (seq2B (seqB hb hc) hd') le_rfl Set.subset_union_right (oracleCost_le k r s p)

noncomputable def maskEnum (p : ℕ) : Fin (2^p) ≃ V p := Equiv.ofBijective _ (maskOfNat_bijective p)

noncomputable def totalTerms {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) : CountPair (InCount k r s q) :=
  let m := maskEnum (min cap (r*k))
  (fun x => ∑ i, (maskTerms hk col cap (m i)).1 x, fun x => ∑ i, (maskTerms hk col cap (m i)).2 x)

noncomputable def wantVal {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (x : IC k r s q) : ℕ :=
  if ovFlag cap x then 0 else
    ∑ c ∈ Finset.univ.filter (fun c : SeqV r k =>
      ∀ j, dotProduct (flatObs x j) (flattenV r k c) = inWant x j),
      hitF hk col (inRaw x) (inDelta x) (inPath x) (inTest x) (inTarget x) c

lemma noOverflow {k r s q : ℕ} {x : IC k r s q} {cap : ℕ} (h : ovFlag cap x = false) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (flatObs x))) ≤ cap := by
  unfold ovFlag at h
  exact Nat.not_lt.mp (of_decide_eq_false h)

lemma total_spec {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (x : IC k r s q) :
    ((totalTerms hk col cap).1 x : ℤ) - (totalTerms hk col cap).2 x =
      (2 : ℤ)^(min cap (r*k)) * (wantVal hk col cap x : ℤ) := by
  classical
  let p := min cap (r*k)
  let H := hitF hk col (inRaw x) (inDelta x) (inPath x) (inTest x) (inTarget x)
  unfold totalTerms
  simp only [Nat.cast_sum, ← Finset.sum_sub_distrib, maskTerms_spec]
  cases hO : ovFlag cap x with
  | true => simp [wantVal, hO]
  | false =>
    cases hC : rowsConsistent (redRows x) with
    | false =>
      have hbad (c : SeqV r k) : ¬∀ j, dotProduct (flatObs x j) (flattenV r k c) = inWant x j :=
        (rows_spec cap (flatObs x) (inWant x) (flattenV r k c)).2 hC
      simp [wantVal, hO, hC, Finset.sum_filter, hbad]
    | true =>
      have hcap := noOverflow hO
      have heq (c : SeqV r k) : (∀ j, dotProduct (flatObs x j) (flattenV r k c) = inWant x j) ↔
          ∀ j, dotProduct (Padded cap x j).1 (flattenV r k c) = (Padded cap x j).2 :=
        (rows_spec cap (flatObs x) (inWant x) (flattenV r k c)).1 hcap hC
      simp only [hO, hC, Bool.not_false, Bool.and_self, ite_true]
      have hinner (m : V p) :
          coeff hk col (inRaw x) (inDelta x) (inPath x) (inTest x) (inTarget x) (maskFreq cap m x) =
            ∑ c : SeqV r k, (H c : ℤ) * sg (dotProduct (freq (Padded cap x) m) (flattenV r k c)) := by
        unfold coeff
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← flatten_dot]
        change (H c : ℤ) * sg (dotProduct (flattenV r k ((flattenV r k).symm (freq (Padded cap x) m)))
          (flattenV r k c)) = _
        rw [LinearEquiv.apply_symm_apply]
      simp_rw [hinner]
      let f (m : V p) := sg (rhsFreq (Padded cap x) m) *
        ∑ c : SeqV r k, (H c : ℤ) * sg (dotProduct (freq (Padded cap x) m) (flattenV r k c))
      change (∑ i : Fin (2^p), f (maskEnum p i)) = _
      rw [Equiv.sum_comp (maskEnum p)]
      dsimp only [f]
      rw [walshHit (Padded cap x) (flattenV r k) H]
      simp [wantVal, hO, Finset.sum_filter, Nat.cast_sum, heq, H]

lemma totalTerm_bound {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (x : IC k r s q) :
    (totalTerms hk col cap).2 x < 2^(answerLength r k (min cap (r*k))) := by
  let p := min cap (r*k)
  let n := measureN r k
  calc
    _ ≤ ∑ _i : Fin (2^p), 2^n := by
      change (∑ i : Fin (2^p), (maskTerms hk col cap (maskEnum p i)).2 x) ≤ _
      apply Finset.sum_le_sum
      intro i _
      exact (maskTerm_bound hk col cap (maskEnum p i) x).2
    _ = 2^(p+n) := by simp [pow_add]
    _ < 2^(answerLength r k p) := Nat.pow_lt_pow_right (by decide) (by dsimp [answerLength, n]; omega)

lemma total_nonnegative {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (x : IC k r s q) :
    (totalTerms hk col cap).2 x ≤ (totalTerms hk col cap).1 x := by
  have h := total_spec hk col cap x
  have hp : 0 ≤ (2 : ℤ)^(min cap (r*k)) * (wantVal hk col cap x : ℤ) := by positivity
  omega

noncomputable abbrev ansBits {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (j : Fin (measureN r k+1)) :
    Sig (InCount k r s q) := fun x =>
  ((totalTerms hk col cap).1 x - (totalTerms hk col cap).2 x).testBit (min cap (r*k)+j.val)

lemma ansBits_spec {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) (j : Fin (measureN r k+1))
    (x : IC k r s q) : ansBits hk col cap j x = (wantVal hk col cap x).testBit j.val := by
  have hs := total_spec hk col cap x
  have h : (totalTerms hk col cap).1 x - (totalTerms hk col cap).2 x = wantVal hk col cap x*2^(min cap (r*k)) := by
    rw [mul_comm] at hs
    exact_mod_cast (Int.ofNat_sub (total_nonnegative hk col cap x)).trans hs
  change ((totalTerms hk col cap).1 x - (totalTerms hk col cap).2 x).testBit _ = _
  rw [h, Nat.testBit_mul_two_pow]
  simp

lemma listOfFn_sumVal {N : ℕ} : ∀ {n : ℕ} (f : Fin n → Inp N → ℕ) (x : Inp N),
    sumListVal (List.ofFn f) x = ∑ i : Fin n, f i x := by
  intro n
  induction n with
  | zero => intro f x; simp [sumListVal]
  | succ n ih => intro f x; simp only [List.ofFn_succ, sumListVal, Fin.sum_univ_succ, ih]

lemma aggCost_le {n n0 L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    n*(n0+100*L^2) + (n*(9*L) + n*(9*L)) + 19*L ≤ n*(n0+256*L^2) := by
  have hLL : L ≤ L^2 := by nlinarith
  have h1 := Nat.mul_le_mul_left n hLL
  have h2 : L ≤ n*L := by simpa using Nat.mul_le_mul_right L hn
  simp only [Nat.mul_add]
  have h (c : ℕ) : n*(c*L) = c*(n*L) := by ring
  have h' (c : ℕ) : n*(c*L^2) = c*(n*L^2) := by ring
  rw [h, h', h']
  omega

lemma aggregateB {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) :
    let p := min cap (r*k)
    let L := answerLength r k p
    Build (readyWires k r s q cap) ({ovFlag cap} ∪ Set.range (ansBits hk col cap))
      (2^p*(524288*(r+1)*((k+1)*(k+s+p+1)+(termW r k+1)^2)+256*L^2)) := by
  intro p L
  let N := InCount k r s q
  let m := maskEnum p
  let a (i : Fin (2^p)) := maskTerms (s:=s) (q:=q) hk col cap (m i)
  let A := readyWires k r s q cap
  let C := ⋃ i, pairBits L (a i)
  let D := A ∪ C
  let cost := 524288*(r+1)*((k+1)*(k+s+p+1)+(termW r k+1)^2)
  have h1 : Build A C (2^p*(cost+100*L^2)) :=
    finB (fun i => pairBits L (a i)) _ (fun i => maskTermsB hk col cap (m i))
  have hf : (fun _ => false) ∈ A := Or.inl (signal0false N)
  have ht : (fun _ => true) ∈ A := Or.inl (signal0true N)
  let T := totalTerms (r:=r) (s:=s) (q:=q) hk col cap
  have hs (b : Bool) : Build D (Set.range (bitsOf L (if b then T.2 else T.1))) (2^p*(9*L)) := by
    let f : Fin (2^p) → Inp N → ℕ := fun i => if b then (a i).2 else (a i).1
    have h := sumListB (A := D) L (Or.inl hf) (List.ofFn f) (by
      intro u hu j
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      refine Or.inr (Set.mem_iUnion.mpr ⟨i,?_⟩)
      cases b
      · exact Or.inl ⟨j,rfl⟩
      · exact Or.inr ⟨j,rfl⟩)
    have he : sumListVal (List.ofFn f) = (if b then T.2 else T.1) := by
      funext x
      rw [listOfFn_sumVal]
      cases b <;> rfl
    simpa only [he, List.length_ofFn] using h
  have h2 : Build D (pairBits L T) (2^p*(9*L)+2^p*(9*L)) := unionB (hs false) (hs true)
  let E := A ∪ (C ∪ pairBits L T)
  have h3 : Build E (Set.range (bitsOf L (fun x => T.1 x - T.2 x))) (19*L) :=
    subTwoB L T.1 T.2 (Or.inl hf) (Or.inl ht)
      (fun j => Or.inr (Or.inr (Or.inl ⟨j,rfl⟩))) (fun j => Or.inr (Or.inr (Or.inr ⟨j,rfl⟩)))
      (fun x => ⟨total_nonnegative hk col cap x, totalTerm_bound hk col cap x⟩)
  have h4 := seq2B (seqB h1 h2) h3
  refine relaxB h4 le_rfl ?_ (aggCost_le (Nat.two_pow_pos p) (by dsimp [L,answerLength]; omega))
  intro f hf'
  rcases hf' with h | ⟨j,rfl⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact Or.inl (Or.inr (rows_out_overflow cap (fun x => redRows x) (ovFlag cap)))
  · let i : Fin L := ⟨p+j.val, by dsimp [L,answerLength]; omega⟩
    exact Or.inr ⟨i,rfl⟩

lemma fullBuild {k r s q : ℕ} (hk : 0 < k) (col : Bool) (cap : ℕ) :
    let p := min cap (r*k)
    let L := answerLength r k p
    Build (initProj (InCount k r s q)) ({ovFlag cap} ∪ Set.range (ansBits hk col cap))
      (65536*(q+1)*(r*k+2)^3 +
      2^p*(524288*(r+1)*((k+1)*(k+s+p+1)+(termW r k+1)^2)+256*L^2)) :=
  transB (readyB k r s q cap) (aggregateB hk col cap)

end PEqualNP.Outside.L_meta_25894_aux

open PEqualNP.Outside.L_meta_25894_aux in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25894 : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ col : Bool,
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let S := Fin r → W
    let encodeInput := fun (raw : W) (delta : Fin s → W)
      (path : Fin (r+1) → Fin s → W) (test target : W) =>
      let bits := fun (x : W) => (List.finRange k).map (fun j => decide (x j ≠ 0))
      bits raw ++ (List.finRange s).flatMap (fun p => bits (delta p)) ++
      (List.finRange (r+1)).flatMap (fun t =>
        (List.finRange s).flatMap (fun p => bits (path t p))) ++ bits test ++ bits target
    let coords := fun (b : S) => (List.finRange r).flatMap (fun t =>
      (List.finRange k).map (fun j => decide (b t j ≠ 0)))
    let hits := fun (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W)
      (test target : W) (c : S) =>
      ((Finset.univ : Finset W).filter (fun name =>
        (∀ t p, state (name,c) (raw+delta p) t - state (name,c) raw t = path t p) ∧
        (∀ j, test j ≠ 0 → state (name,c) raw (Fin.last r) j = target j))).card
    let pairing := fun (b c : S) => ∑ t : Fin r, dotProduct (b t) (c t)
    let countBits := (r+1)*k
    let w := Nat.log2 countBits + 1
    let common := (3+s+(r+1)*s)*k
    ∀ q cap : Nat,
      let p := min cap (r*k)
      let inputs := common+q*r*k+q
      let length := countBits+p+3
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (overflow : Fin (inputs+C.size))
        (answer : Fin (countBits+1) → Fin (inputs+C.size)),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
        C.output = overflow.val ∧
        C.size ≤ 65536*(q+1)*(r*k+2)^3 +
          2^p * (524288*(r+1)*((k+1)*(k+s+p+1)+(w+1)^2) + 256*length^2) ∧
        ∀ (raw : W) (delta : Fin s → W) (path : Fin (r+1) → Fin s → W)
          (test target : W) (obs : Fin q → S) (wanted : Fin q → F),
          let xs := encodeInput raw delta path test target ++
            (List.finRange q).flatMap (fun j => coords (obs j)) ++
            (List.finRange q).map (fun j => decide (wanted j ≠ 0))
          let rank := Module.finrank F (Submodule.span F (Set.range obs))
          let val : Nat := if rank ≤ cap then
            ∑ c ∈ (Finset.univ : Finset S).filter (fun c => ∀ j, pairing (obs j) c = wanted j),
              hits raw delta path test target c
            else 0
          (C.wires xs).getD overflow.val false = decide (cap < rank) ∧
          (∀ j : Fin (countBits+1), (C.wires xs).getD (answer j).val false = val.testBit j.val) := by
  intro k r s hk F W ix rot layer col initial gap inject state S encodeInput coords hits pairing
    countBits w common q cap p inputs length
  have hbuild := fullBuild (r := r) (s := s) (q := q) hk col cap
  obtain ⟨C, overflow, answer, hfan, hback, hout, hsize, hflag, hbits⟩ :=
    finishFlagBits (startSched inputs) hbuild
  refine ⟨C, overflow, answer, hfan, hback, hout, by simpa using hsize, ?_⟩
  intro raw delta path test target obs wanted xs rank val
  let x := packVector (inputData raw delta path test target obs wanted)
  have hx : List.ofFn x = xs := packVector_spec raw delta path test target obs wanted
  have hraw : inRaw x = raw := funext fun j => decodeSlot _ (slotRaw j)
  have hdelta : inDelta x = delta := funext fun i => funext fun j => decodeSlot _ (slotDelta i j)
  have hpath : inPath x = path := funext fun t => funext fun i => funext fun j => decodeSlot _ (slotPath t i j)
  have htest : inTest x = test := funext fun j => decodeSlot _ (slotTest j)
  have htarget : inTarget x = target := funext fun j => decodeSlot _ (slotTarget j)
  have hobs : inObs x = obs := funext fun i => funext fun t => funext fun j => decodeSlot _ (slotObs i t j)
  have hwanted : inWant x = wanted := funext fun i => decodeSlot _ (slotWant i)
  have hrank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (flatObs x))) = rank := by
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun i => flattenV r k (inObs x i)))) = _
    rw [flatten_rank]
    exact congrArg (fun o : Fin q → SeqV r k => Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range o))) hobs
  have hov : ovFlag cap x = decide (cap < rank) := by
    unfold ovFlag
    rw [hrank]
  have hv : wantVal hk col cap x = val := by
    unfold wantVal
    rw [hov]
    by_cases h : rank ≤ cap
    · have h' : ¬ cap < rank := by omega
      simp only [h', decide_false, Bool.false_eq_true, ite_false, val, h, ite_true]
      simp only [flatObs, flatten_dot, hobs, hraw, hdelta, hpath, htest, htarget]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairing]
      constructor <;> intro H j
      · exact (H j).trans (congrFun hwanted j)
      · exact (H j).trans (congrFun hwanted j).symm
    · have h' : cap < rank := by omega
      simp [val, h, h']
  refine ⟨?_, fun j => ?_⟩
  · rw [← hx, hflag x, hov]
  · rw [← hx, hbits j x, ansBits_spec hk col cap j x, hv]
