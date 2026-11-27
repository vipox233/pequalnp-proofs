import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25940_aux

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

structure Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop where
  run : ∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B)

theorem idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

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
      · exact hw a (Or.inr h2b)⟩

theorem seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

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
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩⟩

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

structure Quad (m : ℕ) where
  B : Fin m → Fin m → ZMod 2
  l : Fin m → ZMod 2
  c : ZMod 2

def Quad.Valid {m : ℕ} (Q : Quad m) : Prop :=
  (∀ i, Q.B i i = 0) ∧ (∀ i j, Q.B i j = Q.B j i)

def Quad.zero (m : ℕ) : Quad m := ⟨fun _ _ => 0, fun _ => 0, 0⟩

def Quad.add {m : ℕ} (P Q : Quad m) : Quad m :=
  ⟨fun i j => P.B i j + Q.B i j, fun i => P.l i + Q.l i, P.c + Q.c⟩

def Quad.eval {m : ℕ} (Q : Quad m) (a : Fin m → ZMod 2) : ZMod 2 :=
  Q.c + ∑ i : Fin m, Q.l i * a i +
    ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then Q.B i j * a i * a j else 0

theorem Quad.eval_zero {m : ℕ} (a : Fin m → ZMod 2) :
    (Quad.zero m).eval a = 0 := by
  simp [Quad.eval, Quad.zero]

theorem Quad.valid_zero (m : ℕ) : (Quad.zero m).Valid :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem Quad.valid_add {m : ℕ} {P Q : Quad m} (hP : P.Valid) (hQ : Q.Valid) :
    (P.add Q).Valid :=
  ⟨fun i => by simp [Quad.add, hP.1 i, hQ.1 i],
   fun i j => by simp [Quad.add, hP.2 i j, hQ.2 i j]⟩

theorem Quad.eval_add {m : ℕ} (P Q : Quad m) (a : Fin m → ZMod 2) :
    (P.add Q).eval a = P.eval a + Q.eval a := by
  unfold Quad.eval Quad.add
  have h1 : (∑ i : Fin m, (P.l i + Q.l i) * a i) =
      (∑ i : Fin m, P.l i * a i) + (∑ i : Fin m, Q.l i * a i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_mul _ _ _)
  have h2 : (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then (P.B i j + Q.B i j) * a i * a j else 0) =
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then P.B i j * a i * a j else 0) +
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then Q.B i j * a i * a j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i.val < j.val <;> simp only [h, ↓reduceIte, add_zero]
    ring
  rw [h1, h2]
  ring

def Quad.addAffineProd {m : ℕ} (Q : Quad m)
    (e0 : ZMod 2) (e : Fin m → ZMod 2) (f0 : ZMod 2) (f : Fin m → ZMod 2) : Quad m :=
  { B := fun i j => if i = j then 0 else Q.B i j + e i * f j + e j * f i
    l := fun i => Q.l i + e0 * f i + f0 * e i + e i * f i
    c := Q.c + e0 * f0 }

theorem Quad.valid_addAffineProd {m : ℕ} {Q : Quad m} (hQ : Q.Valid)
    (e0 : ZMod 2) (e : Fin m → ZMod 2) (f0 : ZMod 2) (f : Fin m → ZMod 2) :
    (Q.addAffineProd e0 e f0 f).Valid := by
  refine ⟨fun i => by simp [Quad.addAffineProd], fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; simp [Quad.addAffineProd]
  · have hji : j ≠ i := Ne.symm hij
    simp only [Quad.addAffineProd, hij, hji, ↓reduceIte, hQ.2 i j]
    ring

theorem Quad.eval_addAffineProd {m : ℕ} (Q : Quad m)
    (e0 : ZMod 2) (e : Fin m → ZMod 2) (f0 : ZMod 2) (f : Fin m → ZMod 2)
    (a : Fin m → ZMod 2) :
    (Q.addAffineProd e0 e f0 f).eval a =
      Q.eval a + (e0 + ∑ i : Fin m, e i * a i) * (f0 + ∑ i : Fin m, f i * a i) := by
  have hprod : (e0 + ∑ i : Fin m, e i * a i) * (f0 + ∑ j : Fin m, f j * a j) =
      e0 * f0 +
      (∑ i : Fin m, (e0 * f i + f0 * e i + e i * f i) * a i) +
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then (e i * f j + e j * f i) * a i * a j else 0) := by
    have hexp : (e0 + ∑ i : Fin m, e i * a i) * (f0 + ∑ j : Fin m, f j * a j) =
        e0 * f0 + (∑ j : Fin m, e0 * (f j * a j)) + (∑ i : Fin m, (e i * a i) * f0) +
        (∑ i : Fin m, ∑ j : Fin m, (e i * a i) * (f j * a j)) := by
      rw [add_mul, mul_add, mul_add, Finset.mul_sum, Finset.sum_mul]
      have hdd : (∑ i : Fin m, e i * a i) * (∑ j : Fin m, f j * a j) =
          ∑ i : Fin m, ∑ j : Fin m, (e i * a i) * (f j * a j) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
      rw [hdd]
      ring
    have hsplit : (∑ i : Fin m, ∑ j : Fin m, (e i * a i) * (f j * a j)) =
        (∑ i : Fin m, e i * f i * a i) +
        (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then e i * f j * a i * a j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if j.val < i.val then e i * f j * a i * a j else 0) := by
      have hterm : ∀ i j : Fin m,
          (e i * a i) * (f j * a j) =
          (if i = j then e i * f i * a i else 0) +
          (if i.val < j.val then e i * f j * a i * a j else 0) +
          (if j.val < i.val then e i * f j * a i * a j else 0) := by
        intro i j
        rcases lt_trichotomy i.val j.val with hlt | heq | hgt
        · have hne : i ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          have hngt : ¬ j.val < i.val := by omega
          simp only [hne, hlt, hngt, ↓reduceIte, zero_add, add_zero]
          ring
        · have hij : i = j := Fin.ext heq
          subst hij
          simp only [lt_irrefl, ↓reduceIte, add_zero]
          have : a i * a i = a i := z2_mul_self (a i)
          calc
            e i * a i * (f i * a i) = e i * f i * (a i * a i) := by ring
            _ = e i * f i * a i := by rw [this]
        · have hne : i ≠ j := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
          have hnlt : ¬ i.val < j.val := by omega
          simp only [hne, hnlt, hgt, ↓reduceIte, zero_add]
          ring
      simp_rw [hterm, Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp
    have hswap : (∑ i : Fin m, ∑ j : Fin m, if j.val < i.val then e i * f j * a i * a j else 0) =
        ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then e j * f i * a i * a j else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases h : i.val < j.val <;> simp only [h, ↓reduceIte]
      ring
    rw [hexp, hsplit, hswap]
    have hlin : (∑ j : Fin m, e0 * (f j * a j)) + (∑ i : Fin m, e i * a i * f0) +
        (∑ i : Fin m, e i * f i * a i) =
        ∑ i : Fin m, (e0 * f i + f0 * e i + e i * f i) * a i := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have hquad :
        (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then e i * f j * a i * a j else 0) +
        (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then e j * f i * a i * a j else 0) =
        ∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then (e i * f j + e j * f i) * a i * a j else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : i.val < j.val <;> simp only [h, ↓reduceIte, add_zero]
      ring
    calc
      e0 * f0 + (∑ j, e0 * (f j * a j)) + (∑ i, e i * a i * f0) +
          ((∑ i, e i * f i * a i) +
            (∑ i, ∑ j, if i.val < j.val then e i * f j * a i * a j else 0) +
            (∑ i, ∑ j, if i.val < j.val then e j * f i * a i * a j else 0)) =
        e0 * f0 + ((∑ j, e0 * (f j * a j)) + (∑ i, e i * a i * f0) + (∑ i, e i * f i * a i)) +
          ((∑ i, ∑ j, if i.val < j.val then e i * f j * a i * a j else 0) +
            (∑ i, ∑ j, if i.val < j.val then e j * f i * a i * a j else 0)) := by ring
      _ = _ := by rw [hlin, hquad]
  rw [hprod]
  unfold Quad.eval Quad.addAffineProd
  have h1 : (∑ i : Fin m, (Q.l i + e0 * f i + f0 * e i + e i * f i) * a i) =
      (∑ i : Fin m, Q.l i * a i) + (∑ i : Fin m, (e0 * f i + f0 * e i + e i * f i) * a i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : (∑ i : Fin m, ∑ j : Fin m,
        if i.val < j.val then (if i = j then 0 else Q.B i j + e i * f j + e j * f i) * a i * a j else 0) =
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then Q.B i j * a i * a j else 0) +
      (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then (e i * f j + e j * f i) * a i * a j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i.val < j.val
    · have hne : i ≠ j := fun heq => by rw [heq] at h; exact lt_irrefl _ h
      simp only [h, hne, ↓reduceIte]
      ring
    · simp only [h, ↓reduceIte, add_zero]
  rw [h1, h2]
  ring

theorem Quad.secondDiff_eq_B {m : ℕ} {Q : Quad m} (hQ : Q.Valid) (r s : Fin m) :
    let unit := fun (j i : Fin m) => (if i = j then 1 else 0 : ZMod 2)
    Q.eval (unit r + unit s) + Q.eval (unit r) + Q.eval (unit s) + Q.eval 0 = Q.B r s := by
  intro unit
  by_cases hrs : r = s
  · subst hrs
    have h0 : unit r + unit r = 0 := by
      funext i; simp [unit, z2_add_self]
    rw [h0, hQ.1 r]
    have h1 : Q.eval 0 + Q.eval (unit r) + Q.eval (unit r) + Q.eval 0 =
        (Q.eval 0 + Q.eval 0) + (Q.eval (unit r) + Q.eval (unit r)) := by ring
    rw [h1, z2_add_self, z2_add_self, add_zero]
  · have heval0 : Q.eval 0 = Q.c := by simp [Quad.eval]
    have heval1 : ∀ u : Fin m, Q.eval (unit u) = Q.c + Q.l u := by
      intro u
      unfold Quad.eval
      have hl : ∑ i : Fin m, Q.l i * unit u i = Q.l u := by
        rw [Finset.sum_eq_single u]
        · simp [unit]
        · intro i _ hiu; simp [unit, hiu]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hq : ∑ i : Fin m, ∑ j : Fin m,
          (if i.val < j.val then Q.B i j * unit u i * unit u j else 0) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
        by_cases hlt : i.val < j.val
        · have hne : i ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
          by_cases hi : i = u
          · subst hi; simp [unit, hlt, Ne.symm hne]
          · simp [unit, hlt, hi]
        · simp [hlt]
      rw [hl, hq, add_zero]
    have heval2 : ∀ u v : Fin m, u.val < v.val →
        Q.eval (unit u + unit v) = Q.c + Q.l u + Q.l v + Q.B u v := by
      intro u v huv
      have huv_ne : u ≠ v := fun h => by rw [h] at huv; exact lt_irrefl _ huv
      unfold Quad.eval
      have hl : ∑ i : Fin m, Q.l i * (unit u + unit v) i = Q.l u + Q.l v := by
        have hsp : ∀ i : Fin m, Q.l i * (unit u + unit v) i =
            Q.l i * unit u i + Q.l i * unit v i := fun i => mul_add _ _ _
        simp_rw [hsp, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single u]
          · simp [unit]
          · intro i _ hiu; simp [unit, hiu]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [Finset.sum_eq_single v]
          · simp [unit]
          · intro i _ hiv; simp [unit, hiv]
          · intro h; exact absurd (Finset.mem_univ _) h
      have hq : ∑ i : Fin m, ∑ j : Fin m,
          (if i.val < j.val then Q.B i j * (unit u + unit v) i * (unit u + unit v) j else 0) =
          Q.B u v := by
        rw [Finset.sum_eq_single u]
        · rw [Finset.sum_eq_single v]
          · simp [unit, huv, huv_ne, Ne.symm huv_ne]
          · intro j _ hjv
            by_cases hlt : u.val < j.val
            · have hju : j ≠ u := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
              simp [unit, hlt, hjv, hju]
            · simp [hlt]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro i _ hiu
          refine Finset.sum_eq_zero (fun j _ => ?_)
          by_cases hlt : i.val < j.val
          · by_cases hiv : i = v
            · subst hiv
              have hji : j ≠ i := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
              have hju : j ≠ u := fun h => by rw [h] at hlt; omega
              simp [unit, hlt, hji, hju]
            · simp [unit, hlt, hiu, hiv]
          · simp [hlt]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hl, hq]
      ring
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hrs) with hlt | hgt
    · rw [heval2 r s hlt, heval1 r, heval1 s, heval0]
      have h1 : (Q.c + Q.l r + Q.l s + Q.B r s) + (Q.c + Q.l r) + (Q.c + Q.l s) + Q.c =
          Q.B r s + (Q.c + Q.c) + (Q.c + Q.c) + (Q.l r + Q.l r) + (Q.l s + Q.l s) := by ring
      rw [h1, z2_add_self Q.c, z2_add_self (Q.l r), z2_add_self (Q.l s)]
      ring
    · rw [add_comm (unit r) (unit s), heval2 s r hgt, heval1 r, heval1 s, heval0, hQ.2 s r]
      have h1 : (Q.c + Q.l s + Q.l r + Q.B r s) + (Q.c + Q.l r) + (Q.c + Q.l s) + Q.c =
          Q.B r s + (Q.c + Q.c) + (Q.c + Q.c) + (Q.l r + Q.l r) + (Q.l s + Q.l s) := by ring
      rw [h1, z2_add_self Q.c, z2_add_self (Q.l r), z2_add_self (Q.l s)]
      ring

def Quad.delVar {m : ℕ} (Q : Quad m) (i : Fin m) : Quad m :=
  { B := fun u v => if u = i ∨ v = i then 0 else Q.B u v
    l := fun u => if u = i then 0 else Q.l u
    c := Q.c }

theorem Quad.valid_delVar {m : ℕ} {Q : Quad m} (hQ : Q.Valid) (i : Fin m) :
    (Q.delVar i).Valid := by
  refine ⟨fun u => ?_, fun u v => ?_⟩
  · by_cases h : u = i <;> simp [Quad.delVar, h, hQ.1 u]
  · by_cases hu : u = i <;> by_cases hv : v = i <;> simp [Quad.delVar, hu, hv, hQ.2 u v]

theorem Quad.eval_eq_delVar_add {m : ℕ} {Q : Quad m} (hQ : Q.Valid) (i : Fin m)
    (a : Fin m → ZMod 2) :
    Q.eval a = (Q.delVar i).eval a +
      a i * (Q.l i + ∑ u : Fin m, (if u = i then 0 else Q.B i u) * a u) := by
  unfold Quad.eval Quad.delVar
  have hlin : (∑ u : Fin m, Q.l u * a u) =
      (∑ u : Fin m, (if u = i then 0 else Q.l u) * a u) + Q.l i * a i := by
    have hsp : ∀ u : Fin m, Q.l u * a u =
        (if u = i then 0 else Q.l u) * a u + (if u = i then Q.l i * a i else 0) := by
      intro u
      by_cases h : u = i <;> simp [h]
    rw [Finset.sum_congr rfl (fun u _ => hsp u), Finset.sum_add_distrib]
    congr 1
    simp
  have hquad :
      (∑ u : Fin m, ∑ v : Fin m, if u.val < v.val then Q.B u v * a u * a v else 0) =
      (∑ u : Fin m, ∑ v : Fin m,
        if u.val < v.val then (if u = i ∨ v = i then 0 else Q.B u v) * a u * a v else 0) +
      a i * (∑ u : Fin m, (if u = i then 0 else Q.B i u) * a u) := by
    have hsp : ∀ u v : Fin m,
        (if u.val < v.val then Q.B u v * a u * a v else 0) =
        (if u.val < v.val then (if u = i ∨ v = i then 0 else Q.B u v) * a u * a v else 0) +
        ((if u = i ∧ u.val < v.val then Q.B i v * a i * a v else 0) +
         (if v = i ∧ u.val < v.val then Q.B u i * a u * a i else 0)) := by
      intro u v
      by_cases hlt : u.val < v.val
      · have hne : u ≠ v := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
        by_cases hu : u = i
        · subst hu
          have hvi : v ≠ u := Ne.symm hne
          simp [hlt, hvi]
        · by_cases hv : v = i
          · subst hv; simp [hlt, hu]
          · simp [hlt, hu, hv]
      · simp [hlt]
    rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => hsp u v))]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    have hA : (∑ u : Fin m, ∑ v : Fin m, if u = i ∧ u.val < v.val then Q.B i v * a i * a v else 0) =
        ∑ v : Fin m, if i.val < v.val then Q.B i v * a i * a v else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro u _ hui; simp [hui]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hB : (∑ u : Fin m, ∑ v : Fin m, if v = i ∧ u.val < v.val then Q.B u i * a u * a i else 0) =
        ∑ u : Fin m, if u.val < i.val then Q.B i u * a i * a u else 0 := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_eq_single i]
      · by_cases hlt : u.val < i.val
        · simp only [hlt, and_self, ↓reduceIte, hQ.2 u i]; ring
        · simp [hlt]
      · intro v _ hvi; simp [hvi]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hA, hB, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rcases lt_trichotomy i.val u.val with hlt | heq | hgt
    · have hui : u ≠ i := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      have hngt : ¬ u.val < i.val := by omega
      simp only [hlt, hngt, hui, ↓reduceIte, add_zero]
      ring
    · have hui : u = i := Fin.ext heq.symm
      subst hui
      simp
    · have hui : u ≠ i := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
      have hnlt : ¬ i.val < u.val := by omega
      simp only [hnlt, hgt, hui, ↓reduceIte, zero_add]
      ring
  rw [hlin, hquad]
  ring

structure GaussState (R C P : ℕ) where
  used : Fin R → Bool
  M : Fin R → Fin C → ZMod 2
  Pay : Fin R → Fin P → ZMod 2

def gaussStep {R C P : ℕ} (col : ℕ) (st : GaussState R C P) : GaussState R C P :=
  if hcol : col < C then
    let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin R → Bool := fun r => !(st.used r) && z2b (st.M r c0)
    let isPiv : Fin R → Bool := firstTrue cond
    let pivM : Fin C → ZMod 2 := fun c =>
      b2z ((List.finRange R).any (fun r => isPiv r && z2b (st.M r c)))
    let pivP : Fin P → ZMod 2 := fun p =>
      b2z ((List.finRange R).any (fun r => isPiv r && z2b (st.Pay r p)))
    { used := fun r => st.used r || isPiv r
      M := fun r c => if !(isPiv r) && z2b (st.M r c0) then st.M r c + pivM c else st.M r c
      Pay := fun r p => if !(isPiv r) && z2b (st.M r c0) then st.Pay r p + pivP p else st.Pay r p }
  else st

def gaussElim {R C P : ℕ} (M0 : Fin R → Fin C → ZMod 2) (Pay0 : Fin R → Fin P → ZMod 2) :
    GaussState R C P :=
  (List.range C).foldl (fun st col => gaussStep col st) ⟨fun _ => false, M0, Pay0⟩

theorem gaussStep_spec {R C P : ℕ} (col : ℕ) (hcol : col < C) (st : GaussState R C P) :
    let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin R → Bool := fun r => !(st.used r) && z2b (st.M r c0)
    let st' := gaussStep col st
    (∀ r, st'.used r = true ↔ st.used r = true ∨ firstTrue cond r = true) ∧
    ((∀ r, cond r = false) → st' = st) ∧
    (∀ p0, firstTrue cond p0 = true →
      st'.M p0 = st.M p0 ∧ st'.Pay p0 = st.Pay p0 ∧
      ∀ r, r ≠ p0 →
        st'.M r = st.M r + (st.M r c0) • st.M p0 ∧
        st'.Pay r = st.Pay r + (st.M r c0) • st.Pay p0) := by
  intro c0 cond st'
  have hst' : st' =
      let isPiv : Fin R → Bool := firstTrue cond
      let pivM : Fin C → ZMod 2 := fun c =>
        b2z ((List.finRange R).any (fun r => isPiv r && z2b (st.M r c)))
      let pivP : Fin P → ZMod 2 := fun p =>
        b2z ((List.finRange R).any (fun r => isPiv r && z2b (st.Pay r p)))
      { used := fun r => st.used r || isPiv r
        M := fun r c => if !(isPiv r) && z2b (st.M r c0) then st.M r c + pivM c else st.M r c
        Pay := fun r p => if !(isPiv r) && z2b (st.M r c0) then st.Pay r p + pivP p else st.Pay r p } := by
    simp only [st', gaussStep, hcol, ↓reduceDIte, c0, cond]
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [hst']
    simp
  · intro hnone
    have hnoPiv : ∀ r, firstTrue cond r = false := by
      intro r
      cases h : firstTrue cond r
      · rfl
      · have := ((firstTrue_spec cond r).mp h).1
        rw [hnone r] at this
        exact Bool.noConfusion this
    rw [hst']
    cases st with
    | mk u M Pay =>
      have hany0 : ((List.finRange R).any (fun _ => false)) = false := by simp
      dsimp only
      congr 1
      · funext r; simp [hnoPiv r]
      · funext r c
        simp only [hnoPiv, Bool.false_and, hany0, b2z, Bool.false_eq_true, ↓reduceIte, add_zero, ite_self]
      · funext r p
        simp only [hnoPiv, Bool.false_and, hany0, b2z, Bool.false_eq_true, ↓reduceIte, add_zero, ite_self]
  · intro p0 hp0
    have huniq : ∀ r, firstTrue cond r = true ↔ r = p0 := fun r =>
      ⟨fun h => firstTrue_unique cond h hp0, fun h => h ▸ hp0⟩
    have hpivM : ∀ c, b2z ((List.finRange R).any (fun r => firstTrue cond r && z2b (st.M r c))) =
        st.M p0 c := by
      intro c
      have hany : ((List.finRange R).any (fun r => firstTrue cond r && z2b (st.M r c))) =
          z2b (st.M p0 c) := by
        cases h : z2b (st.M p0 c)
        · rw [List.any_eq_false]
          intro r _
          by_cases hr : r = p0
          · subst hr; simp [h]
          · have hf : firstTrue cond r = false := by
              cases h' : firstTrue cond r
              · rfl
              · exact absurd ((huniq r).mp h') hr
            simp [hf]
        · rw [List.any_eq_true]
          exact ⟨p0, List.mem_finRange p0, by simp [hp0, h]⟩
      rw [hany, b2z_z2b]
    have hpivP : ∀ p, b2z ((List.finRange R).any (fun r => firstTrue cond r && z2b (st.Pay r p))) =
        st.Pay p0 p := by
      intro p
      have hany : ((List.finRange R).any (fun r => firstTrue cond r && z2b (st.Pay r p))) =
          z2b (st.Pay p0 p) := by
        cases h : z2b (st.Pay p0 p)
        · rw [List.any_eq_false]
          intro r _
          by_cases hr : r = p0
          · subst hr; simp [h]
          · have hf : firstTrue cond r = false := by
              cases h' : firstTrue cond r
              · rfl
              · exact absurd ((huniq r).mp h') hr
            simp [hf]
        · rw [List.any_eq_true]
          exact ⟨p0, List.mem_finRange p0, by simp [hp0, h]⟩
      rw [hany, b2z_z2b]
    rw [hst']
    refine ⟨?_, ?_, ?_⟩
    · funext c; simp [hp0]
    · funext p; simp [hp0]
    · intro r hr
      have hrf : firstTrue cond r = false := by
        cases h' : firstTrue cond r
        · rfl
        · exact absurd ((huniq r).mp h') hr
      refine ⟨?_, ?_⟩
      · funext c
        simp only [hrf, Bool.not_false, Bool.true_and, hpivM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases z2_cases (st.M r c0) with h0 | h1
        · simp [h0, z2b_zero]
        · simp [h1, z2b_one]
      · funext p
        simp only [hrf, Bool.not_false, Bool.true_and, hpivP, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases z2_cases (st.M r c0) with h0 | h1
        · simp [h0, z2b_zero]
        · simp [h1, z2b_one]

theorem gaussElim_invariants {R C P : ℕ}
    (M0 : Fin R → Fin C → ZMod 2) (Pay0 : Fin R → Fin P → ZMod 2) :
    let st := gaussElim M0 Pay0
    Submodule.span (ZMod 2) (Set.range st.M) = Submodule.span (ZMod 2) (Set.range M0) ∧
    (∀ r, st.used r = true → ∃ c : Fin C, st.M r c = 1 ∧ ∀ j, j ≠ r → st.M j c = 0) ∧
    (∀ r, st.used r = false → ∀ c : Fin C, st.M r c = 0) ∧
    (∀ (α : Type) [AddCommGroup α] [Module (ZMod 2) α] (f : (Fin C → ZMod 2) → (Fin P → ZMod 2) → α),
      (∀ m1 m2 p1 p2, f (m1 + m2) (p1 + p2) = f m1 p1 + f m2 p2) →
      ((∀ r, f (st.M r) (st.Pay r) = 0) ↔ (∀ r, f (M0 r) (Pay0 r) = 0))) ∧
    (∀ (PropRow : (Fin C → ZMod 2) → Prop),
      PropRow 0 → (∀ u v, PropRow u → PropRow v → PropRow (u + v)) →
      (∀ r, PropRow (M0 r)) → (∀ r, PropRow (st.M r))) := by
  have hloop : ∀ t ≤ C,
      let st := (List.range t).foldl (fun s col => gaussStep col s) ⟨fun _ => false, M0, Pay0⟩
      Submodule.span (ZMod 2) (Set.range st.M) = Submodule.span (ZMod 2) (Set.range M0) ∧
      (∀ r, st.used r = true → ∃ c : Fin C, c.val < t ∧ st.M r c = 1 ∧ ∀ j, j ≠ r → st.M j c = 0) ∧
      (∀ r, st.used r = false → ∀ c : Fin C, c.val < t → st.M r c = 0) ∧
      (∀ (α : Type) [AddCommGroup α] [Module (ZMod 2) α] (f : (Fin C → ZMod 2) → (Fin P → ZMod 2) → α),
        (∀ m1 m2 p1 p2, f (m1 + m2) (p1 + p2) = f m1 p1 + f m2 p2) →
        ((∀ r, f (st.M r) (st.Pay r) = 0) ↔ (∀ r, f (M0 r) (Pay0 r) = 0))) ∧
      (∀ (PropRow : (Fin C → ZMod 2) → Prop),
        PropRow 0 → (∀ u v, PropRow u → PropRow v → PropRow (u + v)) →
        (∀ r, PropRow (M0 r)) → (∀ r, PropRow (st.M r))) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · intro r h; exact Bool.noConfusion h
      · intro r _ c hc; omega
      · intro _ _ _ _ _; exact Iff.rfl
      · intro _ _ _ h; exact h
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨hspan, hpiv, hzero, hlin, hprop⟩
      let st := (List.range t).foldl (fun s col => gaussStep col s) ⟨fun _ => false, M0, Pay0⟩
      have hst_next : (List.range (t + 1)).foldl (fun s col => gaussStep col s)
          ⟨fun _ => false, M0, Pay0⟩ = gaussStep t st := by
        simp [List.range_succ, List.foldl_append, st]
      rw [hst_next]
      have hcol : t < C := by omega
      let c0 : Fin C := ⟨t, hcol⟩
      let cond : Fin R → Bool := fun r => !(st.used r) && z2b (st.M r c0)
      rcases gaussStep_spec t hcol st with ⟨hused, hnone, hsome⟩
      by_cases hex : ∃ r : Fin R, cond r = true
      · rcases (exists_firstTrue_iff cond).mpr hex with ⟨p0, hp0⟩
        rcases hsome p0 hp0 with ⟨hMp0, hPp0, hother⟩
        have hp0_cond := ((firstTrue_spec cond p0).mp hp0).1
        have hp0_unused : st.used p0 = false := by
          simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hp0_cond
          exact hp0_cond.1
        have hp0_one : st.M p0 c0 = 1 := by
          simp only [cond, Bool.and_eq_true] at hp0_cond
          have := hp0_cond.2
          rcases z2_cases (st.M p0 c0) with h | h
          · simp [h, z2b_zero] at this
          · exact h
        have hstep_span : Submodule.span (ZMod 2) (Set.range (gaussStep t st).M) =
            Submodule.span (ZMod 2) (Set.range st.M) := by
          apply le_antisymm
          · rw [Submodule.span_le]
            rintro _ ⟨r, rfl⟩
            by_cases hr : r = p0
            · subst hr; rw [hMp0]; exact Submodule.subset_span ⟨r, rfl⟩
            · rw [(hother r hr).1]
              exact Submodule.add_mem _ (Submodule.subset_span ⟨r, rfl⟩)
                (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p0, rfl⟩))
          · rw [Submodule.span_le]
            rintro _ ⟨r, rfl⟩
            by_cases hr : r = p0
            · subst hr; rw [← hMp0]; exact Submodule.subset_span ⟨r, rfl⟩
            · have heq : st.M r = (gaussStep t st).M r + (st.M r c0) • (gaussStep t st).M p0 := by
                rw [(hother r hr).1, hMp0, add_assoc]
                have h2 : (st.M r c0) • st.M p0 + (st.M r c0) • st.M p0 = 0 := by
                  funext c; simp [z2_add_self]
                rw [h2, add_zero]
              rw [heq]
              exact Submodule.add_mem _ (Submodule.subset_span ⟨r, rfl⟩)
                (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p0, rfl⟩))
        refine ⟨hstep_span.trans hspan, ?_, ?_, ?_, ?_⟩
        · intro r hr
          rcases (hused r).mp hr with hr_old | hr_new
          · rcases hpiv r hr_old with ⟨c, hct, hrc1, hoth⟩
            have hp0_ne : p0 ≠ r := fun h => by rw [h, hr_old] at hp0_unused; exact Bool.noConfusion hp0_unused
            have hp0c0 : st.M p0 c = 0 := hoth p0 hp0_ne
            refine ⟨c, by omega, ?_, ?_⟩
            · have hrp0 : r ≠ p0 := Ne.symm hp0_ne
              have := congrFun (hother r hrp0).1 c
              rw [this, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp0c0, mul_zero, add_zero, hrc1]
            · intro j hj
              by_cases hjp0 : j = p0
              · subst hjp0; rw [hMp0]; exact hp0c0
              · have := congrFun (hother j hjp0).1 c
                rw [this, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp0c0, mul_zero, add_zero, hoth j hj]
          · have hrp0 : r = p0 := firstTrue_unique cond hr_new hp0
            subst hrp0
            refine ⟨c0, by simp [c0], by rw [hMp0]; exact hp0_one, ?_⟩
            intro j hj
            have := congrFun (hother j hj).1 c0
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp0_one, mul_one] at this
            rw [this, z2_add_self]
        · intro r hr c hc
          have hr_old : st.used r = false := by
            cases hu : st.used r
            · rfl
            · have := (hused r).mpr (Or.inl hu)
              rw [hr] at this; exact Bool.noConfusion this
          have hr_ne : r ≠ p0 := by
            intro h; subst h
            have := (hused r).mpr (Or.inr hp0)
            rw [hr] at this; exact Bool.noConfusion this
          have hm := congrFun (hother r hr_ne).1 c
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
          by_cases hct : c.val < t
          · rw [hm, hzero r hr_old c hct, hzero p0 hp0_unused c hct, mul_zero, add_zero]
          · have hce : c = c0 := Fin.ext (by dsimp [c0]; omega)
            subst hce
            rw [hm, hp0_one, mul_one, z2_add_self]
        · intro α _ _ f hf
          rw [← hlin α f hf]
          have hscale : ∀ (s : ZMod 2) m1 m2 p1 p2,
              f (m1 + s • m2) (p1 + s • p2) = f m1 p1 + s • f m2 p2 := by
            intro s m1 m2 p1 p2
            rcases z2_cases s with rfl | rfl
            · simp
            · simpa using hf m1 m2 p1 p2
          constructor
          · intro hall r
            by_cases hr : r = p0
            · subst hr; rw [← hMp0, ← hPp0]; exact hall r
            · have h1 := hall r
              have h2 := hall p0
              rw [(hother r hr).1, (hother r hr).2, hscale, ← hMp0, ← hPp0, h2, smul_zero, add_zero] at h1
              exact h1
          · intro hall r
            by_cases hr : r = p0
            · subst hr; rw [hMp0, hPp0]; exact hall r
            · rw [(hother r hr).1, (hother r hr).2, hscale, hall r, hall p0, smul_zero, add_zero]
        · intro PropRow hP0 hPadd hPM0 r
          have hPrev := hprop PropRow hP0 hPadd hPM0
          by_cases hr : r = p0
          · subst hr; rw [hMp0]; exact hPrev r
          · rw [(hother r hr).1]
            rcases z2_cases (st.M r c0) with h0 | h1
            · rw [h0, zero_smul, add_zero]; exact hPrev r
            · rw [h1, one_smul]; exact hPadd _ _ (hPrev r) (hPrev p0)
      · push Not at hex
        have hallf : ∀ r, cond r = false := fun r => by
          cases h : cond r
          · rfl
          · exact absurd h (hex r)
        rw [hnone hallf]
        refine ⟨hspan, ?_, ?_, hlin, hprop⟩
        · intro r hr
          rcases hpiv r hr with ⟨c, hct, h1, h2⟩
          exact ⟨c, by omega, h1, h2⟩
        · intro r hr c hc
          by_cases hct : c.val < t
          · exact hzero r hr c hct
          · have hce : c = c0 := Fin.ext (by dsimp [c0]; omega)
            subst hce
            have hcf := hallf r
            simp only [cond, hr, Bool.not_false, Bool.true_and] at hcf
            rcases z2_cases (st.M r c0) with h | h
            · exact h
            · simp [h, z2b_one] at hcf
  rcases hloop C le_rfl with ⟨hspan, hpiv, hzero, hlin, hprop⟩
  refine ⟨hspan, ?_, ?_, hlin, hprop⟩
  · intro r hr
    rcases hpiv r hr with ⟨c, _, h1, h2⟩
    exact ⟨c, h1, h2⟩
  · intro r hr c
    exact hzero r hr c c.isLt

theorem gaussElim_rank_eq {R C P : ℕ}
    (M0 : Fin R → Fin C → ZMod 2) (Pay0 : Fin R → Fin P → ZMod 2) :
    let st := gaussElim M0 Pay0
    (Finset.univ.filter (fun r : Fin R => st.used r = true)).card =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M0)) := by
  classical
  intro st
  rcases gaussElim_invariants M0 Pay0 with ⟨hspan, hpiv, hzero, _, _⟩
  let U : Finset (Fin R) := Finset.univ.filter (fun r : Fin R => st.used r = true)
  let S : Submodule (ZMod 2) (Fin C → ZMod 2) := Submodule.span (ZMod 2) (Set.range M0)
  have hmemS : ∀ r : U, st.M r.val ∈ S := by
    intro r
    change st.M r.val ∈ Submodule.span (ZMod 2) (Set.range M0)
    rw [← hspan]
    exact Submodule.subset_span ⟨r.val, rfl⟩
  let v : U → S := fun r => ⟨st.M r.val, hmemS r⟩
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha r
    have hval := congrArg Subtype.val ha
    simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, v] at hval
    rcases hpiv r.val (Finset.mem_filter.mp r.2).2 with ⟨c, h1, hoth⟩
    have hc := congrFun hval c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
    rw [Finset.sum_eq_single r] at hc
    · change a r * (gaussElim M0 Pay0).M r.val c = 0 at hc
      rw [h1, mul_one] at hc
      exact hc
    · intro j _ hj
      have hne : j.val ≠ r.val := fun h => hj (Subtype.ext h)
      change a j * (gaussElim M0 Pay0).M j.val c = 0
      rw [hoth j.val hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    rintro ⟨y, hy⟩ _
    have hy' : y ∈ Submodule.span (ZMod 2) (Set.range st.M) := by rwa [hspan]
    have hmap : Submodule.span (ZMod 2) (Set.range st.M) ≤
        Submodule.map S.subtype (Submodule.span (ZMod 2) (Set.range v)) := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      by_cases hu : st.used r = true
      · have hrU : r ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
        exact ⟨v ⟨r, hrU⟩, Submodule.subset_span ⟨⟨r, hrU⟩, rfl⟩, rfl⟩
      · have huf : st.used r = false := by cases h : st.used r <;> simp_all
        have hr0 : st.M r = 0 := funext (hzero r huf)
        rw [hr0]
        exact Submodule.zero_mem _
    rcases hmap hy' with ⟨w, hw, hwy⟩
    have : w = ⟨y, hy⟩ := Subtype.ext hwy
    rwa [← this]
  let b : Module.Basis U (ZMod 2) S := Module.Basis.mk hli htop
  have hcard : Fintype.card U = Module.finrank (ZMod 2) S := (Module.finrank_eq_card_basis b).symm
  rw [← Fintype.card_coe]
  exact hcard

def gaussSigs {N R C P : ℕ} (st : (Fin N → Bool) → GaussState R C P) : Set (Sig N) :=
  Set.range (fun r : Fin R => fun x => (st x).used r) ∪
  {f | ∃ r c, (fun x => z2b ((st x).M r c)) = f} ∪
  {f | ∃ r p, (fun x => z2b ((st x).Pay r p)) = f}

theorem gaussStepB {N R C P : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (col : ℕ) (st : (Fin N → Bool) → GaussState R C P) :
    Build (Base ∪ gaussSigs st) (gaussSigs (fun x => gaussStep col (st x)))
      (R * (R + 4) + (C + P) * (2 * R) + R * (1 + (C + P) * 10)) := by
  by_cases hcol : col < C
  · let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin R → Sig N := fun r x => !((st x).used r) && z2b ((st x).M r c0)
    let isPiv : Fin R → Sig N := fun r x => firstTrue (fun j => cond j x) r
    let pivM : Fin C → Sig N := fun c x =>
      (List.finRange R).any (fun r => isPiv r x && z2b ((st x).M r c))
    let pivP : Fin P → Sig N := fun p x =>
      (List.finRange R).any (fun r => isPiv r x && z2b ((st x).Pay r p))
    have hcondB : Build (Base ∪ gaussSigs st) (Set.range cond) (R * 2) := by
      refine finSigB cond 2 (fun r => ?_)
      have h1 : Build (Base ∪ gaussSigs st) {fun x => !((st x).used r)} 1 :=
        notB (Or.inr (Or.inl (Or.inl ⟨r, rfl⟩)))
      have h2 : Build ((Base ∪ gaussSigs st) ∪ {fun x => !((st x).used r)}) {cond r} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))
      exact seq2B h1 h2
    have hftB : Build ((Base ∪ gaussSigs st) ∪ Set.range cond) (Set.range isPiv) (R * (R + 2)) :=
      firstTrueB cond (Or.inl (Or.inl hfalse)) (fun r => Or.inr ⟨r, rfl⟩)
    let A1 := (Base ∪ gaussSigs st) ∪ (Set.range cond ∪ Set.range isPiv)
    have h1 : Build (Base ∪ gaussSigs st) (Set.range cond ∪ Set.range isPiv) (R * 2 + R * (R + 2)) :=
      seqB hcondB hftB
    have hpivMB : Build A1 (Set.range pivM) (C * (2 * R)) := by
      refine finSigB pivM (2 * R) (fun c => ?_)
      let term : Fin R → Sig N := fun r x => isPiv r x && z2b ((st x).M r c)
      have ht : Build A1 (Set.range term) (R * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c, rfl⟩)))))
      have hor : Build (A1 ∪ Set.range term) {pivM c} R := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange R).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange R).map term).any (fun f => f x)) = pivM c := by
          funext x; simp [pivM, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have hpivPB : Build A1 (Set.range pivP) (P * (2 * R)) := by
      refine finSigB pivP (2 * R) (fun p => ?_)
      let term : Fin R → Sig N := fun r x => isPiv r x && z2b ((st x).Pay r p)
      have ht : Build A1 (Set.range term) (R * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inr ⟨r, p, rfl⟩))))
      have hor : Build (A1 ∪ Set.range term) {pivP p} R := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange R).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange R).map term).any (fun f => f x)) = pivP p := by
          funext x; simp [pivP, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have h2 : Build A1 (Set.range pivM ∪ Set.range pivP) (C * (2 * R) + P * (2 * R)) :=
      unionB hpivMB hpivPB
    let A2 := A1 ∪ (Set.range pivM ∪ Set.range pivP)
    have h3 : Build A2 (gaussSigs (fun x => gaussStep col (st x))) (R * (1 + (C + P) * 10)) := by
      have husedB : Build A2 (Set.range (fun r : Fin R => fun x => (gaussStep col (st x)).used r)) (R * 1) :=
        finSigB _ 1 (fun r => by
          have heq : (fun x => (gaussStep col (st x)).used r) = fun x => (st x).used r || isPiv r x := by
            funext x; simp [gaussStep, hcol, isPiv, cond, c0]
          rw [heq]
          exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨r, rfl⟩)))))
            (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩))))
      have hMB : Build A2 {f | ∃ r c, (fun x => z2b ((gaussStep col (st x)).M r c)) = f} (R * (C * 10)) :=
        fin2SigB _ 10 (fun r c => by
          let np : Sig N := fun x => !(isPiv r x)
          let flag : Sig N := fun x => np x && z2b ((st x).M r c0)
          let xored : Sig N := fun x => xor (z2b ((st x).M r c)) (pivM c x)
          let out : Sig N := fun x => if flag x then xored x else z2b ((st x).M r c)
          have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
          have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))))
          have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {xored} 4 :=
            xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c, rfl⟩)))))))
              (Or.inl (Or.inl (Or.inr (Or.inl ⟨c, rfl⟩))))
          have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4 :=
            iteB (Or.inl (Or.inr rfl)) (Or.inr rfl)
              (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c, rfl⟩))))))))
          have heq : out = fun x => z2b ((gaussStep col (st x)).M r c) := by
            funext x
            simp only [out, flag, np, xored, gaussStep, hcol, ↓reduceDIte, isPiv, cond, c0, pivM]
            cases hf : (!(firstTrue (fun j => !((st x).used j) && z2b ((st x).M j c0)) r) &&
                z2b ((st x).M r c0)) <;> simp [z2b_add, z2b_b2z]
          rw [← heq]
          exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
            le_rfl Set.subset_union_right (by omega))
      have hPB : Build A2 {f | ∃ r p, (fun x => z2b ((gaussStep col (st x)).Pay r p)) = f} (R * (P * 10)) :=
        fin2SigB _ 10 (fun r p => by
          let np : Sig N := fun x => !(isPiv r x)
          let flag : Sig N := fun x => np x && z2b ((st x).M r c0)
          let xored : Sig N := fun x => xor (z2b ((st x).Pay r p)) (pivP p x)
          let out : Sig N := fun x => if flag x then xored x else z2b ((st x).Pay r p)
          have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
          have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))))
          have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {xored} 4 :=
            xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨r, p, rfl⟩))))))
              (Or.inl (Or.inl (Or.inr (Or.inr ⟨p, rfl⟩))))
          have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4 :=
            iteB (Or.inl (Or.inr rfl)) (Or.inr rfl)
              (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨r, p, rfl⟩)))))))
          have heq : out = fun x => z2b ((gaussStep col (st x)).Pay r p) := by
            funext x
            simp only [out, flag, np, xored, gaussStep, hcol, ↓reduceDIte, isPiv, cond, c0, pivP]
            cases hf : (!(firstTrue (fun j => !((st x).used j) && z2b ((st x).M j c0)) r) &&
                z2b ((st x).M r c0)) <;> simp [z2b_add, z2b_b2z]
          rw [← heq]
          exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
            le_rfl Set.subset_union_right (by omega))
      exact relaxB (unionB (unionB husedB hMB) hPB) le_rfl Set.subset_union_right
        (by ring_nf; omega)
    have hall := transB (transB (extB h1) (extB h2)) h3
    exact relaxB hall le_rfl Set.subset_union_right (by ring_nf; omega)
  · have heq : (fun x => gaussStep col (st x)) = st := by
      funext x; simp [gaussStep, hcol]
    rw [heq]
    exact relaxB (idleB (A := Base ∪ gaussSigs st) (B := gaussSigs st) Set.subset_union_right)
      le_rfl Set.subset_union_right (Nat.zero_le _)

theorem gaussElimB {N R C P : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (M0 : (Fin N → Bool) → Fin R → Fin C → ZMod 2)
    (Pay0 : (Fin N → Bool) → Fin R → Fin P → ZMod 2)
    (hM0 : ∀ r c, (fun x => z2b (M0 x r c)) ∈ Base)
    (hPay0 : ∀ r p, (fun x => z2b (Pay0 x r p)) ∈ Base) :
    Build Base (gaussSigs (fun x => gaussElim (M0 x) (Pay0 x)))
      (C * (R * (R + 4) + (C + P) * (2 * R) + R * (1 + (C + P) * 10))) := by
  let st0 : (Fin N → Bool) → GaussState R C P := fun x => ⟨fun _ => false, M0 x, Pay0 x⟩
  have hst0 : gaussSigs st0 ⊆ Base := by
    rintro f ((⟨r, rfl⟩ | ⟨r, c, rfl⟩) | ⟨r, p, rfl⟩)
    · exact hfalse
    · exact hM0 r c
    · exact hPay0 r p
  have hit := iterB (Sigs := gaussSigs) (step := gaussStep)
    (c := R * (R + 4) + (C + P) * (2 * R) + R * (1 + (C + P) * 10))
    (Base := Base) (fun col st => gaussStepB Base hfalse col st) C st0
  exact relaxB hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl

def quadSigs {N m : ℕ} (Q : (Fin N → Bool) → Quad m) : Set (Sig N) :=
  {f | ∃ i j, (fun x => z2b ((Q x).B i j)) = f} ∪
  Set.range (fun i : Fin m => fun x => z2b ((Q x).l i)) ∪
  {fun x => z2b (Q x).c}

theorem addAffineProdB {N m : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (Q : (Fin N → Bool) → Quad m)
    (e0 f0 : (Fin N → Bool) → ZMod 2)
    (e f : (Fin N → Bool) → Fin m → ZMod 2)
    (hQ : quadSigs Q ⊆ Base)
    (he0 : (fun x => z2b (e0 x)) ∈ Base)
    (hf0 : (fun x => z2b (f0 x)) ∈ Base)
    (he : ∀ i, (fun x => z2b (e x i)) ∈ Base)
    (hf : ∀ i, (fun x => z2b (f x i)) ∈ Base) :
    Build Base (quadSigs (fun x => (Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)))
      (m * (m * 10) + m * 15 + 5) := by
  have hBB : Build Base
      {g | ∃ i j, (fun x => z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j)) = g}
      (m * (m * 10)) := by
    refine fin2SigB _ 10 (fun i j => ?_)
    by_cases hij : i = j
    · have heq : (fun x => z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j)) =
          fun _ => false := by
        funext x; simp [Quad.addAffineProd, hij, z2b_zero]
      rw [heq]
      exact relaxB (idleB (A := Base) (B := {fun _ => false}) (by simpa using hfalse))
        le_rfl Set.subset_union_right (by omega)
    · let t1 : Sig N := fun x => z2b (e x i) && z2b (f x j)
      let t2 : Sig N := fun x => z2b (e x j) && z2b (f x i)
      let s1 : Sig N := fun x => xor (z2b ((Q x).B i j)) (t1 x)
      let s2 : Sig N := fun x => xor (s1 x) (t2 x)
      have h1 : Build Base {t1} 1 := andB (he i) (hf j)
      have h2 : Build (Base ∪ {t1}) {t2} 1 := andB (Or.inl (he j)) (Or.inl (hf i))
      have h3 : Build ((Base ∪ {t1}) ∪ {t2}) {s1} 4 :=
        xorB (Or.inl (Or.inl (hQ (Or.inl (Or.inl ⟨i, j, rfl⟩))))) (Or.inl (Or.inr rfl))
      have h4 : Build (((Base ∪ {t1}) ∪ {t2}) ∪ {s1}) {s2} 4 :=
        xorB (Or.inr rfl) (Or.inl (Or.inr rfl))
      have heq : s2 = fun x => z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).B i j) := by
        funext x
        simp only [s2, s1, t1, t2, Quad.addAffineProd, hij, ↓reduceIte, z2b_add, z2b_mul]
      rw [← heq]
      exact relaxB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) h4)
        le_rfl Set.subset_union_right (by omega)
  have hll : Build Base
      (Set.range (fun i : Fin m => fun x => z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).l i)))
      (m * 15) := by
    refine finSigB _ 15 (fun i => ?_)
    let t1 : Sig N := fun x => z2b (e0 x) && z2b (f x i)
    let t2 : Sig N := fun x => z2b (f0 x) && z2b (e x i)
    let t3 : Sig N := fun x => z2b (e x i) && z2b (f x i)
    let s1 : Sig N := fun x => xor (z2b ((Q x).l i)) (t1 x)
    let s2 : Sig N := fun x => xor (s1 x) (t2 x)
    let s3 : Sig N := fun x => xor (s2 x) (t3 x)
    have h1 : Build Base {t1} 1 := andB he0 (hf i)
    have h2 : Build (Base ∪ {t1}) {t2} 1 := andB (Or.inl hf0) (Or.inl (he i))
    have h3 : Build ((Base ∪ {t1}) ∪ {t2}) {t3} 1 := andB (Or.inl (Or.inl (he i))) (Or.inl (Or.inl (hf i)))
    have h4 : Build (((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) {s1} 4 :=
      xorB (Or.inl (Or.inl (Or.inl (hQ (Or.inl (Or.inr ⟨i, rfl⟩)))))) (Or.inl (Or.inl (Or.inr rfl)))
    have h5 : Build ((((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) ∪ {s1}) {s2} 4 :=
      xorB (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))
    have h6 : Build (((((Base ∪ {t1}) ∪ {t2}) ∪ {t3}) ∪ {s1}) ∪ {s2}) {s3} 4 :=
      xorB (Or.inr rfl) (Or.inl (Or.inl (Or.inr rfl)))
    have heq : s3 = fun x => z2b (((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).l i) := by
      funext x
      simp only [s3, s2, s1, t1, t2, t3, Quad.addAffineProd, z2b_add, z2b_mul]
    rw [← heq]
    exact relaxB (transB (transB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) (extB h4)) (extB h5)) h6)
      le_rfl Set.subset_union_right (by omega)
  have hcc : Build Base {fun x => z2b ((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).c} 5 := by
    let t1 : Sig N := fun x => z2b (e0 x) && z2b (f0 x)
    let s1 : Sig N := fun x => xor (z2b (Q x).c) (t1 x)
    have h1 : Build Base {t1} 1 := andB he0 hf0
    have h2 : Build (Base ∪ {t1}) {s1} 4 := xorB (Or.inl (hQ (Or.inr rfl))) (Or.inr rfl)
    have heq : s1 = fun x => z2b ((Q x).addAffineProd (e0 x) (e x) (f0 x) (f x)).c := by
      funext x; simp [s1, t1, Quad.addAffineProd, z2b_add, z2b_mul]
    rw [← heq]
    exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by omega)
  exact relaxB (unionB (unionB hBB hll) hcc) le_rfl Set.subset_union_right (by omega)

def shiftOneHot {L : ℕ} (p : Fin (L + 1) → Bool) : Fin (L + 1) → Bool :=
  fun k => if h0 : k.val = 0 then false else p ⟨k.val - 1, by omega⟩

theorem shiftOneHot_spec {L e : ℕ} (_he : e < L) :
    shiftOneHot (fun k : Fin (L + 1) => decide (k.val = e)) =
      fun k : Fin (L + 1) => decide (k.val = e + 1) := by
  funext k
  unfold shiftOneHot
  by_cases h0 : k.val = 0
  · simp [h0]
  · simp only [h0, ↓reduceDIte]
    by_cases hk : k.val = e + 1
    · simp [hk]
    · simp only [hk, decide_false, decide_eq_false_iff_not]; omega

structure PackState (m h : ℕ) where
  cnt : Fin (h + 1) → Bool
  qs : Fin h → Quad m

def packStep {t m h : ℕ} (used : Fin t → Bool) (rowQ : Fin t → Quad m)
    (j : ℕ) (st : PackState m h) : PackState m h :=
  if hj : j < t then
    let j0 : Fin t := ⟨j, hj⟩
    let u := used j0
    { cnt := fun v => if u then shiftOneHot st.cnt v else st.cnt v
      qs := fun s =>
        if u && st.cnt s.castSucc then rowQ j0 else st.qs s }
  else st

def packUsed {t m h : ℕ} (used : Fin t → Bool) (rowQ : Fin t → Quad m) :
    PackState m h :=
  (List.range t).foldl (fun st j => packStep used rowQ j st)
    ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩

theorem packUsed_valid {t m h : ℕ} (used : Fin t → Bool) (rowQ : Fin t → Quad m)
    (hvalid : ∀ j, (rowQ j).Valid) :
    ∀ s : Fin h, ((packUsed used rowQ).qs s).Valid := by
  have hloop : ∀ r, ∀ s : Fin h,
      (((List.range r).foldl (fun st j => packStep used rowQ j st)
        ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩).qs s).Valid := by
    intro r
    induction r with
    | zero => intro _; exact Quad.valid_zero m
    | succ r ih =>
      intro s
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      unfold packStep
      by_cases hr : r < t
      · simp only [hr, ↓reduceDIte]
        split_ifs
        · exact hvalid ⟨r, hr⟩
        · exact ih s
      · simp only [hr, ↓reduceDIte]; exact ih s
  exact hloop t

theorem packUsed_spec {t m h : ℕ} (used : Fin t → Bool) (rowQ : Fin t → Quad m)
    (hvalid : ∀ j, (rowQ j).Valid)
    (hcnt : (Finset.univ.filter (fun j : Fin t => used j = true)).card ≤ h) :
    let st : PackState m h := packUsed used rowQ
    (∀ s : Fin h, (st.qs s).Valid) ∧
    ∀ a : Fin m → ZMod 2,
      (∀ j : Fin t, used j = true → (rowQ j).eval a = 0) ↔
      (∀ s : Fin h, (st.qs s).eval a = 0) := by
  have hloop : ∀ r ≤ t,
      let st : PackState m h := (List.range r).foldl (fun s j => packStep used rowQ j s)
        ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩
      let kr := (Finset.univ.filter (fun j : Fin t => j.val < r ∧ used j = true)).card
      st.cnt = (fun v : Fin (h + 1) => decide (v.val = kr)) ∧
      (∀ s : Fin h, kr ≤ s.val → st.qs s = Quad.zero m) ∧
      (∀ s : Fin h, (st.qs s).Valid) ∧
      (∀ a : Fin m → ZMod 2,
        (∀ j : Fin t, j.val < r → used j = true → (rowQ j).eval a = 0) ↔
        (∀ s : Fin h, (st.qs s).eval a = 0)) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨by simp, fun _ _ => rfl, fun _ => Quad.valid_zero m, fun a => ?_⟩
      constructor
      · intro _ s; exact Quad.eval_zero a
      · intro _ j hj; omega
    | succ r ih =>
      intro hr
      rcases ih (by omega) with ⟨hcnt_eq, hzero_tail, hval_prev, hequiv_prev⟩
      set st : PackState m h := (List.range r).foldl (fun s j => packStep used rowQ j s)
        ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩
      have hst_next : (List.range (r + 1)).foldl (fun s j => packStep used rowQ j s)
          ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩ = packStep used rowQ r st := by
        simp [List.range_succ, List.foldl_append, st]
      rw [hst_next]
      have hrt : r < t := by omega
      let j0 : Fin t := ⟨r, hrt⟩
      set Sr := Finset.univ.filter (fun j : Fin t => j.val < r ∧ used j = true)
      set Sr1 := Finset.univ.filter (fun j : Fin t => j.val < r + 1 ∧ used j = true)
      have hSr1_le : Sr1.card ≤ h := by
        calc
          Sr1.card ≤ (Finset.univ.filter (fun j : Fin t => used j = true)).card := by
            refine Finset.card_le_card ?_
            intro j hj
            simp only [Sr1, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact hj.2
          _ ≤ h := hcnt
      by_cases hu : used j0 = true
      · have hSr1_eq : Sr1 = insert j0 Sr := by
          ext j
          simp only [Sr1, Sr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hju⟩
            by_cases hje : j.val = r
            · left; exact Fin.ext hje
            · right; exact ⟨by omega, hju⟩
          · rintro (rfl | ⟨hlt, hju⟩)
            · exact ⟨by simp [j0], hu⟩
            · exact ⟨by omega, hju⟩
        have hj0_not : j0 ∉ Sr := by simp [Sr, j0]
        have hk_succ : Sr1.card = Sr.card + 1 := by
          rw [hSr1_eq, Finset.card_insert_of_notMem hj0_not]
        have hk_lt : Sr.card < h := by omega
        have hstep_cnt : (packStep used rowQ r st).cnt =
            fun v : Fin (h + 1) => decide (v.val = Sr1.card) := by
          funext v
          simp only [packStep, hrt, ↓reduceDIte, j0, hu, ↓reduceIte, hk_succ]
          rw [hcnt_eq]
          exact congrFun (shiftOneHot_spec hk_lt) v
        have hstep_qs : ∀ s : Fin h, (packStep used rowQ r st).qs s =
            if s.val = Sr.card then rowQ j0 else st.qs s := by
          intro s
          simp only [packStep, hrt, ↓reduceDIte, j0, hu, Bool.true_and]
          rw [hcnt_eq]
          by_cases hs : s.val = Sr.card <;> simp [hs]
        refine ⟨hstep_cnt, ?_, ?_, ?_⟩
        · intro s hs
          rw [hstep_qs s]
          have hne : s.val ≠ Sr.card := by omega
          simp only [hne, ↓reduceIte]
          exact hzero_tail s (by omega)
        · intro s
          rw [hstep_qs s]
          by_cases hs : s.val = Sr.card
          · simp only [hs, ↓reduceIte]; exact hvalid j0
          · simp only [hs, ↓reduceIte]; exact hval_prev s
        · intro a
          constructor
          · intro hall s
            rw [hstep_qs s]
            by_cases hs : s.val = Sr.card
            · simp only [hs, ↓reduceIte]
              exact hall j0 (by simp [j0]) hu
            · simp only [hs, ↓reduceIte]
              exact (hequiv_prev a).mp (fun j hj hju => hall j (by omega) hju) s
          · intro hall j hj hju
            by_cases hjr : j.val = r
            · have hje : j = j0 := Fin.ext hjr
              subst hje
              have hslot := hall ⟨Sr.card, hk_lt⟩
              rw [hstep_qs ⟨Sr.card, hk_lt⟩] at hslot
              simpa using hslot
            · refine (hequiv_prev a).mpr ?_ j (by omega) hju
              intro s
              by_cases hs : s.val = Sr.card
              · rw [hzero_tail s (by omega)]
                exact Quad.eval_zero a
              · have hslot := hall s
                rw [hstep_qs s] at hslot
                simpa [hs] using hslot
      · have huf : used j0 = false := by cases h' : used j0 <;> simp_all
        have hSr1_eq : Sr1 = Sr := by
          ext j
          simp only [Sr1, Sr, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hju⟩
            refine ⟨?_, hju⟩
            by_contra hge
            have hje : j = j0 := Fin.ext (by dsimp [j0]; omega)
            rw [hje, huf] at hju
            exact Bool.noConfusion hju
          · rintro ⟨hlt, hju⟩
            exact ⟨by omega, hju⟩
        have hst_eq : packStep used rowQ r st = st := by
          unfold packStep
          simp only [hrt, ↓reduceDIte]
          have huf' : used ⟨r, hrt⟩ = false := huf
          simp [huf']
        rw [hst_eq, hSr1_eq]
        refine ⟨hcnt_eq, hzero_tail, hval_prev, fun a => ?_⟩
        rw [← hequiv_prev a]
        constructor
        · intro hall j hj hju; exact hall j (by omega) hju
        · intro hall j hj hju
          by_cases hjr : j.val = r
          · have hje : j = j0 := Fin.ext hjr
            rw [hje, huf] at hju
            exact Bool.noConfusion hju
          · exact hall j (by omega) hju
  rcases hloop t le_rfl with ⟨_, _, hval, hequiv⟩
  refine ⟨hval, fun a => ?_⟩
  dsimp only [packUsed]
  rw [← hequiv a]
  constructor
  · intro h j _ hu; exact h j hu
  · intro h j hu; exact h j j.isLt hu

def packSigs {N m h : ℕ} (st : (Fin N → Bool) → PackState m h) : Set (Sig N) :=
  Set.range (fun v : Fin (h + 1) => fun x => (st x).cnt v) ∪
  ⋃ s : Fin h, quadSigs (fun x => (st x).qs s)

theorem packStepB {N t m h : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (used : (Fin N → Bool) → Fin t → Bool)
    (rowQ : (Fin N → Bool) → Fin t → Quad m)
    (hused : ∀ j, (fun x => used x j) ∈ Base)
    (hrowQ : ∀ j, quadSigs (fun x => rowQ x j) ⊆ Base)
    (j : ℕ) (st : (Fin N → Bool) → PackState m h) :
    Build (Base ∪ packSigs st) (packSigs (fun x => packStep (used x) (rowQ x) j (st x)))
      ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4))) := by
  by_cases hj : j < t
  · let j0 : Fin t := ⟨j, hj⟩
    have hcntB : Build (Base ∪ packSigs st)
        (Set.range (fun v : Fin (h + 1) => fun x => (packStep (used x) (rowQ x) j (st x)).cnt v))
        ((h + 1) * 4) := by
      refine finSigB _ 4 (fun v => ?_)
      have hsh : (fun x => shiftOneHot (st x).cnt v) ∈ Base ∪ packSigs st := by
        unfold shiftOneHot
        by_cases h0 : v.val = 0
        · simp only [h0, ↓reduceDIte]; exact Or.inl hfalse
        · simp only [h0, ↓reduceDIte]; exact Or.inr (Or.inl ⟨⟨v.val - 1, by omega⟩, rfl⟩)
      have heq : (fun x => (packStep (used x) (rowQ x) j (st x)).cnt v) =
          fun x => if used x j0 then shiftOneHot (st x).cnt v else (st x).cnt v := by
        funext x; simp [packStep, hj, j0]
      rw [heq]
      exact iteB (Or.inl (hused j0)) hsh (Or.inr (Or.inl ⟨v, rfl⟩))
    have hqsB : Build (Base ∪ packSigs st)
        (⋃ s : Fin h, quadSigs (fun x => (packStep (used x) (rowQ x) j (st x)).qs s))
        (h * (1 + (m * (m * 4) + m * 4 + 4))) := by
      refine finB _ (1 + (m * (m * 4) + m * 4 + 4)) (fun s => ?_)
      let flag : Sig N := fun x => used x j0 && (st x).cnt s.castSucc
      have hflag : Build (Base ∪ packSigs st) {flag} 1 :=
        andB (Or.inl (hused j0)) (Or.inr (Or.inl ⟨s.castSucc, rfl⟩))
      let A1 := (Base ∪ packSigs st) ∪ {flag}
      have hqB : Build A1 (quadSigs (fun x => (packStep (used x) (rowQ x) j (st x)).qs s))
          (m * (m * 4) + m * 4 + 4) := by
        have hB : Build A1
            {f | ∃ a b, (fun x => z2b (((packStep (used x) (rowQ x) j (st x)).qs s).B a b)) = f}
            (m * (m * 4)) :=
          fin2SigB _ 4 (fun a b => by
            have heq : (fun x => z2b (((packStep (used x) (rowQ x) j (st x)).qs s).B a b)) =
                fun x => if flag x then z2b ((rowQ x j0).B a b) else z2b (((st x).qs s).B a b) := by
              funext x
              simp only [packStep, hj, ↓reduceDIte, j0, flag]
              cases used x j0 && (st x).cnt s.castSucc <;> simp
            rw [heq]
            exact iteB (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inl (Or.inl ⟨a, b, rfl⟩)))))
              (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inl ⟨a, b, rfl⟩)⟩)))))
        have hL : Build A1
            (Set.range (fun a : Fin m => fun x => z2b (((packStep (used x) (rowQ x) j (st x)).qs s).l a)))
            (m * 4) :=
          finSigB _ 4 (fun a => by
            have heq : (fun x => z2b (((packStep (used x) (rowQ x) j (st x)).qs s).l a)) =
                fun x => if flag x then z2b ((rowQ x j0).l a) else z2b (((st x).qs s).l a) := by
              funext x
              simp only [packStep, hj, ↓reduceDIte, j0, flag]
              cases used x j0 && (st x).cnt s.castSucc <;> simp
            rw [heq]
            exact iteB (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inl (Or.inr ⟨a, rfl⟩)))))
              (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inr ⟨a, rfl⟩)⟩)))))
        have hC : Build A1
            {fun x => z2b ((packStep (used x) (rowQ x) j (st x)).qs s).c} 4 := by
          have heq : (fun x => z2b ((packStep (used x) (rowQ x) j (st x)).qs s).c) =
              fun x => if flag x then z2b (rowQ x j0).c else z2b ((st x).qs s).c := by
            funext x
            simp only [packStep, hj, ↓reduceDIte, j0, flag]
            cases used x j0 && (st x).cnt s.castSucc <;> simp
          rw [heq]
          exact iteB (Or.inr rfl) (Or.inl (Or.inl (hrowQ j0 (Or.inr rfl))))
            (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inr rfl⟩))))
        exact relaxB (unionB (unionB hB hL) hC) le_rfl Set.subset_union_right (by omega)
      exact seq2B hflag hqB
    exact unionB hcntB hqsB
  · have heq : (fun x => packStep (used x) (rowQ x) j (st x)) = st := by
      funext x; simp [packStep, hj]
    rw [heq]
    exact relaxB (idleB (A := Base ∪ packSigs st) (B := packSigs st) Set.subset_union_right)
      le_rfl Set.subset_union_right (Nat.zero_le _)

theorem packUsedB {N t m h : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (used : (Fin N → Bool) → Fin t → Bool)
    (rowQ : (Fin N → Bool) → Fin t → Quad m)
    (hused : ∀ j, (fun x => used x j) ∈ Base)
    (hrowQ : ∀ j, quadSigs (fun x => rowQ x j) ⊆ Base) :
    Build Base (packSigs (h := h) (fun x => packUsed (used x) (rowQ x)))
      (t * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4)))) := by
  let st0 : (Fin N → Bool) → PackState m h :=
    fun _ => ⟨fun v => decide (v.val = 0), fun _ => Quad.zero m⟩
  have hst0 : packSigs st0 ⊆ Base := by
    rintro f (⟨v, rfl⟩ | hq)
    · by_cases hv : v.val = 0
      · simpa [st0, hv] using htrue
      · simpa [st0, hv] using hfalse
    · rcases Set.mem_iUnion.mp hq with ⟨s, ((⟨a, b, rfl⟩ | ⟨a, rfl⟩) | rfl)⟩
      · simpa [st0, Quad.zero, z2b_zero] using hfalse
      · simpa [st0, Quad.zero, z2b_zero] using hfalse
      · simpa [st0, Quad.zero, z2b_zero] using hfalse
  have hit' : ∀ r, Build Base (packSigs (fun x =>
      (List.range r).foldl (fun s j => packStep (used x) (rowQ x) j s) (st0 x)))
      (r * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4)))) := by
    intro r
    induction r with
    | zero =>
      simpa using idleB (A := Base) (B := packSigs st0) hst0
    | succ r ih =>
      let str : (Fin N → Bool) → PackState m h :=
        fun x => (List.range r).foldl (fun s j => packStep (used x) (rowQ x) j s) (st0 x)
      have hstep := packStepB Base hfalse used rowQ hused hrowQ r str
      have heq : (fun x => (List.range (r + 1)).foldl (fun s j => packStep (used x) (rowQ x) j s) (st0 x)) =
          fun x => packStep (used x) (rowQ x) r (str x) := by
        funext x; simp [List.range_succ, List.foldl_append, str]
      rw [heq]
      exact relaxB (seq2B ih hstep) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])
  exact hit' t

structure AffState (t m h : ℕ) where
  affUsed : Fin t → Bool
  A : Fin t → Fin m → ZMod 2
  b : Fin t → ZMod 2
  varElim : Fin m → Bool
  qs : Fin h → Quad m

def affStep {t m h : ℕ} (v : ℕ) (st : AffState t m h) : AffState t m h :=
  if hv : v < m then
    let i0 : Fin m := ⟨v, hv⟩
    let cond : Fin t → Bool := fun r => !(st.affUsed r) && z2b (st.A r i0)
    let isPiv : Fin t → Bool := firstTrue cond
    let found : Bool := (List.finRange t).any isPiv
    let pivA : Fin m → ZMod 2 := fun u =>
      b2z ((List.finRange t).any (fun r => isPiv r && z2b (st.A r u)))
    let pivb : ZMod 2 :=
      b2z ((List.finRange t).any (fun r => isPiv r && z2b (st.b r)))
    let e : Fin m → ZMod 2 := fun u => if u = i0 then 0 else pivA u
    { affUsed := fun r => st.affUsed r || isPiv r
      A := fun r u => if !(isPiv r) && z2b (st.A r i0) then st.A r u + pivA u else st.A r u
      b := fun r => if !(isPiv r) && z2b (st.A r i0) then st.b r + pivb else st.b r
      varElim := fun u => st.varElim u || (found && decide (u = i0))
      qs := fun s =>
        let Qs := st.qs s
        let f : Fin m → ZMod 2 := fun u => if u = i0 then 0 else Qs.B i0 u
        let Qsub := (Qs.delVar i0).addAffineProd pivb e (Qs.l i0) f
        if found then Qsub else Qs }
  else st

def affElim {t m h : ℕ} (A0 : Fin t → Fin m → ZMod 2) (b0 : Fin t → ZMod 2)
    (qs0 : Fin h → Quad m) : AffState t m h :=
  (List.range m).foldl (fun st v => affStep v st)
    ⟨fun _ => false, A0, b0, fun _ => false, qs0⟩

def AffState.sols {t m h : ℕ} (st : AffState t m h) : Finset (Fin m → ZMod 2) :=
  Finset.univ.filter (fun a =>
    (∀ u : Fin m, st.varElim u = true → a u = 0) ∧
    (∀ r : Fin t, st.affUsed r = false → st.b r + ∑ u : Fin m, st.A r u * a u = 0) ∧
    (∀ s : Fin h, (st.qs s).eval a = 0))

theorem affElim_spec {t m h : ℕ}
    (A0 : Fin t → Fin m → ZMod 2) (b0 : Fin t → ZMod 2) (qs0 : Fin h → Quad m)
    (hqs0 : ∀ s : Fin h, (qs0 s).Valid) :
    let st := affElim A0 b0 qs0
    let consistent : Bool := (List.finRange t).all (fun r => st.affUsed r || !(z2b (st.b r)))
    (∀ s : Fin h, (st.qs s).Valid) ∧
    (∀ s : Fin h, ∀ u : Fin m, st.varElim u = true →
      (st.qs s).l u = 0 ∧ ∀ w : Fin m, (st.qs s).B u w = 0) ∧
    (Finset.univ.filter (fun a : Fin m → ZMod 2 =>
      (∀ r : Fin t, b0 r + ∑ u : Fin m, A0 r u * a u = 0) ∧
      (∀ s : Fin h, (qs0 s).eval a = 0))).card =
    if consistent then
      (Finset.univ.filter (fun a : Fin m → ZMod 2 =>
        (∀ u : Fin m, st.varElim u = true → a u = 0) ∧
        (∀ s : Fin h, (st.qs s).eval a = 0))).card
    else 0 := by
  have hloop : ∀ v ≤ m,
      let st := (List.range v).foldl (fun s k => affStep k s)
        ⟨fun _ => false, A0, b0, fun _ => false, qs0⟩
      (∀ u : Fin m, st.varElim u = true → u.val < v) ∧
      (∀ r : Fin t, st.affUsed r = false → ∀ u : Fin m, u.val < v → st.A r u = 0) ∧
      (∀ s : Fin h, (st.qs s).Valid) ∧
      (∀ s : Fin h, ∀ u : Fin m, st.varElim u = true →
        (st.qs s).l u = 0 ∧ ∀ w : Fin m, (st.qs s).B u w = 0) ∧
      st.sols.card =
        (Finset.univ.filter (fun a : Fin m → ZMod 2 =>
          (∀ r : Fin t, b0 r + ∑ u : Fin m, A0 r u * a u = 0) ∧
          (∀ s : Fin h, (qs0 s).eval a = 0))).card := by
    intro v
    induction v with
    | zero =>
      intro _
      refine ⟨fun u hu => Bool.noConfusion hu, fun _ _ _ hu => by omega, hqs0,
        fun _ _ hu => Bool.noConfusion hu, ?_⟩
      congr 1
      ext a
      simp [AffState.sols]
    | succ v ih =>
      intro hv
      rcases ih (by omega) with ⟨hve_lt, hA_zero, hq_val, hq_supp, hcard⟩
      set st := (List.range v).foldl (fun s k => affStep k s)
        ⟨fun _ => false, A0, b0, fun _ => false, qs0⟩
      have hst_next : (List.range (v + 1)).foldl (fun s k => affStep k s)
          ⟨fun _ => false, A0, b0, fun _ => false, qs0⟩ = affStep v st := by
        simp [List.range_succ, List.foldl_append, st]
      rw [hst_next]
      have hvm : v < m := by omega
      let i0 : Fin m := ⟨v, hvm⟩
      let cond : Fin t → Bool := fun r => !(st.affUsed r) && z2b (st.A r i0)
      let isPiv : Fin t → Bool := firstTrue cond
      by_cases hex : ∃ r : Fin t, cond r = true
      · rcases (exists_firstTrue_iff cond).mpr hex with ⟨p0, hp0⟩
        have huniq : ∀ r, isPiv r = true ↔ r = p0 := fun r =>
          ⟨fun h => firstTrue_unique cond h hp0, fun h => h ▸ hp0⟩
        have hfound : (List.finRange t).any isPiv = true :=
          List.any_eq_true.mpr ⟨p0, List.mem_finRange p0, hp0⟩
        have hp0_cond := ((firstTrue_spec cond p0).mp hp0).1
        have hp0_unused : st.affUsed p0 = false := by
          simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hp0_cond
          exact hp0_cond.1
        have hp0_one : st.A p0 i0 = 1 := by
          simp only [cond, Bool.and_eq_true] at hp0_cond
          have := hp0_cond.2
          rcases z2_cases (st.A p0 i0) with h | h
          · simp [h, z2b_zero] at this
          · exact h
        have hpivA : ∀ u, b2z ((List.finRange t).any (fun r => isPiv r && z2b (st.A r u))) = st.A p0 u := by
          intro u
          have hany : (List.finRange t).any (fun r => isPiv r && z2b (st.A r u)) = z2b (st.A p0 u) := by
            cases h : z2b (st.A p0 u)
            · rw [List.any_eq_false]
              intro r _
              by_cases hr : r = p0
              · subst hr; simp [h]
              · have hf : isPiv r = false := by
                  cases h' : isPiv r
                  · rfl
                  · exact absurd ((huniq r).mp h') hr
                simp [hf]
            · exact List.any_eq_true.mpr ⟨p0, List.mem_finRange p0, by simp [isPiv, hp0, h]⟩
          rw [hany, b2z_z2b]
        have hpivb : b2z ((List.finRange t).any (fun r => isPiv r && z2b (st.b r))) = st.b p0 := by
          have hany : (List.finRange t).any (fun r => isPiv r && z2b (st.b r)) = z2b (st.b p0) := by
            cases h : z2b (st.b p0)
            · rw [List.any_eq_false]
              intro r _
              by_cases hr : r = p0
              · subst hr; simp [h]
              · have hf : isPiv r = false := by
                  cases h' : isPiv r
                  · rfl
                  · exact absurd ((huniq r).mp h') hr
                simp [hf]
            · exact List.any_eq_true.mpr ⟨p0, List.mem_finRange p0, by simp [isPiv, hp0, h]⟩
          rw [hany, b2z_z2b]
        let e : Fin m → ZMod 2 := fun u => if u = i0 then 0 else st.A p0 u
        have hst' : affStep v st =
            { affUsed := fun r => st.affUsed r || isPiv r
              A := fun r u => if !(isPiv r) && z2b (st.A r i0) then st.A r u + st.A p0 u else st.A r u
              b := fun r => if !(isPiv r) && z2b (st.A r i0) then st.b r + st.b p0 else st.b r
              varElim := fun u => st.varElim u || decide (u = i0)
              qs := fun s =>
                let Qs := st.qs s
                (Qs.delVar i0).addAffineProd (st.b p0) e (Qs.l i0)
                  (fun u => if u = i0 then 0 else Qs.B i0 u) } := by
          simp only [affStep, hvm, ↓reduceDIte, i0, cond, isPiv, hfound, hpivA, hpivb, Bool.true_and,
            ↓reduceIte, e]
        have he_zero_elim : ∀ u : Fin m, st.varElim u = true → e u = 0 := by
          intro u hu
          have hult : u.val < v := hve_lt u hu
          have hne : u ≠ i0 := fun h => by rw [h] at hult; exact lt_irrefl _ hult
          simp only [e, hne, ↓reduceIte]
          exact hA_zero p0 hp0_unused u hult
        have hi0_not_elim : st.varElim i0 = false := by
          cases h : st.varElim i0
          · rfl
          · have := hve_lt i0 h; simp [i0] at this
        have hrow_upd : ∀ r, r ≠ p0 →
            (∀ u, (affStep v st).A r u = st.A r u + st.A r i0 * st.A p0 u) ∧
            (affStep v st).b r = st.b r + st.A r i0 * st.b p0 := by
          intro r hr
          have hrf : isPiv r = false := by
            cases h' : isPiv r
            · rfl
            · exact absurd ((huniq r).mp h') hr
          rw [hst']
          rcases z2_cases (st.A r i0) with h0 | h1
          · exact ⟨fun u => by simp [hrf, h0, z2b_zero], by simp [hrf, h0, z2b_zero]⟩
          · exact ⟨fun u => by simp [hrf, h1, z2b_one], by simp [hrf, h1, z2b_one]⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro u hu
          rw [hst'] at hu
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hu
          rcases hu with hu | rfl
          · exact Nat.lt_succ_of_lt (hve_lt u hu)
          · simp [i0]
        · intro r hr u hu
          rw [hst'] at hr
          simp only [Bool.or_eq_false_iff] at hr
          have hr_ne : r ≠ p0 := fun h => by
            rw [h] at hr
            exact Bool.noConfusion (hp0.symm.trans hr.2)
          rw [(hrow_upd r hr_ne).1 u]
          by_cases huv : u.val < v
          · rw [hA_zero r hr.1 u huv, hA_zero p0 hp0_unused u huv, mul_zero, add_zero]
          · have hui : u = i0 := Fin.ext (by dsimp [i0]; omega)
            subst hui
            rw [hp0_one, mul_one, z2_add_self]
        · intro s
          rw [hst']
          exact Quad.valid_addAffineProd (Quad.valid_delVar (hq_val s) i0) _ _ _ _
        · intro s u hu
          rw [hst'] at hu ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hu
          rcases hu with hu_old | rfl
          · have hult : u.val < v := hve_lt u hu_old
            have hui : u ≠ i0 := fun h => by rw [h] at hult; exact lt_irrefl _ hult
            have heu : e u = 0 := he_zero_elim u hu_old
            have hBu : (st.qs s).B i0 u = 0 := by
              rw [(hq_val s).2 i0 u]
              exact (hq_supp s u hu_old).2 i0
            refine ⟨?_, fun w => ?_⟩
            · simp only [Quad.addAffineProd, Quad.delVar, hui, ↓reduceIte,
                (hq_supp s u hu_old).1, heu, hBu, mul_zero, add_zero]
            · by_cases huw : u = w
              · simp [Quad.addAffineProd, huw]
              · by_cases hwi : w = i0
                · simp [Quad.addAffineProd, Quad.delVar, hui, hwi, e]
                · simp only [Quad.addAffineProd, Quad.delVar, huw, hui, hwi, or_self, ↓reduceIte,
                    (hq_supp s u hu_old).2 w, heu, hBu, zero_mul, mul_zero, add_zero]
          · refine ⟨?_, fun w => ?_⟩
            · simp [Quad.addAffineProd, Quad.delVar, e]
            · by_cases hiw : i0 = w
              · simp [Quad.addAffineProd, hiw]
              · simp [Quad.addAffineProd, Quad.delVar, hiw, e]
        · rw [← hcard]
          have hdep_eval : ∀ (s : Fin h) (a : Fin m → ZMod 2),
              a i0 = st.b p0 + ∑ u : Fin m, e u * a u →
              ((affStep v st).qs s).eval (Function.update a i0 0) = (st.qs s).eval a := by
            intro s a hai
            have hQeq : ((affStep v st).qs s).eval (Function.update a i0 0) =
                ((affStep v st).qs s).eval a := by
              rw [hst']
              let Q' := ((st.qs s).delVar i0).addAffineProd (st.b p0) e ((st.qs s).l i0)
                (fun u => if u = i0 then 0 else (st.qs s).B i0 u)
              have hQ'0 : Q'.l i0 = 0 ∧ ∀ w, Q'.B i0 w = 0 ∧ Q'.B w i0 = 0 := by
                refine ⟨by simp [Q', Quad.addAffineProd, Quad.delVar, e], fun w => ⟨?_, ?_⟩⟩
                · by_cases h : i0 = w <;> simp [Q', Quad.addAffineProd, Quad.delVar, h, e]
                · by_cases h : w = i0 <;> simp [Q', Quad.addAffineProd, Quad.delVar, h, e]
              change Q'.eval (Function.update a i0 0) = Q'.eval a
              unfold Quad.eval
              congr 1
              · congr 1
                refine Finset.sum_congr rfl (fun u _ => ?_)
                by_cases hu : u = i0
                · subst hu; simp [hQ'0.1]
                · simp [Function.update, hu]
              · refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => ?_))
                by_cases hlt : u.val < w.val
                · by_cases hu : u = i0
                  · subst hu; simp [hlt, (hQ'0.2 w).1]
                  · by_cases hw : w = i0
                    · subst hw; simp [hlt, (hQ'0.2 u).2]
                    · simp [hlt, Function.update, hu, hw]
                · simp [hlt]
            rw [hQeq, hst']
            rw [Quad.eval_addAffineProd, Quad.eval_eq_delVar_add (hq_val s) i0 a, hai]
          have he_sum_upd : ∀ a : Fin m → ZMod 2,
              ∑ u : Fin m, e u * Function.update a i0 0 u = ∑ u : Fin m, e u * a u := by
            intro a
            refine Finset.sum_congr rfl (fun u _ => ?_)
            by_cases hu : u = i0
            · subst hu; simp [e]
            · simp [Function.update, hu]
          have hp0_eq : ∀ a : Fin m → ZMod 2,
              st.b p0 + ∑ u : Fin m, st.A p0 u * a u = 0 ↔
              a i0 = st.b p0 + ∑ u : Fin m, e u * a u := by
            intro a
            have hsp : ∑ u : Fin m, st.A p0 u * a u = a i0 + ∑ u : Fin m, e u * a u := by
              have hterm : ∀ u : Fin m, st.A p0 u * a u =
                  (if u = i0 then a i0 else 0) + e u * a u := by
                intro u
                by_cases hu : u = i0
                · subst hu; simp [e, hp0_one]
                · simp [e, hu]
              simp_rw [hterm, Finset.sum_add_distrib]
              congr 1
              simp
            rw [hsp]
            constructor
            · intro h
              have h1 : a i0 + (st.b p0 + ∑ u, e u * a u) = 0 := by
                calc a i0 + (st.b p0 + ∑ u, e u * a u) = st.b p0 + (a i0 + ∑ u, e u * a u) := by ring
                  _ = 0 := h
              calc
                a i0 = a i0 + (st.b p0 + ∑ u, e u * a u) + (st.b p0 + ∑ u, e u * a u) := by
                  rw [add_assoc, z2_add_self, add_zero]
                _ = st.b p0 + ∑ u, e u * a u := by rw [h1, zero_add]
            · intro h
              rw [h]
              have : st.b p0 + (st.b p0 + ∑ u, e u * a u + ∑ u, e u * a u) =
                  (st.b p0 + st.b p0) + ((∑ u, e u * a u) + (∑ u, e u * a u)) := by ring
              rw [this, z2_add_self, z2_add_self, add_zero]
          refine Finset.card_bij (fun a' _ => Function.update a' i0 (st.b p0 + ∑ u, e u * a' u))
            ?_ ?_ ?_
          · intro a' ha'
            rcases (Finset.mem_filter.mp ha').2 with ⟨hsupp', haff', hqs'⟩
            have ha'i0 : a' i0 = 0 := by
              apply hsupp' i0
              rw [hst']; simp
            let a := Function.update a' i0 (st.b p0 + ∑ u, e u * a' u)
            have hupd : Function.update a i0 0 = a' := by
              funext u
              by_cases hu : u = i0
              · subst hu; simp [ha'i0]
              · simp [a, Function.update, hu]
            have hai : a i0 = st.b p0 + ∑ u, e u * a u := by
              have h1 : a i0 = st.b p0 + ∑ u, e u * a' u := by simp [a]
              rw [h1, ← hupd, he_sum_upd]
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
            · intro u hu
              have hui : u ≠ i0 := fun h => by rw [h, hi0_not_elim] at hu; exact Bool.noConfusion hu
              simp only [Function.update, hui, ↓reduceDIte]
              apply hsupp' u
              rw [hst']; simp [hu]
            · intro r hr
              by_cases hrp : r = p0
              · subst hrp; exact (hp0_eq a).mpr hai
              · have hrf : isPiv r = false := by
                  cases h' : isPiv r
                  · rfl
                  · exact absurd ((huniq r).mp h') hrp
                have hr' : (affStep v st).affUsed r = false := by
                  rw [hst']; simp [hr, hrf]
                have heq' := haff' r hr'
                have hA0_i0 : (affStep v st).A r i0 = 0 := by
                  rw [(hrow_upd r hrp).1 i0, hp0_one, mul_one, z2_add_self]
                have hsum_same : ∑ u : Fin m, (affStep v st).A r u * a' u =
                    ∑ u : Fin m, (affStep v st).A r u * a u := by
                  refine Finset.sum_congr rfl (fun u _ => ?_)
                  by_cases hu : u = i0
                  · subst hu; simp [hA0_i0]
                  · simp [a, hu]
                rw [hsum_same] at heq'
                have hexp : (affStep v st).b r + ∑ u : Fin m, (affStep v st).A r u * a u =
                    (st.b r + ∑ u : Fin m, st.A r u * a u) +
                    st.A r i0 * (st.b p0 + ∑ u : Fin m, st.A p0 u * a u) := by
                  rw [(hrow_upd r hrp).2]
                  have hterm : ∀ u, (affStep v st).A r u * a u =
                      st.A r u * a u + st.A r i0 * (st.A p0 u * a u) := by
                    intro u; rw [(hrow_upd r hrp).1 u]; ring
                  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
                  ring
                rw [hexp, (hp0_eq a).mpr hai, mul_zero, add_zero] at heq'
                exact heq'
            · intro s
              rw [← hdep_eval s a hai, hupd]
              exact hqs' s
          · intro a1 ha1 a2 ha2 heq
            have h1i : a1 i0 = 0 := by
              apply (Finset.mem_filter.mp ha1).2.1 i0
              rw [hst']; simp
            have h2i : a2 i0 = 0 := by
              apply (Finset.mem_filter.mp ha2).2.1 i0
              rw [hst']; simp
            funext u
            by_cases hu : u = i0
            · subst hu; rw [h1i, h2i]
            · have := congrFun heq u
              simpa [Function.update, hu] using this
          · intro a ha
            rcases (Finset.mem_filter.mp ha).2 with ⟨hsupp, haff, hqs⟩
            have hai : a i0 = st.b p0 + ∑ u, e u * a u := (hp0_eq a).mp (haff p0 hp0_unused)
            let a' := Function.update a i0 0
            refine ⟨a', ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
              · intro u hu
                rw [hst'] at hu
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hu
                rcases hu with hu | rfl
                · by_cases hui : u = i0
                  · subst hui; simp [a']
                  · simp [a', hui, hsupp u hu]
                · simp [a']
              · intro r hr
                rw [hst'] at hr
                simp only [Bool.or_eq_false_iff] at hr
                have hrp : r ≠ p0 := fun h => by
                  rw [h] at hr
                  exact Bool.noConfusion (hp0.symm.trans hr.2)
                have hA0_i0 : (affStep v st).A r i0 = 0 := by
                  rw [(hrow_upd r hrp).1 i0, hp0_one, mul_one, z2_add_self]
                have hsum_same : ∑ u : Fin m, (affStep v st).A r u * a' u =
                    ∑ u : Fin m, (affStep v st).A r u * a u := by
                  refine Finset.sum_congr rfl (fun u _ => ?_)
                  by_cases hu : u = i0
                  · subst hu; simp [hA0_i0]
                  · simp [a', hu]
                rw [hsum_same, (hrow_upd r hrp).2]
                have hterm : ∀ u, (affStep v st).A r u * a u =
                    st.A r u * a u + st.A r i0 * (st.A p0 u * a u) := by
                  intro u; rw [(hrow_upd r hrp).1 u]; ring
                simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
                calc
                  st.b r + st.A r i0 * st.b p0 +
                      ((∑ u, st.A r u * a u) + st.A r i0 * ∑ u, st.A p0 u * a u) =
                    (st.b r + ∑ u, st.A r u * a u) +
                      st.A r i0 * (st.b p0 + ∑ u, st.A p0 u * a u) := by ring
                  _ = 0 + st.A r i0 * 0 := by rw [haff r hr.1, haff p0 hp0_unused]
                  _ = 0 := by ring
              · intro s
                rw [hdep_eval s a hai]
                exact hqs s
            · funext u
              by_cases hu : u = i0
              · subst hu
                simp only [Function.update_self]
                rw [he_sum_upd, ← hai]
              · simp [a', Function.update, hu]
      · push Not at hex
        have hallf : ∀ r, cond r = false := fun r => by
          cases h' : cond r
          · rfl
          · exact absurd h' (hex r)
        have hnoPiv : ∀ r, isPiv r = false := fun r => by
          cases h' : isPiv r
          · rfl
          · have := ((firstTrue_spec cond r).mp h').1
            rw [hallf r] at this; exact Bool.noConfusion this
        have hst_eq : affStep v st = st := by
          have hgen : ∀ (s : AffState t m h),
              (∀ r, firstTrue (fun r => !(s.affUsed r) && z2b (s.A r i0)) r = false) →
              affStep v s = s := by
            rintro ⟨u, A, b, ve, qs⟩ hnp
            have hany0 : ((List.finRange t).any (fun _ => false)) = false := by simp
            have hnf : (List.finRange t).any (firstTrue (fun r => !(u r) && z2b (A r i0))) = false := by
              rw [List.any_eq_false]; intro r _; simp [hnp r]
            simp only [affStep, hvm, ↓reduceDIte]
            change ({ affUsed := _, A := _, b := _, varElim := _, qs := _ } : AffState t m h) = _
            congr 1
            · funext r; simp [i0, hnp r]
            · funext r w
              simp only [i0, hnp, Bool.false_and, hany0, b2z, Bool.false_eq_true, ↓reduceIte, add_zero, ite_self]
            · funext r
              simp only [i0, hnp, Bool.false_and, hany0, b2z, Bool.false_eq_true, ↓reduceIte, add_zero, ite_self]
            · funext w; simp [i0, hnf]
            · funext s; simp [i0, hnf]
          exact hgen st hnoPiv
        rw [hst_eq]
        refine ⟨fun u hu => Nat.lt_succ_of_lt (hve_lt u hu), ?_, hq_val, hq_supp, hcard⟩
        intro r hr u hu
        by_cases huv : u.val < v
        · exact hA_zero r hr u huv
        · have hui : u = i0 := Fin.ext (by dsimp [i0]; omega)
          subst hui
          have hcf := hallf r
          simp only [cond, hr, Bool.not_false, Bool.true_and] at hcf
          rcases z2_cases (st.A r i0) with h' | h'
          · exact h'
          · simp [h', z2b_one] at hcf
  rcases hloop m le_rfl with ⟨_, hA_zero, hq_val, hq_supp, hcard⟩
  intro st consistent
  have hA_zero' : ∀ r : Fin t, st.affUsed r = false → ∀ u : Fin m, st.A r u = 0 :=
    fun r hr u => hA_zero r hr u u.isLt
  refine ⟨hq_val, hq_supp, ?_⟩
  rw [← hcard]
  have hcons_iff : consistent = true ↔ ∀ r : Fin t, st.affUsed r = false → st.b r = 0 := by
    simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      Bool.not_eq_true']
    constructor
    · intro hall r hr
      rcases hall r with h1 | h2
      · rw [hr] at h1; exact Bool.noConfusion h1
      · rcases z2_cases (st.b r) with h' | h'
        · exact h'
        · simp [h', z2b_one] at h2
    · intro hall r
      cases hu : st.affUsed r
      · right; rw [hall r hu, z2b_zero]
      · left; rfl
  by_cases hc : consistent = true
  · simp only [hc, ↓reduceIte]
    have hbr0 := hcons_iff.mp hc
    congr 1
    ext a
    simp only [AffState.sols, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, fun r hr => ?_, h3⟩
      change st.b r + ∑ u : Fin m, st.A r u * a u = 0
      have hAr : ∀ u : Fin m, st.A r u = 0 := hA_zero' r hr
      rw [hbr0 r hr, Finset.sum_eq_zero (fun u _ => by rw [hAr u, zero_mul]), add_zero]
  · have hcf : consistent = false := by cases h' : consistent <;> simp_all
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    have haff := (Finset.mem_filter.mp ha).2.2.1
    have hnot : ¬ (∀ r : Fin t, st.affUsed r = false → st.b r = 0) := fun hall =>
      hc (hcons_iff.mpr hall)
    push Not at hnot
    rcases hnot with ⟨r, hr, hbr⟩
    have h1 : st.b r + ∑ u : Fin m, st.A r u * a u = 0 := haff r hr
    have hAr : ∀ u : Fin m, st.A r u = 0 := hA_zero' r hr
    rw [Finset.sum_eq_zero (fun u _ => by rw [hAr u, zero_mul]), add_zero] at h1
    exact hbr h1

def affSigs {N t m h : ℕ} (st : (Fin N → Bool) → AffState t m h) : Set (Sig N) :=
  Set.range (fun r : Fin t => fun x => (st x).affUsed r) ∪
  {f | ∃ r u, (fun x => z2b ((st x).A r u)) = f} ∪
  Set.range (fun r : Fin t => fun x => z2b ((st x).b r)) ∪
  Set.range (fun u : Fin m => fun x => (st x).varElim u) ∪
  ⋃ s : Fin h, quadSigs (fun x => (st x).qs s)

theorem affStepB {N t m h : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (v : ℕ) (st : (Fin N → Bool) → AffState t m h) :
    Build (Base ∪ affSigs st) (affSigs (fun x => affStep v (st x)))
      (t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
        h * (m * (m * 14) + m * 19 + 9)) := by
  by_cases hv : v < m
  · let i0 : Fin m := ⟨v, hv⟩
    let cond : Fin t → Sig N := fun r x => !((st x).affUsed r) && z2b ((st x).A r i0)
    let isPiv : Fin t → Sig N := fun r x => firstTrue (fun j => cond j x) r
    let found : Sig N := fun x => (List.finRange t).any (fun r => isPiv r x)
    let pivA : Fin m → Sig N := fun u x => (List.finRange t).any (fun r => isPiv r x && z2b ((st x).A r u))
    let pivb : Sig N := fun x => (List.finRange t).any (fun r => isPiv r x && z2b ((st x).b r))
    have hcondB : Build (Base ∪ affSigs st) (Set.range cond) (t * 2) := by
      refine finSigB cond 2 (fun r => ?_)
      have h1 : Build (Base ∪ affSigs st) {fun x => !((st x).affUsed r)} 1 :=
        notB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))))
      have h2 : Build ((Base ∪ affSigs st) ∪ {fun x => !((st x).affUsed r)}) {cond r} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, i0, rfl⟩))))))
      exact seq2B h1 h2
    have hftB : Build ((Base ∪ affSigs st) ∪ Set.range cond) (Set.range isPiv) (t * (t + 2)) :=
      firstTrueB cond (Or.inl (Or.inl hfalse)) (fun r => Or.inr ⟨r, rfl⟩)
    let A1 := (Base ∪ affSigs st) ∪ (Set.range cond ∪ Set.range isPiv)
    have h1 : Build (Base ∪ affSigs st) (Set.range cond ∪ Set.range isPiv) (t * 2 + t * (t + 2)) :=
      seqB hcondB hftB
    have hfoundB : Build A1 {found} t := by
      have h := orListB (A := A1) ((List.finRange t).map isPiv)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr (Or.inr ⟨r, rfl⟩))
        (Or.inl (Or.inl hfalse))
      have heq : (fun x => ((List.finRange t).map isPiv).any (fun f => f x)) = found := by
        funext x; simp [found, List.any_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at h
      exact h
    have hpivAB : Build A1 (Set.range pivA) (m * (2 * t)) := by
      refine finSigB pivA (2 * t) (fun u => ?_)
      let term : Fin t → Sig N := fun r x => isPiv r x && z2b ((st x).A r u)
      have ht : Build A1 (Set.range term) (t * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, u, rfl⟩)))))))
      have hor : Build (A1 ∪ Set.range term) {pivA u} t := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange t).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange t).map term).any (fun f => f x)) = pivA u := by
          funext x; simp [pivA, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have hpivbB : Build A1 {pivb} (2 * t) := by
      let term : Fin t → Sig N := fun r x => isPiv r x && z2b ((st x).b r)
      have ht : Build A1 (Set.range term) (t * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r, rfl⟩))))))
      have hor : Build (A1 ∪ Set.range term) {pivb} t := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange t).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange t).map term).any (fun f => f x)) = pivb := by
          funext x; simp [pivb, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have h2 : Build A1 (({found} ∪ Set.range pivA) ∪ {pivb}) (t + m * (2 * t) + 2 * t) :=
      unionB (unionB hfoundB hpivAB) hpivbB
    let A2 := A1 ∪ (({found} ∪ Set.range pivA) ∪ {pivb})
    have hFA2 : (fun _ => false) ∈ A2 := Or.inl (Or.inl (Or.inl hfalse))
    have husedB : Build A2 (Set.range (fun r : Fin t => fun x => (affStep v (st x)).affUsed r)) (t * 1) :=
      finSigB _ 1 (fun r => by
        have heq : (fun x => (affStep v (st x)).affUsed r) = fun x => (st x).affUsed r || isPiv r x := by
          funext x; simp [affStep, hv, i0, cond, isPiv]
        rw [heq]
        exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))))))
          (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩))))
    have hAB : Build A2 {f | ∃ r u, (fun x => z2b ((affStep v (st x)).A r u)) = f} (t * (m * 10)) :=
      fin2SigB _ 10 (fun r u => by
        let np : Sig N := fun x => !(isPiv r x)
        let flag : Sig N := fun x => np x && z2b ((st x).A r i0)
        let xored : Sig N := fun x => xor (z2b ((st x).A r u)) (pivA u x)
        let out : Sig N := fun x => if flag x then xored x else z2b ((st x).A r u)
        have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
        have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
          andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, i0, rfl⟩))))))))
        have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {xored} 4 :=
          xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, u, rfl⟩)))))))))
            (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))
        have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4 :=
          iteB (Or.inl (Or.inr rfl)) (Or.inr rfl)
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, u, rfl⟩))))))))))
        have heq : out = fun x => z2b ((affStep v (st x)).A r u) := by
          funext x
          simp only [out, flag, np, xored, affStep, hv, ↓reduceDIte, i0, cond, isPiv, pivA]
          cases hf : (!(firstTrue (fun j => !((st x).affUsed j) && z2b ((st x).A j i0)) r) &&
              z2b ((st x).A r i0)) <;> simp [z2b_add, z2b_b2z]
        rw [← heq]
        exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
          le_rfl Set.subset_union_right (by omega))
    have hbB : Build A2 (Set.range (fun r : Fin t => fun x => z2b ((affStep v (st x)).b r))) (t * 10) :=
      finSigB _ 10 (fun r => by
        let np : Sig N := fun x => !(isPiv r x)
        let flag : Sig N := fun x => np x && z2b ((st x).A r i0)
        let xored : Sig N := fun x => xor (z2b ((st x).b r)) (pivb x)
        let out : Sig N := fun x => if flag x then xored x else z2b ((st x).b r)
        have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
        have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
          andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, i0, rfl⟩))))))))
        have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {xored} 4 :=
          xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r, rfl⟩))))))))
            (Or.inl (Or.inl (Or.inr (Or.inr rfl))))
        have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {xored}) {out} 4 :=
          iteB (Or.inl (Or.inr rfl)) (Or.inr rfl)
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨r, rfl⟩)))))))))
        have heq : out = fun x => z2b ((affStep v (st x)).b r) := by
          funext x
          simp only [out, flag, np, xored, affStep, hv, ↓reduceDIte, i0, cond, isPiv, pivb]
          cases hf : (!(firstTrue (fun j => !((st x).affUsed j) && z2b ((st x).A j i0)) r) &&
              z2b ((st x).A r i0)) <;> simp [z2b_add, z2b_b2z]
        rw [← heq]
        exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
          le_rfl Set.subset_union_right (by omega))
    have hveB : Build A2 (Set.range (fun u : Fin m => fun x => (affStep v (st x)).varElim u)) (m * 1) :=
      finSigB _ 1 (fun u => by
        by_cases hu : u = i0
        · have heq : (fun x => (affStep v (st x)).varElim u) = fun x => (st x).varElim u || found x := by
            funext x; simp [affStep, hv, i0, hu, cond, isPiv, found]
          rw [heq]
          exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))
            (Or.inr (Or.inl (Or.inl rfl)))
        · have heq : (fun x => (affStep v (st x)).varElim u) = fun x => (st x).varElim u := by
            funext x; simp [affStep, hv, i0, hu]
          rw [heq]
          exact relaxB (idleB (A := A2) (B := {fun x => (st x).varElim u})
            (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))))
            le_rfl Set.subset_union_right (by omega))
    have hqsB : Build A2 (⋃ s : Fin h, quadSigs (fun x => (affStep v (st x)).qs s))
        (h * (m * (m * 14) + m * 19 + 9)) := by
      refine finB _ (m * (m * 14) + m * 19 + 9) (fun s => ?_)
      let Qdel : (Fin N → Bool) → Quad m := fun x => ((st x).qs s).delVar i0
      let eZ : (Fin N → Bool) → Fin m → ZMod 2 := fun x u => if u = i0 then 0 else b2z (pivA u x)
      let fZ : (Fin N → Bool) → Fin m → ZMod 2 := fun x u => if u = i0 then 0 else ((st x).qs s).B i0 u
      let Qsub : (Fin N → Bool) → Quad m :=
        fun x => (Qdel x).addAffineProd (b2z (pivb x)) (eZ x) (((st x).qs s).l i0) (fZ x)
      have hQdel_in : quadSigs Qdel ⊆ A2 := by
        rintro g ((⟨a, b, rfl⟩ | ⟨a, rfl⟩) | rfl)
        · by_cases h1 : a = i0 ∨ b = i0
          · have : (fun x => z2b ((Qdel x).B a b)) = fun _ => false := by
              funext x; simp [Qdel, Quad.delVar, h1, z2b_zero]
            rw [this]; exact hFA2
          · have : (fun x => z2b ((Qdel x).B a b)) = fun x => z2b (((st x).qs s).B a b) := by
              funext x; simp [Qdel, Quad.delVar, h1]
            rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inl ⟨a, b, rfl⟩)⟩))))
        · dsimp only
          by_cases h1 : a = i0
          · have : (fun x => z2b ((Qdel x).l a)) = fun _ => false := by
              funext x; simp [Qdel, Quad.delVar, h1, z2b_zero]
            rw [this]; exact hFA2
          · have : (fun x => z2b ((Qdel x).l a)) = fun x => z2b (((st x).qs s).l a) := by
              funext x; simp [Qdel, Quad.delVar, h1]
            rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inr ⟨a, rfl⟩)⟩))))
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inr rfl⟩))))
      have hpivb_in : (fun x => z2b (b2z (pivb x))) ∈ A2 := by
        have : (fun x => z2b (b2z (pivb x))) = pivb := funext (fun x => z2b_b2z (pivb x))
        rw [this]; exact Or.inr (Or.inr rfl)
      have hsubB : Build A2 (quadSigs Qsub) (m * (m * 10) + m * 15 + 5) :=
        addAffineProdB A2 hFA2 Qdel (fun x => b2z (pivb x))
          (fun x => ((st x).qs s).l i0) eZ fZ hQdel_in
          hpivb_in
          (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inr ⟨i0, rfl⟩)⟩)))))
          (fun u => by
            by_cases hu : u = i0
            · have : (fun x => z2b (eZ x u)) = fun _ => false := by funext x; simp [eZ, hu, z2b_zero]
              rw [this]; exact hFA2
            · have : (fun x => z2b (eZ x u)) = pivA u := by funext x; simp [eZ, hu, z2b_b2z]
              rw [this]; exact Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))
          (fun u => by
            by_cases hu : u = i0
            · have : (fun x => z2b (fZ x u)) = fun _ => false := by funext x; simp [fZ, hu, z2b_zero]
              rw [this]; exact hFA2
            · have : (fun x => z2b (fZ x u)) = fun x => z2b (((st x).qs s).B i0 u) := by
                funext x; simp [fZ, hu]
              rw [this]; exact Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inl ⟨i0, u, rfl⟩)⟩)))))
      have hmuxB : Build (A2 ∪ quadSigs Qsub)
          (quadSigs (fun x => (affStep v (st x)).qs s)) (m * (m * 4) + m * 4 + 4) := by
        have hB : Build (A2 ∪ quadSigs Qsub)
            {f | ∃ a b, (fun x => z2b (((affStep v (st x)).qs s).B a b)) = f} (m * (m * 4)) :=
          fin2SigB _ 4 (fun a b => by
            have heq : (fun x => z2b (((affStep v (st x)).qs s).B a b)) =
                fun x => if found x then z2b ((Qsub x).B a b) else z2b (((st x).qs s).B a b) := by
              funext x
              simp only [affStep, hv, ↓reduceDIte, i0, cond, isPiv, found, Qsub, Qdel, eZ, fZ, pivA, pivb]
              cases (List.finRange t).any (firstTrue (fun r => !((st x).affUsed r) && z2b ((st x).A r i0))) <;>
                simp
            rw [heq]
            exact iteB (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inl (Or.inl ⟨a, b, rfl⟩)))
              (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inl ⟨a, b, rfl⟩)⟩)))))))
        have hL : Build (A2 ∪ quadSigs Qsub)
            (Set.range (fun a : Fin m => fun x => z2b (((affStep v (st x)).qs s).l a))) (m * 4) :=
          finSigB _ 4 (fun a => by
            have heq : (fun x => z2b (((affStep v (st x)).qs s).l a)) =
                fun x => if found x then z2b ((Qsub x).l a) else z2b (((st x).qs s).l a) := by
              funext x
              simp only [affStep, hv, ↓reduceDIte, i0, cond, isPiv, found, Qsub, Qdel, eZ, fZ, pivA, pivb]
              cases (List.finRange t).any (firstTrue (fun r => !((st x).affUsed r) && z2b ((st x).A r i0))) <;>
                simp
            rw [heq]
            exact iteB (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inl (Or.inr ⟨a, rfl⟩)))
              (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inl (Or.inr ⟨a, rfl⟩)⟩)))))))
        have hC : Build (A2 ∪ quadSigs Qsub)
            {fun x => z2b ((affStep v (st x)).qs s).c} 4 := by
          have heq : (fun x => z2b ((affStep v (st x)).qs s).c) =
              fun x => if found x then z2b (Qsub x).c else z2b ((st x).qs s).c := by
            funext x
            simp only [affStep, hv, ↓reduceDIte, i0, cond, isPiv, found, Qsub, Qdel, eZ, fZ, pivA, pivb]
            cases (List.finRange t).any (firstTrue (fun r => !((st x).affUsed r) && z2b ((st x).A r i0))) <;>
              simp
          rw [heq]
          exact iteB (Or.inl (Or.inr (Or.inl (Or.inl rfl)))) (Or.inr (Or.inr rfl))
            (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Or.inr rfl⟩))))))
        exact relaxB (unionB (unionB hB hL) hC) le_rfl Set.subset_union_right (by omega)
      exact relaxB (seq2B hsubB hmuxB) le_rfl Set.subset_union_right (by ring_nf; omega)
    have h3 := unionB (unionB (unionB (unionB husedB hAB) hbB) hveB) hqsB
    exact relaxB (transB (transB (extB h1) (extB h2)) h3) le_rfl Set.subset_union_right (by ring_nf; omega)
  · have heq : (fun x => affStep v (st x)) = st := by
      funext x; simp [affStep, hv]
    rw [heq]
    exact relaxB (idleB (A := Base ∪ affSigs st) (B := affSigs st) Set.subset_union_right)
      le_rfl Set.subset_union_right (Nat.zero_le _)

theorem affElimB {N t m h : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (A0 : (Fin N → Bool) → Fin t → Fin m → ZMod 2)
    (b0 : (Fin N → Bool) → Fin t → ZMod 2)
    (qs0 : (Fin N → Bool) → Fin h → Quad m)
    (hA0 : ∀ r u, (fun x => z2b (A0 x r u)) ∈ Base)
    (hb0 : ∀ r, (fun x => z2b (b0 x r)) ∈ Base)
    (hqs0 : ∀ s, quadSigs (fun x => qs0 x s) ⊆ Base) :
    Build Base (affSigs (fun x => affElim (A0 x) (b0 x) (qs0 x)))
      (m * (t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
        h * (m * (m * 14) + m * 19 + 9))) := by
  let st0 : (Fin N → Bool) → AffState t m h :=
    fun x => ⟨fun _ => false, A0 x, b0 x, fun _ => false, qs0 x⟩
  have hst0 : affSigs st0 ⊆ Base := by
    rintro f ((((⟨r, rfl⟩ | ⟨r, u, rfl⟩) | ⟨r, rfl⟩) | ⟨u, rfl⟩) | hq)
    · exact hfalse
    · exact hA0 r u
    · exact hb0 r
    · exact hfalse
    · rcases Set.mem_iUnion.mp hq with ⟨s, hs⟩
      exact hqs0 s hs
  have hit := iterB (Sigs := affSigs) (step := affStep)
    (c := t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
      h * (m * (m * 14) + m * 19 + 9))
    (Base := Base) (fun v st => affStepB Base hfalse v st) m st0
  exact relaxB hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl

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

def oneHotVal {L : ℕ} (p : Fin (L + 1) → Bool) : ℕ :=
  ∑ k : Fin (L + 1), if p k then 2 ^ k.val else 0

theorem oneHotVal_eq {L e : ℕ} (he : e ≤ L) :
    oneHotVal (fun k : Fin (L + 1) => decide (k.val = e)) = 2 ^ e := by
  unfold oneHotVal
  rw [Finset.sum_eq_single ⟨e, by omega⟩]
  · simp
  · intro k _ hk
    have hne : k.val ≠ e := fun h => hk (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem oneHotVal_testBit {L e j : ℕ} (he : e ≤ L) :
    (oneHotVal (fun k : Fin (L + 1) => decide (k.val = e))).testBit j =
      if j < L + 1 then decide (j = e) else false := by
  rw [oneHotVal_eq he, Nat.testBit_two_pow]
  by_cases hj : j < L + 1
  · simp only [hj, ↓reduceIte]
    by_cases hje : e = j <;> simp [hje, eq_comm]
  · simp only [hj, ↓reduceIte]
    have hne : e ≠ j := by omega
    simp [hne]

structure SumState (m : ℕ) where
  active : Fin m → Bool
  Q : Quad m
  zero : Bool
  pow2 : Fin (m + 1) → Bool

def sumStep {m : ℕ} (i : ℕ) (st : SumState m) : SumState m :=
  if hi : i < m then
    let i0 : Fin m := ⟨i, hi⟩
    let cond : Fin m → Bool := fun j => st.active j && z2b (st.Q.B i0 j)
    let isPiv : Fin m → Bool := firstTrue cond
    let found : Bool := (List.finRange m).any isPiv
    let actIso : Fin m → Bool := fun u => if u = i0 then false else st.active u
    let actPair : Fin m → Bool := fun u => if u = i0 || isPiv u then false else st.active u
    let b0 : ZMod 2 := b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.l j)))
    let bv : Fin m → ZMod 2 := fun u =>
      if actPair u then b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.B j u))) else 0
    let av : Fin m → ZMod 2 := fun u => if actPair u then st.Q.B i0 u else 0
    let QdelPair : Quad m :=
      { B := fun u v => if actPair u && actPair v then st.Q.B u v else 0
        l := fun u => if actPair u then st.Q.l u else 0
        c := st.Q.c }
    let Qpair : Quad m := QdelPair.addAffineProd (st.Q.l i0) av b0 bv
    let Qiso : Quad m := st.Q.delVar i0
    if st.active i0 then
      if found then
        { active := actPair
          Q := Qpair
          zero := st.zero
          pow2 := shiftOneHot st.pow2 }
      else
        { active := actIso
          Q := Qiso
          zero := st.zero || z2b (st.Q.l i0)
          pow2 := if z2b (st.Q.l i0) then st.pow2 else shiftOneHot st.pow2 }
    else st
  else st

def evalGaussSum {m : ℕ} (free : Fin m → Bool) (Q0 : Quad m) : SumState m :=
  (List.range m).foldl (fun st i => sumStep i st)
    ⟨free, Q0, false, fun k => decide (k.val = 0)⟩

def Supp {m : ℕ} (act : Fin m → Bool) : Finset (Fin m → ZMod 2) :=
  Finset.univ.filter (fun a => ∀ u : Fin m, act u = false → a u = 0)

theorem quad_eval_eq_of_eq_on_act {m : ℕ} (act : Fin m → Bool) (Q : Quad m)
    (hsupp : ∀ u, act u = false → Q.l u = 0 ∧ ∀ w, Q.B u w = 0 ∧ Q.B w u = 0)
    (a b : Fin m → ZMod 2) (hab : ∀ u, act u = true → a u = b u) :
    Q.eval a = Q.eval b := by
  unfold Quad.eval
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    cases hu : act u
    · simp [(hsupp u hu).1]
    · rw [hab u hu]
  · refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    by_cases hlt : u.val < v.val
    · simp only [hlt, ↓reduceIte]
      cases hu : act u
      · simp [(hsupp u hu).2 v |>.1]
      · cases hv : act v
        · simp [(hsupp v hv).2 u |>.2]
        · rw [hab u hu, hab v hv]
    · simp [hlt]

theorem quad_eval_pair_split {m : ℕ} (act : Fin m → Bool) (Q : Quad m)
    (hQval : Q.Valid)
    (hQsupp : ∀ u : Fin m, act u = false → Q.l u = 0 ∧ ∀ w : Fin m, Q.B u w = 0)
    (i0 j0 : Fin m) (hij_ne : i0 ≠ j0) (hj0_B1 : Q.B i0 j0 = 1)
    (a' : Fin m → ZMod 2) (xi xj : ZMod 2) :
    let act' : Fin m → Bool := fun u => if u = i0 ∨ u = j0 then false else act u
    let av : Fin m → ZMod 2 := fun u => if act' u then Q.B i0 u else 0
    let bv : Fin m → ZMod 2 := fun u => if act' u then Q.B j0 u else 0
    let Qdel : Quad m :=
      { B := fun u v => if act' u && act' v then Q.B u v else 0
        l := fun u => if act' u then Q.l u else 0
        c := Q.c }
    Q.eval (Function.update (Function.update a' j0 xj) i0 xi) =
      Qdel.eval a' + (xi * xj + xi * (Q.l i0 + ∑ u : Fin m, av u * a' u) +
        xj * (Q.l j0 + ∑ u : Fin m, bv u * a' u)) := by
  intro act' av bv Qdel
  let w := Function.update (Function.update a' j0 xj) i0 xi
  have h1 := Quad.eval_eq_delVar_add hQval i0 w
  have hdel1_val : (Q.delVar i0).Valid := Quad.valid_delVar hQval i0
  have h2 := Quad.eval_eq_delVar_add hdel1_val j0 w
  have hwi : w i0 = xi := by simp [w]
  have hwj : w j0 = xj := by simp [w, Function.update, Ne.symm hij_ne]
  have hdel2_eq : ((Q.delVar i0).delVar j0).eval w = Qdel.eval a' := by
    unfold Quad.eval Quad.delVar Qdel
    congr 1
    · congr 1
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases hu1 : u = i0
      · subst hu1; simp [act']
      · by_cases hu2 : u = j0
        · subst hu2; simp [act']
        · cases ha : act u
          · simp [act', hu1, hu2, ha, (hQsupp u ha).1]
          · simp [act', hu1, hu2, ha, w]
    · refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
      by_cases hlt : u.val < v.val
      · simp only [hlt, ↓reduceIte]
        by_cases hu1 : u = i0
        · subst hu1; simp [act']
        · by_cases hu2 : u = j0
          · subst hu2; simp [act']
          · by_cases hv1 : v = i0
            · subst hv1; simp [act']
            · by_cases hv2 : v = j0
              · subst hv2; simp [act']
              · cases hau : act u
                · simp [act', hu1, hu2, hv1, hv2, hau, (hQsupp u hau).2 v]
                · cases hav : act v
                  · have hBv := (hQsupp v hav).2 u
                    rw [hQval.2 v u] at hBv
                    simp [act', hu1, hu2, hv1, hv2, hau, hav, hBv]
                  · simp [act', hu1, hu2, hv1, hv2, hau, hav, w]
      · simp [hlt]
  have hsumA : (∑ u : Fin m, (if u = i0 then 0 else Q.B i0 u) * w u) =
      xj + ∑ u : Fin m, av u * a' u := by
    have hsp : ∀ u : Fin m,
        (if u = i0 then 0 else Q.B i0 u) * w u =
        (if u = j0 then xj else 0) + av u * a' u := by
      intro u
      by_cases hu1 : u = i0
      · subst hu1; simp [act', av, hij_ne]
      · by_cases hu2 : u = j0
        · subst hu2; simp [act', av, hwj, hj0_B1, Ne.symm hij_ne]
        · cases ha : act u
          · have h0 := (hQsupp u ha).2 i0
            rw [hQval.2 u i0] at h0
            simp [act', av, hu1, hu2, ha, h0]
          · simp [act', av, hu1, hu2, ha, w]
    rw [Finset.sum_congr rfl (fun u _ => hsp u), Finset.sum_add_distrib]
    congr 1
    simp
  have hsumB : (Q.delVar i0).l j0 +
      (∑ u : Fin m, (if u = j0 then 0 else (Q.delVar i0).B j0 u) * w u) =
      Q.l j0 + ∑ u : Fin m, bv u * a' u := by
    simp only [Quad.delVar, Ne.symm hij_ne, ↓reduceIte]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases hu1 : u = i0
    · subst hu1; simp [act', bv]
    · by_cases hu2 : u = j0
      · subst hu2; simp [act', bv]
      · cases ha : act u
        · have h0 := (hQsupp u ha).2 j0
          rw [hQval.2 u j0] at h0
          simp [act', bv, hu1, hu2, ha, h0]
        · simp [act', bv, hu1, hu2, ha, w]
  rw [h1, h2, hdel2_eq, hwi, hwj, hsumA, hsumB]
  ring

theorem sumStep_spec {m : ℕ} (r : ℕ) (hrm : r < m) (st : SumState m)
    (hact_ge : ∀ u : Fin m, st.active u = true → r ≤ u.val)
    (hQval : st.Q.Valid)
    (hQsupp : ∀ u : Fin m, st.active u = false → st.Q.l u = 0 ∧ ∀ w : Fin m, st.Q.B u w = 0)
    (e : ℕ)
    (he_bound : e + (Finset.univ.filter (fun u : Fin m => st.active u = true)).card ≤ m)
    (hpow_eq : st.pow2 = fun k : Fin (m + 1) => decide (k.val = e)) :
    let st' := sumStep r st
    (∀ u : Fin m, st'.active u = true → r + 1 ≤ u.val) ∧
    st'.Q.Valid ∧
    (∀ u : Fin m, st'.active u = false → st'.Q.l u = 0 ∧ ∀ w : Fin m, st'.Q.B u w = 0) ∧
    (∃ e' : ℕ, e' + (Finset.univ.filter (fun u : Fin m => st'.active u = true)).card ≤ m ∧
      st'.pow2 = fun k : Fin (m + 1) => decide (k.val = e')) ∧
    (if st'.zero then (0 : ℤ) else
      (oneHotVal st'.pow2 : ℤ) * ∑ a ∈ Supp st'.active, signInt (st'.Q.eval a)) =
    (if st.zero then (0 : ℤ) else
      (oneHotVal st.pow2 : ℤ) * ∑ a ∈ Supp st.active, signInt (st.Q.eval a)) := by
  let i0 : Fin m := ⟨r, hrm⟩
  by_cases hi0 : st.active i0 = true
  · have hi0_in : i0 ∈ Finset.univ.filter (fun u : Fin m => st.active u = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩
    have hact_pos : 1 ≤ (Finset.univ.filter (fun u : Fin m => st.active u = true)).card :=
      Finset.card_pos.mpr ⟨i0, hi0_in⟩
    have he_lt : e < m := by omega
    let cond : Fin m → Bool := fun j => st.active j && z2b (st.Q.B i0 j)
    let isPiv : Fin m → Bool := firstTrue cond
    by_cases hex : ∃ j : Fin m, cond j = true
    · rcases (exists_firstTrue_iff cond).mpr hex with ⟨j0, hj0⟩
      have huniq : ∀ j, isPiv j = true ↔ j = j0 := fun j =>
        ⟨fun h => firstTrue_unique cond h hj0, fun h => h ▸ hj0⟩
      have hfound : (List.finRange m).any isPiv = true :=
        List.any_eq_true.mpr ⟨j0, List.mem_finRange j0, hj0⟩
      have hj0_cond := ((firstTrue_spec cond j0).mp hj0).1
      simp only [cond, Bool.and_eq_true] at hj0_cond
      have hj0_act : st.active j0 = true := hj0_cond.1
      have hj0_B1 : st.Q.B i0 j0 = 1 := by
        have := hj0_cond.2
        rcases z2_cases (st.Q.B i0 j0) with h | h
        · simp [h, z2b_zero] at this
        · exact h
      have hij_ne : i0 ≠ j0 := fun h => by
        rw [h, hQval.1 j0] at hj0_B1
        exact zero_ne_one hj0_B1
      have hb0 : b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.l j))) = st.Q.l j0 := by
        have hany : (List.finRange m).any (fun j => isPiv j && z2b (st.Q.l j)) = z2b (st.Q.l j0) := by
          cases h : z2b (st.Q.l j0)
          · rw [List.any_eq_false]
            intro j _
            by_cases hj : j = j0
            · subst hj; simp [h]
            · have hf : isPiv j = false := by
                cases h' : isPiv j
                · rfl
                · exact absurd ((huniq j).mp h') hj
              simp [hf]
          · exact List.any_eq_true.mpr ⟨j0, List.mem_finRange j0, by simp [isPiv, hj0, h]⟩
        rw [hany, b2z_z2b]
      have hbv_raw : ∀ u, b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.B j u))) = st.Q.B j0 u := by
        intro u
        have hany : (List.finRange m).any (fun j => isPiv j && z2b (st.Q.B j u)) = z2b (st.Q.B j0 u) := by
          cases h : z2b (st.Q.B j0 u)
          · rw [List.any_eq_false]
            intro j _
            by_cases hj : j = j0
            · subst hj; simp [h]
            · have hf : isPiv j = false := by
                cases h' : isPiv j
                · rfl
                · exact absurd ((huniq j).mp h') hj
              simp [hf]
          · exact List.any_eq_true.mpr ⟨j0, List.mem_finRange j0, by simp [isPiv, hj0, h]⟩
        rw [hany, b2z_z2b]
      let act' : Fin m → Bool := fun u => if u = i0 ∨ u = j0 then false else st.active u
      have hact'_eq : (fun u => if u = i0 || isPiv u then false else st.active u) = act' := by
        funext u
        by_cases hu1 : u = i0
        · simp [act', hu1]
        · by_cases hu2 : u = j0
          · subst hu2; simp [act', isPiv, hj0]
          · have hf : isPiv u = false := by
              cases h' : isPiv u
              · rfl
              · exact absurd ((huniq u).mp h') hu2
            simp [act', hu1, hu2, hf]
      let av : Fin m → ZMod 2 := fun u => if act' u then st.Q.B i0 u else 0
      let bv : Fin m → ZMod 2 := fun u => if act' u then st.Q.B j0 u else 0
      let Qdel : Quad m :=
        { B := fun u v => if act' u && act' v then st.Q.B u v else 0
          l := fun u => if act' u then st.Q.l u else 0
          c := st.Q.c }
      let Q' : Quad m := Qdel.addAffineProd (st.Q.l i0) av (st.Q.l j0) bv
      have hact'_pt : ∀ u, (if u = i0 || isPiv u then false else st.active u) = act' u :=
        fun u => congrFun hact'_eq u
      have hst' : sumStep r st = ⟨act', Q', st.zero, shiftOneHot st.pow2⟩ := by
        unfold sumStep
        simp only [hrm, ↓reduceDIte]
        change (if st.active i0 then if (List.finRange m).any isPiv then
          ({ active := fun u => if u = i0 || isPiv u then false else st.active u
             Q := ({ B := fun u v => if (if u = i0 || isPiv u then false else st.active u) &&
                       (if v = i0 || isPiv v then false else st.active v) then st.Q.B u v else 0
                     l := fun u => if (if u = i0 || isPiv u then false else st.active u) then st.Q.l u else 0
                     c := st.Q.c } : Quad m).addAffineProd (st.Q.l i0)
                   (fun u => if (if u = i0 || isPiv u then false else st.active u) then st.Q.B i0 u else 0)
                   (b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.l j))))
                   (fun u => if (if u = i0 || isPiv u then false else st.active u) then
                     b2z ((List.finRange m).any (fun j => isPiv j && z2b (st.Q.B j u))) else 0)
             zero := st.zero
             pow2 := shiftOneHot st.pow2 } : SumState m)
          else _ else _) = _
        simp only [hi0, hfound, ↓reduceIte, hact'_pt, hb0, hbv_raw]
        rfl
      dsimp only
      rw [hst']
      dsimp only
      have hQdel_val : Qdel.Valid := by
        refine ⟨fun u => by dsimp only [Qdel]; split_ifs; exact hQval.1 u; rfl, fun u v => ?_⟩
        dsimp only [Qdel]
        rw [Bool.and_comm, hQval.2 u v]
      have hact'_card : (Finset.univ.filter (fun u : Fin m => act' u = true)).card + 2 =
          (Finset.univ.filter (fun u : Fin m => st.active u = true)).card := by
        have hset : Finset.univ.filter (fun u : Fin m => st.active u = true) =
            insert i0 (insert j0 (Finset.univ.filter (fun u : Fin m => act' u = true))) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, act']
          by_cases hu1 : u = i0
          · subst hu1; simp [hi0]
          · by_cases hu2 : u = j0
            · subst hu2; simp [hj0_act]
            · simp [hu1, hu2]
        have hi_not : i0 ∉ insert j0 (Finset.univ.filter (fun u : Fin m => act' u = true)) := by
          simp [hij_ne, act']
        have hj_not : j0 ∉ Finset.univ.filter (fun u : Fin m => act' u = true) := by
          simp [act']
        rw [hset, Finset.card_insert_of_notMem hi_not, Finset.card_insert_of_notMem hj_not]
      refine ⟨?_, Quad.valid_addAffineProd hQdel_val _ _ _ _, ?_, ?_, ?_⟩
      · intro u hu
        have hne : u ≠ i0 := fun h => by subst h; simp [act'] at hu
        have hu_old : st.active u = true := by
          simp only [act'] at hu
          by_cases h1 : u = i0 ∨ u = j0
          · simp [h1] at hu
          · simp [h1] at hu; exact hu
        have hge := hact_ge u hu_old
        have hval_ne : u.val ≠ r := fun h => hne (Fin.ext h)
        omega
      · intro u hu
        refine ⟨?_, fun w => ?_⟩
        · simp [Q', Quad.addAffineProd, Qdel, av, bv, hu]
        · by_cases huw : u = w
          · simp [Q', Quad.addAffineProd, huw]
          · simp [Q', Quad.addAffineProd, Qdel, av, bv, hu, huw]
      · refine ⟨e + 1, by omega, ?_⟩
        rw [hpow_eq]
        exact shiftOneHot_spec he_lt
      · by_cases hz : st.zero = true
        · simp [hz]
        · have hzf : st.zero = false := by cases h' : st.zero <;> simp_all
          simp only [hzf, Bool.false_eq_true, ↓reduceIte]
          rw [hpow_eq, shiftOneHot_spec he_lt, oneHotVal_eq (by omega : e + 1 ≤ m),
            oneHotVal_eq (by omega : e ≤ m)]
          have hsplit_sum :
              ∑ a ∈ Supp st.active, signInt (st.Q.eval a) =
              2 * ∑ a' ∈ Supp act', signInt (Q'.eval a') := by
            have hbij :
                ∑ a ∈ Supp st.active, signInt (st.Q.eval a) =
                ∑ a' ∈ Supp act', ∑ xi : ZMod 2, ∑ xj : ZMod 2,
                  signInt (st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi)) := by
              have hprod := Finset.sum_product' (Supp act') (Finset.univ : Finset (ZMod 2 × ZMod 2))
                (fun a' p => signInt (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)))
              have hinner : ∀ a' ∈ Supp act',
                  ∑ xi : ZMod 2, ∑ xj : ZMod 2,
                    signInt (st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi)) =
                  ∑ p : ZMod 2 × ZMod 2,
                    signInt (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)) :=
                fun a' _ => (Fintype.sum_prod_type
                  (fun p : ZMod 2 × ZMod 2 => signInt (st.Q.eval (Function.update (Function.update a' j0 p.2) i0 p.1)))).symm
              rw [Finset.sum_congr rfl hinner, ← hprod]
              symm
              refine Finset.sum_bij
                (fun p _ => Function.update (Function.update p.1 j0 p.2.2) i0 p.2.1)
                ?_ ?_ ?_ ?_
              · rintro ⟨a', xi, xj⟩ hp
                have ha' := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩
                have hu1 : u ≠ i0 := fun h => by rw [h, hi0] at hu; exact Bool.noConfusion hu
                have hu2 : u ≠ j0 := fun h => by rw [h, hj0_act] at hu; exact Bool.noConfusion hu
                simp only [Function.update, hu1, hu2, ↓reduceDIte]
                apply ha' u
                simp [act', hu1, hu2, hu]
              · rintro ⟨a1, x1, y1⟩ hp1 ⟨a2, x2, y2⟩ hp2 heq
                have ha1 : ∀ u, act' u = false → a1 u = 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
                have ha2 : ∀ u, act' u = false → a2 u = 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
                have hx : x1 = x2 := by
                  have := congrFun heq i0; simpa using this
                have hy : y1 = y2 := by
                  have := congrFun heq j0; simpa [Ne.symm hij_ne] using this
                have ha : a1 = a2 := by
                  funext u
                  by_cases hu1 : u = i0
                  · rw [hu1, ha1 i0 (by simp [act']), ha2 i0 (by simp [act'])]
                  · by_cases hu2 : u = j0
                    · rw [hu2, ha1 j0 (by simp [act']), ha2 j0 (by simp [act'])]
                    · have := congrFun heq u; simpa [Function.update, hu1, hu2] using this
                rw [ha, hx, hy]
              · intro a ha
                have haS := (Finset.mem_filter.mp ha).2
                let a' := Function.update (Function.update a j0 0) i0 0
                refine ⟨(a', (a i0, a j0)), ?_, ?_⟩
                · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩
                  by_cases hu1 : u = i0
                  · subst hu1; simp [a']
                  · by_cases hu2 : u = j0
                    · subst hu2; simp [a', Ne.symm hij_ne]
                    · have huf : st.active u = false := by simpa [act', hu1, hu2] using hu
                      simp [a', Function.update, hu1, hu2, haS u huf]
                · funext u
                  by_cases hu1 : u = i0
                  · subst hu1; simp
                  · by_cases hu2 : u = j0
                    · subst hu2; simp [Function.update, Ne.symm hij_ne]
                    · simp [a', Function.update, hu1, hu2]
              · intro _ _; rfl
            rw [hbij, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a' _ => ?_)
            let A_val : ZMod 2 := st.Q.l i0 + ∑ u : Fin m, av u * a' u
            let B_val : ZMod 2 := st.Q.l j0 + ∑ u : Fin m, bv u * a' u
            have heval_step : ∀ xi xj : ZMod 2,
                st.Q.eval (Function.update (Function.update a' j0 xj) i0 xi) =
                Qdel.eval a' + (xi * xj + xi * A_val + xj * B_val) :=
              fun xi xj => quad_eval_pair_split st.active st.Q hQval hQsupp i0 j0 hij_ne hj0_B1 a' xi xj
            have hQ'_eval : Q'.eval a' = Qdel.eval a' + A_val * B_val :=
              Quad.eval_addAffineProd Qdel (st.Q.l i0) av (st.Q.l j0) bv a'
            simp_rw [heval_step]
            simp_rw [signInt_add (Qdel.eval a'), ← Finset.mul_sum]
            rw [quadPair_sum, hQ'_eval, signInt_add]
            ring
          rw [hsplit_sum, pow_succ]
          push_cast
          ring
    · push Not at hex
      have hallf : ∀ j, cond j = false := fun j => by
        cases h' : cond j
        · rfl
        · exact absurd h' (hex j)
      have hnoPiv : ∀ j, isPiv j = false := fun j => by
        cases h' : isPiv j
        · rfl
        · have := ((firstTrue_spec cond j).mp h').1
          rw [hallf j] at this; exact Bool.noConfusion this
      have hfound : (List.finRange m).any isPiv = false := by
        rw [List.any_eq_false]; intro j _; simp [hnoPiv j]
      let act' : Fin m → Bool := fun u => if u = i0 then false else st.active u
      have hst' : sumStep r st =
          ⟨act', st.Q.delVar i0, st.zero || z2b (st.Q.l i0),
            if z2b (st.Q.l i0) then st.pow2 else shiftOneHot st.pow2⟩ := by
        unfold sumStep
        simp only [hrm, ↓reduceDIte]
        change (if st.active i0 then if (List.finRange m).any isPiv then _ else
          ({ active := act'
             Q := st.Q.delVar i0
             zero := st.zero || z2b (st.Q.l i0)
             pow2 := if z2b (st.Q.l i0) then st.pow2 else shiftOneHot st.pow2 } : SumState m) else _) = _
        simp only [hi0, hfound, Bool.false_eq_true, ↓reduceIte]
      dsimp only
      rw [hst']
      dsimp only
      have hB_i0_zero : ∀ u : Fin m, st.Q.B i0 u = 0 := by
        intro u
        cases hu : st.active u
        · have h0 := (hQsupp u hu).2 i0
          rwa [hQval.2 u i0] at h0
        · have hcf := hallf u
          simp only [cond, hu, Bool.true_and] at hcf
          rcases z2_cases (st.Q.B i0 u) with h' | h'
          · exact h'
          · simp [h', z2b_one] at hcf
      have hact'_card : (Finset.univ.filter (fun u : Fin m => act' u = true)).card + 1 =
          (Finset.univ.filter (fun u : Fin m => st.active u = true)).card := by
        have hset : Finset.univ.filter (fun u : Fin m => st.active u = true) =
            insert i0 (Finset.univ.filter (fun u : Fin m => act' u = true)) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, act']
          by_cases hu : u = i0
          · subst hu; simp [hi0]
          · simp [hu]
        have hi_not : i0 ∉ Finset.univ.filter (fun u : Fin m => act' u = true) := by simp [act']
        rw [hset, Finset.card_insert_of_notMem hi_not]
      refine ⟨?_, Quad.valid_delVar hQval i0, ?_, ?_, ?_⟩
      · intro u hu
        have hne : u ≠ i0 := fun h => by subst h; simp [act'] at hu
        have hu_old : st.active u = true := by simpa [act', hne] using hu
        have hge := hact_ge u hu_old
        have hval_ne : u.val ≠ r := fun h => hne (Fin.ext h)
        omega
      · intro u hu
        by_cases hui : u = i0
        · subst hui; simp [Quad.delVar]
        · have huf : st.active u = false := by simpa [act', hui] using hu
          refine ⟨by simp [Quad.delVar, hui, (hQsupp u huf).1], fun w => ?_⟩
          by_cases hwi : w = i0
          · simp [Quad.delVar, hwi]
          · simp [Quad.delVar, hui, hwi, (hQsupp u huf).2 w]
      · by_cases hl : z2b (st.Q.l i0) = true
        · refine ⟨e, by omega, by simp [hl, hpow_eq]⟩
        · have hlf : z2b (st.Q.l i0) = false := by cases h' : z2b (st.Q.l i0) <;> simp_all
          refine ⟨e + 1, by omega, ?_⟩
          simp only [hlf, Bool.false_eq_true, ↓reduceIte, hpow_eq]
          exact shiftOneHot_spec he_lt
      · have hsplit_iso :
            ∑ a ∈ Supp st.active, signInt (st.Q.eval a) =
            (if st.Q.l i0 = 0 then 2 else 0) * ∑ a' ∈ Supp act', signInt ((st.Q.delVar i0).eval a') := by
          have hbij :
              ∑ a ∈ Supp st.active, signInt (st.Q.eval a) =
              ∑ a' ∈ Supp act', ∑ xi : ZMod 2,
                signInt (st.Q.eval (Function.update a' i0 xi)) := by
            rw [← Finset.sum_product']
            symm
            refine Finset.sum_bij (fun p _ => Function.update p.1 i0 p.2) ?_ ?_ ?_ ?_
            · rintro ⟨a', xi⟩ hp
              have ha' := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩
              have hu1 : u ≠ i0 := fun h => by rw [h, hi0] at hu; exact Bool.noConfusion hu
              simp only [Function.update, hu1, ↓reduceDIte]
              exact ha' u (by simp [act', hu1, hu])
            · rintro ⟨a1, x1⟩ hp1 ⟨a2, x2⟩ hp2 heq
              have ha1 : ∀ u, act' u = false → a1 u = 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
              have ha2 : ∀ u, act' u = false → a2 u = 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
              have hx : x1 = x2 := by have := congrFun heq i0; simpa using this
              have ha : a1 = a2 := by
                funext u
                by_cases hu : u = i0
                · rw [hu, ha1 i0 (by simp [act']), ha2 i0 (by simp [act'])]
                · have := congrFun heq u; simpa [Function.update, hu] using this
              rw [ha, hx]
            · intro a ha
              have haS := (Finset.mem_filter.mp ha).2
              refine ⟨(Function.update a i0 0, a i0), ?_, ?_⟩
              · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩
                by_cases hu1 : u = i0
                · subst hu1; simp
                · have huf : st.active u = false := by simpa [act', hu1] using hu
                  simp [Function.update, hu1, haS u huf]
              · funext u
                by_cases hu1 : u = i0
                · subst hu1; simp
                · simp [Function.update, hu1]
            · intro _ _; rfl
          rw [hbij, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a' _ => ?_)
          have heval : ∀ xi : ZMod 2,
              st.Q.eval (Function.update a' i0 xi) = (st.Q.delVar i0).eval a' + st.Q.l i0 * xi := by
            intro xi
            rw [Quad.eval_eq_delVar_add hQval i0 (Function.update a' i0 xi)]
            have hB0 : ∑ u : Fin m, (if u = i0 then 0 else st.Q.B i0 u) *
                Function.update a' i0 xi u = 0 := by
              refine Finset.sum_eq_zero (fun u _ => by simp [hB_i0_zero u])
            have hdel : (st.Q.delVar i0).eval (Function.update a' i0 xi) = (st.Q.delVar i0).eval a' := by
              unfold Quad.eval Quad.delVar
              congr 1
              · congr 1
                refine Finset.sum_congr rfl (fun u _ => ?_)
                by_cases hu : u = i0 <;> simp [Function.update, hu]
              · refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
                by_cases hlt : u.val < v.val
                · by_cases hu : u = i0
                  · subst hu; simp [hlt]
                  · by_cases hv : v = i0
                    · subst hv; simp [hlt]
                    · simp [hlt, Function.update, hu, hv]
                · simp [hlt]
            rw [hdel, hB0, add_zero, Function.update_self, mul_comm]
          simp_rw [heval, signInt_add, ← Finset.mul_sum, isoVar_sum]
          ring
        by_cases hz : st.zero = true
        · simp [hz]
        · have hzf : st.zero = false := by cases h' : st.zero <;> simp_all
          rcases z2_cases (st.Q.l i0) with hl | hl
          · simp only [hzf, hl, z2b_zero, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
              hsplit_iso, hpow_eq, shiftOneHot_spec he_lt, oneHotVal_eq (by omega : e + 1 ≤ m),
              oneHotVal_eq (by omega : e ≤ m), pow_succ]
            push_cast
            ring
          · simp only [hzf, hl, z2b_one, Bool.or_true, Bool.false_eq_true, ↓reduceIte, hsplit_iso,
              one_ne_zero, zero_mul, mul_zero]
  · have hi0f : st.active i0 = false := by cases h' : st.active i0 <;> simp_all
    have hst' : sumStep r st = st := by simp [sumStep, hrm, i0, hi0f]
    dsimp only
    rw [hst']
    refine ⟨?_, hQval, hQsupp, ⟨e, he_bound, hpow_eq⟩, rfl⟩
    intro u hu
    have hge := hact_ge u hu
    have hne : u.val ≠ r := fun h => by
      have : u = i0 := Fin.ext h
      rw [this, hi0f] at hu; exact Bool.noConfusion hu
    omega

theorem evalGaussSum_spec {m : ℕ} (free : Fin m → Bool) (Q0 : Quad m)
    (hval0 : Q0.Valid)
    (hsupp0 : ∀ u : Fin m, free u = false → Q0.l u = 0 ∧ ∀ w : Fin m, Q0.B u w = 0) :
    let st := evalGaussSum free Q0
    (∃ e ≤ m, st.pow2 = fun k : Fin (m + 1) => decide (k.val = e)) ∧
    (if st.zero then (0 : ℤ) else (oneHotVal st.pow2 : ℤ) * signInt st.Q.c) =
      ∑ a ∈ Supp free, signInt (Q0.eval a) := by
  have hloop : ∀ r ≤ m,
      let st := (List.range r).foldl (fun s i => sumStep i s)
        ⟨free, Q0, false, fun k => decide (k.val = 0)⟩
      (∀ u : Fin m, st.active u = true → r ≤ u.val) ∧
      st.Q.Valid ∧
      (∀ u : Fin m, st.active u = false → st.Q.l u = 0 ∧ ∀ w : Fin m, st.Q.B u w = 0) ∧
      (∃ e : ℕ, e + (Finset.univ.filter (fun u : Fin m => st.active u = true)).card ≤ m ∧
        st.pow2 = fun k : Fin (m + 1) => decide (k.val = e)) ∧
      (if st.zero then (0 : ℤ) else
        (oneHotVal st.pow2 : ℤ) * ∑ a ∈ Supp st.active, signInt (st.Q.eval a)) =
      ∑ a ∈ Supp free, signInt (Q0.eval a) := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨fun _ _ => Nat.zero_le _, hval0, hsupp0,
        ⟨0, by rw [zero_add]; exact (Finset.card_le_univ _).trans (by simp), rfl⟩, ?_⟩
      change (if false then (0 : ℤ) else (oneHotVal (fun k : Fin (m + 1) => decide (k.val = 0)) : ℤ) *
        ∑ a ∈ Supp free, signInt (Q0.eval a)) = _
      simp only [Bool.false_eq_true, ↓reduceIte, oneHotVal_eq (L := m) (Nat.zero_le m), pow_zero,
        Nat.cast_one, one_mul]
    | succ r ih =>
      intro hr
      rcases ih (by omega) with ⟨hact_ge, hQval, hQsupp, ⟨e, he_bound, hpow_eq⟩, hsum_eq⟩
      set st := (List.range r).foldl (fun s i => sumStep i s)
        ⟨free, Q0, false, fun k => decide (k.val = 0)⟩
      have hst_next : (List.range (r + 1)).foldl (fun s i => sumStep i s)
          ⟨free, Q0, false, fun k => decide (k.val = 0)⟩ = sumStep r st := by
        simp [List.range_succ, List.foldl_append, st]
      dsimp only
      rw [hst_next]
      rcases sumStep_spec r (by omega) st hact_ge hQval hQsupp e he_bound hpow_eq with
        ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, h4, h5.trans hsum_eq⟩
  rcases hloop m le_rfl with ⟨hact_ge, _, _, ⟨e, he_bound, hpow_eq⟩, hsum_eq⟩
  intro st
  have hsum_eq' : (if st.zero then (0 : ℤ) else
      (oneHotVal st.pow2 : ℤ) * ∑ a ∈ Supp st.active, signInt (st.Q.eval a)) =
      ∑ a ∈ Supp free, signInt (Q0.eval a) := hsum_eq
  have hall_false : ∀ u : Fin m, st.active u = false := fun u => by
    cases h' : st.active u
    · rfl
    · have := hact_ge u h'; omega
  have hsupp_sing : Supp st.active = {0} := by
    ext a
    simp only [Supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext u; exact h u (hall_false u)
    · rintro rfl u _; rfl
  have heval0 : st.Q.eval 0 = st.Q.c := by simp [Quad.eval]
  refine ⟨⟨e, by omega, hpow_eq⟩, ?_⟩
  rw [← hsum_eq', hsupp_sing, Finset.sum_singleton, heval0]

def sumSigs {N m : ℕ} (st : (Fin N → Bool) → SumState m) : Set (Sig N) :=
  Set.range (fun u : Fin m => fun x => (st x).active u) ∪
  quadSigs (fun x => (st x).Q) ∪
  {fun x => (st x).zero} ∪
  Set.range (fun k : Fin (m + 1) => fun x => (st x).pow2 k)

theorem sumStepB {N m : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (i : ℕ) (st : (Fin N → Bool) → SumState m) :
    Build (Base ∪ sumSigs st) (sumSigs (fun x => sumStep i (st x)))
      (m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40)) := by
  by_cases hi : i < m
  · let i0 : Fin m := ⟨i, hi⟩
    let cond : Fin m → Sig N := fun j x => (st x).active j && z2b ((st x).Q.B i0 j)
    let isPiv : Fin m → Sig N := fun j x => firstTrue (fun u => cond u x) j
    let found : Sig N := fun x => (List.finRange m).any (fun j => isPiv j x)
    let actIso : Fin m → Sig N := fun u x => if u = i0 then false else (st x).active u
    let actPair : Fin m → Sig N := fun u x => if u = i0 || isPiv u x then false else (st x).active u
    let b0 : Sig N := fun x => (List.finRange m).any (fun j => isPiv j x && z2b ((st x).Q.l j))
    let bvRaw : Fin m → Sig N := fun u x => (List.finRange m).any (fun j => isPiv j x && z2b ((st x).Q.B j u))
    have hcondB : Build (Base ∪ sumSigs st) (Set.range cond) (m * 1) :=
      finSigB cond 1 (fun j =>
        andB (Or.inr (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩))))
          (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨i0, j, rfl⟩)))))))
    have hftB : Build ((Base ∪ sumSigs st) ∪ Set.range cond) (Set.range isPiv) (m * (m + 2)) :=
      firstTrueB cond (Or.inl (Or.inl hfalse)) (fun j => Or.inr ⟨j, rfl⟩)
    let A1 := (Base ∪ sumSigs st) ∪ (Set.range cond ∪ Set.range isPiv)
    have h1 : Build (Base ∪ sumSigs st) (Set.range cond ∪ Set.range isPiv) (m * 1 + m * (m + 2)) :=
      seqB hcondB hftB
    have hfoundB : Build A1 {found} m := by
      have h := orListB (A := A1) ((List.finRange m).map isPiv)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr (Or.inr ⟨j, rfl⟩))
        (Or.inl (Or.inl hfalse))
      have heq : (fun x => ((List.finRange m).map isPiv).any (fun f => f x)) = found := by
        funext x; simp [found, List.any_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at h
      exact h
    have hactPairB : Build A1 (Set.range actPair) (m * 2) := by
      refine finSigB actPair 2 (fun u => ?_)
      by_cases hu : u = i0
      · have heq : actPair u = fun _ => false := by funext x; simp [actPair, hu]
        rw [heq]
        exact relaxB (idleB (A := A1) (B := {fun _ => false})
          (Set.singleton_subset_iff.mpr (Or.inl (Or.inl hfalse))))
          le_rfl Set.subset_union_right (by omega)
      · have heq : actPair u = fun x => !(isPiv u x) && (st x).active u := by
          funext x; simp only [actPair, hu, decide_false, Bool.false_or]
          cases isPiv u x <;> rfl
        rw [heq]
        have hn : Build A1 {fun x => !(isPiv u x)} 1 := notB (Or.inr (Or.inr ⟨u, rfl⟩))
        have ha : Build (A1 ∪ {fun x => !(isPiv u x)}) {fun x => !(isPiv u x) && (st x).active u} 1 :=
          andB (Or.inr rfl) (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩))))))
        exact seq2B hn ha
    have hb0B : Build A1 {b0} (2 * m) := by
      let term : Fin m → Sig N := fun j x => isPiv j x && z2b ((st x).Q.l j)
      have ht : Build A1 (Set.range term) (m * 1) :=
        finSigB term 1 (fun j =>
          andB (Or.inr (Or.inr ⟨j, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩))))))))
      have hor : Build (A1 ∪ Set.range term) {b0} m := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange m).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr ⟨j, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange m).map term).any (fun f => f x)) = b0 := by
          funext x; simp [b0, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have hbvRawB : Build A1 (Set.range bvRaw) (m * (2 * m)) := by
      refine finSigB bvRaw (2 * m) (fun u => ?_)
      let term : Fin m → Sig N := fun j x => isPiv j x && z2b ((st x).Q.B j u)
      have ht : Build A1 (Set.range term) (m * 1) :=
        finSigB term 1 (fun j =>
          andB (Or.inr (Or.inr ⟨j, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨j, u, rfl⟩))))))))
      have hor : Build (A1 ∪ Set.range term) {bvRaw u} m := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange m).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr ⟨j, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange m).map term).any (fun f => f x)) = bvRaw u := by
          funext x; simp [bvRaw, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    let B2 := (({found} ∪ Set.range actPair) ∪ {b0}) ∪ Set.range bvRaw
    have h2 : Build A1 B2 (m + m * 2 + 2 * m + m * (2 * m)) :=
      unionB (unionB (unionB hfoundB hactPairB) hb0B) hbvRawB
    let A2 := A1 ∪ B2
    let avZ : (Fin N → Bool) → Fin m → ZMod 2 := fun x u => if actPair u x then (st x).Q.B i0 u else 0
    let bvZ : (Fin N → Bool) → Fin m → ZMod 2 := fun x u => if actPair u x then b2z (bvRaw u x) else 0
    let QdelPair : (Fin N → Bool) → Quad m := fun x =>
      { B := fun u v => if actPair u x && actPair v x then (st x).Q.B u v else 0
        l := fun u => if actPair u x then (st x).Q.l u else 0
        c := (st x).Q.c }
    let Qpair : (Fin N → Bool) → Quad m :=
      fun x => (QdelPair x).addAffineProd ((st x).Q.l i0) (avZ x) (b2z (b0 x)) (bvZ x)
    have hprepB : Build A2
        (Set.range (fun u : Fin m => fun x => z2b (avZ x u)) ∪
         Set.range (fun u : Fin m => fun x => z2b (bvZ x u)) ∪
         quadSigs QdelPair)
        (m * 1 + m * 1 + (m * (m * 2) + m * 1)) := by
      have havB : Build A2 (Set.range (fun u : Fin m => fun x => z2b (avZ x u))) (m * 1) :=
        finSigB _ 1 (fun u => by
          have heq : (fun x => z2b (avZ x u)) = fun x => actPair u x && z2b ((st x).Q.B i0 u) := by
            funext x; cases h : actPair u x <;> simp [avZ, h, z2b_zero]
          rw [heq]
          exact andB (Or.inr (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
            (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨i0, u, rfl⟩)))))))))
      have hbvB : Build A2 (Set.range (fun u : Fin m => fun x => z2b (bvZ x u))) (m * 1) :=
        finSigB _ 1 (fun u => by
          have heq : (fun x => z2b (bvZ x u)) = fun x => actPair u x && bvRaw u x := by
            funext x; cases h : actPair u x <;> simp [bvZ, h, z2b_zero, z2b_b2z]
          rw [heq]
          exact andB (Or.inr (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩)))) (Or.inr (Or.inr ⟨u, rfl⟩)))
      have hQdelB : Build A2 (quadSigs QdelPair) (m * (m * 2) + m * 1) := by
        have hB : Build A2 {f | ∃ u v, (fun x => z2b ((QdelPair x).B u v)) = f} (m * (m * 2)) :=
          fin2SigB _ 2 (fun u v => by
            let t1 : Sig N := fun x => actPair u x && actPair v x
            let out : Sig N := fun x => t1 x && z2b ((st x).Q.B u v)
            have ht1 : Build A2 {t1} 1 :=
              andB (Or.inr (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩)))) (Or.inr (Or.inl (Or.inl (Or.inr ⟨v, rfl⟩))))
            have hout : Build (A2 ∪ {t1}) {out} 1 :=
              andB (Or.inr rfl)
                (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u, v, rfl⟩)))))))))
            have heq : out = fun x => z2b ((QdelPair x).B u v) := by
              funext x; simp only [out, t1, QdelPair]
              cases actPair u x && actPair v x <;> simp [z2b_zero]
            rw [← heq]
            exact seq2B ht1 hout)
        have hL : Build A2 (Set.range (fun u : Fin m => fun x => z2b ((QdelPair x).l u))) (m * 1) :=
          finSigB _ 1 (fun u => by
            have heq : (fun x => z2b ((QdelPair x).l u)) = fun x => actPair u x && z2b ((st x).Q.l u) := by
              funext x; cases h : actPair u x <;> simp [QdelPair, h, z2b_zero]
            rw [heq]
            exact andB (Or.inr (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
              (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))))))
        have hC : Build A2 {fun x => z2b (QdelPair x).c} 0 :=
          idleB (Set.singleton_subset_iff.mpr
            (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
        exact relaxB (unionB (unionB hB hL) hC) le_rfl Set.subset_union_right (by omega)
      exact unionB (unionB havB hbvB) hQdelB
    let A3 := A2 ∪ (Set.range (fun u : Fin m => fun x => z2b (avZ x u)) ∪
      Set.range (fun u : Fin m => fun x => z2b (bvZ x u)) ∪ quadSigs QdelPair)
    have hb0_in : (fun x => z2b (b2z (b0 x))) ∈ A3 := by
      have : (fun x => z2b (b2z (b0 x))) = b0 := funext (fun x => z2b_b2z (b0 x))
      rw [this]; exact Or.inl (Or.inr (Or.inl (Or.inr rfl)))
    have hQpairB : Build A3 (quadSigs Qpair) (m * (m * 10) + m * 15 + 5) :=
      addAffineProdB A3 (Or.inl (Or.inl (Or.inl (Or.inl hfalse)))) QdelPair
        (fun x => (st x).Q.l i0) (fun x => b2z (b0 x)) avZ bvZ
        (Set.subset_union_right.trans (by intro f hf; exact Or.inr hf))
        (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0, rfl⟩)))))))))
        hb0_in
        (fun u => Or.inr (Or.inl (Or.inl ⟨u, rfl⟩)))
        (fun u => Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))
    let A4 := A3 ∪ quadSigs Qpair
    have hactIso_in : ∀ u, actIso u ∈ A4 := fun u => by
      by_cases hu : u = i0
      · have : actIso u = fun _ => false := by funext x; simp [actIso, hu]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
      · have : actIso u = fun x => (st x).active u := by funext x; simp [actIso, hu]
        rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩)))))))
    have hQiso_in : quadSigs (fun x => (st x).Q.delVar i0) ⊆ A4 := by
      rintro g ((⟨u, v, rfl⟩ | ⟨u, rfl⟩) | rfl)
      · by_cases h1 : u = i0 ∨ v = i0
        · have : (fun x => z2b (((st x).Q.delVar i0).B u v)) = fun _ => false := by
            funext x; simp [Quad.delVar, h1, z2b_zero]
          rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
        · have : (fun x => z2b (((st x).Q.delVar i0).B u v)) = fun x => z2b ((st x).Q.B u v) := by
            funext x; simp [Quad.delVar, h1]
          rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u, v, rfl⟩)))))))))
      · dsimp only
        by_cases h1 : u = i0
        · have : (fun x => z2b (((st x).Q.delVar i0).l u)) = fun _ => false := by
            funext x; simp [Quad.delVar, h1, z2b_zero]
          rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
        · have : (fun x => z2b (((st x).Q.delVar i0).l u)) = fun x => z2b ((st x).Q.l u) := by
            funext x; simp [Quad.delVar, h1]
          rw [this]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
    have hsh_in : ∀ k : Fin (m + 1), (fun x => shiftOneHot (st x).pow2 k) ∈ A4 := fun k => by
      unfold shiftOneHot
      by_cases h0 : k.val = 0
      · simp only [h0, ↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hfalse))))
      · simp only [h0, ↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨⟨k.val - 1, by omega⟩, rfl⟩)))))
    have hmux2 : ∀ (fa fb fc : Sig N), fa ∈ A4 → fb ∈ A4 → fc ∈ A4 →
        Build A4 {fun x => if (st x).active i0 then (if found x then fa x else fb x) else fc x} 8 := by
      intro fa fb fc hfa hfb hfc
      let inner : Sig N := fun x => if found x then fa x else fb x
      have h_in : Build A4 {inner} 4 := iteB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))) hfa hfb
      have h_out : Build (A4 ∪ {inner})
          {fun x => if (st x).active i0 then inner x else fc x} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0, rfl⟩)))))))))
          (Or.inr rfl) (Or.inl hfc)
      exact seq2B h_in h_out
    have hactOut : Build A4 (Set.range (fun u : Fin m => fun x => (sumStep i (st x)).active u)) (m * 8) :=
      finSigB _ 8 (fun u => by
        have heq : (fun x => (sumStep i (st x)).active u) =
            fun x => if (st x).active i0 then (if found x then actPair u x else actIso u x) else (st x).active u := by
          funext x
          simp only [sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found, actPair, actIso]
          cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
        rw [heq]
        exact hmux2 (actPair u) (actIso u) (fun x => (st x).active u)
          (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))))
          (hactIso_in u)
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨u, rfl⟩)))))))))
    have hQOut : Build A4 (quadSigs (fun x => (sumStep i (st x)).Q)) (m * (m * 8) + m * 8 + 8) := by
      have hB : Build A4 {f | ∃ u v, (fun x => z2b ((sumStep i (st x)).Q.B u v)) = f} (m * (m * 8)) :=
        fin2SigB _ 8 (fun u v => by
          have heq : (fun x => z2b ((sumStep i (st x)).Q.B u v)) =
              fun x => if (st x).active i0 then
                (if found x then z2b ((Qpair x).B u v) else z2b (((st x).Q.delVar i0).B u v))
              else z2b ((st x).Q.B u v) := by
            funext x
            simp only [sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found, Qpair, QdelPair,
              actPair, b0, bvZ, bvRaw, avZ]
            cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
          rw [heq]
          exact hmux2 _ _ _ (Or.inr (Or.inl (Or.inl ⟨u, v, rfl⟩)))
            (hQiso_in (Or.inl (Or.inl ⟨u, v, rfl⟩)))
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨u, v, rfl⟩)))))))))))
      have hL : Build A4 (Set.range (fun u : Fin m => fun x => z2b ((sumStep i (st x)).Q.l u))) (m * 8) :=
        finSigB _ 8 (fun u => by
          have heq : (fun x => z2b ((sumStep i (st x)).Q.l u)) =
              fun x => if (st x).active i0 then
                (if found x then z2b ((Qpair x).l u) else z2b (((st x).Q.delVar i0).l u))
              else z2b ((st x).Q.l u) := by
            funext x
            simp only [sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found, Qpair, QdelPair,
              actPair, b0, bvZ, bvRaw, avZ]
            cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
          rw [heq]
          exact hmux2 _ _ _ (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))
            (hQiso_in (Or.inl (Or.inr ⟨u, rfl⟩)))
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨u, rfl⟩)))))))))))
      have hC : Build A4 {fun x => z2b (sumStep i (st x)).Q.c} 8 := by
        have heq : (fun x => z2b (sumStep i (st x)).Q.c) =
            fun x => if (st x).active i0 then
              (if found x then z2b (Qpair x).c else z2b ((st x).Q.delVar i0).c)
            else z2b (st x).Q.c := by
          funext x
          simp only [sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found, Qpair, QdelPair,
            actPair, b0, bvZ, bvRaw, avZ]
          cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
        rw [heq]
        exact hmux2 _ _ _ (Or.inr (Or.inr rfl))
          (hQiso_in (Or.inr rfl))
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))))))
      exact relaxB (unionB (unionB hB hL) hC) le_rfl Set.subset_union_right (by omega)
    have hzeroOut : Build A4 {fun x => (sumStep i (st x)).zero} 9 := by
      let zIso : Sig N := fun x => (st x).zero || z2b ((st x).Q.l i0)
      have hz1 : Build A4 {zIso} 1 :=
        orB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0, rfl⟩))))))))))
      let inner : Sig N := fun x => if found x then (st x).zero else zIso x
      have hz2 : Build (A4 ∪ {zIso}) {inner} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))))
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))) (Or.inr rfl)
      have hz3 : Build ((A4 ∪ {zIso}) ∪ {inner})
          {fun x => if (st x).active i0 then inner x else (st x).zero} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0, rfl⟩))))))))))
          (Or.inr rfl)
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr rfl)))))))))
      have heq : (fun x => if (st x).active i0 then inner x else (st x).zero) =
          fun x => (sumStep i (st x)).zero := by
        funext x
        simp only [inner, zIso, sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found]
        cases (st x).active i0 <;> cases (List.finRange m).any _ <;> rfl
      rw [← heq]
      exact relaxB (transB (transB (extB hz1) (extB hz2)) hz3) le_rfl Set.subset_union_right (by omega)
    have hpowOut : Build A4 (Set.range (fun k : Fin (m + 1) => fun x => (sumStep i (st x)).pow2 k))
        ((m + 1) * 12) := by
      refine finSigB _ 12 (fun k => ?_)
      let pIso : Sig N := fun x => if z2b ((st x).Q.l i0) then (st x).pow2 k else shiftOneHot (st x).pow2 k
      have hp1 : Build A4 {pIso} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨i0, rfl⟩))))))))))
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨k, rfl⟩)))))) (hsh_in k)
      let inner : Sig N := fun x => if found x then shiftOneHot (st x).pow2 k else pIso x
      have hp2 : Build (A4 ∪ {pIso}) {inner} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl rfl)))))))
          (Or.inl (hsh_in k)) (Or.inr rfl)
      have hp3 : Build ((A4 ∪ {pIso}) ∪ {inner})
          {fun x => if (st x).active i0 then inner x else (st x).pow2 k} 4 :=
        iteB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨i0, rfl⟩))))))))))
          (Or.inr rfl)
          (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨k, rfl⟩))))))))
      have heq : (fun x => if (st x).active i0 then inner x else (st x).pow2 k) =
          fun x => (sumStep i (st x)).pow2 k := by
        funext x
        simp only [inner, pIso, sumStep, hi, ↓reduceDIte, i0, cond, isPiv, found]
        cases (st x).active i0 <;> cases (List.finRange m).any _ <;> cases z2b ((st x).Q.l i0) <;> rfl
      rw [← heq]
      exact relaxB (transB (transB (extB hp1) (extB hp2)) hp3) le_rfl Set.subset_union_right (by omega)
    have hOut := unionB (unionB (unionB hactOut hQOut) hzeroOut) hpowOut
    have hall := transB (transB (transB (transB (extB h1) (extB h2)) (extB hprepB)) (extB hQpairB)) hOut
    exact relaxB hall le_rfl Set.subset_union_right (by ring_nf; omega)
  · have heq : (fun x => sumStep i (st x)) = st := by funext x; simp [sumStep, hi]
    rw [heq]
    exact relaxB (idleB (A := Base ∪ sumSigs st) (B := sumSigs st) Set.subset_union_right)
      le_rfl Set.subset_union_right (Nat.zero_le _)

theorem evalGaussSumB {N m : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (free : (Fin N → Bool) → Fin m → Bool)
    (Q0 : (Fin N → Bool) → Quad m)
    (hfree : ∀ u, (fun x => free x u) ∈ Base)
    (hQ0 : quadSigs Q0 ⊆ Base) :
    Build Base (sumSigs (fun x => evalGaussSum (free x) (Q0 x)))
      (m * (m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40))) := by
  let st0 : (Fin N → Bool) → SumState m :=
    fun x => ⟨free x, Q0 x, false, fun k => decide (k.val = 0)⟩
  have hst0 : sumSigs st0 ⊆ Base := by
    rintro f (((⟨u, rfl⟩ | hq) | rfl) | ⟨k, rfl⟩)
    · exact hfree u
    · exact hQ0 hq
    · exact hfalse
    · by_cases hk : k.val = 0
      · simpa [st0, hk] using htrue
      · simpa [st0, hk] using hfalse
  have hit := iterB (Sigs := sumSigs) (step := sumStep)
    (c := m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40))
    (Base := Base) (fun i st => sumStepB Base hfalse i st) m st0
  exact relaxB hit (Set.union_subset le_rfl hst0) Set.subset_union_right le_rfl

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

def combineQuads {m h : ℕ} (qs : Fin h → Quad m) (σ : Fin h → ZMod 2) : Quad m :=
  { B := fun u v => ∑ s : Fin h, σ s * (qs s).B u v
    l := fun u => ∑ s : Fin h, σ s * (qs s).l u
    c := ∑ s : Fin h, σ s * (qs s).c }

theorem combineQuads_valid {m h : ℕ} (qs : Fin h → Quad m) (hval : ∀ s, (qs s).Valid)
    (σ : Fin h → ZMod 2) : (combineQuads qs σ).Valid := by
  refine ⟨fun u => by simp [combineQuads, fun s => (hval s).1 u], fun u v => ?_⟩
  dsimp only [combineQuads]
  exact Finset.sum_congr rfl (fun s _ => by rw [(hval s).2 u v])

theorem combineQuads_supp {m h : ℕ} (qs : Fin h → Quad m) (free : Fin m → Bool)
    (hsupp : ∀ s u, free u = false → (qs s).l u = 0 ∧ ∀ w, (qs s).B u w = 0)
    (σ : Fin h → ZMod 2) :
    ∀ u, free u = false → (combineQuads qs σ).l u = 0 ∧ ∀ w, (combineQuads qs σ).B u w = 0 := by
  intro u hu
  refine ⟨by simp [combineQuads, fun s => (hsupp s u hu).1],
    fun w => by simp [combineQuads, fun s => (hsupp s u hu).2 w]⟩

theorem combineQuads_eval {m h : ℕ} (qs : Fin h → Quad m) (σ : Fin h → ZMod 2)
    (a : Fin m → ZMod 2) :
    (combineQuads qs σ).eval a = ∑ s : Fin h, σ s * (qs s).eval a := by
  unfold combineQuads Quad.eval
  have hlin : (∑ i : Fin m, (∑ s : Fin h, σ s * (qs s).l i) * a i) =
      ∑ s : Fin h, σ s * ∑ i : Fin m, (qs s).l i * a i := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun i _ => by ring))
  have hquad : (∑ i : Fin m, ∑ j : Fin m,
        if i.val < j.val then (∑ s : Fin h, σ s * (qs s).B i j) * a i * a j else 0) =
      ∑ s : Fin h, σ s * ∑ i : Fin m, ∑ j : Fin m,
        if i.val < j.val then (qs s).B i j * a i * a j else 0 := by
    have hinner : ∀ i j : Fin m,
        (if i.val < j.val then (∑ s : Fin h, σ s * (qs s).B i j) * a i * a j else 0) =
        ∑ s : Fin h, if i.val < j.val then σ s * ((qs s).B i j * a i * a j) else 0 := by
      intro i j
      by_cases hlt : i.val < j.val
      · simp only [hlt, ↓reduceIte, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s _ => by ring)
      · simp [hlt]
    simp_rw [hinner]
    trans (∑ i : Fin m, ∑ s : Fin h, ∑ j : Fin m,
        if i.val < j.val then σ s * ((qs s).B i j * a i * a j) else 0)
    · exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      by_cases hlt : i.val < j.val <;> simp [hlt]
  rw [hlin, hquad, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => by ring)

theorem combineQuadsB {N m h : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (qs : (Fin N → Bool) → Fin h → Quad m)
    (hqs : ∀ s : Fin h, quadSigs (fun x => qs x s) ⊆ Base)
    (σ : Fin h → ZMod 2) :
    Build Base (quadSigs (fun x => combineQuads (qs x) σ))
      (m * (m * (4 * h)) + m * (4 * h) + 4 * h) := by
  have hBB : Build Base {f | ∃ u v, (fun x => z2b ((combineQuads (qs x) σ).B u v)) = f}
      (m * (m * (4 * h))) := by
    refine fin2SigB _ (4 * h) (fun u v => ?_)
    let xs : List (Sig N) := (List.finRange h).map (fun s =>
      if z2b (σ s) then (fun x => z2b ((qs x s).B u v)) else (fun _ => false))
    have hxs : ∀ f ∈ xs, f ∈ Base := by
      intro f hf
      rcases List.mem_map.mp hf with ⟨s, _, rfl⟩
      by_cases hs : z2b (σ s) = true
      · simp only [hs, ↓reduceIte]; exact hqs s (Or.inl (Or.inl ⟨u, v, rfl⟩))
      · simp [hs, hfalse]
    have hxl := xorListB xs hxs hfalse
    have heq : (fun x => xorList (xs.map fun f => f x)) =
        fun x => z2b ((combineQuads (qs x) σ).B u v) := by
      funext x
      simp only [combineQuads, z2b_fin_sum, xs, List.map_map]
      congr 1
      refine List.map_congr_left (fun s _ => ?_)
      simp only [Function.comp_apply, z2b_mul]
      cases z2b (σ s) <;> simp
    rw [heq, List.length_map, List.length_finRange] at hxl
    exact hxl
  have hLL : Build Base (Set.range (fun u : Fin m => fun x => z2b ((combineQuads (qs x) σ).l u)))
      (m * (4 * h)) := by
    refine finSigB _ (4 * h) (fun u => ?_)
    let xs : List (Sig N) := (List.finRange h).map (fun s =>
      if z2b (σ s) then (fun x => z2b ((qs x s).l u)) else (fun _ => false))
    have hxs : ∀ f ∈ xs, f ∈ Base := by
      intro f hf
      rcases List.mem_map.mp hf with ⟨s, _, rfl⟩
      by_cases hs : z2b (σ s) = true
      · simp only [hs, ↓reduceIte]; exact hqs s (Or.inl (Or.inr ⟨u, rfl⟩))
      · simp [hs, hfalse]
    have hxl := xorListB xs hxs hfalse
    have heq : (fun x => xorList (xs.map fun f => f x)) =
        fun x => z2b ((combineQuads (qs x) σ).l u) := by
      funext x
      simp only [combineQuads, z2b_fin_sum, xs, List.map_map]
      congr 1
      refine List.map_congr_left (fun s _ => ?_)
      simp only [Function.comp_apply, z2b_mul]
      cases z2b (σ s) <;> simp
    rw [heq, List.length_map, List.length_finRange] at hxl
    exact hxl
  have hCC : Build Base {fun x => z2b (combineQuads (qs x) σ).c} (4 * h) := by
    let xs : List (Sig N) := (List.finRange h).map (fun s =>
      if z2b (σ s) then (fun x => z2b (qs x s).c) else (fun _ => false))
    have hxs : ∀ f ∈ xs, f ∈ Base := by
      intro f hf
      rcases List.mem_map.mp hf with ⟨s, _, rfl⟩
      by_cases hs : z2b (σ s) = true
      · simp only [hs, ↓reduceIte]; exact hqs s (Or.inr rfl)
      · simp [hs, hfalse]
    have hxl := xorListB xs hxs hfalse
    have heq : (fun x => xorList (xs.map fun f => f x)) =
        fun x => z2b (combineQuads (qs x) σ).c := by
      funext x
      simp only [combineQuads, z2b_fin_sum, xs, List.map_map]
      congr 1
      refine List.map_congr_left (fun s _ => ?_)
      simp only [Function.comp_apply, z2b_mul]
      cases z2b (σ s) <;> simp
    rw [heq, List.length_map, List.length_finRange] at hxl
    exact hxl
  exact relaxB (unionB (unionB hBB hLL) hCC) le_rfl Set.subset_union_right (by omega)

def posContrib {m : ℕ} (st : SumState m) : ℕ :=
  if !(st.zero) && !(z2b st.Q.c) then oneHotVal st.pow2 else 0

def negContrib {m : ℕ} (st : SumState m) : ℕ :=
  if !(st.zero) && z2b st.Q.c then oneHotVal st.pow2 else 0

theorem contrib_sub_eq {m : ℕ} (st : SumState m) :
    (posContrib st : ℤ) - (negContrib st : ℤ) =
      if st.zero then 0 else (oneHotVal st.pow2 : ℤ) * signInt st.Q.c := by
  unfold posContrib negContrib signInt
  cases hz : st.zero
  · rcases z2_cases st.Q.c with hc | hc
    · simp [hc, z2b_zero]
    · simp [hc, z2b_one]
  · simp

theorem posContrib_le {m : ℕ} (st : SumState m) (e : ℕ) (he : e ≤ m)
    (hp : st.pow2 = fun k : Fin (m + 1) => decide (k.val = e)) :
    posContrib st ≤ 2 ^ m ∧ negContrib st ≤ 2 ^ m := by
  unfold posContrib negContrib
  rw [hp, oneHotVal_eq he]
  have hle : 2 ^ e ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) he
  constructor <;> split_ifs <;> first | exact hle | exact Nat.zero_le _

def countOneHot {m : ℕ} (u : Fin m → Bool) : Fin (m + 1) → Bool :=
  (List.range m).foldl
    (fun p r => if hr : r < m then (if u ⟨r, hr⟩ then shiftOneHot p else p) else p)
    (fun k => decide (k.val = 0))

theorem countOneHot_spec {m : ℕ} (u : Fin m → Bool) :
    countOneHot u = fun k : Fin (m + 1) =>
      decide (k.val = (Finset.univ.filter (fun j : Fin m => u j = true)).card) := by
  have hloop : ∀ r ≤ m,
      (List.range r).foldl
        (fun p i => if hi : i < m then (if u ⟨i, hi⟩ then shiftOneHot p else p) else p)
        (fun k : Fin (m + 1) => decide (k.val = 0)) =
      fun k : Fin (m + 1) =>
        decide (k.val = (Finset.univ.filter (fun j : Fin m => j.val < r ∧ u j = true)).card) := by
    intro r
    induction r with
    | zero =>
      intro _; funext k; simp
    | succ r ih =>
      intro hr
      have hrm : r < m := by omega
      let j0 : Fin m := ⟨r, hrm⟩
      set Sr := Finset.univ.filter (fun j : Fin m => j.val < r ∧ u j = true)
      set Sr1 := Finset.univ.filter (fun j : Fin m => j.val < r + 1 ∧ u j = true)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [hrm, ↓reduceDIte]
      by_cases hu : u j0 = true
      · have hSr1_eq : Sr1 = insert j0 Sr := by
          ext j
          simp only [Sr1, Sr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hju⟩
            by_cases hje : j.val = r
            · left; exact Fin.ext hje
            · right; exact ⟨by omega, hju⟩
          · rintro (rfl | ⟨hlt, hju⟩)
            · exact ⟨by simp [j0], hu⟩
            · exact ⟨by omega, hju⟩
        have hj0_not : j0 ∉ Sr := by simp [Sr, j0]
        have hlt_m : Sr.card < m := by
          have hsub : Sr1.card ≤ m := by
            calc Sr1.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
              _ = m := Fintype.card_fin m
          rw [hSr1_eq, Finset.card_insert_of_notMem hj0_not] at hsub
          omega
        simp only [j0, hu, ↓reduceIte]
        rw [shiftOneHot_spec hlt_m, hSr1_eq, Finset.card_insert_of_notMem hj0_not]
      · have huf : u j0 = false := by cases h' : u j0 <;> simp_all
        have hSr1_eq : Sr1 = Sr := by
          ext j
          simp only [Sr1, Sr, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hju⟩
            refine ⟨?_, hju⟩
            by_contra hge
            have hje : j = j0 := Fin.ext (by dsimp [j0]; omega)
            rw [hje, huf] at hju; exact Bool.noConfusion hju
          · rintro ⟨hlt, hju⟩; exact ⟨by omega, hju⟩
        simp only [j0, huf, Bool.false_eq_true, ↓reduceIte, hSr1_eq]
  rw [countOneHot, hloop m le_rfl]
  funext k
  congr 1
  congr 1
  congr 1
  ext j
  simp

theorem countOneHotB {N m : ℕ} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (u : (Fin N → Bool) → Fin m → Bool)
    (hu : ∀ j : Fin m, (fun x => u x j) ∈ Base) :
    Build Base (Set.range (fun k : Fin (m + 1) => fun x => countOneHot (u x) k))
      (m * ((m + 1) * 4)) := by
  let Sigs : ((Fin N → Bool) → (Fin (m + 1) → Bool)) → Set (Sig N) :=
    fun p => Set.range (fun k : Fin (m + 1) => fun x => p x k)
  let st0 : (Fin N → Bool) → (Fin (m + 1) → Bool) := fun _ k => decide (k.val = 0)
  have hst0 : Sigs st0 ⊆ Base := by
    rintro _ ⟨k, rfl⟩
    dsimp only
    by_cases hk : k = 0
    · have heq : (fun x : Fin N → Bool => st0 x k) = (fun _ => true) := by
        funext _; simp [st0, hk]
      rw [heq]; exact htrue
    · have heq : (fun x : Fin N → Bool => st0 x k) = (fun _ => false) := by
        funext _; simp [st0, hk]
      rw [heq]; exact hfalse
  have hloop : ∀ r, Build Base (Sigs (fun x =>
      (List.range r).foldl
        (fun p i => if hi : i < m then (if u x ⟨i, hi⟩ then shiftOneHot p else p) else p)
        (st0 x))) (r * ((m + 1) * 4)) := by
    intro r
    induction r with
    | zero => simpa using idleB (A := Base) (B := Sigs st0) hst0
    | succ r ih =>
      let pr : (Fin N → Bool) → (Fin (m + 1) → Bool) := fun x =>
        (List.range r).foldl
          (fun p i => if hi : i < m then (if u x ⟨i, hi⟩ then shiftOneHot p else p) else p)
          (st0 x)
      have hstep : Build (Base ∪ Sigs pr)
          (Sigs (fun x => if hr : r < m then (if u x ⟨r, hr⟩ then shiftOneHot (pr x) else pr x) else pr x))
          ((m + 1) * 4) := by
        by_cases hr : r < m
        · refine finSigB _ 4 (fun k => ?_)
          have hsh : (fun x => shiftOneHot (pr x) k) ∈ Base ∪ Sigs pr := by
            unfold shiftOneHot
            by_cases h0 : k.val = 0
            · simp only [h0, ↓reduceDIte]; exact Or.inl hfalse
            · simp only [h0, ↓reduceDIte]; exact Or.inr ⟨⟨k.val - 1, by omega⟩, rfl⟩
          have heq : (fun x => (if hr' : r < m then (if u x ⟨r, hr'⟩ then shiftOneHot (pr x) else pr x) else pr x) k) =
              fun x => if u x ⟨r, hr⟩ then shiftOneHot (pr x) k else pr x k := by
            funext x; simp only [hr, ↓reduceDIte]; cases u x ⟨r, hr⟩ <;> rfl
          rw [heq]
          exact iteB (Or.inl (hu ⟨r, hr⟩)) hsh (Or.inr ⟨k, rfl⟩)
        · have heq : (fun x => if hr' : r < m then (if u x ⟨r, hr'⟩ then shiftOneHot (pr x) else pr x) else pr x) = pr := by
            funext x; simp [hr]
          rw [heq]
          exact relaxB (idleB (A := Base ∪ Sigs pr) (B := Sigs pr) Set.subset_union_right)
            le_rfl Set.subset_union_right (Nat.zero_le _)
      have heq : (fun x => (List.range (r + 1)).foldl
          (fun p i => if hi : i < m then (if u x ⟨i, hi⟩ then shiftOneHot p else p) else p) (st0 x)) =
          fun x => if hr : r < m then (if u x ⟨r, hr⟩ then shiftOneHot (pr x) else pr x) else pr x := by
        funext x; simp [List.range_succ, List.foldl_append, pr]
      rw [heq]
      exact relaxB (seq2B ih hstep) le_rfl Set.subset_union_right (by simp [Nat.succ_mul])
  exact hloop m

theorem card_subspace_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (S : Submodule (ZMod 2) V) [Fintype S] :
    Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
  let b := Module.finBasis (ZMod 2) S
  have heqv : S ≃ (Fin (Module.finrank (ZMod 2) S) → ZMod 2) := b.equivFun.toEquiv
  rw [Fintype.card_congr heqv]
  simp [Fintype.card_pi, ZMod.card]

theorem matrix_rank_eq_rowSpan_finrank {R C : ℕ} (M : Matrix (Fin R) (Fin C) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun r : Fin R => M r))) := by
  rw [← Matrix.rank_transpose]
  change Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) = _
  have hsubEq : LinearMap.range M.transpose.mulVecLin =
      Submodule.span (ZMod 2) (Set.range (fun r : Fin R => M r)) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hv : M.transpose.mulVecLin v = ∑ r : Fin R, v r • M r := by
        funext c
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
      rw [hv]
      exact Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      refine ⟨Pi.single r 1, ?_⟩
      funext c
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_eq_single r]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsubEq]
end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux.P25940Affine

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F

def lin {m} (v x : V m) : F := ∑ i, v i * x i
def unit {m} (i : Fin m) : V m := fun j => if j = i then 1 else 0

theorem lin_unit {m} (v : V m) (i : Fin m) : lin v (unit i) = v i := by
  simp [lin, unit, mul_ite]

theorem lin_add {m} (v x y : V m) : lin v (x+y) = lin v x + lin v y := by
  simp [lin, mul_add, Finset.sum_add_distrib]

theorem lin_coeff_add {m} (v w x : V m) : lin (v+w) x = lin v x + lin w x := by
  simp [lin, add_mul, Finset.sum_add_distrib]

def Aff {m} (f : V m → F) := ∃ (a : F) (v : V m), ∀ x, f x = a + lin v x

theorem Aff.const {m} (c : F) : Aff (fun _ : V m => c) := by
  exact ⟨c, 0, by simp [lin]⟩

theorem Aff.add {m} {f g : V m → F} (hf : Aff f) (hg : Aff g) : Aff (fun x => f x + g x) := by
  obtain ⟨a,v,hv⟩ := hf
  obtain ⟨b,w,hw⟩ := hg
  exact ⟨a+b,v+w, fun x => by simp only [hv, hw, lin_coeff_add]; ring⟩

theorem Aff.scale {m} {f : V m → F} (b : F) (hf : Aff f) : Aff (fun x => b * f x) := by
  obtain ⟨a,v,hv⟩ := hf
  refine ⟨b*a, fun i => b*v i, fun x => ?_⟩
  simp only [hv, mul_add]; simp [lin, Finset.mul_sum, mul_assoc]

def diff {m} (f : V m → F) (x y : V m) := f 0 - f x - f y + f (x+y)

theorem diff_eq {m} (f : V m → F) (x y : V m) :
    diff f x y = f 0 + f x + f y + f (x+y) := by
  simp [diff, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem Aff.diff_zero {m} {f : V m → F} (hf : Aff f) (x y : V m) : diff f x y = 0 := by
  obtain ⟨a,v,h⟩ := hf
  have h0 : lin v 0 = 0 := by simp [lin]
  simp only [diff,h,lin_add,h0]; ring

theorem two_values (x : F) : x = 0 ∨ x = 1 := by decide +revert

theorem sq_id (x : F) : x*x = x := by rcases two_values x with rfl | rfl <;> decide

theorem degenerate {m} (v w : V m)
    (h : ∀ i j, i < j → v i*w j + v j*w i = 0) : v = 0 ∨ w = 0 ∨ v = w := by
  by_cases hv : v = 0
  · exact Or.inl hv
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hn
    exact hv (funext hn)
  have hi' := (two_values (v i)).resolve_left hi
  have row (j : Fin m) : w j = v j * w i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hh := h i j hij
      rw [hi', one_mul] at hh
      simpa [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_left hh)
    · simp [hi']
    · have hh := h j i hji
      rw [add_comm, hi', one_mul] at hh
      simpa [ZMod.neg_eq_self_mod_two] using (eq_neg_of_add_eq_zero_left hh)
  rcases two_values (w i) with h0 | h1
  · exact Or.inr (Or.inl (funext (fun j => by simpa [h0] using row j)))
  · exact Or.inr (Or.inr (funext (fun j => by simpa [h1] using (row j).symm)))

theorem step_aff {m} {f g q : V m → F} (hf : Aff f) (hg : Aff g) (hq : Aff q)
    (h : ∀ i j : Fin m, i < j → diff (fun x => f x + g x*q x) (unit i) (unit j) = 0) :
    Aff (fun x => f x + g x*q x) := by
  obtain ⟨a,v,hv⟩ := hg
  obtain ⟨b,w,hw⟩ := hq
  have hh (i j : Fin m) (hij : i < j) : v i*w j + v j*w i = 0 := by
    obtain ⟨c,u,hu⟩ := hf
    have e := h i j hij
    have lin0 (l : V m) : lin l 0 = 0 := by simp [lin]
    simp only [diff, hu, hv, hw, lin0, lin_add, lin_unit] at e
    linear_combination e
  apply hf.add
  rcases degenerate v w hh with h0 | h0 | hsame
  · subst v
    simpa only [hv, lin, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using
      (Aff.scale a ⟨b,w,hw⟩ : Aff (fun x => a * q x))
  · subst w
    have ht : ∀ x, q x = b := fun x => by simp [hw,lin]
    simpa only [ht, mul_comm] using (Aff.scale b ⟨a,v,hv⟩ : Aff (fun x => b * g x))
  · subst w
    have he (x : V m) : g x*q x = a*b + (a+b+1)*lin v x := by
      rw [hv,hw]; linear_combination sq_id (lin v x)
    have hl : Aff (lin v) := ⟨0,v,by simp⟩
    simpa only [he] using (Aff.const (a*b)).add (Aff.scale (a+b+1) hl)

def shift {m k} (gen : Fin m → V k) (x : V m) : V k := ∑ i, x i • gen i

theorem shift_apply {m k} (gen : Fin m → V k) (j : Fin k) (x : V m) :
    shift gen x j = lin (fun i => gen i j) x := by
  simp [shift, lin, Finset.sum_apply, smul_eq_mul, mul_comm]

theorem shift_add {m k} (gen : Fin m → V k) (x y : V m) :
    shift gen (x+y) = shift gen x + shift gen y := by
  funext j; simp [shift_apply, lin_add]

theorem shift_unit {m k} (gen : Fin m → V k) (i : Fin m) : shift gen (unit i) = gen i := by
  funext j; rw [shift_apply, lin_unit]

theorem aff_key {m k} (gen : Fin m → V k) (a : V k) (j : Fin k) :
    Aff (fun x => (a + shift gen x) j) := ⟨a j, fun i => gen i j, fun x => by simp [shift_apply]⟩

section Recurrence
variable {m k : ℕ} (hk : 0 < k)
def ix (u : ℕ) : Fin k := ⟨u % k, Nat.mod_lt _ hk⟩
def gap (b : Bool) := if b then 2 else 1
def start (b : Bool) := if b then 3 else 1
def feed (b : Bool) (t : Nat) := if b then 3*(t+1)+1 else 2*t
def rot (s : ℕ) (x : V k) (j : Fin k) := x (ix hk (j.val+k-s % k))
def mix (b : Bool) (z : V k) (i : Fin k) :=
  z i + z (ix hk (i.val+gap b)) + z (ix hk (i.val+k-gap b % k))
def update (b : Bool) (key : V k) (t : ℕ) (C z : V k) (j : Fin k) :=
  mix hk b z j + (1+mix hk b z (ix hk (j.val+1)))*mix hk b z (ix hk (j.val+2)) +
    rot hk (feed b t) key j + C j

def state {r : ℕ} (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (b : Bool) (key : V k) (n : ℕ) : V k :=
  ((List.finRange (r+1)).take n).foldl (fun z tick => update hk b key tick.val (c b tick) z)
    (rot hk (start b) key + name b)

theorem state_step {r : ℕ} (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (b : Bool) (key : V k) (n : ℕ) (hn : n < r+1) :
    state hk name c b key (n+1) = update hk b key n (c b ⟨n,hn⟩) (state hk name c b key n) := by
  unfold state
  rw [List.take_succ_eq_append_getElem (by simpa using hn : n < (List.finRange (r+1)).length)]
  simp

def closed (watch : Bool → ℕ → Fin k → Bool) (N : ℕ) :=
  ∀ b n, n < N → ∀ j : Fin k, watch b (n+1) j = true → ∀ e : Fin 3,
    let i := ix hk (j.val+e.val)
    watch b n i = true ∧ watch b n (ix hk (i.val+gap b)) = true ∧
      watch b n (ix hk (i.val+k-gap b % k)) = true

theorem aff_prefix {r : ℕ} (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (a : V k) (b : Bool) (watch : Bool → ℕ → Fin k → Bool)
    (hc : closed hk watch (r+1))
    (checks : ∀ n, 0 < n → n ≤ r → ∀ j, watch b n j = true → ∀ i l : Fin m, i < l →
      diff (fun x => state hk name c b (a + shift gen x) n j) (unit i) (unit l) = 0) :
    ∀ n, n ≤ r → ∀ j, watch b n j = true → Aff (fun x => state hk name c b (a + shift gen x) n j) := by
  intro n
  induction n with
  | zero =>
    intro _ j _
    exact (aff_key gen a (ix hk (j.val+k-start b % k))).add (Aff.const (name b j))
  | succ n ih =>
    intro hn j hj
    let key (x : V m) := a + shift gen x
    let Y (i : Fin k) (x : V m) := mix hk b (state hk name c b (key x) n) i
    have hY (e : Fin 3) : Aff (Y (ix hk (j.val+e.val))) := by
      obtain ⟨h₁,h₂,h₃⟩ := hc b n (by omega) j hj e
      exact ((ih (by omega) _ h₁).add (ih (by omega) _ h₂)).add (ih (by omega) _ h₃)
    have heq : ix hk (j.val + (0 : Fin 3).val) = j := by apply Fin.ext; simp [ix, Nat.mod_eq_of_lt j.isLt]
    have h₀ : Aff (Y j) := heq ▸ hY 0
    let A := fun x => Y j x + rot hk (feed b n) (key x) j + c b ⟨n,by omega⟩ j
    let G := fun x => 1 + Y (ix hk (j.val+1)) x
    let Q := Y (ix hk (j.val+2))
    have hA : Aff A := (h₀.add (aff_key gen a _)).add (Aff.const _)
    have hG : Aff G := (Aff.const 1).add (hY 1)
    have hQ : Aff Q := hY 2
    have evalStep (x : V m) : state hk name c b (a + shift gen x) (n+1) j = A x + G x*Q x := by
      rw [state_step hk name c b _ n (by omega)]; unfold update A G Q Y key; ring
    have hs := step_aff hA hG hQ (fun i l hil => by
      simpa only [diff,evalStep] using checks (n+1) (by omega) hn j hj i l hil)
    simpa only [evalStep] using hs
end Recurrence

theorem aff_coset {m k} (gen : Fin m → V k) (a : V k) (f : V k → F)
    (hf : Aff (fun x => f (a+shift gen x))) (u x y : V m) :
    let b := a + shift gen u
    f b + f (b+shift gen x) + f (b+shift gen y) + f (b+shift gen x+shift gen y) = 0 := by
  obtain ⟨c,v,h⟩ := hf
  change f (a+shift gen u) + f (a+shift gen u+shift gen x) +
    f (a+shift gen u+shift gen y) + f (a+shift gen u+shift gen x+shift gen y) = 0
  simp only [add_assoc, ←shift_add, h, lin_add]
  generalize lin v u = U; generalize lin v x = X; generalize lin v y = Y
  clear * - c U X Y
  decide +revert

theorem shift_zero {m k} (gen : Fin m → V k) : shift gen 0 = 0 := by simp [shift]

theorem prefix_pair_iff {m d k r : ℕ} (hk : 0 < k)
    (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (dir : Fin d → V k)
    (same : Set.range (shift dir) = Set.range (shift gen))
    {R : Type*} (rep : R → V k) (cover : ∀ a, ∃ s u, a = rep s + shift dir u)
    (watch : Bool → ℕ → Fin k → Bool) (hc : closed hk watch (r+1)) :
    (∀ a b n, n ≤ r → ∀ j, watch b n j = true → ∀ x y,
      state hk name c b a n j + state hk name c b (a+shift gen x) n j +
        state hk name c b (a+shift gen y) n j + state hk name c b (a+shift gen x+shift gen y) n j = 0)
    ↔ (∀ s b n, 0 < n → n ≤ r → ∀ j, watch b n j = true → ∀ i l : Fin d, i < l →
      state hk name c b (rep s) n j + state hk name c b (rep s+dir i) n j +
        state hk name c b (rep s+dir l) n j + state hk name c b (rep s+dir i+dir l) n j = 0) := by
  constructor
  · intro good s b n _ hn j hj i l _
    have memDir (u : Fin d) : dir u ∈ Set.range (shift gen) := by
      rw [← same]; exact ⟨unit u, shift_unit dir u⟩
    obtain ⟨x,hx⟩ := memDir i
    obtain ⟨y,hy⟩ := memDir l
    simpa only [hx,hy] using good (rep s) b n hn j hj x y
  · intro checks a b n hn j hj x y
    obtain ⟨s,u,rfl⟩ := cover a
    have hf := aff_prefix hk name c dir (rep s) b watch hc (by
      intro n hn' hn j hj i l hil
      rw [diff_eq]
      simpa only [shift_add,shift_unit,shift_zero,add_zero,add_assoc] using
        checks s b n hn' hn j hj i l hil) n hn j hj
    have memGen (z : V m) : shift gen z ∈ Set.range (shift dir) := by
      rw [same]; exact ⟨z,rfl⟩
    obtain ⟨x',hx⟩ := memGen x
    obtain ⟨y',hy⟩ := memGen y
    simpa only [hx,hy] using
      aff_coset dir (rep s) (fun key => state hk name c b key n j) hf u x' y'

end PEqualNP.Outside.L_meta_25940_aux.P25940Affine

namespace PEqualNP.Outside.L_meta_25940_aux.P25940Sample
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine PEqualNP.Outside.L_meta_25940_aux

def sample {m k : ℕ} (gen : Fin m → V k) (rep : V k) (f : V k → F) (target : F) : Quad m :=
  ⟨fun i j => f rep + f (rep+gen i) + f (rep+gen j) + f (rep+gen i+gen j),
   fun i => f rep + f (rep+gen i), f rep + target⟩

theorem sample_valid {m k} (gen : Fin m → V k) (rep : V k) (f : V k → F) (target : F) :
    (sample gen rep f target).Valid := by
  constructor
  · intro i
    have hd : rep+gen i+gen i = rep := by funext j; simp [add_assoc,z2_add_self]
    simp only [sample,hd]; linear_combination z2_add_self (f rep) + z2_add_self (f (rep+gen i))
  · intro i j
    have hs : rep+gen i+gen j = rep+gen j+gen i := add_right_comm ..
    simp only [sample,hs]; ring

def OneProduct {m} (q : V m → F) := ∃ (A G H : V m → F), Aff A ∧ Aff G ∧ Aff H ∧
  ∀ x, q x = A x + G x * H x

def Checks {k m r} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (rep : V k) (watch : Bool → ℕ → Fin k → Bool) :=
  ∀ b n, 0 < n → n ≤ r → ∀ j, watch b n j = true → ∀ i l : Fin m, i < l →
    (sample gen rep (fun key => state hk name c b key n j) 0).B i l = 0

theorem terminal_oneProduct {k m r} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (rep : V k) (watch : Bool → ℕ → Fin k → Bool) (hc : closed hk watch (r+1))
    (hs : Checks hk name c gen rep watch) (b : Bool) (j : Fin k) (hj : watch b (r+1) j = true) :
    OneProduct (fun x => state hk name c b (rep+shift gen x) (r+1) j) := by
  have hh := aff_prefix hk name c gen rep b watch hc (by
    intro n hn' hn j hj i l hil; rw [diff_eq]
    simpa only [sample,shift_add,shift_unit,shift_zero,add_zero,add_assoc] using hs b n hn' hn j hj i l hil) r le_rfl
  let key (x : V m) := rep + shift gen x
  let Y (s : Fin k) (x : V m) := mix hk b (state hk name c b (key x) r) s
  have hY (e : Fin 3) : Aff (Y (ix hk (j.val+e.val))) := by
    obtain ⟨h₁,h₂,h₃⟩ := hc b r (by omega) j hj e
    exact ((hh _ h₁).add (hh _ h₂)).add (hh _ h₃)
  have heq : ix hk (j.val + (0 : Fin 3).val) = j := by apply Fin.ext; simp [ix, Nat.mod_eq_of_lt j.isLt]
  have h₀ : Aff (Y j) := heq ▸ hY 0
  let A := fun x => Y j x + rot hk (feed b r) (key x) j + c b ⟨r,by omega⟩ j
  let G := fun x => 1 + Y (ix hk (j.val+1)) x
  let Q := Y (ix hk (j.val+2))
  refine ⟨A,G,Q,(h₀.add (aff_key gen rep _)).add (Aff.const _),(Aff.const 1).add (hY 1),hY 2,fun x => ?_⟩
  change state hk name c b (key x) (r+1) j = A x + G x * Q x
  rw [state_step hk name c b _ r (by omega)]; unfold update A G Q Y key; ring

private theorem four {m} (f : V m → F) (x i j : V m) :
    f x + f (x+i) + f (x+j) + f (x+i+j) = f x - f (x+i) - f (x+j) + f (x+i+j) := by
  simp [sub_eq_add_neg,ZMod.neg_eq_self_mod_two]

private theorem cross {m} {f : V m → F} {a b c : F} {v w z : V m}
    (h : ∀ x, f x = a+lin v x + (b+lin w x)*(c+lin z x)) (x i j : V m) :
    f x + f (x+i) + f (x+j) + f (x+i+j) = lin w i*lin z j + lin w j*lin z i := by
  rw [four]; simp only [h,lin_add]; ring

private theorem sampled_B {m k} (gen : Fin m → V k) (rep : V k) (f : V k → F) (t : F)
    {a b c : F} {v w z : V m} (h : ∀ x, f (rep+shift gen x) = a+lin v x + (b+lin w x)*(c+lin z x))
    (x : V m) (i j : Fin m) :
    (sample gen (rep+shift gen x) f t).B i j = w i*z j + w j*z i := by
  have h' := cross (f := fun x => f (rep+shift gen x)) h x (unit i) (unit j)
  simpa only [sample,shift_add,shift_unit,lin_unit,add_assoc] using h'

private theorem OneProduct.coeffs {m} {q : V m → F} (hf : OneProduct q) :
    ∃ (a b c : F) (v w z : V m), ∀ x, q x = a+lin v x + (b+lin w x)*(c+lin z x) := by
  obtain ⟨A,G,H,⟨a,v,ha⟩,⟨b,w,hb⟩,⟨c,z,hc⟩,h⟩ := hf
  exact ⟨a,b,c,v,w,z,fun x => by rw [h,ha,hb,hc]⟩

theorem sample_eval {m k} (gen : Fin m → V k) (rep : V k) (f : V k → F) (t : F)
    (hp : OneProduct (fun x => f (rep+shift gen x))) (x : V m) :
    (sample gen rep f t).eval x = f (rep+shift gen x) + t := by
  obtain ⟨a,b,c,v,w,z,h⟩ := hp.coeffs
  let P : Quad m := ⟨fun _ _ => 0,v,a+t⟩
  have h0 (v : V m) : lin v 0 = 0 := by simp [lin]
  have hrep : f rep = a+b*c := by simpa only [shift_zero,add_zero,h0] using h 0
  have he (i : Fin m) : f (rep+gen i) = a+v i+(b+w i)*(c+z i) := by
    simpa only [shift_unit,lin_unit] using h (unit i)
  have heq : sample gen rep f t = P.addAffineProd b w c z := by
    have extQ (M N : Quad m) (e : M.B = N.B ∧ M.l = N.l ∧ M.c = N.c) : M = N := by
      cases M; cases N; obtain ⟨rfl,rfl,rfl⟩ := e; rfl
    apply extQ
    refine ⟨funext fun i => funext fun j => ?_,funext fun i => ?_,?_⟩
    · have hb := sampled_B gen rep f t h 0 i j
      simp only [shift_zero,add_zero] at hb
      rw [hb]; change _ = if i=j then 0 else 0 + w i*z j + w j*z i
      split_ifs with heq
      · subst j; exact z2_add_self _
      · simp
    · change f rep + f (rep+gen i) = v i + b*z i + c*w i + w i*z i
      rw [← ZMod.neg_eq_self_mod_two (f rep), hrep, he]; ring
    · change f rep + t = (a+t) + b*c; rw [hrep]; ring
  have hP : P.eval x = a+t+lin v x := by simp [P,Quad.eval,lin]
  rw [heq, Quad.eval_addAffineProd, hP, h]; unfold lin; ring

theorem sample_B_invariant {m k} (gen : Fin m → V k) (rep : V k) (f : V k → F) (t : F)
    (hp : OneProduct (fun x => f (rep+shift gen x))) (x : V m) :
    (sample gen (rep+shift gen x) f t).B = (sample gen rep f t).B := by
  obtain ⟨a,b,c,v,w,z,h⟩ := hp.coeffs
  funext i j; have h0 := sampled_B gen rep f t h 0 i j
  simp only [shift_zero,add_zero] at h0
  exact (sampled_B gen rep f t h x i j).trans h0.symm

def matrix {m k t} (gen : Fin m → V k) (rep : V k) (f : Fin t → V k → F) (target : Fin t → F) :
    Matrix (Fin t) (Fin m × Fin m) F := Matrix.of fun i jl => (sample gen rep (f i) (target i)).B jl.1 jl.2

theorem terminal_sample {m k r t} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (rep : V k) (watch : Bool → ℕ → Fin k → Bool) (hc : closed hk watch (r+1))
    (side : Fin t → Bool) (site : Fin t → Fin k) (hw : ∀ i, watch (side i) (r+1) (site i) = true)
    (target : Fin t → F) (hs : Checks hk name c gen rep watch) :
    let f := fun (i : Fin t) (key : V k) => state hk name c (side i) key (r+1) (site i)
    (∀ i x, (sample gen rep (f i) (target i)).eval x = f i (rep+shift gen x) + target i) ∧
    (∀ x, matrix gen (rep+shift gen x) f target = matrix gen rep f target) ∧
    (∀ x, (matrix gen (rep+shift gen x) f target).rank = (matrix gen rep f target).rank) := by
  let f := fun (i : Fin t) (key : V k) => state hk name c (side i) key (r+1) (site i)
  have hp (i : Fin t) : OneProduct (fun x => f i (rep+shift gen x)) :=
    terminal_oneProduct hk name c gen rep watch hc hs (side i) (site i) (hw i)
  have hm (x : V m) : matrix gen (rep+shift gen x) f target = matrix gen rep f target := by
    ext i jl; exact congrFun (congrFun (sample_B_invariant gen rep (f i) (target i) (hp i) x) jl.1) jl.2
  exact ⟨fun i => sample_eval gen rep (f i) (target i) (hp i),hm,fun x => congrArg Matrix.rank (hm x)⟩

end PEqualNP.Outside.L_meta_25940_aux.P25940Sample

namespace PEqualNP.Outside.L_meta_25940_aux
noncomputable section
abbrev BankGen (m k : ℕ) := Fin m → Fin k → ZMod 2
abbrev bankSt {m k} (g : BankGen m k) := gaussElim g (fun _ => Fin.elim0)
def bankPrivate {m k} (g : BankGen m k) (r : Fin m) (j : Fin k) :=
  (List.finRange m).all (fun s => if s = r then z2b ((bankSt g).M s j) else !(z2b ((bankSt g).M s j)))
def bankPick {m k} (g : BankGen m k) (r : Fin m) := firstTrue (bankPrivate g r)
def bankFree {m k} (g : BankGen m k) (j : Fin k) := !((List.finRange m).any (fun r => bankPick g r j))
def bankF {m k} (g : BankGen m k) := Finset.univ.filter (fun j => bankFree g j = true)
def bankBefore {m k} (g : BankGen m k) (j : Fin k) := ((bankF g).filter (· < j)).card
noncomputable def bankCode (n : ℕ) : Fin (2^n) ≃ (Fin n → ZMod 2) :=
  Fintype.equivOfCardEq (by simp [ZMod.card])
def bankCell (n a b : ℕ) : ZMod 2 :=
  if ha : a < 2^n then if hb : b < n then bankCode n ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0
def bankRep {k m} (p : ℕ) (g : BankGen m k) (i : Fin (2^min k p)) (j : Fin k) : ZMod 2 :=
  if bankFree g j then bankCell (bankF g).card i.val (bankBefore g j) else 0
def bankLive {k m} (p : ℕ) (g : BankGen m k) (i : Fin (2^min k p)) := decide (i.val < 2^(bankF g).card)
def bankGood {k m} (p : ℕ) (g : BankGen m k) := decide ((bankF g).card ≤ p)
theorem bankPrivate_spec {m k} (g : BankGen m k) (r j) : bankPrivate g r j = true ↔
    (bankSt g).M r j = 1 ∧ ∀ s, s ≠ r → (bankSt g).M s j = 0 := by
  simp only [bankPrivate, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · intro h
    refine ⟨(z2_cases _).resolve_left ?_, fun s hs => ?_⟩
    · simpa [z2b] using h r
    · simpa [hs,z2b] using h s
  · rintro ⟨h1,h0⟩ s
    by_cases hs : s = r
    · simpa [hs,h1] using z2b_one
    · simp [hs,h0 s hs,z2b_zero]
theorem bankPick_used {m k} (g : BankGen m k) (r : Fin m) :
    (∃ j, bankPick g r j = true) ↔ (bankSt g).used r = true := by
  change (∃ j, firstTrue _ j = true) ↔ _
  rw [← show (∃ j, bankPrivate g r j = true) ↔ (bankSt g).used r = true from by
    rcases gaussElim_invariants g (fun _ => Fin.elim0) with ⟨_, hp, hz, _, _⟩
    simp_rw [bankPrivate_spec]
    constructor
    · rintro ⟨j,h1,_⟩
      cases h : (bankSt g).used r
      · exact False.elim (zero_ne_one ((hz r h j).symm.trans h1))
      · rfl
    · exact hp r]
  exact exists_firstTrue_iff _
abbrev bankU {m k} (g : BankGen m k) := Finset.univ.filter (fun r => (bankSt g).used r = true)
noncomputable def bankCol {m k} (g : BankGen m k) (r : bankU g) : Fin k :=
  ((bankPick_used g r).2 (Finset.mem_filter.mp r.2).2).choose
theorem bankCol_spec {m k} (g : BankGen m k) (r : bankU g) :
    bankPick g r (bankCol g r) = true := ((bankPick_used g r).2 (Finset.mem_filter.mp r.2).2).choose_spec
theorem bankCol_unique {m k} (g : BankGen m k) (r : bankU g) {j : Fin k} (h : bankPick g r j = true) :
    bankCol g r = j := by
  exact firstTrue_unique _ (bankCol_spec g r) h
theorem bankCol_unit {m k} (g : BankGen m k) (r : bankU g) :
    (bankSt g).M r (bankCol g r) = 1 ∧ ∀ s, s ≠ r.val → (bankSt g).M s (bankCol g r) = 0 :=
  (bankPrivate_spec _ _ _).1 ((firstTrue_spec _ _).1 (bankCol_spec g r)).1
theorem bankCol_inj {m k} (g : BankGen m k) : Function.Injective (bankCol g) := by
  intro r s h
  by_contra hn
  have h0 := (bankCol_unit g s).2 r (fun e => hn (Subtype.ext e))
  rw [← h, (bankCol_unit g r).1] at h0
  exact one_ne_zero h0
theorem bankFree_spec {m k} (g : BankGen m k) (j : Fin k) :
    bankFree g j = true ↔ ¬ ∃ r : bankU g, bankCol g r = j := by
  have h : (∃ r, bankPick g r j = true) ↔ ∃ r : bankU g, bankCol g r = j := by
    constructor
    · rintro ⟨r,hr⟩
      let u : bankU g := ⟨r, by simp [(bankPick_used g r).1 ⟨j, hr⟩]⟩
      exact ⟨u,bankCol_unique g u hr⟩
    · rintro ⟨r,rfl⟩
      exact ⟨r, bankCol_spec g r⟩
  rw [← h]
  change (!(List.finRange m).any _) = true ↔ _
  rw [Bool.not_eq_true', ← Bool.not_eq_true]
  simp
theorem bankF_card {m k} (g : BankGen m k) : (bankF g).card =
    k - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) := by
  classical
  have h : bankF g = (Finset.univ.image (bankCol g))ᶜ := by
    ext j; simp [bankF,bankFree_spec]
  rw [h,Finset.card_compl,Finset.card_image_of_injective _ (bankCol_inj g)]
  simp [gaussElim_rank_eq]
theorem bankGood_iff {m k} (p) (g : BankGen m k) : bankGood p g = true ↔
    k - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ p := by
  simp [bankGood,bankF_card]
def bankSlot {m k} (g : BankGen m k) (j : bankF g) : Fin (bankF g).card :=
  ⟨bankBefore g j, by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have hj : j.val ∈ (bankF g).filter (· < j.val) := by rw [h]; exact j.property
    simp at hj⟩
theorem bankSlot_bij {m k} (g : BankGen m k) : Function.Bijective (bankSlot g) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨StrictMono.injective ?_, by simp⟩
  intro i j hij
  change ((bankF g).filter (· < i.val)).card < ((bankF g).filter (· < j.val)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fun x hx => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, lt_trans (Finset.mem_filter.mp hx).2 hij⟩, fun h => ?_⟩
  have hi : i.val ∈ (bankF g).filter (· < j.val) := Finset.mem_filter.mpr ⟨i.property,hij⟩
  rw [← h] at hi
  exact lt_irrefl _ (Finset.mem_filter.mp hi).2

theorem bank_partition {m k} (p) (g : BankGen m k) (hg : bankGood p g = true) (w : Fin k → ZMod 2) :
    ∃! i : Fin (2^min k p), bankLive p g i = true ∧
        w - bankRep p g i ∈ Submodule.span (ZMod 2) (Set.range g) := by
  classical
  let S := Submodule.span (ZMod 2) (Set.range g)
  let n := (bankF g).card
  have hnk : n ≤ k := by simpa [n] using (bankF g).card_le_univ
  have hnp : n ≤ min k p := le_min hnk (of_decide_eq_true hg)
  let idx : Fin (2^n) → Fin (2^min k p) := Fin.castLE (Nat.pow_le_pow_right (by decide) hnp)
  let f : Fin (2^n) × S → (Fin k → ZMod 2) := fun z => bankRep p g (idx z.1) + z.2.val
  have surj : Function.Surjective f := by
    intro v
    let z : Fin k → ZMod 2 := ∑ r : bankU g, (v (bankCol g r)) • (bankSt g).M r
    have hz : z ∈ S := by
      apply Submodule.sum_mem
      intro r _
      apply Submodule.smul_mem
      change _ ∈ Submodule.span _ (Set.range g)
      rw [← (gaussElim_invariants g (fun _ => Fin.elim0)).1]
      exact Submodule.subset_span ⟨r.val,rfl⟩
    have hp (r : bankU g) : z (bankCol g r) = v (bankCol g r) := by
      simp only [z,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      rw [Fintype.sum_eq_single r]
      · rw [(bankCol_unit g r).1,mul_one]
      · intro s hs
        rw [(bankCol_unit g r).2 s (fun e => hs (Subtype.ext e)),mul_zero]
    let e := Equiv.ofBijective (bankSlot g) (bankSlot_bij g)
    let word : Fin n → ZMod 2 := fun b => (v-z) (e.symm b).val
    let a := (bankCode n).symm word
    refine ⟨⟨a,⟨z,hz⟩⟩,?_⟩
    funext j
    change bankRep p g (idx a) j + z j = v j
    by_cases hj : bankFree g j = true
    · let u : bankF g := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
      have huv : bankCell n a.val (bankBefore g j) = word (e u) := by
        have hb : bankBefore g j < n := (bankSlot g u).isLt
        simp only [bankCell,dite_eq_left a.isLt,dite_eq_left hb]
        exact congrFun ((bankCode n).apply_symm_apply word) (e u)
      change (if bankFree g j then bankCell n a.val (bankBefore g j) else 0) + z j = v j
      rw [ite_eq_left hj,huv]
      simp [word,u]
    · obtain ⟨r, rfl⟩ := Classical.not_not.mp (fun h => hj ((bankFree_spec g j).2 h))
      simp [bankRep,hj,hp]
  have bij : Function.Bijective f := by
    apply (Fintype.bijective_iff_surjective_and_card _).2
    refine ⟨surj,?_⟩
    have hr' : Module.finrank (ZMod 2) S ≤ k := by
      simpa only [Module.finrank_fin_fun] using S.finrank_le
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,ZMod.card,card_subspace_zmod2,← pow_add]
    congr 1
    change (bankF g).card + Module.finrank (ZMod 2) S = k
    rw [bankF_card]
    exact Nat.sub_add_cancel hr'
  obtain ⟨⟨a,s⟩,ha⟩ := surj w
  change bankRep p g (idx a) + s.val = w at ha
  refine ⟨idx a, ⟨decide_eq_true a.isLt,?_⟩,?_⟩
  · rw [← ha,add_sub_cancel_left]; exact s.property
  · rintro i ⟨hi,hs⟩
    let b : Fin (2^n) := ⟨i.val,of_decide_eq_true hi⟩
    have h : f (b,⟨w - bankRep p g i,hs⟩) = f (a,s) := by
      change bankRep p g i + (w - bankRep p g i) = bankRep p g (idx a) + s.val
      rw [ha]; abel
    exact congrArg idx (congrArg Prod.fst (bij.1 h))

def bankSigs {N k m} (p : ℕ) (g : (Fin N → Bool) → BankGen m k) : Set (Sig N) :=
  ({fun x => bankGood p (g x)} ∪ Set.range (fun i => fun x => bankLive p (g x) i)) ∪
    {f | ∃ i j, (fun x => z2b (bankRep p (g x) i j)) = f}

theorem bankAnyB {N n} {A : Set (Sig N)} (f : Fin n → Sig N)
    (hf : ∀ i, f i ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {fun x => (List.finRange n).any (fun i => f i x)} n := by
  simpa [List.any_map,Function.comp_def] using orListB ((List.finRange n).map f) (by simpa using hf) hz
theorem bankAllB {N n} {A : Set (Sig N)} (f : Fin n → Sig N)
    (hf : ∀ i, f i ∈ A) (hz : (fun _ => true) ∈ A) :
    Build A {fun x => (List.finRange n).all (fun i => f i x)} n := by
  simpa [List.all_map,Function.comp_def] using andListB ((List.finRange n).map f) (by simpa using hf) hz

theorem bankMuxB {N n} {A : Set (Sig N)} (hz : (fun _ => false) ∈ A)
    (w : (Fin N → Bool) → Fin n) (f : Fin n → Sig N)
    (hw : ∀ i, (fun x => decide (i = w x)) ∈ A) (hf : ∀ i, f i ∈ A) :
    Build A {fun x => f (w x) x} (n*2) := by
  let terms := fun (i : Fin n) (x : Fin N → Bool) => decide (i = w x) && f i x
  have h1 := finSigB terms 1 (fun i => andB (hw i) (hf i))
  have h2 := bankAnyB (A := A ∪ Set.range terms) terms (fun i => Or.inr ⟨i,rfl⟩) (Or.inl hz)
  have heq : (fun x => (List.finRange n).any (fun i => terms i x)) = fun x => f (w x) x := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [terms]
  rw [heq] at h2
  exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by omega)

def bankAmount {k m} (g : BankGen m k) (a : Fin (k+1)) : Fin (k+1) :=
  ⟨((bankF g).filter (fun j => j.val < a.val)).card, by
    have hh := ((bankF g).filter (fun j => j.val < a.val)).card_le_univ
    simp only [Fintype.card_fin] at hh; omega⟩
theorem bankAmount_full {k m} (g : BankGen m k) :
    (bankAmount g (Fin.last k)).val = (bankF g).card := by
  simp [bankAmount]
theorem bankHistB {N k m} (A : Set (Sig N)) (hz : (fun _ => false) ∈ A)
    (ht : (fun _ => true) ∈ A) (g : (Fin N → Bool) → BankGen m k)
    (hf : ∀ j, (fun x => bankFree (g x) j) ∈ A) :
    Build A (⋃ a : Fin (k+1), Set.range (fun i : Fin (k+1) => fun x => decide (i = bankAmount (g x) a)))
      ((k+1)*(k*((k+1)*4))) := by
  apply finB
  intro a
  let u := fun (x : Fin N → Bool) (j : Fin k) => if j.val < a.val then bankFree (g x) j else false
  have hu (j : Fin k) : (fun x => u x j) ∈ A := by
    by_cases h : j.val < a.val <;> simp [u,h] <;> solve_by_elim
  have heq (i : Fin (k+1)) (x : Fin N → Bool) : countOneHot (u x) i = decide (i = bankAmount (g x) a) := by
    rw [countOneHot_spec]
    have hset : Finset.univ.filter (fun j => u x j = true) = (bankF (g x)).filter (fun j => j.val < a.val) := by
      ext j; by_cases h : j.val < a.val <;> simp [u,h,bankF]
    simp [hset,bankAmount,Fin.ext_iff]
  simpa only [heq] using countOneHotB A hz ht u hu

theorem bankFreeB {N m k} (A : Set (Sig N)) (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (g : (Fin N → Bool) → BankGen m k)
    (hM : ∀ r j, (fun x => z2b ((bankSt (g x)).M r j)) ∈ A) :
    Build A (Set.range (fun j => fun x => bankFree (g x) j))
      (m*(k*1) + m*(k*m) + m*(k*(k+2)) + k*(m+1)) := by
  let neg := fun (r : Fin m) (j : Fin k) (x : Fin N → Bool) => !(z2b ((bankSt (g x)).M r j))
  have H1 := fin2SigB neg 1 (fun r j => notB (hM r j))
  let A1 := A ∪ {f | ∃ r j, neg r j = f}
  let priv := fun (r : Fin m) (j : Fin k) x => bankPrivate (g x) r j
  have H2 : Build A1 {f | ∃ r j, priv r j = f} (m*(k*m)) := by
    refine fin2SigB priv m (fun r j => ?_)
    let term := fun (s : Fin m) (x : Fin N → Bool) => if s = r then z2b ((bankSt (g x)).M s j) else neg s j x
    apply bankAllB term _ (Or.inl ht)
    intro s; by_cases hs : s = r
    · simpa only [term,ite_eq_left hs] using (show (fun x => z2b ((bankSt (g x)).M s j)) ∈ A1 from Or.inl (hM s j))
    · simpa only [term,ite_eq_right hs] using (show neg s j ∈ A1 from Or.inr ⟨s,j,rfl⟩)
  let A2 := A1 ∪ {f | ∃ r j, priv r j = f}
  let pick := fun (r : Fin m) (j : Fin k) x => bankPick (g x) r j
  have H3 : Build A2 (⋃ r, Set.range (pick r)) (m*(k*(k+2))) :=
    finB _ _ (fun r => firstTrueB (priv r) (Or.inl (Or.inl hz)) (fun j => Or.inr ⟨r,j,rfl⟩))
  let A3 := A2 ∪ ⋃ r, Set.range (pick r)
  have H4 : Build A3 (Set.range (fun j => fun x => bankFree (g x) j)) (k*(m+1)) := by
    refine finSigB _ _ (fun j => ?_)
    have hh := bankAnyB (A := A3) (fun r => pick r j)
      (fun r => Or.inr (Set.mem_iUnion.mpr ⟨r,⟨j,rfl⟩⟩)) (Or.inl (Or.inl (Or.inl hz)))
    exact seq2B hh (notB (Or.inr rfl))
  exact transB (transB (transB (extB H1) (extB H2)) (extB H3)) H4

theorem bankB {N k m} (A : Set (Sig N)) (hz : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (p : ℕ) (g : (Fin N → Bool) → BankGen m k) (hg : ∀ r j, (fun x => z2b (g x r j)) ∈ A) :
    Build A (bankSigs p g) (128*(k+m+4)^5*2^min k p) := by
  classical
  let U := 2^min k p
  have G := gaussElimB A hz g (fun _ _ => Fin.elim0) hg (fun _ j => Fin.elim0 j)
  have F := bankFreeB (A ∪ gaussSigs (fun x => bankSt (g x))) (Or.inl hz) (Or.inl ht) g
    (fun r j => Or.inr (Or.inl (Or.inr ⟨r,j,rfl⟩)))
  have GF := seq2B G F
  let A1 := A ∪ Set.range (fun j => fun x => bankFree (g x) j)
  have H := bankHistB A1 (Or.inl hz) (Or.inl ht) g (fun j => Or.inr ⟨j,rfl⟩)
  let A2 := A1 ∪ (⋃ a : Fin (k+1), Set.range (fun i : Fin (k+1) => fun x => decide (i = bankAmount (g x) a)))
  have h0 : (fun _ => false) ∈ A2 := Or.inl (Or.inl hz)
  have h1 : (fun _ => true) ∈ A2 := Or.inl (Or.inl ht)
  have hc (b : Bool) : (fun _ => b) ∈ A2 := by cases b <;> assumption
  have ho (a i : Fin (k+1)) : (fun x => decide (i = bankAmount (g x) a)) ∈ A2 :=
    Or.inr (Set.mem_iUnion.mpr ⟨a,⟨i,rfl⟩⟩)
  let total := fun x => bankAmount (g x) (Fin.last k)
  have goodB : Build A2 {fun x => bankGood p (g x)} ((k+1)*2) := by
    simpa only [total,bankAmount_full,bankGood] using
      bankMuxB h0 total (fun a _ => decide (a.val ≤ p)) (ho _) (fun a => hc _)
  have liveB : Build A2 (Set.range (fun i => fun x => bankLive p (g x) i)) (U*((k+1)*2)) := by
    refine finSigB _ _ (fun i => ?_)
    simpa only [total,bankAmount_full,bankLive] using
      bankMuxB h0 total (fun a _ => decide (i.val < 2^a.val)) (ho _) (fun a => hc _)
  have repB : Build A2 {f | ∃ i j, (fun x => z2b (bankRep p (g x) i j)) = f}
      (U*(k*((k+1)*((k+1)*2) + (k+1)*2 + 1))) := by
    refine fin2SigB _ _ (fun i j => ?_)
    let pos := fun x => bankAmount (g x) j.castSucc
    let tab := fun (a : Fin (k+1)) x => z2b (bankCell a.val i.val (pos x).val)
    have hb := finSigB tab ((k+1)*2) (fun a => bankMuxB h0 pos
        (fun b _ => z2b (bankCell a.val i.val b.val)) (ho _) (fun _ => hc _))
    have hb' := bankMuxB (A := A2 ∪ Set.range tab) (Or.inl h0) total tab
      (fun s => Or.inl (ho _ s)) (fun s => Or.inr ⟨s,rfl⟩)
    have hh := seq2B hb hb'
    have hf : (fun x => bankFree (g x) j) ∈ A2 := Or.inl (Or.inr ⟨j,rfl⟩)
    have hf' := seq2B hh (andB (Or.inl hf) (Or.inr rfl))
    have eq : (fun x => bankFree (g x) j && tab (total x) x) = fun x => z2b (bankRep p (g x) i j) := by
      funext x
      cases e : bankFree (g x) j <;> simp [bankRep,tab,total,e,z2b_zero,pos,bankAmount,bankBefore]
    rwa [eq] at hf'
  have Hout := unionB (unionB goodB liveB) repB
  have full := transB (transB (extB GF) (extB H)) Hout
  apply relaxB full le_rfl Set.subset_union_right
  dsimp only [U]
  obtain ⟨v,hv⟩ := Nat.exists_eq_succ_of_ne_zero (show 2^min k p ≠ 0 by positivity)
  rw [hv,Nat.succ_eq_add_one]
  ring_nf
  omega
end
end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux

def quadPolarMatrix {m t : Nat} (Q : Fin t → Quad m) : Matrix (Fin t) (Fin m × Fin m) (ZMod 2) :=
  fun j ab => (Q j).B ab.1 ab.2

theorem quadPolarRankB {N m t : Nat} (Base : Set (Sig N)) (h : Nat)
    (Q0 : (Fin N → Bool) → Fin t → Quad m)
    (hF : (fun _ => false) ∈ Base) (hT : (fun _ => true) ∈ Base)
    (hQ : ∀ j, quadSigs (fun x => Q0 x j) ⊆ Base) :
    Build Base {fun x => decide ((quadPolarMatrix (Q0 x)).rank ≤ h)}
      ((m*m)*(t*(t+4)+(m*m)*(2*t)+t*(1+(m*m)*10)) + t*((t+1)*4) + (t+1)) := by
  classical
  let e : (Fin m × Fin m) ≃ Fin (m*m) := finProdFinEquiv
  let M (x : Fin N→Bool) (j : Fin t) (a : Fin (m*m)) := (Q0 x j).B (e.symm a).1 (e.symm a).2
  let pay (_ : Fin t) := (Fin.elim0 : Fin 0 → ZMod 2)
  let G (x : Fin N→Bool) := gaussElim (M x) pay
  have g := gaussElimB Base hF M (fun _ => pay)
    (fun j a => hQ j (Or.inl (Or.inl ⟨(e.symm a).1,(e.symm a).2,rfl⟩))) (fun _ p => p.elim0)
  let B1 := Base ∪ gaussSigs G
  let cnt (i : Fin (t+1)) : Sig N := fun x => countOneHot (G x).used i
  have c : Build B1 (Set.range cnt) (t*((t+1)*4)) := countOneHotB B1 (Or.inl hF) (Or.inl hT)
    (fun x => (G x).used) (fun j => Or.inr (Or.inl (Or.inl ⟨j,rfl⟩)))
  let ds := ((List.finRange (t+1)).filter (fun i => decide (i.val ≤ h))).map cnt
  have o := orListB (A:=B1 ∪ Set.range cnt) ds (fun f hf => by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨j,rfl⟩) (Or.inl (Or.inl hF))
  have ds_len : ds.length ≤ t+1 := by
    simp only [ds,List.length_map]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have sem : (fun x => ds.any (fun f => f x)) = fun x => decide ((quadPolarMatrix (Q0 x)).rank ≤ h) := by
    funext x
    let A := quadPolarMatrix (Q0 x)
    have gr : (Finset.univ.filter (fun j => (G x).used j=true)).card = A.rank := by
      calc _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (M x))) := gaussElim_rank_eq _ pay
           _ = (Matrix.of (M x)).rank := (matrix_rank_eq_rowSpan_finrank _).symm
           _ = A.rank := Matrix.rank_reindex (Equiv.refl _) e A
    have cs (i : Fin (t+1)) : cnt i x = decide (i.val=A.rank) := by
      change countOneHot (G x).used i = _; rw [countOneHot_spec,gr]
    have eh : ds.any (fun f => f x) = true ↔ A.rank ≤ h := by
      simp only [ds,List.any_map,List.any_eq_true,List.mem_filter,List.mem_finRange,true_and,
        decide_eq_true_eq,Function.comp_apply,cs]
      constructor
      · rintro ⟨i,hi,he⟩; omega
      · intro hh
        have hr : A.rank ≤ t := by simpa using A.rank_le_card_height
        exact ⟨⟨A.rank,by omega⟩,hh,rfl⟩
    change ds.any (fun f => f x) = decide (A.rank ≤ h)
    by_cases hh : A.rank ≤ h
    · rw [decide_eq_true hh]; exact eh.mpr hh
    · rw [decide_eq_false hh]; cases hx : ds.any (fun f => f x) with
      | false => rfl
      | true => exact (hh (eh.mp hx)).elim
  rw [sem] at o
  have b := seq2B g (seq2B c o)
  exact relaxB b le_rfl Set.subset_union_right (by dsimp only [Nat.add_zero]; omega)

theorem quadPolarRankBoundB {N m t : Nat} (k r : Nat) (Base : Set (Sig N)) (h : Nat)
    (Q0 : (Fin N → Bool) → Fin t → Quad m)
    (hF : (fun _ => false) ∈ Base) (hT : (fun _ => true) ∈ Base)
    (hQ : ∀ j, quadSigs (fun x => Q0 x j) ⊆ Base) :
    Build Base {fun x => decide ((quadPolarMatrix (Q0 x)).rank ≤ h)}
      (2^12*(k+m+r+t+4)^10) := by
  refine relaxB (quadPolarRankB Base h Q0 hF hT hQ) le_rfl Set.subset_union_right ?_
  let d := k+m+r+t
  have hm : m ≤ d := by dsimp [d]; omega
  have ht : t ≤ d := by dsimp [d]; omega
  change _ ≤ 2^12*(d+4)^10
  calc _ ≤ (d*d)*(d*(d+4)+(d*d)*(2*d)+d*(1+(d*d)*10))+d*((d+1)*4)+(d+1) := by gcongr
       _ ≤ _ := by ring_nf; omega

end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
def genericCount {k m t : ℕ} (q : ℕ) (gen : Fin m → Fin k → ZMod 2) (Q0 : Fin t → Quad m) : ℕ :=
  let h := min q t
  let M0 : Fin t → Fin (m * m) → ZMod 2 := fun j idx =>
    let ab := finProdFinEquiv.symm idx
    (Q0 j).B ab.1 ab.2
  let Pay0 : Fin t → Fin (m + 1) → ZMod 2 := fun j p =>
    if hp : p.val < m then (Q0 j).l ⟨p.val, hp⟩ else (Q0 j).c
  let gs1 := gaussElim M0 Pay0
  let Q1 : Fin t → Quad m := fun j =>
    { B := fun a b => gs1.M j (finProdFinEquiv (a, b))
      l := fun i => gs1.Pay j i.castSucc
      c := gs1.Pay j (Fin.last m) }
  let pk : PackState m h := packUsed gs1.used Q1
  let A0 : Fin t → Fin m → ZMod 2 := fun j i => if gs1.used j then 0 else (Q1 j).l i
  let b0 : Fin t → ZMod 2 := fun j => if gs1.used j then 0 else (Q1 j).c
  let aff := affElim A0 b0 pk.qs
  let consistent : Bool := (List.finRange t).all (fun r => aff.affUsed r || !(z2b (aff.b r)))
  let free : Fin m → Bool := fun i => !(aff.varElim i)
  let posList : List ℕ := (List.finRange (2 ^ h)).map (fun σ =>
    posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))
  let negList : List ℕ := (List.finRange (2 ^ h)).map (fun σ =>
    negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))
  let shifted : ℕ := if consistent then posList.sum - negList.sum else 0
  let gsGen := gaussElim gen (fun _ => Fin.elim0)
  let rGen := (Finset.univ.filter (fun j : Fin m => gsGen.used j = true)).card
  shifted / 2 ^ (h + m - rGen)

def genericBit {k m t : ℕ} (q : ℕ) (gen : Fin m → Fin k → ZMod 2) (Q0 : Fin t → Quad m) (o : Fin (k+1)) : Bool :=
    let h := min q t
    let L := m + h + 1
    let gsGen := gaussElim gen (fun _ => Fin.elim0)
    let rGenOH := countOneHot gsGen.used
    let M0 : Fin t → Fin (m * m) → ZMod 2 := fun j idx =>
      let ab := finProdFinEquiv.symm idx
      (Q0 j).B ab.1 ab.2
    let Pay0 : Fin t → Fin (m + 1) → ZMod 2 := fun j p =>
      if hp : p.val < m then (Q0 j).l ⟨p.val, hp⟩ else (Q0 j).c
    let gs1 := gaussElim M0 Pay0
    let Q1 : Fin t → Quad m := fun j =>
      { B := fun a b => gs1.M j (finProdFinEquiv (a, b))
        l := fun i => gs1.Pay j i.castSucc
        c := gs1.Pay j (Fin.last m) }
    let pk : PackState m h := packUsed gs1.used Q1
    let A0 : Fin t → Fin m → ZMod 2 := fun j i => if gs1.used j then 0 else (Q1 j).l i
    let b0 : Fin t → ZMod 2 := fun j => if gs1.used j then 0 else (Q1 j).c
    let aff := affElim A0 b0 pk.qs
    let consistent : Bool := (List.finRange t).all (fun r => aff.affUsed r || !(z2b (aff.b r)))
    let free : Fin m → Bool := fun i => !(aff.varElim i)
    let posSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
      posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
    let negSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
      negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
    let shifted : ℕ := if consistent then posSum - negSum else 0
    (List.finRange (m + 1)).any (fun r =>
      rGenOH r && (if _hlt : h + m - r.val + o.val < L then
        shifted.testBit (h + m - r.val + o.val) else false))

set_option maxHeartbeats 4000000 in
theorem genericCount_bits_eq {k m t : ℕ} (q : ℕ) (gen : Fin m → Fin k → ZMod 2) (Q0 : Fin t → Quad m) :
    let h := min q t
    let L := m + h + 1
    let gsGen := gaussElim gen (fun _ => Fin.elim0)
    let rGenOH := countOneHot gsGen.used
    let M0 : Fin t → Fin (m * m) → ZMod 2 := fun j idx =>
      let ab := finProdFinEquiv.symm idx
      (Q0 j).B ab.1 ab.2
    let Pay0 : Fin t → Fin (m + 1) → ZMod 2 := fun j p =>
      if hp : p.val < m then (Q0 j).l ⟨p.val, hp⟩ else (Q0 j).c
    let gs1 := gaussElim M0 Pay0
    let Q1 : Fin t → Quad m := fun j =>
      { B := fun a b => gs1.M j (finProdFinEquiv (a, b))
        l := fun i => gs1.Pay j i.castSucc
        c := gs1.Pay j (Fin.last m) }
    let pk : PackState m h := packUsed gs1.used Q1
    let A0 : Fin t → Fin m → ZMod 2 := fun j i => if gs1.used j then 0 else (Q1 j).l i
    let b0 : Fin t → ZMod 2 := fun j => if gs1.used j then 0 else (Q1 j).c
    let aff := affElim A0 b0 pk.qs
    let consistent : Bool := (List.finRange t).all (fun r => aff.affUsed r || !(z2b (aff.b r)))
    let free : Fin m → Bool := fun i => !(aff.varElim i)
    let posSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
      posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
    let negSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
      negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
    let shifted : ℕ := if consistent then posSum - negSum else 0
    shifted < 2 ^ L →
    ∀ o : Fin (k + 1),
      (genericCount q gen Q0).testBit o.val =
      (List.finRange (m + 1)).any (fun r =>
        rGenOH r && (if _hlt : h + m - r.val + o.val < L then
          shifted.testBit (h + m - r.val + o.val) else false)) := by
  intro h L gsGen rGenOH M0 Pay0 gs1 Q1 pk A0 b0 aff consistent free
    posSum negSum shifted hsh_lt o
  let rGen := (Finset.univ.filter (fun j : Fin m => gsGen.used j = true)).card
  have hrGen_le : rGen ≤ m := by
    calc rGen ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
      _ = m := Fintype.card_fin m
  have hrOH : ∀ r : Fin (m + 1), rGenOH r = decide (r.val = rGen) :=
    fun r => congrFun (countOneHot_spec gsGen.used) r
  have hdiv : (genericCount q gen Q0).testBit o.val = shifted.testBit (h + m - rGen + o.val) := by
    change (shifted / 2 ^ (h + m - rGen)).testBit o.val = shifted.testBit (h + m - rGen + o.val)
    rw [testBit_eq_decide_div_mod, testBit_eq_decide_div_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hdiv]
  let r0 : Fin (m + 1) := ⟨rGen, by omega⟩
  have hany : (List.finRange (m + 1)).any (fun r =>
      rGenOH r && (if hlt : h + m - r.val + o.val < L then shifted.testBit (h + m - r.val + o.val) else false)) =
      (if hlt : h + m - rGen + o.val < L then shifted.testBit (h + m - rGen + o.val) else false) := by
    cases hval : (if hlt : h + m - rGen + o.val < L then shifted.testBit (h + m - rGen + o.val) else false)
    · rw [List.any_eq_false]
      intro r _
      by_cases hre : r.val = rGen
      · simp [hrOH r, hre, hval]
      · simp [hrOH r, hre]
    · exact List.any_eq_true.mpr ⟨r0, List.mem_finRange r0, by simp [hrOH r0, r0, hval]⟩
  rw [hany]
  by_cases hlt : h + m - rGen + o.val < L
  · simp [hlt]
  · simp only [hlt, ↓reduceDIte]
    have hlt2 : shifted < 2 ^ (h + m - rGen + o.val) :=
      lt_of_lt_of_le hsh_lt (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.testBit_lt_two_pow hlt2

set_option maxHeartbeats 4000000 in
theorem genericCount_correct {k m t : ℕ} (q : ℕ) (base : Fin k → ZMod 2) (gen : Fin m → Fin k → ZMod 2) (Q0 : Fin t → Quad m)
    (P : (Fin k → ZMod 2) → Fin t → Prop) (hQ0_val : ∀ j, (Q0 j).Valid)
    (hEval : ∀ j (a : Fin m → ZMod 2), (Q0 j).eval a = 0 ↔ P (base + ∑ i, a i • gen i) j)
    (hHrank : Matrix.rank (fun j ab => (Q0 j).B ab.1 ab.2 : Matrix (Fin t) (Fin m × Fin m) (ZMod 2)) ≤ q) :
    let W := Fin k → ZMod 2
    let X := Fin m → ZMod 2
    let key := fun a : X => base + ∑ i, a i • gen i
    let count := Nat.card {w : W // w ∈ Set.range key ∧ ∀ j, P w j}
    genericCount q gen Q0 = count ∧
    (let h := min q t
     let M0 : Fin t → Fin (m * m) → ZMod 2 := fun j idx => (Q0 j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
     let Pay0 : Fin t → Fin (m + 1) → ZMod 2 := fun j p => if hp : p.val < m then (Q0 j).l ⟨p.val, hp⟩ else (Q0 j).c
     let gs1 := gaussElim M0 Pay0
     let Q1 : Fin t → Quad m := fun j =>
       { B := fun a b => gs1.M j (finProdFinEquiv (a, b))
         l := fun i => gs1.Pay j i.castSucc
         c := gs1.Pay j (Fin.last m) }
     let pk : PackState m h := packUsed gs1.used Q1
     let A0 : Fin t → Fin m → ZMod 2 := fun j i => if gs1.used j then 0 else (Q1 j).l i
     let b0 : Fin t → ZMod 2 := fun j => if gs1.used j then 0 else (Q1 j).c
     let aff := affElim A0 b0 pk.qs
     let consistent : Bool := (List.finRange t).all (fun r => aff.affUsed r || !(z2b (aff.b r)))
     let free : Fin m → Bool := fun i => !(aff.varElim i)
     let posSum := ((List.finRange (2 ^ h)).map (fun σ =>
       posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
     let negSum := ((List.finRange (2 ^ h)).map (fun σ =>
       negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
     (if consistent then posSum - negSum else 0) < 2 ^ (m + h + 1)) := by
  classical
  intro W X key count
  let H : Matrix (Fin t) (Fin m × Fin m) (ZMod 2) := fun j ab => (Q0 j).B ab.1 ab.2
  have hH_eq_B : ∀ j a b, H j (a,b) = (Q0 j).B a b := fun _ _ _ => rfl
  let h := min q t
  let M0 : Fin t → Fin (m * m) → ZMod 2 := fun j idx =>
    (Q0 j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
  let Pay0 : Fin t → Fin (m + 1) → ZMod 2 := fun j p =>
    if hp : p.val < m then (Q0 j).l ⟨p.val, hp⟩ else (Q0 j).c
  let gs1 := gaussElim M0 Pay0
  have hM0_rank : (Finset.univ.filter (fun j : Fin t => gs1.used j = true)).card ≤ h := by
    have hcard_eq := gaussElim_rank_eq M0 Pay0
    have hfin_eq : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M0)) = H.rank := by
      let eqv : (Fin m × Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin (m * m) → ZMod 2) :=
        LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finProdFinEquiv.symm
      have hspan_map : Submodule.span (ZMod 2) (Set.range M0) =
          Submodule.map eqv.toLinearMap (Submodule.span (ZMod 2) (Set.range (fun j : Fin t => H j))) := by
        rw [Submodule.map_span]
        congr 1
        ext row
        constructor
        · rintro ⟨j, rfl⟩
          refine ⟨H j, ⟨j, rfl⟩, ?_⟩
          funext idx
          simp only [LinearEquiv.coe_coe, eqv, LinearEquiv.funCongrLeft_apply, M0]
          exact hH_eq_B j _ _
        · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
          refine ⟨j, ?_⟩
          funext idx
          simp only [LinearEquiv.coe_coe, eqv, LinearEquiv.funCongrLeft_apply, M0]
          exact (hH_eq_B j _ _).symm
      rw [hspan_map, LinearEquiv.finrank_map_eq, ← Matrix.rank_transpose]
      change _ = Module.finrank (ZMod 2) (LinearMap.range H.transpose.mulVecLin)
      have hsubEq : Submodule.span (ZMod 2) (Set.range (fun j : Fin t => H j)) =
          LinearMap.range H.transpose.mulVecLin := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          refine ⟨Pi.single j 1, ?_⟩
          funext ab
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          rw [Finset.sum_eq_single j]
          · simp
          · intro r _ hr; simp [Pi.single_eq_of_ne hr]
          · intro h'; exact absurd (Finset.mem_univ _) h'
        · rintro _ ⟨w, rfl⟩
          have hw : H.transpose.mulVecLin w = ∑ j : Fin t, w j • H j := by
            funext ab
            simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
          rw [hw]
          exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      rw [hsubEq]
    have hle_t : (Finset.univ.filter (fun j : Fin t => gs1.used j = true)).card ≤ t := by
      calc _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ _
        _ = t := Fintype.card_fin t
    have hle_q : (Finset.univ.filter (fun j : Fin t => gs1.used j = true)).card ≤ q := by
      rw [hcard_eq, hfin_eq]; exact hHrank
    exact le_min hle_q hle_t
  let Q1 : Fin t → Quad m := fun j =>
    { B := fun a b => gs1.M j (finProdFinEquiv (a, b))
      l := fun i => gs1.Pay j i.castSucc
      c := gs1.Pay j (Fin.last m) }
  rcases gaussElim_invariants M0 Pay0 with ⟨_, _, hgs1_zero, hgs1_lin, hgs1_prop⟩
  have hQ1_val : ∀ j, (Q1 j).Valid := by
    let PropRow : (Fin (m * m) → ZMod 2) → Prop := fun row =>
      (∀ i : Fin m, row (finProdFinEquiv (i, i)) = 0) ∧
      (∀ i j : Fin m, row (finProdFinEquiv (i, j)) = row (finProdFinEquiv (j, i)))
    have hall := hgs1_prop PropRow ⟨fun _ => rfl, fun _ _ => rfl⟩
      (fun u v hu hv => ⟨fun i => by simp [hu.1 i, hv.1 i], fun i j => by simp [hu.2 i j, hv.2 i j]⟩)
      (fun j => ⟨fun i => by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hQ0_val j).1 i,
        fun i r => by dsimp only [M0]; rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (hQ0_val j).2 i r⟩)
    exact fun j => hall j
  have hQ1_equiv : ∀ a : X, (∀ j : Fin t, (Q1 j).eval a = 0) ↔ (∀ j : Fin t, P (key a) j) := by
    intro a
    let mkQ : (Fin (m * m) → ZMod 2) → (Fin (m + 1) → ZMod 2) → Quad m := fun row pay =>
      { B := fun i j => row (finProdFinEquiv (i, j))
        l := fun i => pay i.castSucc
        c := pay (Fin.last m) }
    let evalMP : (Fin (m * m) → ZMod 2) → (Fin (m + 1) → ZMod 2) → ZMod 2 := fun row pay =>
      (mkQ row pay).eval a
    have hadd : ∀ m1 m2 p1 p2, evalMP (m1 + m2) (p1 + p2) = evalMP m1 p1 + evalMP m2 p2 :=
      fun m1 m2 p1 p2 => Quad.eval_add (mkQ m1 p1) (mkQ m2 p2) a
    have heq0 : ∀ j, evalMP (M0 j) (Pay0 j) = (Q0 j).eval a := by
      intro j
      change ({ B := fun i r => (Q0 j).B (finProdFinEquiv.symm (finProdFinEquiv (i, r))).1
                  (finProdFinEquiv.symm (finProdFinEquiv (i, r))).2
                l := fun i => if hi : i.castSucc.val < m then (Q0 j).l ⟨i.castSucc.val, hi⟩ else (Q0 j).c
                c := if hc : (Fin.last m).val < m then (Q0 j).l ⟨(Fin.last m).val, hc⟩ else (Q0 j).c } : Quad m).eval a = _
      congr 1
      cases hq : Q0 j with
      | mk B l c =>
        congr 1
        · funext i r; simp
        · funext i; simp [i.isLt]
        · simp
    have hiff := hgs1_lin (ZMod 2) evalMP hadd
    constructor
    · intro h1 j
      have h0 : (Q0 j).eval a = 0 := by rw [← heq0 j]; exact hiff.mp h1 j
      exact (hEval j a).mp h0
    · intro h1
      apply hiff.mpr
      intro j
      rw [heq0 j]; exact (hEval j a).mpr (h1 j)
  let pk : PackState m h := packUsed gs1.used Q1
  rcases packUsed_spec gs1.used Q1 hQ1_val hM0_rank with ⟨hpk_val, hpk_equiv⟩
  let A0 : Fin t → Fin m → ZMod 2 := fun j i => if gs1.used j then 0 else (Q1 j).l i
  let b0 : Fin t → ZMod 2 := fun j => if gs1.used j then 0 else (Q1 j).c
  have hQ1_unused : ∀ j a, gs1.used j = false →
      (Q1 j).eval a = b0 j + ∑ i : Fin m, A0 j i * a i := by
    intro j a hj
    have hB0 : ∀ r s : Fin m, (Q1 j).B r s = 0 := fun r s => hgs1_zero j hj (finProdFinEquiv (r, s))
    simp [Quad.eval, hB0, A0, b0, hj]
  let aff := affElim A0 b0 pk.qs
  let consistent : Bool := (List.finRange t).all (fun r => aff.affUsed r || !(z2b (aff.b r)))
  let free : Fin m → Bool := fun i => !(aff.varElim i)
  rcases affElim_spec A0 b0 pk.qs hpk_val with ⟨haff_val, haff_supp, haff_card⟩
  let SolA : Finset X := Finset.univ.filter (fun a : X => ∀ j : Fin t, P (key a) j)
  have hSolA_eq : SolA.card =
      if consistent then
        (Finset.univ.filter (fun a : X =>
          (∀ u : Fin m, aff.varElim u = true → a u = 0) ∧
          (∀ s : Fin h, (aff.qs s).eval a = 0))).card
      else 0 := by
    rw [← haff_card]
    congr 1
    ext a
    simp only [SolA, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hQ1_equiv a, ← hpk_equiv a]
    constructor
    · intro hall
      refine ⟨fun j => ?_, fun j _ => hall j⟩
      cases hu : gs1.used j
      · rw [← hQ1_unused j a hu]; exact hall j
      · simp [A0, b0, hu]
    · rintro ⟨haff0, hused0⟩ j
      cases hu : gs1.used j
      · rw [hQ1_unused j a hu]; exact haff0 j
      · exact hused0 j hu
  let Nfree : ℕ := (Finset.univ.filter (fun a : X =>
    (∀ u : Fin m, aff.varElim u = true → a u = 0) ∧
    (∀ s : Fin h, (aff.qs s).eval a = 0))).card
  let posSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
    posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
  let negSum : ℕ := ((List.finRange (2 ^ h)).map (fun σ =>
    negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))))).sum
  have hpos_neg_eq : (posSum : ℤ) - (negSum : ℤ) = (2 ^ h * Nfree : ℕ) := by
    have hsum_cast : ∀ (F : Fin (2 ^ h) → ℕ),
        (((List.finRange (2 ^ h)).map F).sum : ℤ) = ∑ σ : Fin (2 ^ h), (F σ : ℤ) := by
      intro F
      rw [← Fin.sum_univ_def, Nat.cast_sum]
    rw [hsum_cast, hsum_cast, ← Finset.sum_sub_distrib]
    have hterm : ∀ σ : Fin (2 ^ h),
        (posContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))) : ℤ) -
        (negContrib (evalGaussSum free (combineQuads aff.qs (maskOfNat h σ.val))) : ℤ) =
        ∑ a ∈ Supp free, signInt ((combineQuads aff.qs (maskOfNat h σ.val)).eval a) := by
      intro σ
      rw [contrib_sub_eq]
      have hsupp' : ∀ s u, free u = false → (aff.qs s).l u = 0 ∧ ∀ w, (aff.qs s).B u w = 0 := by
        intro s u hu
        have hve : aff.varElim u = true := by simp only [free, Bool.not_eq_false'] at hu; exact hu
        exact haff_supp s u hve
      exact (evalGaussSum_spec free _ (combineQuads_valid aff.qs haff_val _)
        (combineQuads_supp aff.qs free hsupp' _)).2
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hinner : ∀ a ∈ Supp free,
        ∑ σ : Fin (2 ^ h), signInt ((combineQuads aff.qs (maskOfNat h σ.val)).eval a) =
        if (∀ s : Fin h, (aff.qs s).eval a = 0) then (2 : ℤ) ^ h else 0 := by
      intro a _
      simp_rw [combineQuads_eval]
      let eqv := Equiv.ofBijective _ (maskOfNat_bijective h)
      have heqv_sum : ∑ σ : Fin (2 ^ h), signInt (∑ s : Fin h, maskOfNat h σ.val s * (aff.qs s).eval a) =
          ∑ τ : Fin h → ZMod 2, signInt (∑ s : Fin h, τ s * (aff.qs s).eval a) :=
        Fintype.sum_equiv eqv _ _ (fun _ => rfl)
      rw [heqv_sum]
      exact char_ortho_sum h (fun s => (aff.qs s).eval a)
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hcard_eq : (Finset.filter (fun a => ∀ s : Fin h, (aff.qs s).eval a = 0) (Supp free)).card = Nfree := by
      congr 1
      ext a
      simp only [Supp, Finset.mem_filter, Finset.mem_univ, true_and, free, Bool.not_eq_false']
    rw [hcard_eq]
    push_cast
    ring
  have hsub_nat : posSum - negSum = 2 ^ h * Nfree := by omega
  have hshifted_eq : (if consistent then posSum - negSum else 0) = 2 ^ h * SolA.card := by
    rw [hSolA_eq, hsub_nat]
    change (if consistent then 2 ^ h * Nfree else 0) = 2 ^ h * (if consistent then Nfree else 0)
    cases consistent <;> simp
  let Llin : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun a => ∑ j : Fin m, a j • gen j
      map_add' := fun a b => by
        funext p
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
          Finset.sum_add_distrib]
      map_smul' := fun c a => by
        funext p
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring) }
  have hrange_L : LinearMap.range Llin = Submodule.span (ZMod 2) (Set.range gen) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      change ∑ j : Fin m, a j • gen j ∈ Submodule.span (ZMod 2) (Set.range gen)
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨(Pi.single j (1 : ZMod 2) : Fin m → ZMod 2), ?_⟩
      change ∑ r : Fin m, ((Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) r) • gen r = gen j
      rw [Finset.sum_eq_single j]
      · simp
      · intro r _ hr; simp [Pi.single_eq_of_ne hr]
      · intro h'; exact absurd (Finset.mem_univ _) h'
  let gsGen := gaussElim gen (fun _ => Fin.elim0)
  let rGen := (Finset.univ.filter (fun j : Fin m => gsGen.used j = true)).card
  have hrGen_eq : rGen = Module.finrank (ZMod 2) (LinearMap.range Llin) := by
    rw [hrange_L]
    exact gaussElim_rank_eq gen (fun _ => Fin.elim0)
  have hrk_null := LinearMap.finrank_range_add_finrank_ker Llin
  rw [Module.finrank_fin_fun (ZMod 2)] at hrk_null
  have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker Llin) = m - rGen := by omega
  have hker_card : Fintype.card (LinearMap.ker Llin) = 2 ^ (m - rGen) := by
    rw [card_subspace_zmod2, hker_dim]
  let SolW : Finset W := Finset.univ.filter (fun w : W => w ∈ Set.range key ∧ ∀ j, P w j)
  have hcount_eq : count = SolW.card := by
    simp only [count, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hSolA_fiber : SolA.card = SolW.card * 2 ^ (m - rGen) := by
    have hmaps : ∀ a ∈ SolA, key a ∈ SolW := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, rfl⟩, (Finset.mem_filter.mp ha).2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ w ∈ SolW, (SolA.filter (fun a => key a = w)).card = 2 ^ (m - rGen) := by
      intro w hw
      rcases (Finset.mem_filter.mp hw).2 with ⟨⟨a0, ha0⟩, hprob⟩
      rw [← hker_card, ← Finset.card_univ]
      refine Finset.card_bij (fun a ha => (⟨a - a0, ?_⟩ : LinearMap.ker Llin)) ?_ ?_ ?_
      · have hka : key a = w := (Finset.mem_filter.mp ha).2
        simp only [LinearMap.mem_ker, map_sub]
        have h1 : Llin a = Llin a0 := by
          have : base + Llin a = base + Llin a0 := by change key a = key a0; rw [hka, ha0]
          exact add_left_cancel this
        exact sub_eq_zero.mpr h1
      · intro _ _; exact Finset.mem_univ _
      · intro a1 _ a2 _ heq
        have h1 : a1 - a0 = a2 - a0 := congrArg Subtype.val heq
        exact sub_left_inj.mp h1
      · rintro ⟨d, hd⟩ _
        refine ⟨a0 + d, ?_, ?_⟩
        · have hkd : key (a0 + d) = w := by
            change base + Llin (a0 + d) = w
            rw [map_add, LinearMap.mem_ker.mp hd, add_zero]
            exact ha0
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩, hkd⟩
          rw [hkd]; exact hprob j
        · apply Subtype.ext; simp
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have hSolW_le : SolW.card ≤ 2 ^ rGen := by
    have hsub : SolW ⊆ Finset.univ.image key := by
      intro w hw
      rcases (Finset.mem_filter.mp hw).2.1 with ⟨a, rfl⟩
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have himg_card : (Finset.univ.image key).card = 2 ^ rGen := by
      have hbij : (Finset.univ.image key).card = Fintype.card (LinearMap.range Llin) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun w hw => (⟨w - base, ?_⟩ : LinearMap.range Llin)) ?_ ?_ ?_
        · rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩
          exact ⟨a, by change Llin a = base + Llin a - base; ring⟩
        · intro _ _; exact Finset.mem_univ _
        · intro w1 _ w2 _ heq
          exact sub_left_inj.mp (congrArg Subtype.val heq)
        · rintro ⟨y, a, rfl⟩ _
          exact ⟨key a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩,
            Subtype.ext (by change base + Llin a - base = Llin a; ring)⟩
      rw [hbij, card_subspace_zmod2, ← hrGen_eq]
    calc SolW.card ≤ (Finset.univ.image key).card := Finset.card_le_card hsub
      _ = 2 ^ rGen := himg_card
  have hrGen_le_m : rGen ≤ m := by omega
  have hshifted_final : (if consistent then posSum - negSum else 0) =
      count * 2 ^ (h + m - rGen) := by
    rw [hshifted_eq, hSolA_fiber, hcount_eq]
    have hpow : 2 ^ h * (SolW.card * 2 ^ (m - rGen)) = SolW.card * (2 ^ h * 2 ^ (m - rGen)) := by ring
    rw [hpow, ← Nat.pow_add, show h + (m - rGen) = h + m - rGen by omega]
  have hshifted_lt : (if consistent then posSum - negSum else 0) < 2 ^ (m + h + 1) := by
    rw [hshifted_final, hcount_eq]
    calc
      SolW.card * 2 ^ (h + m - rGen) ≤ 2 ^ rGen * 2 ^ (h + m - rGen) :=
        Nat.mul_le_mul_right _ hSolW_le
      _ = 2 ^ (rGen + (h + m - rGen)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ (m + h) := by congr 1; omega
      _ < 2 ^ (m + h + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  refine ⟨?_, hshifted_lt⟩
  have halgo_eq : genericCount q gen Q0 = (if consistent then posSum - negSum else 0) / 2 ^ (h + m - rGen) := by
    rfl
  rw [halgo_eq, hshifted_final, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

set_option maxHeartbeats 4000000 in
theorem genericBit_correct {k m t : ℕ} (q : ℕ) (base : Fin k → ZMod 2) (gen : Fin m → Fin k → ZMod 2) (Q0 : Fin t → Quad m)
    (P : (Fin k → ZMod 2) → Fin t → Prop) (hQ0_val : ∀ j, (Q0 j).Valid)
    (hEval : ∀ j (a : Fin m → ZMod 2), (Q0 j).eval a = 0 ↔ P (base + ∑ i, a i • gen i) j)
    (hHrank : Matrix.rank (fun j ab => (Q0 j).B ab.1 ab.2 : Matrix (Fin t) (Fin m × Fin m) (ZMod 2)) ≤ q) (o : Fin (k+1)) :
    genericBit q gen Q0 o = (Nat.card {w : Fin k → ZMod 2 // w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ i, a i • gen i) ∧ ∀ j, P w j}).testBit o.val := by
  obtain ⟨hCount, hBound⟩ := genericCount_correct q base gen Q0 P hQ0_val hEval hHrank
  rw [← hCount]
  exact (genericCount_bits_eq q gen Q0 hBound o).symm

set_option maxHeartbeats 4000000 in
theorem genericBitsB {inputs k m t : ℕ} (q : ℕ) (Base : Set (Sig inputs))
    (gen : (Fin inputs → Bool) → Fin m → Fin k → ZMod 2) (Q0 : (Fin inputs → Bool) → Fin t → Quad m)
    (hF : (fun _ => false) ∈ Base) (hT : (fun _ => true) ∈ Base)
    (hGen : ∀ i j, (fun x => z2b (gen x i j)) ∈ Base)
    (hQ : ∀ j, quadSigs (fun x => Q0 x j) ⊆ Base) (hValid : ∀ x j, (Q0 x j).Valid) :
    Build Base (Set.range (fun o x => genericBit q (gen x) (Q0 x) o))
      (2 ^ 20 * (k+m+t+2)^8 * 2 ^ (min q t)) := by
  let h := min q t
  let L := m + h + 1
  let gsGen := fun x => gaussElim (gen x) (fun _ => Fin.elim0)
  let rGenOH := fun x => countOneHot (gsGen x).used
  let M0 := fun x j idx => (Q0 x j).B (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
  let Pay0 := fun x j (p : Fin (m+1)) => if hp : p.val < m then (Q0 x j).l ⟨p.val, hp⟩ else (Q0 x j).c
  let gs1 := fun x => gaussElim (M0 x) (Pay0 x)
  let Q1 := fun x j =>
    ({ B := fun a b => (gs1 x).M j (finProdFinEquiv (a, b))
       l := fun i => (gs1 x).Pay j i.castSucc
       c := (gs1 x).Pay j (Fin.last m) } : Quad m)
  let pk : (Fin inputs → Bool) → PackState m h := fun x => packUsed (gs1 x).used (Q1 x)
  let A0 := fun x j i => if (gs1 x).used j then 0 else (Q1 x j).l i
  let b0 := fun x j => if (gs1 x).used j then 0 else (Q1 x j).c
  let aff := fun x => affElim (A0 x) (b0 x) (pk x).qs
  let consistent := fun x => (List.finRange t).all (fun r => (aff x).affUsed r || !(z2b ((aff x).b r)))
  let free := fun x i => !((aff x).varElim i)
  let posSum := fun x => ((List.finRange (2 ^ h)).map (fun σ =>
    posContrib (evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val))))).sum
  let negSum := fun x => ((List.finRange (2 ^ h)).map (fun σ =>
    negContrib (evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val))))).sum
  let shifted := fun x => if consistent x then posSum x - negSum x else 0
  let outSig : Fin (k + 1) → Sig inputs := fun o x =>
    (List.finRange (m + 1)).any (fun r =>
      rGenOH x r && (if _hlt : h + m - r.val + o.val < L then
        (shifted x).testBit (h + m - r.val + o.val) else false))
  let B0 := Base
  have hF0 : (fun _ => false) ∈ B0 := hF
  have hT0 : (fun _ => true) ∈ B0 := hT
  have hS0 : Build B0 (⋃ j : Fin t, quadSigs (fun x => Q0 x j))
      (t * (160 + m * 40 + (m * (m * 10) + m * 15 + 5))) :=
    relaxB (idleB (Set.iUnion_subset hQ)) le_rfl Set.subset_union_right (Nat.zero_le _)
  let B1 := B0 ∪ ⋃ j : Fin t, quadSigs (fun x => Q0 x j)
  have hF1 : (fun _ => false) ∈ B1 := Or.inl hF0
  have hT1 : (fun _ => true) ∈ B1 := Or.inl hT0
  have hS1 : Build B1 (gaussSigs gs1)
      ((m * m) * (t * (t + 4) + (m * m + (m + 1)) * (2 * t) + t * (1 + (m * m + (m + 1)) * 10))) :=
    gaussElimB B1 hF1 M0 Pay0
      (fun j idx => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inl (Or.inl ⟨(finProdFinEquiv.symm idx).1,
        (finProdFinEquiv.symm idx).2, rfl⟩)⟩))
      (fun j p => by
        by_cases hp : p.val < m
        · have heq : (fun x => z2b (Pay0 x j p)) = fun x => z2b ((Q0 x j).l ⟨p.val, hp⟩) := by
            funext x; simp [Pay0, hp]
          rw [heq]; exact Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inl (Or.inr ⟨⟨p.val, hp⟩, rfl⟩)⟩)
        · have heq : (fun x => z2b (Pay0 x j p)) = fun x => z2b (Q0 x j).c := by
            funext x; simp [Pay0, hp]
          rw [heq]; exact Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inr rfl⟩))
  let B2 := B1 ∪ gaussSigs gs1
  have hF2 : (fun _ => false) ∈ B2 := Or.inl hF1
  have hT2 : (fun _ => true) ∈ B2 := Or.inl hT1
  have hPack : Build B2 (packSigs pk)
      (t * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4)))) :=
    packUsedB B2 hF2 hT2 (fun x => (gs1 x).used) Q1
      (fun j => Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))
      (fun j => by
        rintro f ((⟨a, b, rfl⟩ | ⟨i, rfl⟩) | rfl)
        · exact Or.inr (Or.inl (Or.inr ⟨j, finProdFinEquiv (a, b), rfl⟩))
        · exact Or.inr (Or.inr ⟨j, i.castSucc, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, Fin.last m, rfl⟩))
  have hA0B : Build B2 {f | ∃ j i, (fun x => z2b (A0 x j i)) = f} (t * (m * 2)) :=
    fin2SigB _ 2 (fun j i => by
      have hn : Build B2 {fun x => !((gs1 x).used j)} 1 := notB (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))
      have ha : Build (B2 ∪ {fun x => !((gs1 x).used j)}) {fun x => z2b (A0 x j i)} 1 := by
        have heq : (fun x => z2b (A0 x j i)) = fun x => !((gs1 x).used j) && z2b ((gs1 x).Pay j i.castSucc) := by
          funext x; simp only [A0, Q1]; cases (gs1 x).used j <;> simp [z2b_zero]
        rw [heq]
        exact andB (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨j, i.castSucc, rfl⟩)))
      exact seq2B hn ha)
  have hb0B : Build B2 (Set.range (fun j : Fin t => fun x => z2b (b0 x j))) (t * 2) :=
    finSigB _ 2 (fun j => by
      have hn : Build B2 {fun x => !((gs1 x).used j)} 1 := notB (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))
      have ha : Build (B2 ∪ {fun x => !((gs1 x).used j)}) {fun x => z2b (b0 x j)} 1 := by
        have heq : (fun x => z2b (b0 x j)) = fun x => !((gs1 x).used j) && z2b ((gs1 x).Pay j (Fin.last m)) := by
          funext x; simp only [b0, Q1]; cases (gs1 x).used j <;> simp [z2b_zero]
        rw [heq]
        exact andB (Or.inr rfl) (Or.inl (Or.inr (Or.inr ⟨j, Fin.last m, rfl⟩)))
      exact seq2B hn ha)
  have hS1b := unionB (unionB hPack hA0B) hb0B
  let B3 := B2 ∪ ((packSigs pk ∪ {f | ∃ j i, (fun x => z2b (A0 x j i)) = f}) ∪
    Set.range (fun j : Fin t => fun x => z2b (b0 x j)))
  have hF3 : (fun _ => false) ∈ B3 := Or.inl hF2
  have hT3 : (fun _ => true) ∈ B3 := Or.inl hT2
  have hS2 : Build B3 (affSigs aff)
      (m * (t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
        h * (m * (m * 14) + m * 19 + 9))) :=
    affElimB B3 hF3 A0 b0 (fun x => (pk x).qs)
      (fun j i => Or.inr (Or.inl (Or.inr ⟨j, i, rfl⟩)))
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
      (fun s => Set.subset_iUnion (fun s => quadSigs (fun x => (pk x).qs s)) s |>.trans
        (Set.subset_union_right.trans (Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_right))))
  let B4 := B3 ∪ affSigs aff
  have hF4 : (fun _ => false) ∈ B4 := Or.inl hF3
  have hT4 : (fun _ => true) ∈ B4 := Or.inl hT3
  have hConsB : Build B4 {consistent} (t * 2 + t) := by
    let term : Fin t → Sig inputs := fun r x => (aff x).affUsed r || !(z2b ((aff x).b r))
    have htB : Build B4 (Set.range term) (t * 2) :=
      finSigB term 2 (fun r => by
        have hn : Build B4 {fun x => !(z2b ((aff x).b r))} 1 :=
          notB (Or.inr (Or.inl (Or.inl (Or.inr ⟨r, rfl⟩))))
        have ho : Build (B4 ∪ {fun x => !(z2b ((aff x).b r))}) {term r} 1 :=
          orB (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))))) (Or.inr rfl)
        exact seq2B hn ho)
    have hallB : Build (B4 ∪ Set.range term) {consistent} t := by
      have h := andListB (A := B4 ∪ Set.range term) ((List.finRange t).map term)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
        (Or.inl hT4)
      have heq : (fun x => ((List.finRange t).map term).all (fun f => f x)) = consistent := by
        funext x; simp [consistent, term, List.all_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at h
      exact h
    exact seq2B htB hallB
  have hFreeB : Build B4 (Set.range (fun i : Fin m => fun x => free x i)) (m * 1) :=
    finSigB _ 1 (fun i => notB (Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))))
  have hS2b := unionB hConsB hFreeB
  let B5 := B4 ∪ ({consistent} ∪ Set.range (fun i : Fin m => fun x => free x i))
  have hF5 : (fun _ => false) ∈ B5 := Or.inl hF4
  have hT5 : (fun _ => true) ∈ B5 := Or.inl hT4
  let posF : Fin (2 ^ h) → (Fin inputs → Bool) → ℕ := fun σ x =>
    posContrib (evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val)))
  let negF : Fin (2 ^ h) → (Fin inputs → Bool) → ℕ := fun σ x =>
    negContrib (evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val)))
  let cSigma : ℕ := (m * (m * (4 * h)) + m * (4 * h) + 4 * h) +
    m * (m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40)) + (4 + L * 2)
  have hOneSigma : ∀ σ : Fin (2 ^ h),
      Build B5 (Set.range (bitsOf L (posF σ)) ∪ Set.range (bitsOf L (negF σ))) cSigma := by
    intro σ
    have hcomb : Build B5 (quadSigs (fun x => combineQuads (aff x).qs (maskOfNat h σ.val)))
        (m * (m * (4 * h)) + m * (4 * h) + 4 * h) :=
      combineQuadsB B5 hF5 (fun x => (aff x).qs)
        (fun s => Set.subset_iUnion (fun s => quadSigs (fun x => (aff x).qs s)) s |>.trans
          (Set.subset_union_right.trans (Set.subset_union_right.trans Set.subset_union_left)))
        (maskOfNat h σ.val)
    have hgs : Build (B5 ∪ quadSigs (fun x => combineQuads (aff x).qs (maskOfNat h σ.val)))
        (sumSigs (fun x => evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val))))
        (m * (m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40))) :=
      evalGaussSumB _ (Or.inl hF5) (Or.inl hT5) free
        (fun x => combineQuads (aff x).qs (maskOfNat h σ.val))
        (fun u => Or.inl (Or.inr (Or.inr ⟨u, rfl⟩)))
        Set.subset_union_right
    let stσ : (Fin inputs → Bool) → SumState m :=
      fun x => evalGaussSum (free x) (combineQuads (aff x).qs (maskOfNat h σ.val))
    have hst_pow : ∀ x, ∃ e ≤ m, (stσ x).pow2 = fun k : Fin (m + 1) => decide (k.val = e) := by
      intro x
      have hQ1v : ∀ j, (Q1 x j).Valid := by
        let PropRow : (Fin (m * m) → ZMod 2) → Prop := fun row =>
          (∀ i : Fin m, row (finProdFinEquiv (i, i)) = 0) ∧
          (∀ i j : Fin m, row (finProdFinEquiv (i, j)) = row (finProdFinEquiv (j, i)))
        exact (gaussElim_invariants (M0 x) (Pay0 x)).2.2.2.2 PropRow ⟨fun _ => rfl, fun _ _ => rfl⟩
          (fun u v hu hv => ⟨fun i => by simp [hu.1 i, hv.1 i], fun i j => by simp [hu.2 i j, hv.2 i j]⟩)
          (fun j => ⟨fun i => by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hValid x j).1 i,
            fun i r => by dsimp only [M0]; rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (hValid x j).2 i r⟩)
      have haff_sp := affElim_spec (A0 x) (b0 x) (pk x).qs (packUsed_valid (gs1 x).used (Q1 x) hQ1v)
      have hsupp' : ∀ s u, free x u = false → ((aff x).qs s).l u = 0 ∧ ∀ w, ((aff x).qs s).B u w = 0 := by
        intro s u hu
        have hve : (aff x).varElim u = true := by simp only [free, Bool.not_eq_false'] at hu; exact hu
        exact haff_sp.2.1 s u hve
      exact (evalGaussSum_spec (free x) _ (combineQuads_valid (aff x).qs haff_sp.1 _)
        (combineQuads_supp (aff x).qs (free x) hsupp' _)).1
    let Aσ := (B5 ∪ quadSigs (fun x => combineQuads (aff x).qs (maskOfNat h σ.val))) ∪ sumSigs stσ
    let nZero : Sig inputs := fun x => !((stσ x).zero)
    let nC : Sig inputs := fun x => !(z2b (stσ x).Q.c)
    let posEn : Sig inputs := fun x => nZero x && nC x
    let negEn : Sig inputs := fun x => nZero x && z2b (stσ x).Q.c
    have henB : Build Aσ ({posEn} ∪ {negEn}) 4 := by
      have h1 : Build Aσ {nZero} 1 := notB (Or.inr (Or.inl (Or.inr rfl)))
      have h2 : Build (Aσ ∪ {nZero}) {nC} 1 :=
        notB (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))
      have h3 : Build ((Aσ ∪ {nZero}) ∪ {nC}) {posEn} 1 :=
        andB (Or.inl (Or.inr rfl)) (Or.inr rfl)
      have h4 : Build (((Aσ ∪ {nZero}) ∪ {nC}) ∪ {posEn}) {negEn} 1 :=
        andB (Or.inl (Or.inl (Or.inr rfl)))
          (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))))
      exact relaxB (transB (transB (extB h1) (extB h2)) (seqB h3 h4)) le_rfl Set.subset_union_right (by omega)
    let Aσ2 := Aσ ∪ ({posEn} ∪ {negEn})
    have hposBits : Build Aσ2 (Set.range (bitsOf L (posF σ))) (L * 1) := by
      refine finSigB _ 1 (fun j => ?_)
      by_cases hj : j.val < m + 1
      · have heq : bitsOf L (posF σ) j = fun x => posEn x && (stσ x).pow2 ⟨j.val, hj⟩ := by
          funext x
          rcases hst_pow x with ⟨e, he, hpow⟩
          change (posContrib (stσ x)).testBit j.val = (posEn x && (stσ x).pow2 ⟨j.val, hj⟩)
          simp only [posContrib, posEn, nZero, nC]
          cases hcond : !(stσ x).zero && !(z2b (stσ x).Q.c)
          · simp
          · simp only [↓reduceIte, Bool.true_and, hpow, oneHotVal_testBit he, hj]
        rw [heq]
        exact andB (Or.inr (Or.inl rfl)) (Or.inl (Or.inr (Or.inr ⟨⟨j.val, hj⟩, rfl⟩)))
      · have heq : bitsOf L (posF σ) j = fun _ => false := by
          funext x
          rcases hst_pow x with ⟨e, he, hpow⟩
          change (posContrib (stσ x)).testBit j.val = false
          simp only [posContrib]
          cases !(stσ x).zero && !(z2b (stσ x).Q.c)
          · simp
          · simp only [↓reduceIte, hpow, oneHotVal_testBit he, hj]
        rw [heq]
        exact relaxB (idleB (A := Aσ2) (B := {fun _ => false})
          (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl hF5))))) le_rfl Set.subset_union_right (by omega)
    have hnegBits : Build Aσ2 (Set.range (bitsOf L (negF σ))) (L * 1) := by
      refine finSigB _ 1 (fun j => ?_)
      by_cases hj : j.val < m + 1
      · have heq : bitsOf L (negF σ) j = fun x => negEn x && (stσ x).pow2 ⟨j.val, hj⟩ := by
          funext x
          rcases hst_pow x with ⟨e, he, hpow⟩
          change (negContrib (stσ x)).testBit j.val = (negEn x && (stσ x).pow2 ⟨j.val, hj⟩)
          simp only [negContrib, negEn, nZero]
          cases hcond : !(stσ x).zero && z2b (stσ x).Q.c
          · simp
          · simp only [↓reduceIte, Bool.true_and, hpow, oneHotVal_testBit he, hj]
        rw [heq]
        exact andB (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨⟨j.val, hj⟩, rfl⟩)))
      · have heq : bitsOf L (negF σ) j = fun _ => false := by
          funext x
          rcases hst_pow x with ⟨e, he, hpow⟩
          change (negContrib (stσ x)).testBit j.val = false
          simp only [negContrib]
          cases !(stσ x).zero && z2b (stσ x).Q.c
          · simp
          · simp only [↓reduceIte, hpow, oneHotVal_testBit he, hj]
        rw [heq]
        exact relaxB (idleB (A := Aσ2) (B := {fun _ => false})
          (Set.singleton_subset_iff.mpr (Or.inl (Or.inl (Or.inl hF5))))) le_rfl Set.subset_union_right (by omega)
    exact relaxB (transB (transB (transB (extB hcomb) (extB hgs)) (extB henB)) (unionB hposBits hnegBits))
      le_rfl Set.subset_union_right (by omega)
  have hAllSig : Build B5
      (⋃ σ : Fin (2 ^ h), Set.range (bitsOf L (posF σ)) ∪ Set.range (bitsOf L (negF σ)))
      (2 ^ h * cSigma) :=
    finB _ cSigma hOneSigma
  let B6 := B5 ∪ ⋃ σ : Fin (2 ^ h), Set.range (bitsOf L (posF σ)) ∪ Set.range (bitsOf L (negF σ))
  have hF6 : (fun _ => false) ∈ B6 := Or.inl hF5
  have hT6 : (fun _ => true) ∈ B6 := Or.inl hT5
  have hsumList_eq : ∀ (Fs : Fin (2 ^ h) → (Fin inputs → Bool) → ℕ) (x : Fin inputs → Bool),
      sumListVal ((List.finRange (2 ^ h)).map Fs) x =
      ((List.finRange (2 ^ h)).map (fun σ => Fs σ x)).sum := by
    intro Fs x
    have hgen : ∀ (l : List (Fin (2 ^ h))),
        sumListVal (l.map Fs) x = (l.map (fun σ => Fs σ x)).sum := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [sumListVal, ih]
    exact hgen (List.finRange (2 ^ h))
  have hPosSumB : Build B6 (Set.range (bitsOf L posSum)) (2 ^ h * (9 * L)) := by
    have h1 := sumListB (A := B6) L hF6 ((List.finRange (2 ^ h)).map posF)
      (fun F hF j => by
        rcases List.mem_map.mp hF with ⟨σ, _, rfl⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨σ, Or.inl ⟨j, rfl⟩⟩))
    have heq : sumListVal ((List.finRange (2 ^ h)).map posF) = posSum :=
      funext (hsumList_eq posF)
    rw [heq, List.length_map, List.length_finRange] at h1
    exact h1
  have hNegSumB : Build B6 (Set.range (bitsOf L negSum)) (2 ^ h * (9 * L)) := by
    have h1 := sumListB (A := B6) L hF6 ((List.finRange (2 ^ h)).map negF)
      (fun F hF j => by
        rcases List.mem_map.mp hF with ⟨σ, _, rfl⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨σ, Or.inr ⟨j, rfl⟩⟩))
    have heq : sumListVal ((List.finRange (2 ^ h)).map negF) = negSum :=
      funext (hsumList_eq negF)
    rw [heq, List.length_map, List.length_finRange] at h1
    exact h1
  have hSumsB := unionB hPosSumB hNegSumB
  let B7 := B6 ∪ (Set.range (bitsOf L posSum) ∪ Set.range (bitsOf L negSum))
  have hF7 : (fun _ => false) ∈ B7 := Or.inl hF6
  have hT7 : (fun _ => true) ∈ B7 := Or.inl hT6
  have hvalidSub : ∀ x, negSum x ≤ posSum x ∧ negSum x < 2 ^ L := by
    intro x
    have hQ1v : ∀ j, (Q1 x j).Valid := by
      let PropRow : (Fin (m * m) → ZMod 2) → Prop := fun row =>
        (∀ i : Fin m, row (finProdFinEquiv (i, i)) = 0) ∧
        (∀ i j : Fin m, row (finProdFinEquiv (i, j)) = row (finProdFinEquiv (j, i)))
      exact (gaussElim_invariants (M0 x) (Pay0 x)).2.2.2.2 PropRow ⟨fun _ => rfl, fun _ _ => rfl⟩
        (fun u v hu hv => ⟨fun i => by simp [hu.1 i, hv.1 i], fun i j => by simp [hu.2 i j, hv.2 i j]⟩)
        (fun j => ⟨fun i => by dsimp only [M0]; rw [Equiv.symm_apply_apply]; exact (hValid x j).1 i,
          fun i r => by dsimp only [M0]; rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact (hValid x j).2 i r⟩)
    have haff_sp := affElim_spec (A0 x) (b0 x) (pk x).qs (packUsed_valid (gs1 x).used (Q1 x) hQ1v)
    have hsupp' : ∀ s u, free x u = false → ((aff x).qs s).l u = 0 ∧ ∀ w, ((aff x).qs s).B u w = 0 := by
      intro s u hu
      have hve : (aff x).varElim u = true := by simp only [free, Bool.not_eq_false'] at hu; exact hu
      exact haff_sp.2.1 s u hve
    have hdiff_ge : (0 : ℤ) ≤ (posSum x : ℤ) - (negSum x : ℤ) := by
      have hsum_cast : ∀ (F : Fin (2 ^ h) → ℕ),
          (((List.finRange (2 ^ h)).map F).sum : ℤ) = ∑ σ : Fin (2 ^ h), (F σ : ℤ) := fun F => by
        rw [← Fin.sum_univ_def, Nat.cast_sum]
      rw [show (posSum x : ℤ) = ∑ σ : Fin (2 ^ h), (posF σ x : ℤ) from hsum_cast (fun σ => posF σ x),
        show (negSum x : ℤ) = ∑ σ : Fin (2 ^ h), (negF σ x : ℤ) from hsum_cast (fun σ => negF σ x),
        ← Finset.sum_sub_distrib]
      have hterm : ∀ σ : Fin (2 ^ h),
          (posF σ x : ℤ) - (negF σ x : ℤ) =
          ∑ a ∈ Supp (free x), signInt ((combineQuads (aff x).qs (maskOfNat h σ.val)).eval a) := fun σ => by
        rw [contrib_sub_eq]
        exact (evalGaussSum_spec (free x) _ (combineQuads_valid (aff x).qs haff_sp.1 _)
          (combineQuads_supp (aff x).qs (free x) hsupp' _)).2
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_nonneg (fun a _ => ?_)
      simp_rw [combineQuads_eval]
      let eqv := Equiv.ofBijective _ (maskOfNat_bijective h)
      have heqv_sum : ∑ σ : Fin (2 ^ h), signInt (∑ s : Fin h, maskOfNat h σ.val s * ((aff x).qs s).eval a) =
          ∑ τ : Fin h → ZMod 2, signInt (∑ s : Fin h, τ s * ((aff x).qs s).eval a) :=
        Fintype.sum_equiv eqv _ _ (fun _ => rfl)
      rw [heqv_sum, char_ortho_sum]
      split_ifs
      · positivity
      · exact le_rfl
    have hneg_lt : negSum x < 2 ^ L := by
      have hsum_le : negSum x ≤ ∑ _σ : Fin (2 ^ h), 2 ^ m := by
        rw [show negSum x = ∑ σ : Fin (2 ^ h), negF σ x from (Fin.sum_univ_def _).symm]
        refine Finset.sum_le_sum (fun σ _ => ?_)
        rcases (evalGaussSum_spec (free x) _ (combineQuads_valid (aff x).qs haff_sp.1 _)
          (combineQuads_supp (aff x).qs (free x) hsupp' _)).1 with ⟨e, he, hpow⟩
        exact (posContrib_le _ e he hpow).2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
      calc
        negSum x ≤ 2 ^ h * 2 ^ m := hsum_le
        _ = 2 ^ (m + h) := by rw [Nat.mul_comm, ← Nat.pow_add]
        _ < 2 ^ L := Nat.pow_lt_pow_right (by omega) (by simp [L])
    exact ⟨by omega, hneg_lt⟩
  have hSubB : Build B7 (Set.range (bitsOf L (fun x => posSum x - negSum x))) (19 * L) :=
    subTwoB L posSum negSum hF7 hT7 (fun j => Or.inr (Or.inl ⟨j, rfl⟩))
      (fun j => Or.inr (Or.inr ⟨j, rfl⟩)) hvalidSub
  let B8 := B7 ∪ Set.range (bitsOf L (fun x => posSum x - negSum x))
  have hShiftB : Build B8 (Set.range (bitsOf L shifted)) (L * 1) :=
    finSigB _ 1 (fun j => by
      have heq : bitsOf L shifted j = fun x => consistent x && bitsOf L (fun x => posSum x - negSum x) j x := by
        funext x; simp only [bitsOf, shifted]; cases consistent x <;> simp
      rw [heq]
      exact andB (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))) (Or.inr ⟨j, rfl⟩))
  have hGenElimB : Build B0 (gaussSigs gsGen)
      (k * (m * (m + 4) + (k + 0) * (2 * m) + m * (1 + (k + 0) * 10))) :=
    gaussElimB B0 hF0 gen (fun _ _ => Fin.elim0)
      hGen
      (fun _ p => Fin.elim0 p)
  have hGenOHB : Build (B0 ∪ gaussSigs gsGen)
      (Set.range (fun r : Fin (m + 1) => fun x => rGenOH x r)) (m * ((m + 1) * 4)) :=
    countOneHotB _ (Or.inl hF0) (Or.inl hT0) (fun x => (gsGen x).used)
      (fun j => Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))
  have hStage4Prep : Build B0 (Set.range (fun r : Fin (m + 1) => fun x => rGenOH x r))
      (k * (m * (m + 4) + (k + 0) * (2 * m) + m * (1 + (k + 0) * 10)) + m * ((m + 1) * 4)) :=
    seq2B hGenElimB hGenOHB
  have hMainPipe : Build B0 (Set.range (bitsOf L shifted))
      (t * (160 + m * 40 + (m * (m * 10) + m * 15 + 5)) +
       (m * m) * (t * (t + 4) + (m * m + (m + 1)) * (2 * t) + t * (1 + (m * m + (m + 1)) * 10)) +
       (t * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4))) + t * (m * 2) + t * 2) +
       m * (t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
         h * (m * (m * 14) + m * 19 + 9)) +
       (t * 2 + t + m * 1) +
       2 ^ h * cSigma +
       (2 ^ h * (9 * L) + 2 ^ h * (9 * L)) +
       19 * L + L * 1) :=
    transB (transB (transB (transB (transB (transB (transB (transB
      (extB hS0) (extB hS1)) (extB hS1b)) (extB hS2)) (extB hS2b)) (extB hAllSig)) (extB hSumsB)) (extB hSubB)) hShiftB
  let B9 := B0 ∪ (Set.range (bitsOf L shifted) ∪ Set.range (fun r : Fin (m + 1) => fun x => rGenOH x r))
  have hBoth := unionB hMainPipe hStage4Prep
  have hOutB : Build B9 (Set.range outSig) ((k + 1) * ((m + 1) * 2)) := by
    refine finSigB outSig ((m + 1) * 2) (fun o => ?_)
    let term : Fin (m + 1) → Sig inputs := fun r x =>
      rGenOH x r && (if hlt : h + m - r.val + o.val < L then
        (shifted x).testBit (h + m - r.val + o.val) else false)
    have htB : Build B9 (Set.range term) ((m + 1) * 1) :=
      finSigB term 1 (fun r => by
        by_cases hlt : h + m - r.val + o.val < L
        · have heq : term r = fun x => rGenOH x r && bitsOf L shifted ⟨h + m - r.val + o.val, hlt⟩ x := by
            funext x; simp [term, bitsOf, hlt]
          rw [heq]
          exact andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inr (Or.inl ⟨⟨h + m - r.val + o.val, hlt⟩, rfl⟩))
        · have heq : term r = fun _ => false := by funext x; simp [term, hlt]
          rw [heq]
          exact relaxB (idleB (A := B9) (B := {fun _ => false}) (Set.singleton_subset_iff.mpr (Or.inl hF0)))
            le_rfl Set.subset_union_right (by omega))
    have horB : Build (B9 ∪ Set.range term) {outSig o} (m + 1) := by
      have h1 := orListB (A := B9 ∪ Set.range term) ((List.finRange (m + 1)).map term)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
        (Or.inl (Or.inl hF0))
      have heq : (fun x => ((List.finRange (m + 1)).map term).any (fun f => f x)) = outSig o := by
        funext x; simp [outSig, term, List.any_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at h1
      exact h1
    exact relaxB (seq2B htB horB) le_rfl Set.subset_union_right (by omega)
  have hTotal := seq2B hBoth hOutB
  refine relaxB hTotal le_rfl Set.subset_union_right ?_
  have h_le_t : h ≤ t := Nat.min_le_right q t
  have h2h_pos : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  let N := k + m + t + 2
  have hkN : k ≤ N := by omega
  have hmN : m ≤ N := by omega
  have htN : t ≤ N := by omega
  have hhN : h ≤ N := by omega
  have hm1N : m + 1 ≤ N := by omega
  have hk1N : k + 1 ≤ N := by omega
  have hh1N : h + 1 ≤ N := by omega
  have hLN : L ≤ 2 * N := by simp only [L]; omega
  have hN2 : 2 ≤ N := by omega
  have hN_le_2 : N ≤ N ^ 2 := by
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * N := Nat.mul_le_mul_left N (by omega)
      _ = N ^ 2 := (pow_two N).symm
  have hN2_le_3 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN_le_3 : N ≤ N ^ 3 := le_trans hN_le_2 hN2_le_3
  have h1_le_3 : 1 ≤ N ^ 3 := le_trans (by omega) hN_le_3
  have hmul2 : ∀ a b, a ≤ N → b ≤ N → a * b ≤ N ^ 2 := fun a b ha hb => by
    calc a * b ≤ N * N := Nat.mul_le_mul ha hb
      _ = N ^ 2 := (pow_two N).symm
  have hmul3 : ∀ a b c, a ≤ N → b ≤ N → c ≤ N → a * (b * c) ≤ N ^ 3 := fun a b c ha hb hc => by
    calc a * (b * c) ≤ N * N ^ 2 := Nat.mul_le_mul ha (hmul2 b c hb hc)
      _ = N ^ 3 := by ring
  have hm2 : m * m ≤ N ^ 2 := hmul2 m m hmN hmN
  have ht2 : t * t ≤ N ^ 2 := hmul2 t t htN htN
  have hk2 : k * k ≤ N ^ 2 := hmul2 k k hkN hkN
  have hmt : m * t ≤ N ^ 2 := hmul2 m t hmN htN
  have hkm : k * m ≤ N ^ 2 := hmul2 k m hkN hmN
  have hm3 : m * (m * m) ≤ N ^ 3 := hmul3 m m m hmN hmN hmN
  have hm2h : m * (m * h) ≤ N ^ 3 := hmul3 m m h hmN hmN hhN
  have hm2t : m * (m * t) ≤ N ^ 3 := hmul3 m m t hmN hmN htN
  have htm2 : t * (m * m) ≤ N ^ 3 := hmul3 t m m htN hmN hmN
  have hhm2 : h * (m * m) ≤ N ^ 3 := hmul3 h m m hhN hmN hmN
  have hkm2 : k * (m * m) ≤ N ^ 3 := hmul3 k m m hkN hmN hmN
  have hk2m : k * (k * m) ≤ N ^ 3 := hmul3 k k m hkN hkN hmN
  have hcSigma_le : cSigma ≤ 400 * N ^ 3 := by
    have h1 : m * (m * (4 * h)) = 4 * (m * (m * h)) := by ring
    have h2 : m * (4 * h) = 4 * (m * h) := by ring
    have h3 : m * (m * (m + 7) + (m + 1) * (2 * m) + (m * (m * 26) + m * 60 + 40)) =
        29 * (m * (m * m)) + 69 * (m * m) + 40 * m := by ring
    have hmh : m * h ≤ N ^ 2 := hmul2 m h hmN hhN
    simp only [cSigma]
    rw [h1, h2, h3]
    omega
  have hp1 : t * (160 + m * 40 + (m * (m * 10) + m * 15 + 5)) ≤ 300 * N ^ 3 := by
    have heq : t * (160 + m * 40 + (m * (m * 10) + m * 15 + 5)) =
        165 * t + 55 * (m * t) + 10 * (t * (m * m)) := by ring
    rw [heq]; omega
  have hp2 : (m * m) * (t * (t + 4) + (m * m + (m + 1)) * (2 * t) + t * (1 + (m * m + (m + 1)) * 10)) ≤ 100 * N ^ 5 := by
    have h1 : t * (t + 4) + (m * m + (m + 1)) * (2 * t) + t * (1 + (m * m + (m + 1)) * 10) =
        t * t + 17 * t + 12 * (t * (m * m)) + 12 * (m * t) := by ring
    have h1le : t * (t + 4) + (m * m + (m + 1)) * (2 * t) + t * (1 + (m * m + (m + 1)) * 10) ≤ 100 * N ^ 3 := by
      rw [h1]; omega
    calc (m * m) * _ ≤ N ^ 2 * (100 * N ^ 3) := Nat.mul_le_mul hm2 h1le
      _ = 100 * N ^ 5 := by ring
  have hp3 : t * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4))) + t * (m * 2) + t * 2 ≤ 100 * N ^ 4 := by
    have hmh : m * h ≤ N ^ 2 := hmul2 m h hmN hhN
    have h1 : (h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4)) =
        9 * h + 4 + 4 * (h * (m * m)) + 4 * (m * h) := by ring
    have h1le : (h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4)) ≤ 50 * N ^ 3 := by
      rw [h1]; omega
    have htm : t * (m * 2) = 2 * (m * t) := by ring
    have hN3_le_4 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN2_le_4 : N ^ 2 ≤ N ^ 4 := le_trans hN2_le_3 hN3_le_4
    have hN_le_4 : N ≤ N ^ 4 := le_trans hN_le_3 hN3_le_4
    have hm1 : t * ((h + 1) * 4 + h * (1 + (m * (m * 4) + m * 4 + 4))) ≤ 50 * N ^ 4 := by
      calc t * _ ≤ N * (50 * N ^ 3) := Nat.mul_le_mul htN h1le
        _ = 50 * N ^ 4 := by ring
    rw [htm]; omega
  have hp4 : m * (t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
      h * (m * (m * 14) + m * 19 + 9)) ≤ 200 * N ^ 4 := by
    have hmh : m * h ≤ N ^ 2 := hmul2 m h hmN hhN
    have h1 : t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
        h * (m * (m * 14) + m * 19 + 9) =
        t * t + 18 * t + 12 * (m * t) + m + 14 * (h * (m * m)) + 19 * (m * h) + 9 * h := by ring
    have h1le : t * (t + 5) + (m + 1) * (2 * t) + t * (1 + m * 10 + 10) + m +
        h * (m * (m * 14) + m * 19 + 9) ≤ 200 * N ^ 3 := by
      rw [h1]; omega
    calc m * _ ≤ N * (200 * N ^ 3) := Nat.mul_le_mul hmN h1le
      _ = 200 * N ^ 4 := by ring
  have hp5 : 2 ^ h * cSigma + (2 ^ h * (9 * L) + 2 ^ h * (9 * L)) ≤ 500 * N ^ 3 * 2 ^ h := by
    have h1 : cSigma + 9 * L + 9 * L ≤ 500 * N ^ 3 := by omega
    calc 2 ^ h * cSigma + (2 ^ h * (9 * L) + 2 ^ h * (9 * L)) = 2 ^ h * (cSigma + 9 * L + 9 * L) := by ring
      _ ≤ 2 ^ h * (500 * N ^ 3) := Nat.mul_le_mul_left _ h1
      _ = 500 * N ^ 3 * 2 ^ h := by ring
  have hp6 : k * (m * (m + 4) + (k + 0) * (2 * m) + m * (1 + (k + 0) * 10)) + m * ((m + 1) * 4) +
      (k + 1) * ((m + 1) * 2) + (t * 2 + t + m * 1) + 19 * L + L * 1 + 2 ≤ 200 * N ^ 3 := by
    have heq : k * (m * (m + 4) + (k + 0) * (2 * m) + m * (1 + (k + 0) * 10)) + m * ((m + 1) * 4) +
        (k + 1) * ((m + 1) * 2) + (t * 2 + t + m * 1) + 19 * L + L * 1 + 2 =
        k * (m * m) + 7 * (k * m) + 12 * (k * (k * m)) + 4 * (m * m) + 7 * m + 2 * k + 3 * t + 20 * L + 4 := by ring
    rw [heq]; omega
  have hN3_le_8 : N ^ 3 ≤ N ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4_le_8 : N ^ 4 ≤ N ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN5_le_8 : N ^ 5 ≤ N ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsum_poly : 300 * N ^ 3 + 100 * N ^ 5 + 100 * N ^ 4 + 200 * N ^ 4 + 200 * N ^ 3 ≤ 1000 * N ^ 8 := by
    omega
  have hmul_2h : 1000 * N ^ 8 ≤ 1000 * N ^ 8 * 2 ^ h := Nat.le_mul_of_pos_right _ h2h_pos
  have h500_le : 500 * N ^ 3 * 2 ^ h ≤ 500 * N ^ 8 * 2 ^ h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hN3_le_8)
  have h1500_le : 1500 * N ^ 8 * 2 ^ h ≤ 2 ^ 20 * N ^ 8 * 2 ^ h := by
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
    norm_num
  have hadd_1500 : 1000 * N ^ 8 * 2 ^ h + 500 * N ^ 8 * 2 ^ h = 1500 * N ^ 8 * 2 ^ h := by ring
  change _ ≤ 2 ^ 20 * N ^ 8 * 2 ^ h
  omega

end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine
namespace Probe259
abbrev In (N : ℕ) := Fin N → Bool
variable {N k m r t : ℕ}
abbrev Val := In N → F
abbrev bit (f : Val (N := N)) : Sig N := fun x => z2b (f x)
abbrev Made (A : Set (Sig N)) (f : Val) (n : ℕ) := Build A {bit f} n

theorem get {A : Set (Sig N)} {f : Val} (hf : bit f ∈ A) : Made A f 0 := idleB (by simpa using hf)
theorem add {A : Set (Sig N)} {f g : Val} {a b : ℕ} (hf : Made A f a) (hg : Made A g b) :
    Made A (fun x => f x + g x) (a+b+4) := by
  have z := unionB hf hg
  apply seq2B z
  rw [show bit (fun x => f x + g x) = (fun x => xor (bit f x) (bit g x)) from funext fun x => z2b_add _ _]
  exact xorB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
theorem mul {A : Set (Sig N)} {f g : Val} {a b : ℕ} (hf : Made A f a) (hg : Made A g b) :
    Made A (fun x => f x * g x) (a+b+1) := by
  apply seq2B (unionB hf hg)
  rw [show bit (fun x => f x * g x) = (fun x => bit f x && bit g x) from funext fun x => z2b_mul _ _]
  exact andB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
theorem one (A : Set (Sig N)) : Made A (fun _ => 1) 1 := by
  unfold Made
  rw [show bit (N := N) (fun _ => 1) = (fun _ => true) from funext fun _ => z2b_one]
  exact constB true

abbrev Name (N k : ℕ) := In N → Bool → V k
abbrev Cst (N k r : ℕ) := In N → Bool → Fin (r+1) → V k
abbrev Key (N k : ℕ) := In N → V k
abbrev Gen (N k m : ℕ) := In N → Fin m → V k

def lane (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (key : Key N k) (b : Bool) (n : ℕ) (j : Fin k) :=
  bit fun x => state hk (nm x) (c x) b (key x) n j

theorem trajB (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (key : Key N k) (A : Set (Sig N))
    (hnm : ∀ b j, (bit fun x => nm x b j) ∈ A) (hc : ∀ b n j, (bit fun x => c x b n j) ∈ A)
    (hkey : ∀ j, (bit fun x => key x j) ∈ A) (b : Bool) (n : ℕ) (hn : n ≤ r+1) :
    Build A (Set.range (lane hk nm c key b n)) ((n+1)*(k*50)) := by
  induction n with
  | zero =>
    simp only [zero_add,one_mul]
    refine finSigB _ 50 fun j => ?_
    have h := add (get (hkey (ix hk (j.val+k-start b % k)))) (get (hnm b j))
    exact relaxB h le_rfl Set.subset_union_right (by decide)
  | succ n ih =>
    have prev := ih (by omega)
    have step : Build (A ∪ Set.range (lane hk nm c key b n)) (Set.range (lane hk nm c key b (n+1))) (k*50) := by
      refine finSigB _ 50 fun j => ?_
      let D := A ∪ Set.range (lane hk nm c key b n)
      let z (x : In N) := state hk (nm x) (c x) b (key x) n
      have hz (i : Fin k) : Made D (fun x => z x i) 0 := get (Or.inr ⟨i,rfl⟩)
      have hy (i : Fin k) : Made D (fun x => mix hk b (z x) i) 8 :=
        add (add (hz i) (hz _)) (hz _)
      have hz' := add (add (add (hy j) (mul (add (one D) (hy (ix hk (j.val+1)))) (hy (ix hk (j.val+2)))))
        (get (A := D) (Or.inl (hkey (ix hk (j.val+k-feed b n % k)))))) (get (A := D) (Or.inl (hc b ⟨n,by omega⟩ j)))
      have eq : lane hk nm c key b (n+1) j = bit (fun x => update hk b (key x) n (c x b ⟨n,by omega⟩) (z x) j) := by
        funext x; exact congrArg (fun v : V k => z2b (v j)) (state_step hk (nm x) (c x) b (key x) n (by omega))
      rw [eq]; exact relaxB hz' le_rfl Set.subset_union_right (by decide)
    exact relaxB (seq2B prev step) le_rfl Set.subset_union_right (by simp only [Nat.add_mul,one_mul,le_refl])

abbrev Sample (m : ℕ) := Unit ⊕ (Fin m ⊕ Fin m × Fin m)
def keyAt (rep : Key N k) (gen : Gen N k m) (s : Sample m) : Key N k :=
  match s with
  | .inl _ => rep
  | .inr (.inl i) => fun x => rep x + gen x i
  | .inr (.inr (i,j)) => fun x => rep x + gen x i + gen x j

theorem enumB {I : Type*} [Fintype I] (A : Set (Sig N)) (U : I → Set (Sig N)) (d : ℕ)
    (h : ∀ i, Build A (U i) d) : Build A (⋃ i, U i) (Fintype.card I*d) := by
  classical
  let e := Fintype.equivFin I
  apply relaxB (finB (fun j => U (e.symm j)) d (fun j => h _)) le_rfl _ le_rfl
  intro f hf
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hf
  exact Or.inr (Set.mem_iUnion.mpr ⟨e i,by simpa using hi⟩)

abbrev Ix (m r : ℕ) := Sample m × Bool × Fin (r+2)
def bank (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m) : Set (Sig N) :=
  ⋃ a : Ix m r, Set.range (lane hk nm c (keyAt rep gen a.1) a.2.1 a.2.2.val)

theorem bankB (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (A : Set (Sig N)) (hnm : ∀ b j, (bit fun x => nm x b j) ∈ A)
    (hc : ∀ b n j, (bit fun x => c x b n j) ∈ A) (hr : ∀ j, (bit fun x => rep x j) ∈ A)
    (hg : ∀ i j, (bit fun x => gen x i j) ∈ A) :
    Build A (bank hk nm c rep gen) ((1+(m+m*m))*(2*(r+2))*(k*8+(r+2)*(k*50))) := by
  classical
  unfold bank
  have cardI : Fintype.card (Ix m r) = (1+(m+m*m))*(2*(r+2)) := by simp [Ix,Sample]
  rw [← cardI]
  apply enumB
  rintro ⟨s,b,n⟩
  let key := keyAt rep gen s
  let K := Set.range (fun j => bit fun x => key x j)
  have keys : Build A K (k*8) := by
    apply finSigB
    intro j
    rcases s with _ | i
    · exact relaxB (get (hr j)) le_rfl Set.subset_union_right (by decide)
    · rcases i with i | ⟨i,l⟩
      · exact relaxB (add (get (hr j)) (get (hg i j))) le_rfl Set.subset_union_right (by decide)
      · exact add (add (get (hr j)) (get (hg i j))) (get (hg l j))
  have hh := trajB hk nm c key (A ∪ K) (fun b j => Or.inl (hnm b j))
    (fun b n j => Or.inl (hc b n j)) (fun j => Or.inr ⟨j,rfl⟩) b n (by omega)
  exact relaxB (seq2B keys hh) le_rfl Set.subset_union_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ n.isLt) _)

theorem bankMem (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (s : Sample m) (b : Bool) (n : ℕ) (hn : n ≤ r+1) (j : Fin k) :
    lane hk nm c (keyAt rep gen s) b n j ∈ bank hk nm c rep gen :=
  Set.mem_iUnion.mpr ⟨(s,b,⟨n,by omega⟩),j,rfl⟩

abbrev Watch (k : ℕ) := Bool → ℕ → Fin k → Bool
abbrev CheckIx (k m r : ℕ) := Bool × Fin r × Fin k × Fin m × Fin m
def corner (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (b : Bool) (n : ℕ) (j : Fin k) (s : Sample m) (x : In N) : F :=
  state hk (nm x) (c x) b (keyAt rep gen s x) n j
def delta (u : Sample m → F) (i j : Fin m) := u (.inl ()) + u (.inr (.inl i)) +
  u (.inr (.inl j)) + u (.inr (.inr (i,j)))
def test (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (w : Watch k) (a : CheckIx k m r) (x : In N) :=
  let (b,n,j,i,l) := a
  if w b (n.val+1) j = true ∧ i < l then
    !(z2b (delta (fun s => corner hk nm c rep gen b (n.val+1) j s x) i l)) else true
noncomputable def prefixOK (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (w : Watch k) (x : In N) := (Finset.univ : Finset (CheckIx k m r)).toList.all
      fun a => test hk nm c rep gen w a x

theorem prefix_spec (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (w : Watch k) (x : In N) : prefixOK hk nm c rep gen w x = true ↔
    ∀ b n, 0 < n → n ≤ r → ∀ j, w b n j = true → ∀ i l : Fin m, i < l →
      delta (fun s => corner hk nm c rep gen b n j s x) i l = 0 := by
  simp only [prefixOK,List.all_eq_true,Finset.mem_toList,Finset.mem_univ,forall_const]
  constructor
  · intro h b n hn hr j hw i l hil
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [test,hw,hil,z2b] using h (b,⟨n,by omega⟩,j,i,l)
  · rintro h ⟨b,n,j,i,l⟩
    by_cases h' : w b (n.val+1) j = true ∧ i < l
    · simp [test,h',h b (n.val+1) (by omega) (by omega) j h'.1 i l h'.2,z2b_zero]
    · simp [test,h']

def rows (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (side : Fin t → Bool) (site : Fin t → Fin k) (target : In N → V t) (u : Fin t) (x : In N) : Quad m :=
  let f := fun s => corner hk nm c rep gen (side u) (r+1) (site u) s x
  ⟨delta f, fun i => f (.inl ()) + f (.inr (.inl i)), f (.inl ()) + target x u⟩

theorem deltaB {A : Set (Sig N)} (v : Sample m → Val (N := N))
    (h : ∀ s, bit (v s) ∈ A) (i j : Fin m) : Made A (fun x => delta (fun s => v s x) i j) 12 :=
  add (add (add (get (h _)) (get (h _))) (get (h _))) (get (h _))

def frontCost (k m r t : ℕ) := (1+(m+m*m))*(2*(r+2))*(k*8+(r+2)*(k*50)) +
  (1 + (2*(r*(k*(m*m)))*13 + 2*(r*(k*(m*m))))) + t*(m*(m*12)+m*4+4)

theorem frontB (hk : 0 < k) (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m)
    (w : Watch k) (side : Fin t → Bool) (site : Fin t → Fin k) (target : In N → V t)
    (A : Set (Sig N)) (hnm : ∀ b j, (bit fun x => nm x b j) ∈ A)
    (hc : ∀ b n j, (bit fun x => c x b n j) ∈ A) (hr : ∀ j, (bit fun x => rep x j) ∈ A)
    (hg : ∀ i j, (bit fun x => gen x i j) ∈ A) (ht : ∀ u, (bit fun x => target x u) ∈ A) :
    Build A ({prefixOK hk nm c rep gen w} ∪ ⋃ u, quadSigs (rows hk nm c rep gen side site target u)) (frontCost k m r t) := by
  classical
  let D := A ∪ bank hk nm c rep gen
  have mem (b n j s) (hn : n ≤ r+1) : bit (corner hk nm c rep gen b n j s) ∈ D :=
    Or.inr (bankMem hk nm c rep gen s b n hn j)
  have quads : Build D (⋃ u, quadSigs (rows hk nm c rep gen side site target u)) (t*(m*(m*12)+m*4+4)) := by
    apply finB
    intro u
    let f := corner hk nm c rep gen (side u) (r+1) (site u)
    have hf (s) : bit (f s) ∈ D := mem _ _ _ _ le_rfl
    exact unionB (unionB (fin2SigB _ 12 (fun i j => deltaB f hf i j))
      (finSigB _ 4 (fun i => add (get (hf (.inl ()))) (get (hf (.inr (.inl i)))))))
      (add (get (hf (.inl ()))) (get (A := D) (Or.inl (ht u))))
  let I := CheckIx k m r
  let d := 2*(r*(k*(m*m)))
  have cardI : Fintype.card I = d := by simp [I,CheckIx,d]
  let T := test hk nm c rep gen w
  let L := (Finset.univ : Finset I).toList
  have tests : Build D (⋃ a, {T a}) (d*13) := by
    rw [← cardI]
    apply enumB
    rintro ⟨b,n,j,i,l⟩
    by_cases h : w b (n.val+1) j = true ∧ i < l
    · have q := deltaB (corner hk nm c rep gen b (n.val+1) j) (fun s => mem _ _ _ _ (by omega)) i l
      have hn := seq2B q (notB (A := D ∪ _) (Or.inr rfl))
      rw [show T (b,n,j,i,l) = (fun x => !z2b (delta (fun s => corner hk nm c rep gen b (n.val+1) j s x) i l)) by
        funext x; simp [T,test,h]]
      exact hn
    · rw [show T (b,n,j,i,l) = (fun _ => true) by funext x; simp [T,test,h]]
      exact relaxB (constB true) le_rfl Set.subset_union_right (by decide)
  have allT : Build D {prefixOK hk nm c rep gen w} (1+(d*13+d)) := by
    let B := D ∪ {fun _ => true}
    apply seq2B (constB (A := D) true)
    apply seq2B (relaxB tests (A' := B) Set.subset_union_left Set.subset_union_right le_rfl)
    let xs := L.map T
    have hf : ∀ f ∈ xs, f ∈ B ∪ ⋃ a, {T a} := by
      intro f hf; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hf; exact Or.inr (Set.mem_iUnion.mpr ⟨a,rfl⟩)
    have hh := andListB xs hf (Or.inl (Or.inr rfl))
    rw [show prefixOK hk nm c rep gen w = (fun x => xs.all (fun f => f x)) by
      funext x; simp [xs,L,T,prefixOK,Function.comp_def]]
    exact relaxB hh le_rfl Set.subset_union_right (by simp [xs,L,cardI,d,I,CheckIx])
  exact relaxB (seq2B (bankB hk nm c rep gen A hnm hc hr hg) (unionB allT quads)) le_rfl
    Set.subset_union_right (by simp [frontCost,d,Nat.add_assoc])

theorem frontCost_le (k m r t : ℕ) : frontCost k m r t ≤ 1024*(k+m+r+t+4)^5 := by
  let s := k+m+r+t
  calc
    frontCost k m r t ≤ frontCost s s s s := by unfold frontCost; gcongr <;> dsimp [s] <;> omega
    _ ≤ 1024*(s+4)^5 := by unfold frontCost; ring_nf; omega

end Probe259
end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
abbrev KeyN (k m r t : ℕ) := (m+2+2*(r+1))*k+t
abbrev KeySlot (k m r t : ℕ) := (Fin m × Fin k) ⊕ ((Bool × Fin k) ⊕ ((Bool × Fin (r+1) × Fin k) ⊕ Fin t))
def slotGen {k m r t} (i : Fin m) (j : Fin k) : KeySlot k m r t := Sum.inl (i,j)
def slotName {k m r t} (b : Bool) (j : Fin k) : KeySlot k m r t := Sum.inr (Sum.inl (b,j))
def slotC {k m r t} (b : Bool) (i : Fin (r+1)) (j : Fin k) : KeySlot k m r t := Sum.inr (Sum.inr (Sum.inl (b,i,j)))
def slotTar {k m r t} (i : Fin t) : KeySlot k m r t := Sum.inr (Sum.inr (Sum.inr i))
def keySlots (k m r t : ℕ) : List (KeySlot k m r t) :=
  (List.ofFn fun i => List.ofFn (slotGen i)).flatten ++ List.ofFn (slotName false) ++ List.ofFn (slotName true) ++
    (List.ofFn fun i => List.ofFn (slotC false i)).flatten ++ (List.ofFn fun i => List.ofFn (slotC true i)).flatten ++ List.ofFn slotTar

theorem keySlots_length (k m r t : ℕ) : (keySlots k m r t).length = KeyN k m r t := by
  simp [keySlots, List.length_flatten, KeyN, Function.comp_def, List.ofFn_const]; ring

theorem keySlots_mem {k m r t} (s : KeySlot k m r t) : s ∈ keySlots k m r t := by
  rcases s with ⟨i,j⟩ | (⟨b,j⟩ | (⟨b,i,j⟩ | i))
  · simp [keySlots,slotGen, List.mem_flatten, List.mem_ofFn]
  · cases b <;> simp [keySlots,slotName,List.mem_ofFn]
  · cases b <;> simp [keySlots,slotC,List.mem_flatten,List.mem_ofFn] <;> tauto
  · simp [keySlots,slotTar,List.mem_ofFn]

def slotIx {k m r t} (s : KeySlot k m r t) : Fin (KeyN k m r t) :=
  ⟨(keySlots k m r t).idxOf s, keySlots_length k m r t ▸ List.idxOf_lt_length_of_mem (keySlots_mem s)⟩

def rawKey {k m r t} (x : Fin (KeyN k m r t) → Bool) (s : KeySlot k m r t) : ZMod 2 := b2z (x (slotIx s))

def keyVector {k m r t} (v : KeySlot k m r t → ZMod 2) : Fin (KeyN k m r t) → Bool :=
  fun i => z2b (v ((keySlots k m r t).get ⟨i.val, by rw [keySlots_length]; exact i.isLt⟩))

theorem decode_key {k m r t} (v : KeySlot k m r t → ZMod 2) (s : KeySlot k m r t) : rawKey (keyVector v) s = v s := by
  simp [rawKey,keyVector,slotIx,b2z_z2b,List.get_eq_getElem,List.getElem_idxOf]

def slotVal {k m r t} (gen : Fin m → Fin k → ZMod 2) (name : Bool → Fin k → ZMod 2)
    (c : Bool → Fin (r+1) → Fin k → ZMod 2) (tar : Fin t → ZMod 2) : KeySlot k m r t → ZMod 2
  | .inl (i,j) => gen i j
  | .inr (.inl (b,j)) => name b j
  | .inr (.inr (.inl (b,i,j))) => c b i j
  | .inr (.inr (.inr i)) => tar i

theorem keyVector_packed {k m r t} (gen : Fin m → Fin k → ZMod 2) (name : Bool → Fin k → ZMod 2)
    (c : Bool → Fin (r+1) → Fin k → ZMod 2) (tar : Fin t → ZMod 2) :
    let pack := fun w : Fin k → ZMod 2 => List.ofFn (fun j => decide (w j ≠ 0))
    List.ofFn (keyVector (slotVal gen name c tar)) =
      (List.ofFn (fun i => pack (gen i))).flatten ++ pack (name false) ++ pack (name true) ++
      (List.ofFn (fun i => pack (c false i))).flatten ++ (List.ofFn (fun i => pack (c true i))).flatten ++
      List.ofFn (fun i => decide (tar i ≠ 0)) := by
  intro pack
  let v := slotVal gen name c tar
  have eqmap : List.ofFn (keyVector v) = (keySlots k m r t).map (fun s => z2b (v s)) := by
    apply List.ext_getElem
    · simp [keySlots_length]
    · intro i hi hj; simp [keyVector]
  rw [eqmap]
  simp only [keySlots,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,slotGen,slotName,slotC,slotTar,v,slotVal,pack,z2b]
  rfl

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

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
end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux

variable {N d k : ℕ}

def bankFlag (good : Sig N) (live localOK : Fin d → Sig N) : Sig N := fun x =>
  good x && (List.ofFn (fun i => (fun y => !(live i y) || localOK i y : Sig N))).all (fun a => a x)

lemma bankFlag_true (good : Sig N) (live localOK : Fin d → Sig N) (x : Fin N → Bool) :
    bankFlag good live localOK x = true ↔ good x=true ∧ ∀ i, live i x=true → localOK i x=true := by
  simp only [bankFlag,Bool.and_eq_true,List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  apply and_congr_right'
  apply forall_congr'; intro i
  cases live i x <;> simp

private lemma buildBankFlag {A : Set (Sig N)} (good : Sig N) (live localOK : Fin d → Sig N)
    (ht : (fun _ => true) ∈ A) (hg : good ∈ A) (hl : ∀ i, live i ∈ A) (ho : ∀ i, localOK i ∈ A) :
    Build A {bankFlag good live localOK} (d*2+d+1) := by
  let chk (i : Fin d) : Sig N := fun x => !(live i x) || localOK i x
  have hchk : Build A (Set.range chk) (d*2) := by
    apply finSigB
    intro i
    exact seq2B (notB (hl i)) (orB (Or.inr rfl) (Or.inl (ho i)))
  let combined : Sig N := fun x => (List.ofFn chk).all (fun a => a x)
  have hall : Build (A ∪ Set.range chk) {combined} d := by
    simpa only [List.length_ofFn] using andListB (A := A ∪ Set.range chk) (List.ofFn chk)
      (fun a h => Or.inr (List.mem_ofFn.mp h)) (Or.inl ht)
  exact seq2B (seq2B hchk hall) (andB (Or.inl hg) (Or.inr rfl))

private lemma bankSumOfFn (F : Fin d → (Fin N → Bool) → ℕ) (x : Fin N → Bool) :
    sumListVal (List.ofFn F) x = ∑ i, F i x := by
  induction d with
  | zero => simp [sumListVal]
  | succ d ih => rw [List.ofFn_succ,Fin.sum_univ_succ]; exact congrArg (F 0 x + ·) (ih (fun i => F i.succ))

theorem finishBankB {A : Set (Sig N)} (good : Sig N) (live localOK : Fin d → Sig N)
    (u : Fin d → Fin (k+1) → Sig N) (f : (Fin N → Bool) → Fin d → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hg : good ∈ A) (hl : ∀ i, live i ∈ A) (ho : ∀ i, localOK i ∈ A)
    (hu : ∀ i j, u i j ∈ A)
    (hc : ∀ x, bankFlag good live localOK x=true → ∀ i, live i x=true →
      ∀ j : Fin (k+1), u i j x=(f x i).testBit j.val) :
    Build A ({bankFlag good live localOK} ∪ Set.range (bitsOf (k+1) (fun x =>
      if bankFlag good live localOK x then ∑ i, if live i x then f x i else 0 else 0)))
      (32*(d+1)*(k+2)) := by
  let flag := bankFlag good live localOK
  let S := A ∪ {flag}
  have hflag := buildBankFlag good live localOK htrue hg hl ho
  let en (i : Fin d) : Sig N := fun x => flag x && live i x
  have hEn : Build S (Set.range en) (d*1) := finSigB _ _ (fun i => andB (Or.inr rfl) (Or.inl (hl i)))
  let M (i : Fin d) (x : Fin N → Bool) := if en i x then f x i else 0
  let bit (i : Fin d) := bitsOf (k+1) (M i)
  let B : Set (Sig N) := {a | ∃ i j, bit i j=a}
  have hbits : Build (S ∪ Set.range en) B (d*((k+1)*1)) := by
    apply fin2SigB bit 1
    intro i j
    have hj : bit i j = fun x => en i x && u i j x := by
      funext x
      change (if en i x then f x i else 0).testBit j.val = _
      cases he : en i x with
      | false => simp
      | true =>
        have hh : flag x=true ∧ live i x=true := by simpa [en] using he
        obtain ⟨hflag',hl'⟩ := hh
        simp [hc x hflag' i hl' j]
    rw [hj]; exact andB (Or.inr ⟨i,rfl⟩) (Or.inl (Or.inl (hu i j)))
  let Fs := List.ofFn M
  have hsum : Build ((S ∪ Set.range en) ∪ B) (Set.range (bitsOf (k+1) (sumListVal Fs))) (d*(9*(k+1))) := by
    simpa only [Fs,List.length_ofFn] using sumListB (A := (S ∪ Set.range en) ∪ B) (k+1)
      (Or.inl (Or.inl (Or.inl hfalse))) Fs (by
        intro F hF j; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hF; exact Or.inr ⟨i,j,rfl⟩)
  have hv : sumListVal Fs = fun x => if flag x then ∑ i, if live i x then f x i else 0 else 0 := by
    funext x; rw [show sumListVal Fs x = ∑ i, M i x from bankSumOfFn M x]
    cases he : flag x <;> simp [M,en,he]
  have H := seqB hflag (seq2B hEn (seq2B hbits hsum))
  rw [hv] at H
  exact relaxB H le_rfl Set.subset_union_right (by nlinarith [Nat.zero_le (d*k)])

end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine Probe259

theorem rowB {N k m r t : Nat} (h : Nat) (hk : 0 < k)
    (nm : Name N k) (c : Cst N k r) (rep : Key N k) (gen : Gen N k m) (w : Watch k)
    (side : Fin t → Bool) (site : Fin t → Fin k) (target : In N → V t)
    (A : Set (Sig N)) (hF : (fun _ => false) ∈ A) (hT : (fun _ => true) ∈ A)
    (hnm : ∀ b j, (bit fun x => nm x b j) ∈ A) (hc : ∀ b n j, (bit fun x => c x b n j) ∈ A)
    (hr : ∀ j, (bit fun x => rep x j) ∈ A) (hg : ∀ i j, (bit fun x => gen x i j) ∈ A)
    (ht : ∀ u, (bit fun x => target x u) ∈ A) :
    let Q := fun x i => rows hk nm c rep gen side site target i x
    Build A ({fun x => prefixOK hk nm c rep gen w x && decide ((quadPolarMatrix (Q x)).rank ≤ h)} ∪
      Set.range (fun j x => genericBit h (gen x) (Q x) j))
      (2^30*(k+m+r+t+4)^12*2^(min t h)) := by
  classical
  intro Q
  let p := prefixOK hk nm c rep gen w
  let front := {p} ∪ ⋃ j, quadSigs (fun x => Q x j)
  let B := A ∪ front
  have fr : Build A front (frontCost k m r t) := frontB hk nm c rep gen w side site target A hnm hc hr hg ht
  have qs (j : Fin t) : quadSigs (fun x => Q x j) ⊆ B := fun _ hf => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j,hf⟩))
  let rankFlag : Sig N := fun x => decide ((quadPolarMatrix (Q x)).rank ≤ h)
  have rank : Build B {rankFlag} (2^12*(k+m+r+t+4)^10) :=
    quadPolarRankBoundB k r B h Q (Or.inl hF) (Or.inl hT) qs
  have both : Build (B ∪ {rankFlag}) {fun x => p x && rankFlag x} 1 :=
    andB (Or.inl (Or.inr (Or.inl rfl))) (Or.inr rfl)
  have val (x : In N) (j : Fin t) : (Q x j).Valid :=
    PEqualNP.Outside.L_meta_25940_aux.P25940Sample.sample_valid (gen x) (rep x) (fun key => state hk (nm x) (c x) (side j) key (r+1) (site j)) (target x j)
  have counts := genericBitsB h B gen Q (Or.inl hF) (Or.inl hT) (fun i j => Or.inl (hg i j)) qs val
  have b := seq2B fr (unionB (seq2B rank both) counts)
  apply relaxB b le_rfl Set.subset_union_right
  let d := k+m+r+t+4
  let e := 2^(min t h)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have he : 1 ≤ e := Nat.one_le_two_pow
  have h5 : d^5 ≤ d^12 := Nat.pow_le_pow_right hd (by decide)
  have h10 : d^10 ≤ d^12 := Nat.pow_le_pow_right hd (by decide)
  have h8 : (k+m+t+2)^8 ≤ d^12 := (Nat.pow_le_pow_left (by dsimp [d]; omega) 8).trans (Nat.pow_le_pow_right hd (by decide))
  have hu : d^12 ≤ d^12*e := Nat.le_mul_of_pos_right _ he
  have hfr : frontCost k m r t ≤ 1024*(d^12*e) := (frontCost_le k m r t).trans (Nat.mul_le_mul_left _ (h5.trans hu))
  have hrank := Nat.mul_le_mul_left (2^12) (h10.trans hu)
  have hct : 2^20*(k+m+t+2)^8*e ≤ 2^20*(d^12*e) := by rw [←Nat.mul_assoc]; gcongr
  have hunit : 1 ≤ d^12*e := (Nat.one_le_pow _ _ hd).trans hu
  change frontCost k m r t + (2^12*d^10+1+2^20*(k+m+t+2)^8*2^(min h t)) ≤ 2^30*d^12*e
  rw [Nat.min_comm h t,show 2^(min t h)=e from rfl,Nat.mul_assoc (2^30)]
  omega

end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux.P25940Sem
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine PEqualNP.Outside.L_meta_25940_aux.P25940Sample PEqualNP.Outside.L_meta_25940_aux

def key {m k} (rep : V k) (gen : Fin m → V k) (x : V m) : V k := rep + shift gen x

theorem mem_key_iff {m k} (rep : V k) (gen : Fin m → V k) (w : V k) :
    w ∈ Set.range (key rep gen) ↔ w - rep ∈ Submodule.span F (Set.range gen) := by
  rw [Submodule.mem_span_range_iff_exists_fun F]
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨x, by unfold key shift; abel⟩
  · rintro ⟨x,hx⟩; exact ⟨x, by change rep + (∑ i, x i • gen i) = w; rw [hx]; abel⟩

def probe {k r t} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (side : Fin t → Bool) (site : Fin t → Fin k) (j : Fin t) (w : V k) : F :=
  state hk name c (side j) w (r+1) (site j)

def fullPrefix {m k r} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (watch : Bool → ℕ → Fin k → Bool) :=
  ∀ a b n, n ≤ r → ∀ j, watch b n j = true → ∀ x y,
    state hk name c b a n j + state hk name c b (a+shift gen x) n j +
      state hk name c b (a+shift gen y) n j + state hk name c b (a+shift gen x+shift gen y) n j = 0

theorem quadPolar_eq {m k t} (rep : V k) (gen : Fin m → V k) (f : Fin t → V k → F) (target : Fin t → F) :
    quadPolarMatrix (fun j => sample gen rep (f j) (target j)) = matrix gen rep f target := rfl

theorem local_global {m k r t d} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (live : Fin d → Bool) (rep : Fin d → V k)
    (part : ∀ w, ∃! i, live i = true ∧ w - rep i ∈ Submodule.span F (Set.range gen))
    (watch : Bool → ℕ → Fin k → Bool) (hc : closed hk watch (r+1))
    (side : Fin t → Bool) (site : Fin t → Fin k) (hw : ∀ j, watch (side j) (r+1) (site j) = true)
    (h : ℕ) (target : Fin t → F) :
    let f := probe hk name c side site
    (∀ i, live i = true → Checks hk name c gen (rep i) watch ∧ (matrix gen (rep i) f target).rank ≤ h) ↔
    fullPrefix hk name c gen watch ∧ ∀ a, (matrix gen a f target).rank ≤ h := by
  let I := {i : Fin d // live i = true}
  have cover (a : V k) : ∃ s : I, ∃ u, a = rep s.val + shift gen u := by
    obtain ⟨s,⟨hl,hw⟩,_⟩ := part a
    obtain ⟨u,e⟩ := (mem_key_iff (rep s) gen a).mpr hw
    exact ⟨⟨s,hl⟩,u,e.symm⟩
  have hp : fullPrefix hk name c gen watch ↔ ∀ s : I, Checks hk name c gen (rep s.val) watch :=
    prefix_pair_iff hk name c gen gen rfl (fun s : I => rep s.val) cover watch hc
  constructor
  · intro conditions
    refine ⟨hp.mpr (fun s => (conditions s.val s.property).1),fun a => ?_⟩
    obtain ⟨s,u,rfl⟩ := cover a
    obtain ⟨hs,hr⟩ := conditions s.val s.property
    have eqr := (terminal_sample hk name c gen (rep s.val) watch hc side site hw target hs).2.2 u
    exact eqr.trans_le hr
  · rintro ⟨hg,hr⟩ i hi
    exact ⟨hp.mp hg ⟨i,hi⟩,hr (rep i)⟩

noncomputable def cosetCount {k m t} (rep : V k) (gen : Fin m → V k) (f : Fin t → V k → F) (target : Fin t → F) : ℕ :=
  Nat.card {w : V k // w ∈ Set.range (key rep gen) ∧ ∀ j, f j w = target j}

theorem cosetCount_eq_filter {k m t} (rep : V k) (gen : Fin m → V k) (f : Fin t → V k → F)
    (target : Fin t → F) [DecidablePred (fun w => w - rep ∈ Submodule.span F (Set.range gen) ∧ ∀ j, f j w = target j)] :
    cosetCount rep gen f target = (Finset.univ.filter
      (fun w => w - rep ∈ Submodule.span F (Set.range gen) ∧ ∀ j, f j w = target j)).card := by
  classical
  unfold cosetCount; simp_rw [mem_key_iff]; rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem local_bit {k m r t} (hk : 0 < k) (name : Bool → V k) (c : Bool → Fin (r+1) → V k)
    (gen : Fin m → V k) (rep : V k) (watch : Bool → ℕ → Fin k → Bool) (hc : closed hk watch (r+1))
    (side : Fin t → Bool) (site : Fin t → Fin k) (hw : ∀ j, watch (side j) (r+1) (site j) = true)
    (h : ℕ) (target : Fin t → F) (hs : Checks hk name c gen rep watch)
    (hr : (matrix gen rep (probe hk name c side site) target).rank ≤ h) (o : Fin (k+1)) :
    let f := probe hk name c side site
    genericBit h gen (fun j => sample gen rep (f j) (target j)) o = (cosetCount rep gen f target).testBit o.val := by
  let f := probe hk name c side site
  let Q := fun j => sample gen rep (f j) (target j)
  have ev := (terminal_sample hk name c gen rep watch hc side site hw target hs).1
  have eq0 (a b : F) : a+b=0 ↔ a=b := by decide +revert
  apply genericBit_correct h rep gen Q (fun w j => f j w = target j) (fun j => sample_valid ..) _ hr o
  intro j a
  change (sample gen rep (f j) (target j)).eval a = 0 ↔ f j (rep+shift gen a) = target j
  have he : (sample gen rep (f j) (target j)).eval a = f j (rep+shift gen a) + target j := ev j a
  rw [he,eq0]

end PEqualNP.Outside.L_meta_25940_aux.P25940Sem

namespace PEqualNP.Outside.L_meta_25940_aux
noncomputable section

theorem bankTotal {α : Type*} [Fintype α] {d : ℕ} (live : Fin d → Bool)
    (cell : Fin d → α → Prop) (P : α → Prop) [DecidablePred P]
    (cover : ∀ w, ∃! i, live i = true ∧ cell i w) :
    (∑ i, if live i then Nat.card {w : α // cell i w ∧ P w} else 0) = (Finset.univ.filter P).card := by
  classical
  let T (i : Fin d) : Finset α := Finset.univ.filter (fun w => live i = true ∧ cell i w ∧ P w)
  have cards (i : Fin d) : (if live i then Nat.card {w : α // cell i w ∧ P w} else 0) = (T i).card := by
    cases hl : live i <;> simp [T,hl,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have un : Finset.univ.biUnion T = Finset.univ.filter P := by
    ext w
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,T]
    constructor
    · rintro ⟨_,_,_,hp⟩; exact hp
    · intro hp; obtain ⟨i,⟨hl,hc⟩,_⟩ := cover w; exact ⟨i,hl,hc,hp⟩
  have dis : ((Finset.univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint T := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr (fun w hi hj => ?_)
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    obtain ⟨s,_,hs⟩ := cover w
    exact hij ((hs i ⟨ai.1,ai.2.1⟩).trans (hs j ⟨aj.1,aj.2.1⟩).symm)
  calc
    _ = ∑ i, (T i).card := Finset.sum_congr rfl (fun i _ => cards i)
    _ = _ := (Finset.card_biUnion dis).symm.trans (congrArg Finset.card un)
end
end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open Probe259 (In)
variable {k m r t p h N d : ℕ}

abbrev Raw (k m r t : ℕ) := In (KeyN k m r t)
def inputGen (x : Raw k m r t) (i : Fin m) (j : Fin k) := rawKey (k:=k) (m:=m) (r:=r) (t:=t) x (slotGen i j)
def inputNm (x : Raw k m r t) (b : Bool) (j : Fin k) := rawKey (k:=k) (m:=m) (r:=r) (t:=t) x (slotName b j)
def inputC (x : Raw k m r t) (b : Bool) (n : Fin (r+1)) (j : Fin k) := rawKey (k:=k) (m:=m) (r:=r) (t:=t) x (slotC b n j)
def inputTar (x : Raw k m r t) (i : Fin t) := rawKey (k:=k) (m:=m) (r:=r) (t:=t) x (slotTar i)

def allProj (N : ℕ) : Set (Sig N) := Set.range fun i : Fin N => fun x : In N => x i
def allBase (N : ℕ) : Set (Sig N) := allProj N ∪ ({fun _ => false} ∪ {fun _ => true})
theorem input_mem (s : KeySlot k m r t) : (fun x => z2b (rawKey x s)) ∈ allBase (KeyN k m r t) :=
  Or.inl ⟨slotIx s,funext fun x => (z2b_b2z (x (slotIx s))).symm⟩

def joinBank (good : Sig N) (live : Fin d → Sig N) (rep : Fin d → In N → PEqualNP.Outside.L_meta_25940_aux.P25940Affine.V k) : Set (Sig N) :=
  {good} ∪ Set.range live ∪ {f | ∃ i j, (fun x => z2b (rep i x j)) = f}
def joinRow (ok : Sig N) (u : Fin (k+1) → Sig N) : Set (Sig N) := {ok} ∪ Set.range u

theorem joinedCircuit (good : Sig N) (live ok : Fin d → Sig N) (rep : Fin d → In N → PEqualNP.Outside.L_meta_25940_aux.P25940Affine.V k)
    (u : Fin d → Fin (k+1) → Sig N) (f : In N → Fin d → ℕ) (cb cr : ℕ)
    (hb : Build (allBase N) (joinBank good live rep) cb)
    (hr : ∀ i, Build (allBase N ∪ joinBank good live rep) (joinRow (ok i) (u i)) cr)
    (hc : ∀ x, bankFlag good live ok x = true → ∀ i, live i x = true → ∀ j, u i j x = (f x i).testBit j.val) :
    ∃ (C : Circuit) (flag : Fin (N+C.size)) (ans : Fin (k+1) → Fin (N+C.size)), FanInTwo C ∧ ReadsBack N C ∧
      C.output = flag.val ∧ C.size ≤ 2+(cb+(d*cr+32*(d+1)*(k+2))) ∧
      (∀ x, (C.wires (List.ofFn x)).getD flag.val false = bankFlag good live ok x) ∧
      ∀ j x, (C.wires (List.ofFn x)).getD (ans j).val false =
        (if bankFlag good live ok x then ∑ i, if live i x then f x i else 0 else 0).testBit j.val := by
  let A := allBase N
  let B := A ∪ joinBank good live rep
  let R := ⋃ i, joinRow (ok i) (u i)
  have init : Build (allProj N) A 2 := extB (unionB (constB false) (constB true))
  have rows : Build B R (d*cr) := finB _ cr hr
  have fin := finishBankB (A:=B ∪ R) good live ok u f (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
    (Or.inl (Or.inl (Or.inr (Or.inr rfl)))) (Or.inl (Or.inr (Or.inl (Or.inl rfl))))
    (fun i => Or.inl (Or.inr (Or.inl (Or.inr ⟨i,rfl⟩))))
    (fun i => Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩))
    (fun i j => Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr ⟨j,rfl⟩⟩)) hc
  simpa only [Nat.zero_add,bitsOf] using finishFlagBits (startSched N) (transB init (seq2B hb (seq2B rows fin)))

theorem joinedCost (k m r t p h : ℕ) :
    2 + (128*(k+m+4)^5*2^min k p + (2^min k p*(2^30*(k+m+r+t+4)^12*2^min t h) +
      32*(2^min k p+1)*(k+2))) ≤ 2^40*(k+m+r+t+4)^14*2^(min k p+min t h) := by
  let s := k+m+r+t+4
  let D := 2^min k p
  let H := 2^min t h
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hd : 1 ≤ D := Nat.one_le_two_pow
  have hh : 1 ≤ H := Nat.one_le_two_pow
  have hp (n : ℕ) (hn : n ≤ 14) : s^n ≤ s^14 := Nat.pow_le_pow_right hs hn
  let M := s^14 * D * H
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by dsimp [M]; positivity)
  have ha : (k+m+4)^5 * D ≤ M := by
    calc
      _ ≤ s^5 * D := by gcongr; dsimp [s]; omega
      _ ≤ s^14 * D := Nat.mul_le_mul_right _ (hp 5 (by decide))
      _ ≤ _ := Nat.le_mul_of_pos_right _ hh
  have hb : s^12 * D * H ≤ M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hp 12 (by decide)))
  have hc : (D+1)*(k+2) ≤ 2*M := by
    have hks : k+2 ≤ s^14 := (show k+2 ≤ s by dsimp [s]; omega).trans (by simpa using hp 1 (by decide))
    calc
      _ ≤ (2*D)*(s^14) := by gcongr; omega
      _ = 2*(s^14*D) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hh)
  rw [pow_add]
  change 2 + (128*(k+m+4)^5*D + (D*(2^30*s^12*H)+32*(D+1)*(k+2))) ≤ 2^40*s^14*(D*H)
  rw [show 2^40*s^14*(D*H) = 2^40*M by dsimp only [M]; ac_rfl,
    show D*(2^30*s^12*H) = 2^30*(s^12*D*H) by ac_rfl,
    Nat.mul_assoc 128, Nat.mul_assoc 32]
  norm_num at *; omega

noncomputable section
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine
abbrev allRep (i : (Fin (2^min k p))) (x : Raw k m r t) := bankRep p ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x) i
abbrev allLive (i : (Fin (2^min k p))) (x : Raw k m r t) := bankLive p ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x) i
abbrev allGood (x : Raw k m r t) := bankGood p ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x)
def allQ (hk : 0 < k) (side : Fin t → Bool) (site : Fin t → Fin k) (i : (Fin (2^min k p))) (x : Raw k m r t) (u : Fin t) :=
  Probe259.rows hk (inputNm (k:=k) (m:=m) (r:=r) (t:=t)) (inputC (k:=k) (m:=m) (r:=r) (t:=t)) ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i) (inputGen (k:=k) (m:=m) (r:=r) (t:=t)) side site (inputTar (k:=k) (m:=m) (r:=r) (t:=t)) u x
noncomputable def allOK (hk : 0 < k) (w : Probe259.Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (i : (Fin (2^min k p))) (x : Raw k m r t) :=
  Probe259.prefixOK hk (inputNm (k:=k) (m:=m) (r:=r) (t:=t)) (inputC (k:=k) (m:=m) (r:=r) (t:=t)) ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i) (inputGen (k:=k) (m:=m) (r:=r) (t:=t)) w x && decide ((quadPolarMatrix (allQ (m:=m) (r:=r) (p:=p) hk side site i x)).rank ≤ h)
noncomputable def allFlag (hk : 0 < k) (w : Probe259.Watch k) (side : Fin t → Bool) (site : Fin t → Fin k) :
    Sig (KeyN k m r t) :=
  bankFlag (allGood (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) (allLive (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) (allOK (p:=p) (h:=h) (m:=m) (r:=r) hk w side site)
noncomputable def allU (hk : 0 < k) (side : Fin t → Bool) (site : Fin t → Fin k) (i : (Fin (2^min k p))) (o : Fin (k+1)) (x : Raw k m r t) :=
  genericBit h ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x) (allQ (m:=m) (r:=r) (p:=p) hk side site i x) o
noncomputable def localF (hk : 0 < k) (side : Fin t → Bool) (site : Fin t → Fin k) (x : Raw k m r t) (i : (Fin (2^min k p))) :=
  PEqualNP.Outside.L_meta_25940_aux.P25940Sem.cosetCount ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i x) ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x) (PEqualNP.Outside.L_meta_25940_aux.P25940Sem.probe hk ((inputNm (k:=k) (m:=m) (r:=r) (t:=t)) x) ((inputC (k:=k) (m:=m) (r:=r) (t:=t)) x) side site) ((inputTar (k:=k) (m:=m) (r:=r) (t:=t)) x)
def AllOut (hk : 0 < k) (w : Probe259.Watch k) (side : Fin t → Bool) (site : Fin t → Fin k) : Prop :=
  ∃ (C : Circuit) (flag : Fin (KeyN k m r t+C.size)) (ans : Fin (k+1) → Fin (KeyN k m r t+C.size)),
    FanInTwo C ∧ ReadsBack (KeyN k m r t) C ∧ C.output = flag.val ∧
    C.size ≤ 2^40*(k+m+r+t+4)^14*2^(min k p+min t h) ∧
    (∀ x, (C.wires (List.ofFn x)).getD flag.val false = allFlag (m:=m) (r:=r) (p:=p) (h:=h) hk w side site x) ∧
    ∀ j x, (C.wires (List.ofFn x)).getD (ans j).val false =
      (if allFlag (m:=m) (r:=r) (p:=p) (h:=h) hk w side site x then
        ∑ i, if (allLive (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i x then localF (m:=m) (r:=r) (p:=p) hk side site x i else 0 else 0).testBit j.val

variable (p h)
theorem allCircuitOfBits (hk : 0 < k) (w : Probe259.Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (hc : ∀ x, allFlag (m:=m) (r:=r) (p:=p) (h:=h) hk w side site x = true → ∀ i, (allLive (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i x = true → ∀ j,
      allU (m:=m) (r:=r) (p:=p) (h:=h) hk side site i j x = (localF (m:=m) (r:=r) (p:=p) hk side site x i).testBit j.val) :
    AllOut (m:=m) (r:=r) (p:=p) (h:=h) hk w side site := by
  let A := allBase (KeyN k m r t)
  let B := A ∪ joinBank (allGood (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) (allLive (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) (allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p))
  have hF : (fun _ => false) ∈ A := Or.inr (Or.inl rfl)
  have hT : (fun _ => true) ∈ A := Or.inr (Or.inr rfl)
  have bank := bankB A hF hT p (inputGen (k:=k) (m:=m) (r:=r) (t:=t)) (fun i j => input_mem (slotGen i j))
  have row (i : (Fin (2^min k p))) := rowB h hk (inputNm (k:=k) (m:=m) (r:=r) (t:=t)) (inputC (k:=k) (m:=m) (r:=r) (t:=t)) ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i) (inputGen (k:=k) (m:=m) (r:=r) (t:=t)) w side site (inputTar (k:=k) (m:=m) (r:=r) (t:=t)) B (Or.inl hF) (Or.inl hT)
    (fun b j => Or.inl (input_mem (slotName b j))) (fun b n j => Or.inl (input_mem (slotC b n j)))
    (fun j => Or.inr (Or.inr ⟨i,j,rfl⟩)) (fun i j => Or.inl (input_mem (slotGen i j)))
    (fun u => Or.inl (input_mem (slotTar u)))
  obtain ⟨C,flag,ans,hft,hb,ho,hs,hfl,ha⟩ := joinedCircuit (allGood (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) (allLive (k:=k) (m:=m) (r:=r) (t:=t) (p:=p))
    (allOK (m:=m) (r:=r) (p:=p) (h:=h) hk w side site) (allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p))
    (allU (m:=m) (r:=r) (p:=p) (h:=h) hk side site) (localF (m:=m) (r:=r) (p:=p) hk side site)
    _ _ bank row hc
  exact ⟨C,flag,ans,hft,hb,ho,hs.trans (joinedCost k m r t p h),hfl,ha⟩

theorem allCircuit (hk : 0 < k) (w : Probe259.Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (hc : closed hk w (r+1)) (hw : ∀ j, w (side j) (r+1) (site j) = true) :
    AllOut (m:=m) (r:=r) (p:=p) (h:=h) hk w side site := by
  apply allCircuitOfBits
  intro x hx i hi o
  have conditions := ((bankFlag_true _ _ _ x).mp hx).2 i hi
  change (_ && _) = true at conditions
  simp only [Bool.and_eq_true] at conditions
  obtain ⟨hf,hr⟩ := conditions
  exact PEqualNP.Outside.L_meta_25940_aux.P25940Sem.local_bit hk ((inputNm (k:=k) (m:=m) (r:=r) (t:=t)) x) ((inputC (k:=k) (m:=m) (r:=r) (t:=t)) x) ((inputGen (k:=k) (m:=m) (r:=r) (t:=t)) x) ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i x) w hc side site hw h ((inputTar (k:=k) (m:=m) (r:=r) (t:=t)) x)
    ((Probe259.prefix_spec hk (inputNm (k:=k) (m:=m) (r:=r) (t:=t)) (inputC (k:=k) (m:=m) (r:=r) (t:=t)) ((allRep (k:=k) (m:=m) (r:=r) (t:=t) (p:=p)) i) (inputGen (k:=k) (m:=m) (r:=r) (t:=t)) w x).mp hf) (of_decide_eq_true hr) o
end

end PEqualNP.Outside.L_meta_25940_aux

namespace PEqualNP.Outside.L_meta_25940_aux
open PEqualNP.Outside.L_meta_25940_aux.P25940Affine PEqualNP.Outside.L_meta_25940_aux.P25940Sem PEqualNP.Outside.L_meta_25940_aux.P25940Sample Probe259
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
noncomputable section
variable {k m r t : ℕ}

def dataGood (p h : ℕ) (hk : 0 < k) (w : Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (gen : Fin m → V k) (nm : Bool → V k) (c : Bool → Fin (r+1) → V k) (tar : V t) : Prop :=
  k - Module.finrank F (Submodule.span F (Set.range gen)) ≤ p ∧
  fullPrefix hk nm c gen w ∧ ∀ a, (matrix gen a (probe hk nm c side site) tar).rank ≤ h

def dataCount (hk : 0 < k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (nm : Bool → V k) (c : Bool → Fin (r+1) → V k) (tar : V t) : ℕ :=
  (Finset.univ.filter fun a => ∀ i, probe hk nm c side site i a = tar i).card

theorem keyLocalOK (p h : ℕ) (hk : 0 < k) (w : Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (i : Fin (2^min k p)) (x : Raw k m r t) :
    allOK (p:=p) (h:=h) hk w side site i x = true ↔
    Checks hk (inputNm x) (inputC x) (inputGen x) (bankRep p (inputGen x) i) w ∧
      (matrix (inputGen x) (bankRep p (inputGen x) i) (probe hk (inputNm x) (inputC x) side site) (inputTar x)).rank ≤ h := by
  change (_ && decide _) = true ↔ _
  rw [Bool.and_eq_true,decide_eq_true_eq]
  exact and_congr (prefix_spec hk inputNm inputC (fun y => bankRep p (inputGen y) i) inputGen w x) Iff.rfl

theorem allFlag_spec (p h : ℕ) (hk : 0 < k) (w : Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (hc : closed hk w (r+1)) (hw : ∀ i, w (side i) (r+1) (site i) = true) (x : Raw k m r t) :
    allFlag (p:=p) (h:=h) hk w side site x = true ↔ dataGood p h hk w side site (inputGen x) (inputNm x) (inputC x) (inputTar x) := by
  rw [allFlag,bankFlag_true]; unfold dataGood
  rw [← bankGood_iff]
  apply and_congr_right; intro hg
  simp only [keyLocalOK]
  exact local_global hk (inputNm x) (inputC x) (inputGen x) (bankLive p (inputGen x)) (bankRep p (inputGen x)) (bank_partition p (inputGen x) hg) w hc side site hw h (inputTar x)

theorem allCount_spec (p : ℕ) (hk : 0 < k) (side : Fin t → Bool) (site : Fin t → Fin k) (x : Raw k m r t)
    (hg : bankGood p (inputGen x) = true) :
    (∑ i, if bankLive p (inputGen x) i then localF (p:=p) hk side site x i else 0) =
    dataCount hk side site (inputNm x) (inputC x) (inputTar x) := by
  apply bankTotal (bankLive p (inputGen x)) (fun i a => a ∈ Set.range (PEqualNP.Outside.L_meta_25940_aux.P25940Sem.key (bankRep p (inputGen x) i) (inputGen x))) (fun a => ∀ j, probe hk (inputNm x) (inputC x) side site j a = inputTar x j)
  simp only [mem_key_iff]
  exact bank_partition p (inputGen x) hg

theorem circuitRawSpec (p h : ℕ) (hk : 0 < k) (w : Watch k) (side : Fin t → Bool) (site : Fin t → Fin k)
    (hc : closed hk w (r+1)) (hw : ∀ i, w (side i) (r+1) (site i) = true) :
    let N := KeyN k m r t
    ∃ (C : Circuit) (flag : Fin (N+C.size)) (ans : Fin (k+1) → Fin (N+C.size)),
      FanInTwo C ∧ ReadsBack N C ∧ C.output = flag.val ∧ C.size ≤ 2^40*(k+m+r+t+4)^14*2^(min k p+min t h) ∧
      ∀ x : Raw k m r t, let get := fun i : Fin (N+C.size) => (C.wires (List.ofFn x)).getD i.val false
        (get flag = true ↔ dataGood p h hk w side site (inputGen x) (inputNm x) (inputC x) (inputTar x)) ∧
        ∀ j, get (ans j) = (if get flag then dataCount hk side site (inputNm x) (inputC x) (inputTar x) else 0).testBit j.val := by
  obtain ⟨C,flag,ans,hf,hb,ho,hcst,hflag,hans⟩ := allCircuit (m:=m) p h hk w side site hc hw
  refine ⟨C,flag,ans,hf,hb,ho,hcst,fun x => ?_⟩
  dsimp only
  simp only [hflag x]
  refine ⟨allFlag_spec p h hk w side site hc hw x, fun j => ?_⟩
  rw [hans j x]
  by_cases hh : allFlag (p:=p) (h:=h) hk w side site x = true
  · simpa only [ite_eq_left hh,allLive] using congrArg (fun z : ℕ => z.testBit j.val) (allCount_spec p hk side site x ((bankFlag_true _ _ _ x).1 hh).1)
  · simp only [ite_eq_right hh]
end
end PEqualNP.Outside.L_meta_25940_aux

open PEqualNP.Outside.L_meta_25940_aux in
theorem PEqualNP.Outside.L_meta_25940 : (∀ (k m r t p h : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let E := Fin m → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-s % k))
  let gap := fun (b : Bool) => if b then 2 else 1
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let closed := fun (N : Nat) (watch : Bool → Nat → Fin k → Bool) =>
    ∀ (b : Bool) (t : Nat), t < N → ∀ j : Fin k, watch b (t+1) j = true →
      ∀ e : Fin 3, let i := ix (j.val+e.val)
        watch b t i = true ∧ watch b t (ix (i.val+gap b)) = true ∧
        watch b t (ix (i.val+k-gap b % k)) = true
  ∀ (watch : Bool → Nat → Fin k → Bool) (side : Fin t → Bool) (site : Fin t → Fin k),
    closed (r+1) watch → (∀ i, watch (side i) (r+1) (site i) = true) →
    let inputs := (m+2+2*(r+1))*k+t
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+C.size))
      (ans : Fin (k+1) → Fin (inputs+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
      C.output = flag.val ∧
      C.size ≤ 2^40*(k+m+r+t+4)^14*2^(min k p + min t h) ∧
      ∀ (gen : Fin m → W) (name : Bool → W) (c : Bool → Fin (r+1) → W) (target : Fin t → F),
        let state := fun (b : Bool) (key : W) (n : Nat) =>
          ((List.finRange (r+1)).take n).foldl (fun z tick =>
            let y := fun i : Fin k =>
              z i + z (ix (i.val+gap b)) + z (ix (i.val+k-gap b % k))
            fun j : Fin k => y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
              rot (feed b tick.val) key j + c b tick j) (rot (start b) key + name b)
        let shift := fun a : E => ∑ i : Fin m, a i • gen i
        let probe := fun (key : W) (i : Fin t) => state (side i) key (r+1) (site i)
        let polar := fun (a : W) => (fun (i : Fin t) (jl : Fin m × Fin m) =>
          probe a i + probe (a+gen jl.1) i + probe (a+gen jl.2) i +
            probe (a+gen jl.1+gen jl.2) i : Matrix (Fin t) (Fin m × Fin m) F)
        let good := k - Module.finrank F (Submodule.span F (Set.range gen)) ≤ p ∧
          (∀ (a : W) (b : Bool) (n : Nat), n ≤ r → ∀ j : Fin k, watch b n j = true →
            ∀ x y : E, state b a n j + state b (a+shift x) n j + state b (a+shift y) n j +
              state b (a+shift x+shift y) n j = 0) ∧
          (∀ a : W, Matrix.rank (polar a) ≤ h)
        let pack := fun w : W => List.ofFn (fun j : Fin k => decide (w j ≠ 0))
        let bits := (List.ofFn (fun i => pack (gen i))).flatten ++ pack (name false) ++
          pack (name true) ++ (List.ofFn (fun i => pack (c false i))).flatten ++
          (List.ofFn (fun i => pack (c true i))).flatten ++
          List.ofFn (fun i : Fin t => decide (target i ≠ 0))
        let wire := fun i : Fin (inputs+C.size) => (C.wires bits).getD i.val false
        let count := ((Finset.univ : Finset W).filter (fun key => ∀ i, probe key i = target i)).card
        (wire flag = true ↔ good) ∧
          (∀ i : Fin (k+1), wire (ans i) = ((if wire flag then count else 0).testBit i.val))) := by
  intro k m r t p h hk F W E ix rot gap start feed closed watch side site hc hw inputs
  obtain ⟨C,flag,ans,hf,hr,ho,hsize,H⟩ := circuitRawSpec (m:=m) p h hk watch side site hc hw
  refine ⟨C,flag,ans,hf,hr,ho,hsize,?_⟩
  intro gen nm c tar
  let x := keyVector (slotVal gen nm c tar)
  have hgen : inputGen x = gen := by funext i j; exact decode_key (slotVal gen nm c tar) (slotGen i j)
  have hnm : inputNm x = nm := by funext b j; exact decode_key (slotVal gen nm c tar) (slotName b j)
  have hcst : inputC x = c := by funext b n j; exact decode_key (slotVal gen nm c tar) (slotC b n j)
  have htar : inputTar x = tar := by funext i; exact decode_key (slotVal gen nm c tar) (slotTar i)
  have out := H x
  dsimp only at out ⊢
  rw [hgen,hnm,hcst,htar] at out
  rw [← keyVector_packed gen nm c tar]
  exact out
