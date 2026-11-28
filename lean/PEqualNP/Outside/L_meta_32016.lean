import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32016

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

-- The gate scheduling and ripple adder adapt L-meta-25940.
abbrev Sig (N : ℕ) := (Fin N → Bool) → Bool

def Scheduled (N : ℕ) (k : ℕ) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack N ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < N + k ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

lemma wireLength (C : Circuit) (w : List Bool) :
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

lemma startSched (N : ℕ) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma realizeDeps {N k : ℕ} {S : Set (Sig N)} {gs : List Gate}
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

lemma pushSched {N k : ℕ} {S : Set (Sig N)}
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

def Build {N : ℕ} (A B : Set (Sig N)) (b : ℕ) : Prop :=
  Nonempty (∀ {k : ℕ} {S : Set (Sig N)}, Scheduled N k S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B))

lemma Build.run {N b : ℕ} {A B : Set (Sig N)} (h : Build A B b)
    {k : ℕ} {S : Set (Sig N)} (hs : Scheduled N k S) (ha : A ⊆ S) :
    ∃ c ≤ b, Scheduled N (k + c) (S ∪ B) := by
  obtain ⟨hh⟩ := h
  exact hh hs ha

lemma idleB {N : ℕ} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

lemma relaxB {N : ℕ} {A A' B B' : Set (Sig N)} {b b' : ℕ}
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

lemma seqB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

lemma seq2B {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

lemma gateB {N : ℕ} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩⟩

lemma constB {N : ℕ} {A : Set (Sig N)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

lemma notB {N : ℕ} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

lemma andB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma orB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

lemma xorB {N : ℕ} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
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

lemma listB {N : ℕ} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : ℕ)
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

lemma finB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : ℕ)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  refine relaxB hl le_rfl ?_ (by simp)
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨List.mem_finRange i, hfi⟩⟩)

lemma finSigB {N n : ℕ} {A : Set (Sig N)} (F : Fin n → Sig N) (c : ℕ)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_range.mp hf with ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

lemma unionB {N : ℕ} {A B C : Set (Sig N)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

lemma andListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
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

lemma orListB {N : ℕ} {A : Set (Sig N)} (xs : List (Sig N))
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

def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

lemma fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
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

lemma testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

lemma mod_two_pow_succ_eq (a j : ℕ) :
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

lemma rippleCarry_spec (a b : ℕ) :
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

lemma rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
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

lemma sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl

def sumListVal {N : ℕ} : List ((Fin N → Bool) → ℕ) → (Fin N → Bool) → ℕ
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

lemma sumListB {N : ℕ} {A : Set (Sig N)} (L : ℕ)
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

def z2b (x : ZMod 2) : Bool := decide (x ≠ 0)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

lemma b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by
  rcases z2_cases x with rfl | rfl <;> rfl

lemma z2b_zero : z2b 0 = false := by decide

lemma z2b_one : z2b 1 = true := by decide

lemma z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> rfl

lemma z2b_mul (x y : ZMod 2) : z2b (x * y) = (z2b x && z2b y) := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> rfl

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> rfl

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases z2_cases x with rfl | rfl <;> rfl

-- The natural word bit identities adapt L-meta-29717.
private def rot (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word j : ℕ) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

private def step (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

private lemma rot_lt (k s word : ℕ) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma xor_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

private lemma testBit_rot {k s word b : ℕ} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private lemma testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

private lemma testBit_step_all (k word b : ℕ) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

private lemma testBit_step {k word b : ℕ} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

private lemma step_lt (k word : ℕ) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]


abbrev F := ZMod 2

abbrev Word (k : ℕ) := Fin k → F

lemma word_add_self {k : ℕ} (w : Word k) : w + w = 0 :=
  funext fun i => z2_add_self (w i)

lemma word_neg_self {k : ℕ} (w : Word k) : -w = w := by
  rw [← add_right_inj w, add_neg_cancel, word_add_self]

def wordOfNat (k n : ℕ) : Word k := fun i => b2z (n.testBit i.val)

lemma wordOfNat_zero (k : ℕ) : wordOfNat k 0 = 0 := by
  funext i
  simp [wordOfNat, b2z]

lemma wordOfNat_xor (k a b : ℕ) : wordOfNat k (a ^^^ b) = wordOfNat k a + wordOfNat k b := by
  funext i
  simp only [wordOfNat, Nat.testBit_xor, b2z_xor, Pi.add_apply]

lemma wordOfNat_and (k a b : ℕ) (i : Fin k) :
    wordOfNat k (a &&& b) i = wordOfNat k a i * wordOfNat k b i := by
  simp only [wordOfNat, Nat.testBit_and, b2z_and]

lemma wordOfNat_eq_iff {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    wordOfNat k a = wordOfNat k b ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => congrArg _ h⟩
  by_cases hi : i < k
  · simpa only [wordOfNat, z2b_b2z] using congrArg z2b (congrFun h (⟨i, hi⟩ : Fin k))
  · have hp : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

noncomputable def wordEquiv (k : ℕ) : Fin (2 ^ k) ≃ Word k :=
  Equiv.ofBijective (fun w => wordOfNat k w.val) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ((wordOfNat_eq_iff a.isLt b.isLt).mp hab), ?_⟩
    simp [Fintype.card_fun])

lemma wordOfNat_wordEquiv_symm {k : ℕ} (w : Word k) :
    wordOfNat k ((wordEquiv k).symm w).val = w :=
  (wordEquiv k).apply_symm_apply w

def idx {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ hk⟩

lemma idx_val {k : ℕ} (hk : 0 < k) (i : Fin k) : idx hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

lemma idx_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    idx hk ((idx hk a).val + b) = idx hk (a + b) :=
  Fin.ext (by simp [idx, Nat.mod_add_mod])

def rotIndex {k : ℕ} (hk : 0 < k) (s : ℕ) (i : Fin k) : Fin k :=
  idx hk (i.val + (k - s % k))

def rotW {k : ℕ} (hk : 0 < k) (s : ℕ) : Word k →ₗ[F] Word k where
  toFun w i := w (rotIndex hk s i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma rotW_apply {k : ℕ} (hk : 0 < k) (s : ℕ) (w : Word k) (i : Fin k) :
    rotW hk s w i = w (rotIndex hk s i) := rfl

lemma rotW_comm {k : ℕ} (hk : 0 < k) (s t : ℕ) (w : Word k) :
    rotW hk s (rotW hk t w) = rotW hk t (rotW hk s w) := by
  funext i
  simp only [rotW_apply, rotIndex]
  rw [idx_add, idx_add]
  congr 2
  omega

lemma wordOfNat_rot {k s n : ℕ} (hk : 0 < k) (hn : n < 2 ^ k) :
    wordOfNat k (rot k s n) = rotW hk s (wordOfNat k n) := by
  funext i
  have hs := Nat.mod_lt s hk
  simp only [wordOfNat, rotW_apply, rotIndex, idx, testBit_rot hn i.isLt]
  rw [show i.val + k - s % k = i.val + (k - s % k) by omega]

def maskW {k : ℕ} (mask : Word k) : Word k →ₗ[F] Word k where
  toFun w i := w i * mask i
  map_add' x y := by funext i; simp only [Pi.add_apply]; ring
  map_smul' a x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma wordOfNat_mask {k a b : ℕ} :
    wordOfNat k (a &&& b) = maskW (wordOfNat k b) (wordOfNat k a) :=
  funext fun i => wordOfNat_and k a b i

lemma mask_lt {k : ℕ} (a : ℕ) {b : ℕ} (hb : b < 2 ^ k) : a &&& b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hp : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  simp [Nat.testBit_and, Nat.testBit_lt_two_pow (hb.trans_le hp)]

def mixW {k : ℕ} (hk : 0 < k) (g : ℕ) : Word k →ₗ[F] Word k :=
  LinearMap.id + rotW hk g + rotW hk (k - g)

lemma mixW_apply {k : ℕ} (hk : 0 < k) (g : ℕ) (w : Word k) (i : Fin k) :
    mixW hk g w i = w i + rotW hk g w i + rotW hk (k - g) w i := rfl

lemma mixW_rotW {k : ℕ} (hk : 0 < k) (g s : ℕ) (w : Word k) :
    mixW hk g (rotW hk s w) = rotW hk s (mixW hk g w) := by
  change rotW hk s w + rotW hk g (rotW hk s w) + rotW hk (k-g) (rotW hk s w) = _
  rw [rotW_comm hk g s, rotW_comm hk (k-g) s]
  simp only [mixW, LinearMap.add_apply, LinearMap.id_apply, map_add]

lemma wordOfNat_mix {k w : ℕ} (hk : 0 < k) (hw : w < 2 ^ k) (g : ℕ) :
    wordOfNat k (w ^^^ rot k g w ^^^ rot k (k - g) w) =
      mixW hk g (wordOfNat k w) := by
  simp only [mixW, LinearMap.add_apply, LinearMap.id_apply, wordOfNat_xor, wordOfNat_rot hk hw]

lemma mix_lt {k w : ℕ} (hw : w < 2 ^ k) (g : ℕ) :
    w ^^^ rot k g w ^^^ rot k (k - g) w < 2 ^ k :=
  xor_lt (xor_lt hw (rot_lt k g w)) (rot_lt k _ w)

def chiW {k : ℕ} (hk : 0 < k) (w : Word k) : Word k :=
  fun i => w i + (1 + w (idx hk (i.val + 1))) * w (idx hk (i.val + 2))

lemma b2z_not (b : Bool) : b2z (!b) = 1 + b2z b := by cases b <;> decide

lemma wordOfNat_step {k n : ℕ} (hk : 0 < k) :
    wordOfNat k (step k n) = chiW hk (wordOfNat k n) := by
  funext i
  simp only [wordOfNat, testBit_step i.isLt, stepBit, chiW, idx, b2z_xor, b2z_and, b2z_not]

def lastRotation (start : ℕ) (fresh : ℕ → ℕ) : ℕ → ℕ
  | 0 => start
  | r + 1 => fresh r

def stateW {k : ℕ} (hk : 0 < k) (g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Word k) (key name : Word k) : ℕ → Word k
  | 0 => rotW hk start key + name
  | r + 1 =>
      chiW hk (mixW hk g (stateW hk g start fresh c key name r)) +
        rotW hk (fresh r) key + c (r + 1)

def stateNat (k g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Fin (2 ^ k)) (key name rounds : ℕ) : ℕ :=
  (List.range rounds).foldl (fun state j =>
    step k (state ^^^ rot k g state ^^^ rot k (k-g) state) ^^^
      rot k (fresh j) key ^^^ (c (j+1)).val) (rot k start key ^^^ name)

lemma stateNat_succ (k g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Fin (2 ^ k)) (key name r : ℕ) :
    stateNat k g start fresh c key name (r+1) =
      step k (stateNat k g start fresh c key name r ^^^
        rot k g (stateNat k g start fresh c key name r) ^^^
        rot k (k-g) (stateNat k g start fresh c key name r)) ^^^
      rot k (fresh r) key ^^^ (c (r+1)).val := by
  simp [stateNat, List.range_succ, List.foldl_append]

lemma stateNat_lt {k : ℕ} (g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Fin (2 ^ k)) (key : ℕ) (name : Fin (2 ^ k)) (r : ℕ) :
    stateNat k g start fresh c key name.val r < 2 ^ k := by
  cases r with
  | zero => exact xor_lt (rot_lt k _ _) name.isLt
  | succ r =>
    rw [stateNat_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (c (r+1)).isLt

lemma wordOfNat_state {k : ℕ} (hk : 0 < k) (g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Fin (2 ^ k)) (key name : Fin (2 ^ k)) (r : ℕ) :
    wordOfNat k (stateNat k g start fresh c key.val name.val r) =
      stateW hk g start fresh (fun j => wordOfNat k (c j).val)
        (wordOfNat k key.val) (wordOfNat k name.val) r := by
  induction r with
  | zero =>
    change wordOfNat k (rot k start key.val ^^^ name.val) = _
    rw [wordOfNat_xor, wordOfNat_rot hk key.isLt]
    rfl
  | succ r ih =>
    rw [stateNat_succ, wordOfNat_xor, wordOfNat_xor, wordOfNat_step hk,
      wordOfNat_rot hk key.isLt, wordOfNat_mix hk (stateNat_lt g start fresh c key.val name r), ih]
    rfl

lemma stateW_shift {k : ℕ} (hk : 0 < k) (g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Word k) (key name d : Word k) (hd : mixW hk g d = 0) (r : ℕ) :
    stateW hk g start fresh c (key + d) name r =
      stateW hk g start fresh c key name r + rotW hk (lastRotation start fresh r) d := by
  induction r with
  | zero => simp [stateW, lastRotation, add_right_comm]
  | succ r ih =>
    simp only [stateW, lastRotation]
    rw [show stateW hk g start fresh c (key + d) name r =
        stateW hk g start fresh c key name r + rotW hk (lastRotation start fresh r) d from ih,
      map_add, mixW_rotW, hd, map_zero, add_zero, map_add]
    abel

lemma idx_rot_add {k : ℕ} (hk : 0 < k) (t g : ℕ) :
    rotIndex hk g (idx hk (t + g)) = idx hk t := by
  unfold rotIndex
  rw [idx_add]
  have hg := Nat.mod_lt g hk
  have hdiv := Nat.div_add_mod g k
  have h : t + g + (k - g % k) = t + (g / k + 1) * k := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (g / k) k]
    omega
  rw [h]
  apply Fin.ext
  simp [idx, Nat.add_mul_mod_self_right]

lemma rotIndex_rev {k : ℕ} (hk : 0 < k) {g : ℕ} (hg : 0 < g) (hgk : g ≤ k)
    (i : Fin k) : rotIndex hk (k-g) i = idx hk (i.val + g) := by
  have h : (k-g) % k = k-g := Nat.mod_eq_of_lt (by omega)
  have h' : k - (k-g) = g := by omega
  simp only [rotIndex, h, h']

lemma mixW_at_add {k : ℕ} (hk : 0 < k) {g : ℕ} (hg : 0 < g) (hgk : g ≤ k)
    (t : ℕ) (w : Word k) : mixW hk g w (idx hk (t+g)) =
      w (idx hk (t+g)) + w (idx hk t) + w (idx hk (t+g+g)) := by
  simp only [mixW_apply, rotW_apply, idx_rot_add, rotIndex_rev hk hg hgk, idx_add]

def kernelW {k : ℕ} (hk : 0 < k) (g : ℕ) : Submodule F (Word k) :=
  LinearMap.ker (mixW hk g)

lemma kernel_one_le_two {k : ℕ} (hk : 0 < k) : kernelW hk 1 ≤ kernelW hk 2 := by
  intro w hw
  change mixW hk 1 w = 0 at hw
  change mixW hk 2 w = 0
  by_cases hsmall : k = 1
  · subst k
    have hidx (i : Fin 1) (s : ℕ) : rotIndex hk s i = i := Subsingleton.elim _ _
    have hmix (g : ℕ) : mixW hk g w = w := by
      funext i
      simp only [mixW_apply, rotW_apply, hidx, z2_add_self, zero_add]
    rwa [hmix 2, ← hmix 1]
  · funext i
    let t := (rotIndex hk 2 i).val
    have hfix : idx hk (t+2) = i := by
      dsimp [t, rotIndex]
      rw [idx_add]
      have hmod : 2 % k < k := Nat.mod_lt 2 hk
      have hdiv := Nat.div_add_mod 2 k
      have heq : i.val + (k - 2 % k) + 2 = i.val + (2/k+1)*k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2/k) k]
        omega
      rw [heq]
      exact Fin.ext (by simp [idx, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt])
    have hlocal (t' : ℕ) : w (idx hk (t'+1)) + w (idx hk t') + w (idx hk (t'+1+1)) = 0 := by
      rw [← mixW_at_add hk (by decide : 0 < 1) (by omega : 1 ≤ k), hw]
      rfl
    have haux (a b c d e : F) : b + a + c = 0 → c + b + d = 0 → d + c + e = 0 →
        c + a + e = 0 := by revert a b c d e; decide
    rw [← hfix, mixW_at_add hk (by decide : 0 < 2) (by omega : 2 ≤ k)]
    exact haux _ _ _ _ _ (hlocal t) (hlocal (t+1)) (hlocal (t+2))

lemma kernel_two_card {k : ℕ} (hk : 0 < k) [Fintype (kernelW hk 2)] :
    Fintype.card (kernelW hk 2) ≤ 16 := by
  let restrictFirst (w : kernelW hk 2) (j : Fin 4) : F := w.val (idx hk j.val)
  have hinj : Function.Injective restrictFirst := by
    intro v w h
    apply Subtype.ext
    funext j
    have hres (n : ℕ) (hn : n < k) : v.val (idx hk n) = w.val (idx hk n) := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        by_cases hn4 : n < 4
        · exact congrFun h (⟨n, hn4⟩ : Fin 4)
        · let t := n - 4
          have hv : mixW hk 2 v.val = 0 := v.property
          have hw : mixW hk 2 w.val = 0 := w.property
          have heq (a b c d : F) : a + b + c = 0 → a + b + d = 0 → c = d := by
            intro h1 h2
            exact add_left_cancel (h1.trans h2.symm)
          have hv' := congrFun hv (idx hk (t+2))
          have hw' := congrFun hw (idx hk (t+2))
          rw [mixW_at_add hk (by decide : 0 < 2) (by omega : 2 ≤ k),
            ih (t+2) (by dsimp [t]; omega) (by dsimp [t]; omega),
            ih t (by dsimp [t]; omega) (by dsimp [t]; omega)] at hv'
          rw [mixW_at_add hk (by decide : 0 < 2) (by omega : 2 ≤ k)] at hw'
          have hcd := heq _ _ _ _ hv' hw'
          rwa [show t+2+2 = n by dsimp [t]; omega] at hcd
    simpa only [idx_val] using hres j.val j.isLt
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective restrictFirst hinj

def viewW {k : ℕ} (hk : 0 < k) (s : ℕ) (mask : Word k) : Word k →ₗ[F] Word k :=
  (maskW mask).comp (rotW hk s)

def rowShifts {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k) :
    Submodule F (Word k) := kernelW hk 1 ⊓ LinearMap.ker VC

def colMap {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k) :
    kernelW hk 2 →ₗ[F] Word k := VC.comp (kernelW hk 2).subtype

def rowMap {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k) :
    rowShifts hk VC →ₗ[F] Word k := VR.comp (rowShifts hk VC).subtype

noncomputable def sectionLift {k : ℕ} (S : Submodule F (Word k))
    (f : S →ₗ[F] Word k) : LinearMap.range f →ₗ[F] S :=
  Classical.choose (f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict))

lemma sectionLift_apply {k : ℕ} (S : Submodule F (Word k))
    (f : S →ₗ[F] Word k) (a : LinearMap.range f) :
    f (sectionLift S f a) = a.val := by
  have h := Classical.choose_spec (f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict))
  exact congrArg Subtype.val (LinearMap.congr_fun h a)

lemma sectionLift_injective {k : ℕ} (S : Submodule F (Word k))
    (f : S →ₗ[F] Word k) : Function.Injective (sectionLift S f) := by
  intro a b h
  apply Subtype.ext
  rw [← sectionLift_apply S f a, ← sectionLift_apply S f b, h]

noncomputable def colLift {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k) :
    LinearMap.range (colMap hk VC) →ₗ[F] Word k :=
  (kernelW hk 2).subtype.comp (sectionLift _ (colMap hk VC))

noncomputable def rowLift {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k) :
    LinearMap.range (rowMap hk VR VC) →ₗ[F] Word k :=
  (rowShifts hk VC).subtype.comp (sectionLift _ (rowMap hk VR VC))

lemma colLift_mem {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k)
    (a : LinearMap.range (colMap hk VC)) : colLift hk VC a ∈ kernelW hk 2 :=
  (sectionLift _ (colMap hk VC) a).property

lemma rowLift_mem {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k)
    (b : LinearMap.range (rowMap hk VR VC)) : rowLift hk VR VC b ∈ rowShifts hk VC :=
  (sectionLift _ (rowMap hk VR VC) b).property

lemma colLift_view {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k)
    (a : LinearMap.range (colMap hk VC)) : VC (colLift hk VC a) = a.val :=
  sectionLift_apply _ (colMap hk VC) a

lemma rowLift_view {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k)
    (b : LinearMap.range (rowMap hk VR VC)) : VR (rowLift hk VR VC b) = b.val :=
  sectionLift_apply _ (rowMap hk VR VC) b

lemma rowLift_col_zero {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k)
    (b : LinearMap.range (rowMap hk VR VC)) : VC (rowLift hk VR VC b) = 0 :=
  (rowLift_mem hk VR VC b).2

lemma col_range_card {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k)
    [Fintype (LinearMap.range (colMap hk VC))] :
    Fintype.card (LinearMap.range (colMap hk VC)) ≤ 16 := by
  letI : Fintype (kernelW hk 2) := Fintype.ofFinite _
  exact (Fintype.card_le_of_injective _ (sectionLift_injective _ (colMap hk VC))).trans
    (kernel_two_card hk)

lemma row_range_card {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k)
    [Fintype (LinearMap.range (rowMap hk VR VC))] :
    Fintype.card (LinearMap.range (rowMap hk VR VC)) ≤ 16 := by
  letI : Fintype (kernelW hk 2) := Fintype.ofFinite _
  let e : LinearMap.range (rowMap hk VR VC) → kernelW hk 2 := fun b =>
    ⟨rowLift hk VR VC b, kernel_one_le_two hk (rowLift_mem hk VR VC b).1⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Subtype.ext ((rowLift_view hk VR VC a).symm.trans
      ((congrArg (fun q : kernelW hk 2 => VR q.val) hab).trans (rowLift_view hk VR VC b)))
  exact (Fintype.card_le_of_injective e he).trans (kernel_two_card hk)

noncomputable def shiftPair {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k) :
    (LinearMap.range (colMap hk VC) × LinearMap.range (rowMap hk VR VC)) →ₗ[F] Word k :=
  (colLift hk VC).coprod (rowLift hk VR VC)

lemma shiftPair_injective {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k) :
    Function.Injective (shiftPair hk VR VC) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  change colLift hk VC a + rowLift hk VR VC b = colLift hk VC a' + rowLift hk VR VC b' at h
  have hcol := congrArg (fun w => VC w) h
  simp only [map_add, colLift_view, rowLift_col_zero, add_zero] at hcol
  have hc : a = a' := Subtype.ext hcol
  subst a'
  have hr := congrArg (fun w => VR w) (add_left_cancel h)
  exact Prod.ext rfl (Subtype.ext (by simpa only [rowLift_view] using hr))

noncomputable def keyEquiv {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k)
    (D : Submodule F (Word k)) (hD : IsCompl D (LinearMap.range (shiftPair hk VR VC))) :
    (D × LinearMap.range (colMap hk VC) × LinearMap.range (rowMap hk VR VC)) ≃ₗ[F] Word k :=
  ((LinearEquiv.refl F D).prodCongr (LinearEquiv.ofInjective _ (shiftPair_injective hk VR VC))).trans
    (D.prodEquivOfIsCompl _ hD)

lemma budgetB {N b b' : ℕ} {A B : Set (Sig N)}
    (h : Build A B b) (hb : b ≤ b') : Build A B b' :=
  relaxB h le_rfl Set.subset_union_right hb

lemma finishB {N b : ℕ} (f : Sig N)
    (h : Build (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) {f} b) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack N C ∧ C.size ≤ b ∧
      ∀ x : Fin N → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨k, hk, gs, hgs, hr, hf, hw⟩ := h.run (startSched N) le_rfl
  obtain ⟨i, _, hi⟩ := hw f (Or.inr rfl)
  exact ⟨⟨gs, i⟩, hf, hr, by simpa [Circuit.size, hgs] using hk, hi⟩

noncomputable def enum (α : Type*) [Fintype α] : List α :=
  (Finset.univ : Finset α).toList

lemma mem_enum {α : Type*} [Fintype α] (a : α) : a ∈ enum α := by
  simp [enum]

lemma length_enum (α : Type*) [Fintype α] : (enum α).length = Fintype.card α := by
  simp [enum]

lemma indexedSigB {N : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    (f : α → Sig N) (c : ℕ) (hf : ∀ a, Build A {f a} c) :
    Build A (Set.range f) (Fintype.card α * c) := by
  have h := listB (fun a => {f a}) c (enum α) (fun a _ => hf a)
  refine relaxB h le_rfl ?_ (by rw [length_enum])
  rintro _ ⟨a, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨mem_enum a, rfl⟩⟩)

def wordBit {N k : ℕ} (w : (Fin N → Bool) → Word k) (i : Fin k) : Sig N :=
  fun x => z2b (w x i)

def wordSigs {N k : ℕ} (w : (Fin N → Bool) → Word k) : Set (Sig N) :=
  Set.range (wordBit w)

lemma wordBit_mem {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : wordSigs w ⊆ A) (i : Fin k) : wordBit w i ∈ A :=
  hw ⟨i, rfl⟩

lemma wordSigs_subset {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : ∀ i, wordBit w i ∈ A) : wordSigs w ⊆ A := by
  rintro _ ⟨i, rfl⟩
  exact hw i

lemma wordConst {N k : ℕ} {A : Set (Sig N)} (w : Word k)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    wordSigs (fun _ => w) ⊆ A := by
  apply wordSigs_subset
  intro i
  change (fun _ => z2b (w i)) ∈ A
  obtain h | h := z2_cases (w i)
  · rw [h, z2b_zero]
    exact h0
  · rw [h, z2b_one]
    exact h1

lemma wordRot {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : wordSigs w ⊆ A) (hk : 0 < k) (s : ℕ) :
    wordSigs (fun x => rotW hk s (w x)) ⊆ A := by
  apply wordSigs_subset
  intro i
  exact wordBit_mem hw (rotIndex hk s i)

lemma wordMask {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : wordSigs w ⊆ A) (h0 : (fun _ => false) ∈ A) (mask : Word k) :
    wordSigs (fun x => maskW mask (w x)) ⊆ A := by
  apply wordSigs_subset
  intro i
  change (fun x => z2b (w x i * mask i)) ∈ A
  obtain h | h := z2_cases (mask i)
  · simp only [h, mul_zero, z2b_zero]
    exact h0
  · simp only [h, mul_one]
    exact wordBit_mem hw i

lemma wordAddB {N k : ℕ} {A : Set (Sig N)} {u v : (Fin N → Bool) → Word k}
    (hu : wordSigs u ⊆ A) (hv : wordSigs v ⊆ A) :
    Build A (wordSigs (fun x => u x + v x)) (4 * k) := by
  rw [Nat.mul_comm]
  apply finSigB
  intro i
  change Build A {fun x => z2b (u x i + v x i)} 4
  simp only [z2b_add]
  exact xorB (wordBit_mem hu i) (wordBit_mem hv i)

lemma mixWB {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : wordSigs w ⊆ A) (hk : 0 < k) (g : ℕ) :
    Build A (wordSigs (fun x => mixW hk g (w x))) (8 * k) := by
  let m := fun x => w x + rotW hk g (w x)
  have h1 : Build A (wordSigs m) (4*k) := wordAddB hw (wordRot hw hk g)
  have h2 : Build (A ∪ wordSigs m) (wordSigs (fun x => m x + rotW hk (k-g) (w x))) (4*k) :=
    wordAddB Set.subset_union_right ((wordRot hw hk (k-g)).trans Set.subset_union_left)
  change Build A (wordSigs (fun x => m x + rotW hk (k-g) (w x))) (8*k)
  rw [show 8*k = 4*k+4*k by omega]
  exact seq2B h1 h2

lemma chiWB {N k : ℕ} {A : Set (Sig N)} {w : (Fin N → Bool) → Word k}
    (hw : wordSigs w ⊆ A) (hk : 0 < k) :
    Build A (wordSigs (fun x => chiW hk (w x))) (6 * k) := by
  rw [Nat.mul_comm]
  apply finSigB
  intro i
  let a := wordBit w i
  let b := wordBit w (idx hk (i.val+1))
  let c := wordBit w (idx hk (i.val+2))
  let nb : Sig N := fun x => !(b x)
  let p : Sig N := fun x => nb x && c x
  have h1 : Build A {nb} 1 := notB (wordBit_mem hw _)
  have h2 : Build (A ∪ {nb}) {p} 1 := andB (Or.inr rfl) (Or.inl (wordBit_mem hw _))
  have h3 : Build ((A ∪ {nb}) ∪ {p}) {fun x => xor (a x) (p x)} 4 :=
    xorB (Or.inl (Or.inl (wordBit_mem hw i))) (Or.inr rfl)
  have h : Build A {fun x => xor (a x) (p x)} 6 := by
    exact seq2B h1 (seq2B h2 h3)
  change Build A {fun x => z2b (w x i + (1 + w x (idx hk (i.val+1))) * w x (idx hk (i.val+2)))} 6
  simp only [z2b_add, z2b_mul, z2b_one, Bool.true_xor]
  exact h

lemma stateWB {N k : ℕ} {A : Set (Sig N)} (hk : 0 < k) (g start : ℕ) (fresh : ℕ → ℕ)
    (c : ℕ → Word k) (key name : (Fin N → Bool) → Word k)
    (hkey : wordSigs key ⊆ A) (hname : wordSigs name ⊆ A)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (r : ℕ) :
    Build A (wordSigs (fun x => stateW hk g start fresh c (key x) (name x) r))
      (4*k + r*(22*k)) := by
  induction r with
  | zero =>
    simpa only [stateW, Nat.zero_mul, Nat.add_zero] using wordAddB (wordRot hkey hk start) hname
  | succ r ih =>
    let state := fun x => stateW hk g start fresh c (key x) (name x) r
    let mixed := fun x => mixW hk g (state x)
    let nonlinear := fun x => chiW hk (mixed x)
    let injected := fun x => nonlinear x + rotW hk (fresh r) (key x)
    have hmix : Build (A ∪ wordSigs state) (wordSigs mixed) (8*k) :=
      mixWB Set.subset_union_right hk g
    have hchi : Build ((A ∪ wordSigs state) ∪ wordSigs mixed) (wordSigs nonlinear) (6*k) :=
      chiWB Set.subset_union_right hk
    have hinj : Build ((A ∪ wordSigs state) ∪ wordSigs nonlinear) (wordSigs injected) (4*k) :=
      wordAddB Set.subset_union_right ((wordRot hkey hk (fresh r)).trans
        (Set.subset_union_left.trans Set.subset_union_left))
    have hconst : Build ((A ∪ wordSigs state) ∪ wordSigs injected)
        (wordSigs (fun x => injected x + c (r+1))) (4*k) :=
      wordAddB Set.subset_union_right ((wordConst _ h0 h1).trans
        (Set.subset_union_left.trans Set.subset_union_left))
    have hround := seq2B (seq2B (seq2B hmix hchi) hinj) hconst
    have h := seq2B ih hround
    change Build A (wordSigs (fun x => injected x + c (r+1))) (4*k + (r+1)*(22*k))
    rw [show 4*k + (r+1)*(22*k) = 4*k+r*(22*k)+(8*k+6*k+4*k+4*k) by ring]
    exact h

def residual {k : ℕ} (mask out target : Word k) : Word k :=
  maskW mask (out + target)

lemma residual_eq_iff {k : ℕ} {mask out target : Word k} :
    residual mask out target = 0 ↔ maskW mask out = maskW mask target := by
  rw [residual, map_add, ← eq_neg_iff_add_eq_zero, word_neg_self]

lemma residual_translate {k : ℕ} (mask out target d : Word k) :
    residual mask (out + d) target = residual mask out target + maskW mask d := by
  simp only [residual, map_add]
  abel

lemma residual_cancel {k : ℕ} {mask out target d : Word k} :
    maskW mask (out + d) = maskW mask target ↔ residual mask out target = maskW mask d := by
  rw [← residual_eq_iff, residual_translate, ← eq_neg_iff_add_eq_zero, word_neg_self]

lemma residB {N k : ℕ} {A : Set (Sig N)} {u v : (Fin N → Bool) → Word k}
    (hu : wordSigs u ⊆ A) (hv : wordSigs v ⊆ A) (mask : Word k)
    (h0 : (fun _ => false) ∈ A) :
    Build A (wordSigs (fun x => residual mask (u x) (v x))) (4*k) := by
  refine relaxB (wordAddB hu hv) le_rfl ?_ le_rfl
  exact wordMask Set.subset_union_right (Or.inl h0) mask

noncomputable def matchFlag {N k : ℕ} (w : (Fin N → Bool) → Word k) (v : Word k) : Sig N :=
  fun x => decide (w x = v)

lemma matchFlag_spec {N k : ℕ} (w : (Fin N → Bool) → Word k) (v : Word k) (x : Fin N → Bool) :
    matchFlag w v x = true ↔ w x = v := by simp [matchFlag]

noncomputable def constWordDeps {N k : ℕ} (w : (Fin N → Bool) → Word k) (v : Word k) :
    List (Sig N) :=
  (List.finRange k).map fun i =>
    if z2b (v i) then wordBit w i else fun x => !(wordBit w i x)

lemma matchFlag_eq_all {N k : ℕ} (w : (Fin N → Bool) → Word k) (v : Word k) :
    matchFlag w v = fun x => (constWordDeps w v).all (fun f => f x) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [matchFlag_spec, List.all_eq_true]
  constructor
  · intro h a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    have hi : w x i = v i := congrFun h i
    cases hv : z2b (v i) <;> simp [wordBit, hi, hv]
  · intro h
    funext i
    have hi := h _ (List.mem_map_of_mem (f := fun j : Fin k =>
      if z2b (v j) then wordBit w j else fun y => !(wordBit w j y)) (List.mem_finRange i))
    have he : z2b (w x i) = z2b (v i) := by
      cases hv : z2b (v i) <;> simpa [wordBit, hv] using hi
    simpa only [b2z_z2b] using congrArg b2z he

lemma matchesB {N k : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    {w : (Fin N → Bool) → Word k} (hw : wordSigs w ⊆ A) (values : α → Word k)
    (h1 : (fun _ => true) ∈ A) :
    Build A (Set.range (fun a => matchFlag w (values a))) (k + Fintype.card α*k) := by
  let negs : Fin k → Sig N := fun i x => !(wordBit w i x)
  have hn : Build A (Set.range negs) k := by
    simpa only [Nat.mul_one] using finSigB negs 1 (fun i => notB (wordBit_mem hw i))
  have hf (a : α) : Build (A ∪ Set.range negs) {matchFlag w (values a)} k := by
    rw [matchFlag_eq_all]
    have ht : ∀ f ∈ constWordDeps w (values a), f ∈ A ∪ Set.range negs := by
      intro f hf
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
      split
      · exact Or.inl (wordBit_mem hw i)
      · exact Or.inr ⟨i, rfl⟩
    simpa [constWordDeps] using andListB (constWordDeps w (values a)) ht (Or.inl h1)
  exact seq2B hn (indexedSigB (fun a => matchFlag w (values a)) k hf)

noncomputable def anyFlag {N : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N) : Sig N :=
  fun x => (enum α).any (fun a => flags a x)

lemma anyFlag_spec {N : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N) (x : Fin N → Bool) :
    anyFlag flags x = true ↔ ∃ a, flags a x = true := by
  simp [anyFlag, List.any_eq_true, mem_enum]

lemma anyFlagB {N : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    (flags : α → Sig N) (hf : Set.range flags ⊆ A) (h0 : (fun _ => false) ∈ A) :
    Build A {anyFlag flags} (Fintype.card α) := by
  have h := orListB ((enum α).map flags)
    (fun g hg => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg; exact hf ⟨a, rfl⟩) h0
  unfold anyFlag
  simpa [length_enum, List.any_map, Function.comp_def] using h

noncomputable def selectWord {N k : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N)
    (values : α → Word k) (x : Fin N → Bool) : Word k :=
  fun i => b2z (((enum α).filter (fun a => z2b (values a i))).any (fun a => flags a x))

lemma selectWord_eq {N k : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N)
    (values : α → Word k) (x : Fin N → Bool) (a : α)
    (ha : flags a x = true) (hu : ∀ a', flags a' x = true → a' = a) :
    selectWord flags values x = values a := by
  funext i
  have he (a' : α) : a' ∈ (enum α).filter (fun t => z2b (values t i)) ↔
      z2b (values a' i) = true := by simp [mem_enum]
  have hz : ((enum α).filter (fun t => z2b (values t i))).any (fun a' => flags a' x) =
      z2b (values a i) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true]
    constructor
    · rintro ⟨a', hm, hh⟩
      obtain rfl := hu a' hh
      exact (he a').mp hm
    · intro hi
      exact ⟨a, (he a).mpr hi, ha⟩
  simp only [selectWord, hz, b2z_z2b]

lemma selectWordB {N k : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    (flags : α → Sig N) (hf : Set.range flags ⊆ A) (values : α → Word k)
    (h0 : (fun _ => false) ∈ A) :
    Build A (wordSigs (selectWord flags values)) (k * Fintype.card α) := by
  apply finSigB
  intro i
  let items := (enum α).filter (fun t => z2b (values t i))
  have h := orListB (items.map flags)
    (fun g hg => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg; exact hf ⟨a, rfl⟩) h0
  have hlen : (items.map flags).length ≤ Fintype.card α := by
    simpa only [List.length_map, length_enum, items] using
      List.length_filter_le (fun t => z2b (values t i)) (enum α)
  unfold wordBit selectWord
  rw [show (fun x => z2b (b2z (items.any (fun a => flags a x)))) =
      (fun x => (items.map flags).any (fun g => g x)) by
    funext x
    simp only [z2b_b2z, List.any_map, Function.comp_def]]
  exact budgetB h hlen

def rowFresh (j : ℕ) : ℕ := 2*j

def colFresh (j : ℕ) : ℕ := 3*(j+1)+1

noncomputable def tableFlags {N k : ℕ} {α : Type*} (hk : 0 < k) (g start r : ℕ)
    (fresh : ℕ → ℕ) (c : ℕ → Word k) (mask : Word k)
    (key name target : (Fin N → Bool) → Word k) (values : α → Word k) (a : α) : Sig N :=
  matchFlag (fun x => residual mask (stateW hk g start fresh c (key x) (name x) r) (target x))
    (values a)

lemma tableFlagsB {N k : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    (hk : 0 < k) (g start r : ℕ) (fresh : ℕ → ℕ) (c : ℕ → Word k) (mask : Word k)
    (key name target : (Fin N → Bool) → Word k) (values : α → Word k)
    (hkey : wordSigs key ⊆ A) (hname : wordSigs name ⊆ A) (htarget : wordSigs target ⊆ A)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) :
    Build A (Set.range (tableFlags hk g start r fresh c mask key name target values))
      ((4*k + r*(22*k)) + 4*k + (k + Fintype.card α*k)) := by
  let state := fun x => stateW hk g start fresh c (key x) (name x) r
  let err := fun x => residual mask (state x) (target x)
  have hs : Build A (wordSigs state) (4*k + r*(22*k)) :=
    stateWB hk g start fresh c key name hkey hname h0 h1 r
  have he : Build (A ∪ wordSigs state) (wordSigs err) (4*k) :=
    residB Set.subset_union_right (htarget.trans Set.subset_union_left) mask (Or.inl h0)
  have hm : Build (A ∪ wordSigs err) (Set.range (tableFlags hk g start r fresh c mask key name target values))
      (k + Fintype.card α*k) :=
    matchesB Set.subset_union_right values (Or.inl h1)
  exact seq2B (seq2B hs he) hm

noncomputable def slotFlag {N k : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Word k) (mr mc seed : Word k)
    (valuesC : α → Word k) (valuesR : β → Word k) (rowKeys : α → Word k)
    (u v tr tc : (Fin N → Bool) → Word k) : Sig N :=
  let cf := tableFlags hk 2 3 r colFresh cC mc (fun _ => seed) v tc valuesC
  let key := selectWord cf rowKeys
  let rf := tableFlags hk 1 1 r rowFresh cR mr key u tr valuesR
  fun x => anyFlag cf x && anyFlag rf x

set_option maxHeartbeats 800000 in
lemma slotFlagB {N k : ℕ} {α β : Type*} [Fintype α] [Fintype β] {A : Set (Sig N)}
    (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Word k) (mr mc seed : Word k)
    (valuesC : α → Word k) (valuesR : β → Word k) (rowKeys : α → Word k)
    (u v tr tc : (Fin N → Bool) → Word k)
    (hu : wordSigs u ⊆ A) (hv : wordSigs v ⊆ A) (htr : wordSigs tr ⊆ A) (htc : wordSigs tc ⊆ A)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (ha : Fintype.card α ≤ 16) (hb : Fintype.card β ≤ 16) :
    Build A {slotFlag hk r cR cC mr mc seed valuesC valuesR rowKeys u v tr tc}
      (100*(k+1)*(r+1)) := by
  let cf := tableFlags hk 2 3 r colFresh cC mc (fun _ => seed) v tc valuesC
  let key := selectWord cf rowKeys
  let rf := tableFlags hk 1 1 r rowFresh cR mr key u tr valuesR
  let ac := Fintype.card α
  let bc := Fintype.card β
  let ct := (4*k + r*(22*k)) + 4*k + (k + ac*k)
  let rt := (4*k + r*(22*k)) + 4*k + (k + bc*k)
  have hc : Build A (Set.range cf) ct :=
    tableFlagsB hk 2 3 r colFresh cC mc _ v tc valuesC (wordConst seed h0 h1) hv htc h0 h1
  have hs : Build (A ∪ Set.range cf) (wordSigs key) (k*ac) :=
    selectWordB cf Set.subset_union_right rowKeys (Or.inl h0)
  have hl : A ⊆ (A ∪ Set.range cf) ∪ wordSigs key :=
    Set.subset_union_left.trans Set.subset_union_left
  have hr : Build ((A ∪ Set.range cf) ∪ wordSigs key) (Set.range rf) rt :=
    tableFlagsB hk 1 1 r rowFresh cR mr key u tr valuesR Set.subset_union_right
      (hu.trans hl) (htr.trans hl) (hl h0) (hl h1)
  have hcr : Build A (Set.range cf ∪ Set.range rf) (ct + (k*ac + rt)) :=
    seqB hc (seq2B hs hr)
  let E := A ∪ (Set.range cf ∪ Set.range rf)
  have hco : Build E {anyFlag cf} ac :=
    anyFlagB cf (Set.subset_union_left.trans Set.subset_union_right) (Or.inl h0)
  have hro : Build E {anyFlag rf} bc :=
    anyFlagB rf (Set.subset_union_right.trans Set.subset_union_right) (Or.inl h0)
  have hf : Build (E ∪ ({anyFlag cf} ∪ {anyFlag rf}))
      {slotFlag hk r cR cC mr mc seed valuesC valuesR rowKeys u v tr tc} 1 :=
    andB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  refine budgetB (seq2B hcr (seq2B (unionB hco hro) hf)) ?_
  have ha' : ac*k ≤ 16*k := Nat.mul_le_mul_right k ha
  have hb' : bc*k ≤ 16*k := Nat.mul_le_mul_right k hb
  have ha'' : k*ac ≤ k*16 := Nat.mul_le_mul_left k ha
  change ct + (k*ac + rt) + (ac+bc+1) ≤ _
  dsimp only [ct, rt, ac, bc] at *
  nlinarith

abbrev ColCode {k : ℕ} (hk : 0 < k) (VC : Word k →ₗ[F] Word k) :=
  LinearMap.range (colMap hk VC)

abbrev RowCode {k : ℕ} (hk : 0 < k) (VR VC : Word k →ₗ[F] Word k) :=
  LinearMap.range (rowMap hk VR VC)

def rowView {k : ℕ} (hk : 0 < k) (r : ℕ) (mr : Word k) : Word k →ₗ[F] Word k :=
  viewW hk (lastRotation 1 rowFresh r) mr

def colView {k : ℕ} (hk : 0 < k) (r : ℕ) (mc : Word k) : Word k →ₗ[F] Word k :=
  viewW hk (lastRotation 3 colFresh r) mc

def hitsWord {k : ℕ} (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Word k)
    (mr mc u v tr tc key : Word k) : Prop :=
  maskW mr (stateW hk 1 1 rowFresh cR key u r) = maskW mr tr ∧
  maskW mc (stateW hk 2 3 colFresh cC key v r) = maskW mc tc

noncomputable def slot {N k : ℕ} (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Word k) (mr mc seed : Word k)
    [Fintype (ColCode hk (colView hk r mc))]
    [Fintype (RowCode hk (rowView hk r mr) (colView hk r mc))]
    (u v tr tc : (Fin N → Bool) → Word k) : Sig N :=
  slotFlag hk r cR cC mr mc seed
    (fun a : ColCode hk (colView hk r mc) => a.val)
    (fun b : RowCode hk (rowView hk r mr) (colView hk r mc) => b.val)
    (fun a => seed + colLift hk (colView hk r mc) a) u v tr tc

set_option maxHeartbeats 1000000 in
lemma slot_spec {N k : ℕ} (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Word k) (mr mc seed : Word k)
    [Fintype (ColCode hk (colView hk r mc))]
    [Fintype (RowCode hk (rowView hk r mr) (colView hk r mc))]
    (u v tr tc : (Fin N → Bool) → Word k) (x : Fin N → Bool) :
    let P := fun p : ColCode hk (colView hk r mc) × RowCode hk (rowView hk r mr) (colView hk r mc) =>
      hitsWord hk r cR cC mr mc (u x) (v x) (tr x) (tc x)
        (seed + (colLift hk (colView hk r mc) p.1 +
          rowLift hk (rowView hk r mr) (colView hk r mc) p.2))
    (slot hk r cR cC mr mc seed u v tr tc x = true ↔ ∃ p, P p) ∧
      ∀ p q, P p → P q → p = q := by
  let VR := rowView hk r mr
  let VC := colView hk r mc
  let cf := tableFlags hk 2 3 r colFresh cC mc (fun _ => seed) v tc (fun a : ColCode hk VC => a.val)
  let liftC := colLift hk VC
  let liftR := rowLift hk VR VC
  let key := selectWord cf (fun a => seed + liftC a)
  let rf := tableFlags hk 1 1 r rowFresh cR mr key u tr (fun b : RowCode hk VR VC => b.val)
  have hc (a : ColCode hk VC) (b : RowCode hk VR VC) :
      maskW mc (stateW hk 2 3 colFresh cC (seed + (liftC a + liftR b)) (v x) r) = maskW mc (tc x)
        ↔ cf a x = true := by
    have hmem : liftC a + liftR b ∈ kernelW hk 2 :=
      Submodule.add_mem _ (colLift_mem hk VC a) (kernel_one_le_two hk (rowLift_mem hk VR VC b).1)
    have hview : VC (liftC a + liftR b) = a.val := by
      simp only [map_add, liftC, liftR, colLift_view, rowLift_col_zero, add_zero]
    rw [stateW_shift hk 2 3 colFresh cC seed (v x) _ hmem, residual_cancel]
    change residual mc (stateW hk 2 3 colFresh cC seed (v x) r) (tc x) = VC (liftC a + liftR b) ↔ _
    rw [hview]
    exact (matchFlag_spec
      (fun y => residual mc (stateW hk 2 3 colFresh cC seed (v y) r) (tc y)) a.val x).symm
  have hcu (a a' : ColCode hk VC) (ha : cf a x = true) (ha' : cf a' x = true) : a = a' := by
    have h : residual mc (stateW hk 2 3 colFresh cC seed (v x) r) (tc x) = a.val :=
      (matchFlag_spec _ _ _).mp ha
    have h' : residual mc (stateW hk 2 3 colFresh cC seed (v x) r) (tc x) = a'.val :=
      (matchFlag_spec _ _ _).mp ha'
    exact Subtype.ext (h.symm.trans h')
  have hru (b b' : RowCode hk VR VC) (hb : rf b x = true) (hb' : rf b' x = true) : b = b' := by
    have h : residual mr (stateW hk 1 1 rowFresh cR (key x) (u x) r) (tr x) = b.val :=
      (matchFlag_spec _ _ _).mp hb
    have h' : residual mr (stateW hk 1 1 rowFresh cR (key x) (u x) r) (tr x) = b'.val :=
      (matchFlag_spec _ _ _).mp hb'
    exact Subtype.ext (h.symm.trans h')
  have hr (a : ColCode hk VC) (b : RowCode hk VR VC) (ha : cf a x = true) :
      maskW mr (stateW hk 1 1 rowFresh cR (seed + (liftC a + liftR b)) (u x) r) = maskW mr (tr x)
        ↔ rf b x = true := by
    have hkey : key x = seed + liftC a :=
      selectWord_eq cf _ x a ha (fun a' ha' => hcu a' a ha' ha)
    have hmem : liftR b ∈ kernelW hk 1 := (rowLift_mem hk VR VC b).1
    rw [← add_assoc, stateW_shift hk 1 1 rowFresh cR (seed+liftC a) (u x) _ hmem, residual_cancel,
      ← hkey]
    change residual mr (stateW hk 1 1 rowFresh cR (key x) (u x) r) (tr x) = VR (liftR b) ↔ _
    rw [rowLift_view]
    exact (matchFlag_spec
      (fun y => residual mr (stateW hk 1 1 rowFresh cR (key y) (u y) r) (tr y)) b.val x).symm
  have hp (a : ColCode hk VC) (b : RowCode hk VR VC) :
      hitsWord hk r cR cC mr mc (u x) (v x) (tr x) (tc x) (seed + (liftC a + liftR b)) ↔
        cf a x = true ∧ rf b x = true := by
    constructor
    · rintro ⟨hrow, hcol⟩
      have ha := (hc a b).mp hcol
      exact ⟨ha, (hr a b ha).mp hrow⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(hr a b ha).mpr hb, (hc a b).mpr ha⟩
  dsimp only
  change ((anyFlag cf x && anyFlag rf x) = true ↔ _) ∧ _
  rw [Bool.and_eq_true, anyFlag_spec, anyFlag_spec]
  constructor
  · constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a,b), (hp a b).mpr ⟨ha,hb⟩⟩
    · rintro ⟨⟨a,b⟩, h⟩
      obtain ⟨ha, hb⟩ := (hp a b).mp h
      exact ⟨⟨a,ha⟩, ⟨b,hb⟩⟩
  · rintro ⟨a,b⟩ ⟨a',b'⟩ h h'
    obtain ⟨ha, hb⟩ := (hp a b).mp h
    obtain ⟨ha', hb'⟩ := (hp a' b').mp h'
    exact Prod.ext (hcu a a' ha ha') (hru b b' hb hb')

noncomputable def score {N : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N) (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun a => flags a x = true)).card

lemma sumListVal_flags {N : ℕ} {α : Type*} (flags : α → Sig N) (xs : List α) (x : Fin N → Bool) :
    sumListVal (xs.map (fun a y => (flags a y).toNat)) x = (xs.filter (fun a => flags a x)).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, sumListVal, ih, List.filter_cons]
    cases flags a x <;> simp [Nat.add_comm]

lemma score_eq_sum {N : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N) :
    score flags = sumListVal ((enum α).map (fun a y => (flags a y).toNat)) := by
  classical
  funext x
  rw [sumListVal_flags]
  unfold enum
  rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList (Finset.univ : Finset α)).filter _)]
  simp only [score, List.toFinset_filter, Finset.toList_toFinset]

lemma score_le {N : ℕ} {α : Type*} [Fintype α] (flags : α → Sig N) (x : Fin N → Bool) :
    score flags x ≤ Fintype.card α :=
  Finset.card_filter_le _ _

lemma scoreB {N L : ℕ} {α : Type*} [Fintype α] {A : Set (Sig N)}
    (flags : α → Sig N) (hf : Set.range flags ⊆ A) (h0 : (fun _ => false) ∈ A) :
    Build A (Set.range (bitsOf L (score flags))) (Fintype.card α * (9*L)) := by
  rw [score_eq_sum]
  have h : ∀ G ∈ (enum α).map (fun a y => (flags a y).toNat),
      ∀ i : Fin L, bitsOf L G i ∈ A := by
    intro G hG i
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hG
    by_cases hi : i.val = 0
    · have he : bitsOf L (fun y => (flags a y).toNat) i = flags a := by
        funext x
        unfold bitsOf
        rw [hi]
        change (flags a x).toNat.testBit 0 = flags a x
        cases flags a x <;> decide
      rw [he]
      exact hf ⟨a, rfl⟩
    · have he : bitsOf L (fun y => (flags a y).toNat) i = (fun _ => false) := by
        funext x
        unfold bitsOf
        have hlt : (flags a x).toNat < 2 ^ i.val := by
          have hp : 2 ^ 1 ≤ 2 ^ i.val := Nat.pow_le_pow_right (by decide) (by omega)
          calc (flags a x).toNat ≤ 1 := by cases flags a x <;> decide
            _ < 2 ^ i.val := by omega
        exact Nat.testBit_lt_two_pow hlt
      rw [he]
      exact h0
  simpa only [List.length_map, length_enum] using sumListB L h0 _ h

def compareStep (a b c : Bool) : Bool := (!a && b) || ((!a || b) && c)

lemma compareStepB {N : ℕ} {A : Set (Sig N)} {a b c : Sig N}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun x => compareStep (a x) (b x) (c x)} 5 := by
  let na : Sig N := fun x => !(a x)
  let ab : Sig N := fun x => na x && b x
  let ao : Sig N := fun x => na x || b x
  let ac : Sig N := fun x => ao x && c x
  have hn : Build A {na} 1 := notB ha
  have h1 : Build (A ∪ {na}) {ab} 1 := andB (Or.inr rfl) (Or.inl hb)
  have h2 : Build (A ∪ {na}) {ao} 1 := orB (Or.inr rfl) (Or.inl hb)
  have h3 : Build ((A ∪ {na}) ∪ ({ab} ∪ {ao})) {ac} 1 :=
    andB (Or.inr (Or.inr rfl)) (Or.inl (Or.inl hc))
  have h4 : Build ((A ∪ {na}) ∪ (({ab} ∪ {ao}) ∪ {ac}))
      {fun x => compareStep (a x) (b x) (c x)} 1 :=
    orB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  exact seq2B hn (seq2B (seqB (unionB h1 h2) h3) h4)

def compareBits (a b : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => compareStep (a.testBit j) (b.testBit j) (compareBits a b j)

lemma compareBits_spec (a b j : ℕ) :
    compareBits a b j = decide (a % 2^j ≤ b % 2^j) := by
  induction j with
  | zero => simp [compareBits, Nat.mod_one]
  | succ j ih =>
    rw [compareBits, ih, mod_two_pow_succ_eq a j, mod_two_pow_succ_eq b j]
    have ha := Nat.mod_lt a (Nat.two_pow_pos j)
    have hb := Nat.mod_lt b (Nat.two_pow_pos j)
    cases h₁ : a.testBit j <;> cases h₂ : b.testBit j <;>
      simp only [h₁, h₂, Bool.false_eq_true, Bool.true_eq, if_false, if_true, Nat.add_zero, compareStep,
        Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
        Bool.or_false, Bool.or_true, Nat.add_le_add_iff_right]
    · rw [decide_eq_true]
      omega
    · rw [decide_eq_false]
      omega

lemma compareBitsB {N : ℕ} {A : Set (Sig N)} (a b : (Fin N → Bool) → ℕ)
    (h1 : (fun _ => true) ∈ A) (L : ℕ)
    (ha : ∀ j : Fin L, bitsOf L a j ∈ A) (hb : ∀ j : Fin L, bitsOf L b j ∈ A) :
    Build A {fun x => compareBits (a x) (b x) L} (5*L) := by
  induction L with
  | zero => exact idleB (by simpa only [compareBits, Set.singleton_subset_iff] using h1)
  | succ L ih =>
    let prev : Sig N := fun x => compareBits (a x) (b x) L
    have hprev : Build A {prev} (5*L) :=
      ih (fun j => ha j.castSucc) (fun j => hb j.castSucc)
    have hnew : Build (A ∪ {prev}) {fun x => compareBits (a x) (b x) (L+1)} 5 :=
      compareStepB (Or.inl (ha (Fin.last L))) (Or.inl (hb (Fin.last L))) (Or.inr rfl)
    rw [show 5*(L+1) = 5*L+5 by omega]
    exact seq2B hprev hnew


lemma count_by_fibers {N : ℕ} {S α β W : Type*} [Fintype S] [Fintype W]
    (e : (S × α × β) ≃ W) (P : W → Prop) [DecidablePred P]
    (flags : S → Sig N) (x : Fin N → Bool)
    (hex : ∀ s, flags s x = true ↔ ∃ q : α × β, P (e (s,q)))
    (hinj : ∀ s (q q' : α × β), P (e (s,q)) → P (e (s,q')) → q = q') :
    (Finset.univ.filter P).card = score flags x := by
  classical
  unfold score
  refine Finset.card_bij (fun w _ => (e.symm w).1) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact (hex _).mpr ⟨(e.symm w).2, by simpa using hw⟩
  · intro w hw w' hw' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    apply e.symm.injective
    apply Prod.ext h
    apply hinj (e.symm w).1
    · simpa using hw
    · rw [h]
      simpa using hw'
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨p, hp⟩ := (hex s).mp hs
    exact ⟨e (s,p), by simpa using hp, by simp⟩

lemma card_image_word {k : ℕ} (P : Submodule F (Word k)) (f : Word k →ₗ[F] Word k)
    (source : Finset ℕ) (view : ℕ → ℕ)
    (hs : ∀ n, n ∈ source ↔ n < 2 ^ k ∧ wordOfNat k n ∈ P)
    (hv : ∀ n < 2 ^ k, view n < 2 ^ k ∧ wordOfNat k (view n) = f (wordOfNat k n))
    [Fintype (LinearMap.range (f.comp P.subtype))] :
    (source.image view).card = Fintype.card (LinearMap.range (f.comp P.subtype)) := by
  classical
  have hmem (n : ℕ) : n ∈ source.image view ↔
      n < 2 ^ k ∧ wordOfNat k n ∈ LinearMap.range (f.comp P.subtype) := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨hmk, hmP⟩ := (hs m).mp hm
      obtain ⟨hvlt, hveq⟩ := hv m hmk
      exact ⟨hvlt, ⟨⟨wordOfNat k m, hmP⟩, hveq.symm⟩⟩
    · rintro ⟨hn, ⟨w, hw⟩⟩
      let m := (wordEquiv k).symm w.val
      have hm : wordOfNat k m.val = w.val := wordOfNat_wordEquiv_symm _
      have hview : wordOfNat k (view m.val) = wordOfNat k n := by
        rw [(hv m.val m.isLt).2, hm]
        exact hw
      refine ⟨m.val, (hs m.val).mpr ⟨m.isLt, hm ▸ w.property⟩, ?_⟩
      exact (wordOfNat_eq_iff (hv m.val m.isLt).1 hn).mp hview
  change (source.image view).card = (Finset.univ : Finset (LinearMap.range (f.comp P.subtype))).card
  refine Finset.card_bij (fun n hn => ⟨wordOfNat k n, ((hmem n).mp hn).2⟩) ?_ ?_ ?_
  · simp
  · intro n hn m hm he
    exact (wordOfNat_eq_iff ((hmem n).mp hn).1 ((hmem m).mp hm).1).mp (congrArg Subtype.val he)
  · intro w _
    let n := (wordEquiv k).symm w.val
    have he : wordOfNat k n.val = w.val := wordOfNat_wordEquiv_symm _
    exact ⟨n.val, (hmem n.val).mpr ⟨n.isLt, he ▸ w.property⟩, Subtype.ext he⟩

lemma card_filter_word {k : ℕ} (P : ℕ → Prop) (Q : Word k → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ n < 2^k, P n ↔ Q (wordOfNat k n)) :
    ((Finset.range (2^k)).filter P).card = (Finset.univ.filter Q).card := by
  classical
  refine Finset.card_bij (fun n _ => wordOfNat k n) ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h n (Finset.mem_range.mp hn)).mp hp⟩
  · intro n hn m hm he
    exact (wordOfNat_eq_iff
      (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)).mp he
  · intro w hw
    let n := (wordEquiv k).symm w
    have he : wordOfNat k n.val = w := wordOfNat_wordEquiv_symm _
    refine ⟨n.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.isLt, (h n.val n.isLt).mpr ?_⟩, he⟩
    rw [he]
    exact (Finset.mem_filter.mp hw).2

def kernelNat (k g : ℕ) : Finset ℕ :=
  (Finset.range (2^k)).filter (fun w => w ^^^ rot k g w ^^^ rot k (k-g) w = 0)

lemma mem_kernelNat {k g n : ℕ} (hk : 0 < k) :
    n ∈ kernelNat k g ↔ n < 2^k ∧ wordOfNat k n ∈ kernelW hk g := by
  simp only [kernelNat, Finset.mem_filter, Finset.mem_range]
  by_cases hn : n < 2^k
  · simp only [hn, true_and]
    change _ ↔ mixW hk g (wordOfNat k n) = 0
    rw [← wordOfNat_mix hk hn, ← wordOfNat_zero k,
      wordOfNat_eq_iff (mix_lt hn g) (Nat.two_pow_pos k)]
  · simp [hn]

def viewNat (k s : ℕ) (mask : Fin (2^k)) (d : ℕ) : ℕ := rot k s d &&& mask.val

lemma viewNat_spec {k : ℕ} (hk : 0 < k) (s : ℕ) (mask : Fin (2^k)) (d : ℕ) (hd : d < 2^k) :
    viewNat k s mask d < 2^k ∧
      wordOfNat k (viewNat k s mask d) = viewW hk s (wordOfNat k mask.val) (wordOfNat k d) := by
  refine ⟨mask_lt _ mask.isLt, ?_⟩
  rw [viewNat, wordOfNat_mask, wordOfNat_rot hk hd]
  rfl

lemma col_card_nat {k : ℕ} (hk : 0 < k) (r : ℕ) (mc : Fin (2^k))
    [Fintype (ColCode hk (colView hk r (wordOfNat k mc.val)))] :
    ((kernelNat k 2).image (viewNat k (lastRotation 3 colFresh r) mc)).card =
      Fintype.card (ColCode hk (colView hk r (wordOfNat k mc.val))) :=
  @card_image_word k (kernelW hk 2) (colView hk r (wordOfNat k mc.val)) _ _
    (fun _ => mem_kernelNat hk) (viewNat_spec hk _ mc)
    (inferInstanceAs (Fintype (ColCode hk (colView hk r (wordOfNat k mc.val)))))

lemma row_card_nat {k : ℕ} (hk : 0 < k) (r : ℕ) (mr mc : Fin (2^k))
    [Fintype (RowCode hk (rowView hk r (wordOfNat k mr.val)) (colView hk r (wordOfNat k mc.val)))] :
    (((kernelNat k 1).filter (fun d => viewNat k (lastRotation 3 colFresh r) mc d = 0)).image
      (viewNat k (lastRotation 1 rowFresh r) mr)).card =
      Fintype.card (RowCode hk (rowView hk r (wordOfNat k mr.val)) (colView hk r (wordOfNat k mc.val))) := by
  refine @card_image_word k (rowShifts hk (colView hk r (wordOfNat k mc.val)))
    (rowView hk r (wordOfNat k mr.val)) _ _ ?_ (viewNat_spec hk _ mr)
    (inferInstanceAs (Fintype (RowCode hk (rowView hk r (wordOfNat k mr.val)) (colView hk r (wordOfNat k mc.val)))))
  intro n
  rw [Finset.mem_filter, mem_kernelNat hk]
  by_cases hn : n < 2^k
  · have h := viewNat_spec hk (lastRotation 3 colFresh r) mc n hn
    have h0 : viewNat k (lastRotation 3 colFresh r) mc n = 0 ↔
        colView hk r (wordOfNat k mc.val) (wordOfNat k n) = 0 := by
      change _ ↔ viewW hk (lastRotation 3 colFresh r) (wordOfNat k mc.val) (wordOfNat k n) = 0
      rw [← h.2, ← wordOfNat_zero k, wordOfNat_eq_iff h.1 (Nat.two_pow_pos k)]
    simp only [hn, true_and, h0]
    rfl
  · simp [hn]

abbrev hitsNat {k : ℕ} (r : ℕ) (cR cC : ℕ → Fin (2^k)) (mr mc u v tr tc : Fin (2^k)) (key : ℕ) : Prop :=
  (stateNat k 1 1 rowFresh cR key u.val r &&& mr.val) = (tr.val &&& mr.val) ∧
  (stateNat k 2 3 colFresh cC key v.val r &&& mc.val) = (tc.val &&& mc.val)

lemma hitsNat_iff {k : ℕ} (hk : 0 < k) (r : ℕ) (cR cC : ℕ → Fin (2^k))
    (mr mc u v tr tc : Fin (2^k)) (n : ℕ) (hn : n < 2^k) :
    hitsNat r cR cC mr mc u v tr tc n ↔
      hitsWord hk r (fun j => wordOfNat k (cR j).val) (fun j => wordOfNat k (cC j).val)
        (wordOfNat k mr.val) (wordOfNat k mc.val) (wordOfNat k u.val) (wordOfNat k v.val)
        (wordOfNat k tr.val) (wordOfNat k tc.val) (wordOfNat k n) := by
  have hmask (g start : ℕ) (fresh : ℕ → ℕ) (c : ℕ → Fin (2^k))
      (mask name target : Fin (2^k)) :
      (stateNat k g start fresh c n name.val r &&& mask.val) = (target.val &&& mask.val) ↔
      maskW (wordOfNat k mask.val) (stateW hk g start fresh
        (fun j => wordOfNat k (c j).val) (wordOfNat k n) (wordOfNat k name.val) r) =
        maskW (wordOfNat k mask.val) (wordOfNat k target.val) := by
    rw [← wordOfNat_state hk g start fresh c ⟨n,hn⟩ name r,
      ← wordOfNat_mask, ← wordOfNat_mask,
      wordOfNat_eq_iff (mask_lt _ mask.isLt) (mask_lt _ mask.isLt)]
  exact and_congr (hmask 1 1 rowFresh cR mr u tr) (hmask 2 3 colFresh cC mc v tc)

def bitsNat (n x : ℕ) : List Bool := (List.range n).map (fun i => x.testBit i)

lemma length_bitsNat (n x : ℕ) : (bitsNat n x).length = n := by simp [bitsNat]

lemma getD_bitsNat (n x i : ℕ) (hi : i < n) : (bitsNat n x).getD i false = x.testBit i := by
  rw [List.getD_eq_getElem _ _ (by rwa [length_bitsNat])]
  simp [bitsNat]

def inputWord {N n offset : ℕ} (h : offset + n ≤ N) (x : Fin N → Bool) : Word n :=
  fun i => b2z (x ⟨offset+i.val, by have := i.isLt; omega⟩)

def inputSigs (N : ℕ) : Set (Sig N) := Set.range (fun i : Fin N => fun x => x i)

lemma inputWord_mem {N n offset : ℕ} (h : offset + n ≤ N) :
    wordSigs (inputWord h) ⊆ inputSigs N := by
  apply wordSigs_subset
  intro i
  refine ⟨⟨offset+i.val, by have := i.isLt; omega⟩, ?_⟩
  funext x
  simp only [wordBit, inputWord, z2b_b2z]

def readInput (N : ℕ) (l : List Bool) : Fin N → Bool := fun i => l.getD i.val false

lemma readInput_ofFn {N : ℕ} (l : List Bool) (hl : l.length = N) :
    List.ofFn (readInput N l) = l := by
  subst N
  convert List.ofFn_get l using 2
  funext i
  unfold readInput
  rw [List.getD_eq_getElem _ _ i.isLt]
  rfl

lemma inputWord_packed {N n offset : ℕ} (h : offset + n ≤ N) (pre suf : List Bool)
    (hp : pre.length = offset) (w : ℕ) :
    inputWord h (readInput N (pre ++ bitsNat n w ++ suf)) = wordOfNat n w := by
  funext i
  have hi := i.isLt
  simp only [List.append_assoc]
  change b2z ((pre ++ (bitsNat n w ++ suf)).getD (offset+i.val) false) = b2z (w.testBit i.val)
  rw [List.getD_append_right _ _ _ _ (by omega), hp, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by rwa [length_bitsNat]), getD_bitsNat _ _ _ i.isLt]

lemma wordEquiv_inv_bit {n : ℕ} (w : Word n) (i : Fin n) :
    ((wordEquiv n).symm w).val.testBit i.val = z2b (w i) := by
  have h := congrArg z2b (congrFun (wordOfNat_wordEquiv_symm w) i)
  simpa only [wordOfNat, z2b_b2z] using h

lemma lastRotation_row (r : ℕ) :
    lastRotation 1 rowFresh r = (if r=0 then 1 else 2*(r-1)) := by
  cases r <;> simp [lastRotation, rowFresh]

lemma lastRotation_col (r : ℕ) :
    lastRotation 3 colFresh r = (if r=0 then 3 else 3*r+1) := by
  cases r <;> simp [lastRotation, colFresh]

set_option maxHeartbeats 3000000 in
lemma proof32016 (k r : ℕ) (hk : 0 < k) (cR cC : ℕ → Fin (2^k)) (mr mc : Fin (2^k)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (4*k+(k+1)) C ∧
      C.size ≤ 192*(k+1)*(r+1)*
        (2^k / (((kernelNat k 2).image (viewNat k (lastRotation 3 colFresh r) mc)).card *
          (((kernelNat k 1).filter (fun d => viewNat k (lastRotation 3 colFresh r) mc d = 0)).image
            (viewNat k (lastRotation 1 rowFresh r) mr)).card)) ∧
      ∀ (u v tr tc : Fin (2^k)) (t : Fin (2^(k+1))),
        C.eval (bitsNat k u.val ++ bitsNat k v.val ++ bitsNat k tr.val ++ bitsNat k tc.val ++
          bitsNat (k+1) t.val) =
          decide (t.val ≤ ((Finset.range (2^k)).filter (hitsNat r cR cC mr mc u v tr tc)).card) := by
  classical
  let wR := fun j => wordOfNat k (cR j).val
  let wC := fun j => wordOfNat k (cC j).val
  let mR := wordOfNat k mr.val
  let mC := wordOfNat k mc.val
  let VR := rowView hk r mR
  let VC := colView hk r mC
  let Col := ColCode hk VC
  let Row := RowCode hk VR VC
  obtain ⟨D, hD⟩ := (LinearMap.range (shiftPair hk VR VC)).exists_isCompl
  letI : Fintype D := Fintype.ofFinite _
  letI hCol : Fintype Col := Fintype.ofFinite _
  letI hRow : Fintype Row := Fintype.ofFinite _
  let e := keyEquiv hk VR VC D hD.symm
  let m := Fintype.card D
  have ha : Fintype.card Col ≤ 16 := @col_range_card k hk VC hCol
  have hb : Fintype.card Row ≤ 16 := @row_range_card k hk VR VC hRow
  have hcPos : 0 < Fintype.card Col := Fintype.card_pos_iff.mpr ⟨(0 : Col)⟩
  have hrPos : 0 < Fintype.card Row := Fintype.card_pos_iff.mpr ⟨(0 : Row)⟩
  have hmPos : 0 < m := Fintype.card_pos_iff.mpr ⟨(0 : D)⟩
  have hcount : m * (Fintype.card Col * Fintype.card Row) = 2^k := by
    have h := Fintype.card_congr e.toEquiv
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] using h
  have hdiv : 2^k / (((kernelNat k 2).image (viewNat k (lastRotation 3 colFresh r) mc)).card *
          (((kernelNat k 1).filter (fun d => viewNat k (lastRotation 3 colFresh r) mc d = 0)).image
            (viewNat k (lastRotation 1 rowFresh r) mr)).card) = m := by
    rw [@col_card_nat k hk r mc hCol, @row_card_nat k hk r mr mc hRow]
    change 2^k / (Fintype.card Col * Fintype.card Row) = m
    calc
      _ = (m * (Fintype.card Col * Fintype.card Row)) /
          (Fintype.card Col * Fintype.card Row) :=
        congrArg (fun n => n / (Fintype.card Col * Fintype.card Row)) hcount.symm
      _ = m := Nat.mul_div_cancel m (Nat.mul_pos hcPos hrPos)
  have hle : m ≤ 2^k := by
    rw [← hcount]
    exact Nat.le_mul_of_pos_right m (Nat.mul_pos hcPos hrPos)
  let N := 4*k+(k+1)
  have hU : 0+k ≤ N := by dsimp [N]; omega
  have hV : k+k ≤ N := by dsimp [N]; omega
  have hTR : 2*k+k ≤ N := by dsimp [N]; omega
  have hTC : 3*k+k ≤ N := by dsimp [N]; omega
  have hT : 4*k+(k+1) ≤ N := le_rfl
  let U := inputWord hU
  let V := inputWord hV
  let TR := inputWord hTR
  let TC := inputWord hTC
  let T := inputWord hT
  let threshold : (Fin N → Bool) → ℕ := fun x => ((wordEquiv (k+1)).symm (T x)).val
  let flags : D → Sig N := fun d => @slot N k hk r wR wC mR mC d.val hCol hRow U V TR TC
  let A := inputSigs N ∪ ({fun _ => false} ∪ {fun _ => true})
  have h0 : (fun _ => false) ∈ A := Or.inr (Or.inl rfl)
  have h1 : (fun _ => true) ∈ A := Or.inr (Or.inr rfl)
  have hconst : Build (inputSigs N) ({(fun _ => false)} ∪ {(fun _ => true)}) 2 :=
    unionB (constB false) (constB true)
  have hflag (d : D) :
      Build A {flags d} (100*(k+1)*(r+1)) :=
    @slotFlagB N k Col Row hCol hRow A hk r wR wC mR mC d.val
      (fun a => a.val) (fun b => b.val) (fun a => d.val + colLift hk VC a) U V TR TC
      ((inputWord_mem hU).trans Set.subset_union_left) ((inputWord_mem hV).trans Set.subset_union_left)
      ((inputWord_mem hTR).trans Set.subset_union_left) ((inputWord_mem hTC).trans Set.subset_union_left)
      h0 h1 ha hb
  have hslots : Build A (Set.range flags) (m * (100*(k+1)*(r+1))) :=
    indexedSigB flags _ hflag
  let BS := Set.range (bitsOf (k+1) (score flags))
  have hscore : Build (A ∪ Set.range flags) BS (m * (9*(k+1))) :=
    scoreB flags Set.subset_union_right (Or.inl h0)
  have htmem (i : Fin (k+1)) : bitsOf (k+1) threshold i ∈ A := by
    have eq : bitsOf (k+1) threshold i = wordBit T i := by
      funext x
      exact wordEquiv_inv_bit (T x) i
    rw [eq]
    exact wordBit_mem ((inputWord_mem hT).trans Set.subset_union_left) i
  have hcmp : Build (A ∪ BS) {fun x => compareBits (threshold x) (score flags x) (k+1)} (5*(k+1)) :=
    compareBitsB threshold (score flags) (Or.inl h1) (k+1)
      (fun i => Or.inl (htmem i)) (fun i => Or.inr ⟨i,rfl⟩)
  have hbuild := seq2B hconst (seq2B (seq2B hslots hscore) hcmp)
  obtain ⟨C, hfan, hread, hsize, heval⟩ := finishB _ hbuild
  refine ⟨C, hfan, hread, ?_, ?_⟩
  · rw [hdiv]
    refine hsize.trans ?_
    have hm1 : 0 < (r+1)*m := Nat.mul_pos (Nat.succ_pos r) hmPos
    have hl : k+1 ≤ (k+1)*(r+1)*m := by
      rw [Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ hm1
    have hml : m*(k+1) ≤ (k+1)*(r+1)*m := by
      rw [Nat.mul_comm m (k+1)]
      exact Nat.mul_le_mul_right m (Nat.le_mul_of_pos_right _ (Nat.succ_pos r))
    nlinarith
  · intro u v tr tc t
    let l := bitsNat k u.val ++ bitsNat k v.val ++ bitsNat k tr.val ++ bitsNat k tc.val ++
      bitsNat (k+1) t.val
    let x := readInput N l
    have hLen : l.length = N := by
      simp only [l, N, List.length_append, length_bitsNat]
      omega
    have hu : U x = wordOfNat k u.val := by
      have h := inputWord_packed hU []
        (bitsNat k v.val ++ bitsNat k tr.val ++ bitsNat k tc.val ++ bitsNat (k+1) t.val) rfl u.val
      simpa only [U, x, l, List.nil_append, List.append_assoc] using h
    have hv : V x = wordOfNat k v.val := by
      have h := inputWord_packed hV (bitsNat k u.val)
        (bitsNat k tr.val ++ bitsNat k tc.val ++ bitsNat (k+1) t.val) (length_bitsNat _ _) v.val
      simpa only [V, x, l, List.append_assoc] using h
    have htr : TR x = wordOfNat k tr.val := by
      have h := inputWord_packed hTR (bitsNat k u.val ++ bitsNat k v.val)
        (bitsNat k tc.val ++ bitsNat (k+1) t.val)
        (by simp only [List.length_append, length_bitsNat]; omega) tr.val
      simpa only [TR, x, l, List.append_assoc] using h
    have htc : TC x = wordOfNat k tc.val := by
      have h := inputWord_packed hTC (bitsNat k u.val ++ bitsNat k v.val ++ bitsNat k tr.val)
        (bitsNat (k+1) t.val)
        (by simp only [List.length_append, length_bitsNat]; omega) tc.val
      simpa only [TC, x, l, List.append_assoc] using h
    have ht : threshold x = t.val := by
      have ht' : T x = wordOfNat (k+1) t.val := by
        have h := inputWord_packed hT
          (bitsNat k u.val ++ bitsNat k v.val ++ bitsNat k tr.val ++ bitsNat k tc.val) []
          (by simp only [List.length_append, length_bitsNat]; omega) t.val
        simpa only [T, x, l, List.append_nil, List.append_assoc] using h
      unfold threshold
      rw [ht']
      exact congrArg Fin.val ((wordEquiv (k+1)).symm_apply_apply t)
    let P := hitsWord hk r wR wC mR mC (U x) (V x) (TR x) (TC x)
    have hsp (d : D) := @slot_spec N k hk r wR wC mR mC d.val hCol hRow U V TR TC x
    have hcounts : (Finset.univ.filter P).card = score flags x := by
      apply count_by_fibers e.toEquiv P flags x
      · intro d
        exact (hsp d).1
      · intro d a b
        exact (hsp d).2 a b
    have hNatCount : ((Finset.range (2^k)).filter (hitsNat r cR cC mr mc u v tr tc)).card =
        score flags x := by
      refine (card_filter_word _ P ?_).trans hcounts
      intro n hn
      unfold P
      rw [hu, hv, htr, htc]
      exact hitsNat_iff hk r cR cC mr mc u v tr tc n hn
    have hScoreLt : score flags x < 2^(k+1) := by
      have h := (score_le flags x).trans hle
      rw [Nat.pow_succ]
      have := Nat.two_pow_pos k
      omega
    change C.eval l = _
    rw [← readInput_ofFn l hLen, heval x, compareBits_spec, ht, Nat.mod_eq_of_lt t.isLt,
      Nat.mod_eq_of_lt hScoreLt]
    rw [hNatCount]

end PEqualNP.Outside.L_meta_32016

theorem PEqualNP.Outside.L_meta_32016 : ∀ (k r : Nat), 0 < k → ∀ (cR cC : Nat → Fin (2^k)) (mr mc : Fin (2^k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ (cR (rowIndex + 1)).val) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ (cC (colIndex + 1)).val)
      (rot 3 colKey ^^^ colName)
  let words := Finset.range (2 ^ k)
  let ker := fun (g : Nat) => words.filter (fun w =>
    (w ^^^ rot g w ^^^ rot (k-g) w) = 0)
  let viewR := fun (d : Nat) => rot (if r=0 then 1 else 2*(r-1)) d &&& mr.val
  let viewC := fun (d : Nat) => rot (if r=0 then 3 else 3*r+1) d &&& mc.val
  let a := ((ker 2).image viewC).card
  let b := (((ker 1).filter (fun d => viewC d = 0)).image viewR).card
  let slots := 2 ^ k / (a*b)
  let bits := fun (n x : Nat) => (List.range n).map (fun i => x.testBit i)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (4*k+(k+1)) C ∧
    C.size ≤ 192*(k+1)*(r+1)*slots ∧
    ∀ (u v tr tc : Fin (2^k)) (t : Fin (2^(k+1))),
      let hits := words.filter (fun w =>
        (first w u.val &&& mr.val) = (tr.val &&& mr.val) ∧
        (second w v.val &&& mc.val) = (tc.val &&& mc.val))
      C.eval (bits k u.val ++ bits k v.val ++ bits k tr.val ++ bits k tc.val ++
        bits (k+1) t.val) = decide (t.val ≤ hits.card) := by
  intro k r hk cR cC mr mc
  dsimp only
  obtain ⟨C, hfan, hread, hsize, heval⟩ :=
    PEqualNP.Outside.L_meta_32016.proof32016 k r hk cR cC mr mc
  refine ⟨C, hfan, hread, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_32016.lastRotation_row,
      PEqualNP.Outside.L_meta_32016.lastRotation_col] at hsize
    exact hsize
  · exact heval
